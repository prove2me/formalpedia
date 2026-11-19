-- Prove2me | solution 1 for Lax455465Proofs.RamRegionCore.iteration_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:57:32.584142+00:00
-- url     : https://prove2.me/submissions/4d954ad0-537a-4fa2-8c45-a93e10a5ce1a

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.NNRat.BigOperators
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.List.FinRange
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax455465Proofs_RamRegionSetup_command_spec_native

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

namespace Lax455465Proofs.RamRegionSetup
end Lax455465Proofs.RamRegionSetup
theorem Lax455465Proofs.RamRegionSetup.command_spec:∀ (B M H:Nat) {n:Nat} (weights:Fin n→ NNRat) (capacity length:Lax455465Proofs.MetricMatrix.Matrix n)
  (root:Fin n) (seed beta delta:NNRat) (k:Nat),
  Nat.le k M→
    Nat.lt
        (HAdd.hAdd
          (HMul.hMul ((2:Nat))
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
              ((2:Nat))))
          ((3:Nat)))
        B→
      Nat.lt
          (HAdd.hAdd
            (HMul.hMul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) H)
                ((2:Nat))))
            ((3:Nat)))
          B→
        Nat.lt
            (HAdd.hAdd
              (HMul.hMul
                ((2:Nat))
                (HMul.hMul n n))
              ((2:Nat)))
            B→
          Nat.lt
              (HAdd.hAdd
                (HMul.hMul
                  ((2:Nat)) n)
                ((2:Nat)))
              B→
            Nat.lt
                (HAdd.hAdd
                  (HMul.hMul
                    ((2:Nat))
                    (HAdd.hAdd
                      (HAdd.hAdd k
                        ((1:Nat)))
                      (HMul.hMul
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
                              (HAdd.hAdd
                                (HAdd.hAdd k
                                  ((1:Nat)))
                                (HMul.hMul
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
                                  (HAdd.hAdd
                                    (HAdd.hAdd k
                                      ((1:Nat)))
                                    (HMul.hMul
                                      ((2:Nat)) n)))
                                τ)
                              (@Lax455465Proofs.RamSelectedRegion.Selected n
                                (@Lax455465Proofs.RamRegionSetup.query n weights capacity length root seed beta)
                                (@Lax455465Proofs.RadiusData.candidates n (length root)
                                  (fun (v:Fin n) => length v root) k delta)
                                τ)))
                        (Lax455465Proofs.RamRegionSetup.cost n k M H):= @Lax455465Proofs.RamRegionSetup.command_spec_native

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

theorem gcdStep_spec (B a b:ℕ) (ha:a < B) (hb:b < B):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdStep
      (fun _ σ' => σ'.vars "gcd.a"=b∧ σ'.vars "gcd.b"=a % b) 12:=by
  rintro σ ⟨hsa,hsb⟩
  have hdiv:a / b < B:=(Nat.div_le_self a b).trans_lt ha
  have hmul:a / b * b < B:=(Nat.div_mul_le_self a b).trans_lt ha
  have hsub:a - a / b * b < B:=(Nat.sub_le _ _).trans_lt ha
  (expose_names;
    (refine let c0:Nat:= @HMod.hMod Nat Nat Nat (@instHMod Nat Nat.instMod) a b; let c1:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "gcd.a") b) (@Eq Nat (Env.vars σ' "gcd.b") c0)) σ; let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "gcd.a") (Env.vars σ "gcd.b"); let c3:Nat:=Nat.mul c2 (Env.vars σ "gcd.b"); let c4:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) (Env.vars σ "gcd.a") c3; let c5:Env:=Env.setVar σ "gcd.t" c4; let c6:Nat:=Env.vars c5 "gcd.b"; let c7:Env:=Env.setVar c5 "gcd.a" c6; let c8:Nat:=Env.vars c7 "gcd.t"; let c9:Env:=Env.setVar c7 "gcd.b" c8; let c10:Nat→ Nat→ Nat:=Nat.add; let c11:Nat→ Nat:=c10 ((1:Nat)); let c12:Expr:=Expr.mul (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b"); let c13:Expr:=Expr.sub (Expr.var "gcd.a") c12; let c14:Nat:=c11 (Expr.size c13); let c15:Nat:=c11 (Expr.size (Expr.var "gcd.b")); let c16:Nat:=c11 (Expr.size (Expr.var "gcd.t")); let c17:Nat:=c10 c15 c16; let c18:String→ Nat:=Env.vars c9; @Exists.intro Env (fun (σ':Env) => And (Run B gcdStep σ σ' ((12:Nat))) (c1 σ')) c9 (@And.intro (Run B gcdStep σ c9 ((12:Nat))) (c1 c9) (RunStep.mono B gcdStep σ c9 (c10 c14 c17) ((12:Nat)) (RunStep.seq B (Com.assign "gcd.t" c13) (Com.seq (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t"))) σ c5 c9 c14 c17 (RunStep.assign B σ "gcd.t" c13 c4 (RunStep.eval_sub B σ (Expr.var "gcd.a") c12 (Env.vars σ "gcd.a") c3 (RunStep.eval_var B σ "gcd.a" (?nAX_g5407_0_0_0)) (RunStep.eval_mul B σ (Expr.div (Expr.var "gcd.a") (Expr.var "gcd.b")) (Expr.var "gcd.b") c2 (Env.vars σ "gcd.b") (RunStep.eval_div B σ (Expr.var "gcd.a") (Expr.var "gcd.b") (Env.vars σ "gcd.a") (Env.vars σ "gcd.b") (RunStep.eval_var B σ "gcd.a" (?nAX_g5407_0_0_1)) (RunStep.eval_var B σ "gcd.b" (?nAX_g5407_0_0_2)) ?_) (RunStep.eval_var B σ "gcd.b" (?nAX_g5407_0_0_3)) ?_) (?nAX_g5407_0_0_4))) (RunStep.seq B (Com.assign "gcd.a" (Expr.var "gcd.b")) (Com.assign "gcd.b" (Expr.var "gcd.t")) c5 c7 c9 c15 c16 (RunStep.assign B c5 "gcd.a" (Expr.var "gcd.b") c6 (RunStep.eval_var B c5 "gcd.b" (?nAX_g5407_0_0_5))) (RunStep.assign B c7 "gcd.b" (Expr.var "gcd.t") c8 (RunStep.eval_var B c7 "gcd.t" (?nAX_g5407_0_0_6))))) (?nAX_g5407_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5407_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5407_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp_all [Nat.mod_def,Nat.mul_comm]

theorem remainder_half (d r:ℕ) (hr:0 < r) (hrd:r < d):d % r≤ d / 2:=by
  by_cases h:r≤ d / 2
  · exact (Nat.mod_lt d hr).le.trans h
  · rw [Nat.mod_eq_sub_mod hrd.le,Nat.mod_eq_of_lt (by omega)]
    omega

theorem size_half_lt (b:ℕ) (hb:0 < b):(b / 2).size < b.size:=by
  have hs:0 < b.size:=Nat.size_pos.mpr hb
  have hp:b < 2 ^ b.size:=Nat.lt_size_self b
  have he:2 ^ b.size=2 * 2 ^ (b.size - 1):=by
    calc
      _=2 ^ ((b.size - 1) + 1):=congrArg (fun k => 2 ^ k) (by omega)
      _=_:=by rw [pow_succ]; omega
  have hhalf:b / 2 < 2 ^ (b.size - 1):=by omega
  have h:=Nat.size_le.mpr hhalf
  omega

theorem gcd_swap_mod (a b:ℕ):Nat.gcd b (a % b)=Nat.gcd a b:=by
  rw [Nat.gcd_comm b _, ← Nat.gcd_rec,Nat.gcd_comm]

theorem gcdDoubleStep_spec (B M a b:ℕ) (hM:M < B)
    (ha:a≤ M) (hb:b≤ M) (hbpos:0 < b):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdDoubleStep
      (fun _ σ' => σ'.vars "gcd.a" ≤ M∧ σ'.vars "gcd.b" ≤ M∧
        Nat.gcd (σ'.vars "gcd.a") (σ'.vars "gcd.b")=Nat.gcd a b∧
        (σ'.vars "gcd.b").size < b.size) 32:=by
  intro σ hσ
  obtain ⟨τ,hrun,hτa,hτb⟩:=(gcdStep_spec B a b (ha.trans_lt hM) (hb.trans_lt hM)) σ hσ
  have hrlt:a % b < b:=Nat.mod_lt a hbpos
  have hrB:a % b < B:=hrlt.trans (hb.trans_lt hM)
  have h0B:0 < B:=(Nat.zero_le M).trans_lt hM
  by_cases hr0:a % b=0
  · have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some false:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb,hr0]
      rfl
    refine ⟨τ, (hrun.seq (Run.ite_false hc Run.skip)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hτa,hτb]
    refine ⟨hb,hrlt.le.trans hb,gcd_swap_mod a b, ?_⟩
    rw [hr0]
    exact Nat.size_pos.mpr hbpos
  · have hrpos:0 < a % b:=Nat.pos_of_ne_zero hr0
    have hc:(Cond.lt (.lit 0) (.var "gcd.b")).evalB B τ=some true:=by
      rw [evalB_condLt (evalB_lit h0B) (evalB_var (hτb ▸ hrB)),hτb]
      simp [hrpos]
    obtain ⟨ν,hrν,hνa,hνb⟩:=
      (gcdStep_spec B b (a % b) (hb.trans_lt hM) hrB) τ ⟨hτa,hτb⟩
    refine ⟨ν, (hrun.seq (Run.ite_true hc hrν)).mono (by norm_num), ?_⟩
    dsimp only
    rw [hνa,hνb]
    refine ⟨hrlt.le.trans hb, (Nat.mod_lt b hrpos).le.trans (hrlt.le.trans hb),
      (gcd_swap_mod b (a % b)).trans (gcd_swap_mod a b), ?_⟩
    exact (Nat.size_le_size (remainder_half b (a % b) hrpos hrlt)).trans_lt
      (size_half_lt b hbpos)

theorem gcdLoop_spec (B M a b:ℕ) (hM:M < B) (ha:a≤ M) (hb:b≤ M):
    Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => σ'.vars "gcd.a"=Nat.gcd a b∧ σ'.vars "gcd.b"=0)
      (36 * b.size + 4):=by
  let I:=fun σ:Env => σ.vars "gcd.a" ≤ M∧ σ.vars "gcd.b" ≤ M∧
    Nat.gcd (σ.vars "gcd.a") (σ.vars "gcd.b")=Nat.gcd a b
  have hloop:Spec B (fun σ => σ.vars "gcd.a"=a∧ σ.vars "gcd.b"=b) gcdLoop
      (fun _ σ' => I σ'∧
        (Cond.lt (.lit 0) (.var "gcd.b")).evalB B σ'=some false)
      (36 * b.size + 4):=by
    apply Spec.while_count I (fun σ => (σ.vars "gcd.b").size) 32
    · intro σ hI
      exact ⟨_,evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
        (evalB_var (hI.2.1.trans_lt hM))⟩
    · rintro σ ⟨hI,hc⟩
      have hbpos:0 < σ.vars "gcd.b" :=by
        rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
          (evalB_var (hI.2.1.trans_lt hM))] at hc
        simpa using hc
      obtain ⟨τ,hr,hτa,hτb,hτg,hτs⟩:=
        gcdDoubleStep_spec B M _ _ hM hI.1 hI.2.1 hbpos σ ⟨rfl,rfl⟩
      exact ⟨τ,hr, ⟨hτa,hτb,hτg.trans hI.2.2⟩,hτs⟩
    · rintro σ ⟨hσa,hσb⟩
      exact ⟨hσa ▸ ha,hσb ▸ hb,by rw [hσa,hσb]⟩
    · rintro σ ⟨_,hσb⟩
      simp [hσb]
  apply hloop.post
  rintro σ τ _ ⟨hI,hc⟩
  have hb0:τ.vars "gcd.b"=0:=by
    rw [evalB_condLt (evalB_lit ((Nat.zero_le M).trans_lt hM))
      (evalB_var (hI.2.1.trans_lt hM))] at hc
    simpa using hc
  exact ⟨by simpa [hb0] using hI.2.2,hb0⟩

theorem normalizeFraction_spec (B n d:ℕ) (hn:n < B) (hd:d < B) (hdpos:0 < d):
    Spec B (fun σ => σ.vars "rat.n"=n∧ σ.vars "rat.d"=d) normalizeFraction
      (fun _ σ' => σ'.vars "rat.n"=n / Nat.gcd n d∧
        σ'.vars "rat.d"=d / Nat.gcd n d) (36 * d.size + 16):=by
  have hM:max n d < B:=max_lt hn hd
  have hg:Nat.gcd n d < B:=(Nat.gcd_le_right n hdpos).trans_lt hd
  have hnDiv:n / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hn
  have hdDiv:d / Nat.gcd n d < B:=(Nat.div_le_self _ _).trans_lt hd
  have hs:=(gcdLoop_spec B (max n d) n d hM (le_max_left _ _) (le_max_right _ _)).frame
  rintro σ ⟨hσn,hσd⟩
  (expose_names;
    (refine let c0:Nat:=Env.vars (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d"; let c1:Env:=Env.setVar (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" c0; let c2:Env→ Nat→ Prop:=Run B gcdLoop c1; let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat→ Nat:=c3 (Nat.mul ((36:Nat)) (Nat.size d)); let c5:Nat:=c4 ((4:Nat)); let c6:String→ Nat:=Env.vars c1; let c7:List Nat:=Env.inp c1; let c8:List Nat:=Env.out c1; let c9:Env→ Prop:=fun (σ':Env) => And (c2 σ' c5) (And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') c8))))); let c10:Nat:=c4 ((16:Nat)); let c11:Nat→ Nat→ Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv); let c12:Nat:=c11 n (Nat.gcd n d); let c13:Nat:=c11 d (Nat.gcd n d); let c14:Env→ Prop:=(fun (x σ':Env) => And (@Eq Nat (Env.vars σ' "rat.n") c12) (@Eq Nat (Env.vars σ' "rat.d") c13)) σ; let c15:Env→ Prop:=fun (σ':Env) => And (Run B normalizeFraction σ σ' c10) (c14 σ'); let c16:Prop:= @Exists Env c15; let c17:Nat→ Nat:=c3 ((1:Nat)); let c18:Nat:=c17 (Expr.size (Expr.var "rat.n")); let c19:Nat:=c17 (Expr.size (Expr.var "rat.d")); let c20:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a"))); let c21:Nat:=c17 (Expr.size (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a"))); let c22:Nat:=c3 c20 c21; let c23:Nat:=c3 c5 c22; let c24:Nat:=c3 c19 c23; let c25:Com:=Com.assign "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")); let c26:Com:=Com.assign "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")); let c27:Com:=Com.seq c25 c26; let c28:Com:=Com.seq gcdLoop c27; @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => c16) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "gcd.a") n) (@Eq Nat (Env.vars σ_1 "gcd.b") d)) gcdLoop (fun (σ_1 σ':Env) => And (And (@Eq Nat (Env.vars σ' "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars σ' "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars σ' y) (Env.vars σ_1 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs σ_1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp σ') (Env.inp σ_1)) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out σ') (Env.out σ_1)))))) c5 hs c1 ?_) fun (w:Env) (h:And (c2 w c5) (And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))))) => let c0_1:Prop:=And (And (@Eq Nat (Env.vars w "gcd.a") (Nat.gcd n d)) (@Eq Nat (Env.vars w "gcd.b") ((0:Nat)))) (And (∀ y∉ Com.wvars gcdLoop, @Eq Nat (Env.vars w y) (c6 y)) (And (∀ a∉ Com.warrs gcdLoop, @Eq (List Nat) (Env.arrs w a) (Env.arrs c1 a)) (And (Not (Com.reads gcdLoop)→ @Eq (List Nat) (Env.inp w) c7) (Com.NoWrite gcdLoop→ @Eq (List Nat) (Env.out w) c8)))); let c1_1:Nat:=c11 (Env.vars w "rat.n") (Env.vars w "gcd.a"); let c2_1:Env:=Env.setVar w "rat.n" c1_1; let c3_1:String→ Nat:=Env.vars c2_1; let c4_1:Nat:=c3_1 "rat.d"; let c5_1:Nat:=c3_1 "gcd.a"; let c6_1:Nat:=c11 c4_1 c5_1; let c7_1:Env:=Env.setVar c2_1 "rat.d" c6_1; let c8_1:String→ Nat:=Env.vars c7_1; @And.casesOn (c2 w c5) c0_1 (fun (x:And (c2 w c5) c0_1) => c16) h fun (left:c2 w c5) (right:c0_1) => @Exists.intro Env c15 c7_1 (@And.intro (Run B normalizeFraction σ c7_1 c10) (c14 c7_1) (RunStep.mono B normalizeFraction σ c7_1 (c3 c18 c24) c10 (RunStep.seq B (Com.assign "gcd.a" (Expr.var "rat.n")) (Com.seq (Com.assign "gcd.b" (Expr.var "rat.d")) c28) σ (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c7_1 c18 c24 (RunStep.assign B σ "gcd.a" (Expr.var "rat.n") (Env.vars σ "rat.n") (RunStep.eval_var B σ "rat.n" (?nAX_g5416_0_0_0))) (RunStep.seq B (Com.assign "gcd.b" (Expr.var "rat.d")) c28 (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) c1 c7_1 c19 c23 (RunStep.assign B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "gcd.b" (Expr.var "rat.d") c0 (RunStep.eval_var B (Env.setVar σ "gcd.a" (Env.vars σ "rat.n")) "rat.d" (?nAX_g5416_0_0_1))) (RunStep.seq B gcdLoop c27 c1 w c7_1 c5 c22 left (RunStep.seq B c25 c26 w c2_1 c7_1 c20 c21 (RunStep.assign B w "rat.n" (Expr.div (Expr.var "rat.n") (Expr.var "gcd.a")) c1_1 (RunStep.eval_div B w (Expr.var "rat.n") (Expr.var "gcd.a") (Env.vars w "rat.n") (Env.vars w "gcd.a") (RunStep.eval_var B w "rat.n" ?_) (RunStep.eval_var B w "gcd.a" (?nAX_g5416_0_0_2)) ?_)) (RunStep.assign B c2_1 "rat.d" (Expr.div (Expr.var "rat.d") (Expr.var "gcd.a")) c6_1 (RunStep.eval_div B c2_1 (Expr.var "rat.d") (Expr.var "gcd.a") c4_1 c5_1 (RunStep.eval_var B c2_1 "rat.d" ?_) (RunStep.eval_var B c2_1 "gcd.a" (?nAX_g5416_0_0_3)) ?_)))))) (?nAX_g5416_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5416_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5416_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all [gcdLoop,gcdDoubleStep,gcdStep,Com.wvars]

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
      (36 * (d₁ * d₂).size + 64):=by
  have hM:M < B:=by nlinarith
  have hn₁B:=hn₁.trans_lt hM
  have hd₁B:=hd₁.trans_lt hM
  have hn₂B:=hn₂.trans_lt hM
  have hd₂B:=hd₂.trans_lt hM
  have hnn:n₁ * n₂ < B:=(Nat.mul_le_mul hn₁ hn₂).trans_lt (by nlinarith)
  have hdd:d₁ * d₂ < B:=(Nat.mul_le_mul hd₁ hd₂).trans_lt (by nlinarith)
  have h1:1 < B:=by nlinarith
  have hs₁B:s₁ < B:=hs₁.trans_lt h1
  have hs₂B:s₂ < B:=hs₂.trans_lt h1
  have hmul:fractionValue (if s₁=s₂ then 0 else 1) (n₁ * n₂) (d₁ * d₂) =
      fractionValue s₁ n₁ d₁ * fractionValue s₂ n₂ d₂:=by
    have hs₁cases:s₁=0∨ s₁=1:=by omega
    have hs₂cases:s₂=0∨ s₂=1:=by omega
    rcases hs₁cases with rfl | rfl <;> rcases hs₂cases with rfl | rfl <;>
      norm_num [fractionValue,Nat.cast_mul] <;> ring
  have hn:=normalizeFraction_output_spec B (if s₁=s₂ then 0 else 1)
    (n₁ * n₂) (d₁ * d₂) (by split_ifs <;> omega) hnn hdd
    (Nat.mul_pos hd₁pos hd₂pos)
  rintro σ ⟨hσs₁,hσn₁,hσd₁,hσs₂,hσn₂,hσd₂⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat:=c0 (Env.vars σ "left.n") (Env.vars σ "right.n"); let c2:Env:=Env.setVar σ "rat.n" c1; let c3:String→ Nat:=Env.vars c2; let c4:Nat:=c3 "left.d"; let c5:Nat:=c3 "right.d"; let c6:Nat:=c0 c4 c5; let c7:Env:=Env.setVar c2 "rat.d" c6; let c8:String→ Nat:=Env.vars c7; let c9:Nat:=c8 "left.s"; let c10:Nat:=c8 "right.s"; let c11:Prop:= @Eq Nat c9 c10; let c12:Prop:=Not c11; let c13:Nat→ Nat→ Nat:=Nat.add; let c14:Nat:=c0 d₁ d₂; let c15:Nat→ Nat:=c13 (c0 ((36:Nat)) (Nat.size c14)); let c16:Nat:=c15 ((64:Nat)); let c17:Env→ Prop:=FractionOutput (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul) (fractionValue s₁ n₁ d₁) (fractionValue s₂ n₂ d₂)); let c18:Env→ Prop:=(fun (x σ':Env) => c17 σ') σ; let c19:Env→ Prop:=fun (σ':Env) => And (Run B multiplyFraction σ σ' c16) (c18 σ'); let c20:Prop:= @Exists Env c19; let c21:Nat→ Env:=Env.setVar c7 "rat.s"; let c22:Env:=c21 ((0:Nat)); let c23:Env→ Nat→ Prop:=Run B normalizeFraction c22; let c24:Nat:=c15 ((16:Nat)); let c25:Nat:= @ite Nat (@Eq Nat s₁ s₂) (instDecidableEqNat s₁ s₂) ((0:Nat)) ((1:Nat)); let c26:Nat:=c0 n₁ n₂; let c27:Env→ Prop:=FractionOutput (fractionValue c25 c26 c14); let c28:Env→ Prop:=fun (σ':Env) => And (c23 σ' c24) (c27 σ'); let c29:String→ Nat:=Env.vars c22; let c30:Nat→ Nat:=c13 ((1:Nat)); let c31:Nat:=c30 (Expr.size (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))); let c32:Nat→ Nat:=c13 c31; let c33:Nat:=c30 (Expr.size (Expr.mul (Expr.var "left.d") (Expr.var "right.d"))); let c34:Nat→ Nat:=c13 c33; let c35:Nat→ Nat:=c13 (c30 (Cond.size (Cond.eq (Expr.var "left.s") (Expr.var "right.s")))); let c36:Nat:=c30 (Expr.size (Expr.lit ((0:Nat)))); let c37:Nat:=c35 c36; let c38:Nat:=c13 c37 c24; let c39:Nat:=c34 c38; let c40:Com:=Com.assign "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")); let c41:Com:=Com.assign "rat.s" (Expr.lit ((0:Nat))); let c42:Com:=Com.assign "rat.s" (Expr.lit ((1:Nat))); let c43:Com:=Com.ite (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42; let c44:Com:=Com.seq c43 normalizeFraction; let c45:Env:=c21 ((1:Nat)); let c46:Env→ Nat→ Prop:=Run B normalizeFraction c45; let c47:Env→ Prop:=fun (σ':Env) => And (c46 σ' c24) (c27 σ'); let c48:String→ Nat:=Env.vars c45; let c49:Nat:=c30 (Expr.size (Expr.lit ((1:Nat)))); let c50:Nat:=c35 c49; let c51:Nat:=c13 c50 c24; let c52:Nat:=c34 c51; @Or.casesOn c11 c12 (fun (x:Or c11 c12) => c20) (Classical.em c11) (fun (hcase:c11) => @Exists.casesOn Env c28 (fun (x:@Exists Env c28) => c20) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c26) (And (@Eq Nat (Env.vars σ_1 "rat.d") c14) (@Eq Nat (Env.vars σ_1 "rat.s") c25))) normalizeFraction (fun (x σ':Env) => c27 σ') c24 hn c22 ?_) fun (w:Env) (h:And (c23 w c24) (c27 w)) => @And.casesOn (c23 w c24) (c27 w) (fun (x:And (c23 w c24) (c27 w)) => c20) h fun (left:c23 w c24) (right:c27 w) => @Exists.intro Env c19 w (@And.intro (Run B multiplyFraction σ w c16) (c18 w) (RunStep.mono B multiplyFraction σ w (c32 c39) c16 (RunStep.seq B (Com.assign "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))) (Com.seq c40 c44) σ c2 w c31 c39 (RunStep.assign B σ "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.n") (Env.vars σ "left.n") (Env.vars σ "right.n") (RunStep.eval_var B σ "left.n" (?nAX_g5428_0_0_0)) (RunStep.eval_var B σ "right.n" (?nAX_g5428_0_0_1)) ?_)) (RunStep.seq B c40 c44 c2 c7 w c33 c38 (RunStep.assign B c2 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c6 (RunStep.eval_mul B c2 (Expr.var "left.d") (Expr.var "right.d") c4 c5 (RunStep.eval_var B c2 "left.d" (?nAX_g5428_0_0_2)) (RunStep.eval_var B c2 "right.d" (?nAX_g5428_0_0_3)) ?_)) (RunStep.seq B c43 normalizeFraction c7 c22 w c37 c24 (RunStep.ite_true B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42 c7 c22 c36 (RunStep.cond_eq_true B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c10 (RunStep.eval_var B c7 "left.s" (?nAX_g5428_0_0_4)) (RunStep.eval_var B c7 "right.s" (?nAX_g5428_0_0_5)) hcase) (RunStep.assign B c7 "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c7 (?nAX_g5428_0_0_6)))) left))) (?nAX_g5428_0_0_7)) ?_)) fun (hcase:c12) => @Exists.casesOn Env c47 (fun (x:@Exists Env c47) => c20) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (Env.vars σ_1 "rat.n") c26) (And (@Eq Nat (Env.vars σ_1 "rat.d") c14) (@Eq Nat (Env.vars σ_1 "rat.s") c25))) normalizeFraction (fun (x σ':Env) => c27 σ') c24 hn c45 ?_) fun (w:Env) (h:And (c46 w c24) (c27 w)) => @And.casesOn (c46 w c24) (c27 w) (fun (x:And (c46 w c24) (c27 w)) => c20) h fun (left:c46 w c24) (right:c27 w) => @Exists.intro Env c19 w (@And.intro (Run B multiplyFraction σ w c16) (c18 w) (RunStep.mono B multiplyFraction σ w (c32 c52) c16 (RunStep.seq B (Com.assign "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n"))) (Com.seq c40 c44) σ c2 w c31 c52 (RunStep.assign B σ "rat.n" (Expr.mul (Expr.var "left.n") (Expr.var "right.n")) c1 (RunStep.eval_mul B σ (Expr.var "left.n") (Expr.var "right.n") (Env.vars σ "left.n") (Env.vars σ "right.n") (RunStep.eval_var B σ "left.n" (?nAX_g5428_0_0_8)) (RunStep.eval_var B σ "right.n" (?nAX_g5428_0_0_9)) ?_)) (RunStep.seq B c40 c44 c2 c7 w c33 c51 (RunStep.assign B c2 "rat.d" (Expr.mul (Expr.var "left.d") (Expr.var "right.d")) c6 (RunStep.eval_mul B c2 (Expr.var "left.d") (Expr.var "right.d") c4 c5 (RunStep.eval_var B c2 "left.d" (?nAX_g5428_0_0_10)) (RunStep.eval_var B c2 "right.d" (?nAX_g5428_0_0_11)) ?_)) (RunStep.seq B c43 normalizeFraction c7 c45 w c50 c24 (RunStep.ite_false B (Cond.eq (Expr.var "left.s") (Expr.var "right.s")) c41 c42 c7 c45 c49 (RunStep.cond_eq_false B c7 (Expr.var "left.s") (Expr.var "right.s") c9 c10 (RunStep.eval_var B c7 "left.s" (?nAX_g5428_0_0_12)) (RunStep.eval_var B c7 "right.s" (?nAX_g5428_0_0_13)) hcase) (RunStep.assign B c7 "rat.s" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c7 h1))) left))) (?nAX_g5428_0_0_14)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g5428_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g5428_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
  all_goals simp_all

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

namespace Lax455465Proofs.RamProductSum

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

theorem value_at (xs ys:List ℚ≥0) (hlen:ys.length=xs.length) (i:ℕ) (hi:i < xs.length):
    (products xs ys)[i]'(by simpa only [products,List.length_ofFn] using hi) =
      xs[i]*ys[i]'(by omega):=by
  simp only [products,List.getElem_ofFn,List.getD_eq_get ys 0 (⟨i,by omega⟩:Fin ys.length)]
  rfl

end Lax455465Proofs.RamProductSum

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionVolume

def NoEvent {n:ℕ} (distance:Fin n→ ℚ) (a b:ℚ):Prop:=
  ∀ v, ¬ (a < distance v∧ distance v < b)

theorem edgePortion_nonneg (length base radius:ℚ) (hl:0≤ length):
    0≤ edgePortion length base radius:=le_min hl (le_max_right _ _)

theorem edgePortion_le (length base radius:ℚ):edgePortion length base radius≤ length:=
  min_le_left _ _

theorem edgePortion_monotone (length base a b:ℚ) (hab:a≤ b):
    edgePortion length base a≤ edgePortion length base b:=by
  exact min_le_min_left length (max_le_max_right 0 (sub_le_sub_right hab base))

theorem bounds {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed radius:ℚ) (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v):
    seed≤ volume capacity length distance seed radius∧
    volume capacity length distance seed radius≤ seed + weight capacity length:=by
  constructor
  · unfold volume
    have h:0≤ ∑ u, ∑ v,
        capacity u v * edgePortion (length u v) (distance u) radius:=
      Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
        mul_nonneg (hc u v) (edgePortion_nonneg _ _ _ (hl u v))))
    linarith
  · unfold volume weight
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro u _
    apply Finset.sum_le_sum
    intro v _
    exact mul_le_mul_of_nonneg_left (edgePortion_le _ _ _) (hc u v)

theorem monotone {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed a b:ℚ) (hc:∀ u v,0≤ capacity u v) (hab:a≤ b):
    volume capacity length distance seed a≤ volume capacity length distance seed b:=by
  unfold volume
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_mul_of_nonneg_left (edgePortion_monotone _ _ _ _ hab) (hc u v)

private theorem crossing_gain (length tail head a b:ℚ)
    (hab:a≤ b) (htail:tail≤ a) (hhead:b≤ head)
    (hlip:head - tail≤ length):
    edgePortion length tail b - edgePortion length tail a=b - a:=by
  have hba:0≤ b - tail:=by linarith
  have haa:0≤ a - tail:=by linarith
  have hbl:b - tail≤ length:=by linarith
  have hal:a - tail≤ length:=by linarith
  simp only [edgePortion,max_eq_left hba,max_eq_left haa,
    min_eq_right hbl,min_eq_right hal]
  ring

theorem gain {n:ℕ} (capacity length:Matrix n) (distance:Fin n→ ℚ)
    (seed a b:ℚ) (hc:∀ u v,0≤ capacity u v) (hab:a≤ b)
    (hevent:NoEvent distance a b)
    (hlip:∀ u v,distance v - distance u≤ length u v):
    (b - a) * boundary capacity distance b≤
      volume capacity length distance seed b - volume capacity length distance seed a:=by
  unfold volume boundary
  rw [add_sub_add_left_eq_sub, ← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  by_cases hcross:distance u < b∧ b≤ distance v
  · rw [if_pos hcross]
    have htail:distance u≤ a:=by
      by_contra h
      exact hevent u ⟨lt_of_not_ge h,hcross.1⟩
    have hgain:=crossing_gain (length u v) (distance u) (distance v)
      a b hab htail hcross.2 (hlip u v)
    have heq:capacity u v * edgePortion (length u v) (distance u) b -
        capacity u v * edgePortion (length u v) (distance u) a =
        (b - a) * capacity u v:=by
      rw [← mul_sub,hgain]
      ring
    exact le_of_eq heq.symm
  · rw [if_neg hcross,mul_zero]
    exact sub_nonneg.mpr (mul_le_mul_of_nonneg_left
      (edgePortion_monotone _ _ _ _ hab) (hc u v))

end Lax455465Proofs.RegionVolume

end

section

open scoped BigOperators

namespace Lax455465Proofs.FiniteRegionGrowth

theorem product_gain_left (a b A B width beta cut:ℚ)
    (ha:0≤ a) (hb:0≤ b) (hA:a≤ A) (hB:b≤ B)
    (hw:0≤ width) (hbeta:0≤ beta)
    (hcut:beta * A≤ cut) (hgain:width * cut≤ A - a):
    width * beta * (a * b)≤ A * B - a * b:=by
  have hfirst:width * beta * a≤ A - a:=by
    calc
      width * beta * a≤ width * beta * A:=
        mul_le_mul_of_nonneg_left hA (mul_nonneg hw hbeta)
      _=width * (beta * A):=by ring
      _≤ width * cut:=mul_le_mul_of_nonneg_left hcut hw
      _≤ A - a:=hgain
  have hsecond:=mul_le_mul_of_nonneg_right hfirst hb
  have hthird:=mul_le_mul_of_nonneg_left hB (ha.trans hA)
  nlinarith

theorem product_gain_right (a b A B width beta cut:ℚ)
    (ha:0≤ a) (hb:0≤ b) (hA:a≤ A) (hB:b≤ B)
    (hw:0≤ width) (hbeta:0≤ beta)
    (hcut:beta * B≤ cut) (hgain:width * cut≤ B - b):
    width * beta * (a * b)≤ A * B - a * b:=by
  simpa only [mul_comm b a,mul_comm B A] using
    product_gain_left b a B A width beta cut hb ha hB hA hw hbeta hcut hgain

theorem subdivided_gain (product radius:ℕ→ ℚ) (beta:ℚ) (k:ℕ)
    (hbeta:0≤ beta)
    (hwidth:∀ i < k,radius i≤ radius (i + 1))
    (hbase:∀ i < k,product 0≤ product i)
    (hgain:∀ i < k,
      (radius (i + 1) - radius i) * beta * product i≤
        product (i + 1) - product i):
    (radius k - radius 0) * beta * product 0≤ product k - product 0:=by
  have hsum:∑ i∈ Finset.range k,
      (radius (i + 1) - radius i) * beta * product 0≤
      ∑ i∈ Finset.range k, (product (i + 1) - product i):=by
    apply Finset.sum_le_sum
    intro i hi
    have hik:=Finset.mem_range.mp hi
    exact (mul_le_mul_of_nonneg_left (hbase i hik)
      (mul_nonneg (sub_nonneg.mpr (hwidth i hik)) hbeta)).trans (hgain i hik)
  simpa only [← Finset.sum_mul,Finset.sum_range_sub] using hsum

theorem doubled_cell (product radius:ℕ→ ℚ) (beta:ℚ) (k:ℕ)
    (hbeta:0≤ beta) (hproduct:0≤ product 0)
    (hwidth:∀ i < k,radius i≤ radius (i + 1))
    (hbase:∀ i < k,product 0≤ product i)
    (hgain:∀ i < k,
      (radius (i + 1) - radius i) * beta * product i≤
        product (i + 1) - product i)
    (hcell:1≤ (radius k - radius 0) * beta):
    2 * product 0≤ product k:=by
  have hgrowth:=subdivided_gain product radius beta k hbeta hwidth hbase hgain
  have hminimum:=mul_le_mul_of_nonneg_right hcell hproduct
  nlinarith

theorem exists_not_doubling (product:ℕ→ ℚ) (k:ℕ) (seed p:ℚ)
    (hseed:0 < seed) (hstart:seed ^ 2≤ product 0)
    (hbudget:product k≤ 4 * p ^ 2 * seed ^ 2)
    (hsteps:4 * p ^ 2 < (2:ℚ) ^ k):
    ∃ j < k,product (j + 1) < 2 * product j:=by
  by_contra h
  have hdouble:∀ j < k,2 * product j≤ product (j + 1):=by
    intro j hj
    exact le_of_not_gt (fun hlt => h ⟨j,hj,hlt⟩)
  have hgrowth:∀ j:ℕ,j≤ k→ (2:ℚ) ^ j * product 0≤ product j:=by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      calc
        (2:ℚ) ^ (j + 1) * product 0=2 * ((2:ℚ) ^ j * product 0):=by
          rw [pow_succ]
          ring
        _≤ 2 * product j:=mul_le_mul_of_nonneg_left (ih (by omega)) (by norm_num)
        _≤ product (j + 1):=hdouble j (by omega)
  have hpow:=hgrowth k le_rfl
  have hstart':=mul_le_mul_of_nonneg_left hstart (pow_nonneg (show (0:ℚ)≤ 2 by norm_num) k)
  have hexcess:=mul_lt_mul_of_pos_right hsteps (sq_pos_of_pos hseed)
  linarith

end Lax455465Proofs.FiniteRegionGrowth

end

section

open scoped BigOperators

namespace Lax455465Proofs.RegionInterval

open RegionVolume

def productVolume {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius:ℚ):ℚ:=
  volume capacity length outDistance seed radius *
    volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed radius

private theorem transpose_weight {n:ℕ} (capacity length:Matrix n):
    weight (fun u v => capacity v u) (fun u v => length v u)=weight capacity length:=by
  unfold weight
  rw [Finset.sum_comm]

theorem budget {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed):
    seed ^ 2≤ productVolume capacity length outDistance inDistance seed radius∧
    productVolume capacity length outDistance inDistance seed radius≤
      (seed + weight capacity length) ^ 2:=by
  obtain ⟨houtLo,houtHi⟩:=bounds capacity length outDistance seed radius hc hl
  obtain ⟨hinLo,hinHi⟩:=bounds (fun u v => capacity v u)
    (fun u v => length v u) inDistance seed radius (fun u v => hc v u) (fun u v => hl v u)
  rw [transpose_weight] at hinHi
  unfold productVolume
  constructor
  · simpa only [pow_two] using mul_le_mul houtLo hinLo hseed (hseed.trans houtLo)
  · simpa only [pow_two] using mul_le_mul houtHi hinHi
      (hseed.trans hinLo) (hseed.trans houtLo |>.trans houtHi)

theorem normalized_budget {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed radius p:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hp:1≤ p) (hweight:weight capacity length≤ p * seed):
    productVolume capacity length outDistance inDistance seed radius≤ 4 * p ^ 2 * seed ^ 2:=by
  have hweightNN:0≤ weight capacity length:=by
    exact Finset.sum_nonneg (fun u _ => Finset.sum_nonneg (fun v _ =>
      mul_nonneg (hc u v) (hl u v)))
  have hseedLe:seed≤ p * seed:=by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hp hseed
  have htotal:seed + weight capacity length≤ 2 * p * seed:=by linarith
  have hsq:=mul_self_le_mul_self (add_nonneg hseed hweightNN) htotal
  calc
    productVolume capacity length outDistance inDistance seed radius≤
        (seed + weight capacity length) ^ 2:=(budget _ _ _ _ _ _ hc hl hseed).2
    _≤ (2 * p * seed) ^ 2:=by simpa only [pow_two] using hsq
    _=4 * p ^ 2 * seed ^ 2:=by ring

theorem monotone {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hab:a≤ b):
    productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b:=by
  have hout:=RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hin:=RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  have hinLo:=(bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtLo:=(bounds capacity length outDistance seed b hc hl).1
  exact mul_le_mul hout hin (hseed.trans hinLo) (hseed.trans houtLo)

theorem gain {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b beta:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (hab:a≤ b) (hbeta:0≤ beta)
    (houtEvent:NoEvent outDistance a b) (hinEvent:NoEvent inDistance a b)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u)
    (hbad:beta * volume capacity length outDistance seed b≤
        boundary capacity outDistance b∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed b≤ boundary (fun u v => capacity v u) inDistance b):
    (b - a) * beta * productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b -
        productVolume capacity length outDistance inDistance seed a:=by
  have houtLo:=(bounds capacity length outDistance seed a hc hl).1
  have hinLo:=(bounds (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a (fun u v => hc v u) (fun u v => hl v u)).1
  have houtMono:=RegionVolume.monotone capacity length outDistance seed a b hc hab
  have hinMono:=RegionVolume.monotone (fun u v => capacity v u) (fun u v => length v u)
    inDistance seed a b (fun u v => hc v u) hab
  unfold productVolume
  rcases hbad with houtBad | hinBad
  · exact FiniteRegionGrowth.product_gain_left _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta houtBad
      (RegionVolume.gain capacity length outDistance seed a b hc hab houtEvent houtLip)
  · exact FiniteRegionGrowth.product_gain_right _ _ _ _ _ _ _
      (hseed.trans houtLo) (hseed.trans hinLo) houtMono hinMono
      (sub_nonneg.mpr hab) hbeta hinBad
      (RegionVolume.gain (fun u v => capacity v u) (fun u v => length v u)
        inDistance seed a b (fun u v => hc v u) hab hinEvent hinLip)

end Lax455465Proofs.RegionInterval

end

section

set_option backward.isDefEq.respectTransparency false

namespace Lax455465Proofs.RegionThresholds

def events {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):Finset ℚ:=
  insert a (insert b ((Finset.univ.image outDistance ∪ Finset.univ.image inDistance).filter
    (fun r => a≤ r∧ r≤ b)))

def candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):List ℚ:=
  (events outDistance inDistance a b).sort

theorem left_mem {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    a∈ events outDistance inDistance a b:=by simp [events]

theorem right_mem {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    b∈ events outDistance inDistance a b:=by simp [events]

theorem bounds {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    ∀ r∈ events outDistance inDistance a b,a≤ r∧ r≤ b:=by
  intro r hr
  simp only [events,Finset.mem_insert,Finset.mem_filter] at hr
  rcases hr with rfl | rfl | ⟨_,h⟩
  · exact ⟨le_rfl,hab⟩
  · exact ⟨hab,le_rfl⟩
  · exact h

private theorem no_member_between (s:Finset ℚ) (j:ℕ) (hj:j + 1 < s.sort.length)
    (r:ℚ) (hr:r∈ s):
    ¬ (s.sort.get ⟨j,by omega⟩ < r∧ r < s.sort.get ⟨j + 1,hj⟩):=by
  obtain ⟨i,hi⟩:=List.mem_iff_get.mp ((Finset.mem_sort (·≤ ·)).mpr hr)
  have hmono:=(Finset.sortedLT_sort s).monotone
  rintro ⟨hlow,hhigh⟩
  by_cases hle:i.val≤ j
  · have h:=hmono (show i≤ ⟨j,by omega⟩ from hle)
    rw [hi] at h
    exact (not_lt_of_ge h) hlow
  · have h:=hmono (show (⟨j + 1,hj⟩:Fin s.sort.length)≤ i by
      change j + 1≤ i.val
      omega)
    rw [hi] at h
    exact (not_lt_of_ge h) hhigh

theorem no_event {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (hab:a≤ b) (j:ℕ) (hj:j + 1 < (candidates outDistance inDistance a b).length):
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j,by omega⟩ < outDistance v∧
      outDistance v < (candidates outDistance inDistance a b).get ⟨j + 1,hj⟩))∧
    (∀ v, ¬ ((candidates outDistance inDistance a b).get ⟨j,by omega⟩ < inDistance v∧
      inDistance v < (candidates outDistance inDistance a b).get ⟨j + 1,hj⟩)):=by
  change j + 1 < (events outDistance inDistance a b).sort.length at hj
  have hstart:=(bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨j,by omega⟩))).1
  have hend:=(bounds outDistance inDistance a b hab _
    ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨j + 1,hj⟩))).2
  constructor
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (outDistance v) ?_ h
    simp only [events,Finset.mem_insert,Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),
      ⟨hstart.trans h.1.le,h.2.le.trans hend⟩⟩
  · intro v h
    apply no_member_between (events outDistance inDistance a b) j hj (inDistance v) ?_ h
    simp only [events,Finset.mem_insert,Finset.mem_filter]
    right; right
    exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,rfl⟩),
      ⟨hstart.trans h.1.le,h.2.le.trans hend⟩⟩

def radius {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (i:ℕ):ℚ:=
  (candidates outDistance inDistance a b).getD i b

theorem length_pos {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ):
    0 < (candidates outDistance inDistance a b).length:=by
  unfold candidates
  rw [Finset.length_sort]
  exact Finset.card_pos.mpr ⟨a,left_mem outDistance inDistance a b⟩

theorem radius_eq_get {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (i:Fin (candidates outDistance inDistance a b).length):
    radius outDistance inDistance a b i.val =
      (candidates outDistance inDistance a b).get i:=
  List.getD_eq_get _ _ i

theorem radius_first {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    radius outDistance inDistance a b 0=a:=by
  let i:Fin (candidates outDistance inDistance a b).length:=
    ⟨0,length_pos outDistance inDistance a b⟩
  change radius outDistance inDistance a b i.val=a
  rw [radius_eq_get]
  obtain ⟨j,hj⟩:=List.mem_iff_get.mp
    ((Finset.mem_sort (·≤ ·)).mpr (left_mem outDistance inDistance a b))
  apply le_antisymm
  · have h:=(Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show i≤ j by exact Nat.zero_le _)
    exact h.trans_eq hj
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ i))).1

theorem radius_last {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ) (hab:a≤ b):
    radius outDistance inDistance a b ((candidates outDistance inDistance a b).length - 1)=b:=by
  have hpos:=length_pos outDistance inDistance a b
  let i:Fin (candidates outDistance inDistance a b).length:=
    ⟨(candidates outDistance inDistance a b).length - 1,by omega⟩
  change radius outDistance inDistance a b i.val=b
  rw [radius_eq_get]
  obtain ⟨j,hj⟩:=List.mem_iff_get.mp
    ((Finset.mem_sort (·≤ ·)).mpr (right_mem outDistance inDistance a b))
  apply le_antisymm
  · exact (bounds outDistance inDistance a b hab _
      ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ i))).2
  · have h:=(Finset.sortedLT_sort (events outDistance inDistance a b)).monotone
      (show j≤ i by change j.val≤ _; exact Nat.le_sub_one_of_lt j.isLt)
    exact (le_of_eq hj.symm).trans h

theorem radius_monotone {n:ℕ} (outDistance inDistance:Fin n→ ℚ) (a b:ℚ)
    (j:ℕ) (hj:j + 1 < (candidates outDistance inDistance a b).length):
    radius outDistance inDistance a b j≤ radius outDistance inDistance a b (j + 1):=by
  rw [radius_eq_get outDistance inDistance a b ⟨j,by omega⟩,
    radius_eq_get outDistance inDistance a b ⟨j + 1,hj⟩]
  exact (Finset.sortedLT_sort _).monotone (show (⟨j,by omega⟩:Fin _)≤ ⟨j + 1,hj⟩ by
    change j≤ j + 1
    omega)

end Lax455465Proofs.RegionThresholds

end

section

namespace Lax455465Proofs.RegionCell

open RegionVolume RegionInterval

theorem doubles {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed a b beta:ℚ)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0≤ seed) (ha:0≤ a) (hab:a≤ b) (hbeta:0≤ beta)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u)
    (hbad:∀ r∈ RegionThresholds.events outDistance inDistance a b,0 < r→
      beta * volume capacity length outDistance seed r≤ boundary capacity outDistance r∨
      beta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r≤
        boundary (fun u v => capacity v u) inDistance r)
    (hcell:1≤ (b - a) * beta):
    2 * productVolume capacity length outDistance inDistance seed a≤
      productVolume capacity length outDistance inDistance seed b:=by
  let radii:=RegionThresholds.radius outDistance inDistance a b
  let candidates:=RegionThresholds.candidates outDistance inDistance a b
  let k:=candidates.length - 1
  let values:=fun i => productVolume capacity length outDistance inDistance seed (radii i)
  have hpos:0 < candidates.length:=RegionThresholds.length_pos outDistance inDistance a b
  have hindex:∀ i < k,i + 1 < candidates.length:=by
    intro i hi
    dsimp [k] at hi
    omega
  have hfirst:radii 0=a:=RegionThresholds.radius_first outDistance inDistance a b hab
  have hlast:radii k=b:=RegionThresholds.radius_last outDistance inDistance a b hab
  have hwidth:∀ i < k,radii i≤ radii (i + 1):=by
    intro i hi
    exact RegionThresholds.radius_monotone outDistance inDistance a b i (hindex i hi)
  have hbase:∀ i < k,values 0≤ values i:=by
    intro i hi
    have hii:i < candidates.length:=by have h:=hindex i hi; omega
    have haRi:a≤ radii i:=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩]
      exact (RegionThresholds.bounds outDistance inDistance a b hab _
        ((Finset.mem_sort (·≤ ·)).mp (List.get_mem _ ⟨i,hii⟩))).1
    dsimp [values]
    rw [hfirst]
    exact RegionInterval.monotone capacity length outDistance inDistance seed a _ hc hl hseed haRi
  have hgain:∀ i < k,
      (radii (i + 1) - radii i) * beta * values i≤ values (i + 1) - values i:=by
    intro i hi
    have hinext:=hindex i hi
    have hii:i < candidates.length:=by omega
    have houtIn:=RegionThresholds.no_event outDistance inDistance a b hab i hinext
    have houtEvent:NoEvent outDistance (radii i) (radii (i + 1)):=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact houtIn.1
    have hinEvent:NoEvent inDistance (radii i) (radii (i + 1)):=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i,hii⟩,
        RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact houtIn.2
    have hmem:radii (i + 1)∈ RegionThresholds.events outDistance inDistance a b:=by
      dsimp only [radii]
      rw [RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩]
      exact (Finset.mem_sort (·≤ ·)).mp (List.get_mem _ _)
    have hpositive:0 < radii (i + 1):=by
      have hstrict:=(Finset.sortedLT_sort (RegionThresholds.events outDistance inDistance a b))
        (show (⟨0,hpos⟩:Fin _) < ⟨i + 1,hinext⟩ by change 0 < i + 1; omega)
      have hr0:=RegionThresholds.radius_eq_get outDistance inDistance a b ⟨0,hpos⟩
      have hr1:=RegionThresholds.radius_eq_get outDistance inDistance a b ⟨i + 1,hinext⟩
      have haR:a < radii (i + 1):=by
        calc
          a=radii 0:=hfirst.symm
          _=(RegionThresholds.candidates outDistance inDistance a b).get ⟨0,hpos⟩:=hr0
          _ < (RegionThresholds.candidates outDistance inDistance a b).get ⟨i + 1,hinext⟩:=hstrict
          _=radii (i + 1):=hr1.symm
      exact ha.trans_lt haR
    exact RegionInterval.gain capacity length outDistance inDistance seed (radii i) (radii (i + 1))
      beta hc hl hseed (hwidth i hi) hbeta houtEvent hinEvent houtLip hinLip
      (hbad _ hmem hpositive)
  have hvalues:0≤ values 0:=by
    have hlow:=(RegionInterval.budget capacity length outDistance inDistance seed (radii 0)
      hc hl hseed).1
    exact (sq_nonneg seed).trans hlow
  have h:=FiniteRegionGrowth.doubled_cell values radii beta k hbeta hvalues hwidth hbase hgain
    (by simpa only [hfirst,hlast] using hcell)
  simpa only [values,hfirst,hlast] using h

end Lax455465Proofs.RegionCell

end

section

namespace Lax455465Proofs.RegionBudget

theorem steps_pos (p:ℕ):0 < steps p:=by unfold steps; omega

theorem exceeds_budget (p:ℕ) (hp:0 < p):
    4 * (p:ℚ) ^ 2 < (2:ℚ) ^ steps p:=by
  have hupperNat:p < 2 ^ (Nat.log2 p + 1):=by
    simpa only [Nat.log2_eq_log_two] using Nat.lt_pow_succ_log_self Nat.one_lt_two p
  have hupper:(p:ℚ) < (2:ℚ) ^ (Nat.log2 p + 1):=by exact_mod_cast hupperNat
  have hpq:0 < (p:ℚ):=by exact_mod_cast hp
  have hpow:0 < (2:ℚ) ^ (Nat.log2 p + 1):=pow_pos (by norm_num) _
  have hsquare:(p:ℚ) ^ 2 < ((2:ℚ) ^ (Nat.log2 p + 1)) ^ 2:=by nlinarith
  have hid:(2:ℚ) ^ steps p=4 * ((2:ℚ) ^ (Nat.log2 p + 1)) ^ 2:=by
    rw [show steps p=(Nat.log2 p + 1) * 2 + 2 by unfold steps; omega,
      pow_add,pow_mul]
    norm_num
    ring
  rw [hid]
  nlinarith

end Lax455465Proofs.RegionBudget

end

section

namespace Lax455465Proofs.RegionSearch

open RegionVolume RegionInterval

private theorem grid_last (k:ℕ) (delta:ℚ) (hk:0 < k):grid k delta k=delta:=by
  have hkq:(k:ℚ) ≠ 0:=by exact_mod_cast (Nat.ne_of_gt hk)
  simp [grid,hkq]

private theorem grid_nonneg (k:ℕ) (delta:ℚ) (j:ℕ) (hd:0≤ delta):
    0≤ grid k delta j:=by unfold grid; positivity

private theorem grid_mono (k:ℕ) (delta:ℚ) (j:ℕ) (hd:0≤ delta):
    grid k delta j≤ grid k delta (j + 1):=by
  unfold grid
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
  exact mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ j) hd

private theorem grid_width (k:ℕ) (delta:ℚ) (j:ℕ)
    (hk:0 < k) (hd:0 < delta):
    (grid k delta (j + 1) - grid k delta j) * slope k delta=1:=by
  have hkq:(k:ℚ) ≠ 0:=by exact_mod_cast (Nat.ne_of_gt hk)
  unfold grid slope
  push_cast
  field_simp [hkq,ne_of_gt hd]
  ring

private theorem grid_le (k:ℕ) (delta:ℚ) (j:ℕ)
    (hk:0 < k) (hd:0≤ delta) (hj:j≤ k):grid k delta j≤ delta:=by
  calc
    grid k delta j≤ grid k delta k:=by
      unfold grid
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg k)
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast hj) hd
    _=delta:=grid_last k delta hk

theorem event_mem_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ)
    (k:ℕ) (delta:ℚ) (j:ℕ) (r:ℚ) (hk:0 < k) (hd:0≤ delta) (hj:j < k)
    (hr:r∈ RegionThresholds.events outDistance inDistance (grid k delta j) (grid k delta (j+1))):
    r∈ candidates outDistance inDistance k delta:=by
  have hb:=RegionThresholds.bounds outDistance inDistance _ _ (grid_mono k delta j hd) r hr
  have hnonnegative:0≤ r:=(grid_nonneg k delta j hd).trans hb.1
  have hdelta:r≤ delta:=hb.2.trans (grid_le k delta (j+1) hk hd (by omega))
  simp only [RegionThresholds.events,Finset.mem_insert,Finset.mem_filter,Finset.mem_union,Finset.mem_image] at hr
  simp only [candidates,List.mem_append,List.mem_map,List.mem_ofFn]
  rcases hr with rfl | rfl | ⟨(⟨v,hv,rfl⟩ | ⟨v,hv,rfl⟩),hcell⟩
  · exact Or.inl (Or.inl ⟨j,List.mem_range.mpr (by omega),rfl⟩)
  · exact Or.inl (Or.inl ⟨j+1,List.mem_range.mpr (by omega),rfl⟩)
  · exact Or.inl (Or.inr ⟨v,by rw [max_eq_left hnonnegative,min_eq_right hdelta]⟩)
  · exact Or.inr ⟨v,by rw [max_eq_left hnonnegative,min_eq_right hdelta]⟩

theorem exists_good {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0 < seed) (hd:0 < delta) (hp:0 < p)
    (hweight:weight capacity length≤ (p:ℚ) * seed)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u):
    ∃ r∈ candidates outDistance inDistance (RegionBudget.steps p) delta,
      0 < r∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r:=by
  let k:=RegionBudget.steps p
  let values:=fun j => productVolume capacity length outDistance inDistance seed (grid k delta j)
  have hk:0 < k:=RegionBudget.steps_pos p
  have hpq:(1:ℚ)≤ p:=by exact_mod_cast hp
  have hstart:seed ^ 2≤ values 0:=
    (RegionInterval.budget capacity length outDistance inDistance seed _ hc hl hseed.le).1
  have hbudget:values k≤ 4 * (p:ℚ) ^ 2 * seed ^ 2:=
    RegionInterval.normalized_budget capacity length outDistance inDistance seed _ p
      hc hl hseed.le hpq hweight
  obtain ⟨j,hj,hnotDouble⟩:=FiniteRegionGrowth.exists_not_doubling values k seed p
    hseed hstart hbudget (RegionBudget.exceeds_budget p hp)
  by_contra h
  have hbad:∀ r∈ RegionThresholds.events outDistance inDistance
      (grid k delta j) (grid k delta (j + 1)),0 < r→
      slope k delta * volume capacity length outDistance seed r≤ boundary capacity outDistance r∨
      slope k delta * volume (fun u v => capacity v u) (fun u v => length v u) inDistance seed r≤
        boundary (fun u v => capacity v u) inDistance r:=by
    intro r hr hpos
    have hmem:r∈ candidates outDistance inDistance k delta:=by
      exact event_mem_candidates outDistance inDistance k delta j r hk hd.le hj hr
    have hfail:¬ Good capacity length outDistance inDistance seed (slope k delta) direction r:=by
      intro hg
      exact h ⟨r,hmem,hpos,hg⟩
    cases hdir:direction r with
    | false =>
      right
      exact le_of_not_ge (by simpa [Good,selectedBoundary,selectedVolume,hdir] using hfail)
    | true =>
      left
      exact le_of_not_ge (by simpa [Good,selectedBoundary,selectedVolume,hdir] using hfail)
  have hdoubled:=RegionCell.doubles capacity length outDistance inDistance seed
    (grid k delta j) (grid k delta (j + 1)) (slope k delta) hc hl hseed.le
    (grid_nonneg k delta j hd.le) (grid_mono k delta j hd.le)
    (by unfold slope; positivity) houtLip hinLip hbad
    (by rw [grid_width k delta j hk hd])
  exact (not_le_of_gt hnotDouble) hdoubled

theorem search_correct {n:ℕ} (capacity length:Matrix n)
    (outDistance inDistance:Fin n→ ℚ) (seed delta:ℚ) (p:ℕ)
    (direction:ℚ→ Bool)
    (hc:∀ u v,0≤ capacity u v) (hl:∀ u v,0≤ length u v)
    (hseed:0 < seed) (hd:0 < delta) (hp:0 < p)
    (hweight:weight capacity length≤ (p:ℚ) * seed)
    (houtLip:∀ u v,outDistance v - outDistance u≤ length u v)
    (hinLip:∀ u v,inDistance v - inDistance u≤ length v u):
    ∃ r,search capacity length outDistance inDistance seed delta p direction=some r∧
      r∈ candidates outDistance inDistance (RegionBudget.steps p) delta∧
      0 < r∧ Good capacity length outDistance inDistance seed
        (slope (RegionBudget.steps p) delta) direction r:=by
  obtain ⟨r,hr,hpositive,hgood⟩:=exists_good capacity length outDistance inDistance
    seed delta p direction hc hl hseed hd hp hweight houtLip hinLip
  cases hs:search capacity length outDistance inDistance seed delta p direction with
  | none =>
    unfold search at hs
    have hnone:=List.find?_eq_none.mp hs r hr
    simp only [decide_eq_true_eq] at hnone
    exact False.elim (hnone ⟨hpositive,hgood⟩)
  | some result =>
    refine ⟨result,rfl,List.mem_of_find?_eq_some hs, ?_⟩
    have hfound:=List.find?_some hs
    simpa only [decide_eq_true_eq] using hfound

end Lax455465Proofs.RegionSearch

end

section

set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Lax455465Proofs.RegionLoop

open Lax455465.RationalEncoding RegionVolume RegionCharging RegionSelection RationalDistances

theorem capacity_nonnegative {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    ∀ u v,0≤ capacity I active u v:=by
  intro u v
  unfold capacity
  split_ifs <;> positivity

theorem residual_cost_le {n:ℕ} (I:RationalInstance n) (d:Distance n)
    (active:Finset (Fin n)) (hd:Nonnegative d):
    weight (capacity I active) d≤ weight (fun u v => (I.capacity u v:ℚ)) d:=by
  apply Finset.sum_le_sum
  intro u _
  apply Finset.sum_le_sum
  intro v _
  apply mul_le_mul_of_nonneg_right _ (hd u v)
  unfold capacity
  split_ifs
  · exact le_rfl
  · exact NNRat.coe_nonneg _

end Lax455465Proofs.RegionLoop

end

section

namespace Lax455465Proofs.MetricCostData

open Lax455465.RationalEncoding DirectedFlowLP MetricMatrix
open scoped BigOperators NNRat

theorem products_eq {n:ℕ} (a b:Matrix n):
    RamProductSum.products (values a) (values b)=values (fun u v => a u v*b u v):=by
  apply List.ext_getElem
  · simp only [RamProductSum.products,List.length_ofFn,length_values]
  · intro i hi hj
    have he:i < n*n:=by simpa only [RamProductSum.products,List.length_ofFn,length_values] using hi
    rw [RamProductSum.value_at (values a) (values b) (by simp) i (by simpa using he)]
    simp only [values,List.getElem_ofFn]

end Lax455465Proofs.MetricCostData

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

theorem mass_height {n:ℕ} (q:Query n) (H:ℕ) (hb:RegionQueryHeight.Bounds q H) (b:Bool):
    LpInputSize.Height (2^H) (BallMassData.mass q.weights (distance q b) q.radius:ℚ):=by
  have hh:=hb.massPrefixBound b (RamMaskedSum.coefficients (List.ofFn q.weights) (BallMassData.mask (distance q b) q.radius)).length
  simpa only [List.take_length,BallMassData.mass] using hh

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

theorem coe_candidates {n:ℕ} (outDistance inDistance:Fin n→ ℚ≥0) (k:ℕ) (delta:ℚ≥0):
    (candidates outDistance inDistance k delta).map (fun q:ℚ≥0 => (q:ℚ)) =
      RegionSearch.candidates (fun v => (outDistance v:ℚ)) (fun v => (inDistance v:ℚ)) k delta:=by
  simp only [candidates,List.map_append,List.map_map,List.map_ofFn,RegionSearch.candidates,Function.comp_apply,NNRat.coe_min]
  congr 2
  · apply List.map_congr_left
    intro j hj
    simp only [Function.comp_apply,NNRat.coe_mul,NNRat.coe_div,NNRat.coe_natCast,RegionSearch.grid]
    ring
  · congr 1
    funext v
    simp [max_eq_left (outDistance v).coe_nonneg]
  · funext v
    simp [max_eq_left (inDistance v).coe_nonneg]

end Lax455465Proofs.RadiusData

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

end Lax455465Proofs.RamFind

end

section

namespace Lax455465Proofs.RadiusSearchData
open RegionQueryData
open scoped NNRat

theorem index_values (radii:List ℚ≥0):
    (List.range radii.length).map (fun i => radii.getD i 0)=radii:=by
  apply List.ext_getElem
  · simp
  · intro i h₁ h₂
    simp only [List.getElem_map,List.getElem_range,
      List.getD_eq_get radii 0 (⟨i,h₂⟩:Fin radii.length),List.get_eq_getElem]

theorem first_value {n:ℕ} (q:Query n) (radii:List ℚ≥0):
    (RamFind.first (predicate q radii) radii.length).map (fun i => radii.getD i 0) =
      radii.find? (fun r => accepted (atRadius q r)):=by
  have h:=List.find?_map (p:=fun r => accepted (atRadius q r))
    (f:=fun i => radii.getD i 0) (l:=List.range radii.length)
  unfold RamFind.first RadiusSearchData.predicate
  simpa only [index_values,Function.comp_def] using h.symm

theorem search_value {n:ℕ} (q:Query n) (delta:ℚ≥0) (p:ℕ)
    (hb:(q.beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta):
    ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).find?
      (fun r => accepted (atRadius q r))).map (fun r:ℚ≥0 => (r:ℚ)) =
      RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
        (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) q.seed delta p (direction q):=by
  unfold RegionSearch.search
  rw [← RadiusData.coe_candidates,List.find?_map]
  congr 2
  funext r
  simp only [Function.comp_def,accepted,atRadius,hb]
  rfl

end Lax455465Proofs.RadiusSearchData

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

set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionChoice
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRegionSetup RegionQueryData
open scoped NNRat

theorem first_of_search {n:ℕ} (q:Query n) (delta:ℚ≥0) (p:ℕ)
    (hb:(q.beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (r:ℚ) (hs:RegionSearch.search (MetricMatrix.rational q.capacity) (MetricMatrix.rational q.length)
      (fun v => (q.outDistance v:ℚ)) (fun v => (q.inDistance v:ℚ)) q.seed delta p (direction q)=some r):
    ∃ i,RamFind.first (RadiusSearchData.predicate q
        (RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta))
        (RegionBudget.steps p+1+2*n)=some i∧
      ((RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta).getD i 0:ℚ)=r:=by
  let radii:=RadiusData.candidates q.outDistance q.inDistance (RegionBudget.steps p) delta
  have he:=congrArg (fun o:Option ℚ≥0 => o.map (fun a:ℚ≥0 => (a:ℚ)))
    (RadiusSearchData.first_value q radii)
  rw [RadiusSearchData.search_value q delta p hb,hs] at he
  cases hi:RamFind.first (RadiusSearchData.predicate q radii) radii.length with
  | none => simp only [hi,Option.map_none] at he; cases he
  | some i =>
    refine ⟨i,?_,?_⟩
    · simpa only [radii,RadiusData.length_candidates] using hi
    · simpa only [hi,Option.map_some,Option.some.injEq] using he

set_option maxHeartbeats 0 in

theorem command_spec (B M H:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0)
    (capacity length:MetricMatrix.Matrix n) (root:Fin n) (seed beta delta:ℚ≥0) (p:ℕ)
    (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ i, ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (query weights capacity length root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (r:ℚ) (hs:RegionSearch.search (MetricMatrix.rational capacity) (MetricMatrix.rational length)
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
      (RegionSelection.direction (fun v => (weights v:ℚ)) (fun v => (length root v:ℚ))
        (fun v => (length v root:ℚ)))=some r):
    Spec B (fun σ => Input weights capacity length root seed beta delta (RegionBudget.steps p) σ∧
      Room n (RegionBudget.steps p+1+2*n) σ) RamRegionSetup.command
      (fun _ τ => ∃ rn:ℚ≥0, (rn:ℚ)=r∧ rn∈RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta∧
        τ.vars "find.found"=1∧
        RamRadiusSearch.Answer (RadiusSearchData.atRadius (query weights capacity length root seed beta) rn) τ)
      (RamRegionSetup.cost n (RegionBudget.steps p) M H):=by
  let q:=query weights capacity length root seed beta
  let radii:=RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta
  obtain ⟨i,hi,hr⟩:=first_of_search q delta p hbeta r hs
  change RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta) radii)
    (RegionBudget.steps p+1+2*n)=some i at hi
  have hlen:radii.length=RegionBudget.steps p+1+2*n:=RadiusData.length_candidates _ _ _ _
  intro σ hσ
  obtain ⟨τ,rr,pr⟩:=RamRegionSetup.command_spec B M H weights capacity length root seed beta delta (RegionBudget.steps p)
    hk hB hquery hindex hvertex hradius hl hd hu hb σ hσ
  refine ⟨τ,rr,radii.getD i 0,hr,?_,?_,?_⟩
  · have hi':i< radii.length:=by
      apply (RamFind.first_some (RadiusSearchData.predicate (query weights capacity length root seed beta) radii) radii.length i (by rwa [hlen])).1
    rw [List.getD_eq_get radii 0 (⟨i,hi'⟩:Fin radii.length),List.get_eq_getElem]
    exact List.getElem_mem hi'
  · have hm:=pr.2.1
    change RamFind.Matches (RamFind.first (RadiusSearchData.predicate (query weights capacity length root seed beta) radii)
      (RegionBudget.steps p+1+2*n)) τ at hm
    simp only [RamFind.Matches,hi] at hm
    exact hm.1
  · have hp:=pr.2.2
    change RamSelectedRegion.Selected (query weights capacity length root seed beta) radii τ at hp
    simpa only [RamSelectedRegion.Selected,hlen,hi] using hp

end Lax455465Proofs.RamRegionChoice

end

section

namespace Lax455465Proofs.RamBooleanVector
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState RamBooleanArithmetic
open scoped NNRat

def Context {n:ℕ} (leftArray rightArray:String) (a b:Fin n→ Bool) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags a)) leftArray σ∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags b)) rightArray σ

theorem entry_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (leftArray rightArray:String)
    (a b:Fin n→ Bool) (v:Fin n) (h2:2< B) (hindex:2*n+2< B):
    Spec B (fun σ => Context leftArray rightArray a b σ∧ σ.vars "mask.i"=v.val)
      (entry mode leftArray rightArray) (fun _ τ => Context leftArray rightArray a b τ∧
        FractionOutput (bit (flag mode (a v) (b v)):ℚ) τ) 50:=by
  have hnum (c:Bool):(bit c).num< B:=by cases c <;> simp [bit] <;> omega
  have hden (c:Bool):(bit c).den=1:=by cases c <;> simp [bit]
  have hget (c:Fin n→ Bool):(MaskedMassData.flags c)[v.val]'(by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt)=bit (c v):=by
    simp [MaskedMassData.flags,bit]
  rintro σ ⟨hσ,hidx⟩
  obtain ⟨ν,ra,pa⟩:=RamUnsignedBuffer.read_spec B leftArray "mask.i" (MaskedMassData.flags a) v.val
    (by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt) h2 (by omega)
    (by rw [hget]; exact hnum _) (by rw [hget,hden]; omega) (by decide) σ ⟨hσ.2.1,hidx⟩
  obtain ⟨μ,rl,pl⟩:=RamUnsignedArithmetic.copy_spec B (bit (a v)) "left" (by omega) (hnum _) (by rw [hden]; omega) (by decide) ν
    (by simpa only [hget] using pa.1)
  have rprior:=ra.seq rl
  obtain ⟨ξ,rb,pb⟩:=RamUnsignedBuffer.read_spec B rightArray "mask.i" (MaskedMassData.flags b) v.val
    (by simpa only [MaskedMassData.flags,List.length_ofFn] using v.isLt) h2 (by omega)
    (by rw [hget]; exact hnum _) (by rw [hget,hden]; omega) (by decide) μ
    ⟨by simpa only [Prefix,rprior.frame_arr rightArray (by change rightArray∉([]:List String); simp)] using hσ.2.2,
      (rprior.frame_var "mask.i" (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)).trans hidx⟩
  obtain ⟨η,rr,pr⟩:=RamUnsignedArithmetic.copy_spec B (bit (b v)) "right" (by omega) (hnum _) (by rw [hden]; omega) (by decide) ξ
    (by simpa only [hget] using pb.1)
  have ple:η.vars "left.s"=0∧ η.vars "left.n"=(bit (a v)).num∧ η.vars "left.d"=1:=by
    have run:=rb.seq rr
    simpa only [String.reduceAppend,hden,run.frame_var "left.s" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),run.frame_var "left.n" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),run.frame_var "left.d" (by dsimp [RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)] using pl
  obtain ⟨τ,rc,pc⟩:=RamBooleanArithmetic.command_spec B mode (a v) (b v) (by omega) η
    ⟨ple.1,ple.2.1,ple.2.2,by simpa only [String.reduceAppend,hden] using pr⟩
  have run:=ra.seq (rl.seq (rb.seq (rr.seq rc)))
  refine ⟨τ,run,?_,pc⟩
  simpa only [Context,Prefix,run.frame_var "metric.n" (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp),
    run.frame_arr leftArray (by change leftArray∉([]:List String); simp),run.frame_arr rightArray (by change rightArray∉([]:List String); simp)] using hσ

set_option maxHeartbeats 0 in

theorem command_spec (B:ℕ) {n:ℕ} (mode:Option Bool) (leftArray rightArray target:String)
    (a b:Fin n→ Bool) (h2:2< B) (hindex:2*n+2< B) (hfresh:leftArray≠target∧ rightArray≠target):
    Spec B (fun σ => Context leftArray rightArray a b σ∧ 2*n<(σ.arrs target).length)
      (command mode leftArray rightArray target) (fun _ τ => Context leftArray rightArray a b τ∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (fun v => flag mode (a v) (b v)))) target τ)
      (72*n+8):=by
  let qs:=MaskedMassData.flags (fun v => flag mode (a v) (b v))
  have hlen:qs.length=n:=List.length_ofFn
  have hv:∀ i, ∀ hi:i< qs.length,qs[i]=bit (flag mode (a ⟨i,by simpa only [hlen] using hi⟩) (b ⟨i,by simpa only [hlen] using hi⟩)):=by
    intro i hi; simp [qs,MaskedMassData.flags,bit]
  have hb:∀ i, ∀ hi:i< qs.length,qs[i].num< B∧ qs[i].den< B:=by
    intro i hi; rw [hv i hi]
    cases flag mode (a _) (b _) <;> simp [bit] <;> omega
  have body:∀ i, ∀ hi:i< qs.length,
      Spec B (fun σ => Context leftArray rightArray a b σ∧ σ.vars "mask.i"=i)
        (entry mode leftArray rightArray) (fun _ τ => Context leftArray rightArray a b τ∧ FractionOutput (qs[i]:ℚ) τ) 50:=by
    intro i hi
    simpa only [hv i hi] using entry_spec B mode leftArray rightArray a b ⟨i,by simpa only [hlen] using hi⟩ h2 hindex
  have hf:=RamUnsignedVector.command_spec B 50 (Context leftArray rightArray a b) "mask.i" "metric.n" target "mask.pos" qs []
    (entry mode leftArray rightArray) (by omega) (by simp only [List.length_nil,hlen]; omega)
    (fun i hi => (hb i hi).1) (fun i hi => (hb i hi).2) (fun _ h => by simpa only [hlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h) body
    (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp)
    (by dsimp [entry,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,RamBooleanArithmetic.command,Com.wvars]; cases mode <;> simp)
    (by change target∉([]:List String); simp) (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,
        rr.frame_var "metric.n" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr leftArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hfresh.1]),
        rr.frame_arr rightArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hfresh.2])] using h)
    (by decide) (by decide)
  rintro σ ⟨hσ,hroom⟩
  let ν:=σ.setVar "mask.pos" 0
  have rz:Run B (.assign "mask.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by omega))
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨by simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hσ,
    by intro i hi; simp at hi,by simp [ν],by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hlen] using hroom⟩
  exact ⟨τ,(rz.seq rr).mono (by simp only [hlen]; omega),pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩

end Lax455465Proofs.RamBooleanVector

end

section

namespace Lax455465Proofs.ResidualData

open Lax455465.RationalEncoding MetricMatrix LpInputSize
open scoped NNRat

theorem weight_products {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    RamProductSum.products (List.ofFn I.weight) (MaskedMassData.flags (mask active)) =
      List.ofFn (weights I active):=by
  apply List.ext_getElem
  · simp only [RamProductSum.products,List.length_ofFn]
  · intro i hi hj
    have hn:i < n:=by simpa only [RamProductSum.products,List.length_ofFn] using hi
    rw [RamProductSum.value_at (List.ofFn I.weight) (MaskedMassData.flags (mask active)) (by simp [MaskedMassData.flags]) i (by simpa using hn)]
    simp only [List.getElem_ofFn,MaskedMassData.flags,mask,weights]
    split_ifs <;> simp_all

theorem capacity_products {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    RamProductSum.products (values I.capacity) (values (RamArcMask.matrix none (mask active))) =
      values (capacity I active):=by
  rw [MetricCostData.products_eq]
  congr 1
  funext u v
  simp only [capacity,RamArcMask.matrix,RamBooleanArithmetic.flag,RamBooleanArithmetic.bit,mask]
  by_cases hu:u∈ active <;> by_cases hv:v∈ active <;> simp [hu,hv]

theorem rational_weights {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    (fun v => (weights I active v:ℚ))=RegionLoop.weights I active:=by
  funext v
  unfold weights RegionLoop.weights
  split_ifs <;> rfl

theorem rational_capacity {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)):
    rational (capacity I active)=RegionLoop.capacity I active:=by
  funext u v
  dsimp only [capacity,rational,RegionLoop.capacity]
  split_ifs <;> rfl

end Lax455465Proofs.ResidualData

end

section

namespace Lax455465Proofs.RamActiveRemove
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState
open scoped NNRat

def Context {n:ℕ} (active outBall inBall:Finset (Fin n)) (outward:Bool) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "region.outward"=(if outward then 1 else 0)∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask outBall))) "region.outMask" σ∧
  Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask inBall))) "region.inMask" σ

def removed {n:ℕ} (active outBall inBall:Finset (Fin n)) (outward:Bool):Finset (Fin n):=
  active \ (if outward then outBall else inBall)

theorem difference_mask {n:ℕ} (active ball:Finset (Fin n)):
    (fun v => RamBooleanArithmetic.flag (some true) (ResidualData.mask active v) (ResidualData.mask ball v)) =
      ResidualData.mask (active \ ball):=by
  funext v
  simp [RamBooleanArithmetic.flag,ResidualData.mask,Finset.mem_sdiff]

set_option maxHeartbeats 0 in

theorem command_spec (B:ℕ) {n:ℕ} (active outBall inBall:Finset (Fin n)) (outward:Bool)
    (h2:2< B) (hindex:2*n+2< B):
    Spec B (fun σ => Context active outBall inBall outward σ∧
      2*n<(σ.arrs "region.nextActive").length∧ 2*n≤(σ.arrs "region.active").length)
      command (fun _ τ => τ.vars "metric.n"=n∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags
          (ResidualData.mask (removed active outBall inBall outward)))) "region.active" τ)
      (96*n+22):=by
  let next:=RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask (removed active outBall inBall outward)))
  have hlen:next.length=2*n:=by simp [next,MaskedMassData.flags]
  have hwords:∀ x∈next,x< B:=by
    intro x hx
    simp only [next,RamUnsignedBuffer.encode,List.mem_flatMap] at hx
    obtain ⟨q,hq,hx⟩:=hx
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈removed active outBall inBall outward <;>
      simp [ResidualData.mask,hv,Lax455465.RationalEncoding.encodeRational] at hx <;> omega
  rintro σ ⟨hσ,hroom,hactive⟩
  have selected:∃ ν,Run B select σ ν (72*n+12)∧
      Prefix next "region.nextActive" ν:=by
    cases ho:outward
    · have hc:(Cond.eq (.var "region.outward") (.lit 1)).evalB B σ=some false:=by
        have hd:σ.vars "region.outward"=0:=by simpa only [ho,Bool.false_eq_true,if_false] using hσ.2.1
        rw [evalB_condEq (evalB_var (hd ▸ (by omega:0< B))) (evalB_lit (by omega)),hd]
        rfl
      obtain ⟨ν,rr,pr⟩:=RamBooleanVector.command_spec B (some true) "region.active" "region.inMask" "region.nextActive"
        (ResidualData.mask active) (ResidualData.mask inBall) h2 hindex (by decide) σ
        ⟨⟨hσ.1,hσ.2.2.1,hσ.2.2.2.2⟩,hroom⟩
      refine ⟨ν,(Run.ite_false (c:=RamBooleanVector.command (some true) "region.active" "region.outMask" "region.nextActive") hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simpa only [next,removed,ho,Bool.false_eq_true,if_false,difference_mask] using pr.2
    · have hc:(Cond.eq (.var "region.outward") (.lit 1)).evalB B σ=some true:=by
        have hd:σ.vars "region.outward"=1:=by simpa only [ho,if_true] using hσ.2.1
        rw [evalB_condEq (evalB_var (hd ▸ (by omega:1< B))) (evalB_lit (by omega)),hd]
        rfl
      obtain ⟨ν,rr,pr⟩:=RamBooleanVector.command_spec B (some true) "region.active" "region.outMask" "region.nextActive"
        (ResidualData.mask active) (ResidualData.mask outBall) h2 hindex (by decide) σ
        ⟨⟨hσ.1,hσ.2.2.1,hσ.2.2.2.1⟩,hroom⟩
      refine ⟨ν,(Run.ite_true (d:=RamBooleanVector.command (some true) "region.active" "region.inMask" "region.nextActive") hc rr).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
      simpa only [next,removed,ho,if_true,difference_mask] using pr.2
  obtain ⟨ν,rs,ps⟩:=selected
  have hn:ν.vars "metric.n"=n:=(rs.frame_var _ (by dsimp [select,RamBooleanVector.command,RamBooleanVector.entry,RamUnsignedVector.command,Com.wvars,RamUnsignedEncoding.command,RamWordBuffer.append]; decide)).trans hσ.1
  let μ:=ν.setVar "copy.count" (2*n)
  have rc:Run B (.assign "copy.count" (.mul (.lit 2) (.var "metric.n"))) ν μ 4:=
    Run.assign (evalB_bin (op:=.mul) (evalB_lit h2) (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n< B)⟩) (by dsimp [Bop.apply]; omega))
  obtain ⟨τ,rr,pr⟩:=RamArrayCopy.command_spec B next "region.nextActive" "region.active" "copy.count"
    (by omega) (by rw [hlen]; omega) hwords (by decide) (by decide) μ
    ⟨by simpa only [Prefix,μ,arrs_setVar] using ps,by simp [μ,hlen],
      by simpa only [μ,arrs_setVar,hlen,RamFrames.run_array_length rs "region.active"] using hactive⟩
  have run:=rs.seq (rc.seq rr)
  exact ⟨τ,run.mono (by rw [hlen]; omega),
    (run.frame_var _ (by dsimp [command,select,RamBooleanVector.command,RamBooleanVector.entry,RamUnsignedVector.command,RamArrayCopy.command,RamArrayCopy.step,Com.wvars,RamUnsignedEncoding.command,RamWordBuffer.append]; decide)).trans hσ.1,pr.2⟩

end Lax455465Proofs.RamActiveRemove

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

structure Room (n len:ℕ) (σ:Env):Prop where
  historyRoom:4*len+4≤(σ.arrs "region.history").length
  activeRoom:2*n≤(σ.arrs "region.active").length
  nextRoom:2*n<(σ.arrs "region.nextActive").length

set_option maxHeartbeats 0 in

theorem command_spec (B:ℕ) {n:ℕ} (q:RegionQueryData.Query n) (active:Finset (Fin n))
    (history:List (Entry n)) (root:Fin n) (hindex:2*n+2< B) (hlen:4*history.length+4< B)
    (hnum:q.radius.num< B) (hden:q.radius.den< B)
    (hdo:q.outDistance=q.length root) (hdi:q.inDistance=(fun v => q.length v root)):
    Spec B (fun σ => Input q active history root σ∧ Room n history.length σ) command
      (fun _ τ => τ.vars "metric.n"=n∧
        Prefix (words (history++[selected q root])) "region.history" τ∧
        τ.vars "history.pos"=4*(history.length+1)∧
        Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags
          (ResidualData.mask (active \ (selected q root).region.ball (MetricMatrix.rational q.length))))) "region.active" τ)
      (96*n+50):=by
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rr,pr⟩:=RamRegionRecord.command_spec B history (selected q root) hlen (by omega) hnum hden σ
    ⟨⟨hσ.historyData,by simpa only [length_words] using hσ.historyPosition,hσ.rootValue,
      hσ.masks.input.radiusData,hσ.masks.directionValue⟩,hroom.historyRoom⟩
  have hc:RamActiveRemove.Context active (ball q.outDistance q.radius) (ball q.inDistance q.radius)
      (RegionQueryData.direction q q.radius) ν:=by
    refine ⟨(rr.frame_var _ (by decide)).trans hσ.masks.input.nValue,
      (rr.frame_var _ (by decide)).trans hσ.masks.directionValue,?_,?_,?_⟩
    · simpa only [Prefix,rr.frame_arr "region.active" (by decide)] using hσ.activeData
    · simpa only [Prefix,rr.frame_arr "region.outMask" (by decide),mask_eq] using hσ.masks.outMask
    · simpa only [Prefix,rr.frame_arr "region.inMask" (by decide),mask_eq] using hσ.masks.inMask
  obtain ⟨τ,ra,pa⟩:=RamActiveRemove.command_spec B active (ball q.outDistance q.radius) (ball q.inDistance q.radius)
    (RegionQueryData.direction q q.radius) (by omega) hindex ν
    ⟨hc,by rw [RamFrames.run_array_length rr "region.nextActive"]; exact hroom.nextRoom,
      by rw [RamFrames.run_array_length rr "region.active"]; exact hroom.activeRoom⟩
  refine ⟨τ,(rr.seq ra).mono (by omega),pa.1,?_,?_,?_⟩
  · simpa only [Prefix,ra.frame_arr "region.history" (by decide)] using pr.1
  · exact (ra.frame_var _ (by decide)).trans pr.2
  · have hball:(selected q root).region.ball (MetricMatrix.rational q.length)=
        if RegionQueryData.direction q q.radius then ball q.outDistance q.radius else ball q.inDistance q.radius:=by
      unfold selected RamRegionRecord.Entry.region RegionLoop.Region.ball ball
      rw [hdo,hdi]
      rfl
    simpa only [RamActiveRemove.removed,hball] using pa.2

end Lax455465Proofs.RamSmallRegion

end

section

namespace Lax455465Proofs.RamRegionLarge
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamUnsignedScalar RamRegionContext
open scoped NNRat

def Input (threshold outMass inMass:ℚ≥0) (σ:Env):Prop:=
  Stored "round.largeThreshold" threshold σ∧ Stored "region.outMass" outMass σ∧ Stored "region.inMass" inMass σ

theorem command_spec (B M:ℕ) (threshold outMass inMass:ℚ≥0) (hB:2*M^2+3< B)
    (ht:LpInputSize.Height M (threshold:ℚ)) (ho:LpInputSize.Height M (outMass:ℚ))
    (hi:LpInputSize.Height M (inMass:ℚ)):
    Spec B (Input threshold outMass inMass) command
      (fun _ τ => Input threshold outMass inMass τ∧ τ.vars "region.large"=
        if (threshold:ℚ)≤ outMass∧ (threshold:ℚ)≤ inMass then 1 else 0) 134:=by
  rintro σ ⟨htσ,hoσ,hiσ⟩
  obtain ⟨ν,ro,po⟩:=RamScalarComparison.command_spec B M threshold outMass "round.largeThreshold" "region.outMass" hB
    (num_bound ht) (den_bound ht) (num_bound ho) (den_bound ho) (by decide) (by decide) (by decide) σ ⟨htσ,hoσ⟩
  let outFlag:ℕ:=if (threshold:ℚ)≤ outMass then 1 else 0
  have hoFlag:ν.vars "cmp.le"=outFlag:=po
  have h1:1< B:=by nlinarith
  have hoB:ν.vars "cmp.le"< B:=by rw [po]; split_ifs <;> omega
  let μ:=ν.setVar "large.out" outFlag
  have rs:Run B (.assign "large.out" (.var "cmp.le")) ν μ 2:=Run.assign (by rw [evalB_var_iff]; exact ⟨po.symm,hoB⟩)
  have rprior:=ro.seq rs
  obtain ⟨ξ,ri,pi⟩:=RamScalarComparison.command_spec B M threshold inMass "round.largeThreshold" "region.inMass" hB
    (num_bound ht) (den_bound ht) (num_bound hi) (den_bound hi) (by decide) (by decide) (by decide) μ
    ⟨by simpa only [Stored,String.reduceAppend,rprior.frame_var "round.largeThreshold.n" (by decide),rprior.frame_var "round.largeThreshold.d" (by decide)] using htσ,
      by simpa only [Stored,String.reduceAppend,rprior.frame_var "region.inMass.n" (by decide),rprior.frame_var "region.inMass.d" (by decide)] using hiσ⟩
  let inFlag:ℕ:=if (threshold:ℚ)≤ inMass then 1 else 0
  have hiFlag:ξ.vars "cmp.le"=inFlag:=pi
  have hout:ξ.vars "large.out"=outFlag:=by simpa only [μ,vars_setVar,if_true,ri.frame_var "large.out" (by decide)]
  have hoBound:outFlag≤1:=by dsimp [outFlag]; split_ifs <;> omega
  have hiBound:inFlag≤1:=by dsimp [inFlag]; split_ifs <;> omega
  have hprod:outFlag*inFlag< B:=(Nat.mul_le_mul hoBound hiBound).trans_lt (by simpa using h1)
  let τ:=ξ.setVar "region.large" (outFlag*inFlag)
  have rm:Run B (.assign "region.large" (.mul (.var "large.out") (.var "cmp.le"))) ξ τ 4:=
    Run.assign (evalB_bin (op:=.mul) (by rw [evalB_var_iff]; exact ⟨hout.symm,hout ▸ hoBound.trans_lt h1⟩)
      (by rw [evalB_var_iff]; exact ⟨hiFlag.symm,hiFlag ▸ hiBound.trans_lt h1⟩) hprod)
  have rr:=ro.seq (rs.seq (ri.seq rm))
  refine ⟨τ,rr,?_,?_⟩
  · exact ⟨by simpa only [Stored,String.reduceAppend,rr.frame_var "round.largeThreshold.n" (by decide),rr.frame_var "round.largeThreshold.d" (by decide)] using htσ,
      by simpa only [Stored,String.reduceAppend,rr.frame_var "region.outMass.n" (by decide),rr.frame_var "region.outMass.d" (by decide)] using hoσ,
      by simpa only [Stored,String.reduceAppend,rr.frame_var "region.inMass.n" (by decide),rr.frame_var "region.inMass.d" (by decide)] using hiσ⟩
  · simp only [τ,vars_setVar,if_true,outFlag,inFlag]
    split_ifs <;> simp_all

end Lax455465Proofs.RamRegionLarge

end

section

namespace Lax455465Proofs.RamRegionBranch
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RegionQueryData RamRegionRecord
open scoped NNRat

structure Input {n:ℕ} (q:Query n) (threshold:ℚ≥0) (active:Finset (Fin n))
    (history:List (Entry n)) (root:Fin n) (σ:Env):Prop where
  smallInput:RamSmallRegion.Input q active history root σ
  phase:σ.vars "region.phase"=0
  thresholdData:Stored "round.largeThreshold" threshold σ
  outMass:Stored "region.outMass" (BallMassData.mass q.weights q.outDistance q.radius) σ
  inMass:Stored "region.inMass" (BallMassData.mass q.weights q.inDistance q.radius) σ

set_option maxHeartbeats 0 in

theorem command_spec (B H:ℕ) {n:ℕ} (q:Query n) (threshold:ℚ≥0) (active:Finset (Fin n))
    (history:List (Entry n)) (root:Fin n) (hb:RegionQueryHeight.Bounds q H)
    (hB:2*(2^H)^2+3< B) (ht:LpInputSize.Height (2^H) (threshold:ℚ))
    (hindex:2*n+2< B) (hlen:4*history.length+4< B)
    (hdo:q.outDistance=q.length root) (hdi:q.inDistance=(fun v => q.length v root)):
    Spec B (fun σ => Input q threshold active history root σ∧ RamSmallRegion.Room n history.length σ)
      command (fun _ τ => Output q threshold active history root τ) (96*n+188):=by
  have h2:2< B:=by nlinarith [(Nat.one_le_two_pow:1≤2^H)]
  have hHB:2^H< B:=by nlinarith [(Nat.one_le_two_pow:1≤2^H)]
  rintro σ ⟨hσ,hroom⟩
  obtain ⟨ν,rl,pl⟩:=RamRegionLarge.command_spec B (2^H) threshold
    (BallMassData.mass q.weights q.outDistance q.radius) (BallMassData.mass q.weights q.inDistance q.radius)
    hB ht (RamRegionContext.mass_height q H hb true) (RamRegionContext.mass_height q H hb false) σ
    ⟨hσ.thresholdData,hσ.outMass,hσ.inMass⟩
  have hi:RamSmallRegion.Input q active history root ν:=by
    have hm:=hσ.smallInput.masks
    refine ⟨⟨RamRegionContext.Input.frame rl hm.input (by dsimp [RamRegionContext.sourceVariables]; decide)
      (by dsimp [RamRegionContext.arrays]; decide),?_,?_,?_⟩,
      (rl.frame_var _ (by decide)).trans hσ.smallInput.rootValue,?_,?_,
      (rl.frame_var _ (by decide)).trans hσ.smallInput.historyPosition⟩
    · simpa only [Prefix,rl.frame_arr "region.outMask" (by decide)] using hm.outMask
    · simpa only [Prefix,rl.frame_arr "region.inMask" (by decide)] using hm.inMask
    · exact (rl.frame_var _ (by decide)).trans hm.directionValue
    · simpa only [Prefix,rl.frame_arr "region.active" (by decide)] using hσ.smallInput.activeData
    · simpa only [Prefix,rl.frame_arr "region.history" (by decide)] using hσ.smallInput.historyData
  have hf:ν.vars "region.large"=if large q threshold then 1 else 0:=pl.2
  by_cases hl:large q threshold
  · have hc:(Cond.eq (.var "region.large") (.lit 1)).evalB B ν=some true:=by
      have he:ν.vars "region.large"=1:=by simpa only [hl,if_true] using hf
      rw [evalB_condEq (evalB_var (he ▸ (by omega:1< B))) (evalB_lit (by omega)),he]
      rfl
    let τ:=ν.setVar "region.phase" 1
    have rp:Run B (.assign "region.phase" (.lit 1)) ν τ 2:=Run.assign (evalB_lit (by omega))
    refine ⟨τ,(rl.seq (Run.ite_true (d:=RamSmallRegion.command) hc rp)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [Output,hl,if_true]
    refine ⟨by simp [τ],?_⟩
    have hm:=hi.masks
    exact ⟨⟨RamRegionContext.Input.frame rp hm.input (by dsimp [RamRegionContext.sourceVariables]; decide)
      (by dsimp [RamRegionContext.arrays]; decide),
      by simpa only [Prefix,τ,arrs_setVar] using hm.outMask,
      by simpa only [Prefix,τ,arrs_setVar] using hm.inMask,
      by simpa only [τ,vars_setVar,String.reduceEq,if_false] using hm.directionValue⟩,
      (rp.frame_var _ (by decide)).trans hi.rootValue,
      by simpa only [Prefix,τ,arrs_setVar] using hi.activeData,
      by simpa only [Prefix,τ,arrs_setVar] using hi.historyData,
      (rp.frame_var _ (by decide)).trans hi.historyPosition⟩
  · have hc:(Cond.eq (.var "region.large") (.lit 1)).evalB B ν=some false:=by
      have he:ν.vars "region.large"=0:=by simpa only [hl,if_false] using hf
      rw [evalB_condEq (evalB_var (he ▸ (by omega:0< B))) (evalB_lit (by omega)),he]
      rfl
    obtain ⟨τ,rs,ps⟩:=RamSmallRegion.command_spec B q active history root hindex hlen
      ((RamRegionContext.num_bound hb.radiusBound).trans_lt hHB)
      ((RamRegionContext.den_bound hb.radiusBound).trans_lt hHB) hdo hdi ν
      ⟨hi,⟨by rw [RamFrames.run_array_length rl "region.history"]; exact hroom.historyRoom,
        by rw [RamFrames.run_array_length rl "region.active"]; exact hroom.activeRoom,
        by rw [RamFrames.run_array_length rl "region.nextActive"]; exact hroom.nextRoom⟩⟩
    have rr:=rl.seq (Run.ite_false (c:=.assign "region.phase" (.lit 1)) hc rs)
    refine ⟨τ,rr.mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [Output,hl,if_false]
    exact ⟨((rl.seq rs).frame_var _ (by decide)).trans hσ.phase,ps⟩

end Lax455465Proofs.RamRegionBranch

end

section

namespace Lax455465Proofs.RamProductVector

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open scoped NNRat

def Context (leftArray rightArray:String) (xs ys:List ℚ≥0) (σ:Env):Prop:=
  σ.vars "product.count"=xs.length∧ Prefix (RamUnsignedBuffer.encode xs) leftArray σ∧
    Prefix (RamUnsignedBuffer.encode ys) rightArray σ

theorem command_spec (B M:ℕ) (leftArray rightArray target:String) (xs ys:List ℚ≥0)
    (hlen:ys.length=xs.length) (hneq:leftArray ≠ target∧ rightArray ≠ target)
    (hB:2*M^2+3 < B) (hindex:2*xs.length+2 < B)
    (hxn:∀ q∈ xs,q.num≤ M) (hxd:∀ q∈ xs,q.den≤ M)
    (hyn:∀ q∈ ys,q.num≤ M) (hyd:∀ q∈ ys,q.den≤ M):
    Spec B (fun σ => Context leftArray rightArray xs ys σ∧ 2*xs.length < (σ.arrs target).length)
      (command leftArray rightArray target) (fun _ τ => Context leftArray rightArray xs ys τ∧
        Prefix (RamUnsignedBuffer.encode (RamProductSum.products xs ys)) target τ)
      ((36*(M^2).size+126)*xs.length+8):=by
  have hM:M < B:=by nlinarith
  have hprod:M*M < B:=by nlinarith
  let qs:=RamProductSum.products xs ys
  have hqlen:qs.length=xs.length:=List.length_ofFn
  have hvalues:∀ i, ∀ hi:i < qs.length,qs[i].num < B∧ qs[i].den < B:=by
    intro i hi
    have hx:i < xs.length:=by rwa [hqlen] at hi
    have hy:i < ys.length:=by omega
    have hxm:xs[i]∈ xs:=List.getElem_mem hx
    have hym:ys[i]∈ ys:=List.getElem_mem hy
    have hh:=LpInputSize.height_mul
      (show LpInputSize.Height M (xs[i]:ℚ) from ⟨by simpa only [NNRat.natAbs_num_coe] using hxn _ hxm,
        by simpa only [NNRat.den_coe] using hxd _ hxm⟩)
      (show LpInputSize.Height M (ys[i]:ℚ) from ⟨by simpa only [NNRat.natAbs_num_coe] using hyn _ hym,
        by simpa only [NNRat.den_coe] using hyd _ hym⟩)
    have he:qs[i]=xs[i]*ys[i]:=RamProductSum.value_at xs ys hlen i hx
    rw [he]
    have hh':LpInputSize.Height (M*M) ((xs[i]*ys[i]:ℚ≥0):ℚ):=by
      simpa only [NNRat.coe_mul] using hh
    have hn:(xs[i]*ys[i]).num≤ M*M:=by simpa only [NNRat.natAbs_num_coe] using hh'.1
    have hd:(xs[i]*ys[i]).den≤ M*M:=by simpa only [NNRat.den_coe] using hh'.2
    exact ⟨hn.trans_lt hprod,hd.trans_lt hprod⟩
  have hbody:∀ i, ∀ hi:i < qs.length,
      Spec B (fun σ => Context leftArray rightArray xs ys σ∧ σ.vars "sum.i"=i)
        (RamArrayProduct.command leftArray rightArray)
        (fun _ τ => Context leftArray rightArray xs ys τ∧ FractionOutput (qs[i]:ℚ) τ)
        (36*(M^2).size+104):=by
    intro i hi σ hσ
    have hx:i < xs.length:=by rwa [hqlen] at hi
    have hy:i < ys.length:=by omega
    have hxm:xs[i]∈ xs:=List.getElem_mem hx
    have hym:ys[i]∈ ys:=List.getElem_mem hy
    obtain ⟨τ,rr,pr⟩:=RamArrayProduct.command_spec B M leftArray rightArray xs ys i hx hy hB
      (by omega) (hxn _ hxm) (hxd _ hxm) (hyn _ hym) (hyd _ hym) σ ⟨hσ.1.2.1,hσ.1.2.2,hσ.2⟩
    have hcost:(xs[i].den*ys[i].den).size≤ (M^2).size:=
      Nat.size_le_size (by nlinarith [Nat.mul_le_mul (hxd _ hxm) (hyd _ hym)])
    refine ⟨τ,rr.mono (by omega),?_,?_⟩
    · simpa only [Context,Prefix,rr.frame_var "product.count" (by
        dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide),
        rr.frame_arr leftArray (by change leftArray∉ ([]:List String); simp),
        rr.frame_arr rightArray (by change rightArray∉ ([]:List String); simp)] using hσ.1
    · simpa only [qs,RamProductSum.value_at xs ys hlen i hx] using pr
  have hf:=RamUnsignedVector.command_spec B (36*(M^2).size+104)
    (Context leftArray rightArray xs ys) "sum.i" "product.count" target "product.pos" qs []
    (RamArrayProduct.command leftArray rightArray) (by nlinarith)
    (by simp only [List.length_nil,hqlen]; omega)
    (fun i hi => (hvalues i hi).1) (fun i hi => (hvalues i hi).2)
    (fun _ h => by simpa only [hqlen] using h.1)
    (fun σ k h => by simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using h)
    hbody
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by dsimp [RamArrayProduct.command,RamUnsignedBuffer.read,RamUnsignedArithmetic.copy,Com.wvars]; decide)
    (by change target∉ ([]:List String); simp)
    (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide)
    (fun rr h => by
      simpa only [Context,Prefix,
        rr.frame_var "product.count" (by dsimp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.wvars]; decide),
        rr.frame_arr leftArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq.1]),
        rr.frame_arr rightArray (by simp [RamUnsignedEncoding.command,RamWordBuffer.append,Com.warrs,hneq.2])] using h)
    (by decide) (by decide)
  rintro σ ⟨hctx,hroom⟩
  let ν:=σ.setVar "product.pos" 0
  have rzero:Run B (.assign "product.pos" (.lit 0)) σ ν 2:=Run.assign (evalB_lit (by nlinarith))
  have hctxν:Context leftArray rightArray xs ys ν:=by
    simpa only [Context,Prefix,ν,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hctx
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨hctxν,by intro i hi; simp at hi,by simp [ν],
    by simpa only [ν,arrs_setVar,List.length_nil,Nat.zero_add,hqlen] using hroom⟩
  refine ⟨τ,(rzero.seq rr).mono ?_,pr.1,by simpa only [List.nil_append,qs] using pr.2.1⟩
  simp only [hqlen,Nat.add_assoc,Nat.reduceAdd]
  omega

end Lax455465Proofs.RamProductVector

end

section

namespace Lax455465Proofs.RamResidual

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational MetricMatrix
open Lax455465.RationalEncoding
open scoped NNRat

def Context {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n)) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "metric.n2"=n*n∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn I.weight)) "flow.weights" σ∧
    Prefix (RamUnsignedBuffer.encode (values I.capacity)) "flow.capacities" σ∧
    Prefix (RamUnsignedBuffer.encode (MaskedMassData.flags (ResidualData.mask active))) "region.active" σ

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (active:Finset (Fin n))
    (hM1:1≤ M) (hB:2*M^2+3 < B) (hindex:2*(n*n)+2 < B) (hvertex:2*n+2 < B)
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M):
    Spec B (fun σ => Context I active σ∧
      2*(n*n) < (σ.arrs "region.arcActive").length∧
      2*(n*n) < (σ.arrs "region.capacities").length∧
      2*n < (σ.arrs "region.weights").length) command
      (fun _ τ => Context I active τ∧
        Prefix (RamUnsignedBuffer.encode (values (ResidualData.capacity I active))) "region.capacities" τ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (ResidualData.weights I active))) "region.weights" τ)
      ((36*(M^2).size+208)*(n*n)+(36*(M^2).size+126)*n+28):=by
  have h2:2 < B:=by nlinarith
  let ws:=List.ofFn I.weight
  let cs:=values I.capacity
  let vs:=MaskedMassData.flags (ResidualData.mask active)
  let es:=values (RamArcMask.matrix none (ResidualData.mask active))
  have hwLen:ws.length=n:=List.length_ofFn
  have hcLen:cs.length=n*n:=length_values _
  have hvLen:vs.length=n:=List.length_ofFn
  have heLen:es.length=n*n:=length_values _
  have hwN:∀ q∈ ws,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hwn v
  have hwD:∀ q∈ ws,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hwd v
  have hcN:∀ q∈ cs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hcn _ _
  have hcD:∀ q∈ cs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq; exact hcd _ _
  have hvN:∀ q∈ vs,q.num≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈ active <;> simp [ResidualData.mask,hv] <;> omega
  have hvD:∀ q∈ vs,q.den≤ M:=by
    intro q hq; obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hq
    by_cases hv:v∈ active <;> simp [ResidualData.mask,hv] <;> omega
  have heN:∀ q∈ es,q.num≤ M:=by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [RamArcMask.matrix]
    cases RamBooleanArithmetic.flag none (ResidualData.mask active _) (ResidualData.mask active _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  have heD:∀ q∈ es,q.den≤ M:=by
    intro q hq; obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hq
    dsimp only [RamArcMask.matrix]
    cases RamBooleanArithmetic.flag none (ResidualData.mask active _) (ResidualData.mask active _) <;>
      simp [RamBooleanArithmetic.bit] <;> omega
  rintro σ ⟨hctx,heRoom,hcRoom,hwRoom⟩
  obtain ⟨ν,re,pe⟩:=RamArcMask.command_spec B none "region.active" "region.arcActive" (ResidualData.mask active)
    (by decide) h2 (by omega) (by omega) hindex hvertex σ ⟨⟨hctx.1,hctx.2.1,hctx.2.2.2.2⟩,heRoom⟩
  let ξ:=ν.setVar "product.count" (n*n)
  have rcCount:Run B (.assign "product.count" (.var "metric.n2")) ν ξ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨pe.1.2.1.symm,pe.1.2.1 ▸ (by omega:n*n < B)⟩)
  have hcCtx:RamProductVector.Context "flow.capacities" "region.arcActive" cs es ξ:=by
    refine ⟨by simp [ξ,hcLen],?_,?_⟩
    · simpa only [cs,Prefix,ξ,arrs_setVar,re.frame_arr "flow.capacities" (by decide)] using hctx.2.2.2.1
    · simpa only [es,Prefix,ξ,arrs_setVar] using pe.2
  obtain ⟨μ,rc,pc⟩:=RamProductVector.command_spec B M "flow.capacities" "region.arcActive" "region.capacities" cs es
    (by rw [heLen,hcLen]) (by decide) hB (by rwa [hcLen]) hcN hcD heN heD ξ
    ⟨hcCtx,by simpa only [ξ,arrs_setVar,hcLen,re.frame_arr "region.capacities" (by decide)] using hcRoom⟩
  have hnμ:μ.vars "metric.n"=n:=
    (rc.frame_var _ (by decide)).trans ((rcCount.frame_var _ (by decide)).trans pe.1.1)
  let ρ:=μ.setVar "product.count" n
  have rwCount:Run B (.assign "product.count" (.var "metric.n")) μ ρ 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hnμ.symm,hnμ ▸ (by omega:n < B)⟩)
  have rprior:=re.seq (rcCount.seq (rc.seq rwCount))
  have hwCtx:RamProductVector.Context "flow.weights" "region.active" ws vs ρ:=by
    refine ⟨by simp [ρ,hwLen],?_,?_⟩
    · simpa only [ws,Prefix,rprior.frame_arr "flow.weights" (by decide)] using hctx.2.2.1
    · simpa only [vs,Prefix,rprior.frame_arr "region.active" (by decide)] using hctx.2.2.2.2
  obtain ⟨τ,rw,pw⟩:=RamProductVector.command_spec B M "flow.weights" "region.active" "region.weights" ws vs
    (by rw [hvLen,hwLen]) (by decide) hB (by rwa [hwLen]) hwN hwD hvN hvD ρ
    ⟨hwCtx,by simpa only [hwLen,rprior.frame_arr "region.weights" (by decide)] using hwRoom⟩
  have rr:=re.seq (rcCount.seq (rc.seq (rwCount.seq rw)))
  refine ⟨τ,rr.mono ?_,?_,?_,?_⟩
  · simp only [hcLen,hwLen,Nat.add_assoc,Nat.reduceAdd]
    ring_nf; omega
  · simpa only [Context,Prefix,
      rr.frame_var "metric.n" (by decide),rr.frame_var "metric.n2" (by decide),
      rr.frame_arr "flow.weights" (by decide),rr.frame_arr "flow.capacities" (by decide),
      rr.frame_arr "region.active" (by decide)] using hctx
  · have rafter:=rwCount.seq rw
    simpa only [cs,es,ResidualData.capacity_products,Prefix,rafter.frame_arr "region.capacities" (by decide)] using pc.2
  · simpa only [ws,vs,ResidualData.weight_products] using pw.2

end Lax455465Proofs.RamResidual

end

section

namespace Lax455465Proofs.RamRegionInvariant
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open Lax455465.RationalEncoding RamRegionRecord
open scoped NNRat

def names:List String:= ["metric.n","metric.n2","round.support","round.steps",
  "round.seed.n","round.seed.d","round.slope.n","round.slope.d",
  "round.delta.n","round.delta.d","round.gridStep.n","round.gridStep.d",
  "round.largeThreshold.n","round.largeThreshold.d"]
def arrays:List String:= ["flow.weights","flow.capacities","metric.old"]

theorem Fixed.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {I:RationalInstance n} {length:MetricMatrix.Matrix n} {seed beta delta threshold:ℚ≥0} {p:ℕ}
    (h:Fixed I length seed beta delta threshold p σ)
    (hx:∀ x∈names,x∉cmd.wvars) (ha:∀ a∈arrays,a∉cmd.warrs):
    Fixed I length seed beta delta threshold p τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [names]))).trans h.nValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.n2Value,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.supportValue,
    (rr.frame_var _ (hx _ (by simp [names]))).trans h.stepsValue,
    RamRoundingConstants.storedFrame rr h.seedData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.betaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.deltaData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.unitData (hx _ (by simp [names])) (hx _ (by simp [names])),
    RamRoundingConstants.storedFrame rr h.thresholdData (hx _ (by simp [names])) (hx _ (by simp [names])),
    by simpa only [Prefix,rr.frame_arr "flow.weights" (ha _ (by simp [arrays]))] using h.weightsData,
    by simpa only [Prefix,rr.frame_arr "flow.capacities" (ha _ (by simp [arrays]))] using h.capacityData,
    by simpa only [Prefix,rr.frame_arr "metric.old" (ha _ (by simp [arrays]))] using h.lengthData⟩

def dynamicNames:List String:= ["region.phase","history.pos"]
def dynamicArrays:List String:= ["region.active","region.history"]

theorem Dynamic.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n:ℕ} {active:Finset (Fin n)} {history:List (Entry n)} (h:Dynamic active history σ)
    (hx:∀ x∈dynamicNames,x∉cmd.wvars) (ha:∀ a∈dynamicArrays,a∉cmd.warrs):Dynamic active history τ:=by
  exact ⟨(rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.phase,
    by simpa only [Prefix,rr.frame_arr "region.active" (ha _ (by simp [dynamicArrays]))] using h.activeData,
    by simpa only [Prefix,rr.frame_arr "region.history" (ha _ (by simp [dynamicArrays]))] using h.historyData,
    (rr.frame_var _ (hx _ (by simp [dynamicNames]))).trans h.historyPosition⟩

theorem Room.frame {B K:ℕ} {cmd:Com} {σ τ:Env} (rr:Run B cmd σ τ K)
    {n p:ℕ} (h:Room n p σ):Room n p τ:=by
  intro a count hm
  rw [RamFrames.run_array_length rr a]
  exact h a count hm

end Lax455465Proofs.RamRegionInvariant

end

section

namespace Lax455465Proofs.RootData
open scoped NNRat

def predicate (qs:List ℚ≥0) (i:ℕ):Bool:=decide (0 < (qs.getD i 0).num)

theorem map_finRange (n:ℕ):(List.finRange n).map Fin.val=List.range n:=by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

theorem predicate_at {n:ℕ} (weights:Fin n→ ℚ≥0) (v:Fin n):
    predicate (List.ofFn weights) v.val=decide (0 < (weights v:ℚ)):=by
  unfold predicate
  rw [List.getD_eq_get (List.ofFn weights) 0 (⟨v.val,by simpa using v.isLt⟩:Fin (List.ofFn weights).length)]
  simp only [List.get_eq_getElem,List.getElem_ofFn,Fin.eta]
  congr 1
  rw [NNRat.num_pos]
  exact propext NNRat.coe_lt_coe.symm

theorem first_eq {n:ℕ} (weights:Fin n→ ℚ≥0):
    RamFind.first (predicate (List.ofFn weights)) n =
      (RegionSelection.chooseRoot (fun v => (weights v:ℚ))).map Fin.val:=by
  rw [RamFind.first,←map_finRange n,List.find?_map]
  unfold RegionSelection.chooseRoot
  congr 1
  apply List.find?_congr
  intro v hv
  exact predicate_at weights v

end Lax455465Proofs.RootData

end

section

namespace Lax455465Proofs.RamRoot

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRational
open scoped NNRat

theorem test_spec (B:ℕ) (qs:List ℚ≥0) (i:ℕ) (hi:i < qs.length)
    (h2:2 < B) (hindex:2*i+1 < B) (hnum:qs[i].num < B) (hden:qs[i].den < B):
    Spec B (fun σ => Prefix (RamUnsignedBuffer.encode qs) "region.weights" σ∧ σ.vars "find.i"=i)
      test (fun _ τ => τ.vars "find.ok"=if RootData.predicate qs i then 1 else 0) 20:=by
  intro σ hσ
  obtain ⟨ν,rr,pr⟩:=RamUnsignedBuffer.read_spec B "region.weights" "find.i" qs i hi h2 hindex hnum hden (by decide) σ hσ
  have hn:ν.vars "rat.n"=qs[i].num:=by simpa only [NNRat.natAbs_num_coe] using pr.1.2.1
  have hc:(Cond.eq (.var "rat.n") (.lit 0)).evalB B ν=some (decide (qs[i].num=0)):=by
    rw [evalB_condEq (evalB_var (hn ▸ hnum)) (evalB_lit (by omega)),hn]
    rfl
  by_cases hz:qs[i].num=0
  · have rb:Run B (.assign "find.ok" (.lit 0)) ν (ν.setVar "find.ok" 0) 2:=Run.assign (evalB_lit (by omega))
    refine ⟨ν.setVar "find.ok" 0,(rr.seq (Run.ite_true (d:=.assign "find.ok" (.lit 1)) (by simpa only [hz,decide_true] using hc) rb)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [vars_setVar,if_pos rfl,RootData.predicate,List.getD_eq_get qs 0 (⟨i,hi⟩:Fin qs.length),List.get_eq_getElem,hz]
    rfl
  · have rb:Run B (.assign "find.ok" (.lit 1)) ν (ν.setVar "find.ok" 1) 2:=Run.assign (evalB_lit (by omega))
    refine ⟨ν.setVar "find.ok" 1,(rr.seq (Run.ite_false (c:=.assign "find.ok" (.lit 0)) (by simpa only [hz,decide_false] using hc) rb)).mono (by dsimp [Cond.size,Expr.size]; omega),?_⟩
    simp only [vars_setVar,if_pos rfl,RootData.predicate,List.getD_eq_get qs 0 (⟨i,hi⟩:Fin qs.length),List.get_eq_getElem,decide_eq_true (Nat.pos_of_ne_zero hz),if_true]

def Context {n:ℕ} (weights:Fin n→ ℚ≥0) (σ:Env):Prop:=
  σ.vars "metric.n"=n∧ σ.vars "find.count"=n∧
    Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ

theorem command_spec (B H:ℕ) {n:ℕ} (weights:Fin n→ ℚ≥0) (h2:2 < B)
    (hH:H < B) (hindex:2*n+2 < B)
    (hnum:∀ v, (weights v).num≤ H) (hden:∀ v, (weights v).den≤ H):
    Spec B (fun σ => σ.vars "metric.n"=n∧ Prefix (RamUnsignedBuffer.encode (List.ofFn weights)) "region.weights" σ)
      command (fun _ τ => Context weights τ∧ RamFind.Matches
        ((RegionSelection.chooseRoot (fun v => (weights v:ℚ))).map Fin.val) τ) (40*n+12):=by
  let qs:=List.ofFn weights
  have hlen:qs.length=n:=List.length_ofFn
  have hb:∀ i,i < n→ Spec B (fun σ => Context weights σ∧ σ.vars "find.i"=i) test
      (fun _ τ => Context weights τ∧ τ.vars "find.ok"=if RootData.predicate qs i then 1 else 0) 20:=by
    intro i hi σ hσ
    have hq:i < qs.length:=by rwa [hlen]
    have he:qs[i]=weights ⟨i,hi⟩:=by simp only [qs,List.getElem_ofFn]
    obtain ⟨τ,rr,pr⟩:=test_spec B qs i hq h2 (by omega)
      (by rw [he]; exact (hnum _).trans_lt hH) (by rw [he]; exact (hden _).trans_lt hH) σ ⟨hσ.1.2.2,hσ.2⟩
    refine ⟨τ,rr,?_,pr⟩
    simpa only [Context,Prefix,rr.frame_var "metric.n" (by decide),rr.frame_var "find.count" (by decide),
      rr.frame_arr "region.weights" (by decide)] using hσ.1
  have hf:=RamFind.command_spec B n 20 (Context weights) (RootData.predicate qs) test (by omega) (by omega)
    (fun _ h => h.2.1)
    (fun σ k name hσ hn => by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hn
      rcases hn with rfl|rfl|rfl <;> simpa only [Context,Prefix,vars_setVar,arrs_setVar,String.reduceEq,if_false] using hσ)
    hb (by decide)
  rintro σ ⟨hn,hprefix⟩
  let ν:=σ.setVar "find.count" n
  have rstart:Run B (.assign "find.count" (.var "metric.n")) σ ν 2:=
    Run.assign (by rw [evalB_var_iff]; exact ⟨hn.symm,hn ▸ (by omega:n < B)⟩)
  obtain ⟨τ,rr,pr⟩:=hf ν ⟨by simpa only [ν,vars_setVar,String.reduceEq,if_false] using hn,
    by simp [ν],by simpa only [ν,Prefix,arrs_setVar] using hprefix⟩
  refine ⟨τ,(rstart.seq rr).mono (by omega),pr.1,?_⟩
  simpa only [qs,RootData.first_eq] using pr.2

end Lax455465Proofs.RamRoot

end

section

namespace Lax455465Proofs.RamRegionPrelude
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamRegionInvariant RamRegionRecord
open Lax455465.RationalEncoding
open scoped NNRat

def command:Com:=.seq RamResidual.command RamRoot.command

set_option maxHeartbeats 0 in

theorem command_spec (B M:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (active:Finset (Fin n)) (history:List (Entry n))
    (hM:1≤ M) (hB:2*M^2+3< B) (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B)
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M):
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Dynamic active history σ∧ Room n p σ)
      command (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Dynamic active history τ∧ Room n p τ∧
        Prefix (RamUnsignedBuffer.encode (MetricMatrix.values (ResidualData.capacity I active))) "region.capacities" τ∧
        Prefix (RamUnsignedBuffer.encode (List.ofFn (ResidualData.weights I active))) "region.weights" τ∧
        RamFind.Matches ((RegionSelection.chooseRoot (RegionLoop.weights I active)).map Fin.val) τ)
      (cost n M):=by
  have hMB:M< B:=by nlinarith
  rintro σ ⟨hσ,hd,hr⟩
  obtain ⟨ν,rr,pr⟩:=RamResidual.command_spec B M I active hM hB hindex hvertex hwn hwd hcn hcd σ
    ⟨⟨hσ.nValue,hσ.n2Value,hσ.weightsData,hσ.capacityData,hd.activeData⟩,
      by simpa only [Nat.mul_assoc] using hr "region.arcActive" (2*n*n) (by simp [extents]),
      by simpa only [Nat.mul_assoc] using hr "region.capacities" (2*n*n) (by simp [extents]),
      hr "region.weights" (2*n) (by simp [extents])⟩
  have hnum:∀ v, (ResidualData.weights I active v).num≤ M:=by
    intro v
    unfold ResidualData.weights
    split_ifs
    · exact hwn v
    · simp
  have hden:∀ v, (ResidualData.weights I active v).den≤ M:=by
    intro v
    unfold ResidualData.weights
    split_ifs
    · exact hwd v
    · simpa using hM
  obtain ⟨τ,rf,pf⟩:=RamRoot.command_spec B M (ResidualData.weights I active) (by nlinarith) hMB hvertex hnum hden ν
    ⟨pr.1.1,pr.2.2⟩
  have run:=rr.seq rf
  refine ⟨τ,run.mono (by dsimp [cost]; nlinarith),
    Fixed.frame run hσ (by dsimp [names]; decide) (by dsimp [arrays]; decide),
    Dynamic.frame run hd (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide),Room.frame run hr,?_,pf.1.2.2,?_⟩
  · simpa only [Prefix,rf.frame_arr "region.capacities" (by decide)] using pr.2.1
  · simpa only [ResidualData.rational_weights] using pf.2

end Lax455465Proofs.RamRegionPrelude

end

section

open scoped BigOperators NNRat
namespace Lax455465Proofs.RegionExecutionData
open Lax455465.RationalEncoding RegionQueryData

theorem search_exists {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (active:Finset (Fin n)) (root:Fin n) (seed delta:ℚ≥0) (p:ℕ)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ)):
    ∃ r,RegionSearch.search (RegionLoop.capacity I active) (MetricMatrix.rational length)
      (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
      (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)=some r:=by
  have hd:RationalDistances.Nonnegative (MetricMatrix.rational length):=fun u v => (length u v).coe_nonneg
  obtain ⟨r,hr,_,_,_⟩:=RegionSearch.search_correct (RegionLoop.capacity I active) (MetricMatrix.rational length)
    (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
    (RegionLoop.chooseDirection I (MetricMatrix.rational length) active root)
    (RegionLoop.capacity_nonnegative I active) hd hseed hdelta hp
    ((RegionLoop.residual_cost_le I _ active hd).trans hcost)
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri root u v])
    (fun u v => by dsimp only [MetricMatrix.rational]; linarith [htri v u root])
  exact ⟨r,hr⟩

end Lax455465Proofs.RegionExecutionData

end

section

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 30000
namespace Lax455465Proofs.RamRegionCore
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamVirtualState RamUnsignedScalar
open RamRegionInvariant RamRegionRecord Lax455465.RationalEncoding
open scoped NNRat

set_option maxHeartbeats 0 in

theorem iteration_spec (B M H:ℕ) {n:ℕ} (I:RationalInstance n) (length:MetricMatrix.Matrix n)
    (seed beta delta threshold:ℚ≥0) (p:ℕ) (active:Finset (Fin n)) (history:List (Entry n))
    (hM:1≤ M) (hk:RegionBudget.steps p≤ M) (hB:2*M^2+3< B) (hquery:2*(2^H)^2+3< B)
    (hindex:2*(n*n)+2< B) (hvertex:2*n+2< B) (hradius:2*(RegionBudget.steps p+1+2*n)+2< B)
    (hlen:4*history.length+4< B) (ht:LpInputSize.Height (2^H) (threshold:ℚ))
    (hwn:∀ v, (I.weight v).num≤ M) (hwd:∀ v, (I.weight v).den≤ M)
    (hcn:∀ u v, (I.capacity u v).num≤ M) (hcd:∀ u v, (I.capacity u v).den≤ M)
    (hl:∀ u v,LpInputSize.Height M (length u v:ℚ))
    (hd:LpInputSize.Height M (delta:ℚ))
    (hu:LpInputSize.Height M ((delta/(RegionBudget.steps p:ℚ≥0):ℚ≥0):ℚ))
    (hb:∀ root:Fin n, ∀ i, ∀ hi:i<(RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta).length,
      RegionQueryHeight.Bounds (RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta)
        (RadiusData.candidates (length root) (fun v => length v root) (RegionBudget.steps p) delta)[i]) H)
    (hbeta:(beta:ℚ)=RegionSearch.slope (RegionBudget.steps p) delta)
    (hseed:0<(seed:ℚ)) (hdelta:0<(delta:ℚ)) (hp:0< p)
    (htri:∀ u v w, (length u w:ℚ)≤(length u v:ℚ)+(length v w:ℚ))
    (hcost:RegionRounding.metricCost I (MetricMatrix.rational length)≤(p:ℚ)*(seed:ℚ))
    (hHist:history.length≤ p):
    Spec B (fun σ => Fixed I length seed beta delta threshold p σ∧ Dynamic active history σ∧ Room n p σ)
      RamRegionLoop.iteration (fun _ τ => Fixed I length seed beta delta threshold p τ∧ Room n p τ∧
        Output I length seed beta delta threshold p active history τ) (cost n p M H):=by
  have h2:2< B:=by nlinarith
  rintro σ ⟨hσ,hstate,hroom⟩
  obtain ⟨σ1,rpre,ppre⟩:=RamRegionPrelude.command_spec B M I length seed beta delta threshold p active history
    hM hB hindex hvertex hwn hwd hcn hcd σ ⟨hσ,hstate,hroom⟩
  have hf:=ppre.1
  have hs:=ppre.2.1
  have hr:=ppre.2.2.1
  have hm:=ppre.2.2.2.2.2
  cases hroot:RegionSelection.chooseRoot (RegionLoop.weights I active) with
  | none =>
    have hfound:σ1.vars "find.found"=0:=by simpa only [hroot,Option.map_none,RamFind.Matches] using hm
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B σ1=some false:=by
      rw [evalB_condEq (evalB_var (hfound ▸ (by omega:0< B))) (evalB_lit (by omega)),hfound]
      rfl
    let τ:=σ1.setVar "region.phase" 2
    have ra:Run B (.assign "region.phase" (.lit 2)) σ1 τ 2:=Run.assign (evalB_lit h2)
    have rb:=Run.ite_false (c:=RamRegionLoop.foundRoot) hc ra
    have rr:=rpre.seq rb
    have rrun:Run B RamRegionLoop.iteration σ τ (RamRegionPrelude.cost n M+(1+(Cond.eq (.var "find.found") (.lit 1)).size+2)):=by
      simpa only [RamRegionLoop.iteration,RamRegionPrelude.command] using rr
    refine ⟨τ,rrun.mono (by dsimp [cost,Cond.size,Expr.size]; omega),
      Fixed.frame ra hf (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame ra hr,?_⟩
    simp only [Output,hroot]
    exact ⟨by simp [τ],by simpa only [Prefix,τ,arrs_setVar] using hs.historyData,
      (ra.frame_var _ (by decide)).trans hs.historyPosition,
      by simpa only [Prefix,τ,arrs_setVar] using hs.activeData⟩
  | some root =>
    have hfound:σ1.vars "find.found"=1∧ σ1.vars "find.result"=root.val:=by
      simpa only [hroot,Option.map_some,RamFind.Matches] using hm
    have hc:(Cond.eq (.var "find.found") (.lit 1)).evalB B σ1=some true:=by
      rw [evalB_condEq (evalB_var (hfound.1 ▸ (by omega:1< B))) (evalB_lit (by omega)),hfound.1]
      rfl
    let σ2:=σ1.setVar "region.root" root.val
    have rroot:Run B (.assign "region.root" (.var "find.result")) σ1 σ2 2:=
      Run.assign (by rw [evalB_var_iff]; exact ⟨hfound.2.symm,hfound.2 ▸ root.isLt.trans (by omega:n< B)⟩)
    have h2f:=Fixed.frame rroot hf (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have h2s:=Dynamic.frame rroot hs (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide)
    have h2r:=Room.frame rroot hr
    have hsetup:RamRegionSetup.Input (ResidualData.weights I active) (ResidualData.capacity I active)
        length root seed beta delta (RegionBudget.steps p) σ2:=
      ⟨h2f.nValue,h2f.n2Value,by simp [σ2],h2f.stepsValue,h2f.seedData,h2f.betaData,h2f.deltaData,h2f.unitData,
        by simpa only [Prefix,σ2,arrs_setVar] using ppre.2.2.2.2.1,
        by simpa only [Prefix,σ2,arrs_setVar] using ppre.2.2.2.1,h2f.lengthData⟩
    have hsetupRoom:RamRegionSetup.Room n (RegionBudget.steps p+1+2*n) σ2:=
      ⟨h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),
        h2r _ _ (by simp [extents]),h2r _ _ (by simp [extents]),
        by simpa only [Nat.mul_assoc] using h2r "region.crossing" (2*n*n) (by simp [extents])⟩
    obtain ⟨r,hsearch⟩:=RegionExecutionData.search_exists I length active root seed delta p hseed hdelta hp htri hcost
    have hsearch':RegionSearch.search (MetricMatrix.rational (ResidualData.capacity I active)) (MetricMatrix.rational length)
        (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)) seed delta p
        (RegionSelection.direction (fun v => (ResidualData.weights I active v:ℚ))
          (fun v => (length root v:ℚ)) (fun v => (length v root:ℚ)))=some r:=by
      simp only [ResidualData.rational_capacity,ResidualData.rational_weights]
      dsimp only [RegionLoop.chooseDirection,MetricMatrix.rational] at hsearch ⊢
      exact hsearch
    obtain ⟨σ3,rsearch,rn,heq,hmem,hyes,pa⟩:=RamRegionChoice.command_spec B M H
      (ResidualData.weights I active) (ResidualData.capacity I active) length root seed beta delta p
      hk hB hquery hindex hvertex hradius hl hd hu (hb root) hbeta r hsearch' σ2 ⟨hsetup,hsetupRoom⟩
    have h3f:=Fixed.frame rsearch h2f (by dsimp [names]; decide) (by dsimp [arrays]; decide)
    have h3s:=Dynamic.frame rsearch h2s (by dsimp [dynamicNames]; decide) (by dsimp [dynamicArrays]; decide)
    have h3r:=Room.frame rsearch h2r
    let q:=RadiusSearchData.atRadius (RegionExecutionData.query I length active root seed beta) rn
    have hbounds:RegionQueryHeight.Bounds q H:=by
      obtain ⟨i,hi,he⟩:=List.mem_iff_getElem.mp hmem
      subst rn
      exact hb root i hi
    have hbranch:RamRegionBranch.Input q threshold active history root σ3:=
      ⟨⟨pa.1,(rsearch.frame_var _ (by decide)).trans hsetup.rootValue,h3s.activeData,h3s.historyData,h3s.historyPosition⟩,
        h3s.phase,h3f.thresholdData,pa.2.1,pa.2.2.1⟩
    have hsmallRoom:RamSmallRegion.Room n history.length σ3:=
      ⟨(by have hh:=h3r "region.history" (4*p+4) (by simp [extents]); omega),
        (h3r "region.active" (2*n) (by simp [extents])).le,h3r "region.nextActive" (2*n) (by simp [extents])⟩
    obtain ⟨τ,rbranch,pbranch⟩:=RamRegionBranch.command_spec B H q threshold active history root hbounds hquery ht hvertex hlen rfl rfl σ3
      ⟨hbranch,hsmallRoom⟩
    have hqueryTest:(Cond.eq (.var "find.found") (.lit 1)).evalB B σ3=some true:=by
      rw [evalB_condEq (evalB_var (hyes ▸ (by omega:1< B))) (evalB_lit (by omega)),hyes]
      rfl
    have rfound:=rroot.seq (rsearch.seq (Run.ite_true (d:=.assign "region.phase" (.lit 3)) hqueryTest rbranch))
    have rr:=rpre.seq (Run.ite_true (d:=.assign "region.phase" (.lit 2)) hc rfound)
    change Run B RamRegionLoop.iteration σ τ _ at rr
    refine ⟨τ,rr.mono (by dsimp [cost,Cond.size,Expr.size]; omega),
      Fixed.frame rbranch h3f (by dsimp [names]; decide) (by dsimp [arrays]; decide),Room.frame rbranch h3r,?_⟩
    simp only [Output,hroot]
    exact ⟨rn,by rw [heq]; exact hsearch,pbranch⟩

end Lax455465Proofs.RamRegionCore

end

theorem solution:∀ (B M H:Nat) {n:Nat} (I:Lax455465.RationalEncoding.RationalInstance n)
  (length:Lax455465Proofs.MetricMatrix.Matrix n) (seed beta delta threshold:NNRat) (p:Nat)
  (active:Finset (Fin n)) (history:List (Lax455465Proofs.RamRegionRecord.Entry n)),
  Nat.le ((1:Nat)) M→
    Nat.le (Lax455465Proofs.RegionBudget.steps p) M→
      Nat.lt
          (Nat.add
            (Nat.mul ((2:Nat))
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) M
                ((2:Nat))))
            ((3:Nat)))
          B→
        Nat.lt
            (Nat.add
              (Nat.mul
                ((2:Nat))
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
                        (Nat.add (Lax455465Proofs.RegionBudget.steps p)
                          ((1:Nat)))
                        (Nat.mul
                          ((2:Nat)) n)))
                    ((2:Nat)))
                  B→
                Nat.lt
                    (Nat.add
                      (Nat.mul
                        ((4:Nat))
                        (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history))
                      ((4:Nat)))
                    B→
                  Lax455465Proofs.LpInputSize.Height
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat)) H)
                      (@NNRat.cast Rat Rat.instNNRatCast threshold)→
                    (∀ (v:Fin n),
                        Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).num M)→
                      (∀ (v:Fin n),
                          Nat.le (@Lax455465.RationalEncoding.RationalInstance.weight n I v).den M)→
                        (∀ (u v:Fin n),
                            Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).num
                              M)→
                          (∀ (u v:Fin n),
                              Nat.le (@Lax455465.RationalEncoding.RationalInstance.capacity n I u v).den
                                M)→
                            (∀ (u v:Fin n),
                                Lax455465Proofs.LpInputSize.Height M (@NNRat.cast Rat Rat.instNNRatCast (length u v)))→
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
                                          (Lax455465Proofs.RegionBudget.steps p))))→
                                  (∀ (root:Fin n) (i:Nat)
                                      (hi:
                                        Nat.lt i
                                          (@List.length NNRat
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta))),
                                      @Lax455465Proofs.RegionQueryHeight.Bounds n
                                        (@Lax455465Proofs.RadiusSearchData.atRadius n
                                          (@Lax455465Proofs.RegionExecutionData.query n I length active root seed beta)
                                          (@GetElem.getElem (List NNRat) Nat NNRat
                                            (fun (as:List NNRat) (i:Nat) =>
                                              Nat.lt i (@List.length NNRat as))
                                            (@List.instGetElemNatLtLength NNRat)
                                            (@Lax455465Proofs.RadiusData.candidates n (length root)
                                              (fun (v:Fin n) => length v root) (Lax455465Proofs.RegionBudget.steps p)
                                              delta)
                                            i hi))
                                        H)→
                                    @Eq Rat (@NNRat.cast Rat Rat.instNNRatCast beta)
                                        (Lax455465Proofs.RegionSearch.slope (Lax455465Proofs.RegionBudget.steps p)
                                          (@NNRat.cast Rat Rat.instNNRatCast delta))→
                                      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                          (@NNRat.cast Rat Rat.instNNRatCast seed)→
                                        @LT.lt Rat Rat.instLT
                                            (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))
                                            (@NNRat.cast Rat Rat.instNNRatCast delta)→
                                          Nat.lt ((0:Nat))
                                              p→
                                            (∀ (u v w:Fin n),
                                                @LE.le Rat Rat.instLE (@NNRat.cast Rat Rat.instNNRatCast (length u w))
                                                  (@HAdd.hAdd Rat Rat Rat (@instHAdd Rat Rat.instAdd)
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length u v))
                                                    (@NNRat.cast Rat Rat.instNNRatCast (length v w))))→
                                              @LE.le Rat Rat.instLE
                                                  (@Lax455465Proofs.RegionRounding.metricCost n I
                                                    (@Lax455465Proofs.MetricMatrix.rational n length))
                                                  (@HMul.hMul Rat Rat Rat (@instHMul Rat Rat.instMul)
                                                    (@Nat.cast Rat Rat.instNatCast p)
                                                    (@NNRat.cast Rat Rat.instNNRatCast seed))→
                                                Nat.le
                                                    (@List.length (Lax455465Proofs.RamRegionRecord.Entry n) history) p→
                                                  Lax808846Proofs.Reasoning.Spec B
                                                    (fun (σ:Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p σ)
                                                        (And
                                                          (@Lax455465Proofs.RamRegionInvariant.Dynamic n active history
                                                            σ)
                                                          (Lax455465Proofs.RamRegionInvariant.Room n p σ)))
                                                    Lax455465Proofs.RamRegionLoop.iteration
                                                    (fun (x τ:Lax808846Proofs.Imp.Env) =>
                                                      And
                                                        (@Lax455465Proofs.RamRegionInvariant.Fixed n I length seed beta
                                                          delta threshold p τ)
                                                        (And (Lax455465Proofs.RamRegionInvariant.Room n p τ)
                                                          (@Lax455465Proofs.RamRegionCore.Output n I length seed beta
                                                            delta threshold p active history τ)))
                                                    (Lax455465Proofs.RamRegionCore.cost n p M H):= @Lax455465Proofs.RamRegionCore.iteration_spec
