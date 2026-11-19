-- Prove2me | solution 1 for Lax109476Proofs.RamRationalFeasibility.decideFeasible_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T16:12:22.524801+00:00
-- url     : https://prove2.me/submissions/b1876d8f-1d05-44bd-a57b-354f5eb14e53

import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Fin.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBoundsInterfaces
import Theorems.Thm_Lax109476Proofs_RamSearchBounds_search_bounded_spec_native
import Theorems.Thm_Lax109476Proofs_RamFeasibilitySetup_setup_spec_native
import Theorems.Thm_Lax109476Proofs_RamFeasibilityQuery_copyInput_spec_native

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
namespace Lax263307Proofs.LightSeparators
end Lax263307Proofs.LightSeparators
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

namespace Lax109476Proofs.RamSearchBounds
end Lax109476Proofs.RamSearchBounds
theorem Lax109476Proofs.RamSearchBounds.search_bounded_spec:∀ {m n:Nat} (A:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Rat),
  LE.le ((2:Nat)) n→
    ∀ (N l w:Nat),
      (∀ (i:Fin m) (j:Fin n),
          LE.le (A i j).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) l))→
        (∀ (i:Fin m),
            Lax109476Proofs.RationalArithmeticBounds.Height (b i)
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) l))→
          LE.le (Lax109476Proofs.RamSearchBounds.wordWidth m n N l) w→
            Lax808846Proofs.Reasoning.Spec
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                ((2:Nat)) w)
              (@Lax109476Proofs.RamSearchBounds.Input m n A b N) Lax109476Proofs.RamSearchLoop.search
              (fun (x τ:Lax808846Proofs.Imp.Env) =>
                And (@Lax109476Proofs.RamSearchLoop.Invariant m n A b N τ)
                  (@Eq (Option Nat)
                    (Lax109476Proofs.EllipsoidSearch.findFirst
                      (fun (j:Nat) =>
                        @Decidable.decide
                          (@Eq (Option (Fin m))
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n→ Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))
                            (@Option.none (Fin m)))
                          (@Option.decidableEqNone (Fin m)
                            (@Lax109476Proofs.RationalSeparation.firstViolation m n A b
                              (@Prod.snd (Matrix (Fin n) (Fin n) Rat) (Fin n→ Rat)
                                (@Lax109476Proofs.EllipsoidSearch.trajectory m n A b j)))))
                      ((0:Nat)) N)
                    (@ite (Option Nat)
                      (@Eq Nat (τ.vars "search.found") ((1:Nat)))
                      (instDecidableEqNat (τ.vars "search.found")
                        ((1:Nat)))
                      (@Option.some Nat (τ.vars "iter.k")) (@Option.none Nat))))
              (Lax109476Proofs.RamSearchBounds.instructionBound m n N l):= @Lax109476Proofs.RamSearchBounds.search_bounded_spec_native
namespace Lax109476Proofs.RamFeasibilitySetup
end Lax109476Proofs.RamFeasibilitySetup
theorem Lax109476Proofs.RamFeasibilitySetup.setup_spec:∀ (m n S w:Nat) (P:Lax109476.LinearProgram.Program Int m n),
  LE.le (HAdd.hAdd m n) S→
    (∀ (i:Fin m) (j:Fin n),
        LE.le (@Lax109476.LinearProgram.Program.A Int m n P i j).natAbs
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat))
            (HMul.hMul ((2:Nat))
              S)))→
      (∀ (i:Fin m),
          LE.le (@Lax109476.LinearProgram.Program.b Int m n P i).natAbs
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat))
              (HMul.hMul
                ((2:Nat)) S)))→
        LE.le (Lax109476Proofs.RamFeasibilitySetup.wordWidth S) w→
          Lax808846Proofs.Reasoning.Spec
            (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
              ((2:Nat)) w)
            (@Lax109476Proofs.RamFeasibilitySetup.Input m n P S) Lax109476Proofs.RamFeasibilitySetup.setup
            (fun (x τ:Lax808846Proofs.Imp.Env) =>
              @Lax109476Proofs.RamSearchBounds.Input (HAdd.hAdd m n) n
                (@Lax109476Proofs.NormalizedFeasibility.normalizedMatrix m n P
                  (Lax109476Proofs.NormalizedFeasibility.outerScale n
                    (Lax109476Proofs.IntegerCertificates.coordinateCap m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat))
                        (HMul.hMul
                          ((2:Nat)) S)))))
                (@Lax109476Proofs.NormalizedFeasibility.normalizedBound m n P
                  (@HDiv.hDiv Rat Rat Rat (@instHDiv Rat Rat.instDiv)
                    (@OfNat.ofNat Rat (nat_lit 1) (@Rat.instOfNat (nat_lit 1)))
                    (@Nat.cast Rat Rat.instNatCast
                      (Lax109476Proofs.NormalizedFeasibility.precisionDenominator m n
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          ((2:Nat))
                          (HMul.hMul
                            ((2:Nat)) S))))))
                (HAdd.hAdd
                  (Lax109476Proofs.EllipsoidSequence.thresholdSteps n
                    (Lax109476Proofs.NormalizedFeasibility.ballExponent m n
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        ((2:Nat))
                        (HMul.hMul
                          ((2:Nat)) S))))
                  ((1:Nat)))
                τ)
            (Lax109476Proofs.RamFeasibilitySetup.instructionBound S):= @Lax109476Proofs.RamFeasibilitySetup.setup_spec_native
namespace Lax109476Proofs.RamFeasibilityQuery
end Lax109476Proofs.RamFeasibilityQuery
theorem Lax109476Proofs.RamFeasibilityQuery.copyInput_spec:∀ (m n:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (w:Nat),
  LE.le
      (Lax109476Proofs.RamDecoder.wordWidth
        (HMul.hMul ((2:Nat))
          (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))))
      w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamFeasibilityQuery.copyInput
      (fun (x τ:Lax808846Proofs.Imp.Env) =>
        @Lax109476Proofs.RamPaddedFeasibility.Input m n (@Lax109476Proofs.IntegerEncoding.integerProgram m n P)
          (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)) τ)
      (HAdd.hAdd
        (HMul.hMul ((71:Nat))
          (HAdd.hAdd (HMul.hMul m n) m))
        ((58:Nat))):= @Lax109476Proofs.RamFeasibilityQuery.copyInput_spec_native

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

theorem clearedNumerator_bound (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i).natAbs≤ (q i).num.natAbs * commonDenominator q:=by
  simp only [clearedNumerator,Int.natAbs_mul,Int.natAbs_natCast]
  exact Nat.mul_le_mul_left _ (Nat.div_le_self _ _)

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

theorem size_add_le (a b:ℕ):Nat.size (a + b)≤ Nat.size a + Nat.size b + 1:=by
  apply Nat.size_le.mpr
  rw [pow_succ,pow_add]
  have ha:=Nat.lt_size_self a
  have hb:=Nat.lt_size_self b
  have hpa:0 < 2 ^ Nat.size a:=by positivity
  have hpb:0 < 2 ^ Nat.size b:=by positivity
  have h₁:=Nat.le_mul_of_pos_right (2 ^ Nat.size a) hpb
  have h₂:=Nat.le_mul_of_pos_left (2 ^ Nat.size b) hpa
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

theorem dimension_bound {m n:ℕ} (P:Program ℚ m n):
    m + n≤ bitSize (encodeProgram P):=by
  have hb:m≤ ∑ i,bitSize (encodeRational (P.b i)):=by
    calc
      m=∑ _i:Fin m,1:=by simp
      _≤ _:=Finset.sum_le_sum (fun i _ => by have h:=(rational_size_bounds (P.b i)).1; omega)
  have hc:n≤ ∑ j,bitSize (encodeRational (P.c j)):=by
    calc
      n=∑ _j:Fin n,1:=by simp
      _≤ _:=Finset.sum_le_sum (fun j _ => by have h:=(rational_size_bounds (P.c j)).1; omega)
  rw [program_size]
  omega

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

theorem programDenominator_bound {m n:ℕ} (P:Program ℚ m n):
    programDenominator P≤ 2 ^ bitSize (encodeProgram P):=
  (commonDenominator_bound (programData P)).trans
    (Nat.pow_le_pow_right (by decide) (denominator_size_sum P))

theorem cleared_datum_bound {m n:ℕ} (P:Program ℚ m n) (i):
    (clearedNumerator (programData P) i).natAbs≤
      2 ^ (2 * bitSize (encodeProgram P)):=by
  have hn:(programData P i).num.natAbs≤ 2 ^ bitSize (encodeProgram P):=
    (Nat.lt_size_self _).le.trans
      (Nat.pow_le_pow_right (by decide) (datum_numerator_size P i))
  calc
    _≤ (programData P i).num.natAbs * programDenominator P:=
      clearedNumerator_bound _ i
    _≤ 2 ^ bitSize (encodeProgram P) * 2 ^ bitSize (encodeProgram P):=
      Nat.mul_le_mul hn (programDenominator_bound P)
    _=_:=by rw [← pow_add]; congr 1; omega

theorem integerProgram_bounds {m n:ℕ} (P:Program ℚ m n):
    (∀ i j, ((integerProgram P).A i j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ i, ((integerProgram P).b i).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P)))∧
    (∀ j, ((integerProgram P).c j).natAbs≤ 2 ^ (2 * bitSize (encodeProgram P))):=
  ⟨fun i j => cleared_datum_bound P (.inl (i,j)),
    fun i => cleared_datum_bound P (.inr (.inl i)),
    fun j => cleared_datum_bound P (.inr (.inr j))⟩

end Lax109476Proofs.IntegerEncoding

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence

theorem scanStates_eq_findFirst {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (start count:ℕ):
    scanStates A b start count (trajectory A b start) =
      findFirst (fun k => decide (firstViolation A b (trajectory A b k).2=none)) start count:=by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [scanStates,findFirst,decide_eq_true_eq]
    by_cases h:firstViolation A b (trajectory A b start).2=none
    · rw [if_pos h,if_pos h]
    · rw [if_neg h,if_neg h]
      exact ih (start + 1)

def search {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):Option (Fin n→ ℚ):=
  (findIteration A b K).map (fun k => (trajectory A b k).2)

end Lax109476Proofs.EllipsoidSearch

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

theorem outerScale_pos (n B:ℕ):0 < outerScale n B:=by
  unfold outerScale
  positivity

theorem precisionDenominator_pos (m n H:ℕ):0 < precisionDenominator m n H:=by
  unfold precisionDenominator relaxationDenominator
  positivity

end Lax109476Proofs.NormalizedFeasibility

end

section

open scoped BigOperators

namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

theorem padded_bounds {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H):
    (∀ i j, ((pad P).A i j).natAbs≤ H)∧ (∀ i, ((pad P).b i).natAbs≤ H):=by
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simpa [pad] using hA i j
      · intro j
        simp [pad]
    · intro i
      refine Fin.addCases ?_ ?_ j
      · intro j
        simp [pad]
      · intro j
        simp only [pad,Fin.addCases_right]
        split_ifs <;> simp_all
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad] using hb i
    · intro i
      simp [pad]

end Lax109476Proofs.FeasibilityPadding

end

section

namespace Lax109476Proofs.IterationBudget

open RationalSizeBounds IntegerCertificates NormalizedFeasibility EllipsoidSequence

theorem ballExponent_polynomial (m n S:ℕ) (hdim:m + n≤ S):
    ballExponent m n (2 ^ (2 * S))≤ 128 * (S + 1) ^ 2:=by
  let H:=2 ^ (2 * S)
  let B:=coordinateCap m n H
  let G:=m * B + n * m * H * B
  let D:=2 * (G + 1)
  let R:=4 * (n + 1) * (B + 1)
  have hsH:Nat.size H=2 * S + 1:=Nat.size_pow
  have hsB:Nat.size B≤ 32 * (S + 1) ^ 2:=
    certificate_cap_size (2 * (m + n) + 2) S (by omega)
  have hm:=size_le_self m
  have hn:=size_le_self n
  have hmb:=size_mul_le m B
  have hnmhb:=size_mul_le (n * m * H) B
  have hnmh:=size_mul_le (n * m) H
  have hnm:=size_mul_le n m
  have hG:=size_add_le (m * B) (n * m * H * B)
  have hGp:=size_add_one_le G
  have hD:=size_mul_le 2 (G + 1)
  have hNH:=size_add_one_le (n * H)
  have hnH:=size_mul_le n H
  have hR:=size_mul_le (4 * (n + 1)) (B + 1)
  have hRn:=size_mul_le 4 (n + 1)
  have hn1:=size_add_one_le n
  have hB1:=size_add_one_le B
  have hN:=size_mul_le (D * (n * H + 1)) R
  have hND:=size_mul_le D (n * H + 1)
  have hs2:Nat.size 2=2:=rfl
  have hs4:Nat.size 4=3:=rfl
  have hbound:Nat.size (D * (n * H + 1) * R)≤ 3 * Nat.size B + 7 * S + 12:=by
    dsimp only [D,G,R] at *
    omega
  change Nat.size (D * (n * H + 1) * R)≤ _
  nlinarith

theorem thresholdSteps_polynomial (m n S:ℕ) (hdim:m + n≤ S):
    thresholdSteps n (ballExponent m n (2 ^ (2 * S)))≤ 1024 * (S + 1) ^ 4:=by
  have hE:=ballExponent_polynomial m n S hdim
  have hn:n≤ S:=by omega
  have hEn:=Nat.mul_le_mul hE hn
  have hstep:=Nat.mul_le_mul (by omega:4 * (n + 1)≤ 4 * (S + 1))
    (Nat.add_le_add_right hEn 1)
  unfold thresholdSteps
  nlinarith

end Lax109476Proofs.IterationBudget

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

theorem height_zero:Height 0 1:=by simp [Height]

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

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

namespace Lax109476Proofs.RamPadEntries

open Lax109476.LinearProgram FeasibilityPadding RationalArithmeticBounds

def entry {m n:ℕ} (P:Program ℚ m n) (i:Fin (m + 2)) (j:Fin (n + 2)):ℚ:=
  if hi:i.val < m then
    if hj:j.val < n then P.A ⟨i.val,hi⟩ ⟨j.val,hj⟩ else 0
  else if n≤ j.val then if i.val - m=j.val - n then 1 else 0 else 0

theorem entry_eq {m n:ℕ} (P:Program ℚ m n) (i:Fin (m + 2)) (j:Fin (n + 2)):
    entry P i j=(pad P).A i j:=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    refine Fin.addCases ?_ ?_ j
    · intro j
      simp [entry,pad,i.isLt,j.isLt]
    · intro j
      have hj:¬ (Fin.natAdd n j).val < n:=by simp
      simp [entry,pad,i.isLt,hj]
  · intro i
    have hi:¬ (Fin.natAdd m i).val < m:=by simp
    refine Fin.addCases ?_ ?_ j
    · intro j
      have hj:¬ n≤ (Fin.castAdd 2 j).val:=by simpa using Nat.not_le.mpr j.isLt
      simp [entry,pad,hi,hj]
    · intro j
      simp [entry,pad,hi,Fin.ext_iff]

def values {m n:ℕ} (P:Program ℚ m n):Fin ((m + 2) * (n + 2))→ ℚ:=
  fun k => entry P k.divNat k.modNat

theorem values_eq {m n:ℕ} (P:Program ℚ m n):
    List.ofFn (values P)=RamMatrixStorage.flatten (pad P).A:=by
  unfold RamMatrixStorage.flatten values
  congr 1
  funext k
  exact entry_eq P k.divNat k.modNat

theorem entry_height {m n:ℕ} (P:Program ℚ m n) (M:ℕ) (hM:1≤ M)
    (hA:∀ i j,Height (P.A i j) M) (i:Fin (m + 2)) (j:Fin (n + 2)):
    Height (entry P i j) M:=by
  unfold entry
  split_ifs with hi hj hnonneg heq
  · exact hA _ _
  all_goals simp_all [Height]

end Lax109476Proofs.RamPadEntries

end

section

namespace Lax109476Proofs.RamPadSelector

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds

theorem constantFraction_spec (B v:ℕ) (h1:1 < B) (hv:v < B):
    Spec B (fun _ => True) (constantFraction v) (fun _ τ => FractionOutput (v:ℚ) τ) 6:=by
  intro σ _
  (expose_names;
    (refine let c0:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@Nat.cast Rat Rat.instNatCast v) τ) σ; let c1:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c2:Env:=Env.setVar c1 "rat.n" v; let c3:Env:=Env.setVar c2 "rat.d" ((1:Nat)); let c4:Nat→ Nat→ Nat:=Nat.add; let c5:Nat→ Nat:=c4 ((1:Nat)); let c6:Nat:=c5 (Expr.size (Expr.lit ((0:Nat)))); let c7:Nat:=c5 (Expr.size (Expr.lit v)); let c8:Nat:=c5 (Expr.size (Expr.lit ((1:Nat)))); let c9:Nat:=c4 c7 c8; let c10:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Exists.intro Env (fun (σ':Env) => And (Run B (constantFraction v) σ σ' ((6:Nat))) (c0 σ')) c3 (@And.intro (Run B (constantFraction v) σ c3 ((6:Nat))) (c0 c3) (RunStep.mono B (constantFraction v) σ c3 (c4 c6 c9) ((6:Nat)) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq (Com.assign "rat.n" (Expr.lit v)) c10) σ c1 c3 c6 c9 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4444_0_0_0))) (RunStep.seq B (Com.assign "rat.n" (Expr.lit v)) c10 c1 c2 c3 c7 c8 (RunStep.assign B c1 "rat.n" (Expr.lit v) v (RunStep.eval_lit B v c1 hv)) (RunStep.assign B c2 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c2 h1)))) (?nAX_g4444_0_0_1)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4444_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4444_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all))
  all_goals simp [FractionOutput,fractionValue]

def fields:List String:= ["source.m", "source.n", "pad.row", "pad.col"]

set_option maxHeartbeats 0 in
theorem selectEntry_spec (B M m n:ℕ) (P:Program ℚ m n)
    (i:Fin (m + 2)) (j:Fin (n + 2)) (h1:1 < B) (hM:1≤ M)
    (hMB:M < B) (hmB:m + 2 < B) (hnB:n + 2 < B) (hmnB:m * n < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ∧
        σ.vars "source.m"=m∧ σ.vars "source.n"=n∧
        σ.vars "pad.row"=i.val∧ σ.vars "pad.col"=j.val)
      selectEntry (fun _ τ => FractionOutput (entry P i j) τ) 40:=by
  have hiB:i.val < B:=i.isLt.trans hmB
  have hjB:j.val < B:=j.isLt.trans hnB
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hzero:=constantFraction_spec B 0 h1 (by omega)
  have hone:=constantFraction_spec B 1 h1 h1
  rintro σ ⟨hσA,hσm,hσn,hσi,hσj⟩
  by_cases hi:i.val < m
  · by_cases hj:j.val < n
    · let ii:Fin m:= ⟨i.val,hi⟩
      let jj:Fin n:= ⟨j.val,hj⟩
      let k:=i.val * n + j.val
      have hk:k < (RamMatrixStorage.flatten P.A).length:=by simpa [k,ii,jj,RamMatrixStorage.flatten] using RamMatrixStorage.row_index_lt ii jj
      have hkB:k < B:=(by simpa only [RamMatrixStorage.flatten,List.length_ofFn] using hk:k < m * n).trans hmnB
      have hmulB:i.val * n < B:=by dsimp [k] at hkB; omega
      have hentry:(RamMatrixStorage.flatten P.A)[k]=P.A ii jj:=RamMatrixStorage.flatten_entry P.A ii jj
      have hq:=hA ii jj
      have hload:=spec_with_fields fields
        (loadLeft_spec B "query.A" (RamMatrixStorage.flatten P.A) k hk h1 hkB
          (by rw [hentry]; exact hq.1.trans_lt hMB) (by rw [hentry]; exact hq.2.trans_lt hMB))
        (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
      have hresult:=RamCopy.leftToResult_spec B (P.A ii jj) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
      (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:=Nat.lt (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c6:Prop:=Not c5; let c7:Nat→ Nat→ Nat:=Nat.add; let c8:Nat:=Nat.mul (Env.vars σ "pad.row") (Env.vars σ "source.n"); let c9:Nat:=c7 c8 (Env.vars σ "pad.col"); let c10:Env:=Env.setVar σ "vec.i" c9; let c11:Env→ Nat→ Prop:=Run B (loadLeft "query.A") c10; let c12:List Rat:= @flatten m n (@Program.A Rat m n P); let c13:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c12 k hk); let c14:Env→ Prop:=FieldsAgree fields c10; let c15:String→ List Nat:=Env.arrs c10; let c16:Env→ Prop:=fun (σ':Env) => And (c11 σ' ((9:Nat))) (And (c13 σ') (And (c14 σ') (@Eq (String→ List Nat) (Env.arrs σ') c15))); let c17:Env→ Prop:=Represents "query.A" c12; let c18:Rat:= @Program.A Rat m n P ii jj; let c19:Env→ Prop:=FractionOutput c18; let c20:Env→ Prop:=LeftOutput c18; let c21:Nat→ Nat:=c7 ((1:Nat)); let c22:Nat→ Nat:=c7 (c21 (Cond.size (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")))); let c23:Nat→ Nat:=c7 (c21 (Cond.size (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")))); let c24:Expr:=Expr.add (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col"); let c25:Nat:=c21 (Expr.size c24); let c26:Nat:=c7 ((9:Nat)) ((6:Nat)); let c27:Nat:=c7 c25 c26; let c28:Nat:=c23 c27; let c29:Com:=Com.assign "vec.i" c24; let c30:Com:=Com.seq c29 (Com.seq (loadLeft "query.A") RamCopy.leftToResult); let c31:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c30 (constantFraction ((0:Nat))); let c32:Cond:=Cond.eq (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")); let c33:Com:=Com.ite c32 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))); let c34:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c33; let c35:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c36:Nat→ Env:=Env.setVar c35 "rat.n"; let c37:Env:=c36 ((0:Nat)); let c38:Env:=Env.setVar c37 "rat.d" ((1:Nat)); let c39:Nat:=c21 (Expr.size (Expr.lit ((0:Nat)))); let c40:Nat→ Nat:=c7 c39; let c41:Nat:=c21 (Expr.size (Expr.lit ((1:Nat)))); let c42:Nat:=c40 c41; let c43:Nat:=c40 c42; let c44:Nat:=c23 c43; let c45:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c46:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c47:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c48:Nat:=c47 (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c49:Nat:=c47 (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c50:Prop:= @Eq Nat c48 c49; let c51:Prop:=Not c50; let c52:Env:=c36 ((1:Nat)); let c53:Env:=Env.setVar c52 "rat.d" ((1:Nat)); let c54:Nat→ Nat:=c7 (c21 (Cond.size c32)); let c55:Nat:=c7 c41 c41; let c56:Nat:=c40 c55; let c57:Nat:=c54 c56; let c58:Nat:=c23 c57; let c59:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c60:Nat:=c54 c43; let c61:Nat:=c23 c60; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c4) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_1:c5) => @Exists.casesOn Env c16 (fun (x:@Exists Env c16) => @Exists Env c4) (RunStep.use B (fun (σ_1:Env) => And (c17 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") k)) (loadLeft "query.A") (fun (σ_1 τ:Env) => And (c13 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((9:Nat)) hload c10 ?_) fun (w:Env) (h:And (c11 w ((9:Nat))) (And (c13 w) (And (c14 w) (@Eq (String→ List Nat) (Env.arrs w) c15)))) => let c0_1:Prop:=c11 w ((9:Nat)); let c1_1:Prop:=And (c13 w) (And (c14 w) (@Eq (String→ List Nat) (Env.arrs w) c15)); let c2_1:Env→ Prop:=fun (σ':Env) => And (Run B RamCopy.leftToResult w σ' ((6:Nat))) (c19 σ'); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => @Exists Env c4) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c2_1 (fun (x:@Exists Env c2_1) => @Exists Env c4) (RunStep.use B c20 RamCopy.leftToResult (fun (x τ:Env) => c19 τ) ((6:Nat)) hresult w ?_) fun (w_1:Env) (h_1:And (Run B RamCopy.leftToResult w w_1 ((6:Nat))) (c19 w_1)) => let c0_2:Prop:=Run B RamCopy.leftToResult w w_1 ((6:Nat)); @And.casesOn c0_2 (c19 w_1) (fun (x:And c0_2 (c19 w_1)) => @Exists Env c4) h_1 fun (left_1:c0_2) (right_1:c19 w_1) => @Exists.intro Env c4 w_1 (@And.intro (Run B selectEntry σ w_1 ((40:Nat))) (c3 w_1) (RunStep.mono B selectEntry σ w_1 (c22 c28) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c31 c34 σ w_1 c28 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c30 (constantFraction ((0:Nat))) σ w_1 c27 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_3)) hcase_1) (RunStep.seq B c29 (Com.seq (loadLeft "query.A") RamCopy.leftToResult) σ c10 w_1 c25 c26 (RunStep.assign B σ "vec.i" c24 c9 (RunStep.eval_add B σ (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col") c8 (Env.vars σ "pad.col") (RunStep.eval_mul B σ (Expr.var "pad.row") (Expr.var "source.n") (Env.vars σ "pad.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_4)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_5)) ?_) (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_6)) ?_)) (RunStep.seq B (loadLeft "query.A") RamCopy.leftToResult c10 w w_1 ((9:Nat)) ((6:Nat)) left left_1)))) (?nAX_g4447_0_0_7)) ?_)) fun (hcase_1:c6) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((40:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c22 c44) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c31 c34 σ c38 c44 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_8)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_9)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c30 (constantFraction ((0:Nat))) σ c38 c43 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_10)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_11)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c45 c46) σ c35 c38 c39 c42 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_0_0_12))) (RunStep.seq B c45 c46 c35 c37 c38 c39 c41 (RunStep.assign B c35 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c35 (?nAX_g4447_0_0_13))) (RunStep.assign B c37 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c37 h1)))))) (?nAX_g4447_0_0_14)) ?_)) fun (hcase:c1) => @Or.casesOn c5 c6 (fun (x:Or c5 c6) => @Exists Env c4) (Classical.em c5) (fun (hcase_1:c5) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((40:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c22 c44) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c31 c34 σ c38 c44 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_15)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_16)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c33 σ c38 c43 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_17)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_18)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c45 c46) σ c35 c38 c39 c42 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_0_0_19))) (RunStep.seq B c45 c46 c35 c37 c38 c39 c41 (RunStep.assign B c35 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c35 (?nAX_g4447_0_0_20))) (RunStep.assign B c37 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c37 h1)))))) (?nAX_g4447_0_0_21)) ?_)) fun (hcase_1:c6) => @Or.casesOn c50 c51 (fun (x:Or c50 c51) => @Exists Env c4) (Classical.em c50) (fun (hcase_2:c50) => @Exists.intro Env c4 c53 (@And.intro (Run B selectEntry σ c53 ((40:Nat))) (c3 c53) (RunStep.mono B selectEntry σ c53 (c22 c58) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c31 c34 σ c53 c58 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_22)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_23)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c33 σ c53 c57 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_25)) hcase_1) (RunStep.ite_true B c32 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c53 c56 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c48 c49 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_26)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_27)) (?nAX_g4447_0_0_28)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_29)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_30)) (?nAX_g4447_0_0_31)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c59 c46) σ c35 c53 c39 c55 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_0_0_32))) (RunStep.seq B c59 c46 c35 c52 c53 c41 c41 (RunStep.assign B c35 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c35 h1)) (RunStep.assign B c52 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c52 h1))))))) (?nAX_g4447_0_0_33)) ?_)) fun (hcase_2:c51) => @Exists.intro Env c4 c38 (@And.intro (Run B selectEntry σ c38 ((40:Nat))) (c3 c38) (RunStep.mono B selectEntry σ c38 (c22 c61) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c31 c34 σ c38 c61 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_34)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_35)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c33 σ c38 c60 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_36)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_37)) hcase_1) (RunStep.ite_false B c32 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c38 c43 (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c48 c49 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_0_0_38)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_0_0_39)) (?nAX_g4447_0_0_40)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_0_0_41)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_0_0_42)) (?nAX_g4447_0_0_43)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c45 c46) σ c35 c38 c39 c42 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_0_0_44))) (RunStep.seq B c45 c46 c35 c37 c38 c39 c41 (RunStep.assign B c35 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c35 (?nAX_g4447_0_0_45))) (RunStep.assign B c37 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c37 h1))))))) (?nAX_g4447_0_0_46)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4447_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_0_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
      all_goals clear hload hresult
      all_goals simp_all [fields,FieldsAgree,entry,k,ii,jj,Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat:=Nat.mul (Env.vars σ "pad.row") (Env.vars σ "source.n"); let c10:Nat:=c8 c9 (Env.vars σ "pad.col"); let c11:Env:=Env.setVar σ "vec.i" c10; let c12:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "query.A"; let c13:String:=c12 ".s"; let c14:Nat:=Env.vars c11 "vec.i"; let c15:Nat:= @List.getD Nat (Env.arrs c11 c13) c14 ((0:Nat)); let c16:Env:=Env.setVar c11 "left.s" c15; let c17:String:=c12 ".n"; let c18:Nat:=Env.vars c16 "vec.i"; let c19:Nat:= @List.getD Nat (Env.arrs c16 c17) c18 ((0:Nat)); let c20:Env:=Env.setVar c16 "left.n" c19; let c21:String:=c12 ".d"; let c22:Nat:=Env.vars c20 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c20 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c20 "left.d" c23; let c25:Nat:=Env.vars c24 "left.s"; let c26:Env:=Env.setVar c24 "rat.s" c25; let c27:Nat:=Env.vars c26 "left.n"; let c28:Env:=Env.setVar c26 "rat.n" c27; let c29:Nat:=Env.vars c28 "left.d"; let c30:Env:=Env.setVar c28 "rat.d" c29; let c31:Nat→ Nat:=c8 ((1:Nat)); let c32:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")))); let c33:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")))); let c34:Expr:=Expr.add (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col"); let c35:Nat:=c31 (Expr.size c34); let c36:Expr:=Expr.get c13 (Expr.var "vec.i"); let c37:Nat:=c31 (Expr.size c36); let c38:Expr:=Expr.get c17 (Expr.var "vec.i"); let c39:Nat:=c31 (Expr.size c38); let c40:Expr:=Expr.get c21 (Expr.var "vec.i"); let c41:Nat:=c31 (Expr.size c40); let c42:Nat:=c8 c39 c41; let c43:Nat:=c8 c37 c42; let c44:Nat:=c31 (Expr.size (Expr.var "left.s")); let c45:Nat:=c31 (Expr.size (Expr.var "left.n")); let c46:Nat:=c31 (Expr.size (Expr.var "left.d")); let c47:Nat:=c8 c45 c46; let c48:Nat:=c8 c44 c47; let c49:Nat:=c8 c43 c48; let c50:Nat:=c8 c35 c49; let c51:Nat:=c33 c50; let c52:Com:=Com.assign "vec.i" c34; let c53:Com:=Com.seq c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult); let c54:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))); let c55:Cond:=Cond.eq (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")); let c56:Com:=Com.ite c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))); let c57:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56; let c58:Com:=Com.assign "left.n" c38; let c59:Com:=Com.assign "left.d" c40; let c60:Env→ Nat→ Prop:=Run B (constantFraction ((0:Nat))) σ; let c61:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c62:Env→ Prop:=fun (σ':Env) => And (c60 σ' ((6:Nat))) (c61 σ'); let c63:Nat:=c33 ((6:Nat)); let c64:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c65:Nat:=c64 (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c66:Nat:=c64 (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c67:Prop:= @Eq Nat c65 c66; let c68:Prop:=Not c67; let c69:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c70:Env:=Env.setVar c69 "rat.n" ((1:Nat)); let c71:Env:=Env.setVar c70 "rat.d" ((1:Nat)); let c72:Nat→ Nat:=c8 (c31 (Cond.size c55)); let c73:Nat:=c31 (Expr.size (Expr.lit ((0:Nat)))); let c74:Nat:=c31 (Expr.size (Expr.lit ((1:Nat)))); let c75:Nat:=c8 c74 c74; let c76:Nat:=c8 c73 c75; let c77:Nat:=c72 c76; let c78:Nat:=c33 c77; let c79:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c80:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c81:Nat:=c72 ((6:Nat)); let c82:Nat:=c33 c81; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c30 (@And.intro (Run B selectEntry σ c30 ((40:Nat))) (c3 c30) (RunStep.mono B selectEntry σ c30 (c32 c51) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c30 c51 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ c30 c50 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_3)) hcase_1) (RunStep.seq B c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult) σ c11 c30 c35 c49 (RunStep.assign B σ "vec.i" c34 c10 (RunStep.eval_add B σ (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col") c9 (Env.vars σ "pad.col") (RunStep.eval_mul B σ (Expr.var "pad.row") (Expr.var "source.n") (Env.vars σ "pad.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_4)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_5)) (?nAX_g4447_1_0_6)) (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_7)) (?nAX_g4447_1_0_8))) (RunStep.seq B (loadLeft "query.A") RamCopy.leftToResult c11 c24 c30 c43 c48 (RunStep.seq B (Com.assign "left.s" c36) (Com.seq c58 c59) c11 c16 c24 c37 c42 (RunStep.assign B c11 "left.s" c36 c15 (RunStep.eval_get B c11 c13 (Expr.var "vec.i") c14 (RunStep.eval_var B c11 "vec.i" (?nAX_g4447_1_0_9)) (?nAX_g4447_1_0_10) (?nAX_g4447_1_0_11))) (RunStep.seq B c58 c59 c16 c20 c24 c39 c41 (RunStep.assign B c16 "left.n" c38 c19 (RunStep.eval_get B c16 c17 (Expr.var "vec.i") c18 (RunStep.eval_var B c16 "vec.i" (?nAX_g4447_1_0_12)) (?nAX_g4447_1_0_13) (?nAX_g4447_1_0_14))) (RunStep.assign B c20 "left.d" c40 c23 (RunStep.eval_get B c20 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c20 "vec.i" (?nAX_g4447_1_0_15)) (?nAX_g4447_1_0_16) (?nAX_g4447_1_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c24 c26 c30 c44 c47 (RunStep.assign B c24 "rat.s" (Expr.var "left.s") c25 (RunStep.eval_var B c24 "left.s" (?nAX_g4447_1_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c26 c28 c30 c45 c46 (RunStep.assign B c26 "rat.n" (Expr.var "left.n") c27 (RunStep.eval_var B c26 "left.n" (?nAX_g4447_1_0_19))) (RunStep.assign B c28 "rat.d" (Expr.var "left.d") c29 (RunStep.eval_var B c28 "left.d" (?nAX_g4447_1_0_20))))))))) (?nAX_g4447_1_0_21)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_22)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_23)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_25)) hcase_1) left)) (?nAX_g4447_1_0_26)) ?_)) fun (hcase:c1) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_27)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_28)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_29)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_30)) hcase_1) left)) (?nAX_g4447_1_0_31)) ?_)) fun (hcase_1:c7) => @Or.casesOn c67 c68 (fun (x:Or c67 c68) => c5) (Classical.em c67) (fun (hcase_2:c67) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((40:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c32 c78) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c71 c78 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_33)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ c71 c77 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_34)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_35)) hcase_1) (RunStep.ite_true B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c71 c76 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_37)) (?nAX_g4447_1_0_38)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_39)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_40)) (?nAX_g4447_1_0_41)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c79 c80) σ c69 c71 c73 c75 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_1_0_42))) (RunStep.seq B c79 c80 c69 c70 c71 c74 c74 (RunStep.assign B c69 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c69 h1)) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1))))))) (?nAX_g4447_1_0_43)) ?_)) fun (hcase_2:c68) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c82) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_44)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_45)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w c81 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_46)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_47)) hcase_1) (RunStep.ite_false B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_1_0_48)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_1_0_49)) (?nAX_g4447_1_0_50)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_1_0_51)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_1_0_52)) (?nAX_g4447_1_0_53)) hcase_2) left))) (?nAX_g4447_1_0_54)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4447_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_1_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals simp_all [entry,Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
  · by_cases hj:j.val < n
    · (expose_names;
        (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat:=Nat.mul (Env.vars σ "pad.row") (Env.vars σ "source.n"); let c10:Nat:=c8 c9 (Env.vars σ "pad.col"); let c11:Env:=Env.setVar σ "vec.i" c10; let c12:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "query.A"; let c13:String:=c12 ".s"; let c14:Nat:=Env.vars c11 "vec.i"; let c15:Nat:= @List.getD Nat (Env.arrs c11 c13) c14 ((0:Nat)); let c16:Env:=Env.setVar c11 "left.s" c15; let c17:String:=c12 ".n"; let c18:Nat:=Env.vars c16 "vec.i"; let c19:Nat:= @List.getD Nat (Env.arrs c16 c17) c18 ((0:Nat)); let c20:Env:=Env.setVar c16 "left.n" c19; let c21:String:=c12 ".d"; let c22:Nat:=Env.vars c20 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c20 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c20 "left.d" c23; let c25:Nat:=Env.vars c24 "left.s"; let c26:Env:=Env.setVar c24 "rat.s" c25; let c27:Nat:=Env.vars c26 "left.n"; let c28:Env:=Env.setVar c26 "rat.n" c27; let c29:Nat:=Env.vars c28 "left.d"; let c30:Env:=Env.setVar c28 "rat.d" c29; let c31:Nat→ Nat:=c8 ((1:Nat)); let c32:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")))); let c33:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")))); let c34:Expr:=Expr.add (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col"); let c35:Nat:=c31 (Expr.size c34); let c36:Expr:=Expr.get c13 (Expr.var "vec.i"); let c37:Nat:=c31 (Expr.size c36); let c38:Expr:=Expr.get c17 (Expr.var "vec.i"); let c39:Nat:=c31 (Expr.size c38); let c40:Expr:=Expr.get c21 (Expr.var "vec.i"); let c41:Nat:=c31 (Expr.size c40); let c42:Nat:=c8 c39 c41; let c43:Nat:=c8 c37 c42; let c44:Nat:=c31 (Expr.size (Expr.var "left.s")); let c45:Nat:=c31 (Expr.size (Expr.var "left.n")); let c46:Nat:=c31 (Expr.size (Expr.var "left.d")); let c47:Nat:=c8 c45 c46; let c48:Nat:=c8 c44 c47; let c49:Nat:=c8 c43 c48; let c50:Nat:=c8 c35 c49; let c51:Nat:=c33 c50; let c52:Com:=Com.assign "vec.i" c34; let c53:Com:=Com.seq c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult); let c54:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))); let c55:Cond:=Cond.eq (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")); let c56:Com:=Com.ite c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))); let c57:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56; let c58:Com:=Com.assign "left.n" c38; let c59:Com:=Com.assign "left.d" c40; let c60:Env→ Nat→ Prop:=Run B (constantFraction ((0:Nat))) σ; let c61:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c62:Env→ Prop:=fun (σ':Env) => And (c60 σ' ((6:Nat))) (c61 σ'); let c63:Nat:=c33 ((6:Nat)); let c64:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c65:Nat:=c64 (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c66:Nat:=c64 (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c67:Prop:= @Eq Nat c65 c66; let c68:Prop:=Not c67; let c69:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c70:Env:=Env.setVar c69 "rat.n" ((1:Nat)); let c71:Env:=Env.setVar c70 "rat.d" ((1:Nat)); let c72:Nat→ Nat:=c8 (c31 (Cond.size c55)); let c73:Nat:=c31 (Expr.size (Expr.lit ((0:Nat)))); let c74:Nat:=c31 (Expr.size (Expr.lit ((1:Nat)))); let c75:Nat:=c8 c74 c74; let c76:Nat:=c8 c73 c75; let c77:Nat:=c72 c76; let c78:Nat:=c33 c77; let c79:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c80:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c81:Nat:=c72 ((6:Nat)); let c82:Nat:=c33 c81; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c30 (@And.intro (Run B selectEntry σ c30 ((40:Nat))) (c3 c30) (RunStep.mono B selectEntry σ c30 (c32 c51) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c30 c51 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ c30 c50 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_3)) hcase_1) (RunStep.seq B c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult) σ c11 c30 c35 c49 (RunStep.assign B σ "vec.i" c34 c10 (RunStep.eval_add B σ (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col") c9 (Env.vars σ "pad.col") (RunStep.eval_mul B σ (Expr.var "pad.row") (Expr.var "source.n") (Env.vars σ "pad.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_4)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_5)) (?nAX_g4447_2_0_6)) (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_7)) (?nAX_g4447_2_0_8))) (RunStep.seq B (loadLeft "query.A") RamCopy.leftToResult c11 c24 c30 c43 c48 (RunStep.seq B (Com.assign "left.s" c36) (Com.seq c58 c59) c11 c16 c24 c37 c42 (RunStep.assign B c11 "left.s" c36 c15 (RunStep.eval_get B c11 c13 (Expr.var "vec.i") c14 (RunStep.eval_var B c11 "vec.i" (?nAX_g4447_2_0_9)) (?nAX_g4447_2_0_10) (?nAX_g4447_2_0_11))) (RunStep.seq B c58 c59 c16 c20 c24 c39 c41 (RunStep.assign B c16 "left.n" c38 c19 (RunStep.eval_get B c16 c17 (Expr.var "vec.i") c18 (RunStep.eval_var B c16 "vec.i" (?nAX_g4447_2_0_12)) (?nAX_g4447_2_0_13) (?nAX_g4447_2_0_14))) (RunStep.assign B c20 "left.d" c40 c23 (RunStep.eval_get B c20 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c20 "vec.i" (?nAX_g4447_2_0_15)) (?nAX_g4447_2_0_16) (?nAX_g4447_2_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c24 c26 c30 c44 c47 (RunStep.assign B c24 "rat.s" (Expr.var "left.s") c25 (RunStep.eval_var B c24 "left.s" (?nAX_g4447_2_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c26 c28 c30 c45 c46 (RunStep.assign B c26 "rat.n" (Expr.var "left.n") c27 (RunStep.eval_var B c26 "left.n" (?nAX_g4447_2_0_19))) (RunStep.assign B c28 "rat.d" (Expr.var "left.d") c29 (RunStep.eval_var B c28 "left.d" (?nAX_g4447_2_0_20))))))))) (?nAX_g4447_2_0_21)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_22)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_23)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_25)) hcase_1) left)) (?nAX_g4447_2_0_26)) ?_)) fun (hcase:c1) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_27)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_28)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_29)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_30)) hcase_1) left)) (?nAX_g4447_2_0_31)) ?_)) fun (hcase_1:c7) => @Or.casesOn c67 c68 (fun (x:Or c67 c68) => c5) (Classical.em c67) (fun (hcase_2:c67) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((40:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c32 c78) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c71 c78 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_33)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ c71 c77 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_34)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_35)) hcase_1) (RunStep.ite_true B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c71 c76 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_37)) (?nAX_g4447_2_0_38)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_39)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_40)) (?nAX_g4447_2_0_41)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c79 c80) σ c69 c71 c73 c75 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_2_0_42))) (RunStep.seq B c79 c80 c69 c70 c71 c74 c74 (RunStep.assign B c69 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c69 h1)) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1))))))) (?nAX_g4447_2_0_43)) ?_)) fun (hcase_2:c68) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c82) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_44)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_45)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w c81 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_46)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_47)) hcase_1) (RunStep.ite_false B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_2_0_48)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_2_0_49)) (?nAX_g4447_2_0_50)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_2_0_51)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_2_0_52)) (?nAX_g4447_2_0_53)) hcase_2) left))) (?nAX_g4447_2_0_54)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4447_2_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_2_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
      all_goals simp_all [entry,Represents]
      all_goals (try split_ifs) <;> (try simp_all) <;> omega
    · by_cases he:i.val - m=j.val - n
      · (expose_names;
          (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat:=Nat.mul (Env.vars σ "pad.row") (Env.vars σ "source.n"); let c10:Nat:=c8 c9 (Env.vars σ "pad.col"); let c11:Env:=Env.setVar σ "vec.i" c10; let c12:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "query.A"; let c13:String:=c12 ".s"; let c14:Nat:=Env.vars c11 "vec.i"; let c15:Nat:= @List.getD Nat (Env.arrs c11 c13) c14 ((0:Nat)); let c16:Env:=Env.setVar c11 "left.s" c15; let c17:String:=c12 ".n"; let c18:Nat:=Env.vars c16 "vec.i"; let c19:Nat:= @List.getD Nat (Env.arrs c16 c17) c18 ((0:Nat)); let c20:Env:=Env.setVar c16 "left.n" c19; let c21:String:=c12 ".d"; let c22:Nat:=Env.vars c20 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c20 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c20 "left.d" c23; let c25:Nat:=Env.vars c24 "left.s"; let c26:Env:=Env.setVar c24 "rat.s" c25; let c27:Nat:=Env.vars c26 "left.n"; let c28:Env:=Env.setVar c26 "rat.n" c27; let c29:Nat:=Env.vars c28 "left.d"; let c30:Env:=Env.setVar c28 "rat.d" c29; let c31:Nat→ Nat:=c8 ((1:Nat)); let c32:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")))); let c33:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")))); let c34:Expr:=Expr.add (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col"); let c35:Nat:=c31 (Expr.size c34); let c36:Expr:=Expr.get c13 (Expr.var "vec.i"); let c37:Nat:=c31 (Expr.size c36); let c38:Expr:=Expr.get c17 (Expr.var "vec.i"); let c39:Nat:=c31 (Expr.size c38); let c40:Expr:=Expr.get c21 (Expr.var "vec.i"); let c41:Nat:=c31 (Expr.size c40); let c42:Nat:=c8 c39 c41; let c43:Nat:=c8 c37 c42; let c44:Nat:=c31 (Expr.size (Expr.var "left.s")); let c45:Nat:=c31 (Expr.size (Expr.var "left.n")); let c46:Nat:=c31 (Expr.size (Expr.var "left.d")); let c47:Nat:=c8 c45 c46; let c48:Nat:=c8 c44 c47; let c49:Nat:=c8 c43 c48; let c50:Nat:=c8 c35 c49; let c51:Nat:=c33 c50; let c52:Com:=Com.assign "vec.i" c34; let c53:Com:=Com.seq c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult); let c54:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))); let c55:Cond:=Cond.eq (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")); let c56:Com:=Com.ite c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))); let c57:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56; let c58:Com:=Com.assign "left.n" c38; let c59:Com:=Com.assign "left.d" c40; let c60:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c61:Env:=Env.setVar c60 "rat.n" ((0:Nat)); let c62:Env:=Env.setVar c61 "rat.d" ((1:Nat)); let c63:Nat:=c31 (Expr.size (Expr.lit ((0:Nat)))); let c64:Nat→ Nat:=c8 c63; let c65:Nat:=c31 (Expr.size (Expr.lit ((1:Nat)))); let c66:Nat:=c64 c65; let c67:Nat:=c64 c66; let c68:Nat:=c33 c67; let c69:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c70:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c71:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c72:Nat:=c71 (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c73:Nat:=c71 (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c74:Prop:= @Eq Nat c72 c73; let c75:Prop:=Not c74; let c76:Env→ Nat→ Prop:=Run B (constantFraction ((1:Nat))) σ; let c77:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((1:Nat))); let c78:Env→ Prop:=fun (σ':Env) => And (c76 σ' ((6:Nat))) (c77 σ'); let c79:Nat→ Nat:=c8 (c31 (Cond.size c55)); let c80:Nat:=c79 ((6:Nat)); let c81:Nat:=c33 c80; let c82:Nat:=c79 c67; let c83:Nat:=c33 c82; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c30 (@And.intro (Run B selectEntry σ c30 ((40:Nat))) (c3 c30) (RunStep.mono B selectEntry σ c30 (c32 c51) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c30 c51 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ c30 c50 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_3)) hcase_1) (RunStep.seq B c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult) σ c11 c30 c35 c49 (RunStep.assign B σ "vec.i" c34 c10 (RunStep.eval_add B σ (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col") c9 (Env.vars σ "pad.col") (RunStep.eval_mul B σ (Expr.var "pad.row") (Expr.var "source.n") (Env.vars σ "pad.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_4)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_5)) (?nAX_g4447_3_0_6)) (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_7)) (?nAX_g4447_3_0_8))) (RunStep.seq B (loadLeft "query.A") RamCopy.leftToResult c11 c24 c30 c43 c48 (RunStep.seq B (Com.assign "left.s" c36) (Com.seq c58 c59) c11 c16 c24 c37 c42 (RunStep.assign B c11 "left.s" c36 c15 (RunStep.eval_get B c11 c13 (Expr.var "vec.i") c14 (RunStep.eval_var B c11 "vec.i" (?nAX_g4447_3_0_9)) (?nAX_g4447_3_0_10) (?nAX_g4447_3_0_11))) (RunStep.seq B c58 c59 c16 c20 c24 c39 c41 (RunStep.assign B c16 "left.n" c38 c19 (RunStep.eval_get B c16 c17 (Expr.var "vec.i") c18 (RunStep.eval_var B c16 "vec.i" (?nAX_g4447_3_0_12)) (?nAX_g4447_3_0_13) (?nAX_g4447_3_0_14))) (RunStep.assign B c20 "left.d" c40 c23 (RunStep.eval_get B c20 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c20 "vec.i" (?nAX_g4447_3_0_15)) (?nAX_g4447_3_0_16) (?nAX_g4447_3_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c24 c26 c30 c44 c47 (RunStep.assign B c24 "rat.s" (Expr.var "left.s") c25 (RunStep.eval_var B c24 "left.s" (?nAX_g4447_3_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c26 c28 c30 c45 c46 (RunStep.assign B c26 "rat.n" (Expr.var "left.n") c27 (RunStep.eval_var B c26 "left.n" (?nAX_g4447_3_0_19))) (RunStep.assign B c28 "rat.d" (Expr.var "left.d") c29 (RunStep.eval_var B c28 "left.d" (?nAX_g4447_3_0_20))))))))) (?nAX_g4447_3_0_21)) ?_)) fun (hcase_1:c7) => @Exists.intro Env c4 c62 (@And.intro (Run B selectEntry σ c62 ((40:Nat))) (c3 c62) (RunStep.mono B selectEntry σ c62 (c32 c68) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c62 c68 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_22)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_23)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ c62 c67 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_25)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c69 c70) σ c60 c62 c63 c66 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_3_0_26))) (RunStep.seq B c69 c70 c60 c61 c62 c63 c65 (RunStep.assign B c60 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c60 (?nAX_g4447_3_0_27))) (RunStep.assign B c61 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c61 h1)))))) (?nAX_g4447_3_0_28)) ?_)) fun (hcase:c1) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c62 (@And.intro (Run B selectEntry σ c62 ((40:Nat))) (c3 c62) (RunStep.mono B selectEntry σ c62 (c32 c68) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c62 c68 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_29)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_30)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ c62 c67 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_31)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_32)) hcase_1) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c69 c70) σ c60 c62 c63 c66 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_3_0_33))) (RunStep.seq B c69 c70 c60 c61 c62 c63 c65 (RunStep.assign B c60 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c60 (?nAX_g4447_3_0_34))) (RunStep.assign B c61 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c61 h1)))))) (?nAX_g4447_3_0_35)) ?_)) fun (hcase_1:c7) => @Or.casesOn c74 c75 (fun (x:Or c74 c75) => c5) (Classical.em c74) (fun (hcase_2:c74) => @Exists.casesOn Env c78 (fun (x:@Exists Env c78) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((1:Nat))) (fun (x τ:Env) => c77 τ) ((6:Nat)) hone σ ?_) fun (w:Env) (h:And (c76 w ((6:Nat))) (c77 w)) => let c0_1:Prop:=c76 w ((6:Nat)); @And.casesOn c0_1 (c77 w) (fun (x:And c0_1 (c77 w)) => c5) h fun (left:c0_1) (right:c77 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c81) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c81 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_37)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w c80 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_38)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_39)) hcase_1) (RunStep.ite_true B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c72 c73 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_40)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_41)) (?nAX_g4447_3_0_42)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_43)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_44)) (?nAX_g4447_3_0_45)) hcase_2) left))) (?nAX_g4447_3_0_46)) ?_)) fun (hcase_2:c75) => @Exists.intro Env c4 c62 (@And.intro (Run B selectEntry σ c62 ((40:Nat))) (c3 c62) (RunStep.mono B selectEntry σ c62 (c32 c83) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c62 c83 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_47)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_48)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ c62 c82 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_49)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_50)) hcase_1) (RunStep.ite_false B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c62 c67 (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c72 c73 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_3_0_51)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_3_0_52)) (?nAX_g4447_3_0_53)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_3_0_54)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_3_0_55)) (?nAX_g4447_3_0_56)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c69 c70) σ c60 c62 c63 c66 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_3_0_57))) (RunStep.seq B c69 c70 c60 c61 c62 c63 c65 (RunStep.assign B c60 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c60 (?nAX_g4447_3_0_58))) (RunStep.assign B c61 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c61 h1))))))) (?nAX_g4447_3_0_59)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4447_3_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_55 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_56 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_57 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_58 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_3_0_59 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
        all_goals simp_all [entry,Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega
      · (expose_names;
          (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=FractionOutput (@entry m n P i j); let c3:Env→ Prop:=(fun (x τ:Env) => c2 τ) σ; let c4:Env→ Prop:=fun (σ':Env) => And (Run B selectEntry σ σ' ((40:Nat))) (c3 σ'); let c5:Prop:= @Exists Env c4; let c6:Prop:=Nat.lt (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c7:Prop:=Not c6; let c8:Nat→ Nat→ Nat:=Nat.add; let c9:Nat:=Nat.mul (Env.vars σ "pad.row") (Env.vars σ "source.n"); let c10:Nat:=c8 c9 (Env.vars σ "pad.col"); let c11:Env:=Env.setVar σ "vec.i" c10; let c12:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "query.A"; let c13:String:=c12 ".s"; let c14:Nat:=Env.vars c11 "vec.i"; let c15:Nat:= @List.getD Nat (Env.arrs c11 c13) c14 ((0:Nat)); let c16:Env:=Env.setVar c11 "left.s" c15; let c17:String:=c12 ".n"; let c18:Nat:=Env.vars c16 "vec.i"; let c19:Nat:= @List.getD Nat (Env.arrs c16 c17) c18 ((0:Nat)); let c20:Env:=Env.setVar c16 "left.n" c19; let c21:String:=c12 ".d"; let c22:Nat:=Env.vars c20 "vec.i"; let c23:Nat:= @List.getD Nat (Env.arrs c20 c21) c22 ((0:Nat)); let c24:Env:=Env.setVar c20 "left.d" c23; let c25:Nat:=Env.vars c24 "left.s"; let c26:Env:=Env.setVar c24 "rat.s" c25; let c27:Nat:=Env.vars c26 "left.n"; let c28:Env:=Env.setVar c26 "rat.n" c27; let c29:Nat:=Env.vars c28 "left.d"; let c30:Env:=Env.setVar c28 "rat.d" c29; let c31:Nat→ Nat:=c8 ((1:Nat)); let c32:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")))); let c33:Nat→ Nat:=c8 (c31 (Cond.size (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")))); let c34:Expr:=Expr.add (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col"); let c35:Nat:=c31 (Expr.size c34); let c36:Expr:=Expr.get c13 (Expr.var "vec.i"); let c37:Nat:=c31 (Expr.size c36); let c38:Expr:=Expr.get c17 (Expr.var "vec.i"); let c39:Nat:=c31 (Expr.size c38); let c40:Expr:=Expr.get c21 (Expr.var "vec.i"); let c41:Nat:=c31 (Expr.size c40); let c42:Nat:=c8 c39 c41; let c43:Nat:=c8 c37 c42; let c44:Nat:=c31 (Expr.size (Expr.var "left.s")); let c45:Nat:=c31 (Expr.size (Expr.var "left.n")); let c46:Nat:=c31 (Expr.size (Expr.var "left.d")); let c47:Nat:=c8 c45 c46; let c48:Nat:=c8 c44 c47; let c49:Nat:=c8 c43 c48; let c50:Nat:=c8 c35 c49; let c51:Nat:=c33 c50; let c52:Com:=Com.assign "vec.i" c34; let c53:Com:=Com.seq c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult); let c54:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))); let c55:Cond:=Cond.eq (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")); let c56:Com:=Com.ite c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))); let c57:Com:=Com.ite (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56; let c58:Com:=Com.assign "left.n" c38; let c59:Com:=Com.assign "left.d" c40; let c60:Env→ Nat→ Prop:=Run B (constantFraction ((0:Nat))) σ; let c61:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c62:Env→ Prop:=fun (σ':Env) => And (c60 σ' ((6:Nat))) (c61 σ'); let c63:Nat:=c33 ((6:Nat)); let c64:Nat→ Nat→ Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat); let c65:Nat:=c64 (Env.vars σ "pad.row") (Env.vars σ "source.m"); let c66:Nat:=c64 (Env.vars σ "pad.col") (Env.vars σ "source.n"); let c67:Prop:= @Eq Nat c65 c66; let c68:Prop:=Not c67; let c69:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c70:Env:=Env.setVar c69 "rat.n" ((1:Nat)); let c71:Env:=Env.setVar c70 "rat.d" ((1:Nat)); let c72:Nat→ Nat:=c8 (c31 (Cond.size c55)); let c73:Nat:=c31 (Expr.size (Expr.lit ((0:Nat)))); let c74:Nat:=c31 (Expr.size (Expr.lit ((1:Nat)))); let c75:Nat:=c8 c74 c74; let c76:Nat:=c8 c73 c75; let c77:Nat:=c72 c76; let c78:Nat:=c33 c77; let c79:Com:=Com.assign "rat.n" (Expr.lit ((1:Nat))); let c80:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); let c81:Nat:=c72 ((6:Nat)); let c82:Nat:=c33 c81; @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c5) (Classical.em c0) (fun (hcase:c0) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.intro Env c4 c30 (@And.intro (Run B selectEntry σ c30 ((40:Nat))) (c3 c30) (RunStep.mono B selectEntry σ c30 (c32 c51) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c30 c51 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_1)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ c30 c50 (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_2)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_3)) hcase_1) (RunStep.seq B c52 (Com.seq (loadLeft "query.A") RamCopy.leftToResult) σ c11 c30 c35 c49 (RunStep.assign B σ "vec.i" c34 c10 (RunStep.eval_add B σ (Expr.mul (Expr.var "pad.row") (Expr.var "source.n")) (Expr.var "pad.col") c9 (Env.vars σ "pad.col") (RunStep.eval_mul B σ (Expr.var "pad.row") (Expr.var "source.n") (Env.vars σ "pad.row") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_4)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_5)) (?nAX_g4447_4_0_6)) (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_7)) (?nAX_g4447_4_0_8))) (RunStep.seq B (loadLeft "query.A") RamCopy.leftToResult c11 c24 c30 c43 c48 (RunStep.seq B (Com.assign "left.s" c36) (Com.seq c58 c59) c11 c16 c24 c37 c42 (RunStep.assign B c11 "left.s" c36 c15 (RunStep.eval_get B c11 c13 (Expr.var "vec.i") c14 (RunStep.eval_var B c11 "vec.i" (?nAX_g4447_4_0_9)) (?nAX_g4447_4_0_10) (?nAX_g4447_4_0_11))) (RunStep.seq B c58 c59 c16 c20 c24 c39 c41 (RunStep.assign B c16 "left.n" c38 c19 (RunStep.eval_get B c16 c17 (Expr.var "vec.i") c18 (RunStep.eval_var B c16 "vec.i" (?nAX_g4447_4_0_12)) (?nAX_g4447_4_0_13) (?nAX_g4447_4_0_14))) (RunStep.assign B c20 "left.d" c40 c23 (RunStep.eval_get B c20 c21 (Expr.var "vec.i") c22 (RunStep.eval_var B c20 "vec.i" (?nAX_g4447_4_0_15)) (?nAX_g4447_4_0_16) (?nAX_g4447_4_0_17))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c24 c26 c30 c44 c47 (RunStep.assign B c24 "rat.s" (Expr.var "left.s") c25 (RunStep.eval_var B c24 "left.s" (?nAX_g4447_4_0_18))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c26 c28 c30 c45 c46 (RunStep.assign B c26 "rat.n" (Expr.var "left.n") c27 (RunStep.eval_var B c26 "left.n" (?nAX_g4447_4_0_19))) (RunStep.assign B c28 "rat.d" (Expr.var "left.d") c29 (RunStep.eval_var B c28 "left.d" (?nAX_g4447_4_0_20))))))))) (?nAX_g4447_4_0_21)) ?_)) fun (hcase_1:c7) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_true B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_22)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_23)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) c53 (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_24)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_25)) hcase_1) left)) (?nAX_g4447_4_0_26)) ?_)) fun (hcase:c1) => @Or.casesOn c6 c7 (fun (x:Or c6 c7) => c5) (Classical.em c6) (fun (hcase_1:c6) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c63) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c63 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_27)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_28)) hcase) (RunStep.ite_true B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w ((6:Nat)) (RunStep.cond_lt_true B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_29)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_30)) hcase_1) left)) (?nAX_g4447_4_0_31)) ?_)) fun (hcase_1:c7) => @Or.casesOn c67 c68 (fun (x:Or c67 c68) => c5) (Classical.em c67) (fun (hcase_2:c67) => @Exists.intro Env c4 c71 (@And.intro (Run B selectEntry σ c71 ((40:Nat))) (c3 c71) (RunStep.mono B selectEntry σ c71 (c32 c78) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ c71 c78 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_32)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_33)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ c71 c77 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_34)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_35)) hcase_1) (RunStep.ite_true B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ c71 c76 (RunStep.cond_eq_true B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_36)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_37)) (?nAX_g4447_4_0_38)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_39)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_40)) (?nAX_g4447_4_0_41)) hcase_2) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c79 c80) σ c69 c71 c73 c75 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4447_4_0_42))) (RunStep.seq B c79 c80 c69 c70 c71 c74 c74 (RunStep.assign B c69 "rat.n" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c69 h1)) (RunStep.assign B c70 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c70 h1))))))) (?nAX_g4447_4_0_43)) ?_)) fun (hcase_2:c68) => @Exists.casesOn Env c62 (fun (x:@Exists Env c62) => c5) (RunStep.use B (fun (x:Env) => True) (constantFraction ((0:Nat))) (fun (x τ:Env) => c61 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c60 w ((6:Nat))) (c61 w)) => let c0_1:Prop:=c60 w ((6:Nat)); @And.casesOn c0_1 (c61 w) (fun (x:And c0_1 (c61 w)) => c5) h fun (left:c0_1) (right:c61 w) => @Exists.intro Env c4 w (@And.intro (Run B selectEntry σ w ((40:Nat))) (c3 w) (RunStep.mono B selectEntry σ w (c32 c82) ((40:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.row") (Expr.var "source.m")) c54 c57 σ w c82 (RunStep.cond_lt_false B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_44)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_45)) hcase) (RunStep.ite_false B (Cond.lt (Expr.var "pad.col") (Expr.var "source.n")) (constantFraction ((0:Nat))) c56 σ w c81 (RunStep.cond_lt_false B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_46)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_47)) hcase_1) (RunStep.ite_false B c55 (constantFraction ((1:Nat))) (constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_eq_false B σ (Expr.sub (Expr.var "pad.row") (Expr.var "source.m")) (Expr.sub (Expr.var "pad.col") (Expr.var "source.n")) c65 c66 (RunStep.eval_sub B σ (Expr.var "pad.row") (Expr.var "source.m") (Env.vars σ "pad.row") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.row" (?nAX_g4447_4_0_48)) (RunStep.eval_var B σ "source.m" (?nAX_g4447_4_0_49)) (?nAX_g4447_4_0_50)) (RunStep.eval_sub B σ (Expr.var "pad.col") (Expr.var "source.n") (Env.vars σ "pad.col") (Env.vars σ "source.n") (RunStep.eval_var B σ "pad.col" (?nAX_g4447_4_0_51)) (RunStep.eval_var B σ "source.n" (?nAX_g4447_4_0_52)) (?nAX_g4447_4_0_53)) hcase_2) left))) (?nAX_g4447_4_0_54)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4447_4_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_19 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_20 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_21 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_22 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_23 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_24 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_25 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_26 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_27 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_28 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_29 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_30 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_31 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_32 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_33 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_34 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_35 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_36 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_37 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_38 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_39 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_40 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_41 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_42 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_43 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_44 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_45 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_46 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_47 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_48 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_49 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_50 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_51 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_52 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_53 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4447_4_0_54 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
        all_goals simp_all [entry,Represents]
        all_goals (try split_ifs) <;> (try simp_all) <;> omega

end Lax109476Proofs.RamPadSelector

end

section

namespace Lax109476Proofs.RamEllipsoidBitBounds

open RamDotProduct RamEllipsoidForm RamEllipsoidStep RamEllipsoidCoefficients
open RamShapeCoordinate RamShapeUpdate RationalSizeBounds

theorem wordWidth_monotone {n h k n' h' k':ℕ} (hn:n≤ n') (hh:h≤ h') (hk:k≤ k'):
    wordWidth n h k≤ wordWidth n' h' k':=by
  have hi:(2 * h + 1) * (n + 1)≤ (2 * h' + 1) * (n' + 1):=
    Nat.mul_le_mul (by omega) (by omega)
  have hf:formExponent n h≤ formExponent n' h':=
    Nat.mul_le_mul (by omega) (by omega)
  have hnn:=Nat.mul_le_mul hn hn
  unfold wordWidth magnitudeExponent
  omega

end Lax109476Proofs.RamEllipsoidBitBounds

end

section

namespace Lax109476Proofs.RamNormalizedBounds

open Lax109476.LinearProgram
open IntegerCertificates NormalizedFeasibility RationalArithmeticBounds

theorem factors_le_ball (m n H:ℕ):
    precisionDenominator m n H≤ ballDenominator m n H∧
      outerScale n (coordinateCap m n H)≤ ballDenominator m n H:=by
  have hD:=precisionDenominator_pos m n H
  have hR:=outerScale_pos n (coordinateCap m n H)
  have hN:0 < n * H + 1:=by omega
  unfold ballDenominator
  exact ⟨(Nat.le_mul_of_pos_right _ hN).trans (Nat.le_mul_of_pos_right _ hR),
    Nat.le_mul_of_pos_left _ (Nat.mul_pos hD hN)⟩

theorem normalized_bounds (m n S:ℕ) (P:Program ℤ m n) (hdim:m + n≤ S)
    (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S)):
    (∀ i j, (normalizedMatrix P (outerScale n (coordinateCap m n (2 ^ (2 * S)))) i j).natAbs≤
      2 ^ coefficientBits S)∧
    (∀ i,Height (normalizedBound P (1 / (precisionDenominator m n (2 ^ (2 * S)):ℚ)) i)
      (2 ^ coefficientBits S)):=by
  let H:=2 ^ (2 * S)
  let D:=precisionDenominator m n H
  let R:=outerScale n (coordinateCap m n H)
  let E:=128 * (S + 1) ^ 2
  have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have hD:1≤ D:=precisionDenominator_pos _ _ _
  have hsmall:=IterationBudget.ballExponent_polynomial m n S hdim
  have hZ:ballDenominator m n H≤ 2 ^ E:=(Nat.lt_size_self _).le.trans
    (Nat.pow_le_pow_right (by decide) hsmall)
  have hf:=factors_le_ball m n H
  have hDb:D≤ 2 ^ E:=hf.1.trans hZ
  have hRb:R≤ 2 ^ E:=hf.2.trans hZ
  have hmul:R * H≤ 2 ^ (E + 2 * S):=by
    rw [pow_add]
    exact Nat.mul_le_mul hRb le_rfl
  have hmulB:R * H≤ 2 ^ coefficientBits S:=hmul.trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [coefficientBits,E]; omega))
  have hRBound:R≤ 2 ^ coefficientBits S:=
    (Nat.le_mul_of_pos_right _ (by omega:0 < H)).trans hmulB
  have hadd:2 * H * D≤ 2 ^ coefficientBits S:=by
    have hp:=Nat.mul_le_mul_left (2 * H) hDb
    have he:2 * H * 2 ^ E=2 ^ (1 + 2 * S + E):=by
      dsimp [H]
      rw [← pow_succ', ← pow_add]
      congr 1
      omega
    rw [he] at hp
    exact hp.trans (Nat.pow_le_pow_right (by decide) (by dsimp [coefficientBits,E]; omega))
  have hε:Height (1 / (D:ℚ)) D:=by
    simpa only [one_div] using height_inv (D:ℚ) D (height_nat D D le_rfl hD)
  have hεB:Height (1 / (D:ℚ)) (2 ^ coefficientBits S):=
    height_mono _ hε (hDb.trans (Nat.pow_le_pow_right (by decide)
      (by dsimp [coefficientBits,E]; omega)))
  constructor
  · intro i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [normalizedMatrix,Int.natAbs_mul] using (Nat.mul_le_mul_left R (hA i j)).trans hmulB
    · intro k
      simp only [normalizedMatrix,Fin.addCases_right]
      split_ifs
      · simpa only [Int.natAbs_neg,Int.natAbs_natCast] using hRBound
      · simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      have hbi:Height (P.b i:ℚ) H:=by simpa [Height] using And.intro (hb i) hH
      simpa only [normalizedBound,Fin.addCases_left] using
        height_mono _ (height_add (P.b i:ℚ) (1 / (D:ℚ)) H D hbi hε) hadd
    · intro i
      simpa only [normalizedBound,Fin.addCases_right] using hεB

end Lax109476Proofs.RamNormalizedBounds

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

open scoped BigOperators

namespace Lax109476Proofs.RamSolverInitialization

open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamStoredProgram RationalArithmeticBounds EncodingSize IntegerEncoding

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

namespace Lax109476Proofs.RamIntegerFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open NormalizedFeasibility IntegerCertificates EllipsoidSequence EllipsoidSearch RamNormalizedBounds

def instructionBound (m n S:ℕ):ℕ:=RamFeasibilitySetup.instructionBound S +
  RamSearchBounds.instructionBound (m + n) n
    (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)

theorem search_width_bound (m n S w:ℕ) (hdim:m + n≤ S) (hw:wordWidth S≤ w):
    RamSearchBounds.wordWidth (m + n) n
      (thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1) (coefficientBits S)≤ w:=by
  let N:=thresholdSteps n (ballExponent m n (2 ^ (2 * S))) + 1
  have hN:N≤ iterationBound S:=by
    have h:=IterationBudget.thresholdSteps_polynomial m n S hdim
    dsimp [N,iterationBound]
    omega
  have hn:n≤ S:=by omega
  have hstate:RamTrajectoryBounds.stateBits n N (coefficientBits S)≤
      RamTrajectoryBounds.stateBits S (iterationBound S) (coefficientBits S):=by
    unfold RamTrajectoryBounds.stateBits
    omega
  have hc:=RamEllipsoidBitBounds.wordWidth_monotone hn hstate hN
  have hprod:=Nat.mul_le_mul hdim hn
  unfold wordWidth RamSearchBounds.wordWidth at hw
  unfold RamSearchBounds.wordWidth
  dsimp only [N] at hc hN
  omega

theorem search_cost_monotone {m n N l m' n' N' l':ℕ}
    (hm:m≤ m') (hn:n≤ n') (hN:N≤ N') (hl:l≤ l'):
    RamSearchBounds.instructionBound m n N l≤ RamSearchBounds.instructionBound m' n' N' l':=by
  unfold RamSearchBounds.instructionBound RamSearchBounds.stepBound RamSearchBounds.rowBound
    RamTrajectoryBounds.instructionBound RamTrajectoryBounds.stateBits
    RamEllipsoidBitBounds.magnitudeExponent RamEllipsoidBitBounds.formExponent
  dsimp only
  gcongr

theorem instructionBound_le (m n S:ℕ) (hdim:m + n≤ S):
    instructionBound m n S≤ uniformInstructionBound S:=by
  have hN:=IterationBudget.thresholdSteps_polynomial m n S hdim
  apply Nat.add_le_add_left
  exact search_cost_monotone hdim (by omega) (by unfold iterationBound; omega) le_rfl

theorem decideFeasible_spec (m n S w:ℕ) (P:Program ℤ m n) (hn:2≤ n)
    (hdim:m + n≤ S) (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S)) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found"=1)=IntegerFeasibilityDecision.feasible P (2 ^ (2 * S)))
      (instructionBound m n S):=by
  have hwSetup:RamFeasibilitySetup.wordWidth S≤ w:=by unfold wordWidth at hw; omega
  have hwSearch:=search_width_bound m n S w hdim hw
  have hbounds:=normalized_bounds m n S P hdim hA hb
  let H:=2 ^ (2 * S)
  let A:=normalizedMatrix P (outerScale n (coordinateCap m n H))
  let b:=normalizedBound P (1 / (precisionDenominator m n H:ℚ))
  let K:=thresholdSteps n (ballExponent m n H)
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=RamFeasibilitySetup.setup_spec m n S w P hdim hA hb hwSetup σ hσ
  obtain ⟨υ,hr₂,hυ,hfind⟩:=RamSearchBounds.search_bounded_spec A b hn (K + 1) (coefficientBits S) w
    hbounds.1 hbounds.2 hwSearch τ hτ
  have he:findIteration A b K=if υ.vars "search.found"=1 then some (υ.vars "iter.k") else none:=by
    change scanStates A b 0 (K + 1) (trajectory A b 0)=_
    rw [scanStates_eq_findFirst]
    exact hfind
  refine ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound,K,H]; omega), ?_⟩
  have hi:=congrArg Option.isSome he
  change decide (υ.vars "search.found"=1)=(findIteration A b K).isSome
  rw [hi]
  split_ifs <;> simp_all

theorem decideFeasible_uniform_spec (m n S w:ℕ) (P:Program ℤ m n) (hn:2≤ n)
    (hdim:m + n≤ S) (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S)) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (RamFeasibilitySetup.Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found"=1)=IntegerFeasibilityDecision.feasible P (2 ^ (2 * S)))
      (uniformInstructionBound S):=
  (decideFeasible_spec m n S w P hn hdim hA hb hw).mono (instructionBound_le m n S hdim)

end Lax109476Proofs.RamIntegerFeasibility

end

section

namespace Lax109476Proofs.RamPadMatrix

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RamMatrixStorage RamPadEntries RationalArithmeticBounds
open RamCenterUpdate RamEllipsoidStep

def fields:List String:= ["pad.k", "pad.count", "source.m", "source.n"]

set_option maxHeartbeats 0 in
theorem padCoordinate_spec (B M m n:ℕ) (P:Program ℚ m n)
    (k:Fin ((m + 2) * (n + 2))) (ys:List ℚ) (hy:k.val < ys.length)
    (hM:1≤ M) (hMB:M < B) (hB:(m + 2) * (n + 2) + m + n + 4 < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ∧ Represents "pad.A" ys σ∧
        σ.vars "pad.k"=k.val∧ σ.vars "source.m"=m∧ σ.vars "source.n"=n)
      padCoordinate
      (fun _ τ => Represents "pad.A" (ys.set k.val (values P k)) τ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ∧ τ.vars "pad.k"=k.val∧
        τ.vars "source.m"=m∧ τ.vars "source.n"=n) 70:=by
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have h1:1 < B:=by omega
  have h2:2 < B:=by omega
  have hmB:m + 2 < B:=by omega
  have hnB:n + 2 < B:=by omega
  have hmn:m * n≤ (m + 2) * (n + 2):=Nat.mul_le_mul (by omega) (by omega)
  have hmnB:m * n < B:=by omega
  have hdivB:k.val / (n + 2) < B:=(Nat.div_le_self _ _).trans_lt hkB
  have hmulB:(k.val / (n + 2)) * (n + 2) < B:=(Nat.div_mul_le_self _ _).trans_lt hkB
  have hmodB:k.val - (k.val / (n + 2)) * (n + 2) < B:=(Nat.sub_le _ _).trans_lt hkB
  have hmod:k.val - (k.val / (n + 2)) * (n + 2)=k.val % (n + 2):=by
    simpa [Nat.mul_comm] using (show k.val % (n + 2)=k.val - (n + 2) * (k.val / (n + 2))
      from Nat.mod_eq_sub_mul_div).symm
  have hq:=entry_height P M hM hA k.divNat k.modNat
  have hselect:=spec_with_fields fields
    (RamPadSelector.selectEntry_spec B M m n P k.divNat k.modNat h1 hM hMB hmB hnB hmnB hA)
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide) (by rfl)
  have hstore:=spec_with_write_frame fields
    (storeReduced_spec B "pad.A" ys (values P k) k.val hy h1 hkB
      (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp [fields] at hx; rcases hx with rfl | rfl | rfl | rfl <;> decide)
  rintro σ ⟨hσA,hσy,hσk,hσm,hσn⟩
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "source.n") ((2:Nat)); let c2:Nat:= @HDiv.hDiv Nat Nat Nat (@instHDiv Nat Nat.instDiv) (Env.vars σ "pad.k") c1; let c3:Env:=Env.setVar σ "pad.row" c2; let c4:String→ Nat:=Env.vars c3; let c5:Nat:=c4 "pad.k"; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c4 "pad.row"; let c8:Nat:=c4 "source.n"; let c9:Nat:=c0 c8 ((2:Nat)); let c10:Nat:=c6 c7 c9; let c11:Nat:= @HSub.hSub Nat Nat Nat (@instHSub Nat instSubNat) c5 c10; let c12:Env:=Env.setVar c3 "pad.col" c11; let c13:Env→ Nat→ Prop:=Run B RamPadSelector.selectEntry c12; let c14:Nat:=c0 m ((2:Nat)); let c15:Nat:=c0 n ((2:Nat)); let c16:Fin c14:= @Fin.divNat c14 c15 k; let c17:Fin c15:= @Fin.modNat c14 c15 k; let c18:Env→ Prop:=FractionOutput (@entry m n P c16 c17); let c19:Env→ Prop:=FieldsAgree fields c12; let c20:String→ List Nat:=Env.arrs c12; let c21:Env→ Prop:=fun (σ':Env) => And (c13 σ' ((40:Nat))) (And (c18 σ') (And (c19 σ') (@Eq (String→ List Nat) (Env.arrs σ') c20))); let c22:Nat:= @Fin.val (c6 c14 c15) k; let c23:Env→ Prop:=Represents "pad.A" (@List.set Rat ys c22 (@values m n P k)); let c24:Env→ Prop:=Represents "query.A" (@flatten m n (@Program.A Rat m n P)); let c25:Env→ Prop:=(fun (x τ:Env) => And (c23 τ) (And (c24 τ) (And (@Eq Nat (Env.vars τ "pad.k") c22) (And (@Eq Nat (Env.vars τ "source.m") m) (@Eq Nat (Env.vars τ "source.n") n))))) σ; let c26:Env→ Prop:=fun (σ':Env) => And (Run B padCoordinate σ σ' ((70:Nat))) (c25 σ'); let c27:Prop:= @Exists Env c26; let c28:Nat:= @Fin.val c14 c16; let c29:Nat:= @Fin.val c15 c17; let c30:String→ Nat:=Env.vars c12; let c31:Nat→ Nat:=c0 ((1:Nat)); let c32:Expr:=Expr.add (Expr.var "source.n") (Expr.lit ((2:Nat))); let c33:Expr:=Expr.div (Expr.var "pad.k") c32; let c34:Nat:=c31 (Expr.size c33); let c35:Expr:=Expr.mul (Expr.var "pad.row") c32; let c36:Expr:=Expr.sub (Expr.var "pad.k") c35; let c37:Nat:=c31 (Expr.size c36); let c38:Nat:=c31 (Expr.size (Expr.var "pad.k")); let c39:Nat:=c0 c38 ((13:Nat)); let c40:Nat:=c0 ((40:Nat)) c39; let c41:Nat:=c0 c37 c40; let c42:Com:=Com.assign "pad.col" c36; let c43:Com:=Com.seq (Com.assign "vec.i" (Expr.var "pad.k")) (storeReduced "pad.A"); let c44:Com:=Com.seq RamPadSelector.selectEntry c43; @Exists.casesOn Env c21 (fun (x:@Exists Env c21) => c27) (RunStep.use B (fun (σ_1:Env) => And (c24 σ_1) (And (@Eq Nat (Env.vars σ_1 "source.m") m) (And (@Eq Nat (Env.vars σ_1 "source.n") n) (And (@Eq Nat (Env.vars σ_1 "pad.row") c28) (@Eq Nat (Env.vars σ_1 "pad.col") c29))))) RamPadSelector.selectEntry (fun (σ_1 τ:Env) => And (c18 τ) (And (FieldsAgree fields σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((40:Nat)) hselect c12 ?_) fun (w:Env) (h:And (c13 w ((40:Nat))) (And (c18 w) (And (c19 w) (@Eq (String→ List Nat) (Env.arrs w) c20)))) => let c0_1:Prop:=c13 w ((40:Nat)); let c1_1:Prop:=And (c18 w) (And (c19 w) (@Eq (String→ List Nat) (Env.arrs w) c20)); let c2_1:Env→ Nat→ Prop:=Run B (storeReduced "pad.A") (Env.setVar w "vec.i" (Env.vars w "pad.k")); let c3_1:Env→ Prop:=FieldsAgree fields (Env.setVar w "vec.i" (Env.vars w "pad.k")); let c4_1:Env→ Prop:=fun (σ':Env) => And (c2_1 σ' ((13:Nat))) (And (c23 σ') (And (c3_1 σ') (∀ a∉ Com.warrs (storeReduced "pad.A"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c27) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c4_1 (fun (x:@Exists Env c4_1) => c27) (RunStep.use B (fun (σ_1:Env) => And (Represents "pad.A" ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") c22) (FractionOutput (@values m n P k) σ_1))) (storeReduced "pad.A") (fun (σ_1 τ:Env) => And (c23 τ) (And (FieldsAgree fields σ_1 τ) (∀ a∉ Com.warrs (storeReduced "pad.A"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore (Env.setVar w "vec.i" (Env.vars w "pad.k")) ?_) fun (w_1:Env) (h_1:And (c2_1 w_1 ((13:Nat))) (And (c23 w_1) (And (c3_1 w_1) (∀ a∉ Com.warrs (storeReduced "pad.A"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a))))) => let c0_2:Prop:=c2_1 w_1 ((13:Nat)); let c1_2:Prop:=And (c23 w_1) (And (c3_1 w_1) (∀ a∉ Com.warrs (storeReduced "pad.A"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c27) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c26 w_1 (@And.intro (Run B padCoordinate σ w_1 ((70:Nat))) (c25 w_1) (RunStep.mono B padCoordinate σ w_1 (c0 c34 c41) ((70:Nat)) (RunStep.seq B (Com.assign "pad.row" c33) (Com.seq c42 c44) σ c3 w_1 c34 c41 (RunStep.assign B σ "pad.row" c33 c2 (RunStep.eval_div B σ (Expr.var "pad.k") c32 (Env.vars σ "pad.k") c1 (RunStep.eval_var B σ "pad.k" (?nAX_g4834_0_0_0)) (RunStep.eval_add B σ (Expr.var "source.n") (Expr.lit ((2:Nat))) (Env.vars σ "source.n") ((2:Nat)) (RunStep.eval_var B σ "source.n" (?nAX_g4834_0_0_1)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4834_0_0_2)) ?_)) (RunStep.seq B c42 c44 c3 c12 w_1 c37 c40 (RunStep.assign B c3 "pad.col" c36 c11 (RunStep.eval_sub B c3 (Expr.var "pad.k") c35 c5 c10 (RunStep.eval_var B c3 "pad.k" (?nAX_g4834_0_0_3)) (RunStep.eval_mul B c3 (Expr.var "pad.row") c32 c7 c9 (RunStep.eval_var B c3 "pad.row" ?_) (RunStep.eval_add B c3 (Expr.var "source.n") (Expr.lit ((2:Nat))) c8 ((2:Nat)) (RunStep.eval_var B c3 "source.n" (?nAX_g4834_0_0_4)) (RunStep.eval_lit B ((2:Nat)) c3 h2) (?nAX_g4834_0_0_5)) ?_) (?nAX_g4834_0_0_6))) (RunStep.seq B RamPadSelector.selectEntry c43 c12 w w_1 ((40:Nat)) c39 left (RunStep.seq B (Com.assign "vec.i" (Expr.var "pad.k")) (storeReduced "pad.A") w (Env.setVar w "vec.i" (Env.vars w "pad.k")) w_1 c38 ((13:Nat)) (RunStep.assign B w "vec.i" (Expr.var "pad.k") (Env.vars w "pad.k") (RunStep.eval_var B w "pad.k" ?_)) left_1)))) (?nAX_g4834_0_0_7)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4834_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4834_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hselect hstore
  all_goals simp_all [fields,FieldsAgree,Represents,values,Fin.divNat,Fin.modNat,
    storeReduced,Com.warrs]
  all_goals aesop

def Invariant {m n:ℕ} (P:Program ℚ m n) (σ:Env):Prop:=
  Represents "query.A" (RamMatrixStorage.flatten P.A) σ∧
    Represents "pad.A" (filled (values P) (σ.vars "pad.k")) σ∧
    σ.vars "pad.k" ≤ (m + 2) * (n + 2)∧ σ.vars "pad.count"=(m + 2) * (n + 2)∧
    σ.vars "source.m"=m∧ σ.vars "source.n"=n

theorem padStep_spec (B M m n:ℕ) (P:Program ℚ m n)
    (hM:1≤ M) (hMB:M < B) (hB:(m + 2) * (n + 2) + m + n + 4 < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Invariant P σ∧ σ.vars "pad.k" < (m + 2) * (n + 2)) padStep
      (fun σ τ => Invariant P τ∧ τ.vars "pad.k"=σ.vars "pad.k" + 1) 74:=by
  rintro σ ⟨⟨hσA,hσp,hσkN,hσcount,hσm,hσn⟩,hσk⟩
  let k:Fin ((m + 2) * (n + 2)):= ⟨σ.vars "pad.k",hσk⟩
  obtain ⟨τ,hr₁,hτp,hτA,hτk,hτm,hτn⟩:=padCoordinate_spec B M m n P k
    (filled (values P) k.val) (by simpa only [filled,List.length_ofFn] using k.isLt) hM hMB hB hA σ ⟨hσA,hσp,rfl,hσm,hσn⟩
  have hτcount:=(hr₁.frame_var "pad.count" (by decide)).trans hσcount
  have h1:1 < B:=by omega
  have hkB:k.val < B:=k.isLt.trans (by omega)
  have hi1B:k.val + 1 < B:=lt_of_le_of_lt k.isLt (by omega)
  have hr₂:Run B (.assign "pad.k" (.add (.var "pad.k") (.lit 1))) τ
      (τ.setVar "pad.k" (k.val + 1)) 4:=by
    exact Run.assign (by simpa only [hτk,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=τ) (x:= "pad.k") (hτk ▸ hkB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "pad.k") 1 < B by simpa [hτk] using hi1B)))
  have hfilled:Represents "pad.A" (filled (values P) (k.val + 1)) τ:=by
    rw [← filled_step]
    exact hτp
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτA
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change k.val + 1≤ (m + 2) * (n + 2)
    exact k.isLt
  · simpa using hτcount
  · simpa using hτm
  · simpa using hτn
  · simp [k]

theorem padLoop_spec (B M m n:ℕ) (P:Program ℚ m n)
    (hM:1≤ M) (hMB:M < B) (hB:(m + 2) * (n + 2) + m + n + 4 < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ∧
        Represents "pad.A" (List.replicate ((m + 2) * (n + 2)) 0) σ∧
        σ.vars "pad.count"=(m + 2) * (n + 2)∧ σ.vars "source.m"=m∧ σ.vars "source.n"=n)
      padLoop
      (fun _ τ => Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ∧ τ.vars "source.m"=m∧ τ.vars "source.n"=n)
      (78 * ((m + 2) * (n + 2)) + 6):=by
  have hlo:=Spec.forRangeZero "pad.k" "pad.count" (Invariant P) ((m + 2) * (n + 2)) 74
    (by omega) (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (padStep_spec B M m n P hM hMB hB hA)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hA,hp,hcount,hm,hn⟩
    simp_all [Invariant,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hk⟩
    refine ⟨?_,hτ.1,hτ.2.2.2.2.1,hτ.2.2.2.2.2⟩
    simpa only [hk,filled_done,values_eq] using hτ.2.1

set_option maxHeartbeats 0 in
theorem padMatrix_spec (B M m n:ℕ) (P:Program ℚ m n)
    (hM:1≤ M) (hMB:M < B) (hB:(m + 2) * (n + 2) + m + n + 4 < B)
    (hA:∀ i j,Height (P.A i j) M):
    Spec B (fun σ => Represents "query.A" (RamMatrixStorage.flatten P.A) σ∧
        Extents "pad.A" ((m + 2) * (n + 2)) σ∧ σ.vars "source.m"=m∧ σ.vars "source.n"=n)
      padMatrix
      (fun _ τ => Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ∧
        Represents "query.A" (RamMatrixStorage.flatten P.A) τ∧
        τ.vars "source.m"=m∧ τ.vars "source.n"=n)
      (111 * ((m + 2) * (n + 2)) + 36):=by
  have h1:1 < B:=by omega
  have h2:2 < B:=by omega
  have hmB:m + 2 < B:=by omega
  have hnB:n + 2 < B:=by omega
  have hcountB:(m + 2) * (n + 2) < B:=by omega
  have hzero:=spec_with_write_frame ["source.m", "source.n", "pad.count"]
    (RamZeroArray.zeroRationalArray_spec B ((m + 2) * (n + 2)) "pad.A" hcountB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hlo:=padLoop_spec B M m n P hM hMB hB hA
  rintro σ ⟨hσA,hσpad,hσm,hσn⟩
  have hs:=hσpad ".s" (by simp)
  have hn:=hσpad ".n" (by simp)
  have hd:=hσpad ".d" (by simp)
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.mul; let c1:Nat→ Nat→ Nat:=Nat.add; let c2:Nat:=c1 (Env.vars σ "source.m") ((2:Nat)); let c3:Nat:=c1 (Env.vars σ "source.n") ((2:Nat)); let c4:Nat:=c0 c2 c3; let c5:Env:=Env.setVar σ "pad.count" c4; let c6:Nat:=Env.vars c5 "pad.count"; let c7:Env:=Env.setVar c5 "vec.n" c6; let c8:Env→ Nat→ Prop:=Run B (RamZeroArray.zeroRationalArray "pad.A") c7; let c9:Nat:=c1 m ((2:Nat)); let c10:Nat:=c1 n ((2:Nat)); let c11:Nat:=c0 c9 c10; let c12:Nat:=c1 (c0 ((33:Nat)) c11) ((18:Nat)); let c13:Env→ Prop:=Represents "pad.A" (@List.replicate Rat c11 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c14:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "pad.A"; let c15:String:=c14 ".s"; let c16:String:=c14 ".n"; let c17:String:=c14 ".d"; let c18:String→ List Nat:=Env.arrs c7; let c19:Env→ Env→ Prop:=FieldsAgree (@List.cons String "source.m" (@List.cons String "source.n" (@List.cons String "pad.count" (@List.nil String)))); let c20:Env→ Prop:=c19 c7; let c21:Env→ Prop:=fun (σ':Env) => And (c8 σ' c12) (And (And (c13 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c11) (∀ b∉ @List.cons String c15 (@List.cons String c16 (@List.cons String c17 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c18 b)))) (And (c20 σ') (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.A"), @Eq (List Nat) (Env.arrs σ' a) (c18 a)))); let c22:Nat:=c1 (c0 ((111:Nat)) c11) ((36:Nat)); let c23:Env→ Prop:=Represents "pad.A" (@flatten c9 c10 (@Program.A Rat c9 c10 (@FeasibilityPadding.pad Rat (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)) (@AddMonoidWithOne.toOne Rat (@AddGroupWithOne.toAddMonoidWithOne Rat (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))) m n P))); let c24:Env→ Prop:=Represents "query.A" (@flatten m n (@Program.A Rat m n P)); let c25:Env→ Env→ Prop:=fun (x τ:Env) => And (c23 τ) (And (c24 τ) (And (@Eq Nat (Env.vars τ "source.m") m) (@Eq Nat (Env.vars τ "source.n") n))); let c26:Env→ Prop:=c25 σ; let c27:Env→ Prop:=fun (σ':Env) => And (Run B padMatrix σ σ' c22) (c26 σ'); let c28:Nat:=c1 (c0 ((78:Nat)) c11) ((6:Nat)); let c29:Nat→ Nat:=c1 ((1:Nat)); let c30:Expr:=Expr.add (Expr.var "source.m") (Expr.lit ((2:Nat))); let c31:Expr:=Expr.add (Expr.var "source.n") (Expr.lit ((2:Nat))); let c32:Expr:=Expr.mul c30 c31; let c33:Nat:=c29 (Expr.size c32); let c34:Nat:=c29 (Expr.size (Expr.var "pad.count")); let c35:Nat:=c1 c12 c28; let c36:Nat:=c1 c34 c35; @Exists.casesOn Env c21 (fun (x:@Exists Env c21) => @Exists Env c27) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c15)) c11) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c16)) c11) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c17)) c11) (@Eq Nat (Env.vars σ_1 "vec.n") c11)))) (RamZeroArray.zeroRationalArray "pad.A") (fun (σ_1 τ:Env) => And (And (c13 τ) (And (@Eq Nat (Env.vars τ "vec.n") c11) (∀ b∉ @List.cons String c15 (@List.cons String c16 (@List.cons String c17 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (c19 σ_1 τ) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.A"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c12 hzero c7 ?_) fun (w:Env) (h:And (c8 w c12) (And (And (c13 w) (And (@Eq Nat (Env.vars w "vec.n") c11) (∀ b∉ @List.cons String c15 (@List.cons String c16 (@List.cons String c17 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c18 b)))) (And (c20 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.A"), @Eq (List Nat) (Env.arrs w a) (c18 a))))) => let c0_1:Prop:=And (And (c13 w) (And (@Eq Nat (Env.vars w "vec.n") c11) (∀ b∉ @List.cons String c15 (@List.cons String c16 (@List.cons String c17 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c18 b)))) (And (c20 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.A"), @Eq (List Nat) (Env.arrs w a) (c18 a))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B padLoop w σ' c28) (And (c23 σ') (And (c24 σ') (And (@Eq Nat (Env.vars σ' "source.m") m) (@Eq Nat (Env.vars σ' "source.n") n)))); @And.casesOn (c8 w c12) c0_1 (fun (x:And (c8 w c12) c0_1) => @Exists Env c27) h fun (left:c8 w c12) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c27) (RunStep.use B (fun (σ_1:Env) => And (c24 σ_1) (And (c13 σ_1) (And (@Eq Nat (Env.vars σ_1 "pad.count") c11) (And (@Eq Nat (Env.vars σ_1 "source.m") m) (@Eq Nat (Env.vars σ_1 "source.n") n))))) padLoop c25 c28 hlo w ?_) fun (w_1:Env) (h_1:And (Run B padLoop w w_1 c28) (And (c23 w_1) (And (c24 w_1) (And (@Eq Nat (Env.vars w_1 "source.m") m) (@Eq Nat (Env.vars w_1 "source.n") n))))) => let c0_2:Prop:=And (c23 w_1) (And (c24 w_1) (And (@Eq Nat (Env.vars w_1 "source.m") m) (@Eq Nat (Env.vars w_1 "source.n") n))); @And.casesOn (Run B padLoop w w_1 c28) c0_2 (fun (x:And (Run B padLoop w w_1 c28) c0_2) => @Exists Env c27) h_1 fun (left_1:Run B padLoop w w_1 c28) (right_1:c0_2) => @Exists.intro Env c27 w_1 (@And.intro (Run B padMatrix σ w_1 c22) (c26 w_1) (RunStep.mono B padMatrix σ w_1 (c1 c33 c36) c22 (RunStep.seq B (Com.assign "pad.count" c32) (Com.seq (Com.assign "vec.n" (Expr.var "pad.count")) (Com.seq (RamZeroArray.zeroRationalArray "pad.A") padLoop)) σ c5 w_1 c33 c36 (RunStep.assign B σ "pad.count" c32 c4 (RunStep.eval_mul B σ c30 c31 c2 c3 (RunStep.eval_add B σ (Expr.var "source.m") (Expr.lit ((2:Nat))) (Env.vars σ "source.m") ((2:Nat)) (RunStep.eval_var B σ "source.m" (?nAX_g4841_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4841_0_0_1)) (RunStep.eval_add B σ (Expr.var "source.n") (Expr.lit ((2:Nat))) (Env.vars σ "source.n") ((2:Nat)) (RunStep.eval_var B σ "source.n" (?nAX_g4841_0_0_2)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4841_0_0_3)) ?_)) (RunStep.seq B (Com.assign "vec.n" (Expr.var "pad.count")) (Com.seq (RamZeroArray.zeroRationalArray "pad.A") padLoop) c5 c7 w_1 c34 c35 (RunStep.assign B c5 "vec.n" (Expr.var "pad.count") c6 (RunStep.eval_var B c5 "pad.count" ?_)) (RunStep.seq B (RamZeroArray.zeroRationalArray "pad.A") padLoop c7 w w_1 c12 c28 left left_1))) (?nAX_g4841_0_0_4)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4841_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4841_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4841_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4841_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4841_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree,Represents,Extents]
  all_goals aesop

end Lax109476Proofs.RamPadMatrix

end

section

namespace Lax109476Proofs.RamPadBound

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRational RamRationalArrays RamFrame RationalArithmeticBounds RamCenterUpdate RamEllipsoidStep

def value {m n:ℕ} (P:Program ℚ m n) (i:Fin (m + 2)):ℚ:=
  if hi:i.val < m then P.b ⟨i.val,hi⟩ else 0

theorem value_eq {m n:ℕ} (P:Program ℚ m n) (i:Fin (m + 2)):
    value P i=(FeasibilityPadding.pad P).b i:=by
  refine Fin.addCases ?_ ?_ i
  · intro i
    simp [value,FeasibilityPadding.pad,i.isLt]
  · intro i
    simp [value,FeasibilityPadding.pad]

theorem value_height {m n:ℕ} (P:Program ℚ m n) (M:ℕ) (hM:1≤ M)
    (hb:∀ i,Height (P.b i) M) (i:Fin (m + 2)):Height (value P i) M:=by
  unfold value
  split_ifs
  · exact hb _
  · simpa [Height] using hM

set_option maxHeartbeats 0 in
theorem selectBound_spec (B M m n:ℕ) (P:Program ℚ m n) (i:Fin (m + 2))
    (hM:1≤ M) (hMB:M < B) (hmB:m + 2 < B) (hb:∀ i,Height (P.b i) M):
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ∧
        σ.vars "source.m"=m∧ σ.vars "pad.k"=i.val)
      selectBound (fun _ τ => FractionOutput (value P i) τ) 21:=by
  have h1:1 < B:=hM.trans_lt hMB
  have hiB:i.val < B:=i.isLt.trans hmB
  have hm:m < B:=by omega
  have hzero:=RamPadSelector.constantFraction_spec B 0 h1 (by omega)
  rintro σ ⟨hσb,hσm,hσi⟩
  by_cases hi:i.val < m
  · let ii:Fin m:= ⟨i.val,hi⟩
    have hq:=hb ii
    have hload:=loadLeft_spec B "query.b" (List.ofFn P.b) i.val (by simpa using hi)
      h1 hiB (by simpa [ii] using hq.1.trans_lt hMB) (by simpa [ii] using hq.2.trans_lt hMB)
    have hresult:=RamCopy.leftToResult_spec B (P.b ii) h1 (hq.1.trans_lt hMB) (hq.2.trans_lt hMB)
    (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.k") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@value m n P i) τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((21:Nat))) (c2 σ'); let c4:Env→ Nat→ Prop:=Run B (loadLeft "query.b") (Env.setVar σ "vec.i" (Env.vars σ "pad.k")); let c5:List Rat:= @List.ofFn Rat m (@Program.b Rat m n P); let c6:Nat→ Nat→ Nat:=Nat.add; let c7:Nat:= @Fin.val (c6 m ((2:Nat))) i; let c8:Env→ Prop:=LeftOutput (@getElem (List Rat) Nat Rat (fun (as:List Rat) (i_1:Nat) => Nat.lt i_1 (@List.length Rat as)) (@List.instGetElemNatLtLength Rat) c5 c7 (?nAX_g4846_0_0_0)); let c9:Env→ Prop:=fun (σ':Env) => And (c4 σ' ((9:Nat))) (c8 σ'); let c10:Env→ Prop:=Represents "query.b" c5; let c11:Env→ Prop:=FractionOutput (@Program.b Rat m n P ii); let c12:Env→ Prop:=LeftOutput (@Program.b Rat m n P ii); let c13:Nat→ Nat:=c6 ((1:Nat)); let c14:Nat→ Nat:=c6 (c13 (Cond.size (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")))); let c15:Nat:=c13 (Expr.size (Expr.var "pad.k")); let c16:Nat:=c6 ((9:Nat)) ((6:Nat)); let c17:Nat:=c6 c15 c16; let c18:Com:=Com.seq (Com.assign "vec.i" (Expr.var "pad.k")) (Com.seq (loadLeft "query.b") RamCopy.leftToResult); let c19:Env:=Env.setVar σ "rat.s" ((0:Nat)); let c20:Env:=Env.setVar c19 "rat.n" ((0:Nat)); let c21:Env:=Env.setVar c20 "rat.d" ((1:Nat)); let c22:Nat:=c13 (Expr.size (Expr.lit ((0:Nat)))); let c23:Nat→ Nat:=c6 c22; let c24:Nat:=c13 (Expr.size (Expr.lit ((1:Nat)))); let c25:Nat:=c23 c24; let c26:Nat:=c23 c25; let c27:Com:=Com.assign "rat.n" (Expr.lit ((0:Nat))); let c28:Com:=Com.assign "rat.d" (Expr.lit ((1:Nat))); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => @Exists Env c3) (Classical.em c0) (fun (hcase:c0) => @Exists.casesOn Env c9 (fun (x:@Exists Env c9) => @Exists Env c3) (RunStep.use B (fun (σ_1:Env) => And (c10 σ_1) (@Eq Nat (Env.vars σ_1 "vec.i") c7)) (loadLeft "query.b") (fun (x τ:Env) => c8 τ) ((9:Nat)) hload (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) ?_) fun (w:Env) (h:And (c4 w ((9:Nat))) (c8 w)) => let c0_1:Prop:=c4 w ((9:Nat)); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B RamCopy.leftToResult w σ' ((6:Nat))) (c11 σ'); @And.casesOn c0_1 (c8 w) (fun (x:And c0_1 (c8 w)) => @Exists Env c3) h fun (left:c0_1) (right:c8 w) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c3) (RunStep.use B c12 RamCopy.leftToResult (fun (x τ:Env) => c11 τ) ((6:Nat)) hresult w ?_) fun (w_1:Env) (h_1:And (Run B RamCopy.leftToResult w w_1 ((6:Nat))) (c11 w_1)) => let c0_2:Prop:=Run B RamCopy.leftToResult w w_1 ((6:Nat)); @And.casesOn c0_2 (c11 w_1) (fun (x:And c0_2 (c11 w_1)) => @Exists Env c3) h_1 fun (left_1:c0_2) (right_1:c11 w_1) => @Exists.intro Env c3 w_1 (@And.intro (Run B selectBound σ w_1 ((21:Nat))) (c2 w_1) (RunStep.mono B selectBound σ w_1 (c14 c17) ((21:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")) c18 (RamPadSelector.constantFraction ((0:Nat))) σ w_1 c17 (RunStep.cond_lt_true B σ (Expr.var "pad.k") (Expr.var "source.m") (Env.vars σ "pad.k") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_0_0_1)) (RunStep.eval_var B σ "source.m" (?nAX_g4846_0_0_2)) hcase) (RunStep.seq B (Com.assign "vec.i" (Expr.var "pad.k")) (Com.seq (loadLeft "query.b") RamCopy.leftToResult) σ (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) w_1 c15 c16 (RunStep.assign B σ "vec.i" (Expr.var "pad.k") (Env.vars σ "pad.k") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_0_0_3))) (RunStep.seq B (loadLeft "query.b") RamCopy.leftToResult (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) w w_1 ((9:Nat)) ((6:Nat)) left left_1))) (?nAX_g4846_0_0_4)) ?_)) fun (hcase:c1) => @Exists.intro Env c3 c21 (@And.intro (Run B selectBound σ c21 ((21:Nat))) (c2 c21) (RunStep.mono B selectBound σ c21 (c14 c26) ((21:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")) c18 (RamPadSelector.constantFraction ((0:Nat))) σ c21 c26 (RunStep.cond_lt_false B σ (Expr.var "pad.k") (Expr.var "source.m") (Env.vars σ "pad.k") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_0_0_5)) (RunStep.eval_var B σ "source.m" (?nAX_g4846_0_0_6)) hcase) (RunStep.seq B (Com.assign "rat.s" (Expr.lit ((0:Nat)))) (Com.seq c27 c28) σ c19 c21 c22 c25 (RunStep.assign B σ "rat.s" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) σ (?nAX_g4846_0_0_7))) (RunStep.seq B c27 c28 c19 c20 c21 c22 c24 (RunStep.assign B c19 "rat.n" (Expr.lit ((0:Nat))) ((0:Nat)) (RunStep.eval_lit B ((0:Nat)) c19 (?nAX_g4846_0_0_8))) (RunStep.assign B c20 "rat.d" (Expr.lit ((1:Nat))) ((1:Nat)) (RunStep.eval_lit B ((1:Nat)) c20 h1))))) (?nAX_g4846_0_0_9)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4846_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_0_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
    all_goals clear hload hresult
    all_goals simp_all [Represents,value,ii]
  · (expose_names;
      (refine let c0:Prop:=Nat.lt (Env.vars σ "pad.k") (Env.vars σ "source.m"); let c1:Prop:=Not c0; let c2:Env→ Prop:=(fun (x τ:Env) => FractionOutput (@value m n P i) τ) σ; let c3:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((21:Nat))) (c2 σ'); let c4:Prop:= @Exists Env c3; let c5:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "query.b"; let c6:String:=c5 ".s"; let c7:Nat:=Env.vars (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) "vec.i"; let c8:Nat:= @List.getD Nat (Env.arrs (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) c6) c7 ((0:Nat)); let c9:Env:=Env.setVar (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) "left.s" c8; let c10:String:=c5 ".n"; let c11:Nat:=Env.vars c9 "vec.i"; let c12:Nat:= @List.getD Nat (Env.arrs c9 c10) c11 ((0:Nat)); let c13:Env:=Env.setVar c9 "left.n" c12; let c14:String:=c5 ".d"; let c15:Nat:=Env.vars c13 "vec.i"; let c16:Nat:= @List.getD Nat (Env.arrs c13 c14) c15 ((0:Nat)); let c17:Env:=Env.setVar c13 "left.d" c16; let c18:Nat:=Env.vars c17 "left.s"; let c19:Env:=Env.setVar c17 "rat.s" c18; let c20:Nat:=Env.vars c19 "left.n"; let c21:Env:=Env.setVar c19 "rat.n" c20; let c22:Nat:=Env.vars c21 "left.d"; let c23:Env:=Env.setVar c21 "rat.d" c22; let c24:Nat→ Nat→ Nat:=Nat.add; let c25:Nat→ Nat:=c24 ((1:Nat)); let c26:Nat→ Nat:=c24 (c25 (Cond.size (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")))); let c27:Nat:=c25 (Expr.size (Expr.var "pad.k")); let c28:Expr:=Expr.get c6 (Expr.var "vec.i"); let c29:Nat:=c25 (Expr.size c28); let c30:Expr:=Expr.get c10 (Expr.var "vec.i"); let c31:Nat:=c25 (Expr.size c30); let c32:Expr:=Expr.get c14 (Expr.var "vec.i"); let c33:Nat:=c25 (Expr.size c32); let c34:Nat:=c24 c31 c33; let c35:Nat:=c24 c29 c34; let c36:Nat:=c25 (Expr.size (Expr.var "left.s")); let c37:Nat:=c25 (Expr.size (Expr.var "left.n")); let c38:Nat:=c25 (Expr.size (Expr.var "left.d")); let c39:Nat:=c24 c37 c38; let c40:Nat:=c24 c36 c39; let c41:Nat:=c24 c35 c40; let c42:Nat:=c24 c27 c41; let c43:Com:=Com.seq (Com.assign "vec.i" (Expr.var "pad.k")) (Com.seq (loadLeft "query.b") RamCopy.leftToResult); let c44:Com:=Com.assign "left.n" c30; let c45:Com:=Com.assign "left.d" c32; let c46:Env→ Nat→ Prop:=Run B (RamPadSelector.constantFraction ((0:Nat))) σ; let c47:Env→ Prop:=FractionOutput (@Nat.cast Rat Rat.instNatCast ((0:Nat))); let c48:Env→ Prop:=fun (σ':Env) => And (c46 σ' ((6:Nat))) (c47 σ'); @Or.casesOn c0 c1 (fun (x:Or c0 c1) => c4) (Classical.em c0) (fun (hcase:c0) => @Exists.intro Env c3 c23 (@And.intro (Run B selectBound σ c23 ((21:Nat))) (c2 c23) (RunStep.mono B selectBound σ c23 (c26 c42) ((21:Nat)) (RunStep.ite_true B (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")) c43 (RamPadSelector.constantFraction ((0:Nat))) σ c23 c42 (RunStep.cond_lt_true B σ (Expr.var "pad.k") (Expr.var "source.m") (Env.vars σ "pad.k") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_1_0_0)) (RunStep.eval_var B σ "source.m" (?nAX_g4846_1_0_1)) hcase) (RunStep.seq B (Com.assign "vec.i" (Expr.var "pad.k")) (Com.seq (loadLeft "query.b") RamCopy.leftToResult) σ (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) c23 c27 c41 (RunStep.assign B σ "vec.i" (Expr.var "pad.k") (Env.vars σ "pad.k") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_1_0_2))) (RunStep.seq B (loadLeft "query.b") RamCopy.leftToResult (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) c17 c23 c35 c40 (RunStep.seq B (Com.assign "left.s" c28) (Com.seq c44 c45) (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) c9 c17 c29 c34 (RunStep.assign B (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) "left.s" c28 c8 (RunStep.eval_get B (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) c6 (Expr.var "vec.i") c7 (RunStep.eval_var B (Env.setVar σ "vec.i" (Env.vars σ "pad.k")) "vec.i" (?nAX_g4846_1_0_3)) (?nAX_g4846_1_0_4) (?nAX_g4846_1_0_5))) (RunStep.seq B c44 c45 c9 c13 c17 c31 c33 (RunStep.assign B c9 "left.n" c30 c12 (RunStep.eval_get B c9 c10 (Expr.var "vec.i") c11 (RunStep.eval_var B c9 "vec.i" (?nAX_g4846_1_0_6)) (?nAX_g4846_1_0_7) (?nAX_g4846_1_0_8))) (RunStep.assign B c13 "left.d" c32 c16 (RunStep.eval_get B c13 c14 (Expr.var "vec.i") c15 (RunStep.eval_var B c13 "vec.i" (?nAX_g4846_1_0_9)) (?nAX_g4846_1_0_10) (?nAX_g4846_1_0_11))))) (RunStep.seq B (Com.assign "rat.s" (Expr.var "left.s")) (Com.seq (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d"))) c17 c19 c23 c36 c39 (RunStep.assign B c17 "rat.s" (Expr.var "left.s") c18 (RunStep.eval_var B c17 "left.s" (?nAX_g4846_1_0_12))) (RunStep.seq B (Com.assign "rat.n" (Expr.var "left.n")) (Com.assign "rat.d" (Expr.var "left.d")) c19 c21 c23 c37 c38 (RunStep.assign B c19 "rat.n" (Expr.var "left.n") c20 (RunStep.eval_var B c19 "left.n" (?nAX_g4846_1_0_13))) (RunStep.assign B c21 "rat.d" (Expr.var "left.d") c22 (RunStep.eval_var B c21 "left.d" (?nAX_g4846_1_0_14)))))))) (?nAX_g4846_1_0_15)) ?_)) fun (hcase:c1) => @Exists.casesOn Env c48 (fun (x:@Exists Env c48) => c4) (RunStep.use B (fun (x:Env) => True) (RamPadSelector.constantFraction ((0:Nat))) (fun (x τ:Env) => c47 τ) ((6:Nat)) hzero σ ?_) fun (w:Env) (h:And (c46 w ((6:Nat))) (c47 w)) => let c0_1:Prop:=c46 w ((6:Nat)); @And.casesOn c0_1 (c47 w) (fun (x:And c0_1 (c47 w)) => c4) h fun (left:c0_1) (right:c47 w) => @Exists.intro Env c3 w (@And.intro (Run B selectBound σ w ((21:Nat))) (c2 w) (RunStep.mono B selectBound σ w (c26 ((6:Nat))) ((21:Nat)) (RunStep.ite_false B (Cond.lt (Expr.var "pad.k") (Expr.var "source.m")) c43 (RamPadSelector.constantFraction ((0:Nat))) σ w ((6:Nat)) (RunStep.cond_lt_false B σ (Expr.var "pad.k") (Expr.var "source.m") (Env.vars σ "pad.k") (Env.vars σ "source.m") (RunStep.eval_var B σ "pad.k" (?nAX_g4846_1_0_16)) (RunStep.eval_var B σ "source.m" (?nAX_g4846_1_0_17)) hcase) left) (?nAX_g4846_1_0_18)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4846_1_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_4 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_5 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_6 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_7 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_8 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_9 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_10 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_11 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_12 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_13 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_14 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_15 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_16 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_17 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4846_1_0_18 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left))
    all_goals simp_all [Represents,value]
    all_goals (try split_ifs) <;> (try simp_all) <;> omega

set_option maxHeartbeats 0 in
theorem padCoordinate_spec (B M m n:ℕ) (P:Program ℚ m n) (i:Fin (m + 2))
    (ys:List ℚ) (hy:i.val < ys.length) (hM:1≤ M) (hMB:M < B)
    (hmB:m + 2 < B) (hb:∀ i,Height (P.b i) M):
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ∧ Represents "pad.b" ys σ∧
        σ.vars "source.m"=m∧ σ.vars "pad.k"=i.val)
      padCoordinate
      (fun _ τ => Represents "pad.b" (ys.set i.val (value P i)) τ∧
        Represents "query.b" (List.ofFn P.b) τ∧ τ.vars "source.m"=m∧ τ.vars "pad.k"=i.val) 36:=by
  have h1:1 < B:=hM.trans_lt hMB
  have hiB:i.val < B:=i.isLt.trans hmB
  have hq:=value_height P M hM hb i
  have hs:=spec_with_fields ["source.m", "pad.k"]
    (selectBound_spec B M m n P i hM hMB hmB hb)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) (by rfl)
  have hstore:=spec_with_write_frame ["source.m", "pad.k"]
    (storeReduced_spec B "pad.b" ys (value P i) i.val hy h1 hiB
      (hq.1.trans_lt hMB) (hq.2.trans_lt hMB))
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
  rintro σ ⟨hσb,hσy,hσm,hσi⟩
  (expose_names;
    (refine let c0:Env→ Env→ Prop:=FieldsAgree (@List.cons String "source.m" (@List.cons String "pad.k" (@List.nil String))); let c1:Env→ Prop:=c0 σ; let c2:Env→ Prop:=fun (σ':Env) => And (Run B selectBound σ σ' ((21:Nat))) (And (FractionOutput (@value m n P i) σ') (And (c1 σ') (@Eq (String→ List Nat) (Env.arrs σ') (Env.arrs σ)))); let c3:Nat→ Nat→ Nat:=Nat.add; let c4:Nat:= @Fin.val (c3 m ((2:Nat))) i; let c5:Env→ Prop:=Represents "pad.b" (@List.set Rat ys c4 (@value m n P i)); let c6:Env→ Prop:=Represents "query.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c7:Env→ Prop:=(fun (x τ:Env) => And (c5 τ) (And (c6 τ) (And (@Eq Nat (Env.vars τ "source.m") m) (@Eq Nat (Env.vars τ "pad.k") c4)))) σ; let c8:Env→ Prop:=fun (σ':Env) => And (Run B padCoordinate σ σ' ((36:Nat))) (c7 σ'); let c9:Prop:= @Exists Env c8; let c10:Nat:=c3 ((1:Nat)) (Expr.size (Expr.var "pad.k")); let c11:Nat:=c3 c10 ((13:Nat)); @Exists.casesOn Env c2 (fun (x:@Exists Env c2) => c9) (RunStep.use B (fun (σ_1:Env) => And (c6 σ_1) (And (@Eq Nat (Env.vars σ_1 "source.m") m) (@Eq Nat (Env.vars σ_1 "pad.k") c4))) selectBound (fun (σ_1 τ:Env) => And (FractionOutput (@value m n P i) τ) (And (c0 σ_1 τ) (@Eq (String→ List Nat) (Env.arrs τ) (Env.arrs σ_1)))) ((21:Nat)) hs σ ?_) fun (w:Env) (h:And (Run B selectBound σ w ((21:Nat))) (And (FractionOutput (@value m n P i) w) (And (c1 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))))) => let c0_1:Prop:=Run B selectBound σ w ((21:Nat)); let c1_1:Prop:=And (FractionOutput (@value m n P i) w) (And (c1 w) (@Eq (String→ List Nat) (Env.arrs w) (Env.arrs σ))); let c2_1:Env→ Nat→ Prop:=Run B (storeReduced "pad.b") (Env.setVar w "vec.i" (Env.vars w "pad.k")); let c3_1:Env→ Prop:=c0 (Env.setVar w "vec.i" (Env.vars w "pad.k")); let c4_1:Env→ Prop:=fun (σ':Env) => And (c2_1 σ' ((13:Nat))) (And (c5 σ') (And (c3_1 σ') (∀ a∉ Com.warrs (storeReduced "pad.b"), @Eq (List Nat) (Env.arrs σ' a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a)))); @And.casesOn c0_1 c1_1 (fun (x:And c0_1 c1_1) => c9) h fun (left:c0_1) (right:c1_1) => @Exists.casesOn Env c4_1 (fun (x:@Exists Env c4_1) => c9) (RunStep.use B (fun (σ_1:Env) => And (Represents "pad.b" ys σ_1) (And (@Eq Nat (Env.vars σ_1 "vec.i") c4) (FractionOutput (@value m n P i) σ_1))) (storeReduced "pad.b") (fun (σ_1 τ:Env) => And (c5 τ) (And (c0 σ_1 τ) (∀ a∉ Com.warrs (storeReduced "pad.b"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) ((13:Nat)) hstore (Env.setVar w "vec.i" (Env.vars w "pad.k")) ?_) fun (w_1:Env) (h_1:And (c2_1 w_1 ((13:Nat))) (And (c5 w_1) (And (c3_1 w_1) (∀ a∉ Com.warrs (storeReduced "pad.b"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a))))) => let c0_2:Prop:=c2_1 w_1 ((13:Nat)); let c1_2:Prop:=And (c5 w_1) (And (c3_1 w_1) (∀ a∉ Com.warrs (storeReduced "pad.b"), @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs (Env.setVar w "vec.i" (Env.vars w "pad.k")) a))); @And.casesOn c0_2 c1_2 (fun (x:And c0_2 c1_2) => c9) h_1 fun (left_1:c0_2) (right_1:c1_2) => @Exists.intro Env c8 w_1 (@And.intro (Run B padCoordinate σ w_1 ((36:Nat))) (c7 w_1) (RunStep.mono B padCoordinate σ w_1 (c3 ((21:Nat)) c11) ((36:Nat)) (RunStep.seq B selectBound (Com.seq (Com.assign "vec.i" (Expr.var "pad.k")) (storeReduced "pad.b")) σ w w_1 ((21:Nat)) c11 left (RunStep.seq B (Com.assign "vec.i" (Expr.var "pad.k")) (storeReduced "pad.b") w (Env.setVar w "vec.i" (Env.vars w "pad.k")) w_1 c10 ((13:Nat)) (RunStep.assign B w "vec.i" (Expr.var "pad.k") (Env.vars w "pad.k") (RunStep.eval_var B w "pad.k" ?_)) left_1)) (?nAX_g4848_0_0_0)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4848_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hs hstore
  all_goals simp_all [Represents,FieldsAgree,storeReduced,Com.warrs]
  all_goals aesop

def Invariant {m n:ℕ} (P:Program ℚ m n) (σ:Env):Prop:=
  Represents "query.b" (List.ofFn P.b) σ∧
    Represents "pad.b" (filled (value P) (σ.vars "pad.k")) σ∧
    σ.vars "pad.k" ≤ m + 2∧ σ.vars "pad.count"=m + 2∧ σ.vars "source.m"=m

theorem padStep_spec (B M m n:ℕ) (P:Program ℚ m n) (hM:1≤ M) (hMB:M < B)
    (hmB:m + 2 < B) (hb:∀ i,Height (P.b i) M):
    Spec B (fun σ => Invariant P σ∧ σ.vars "pad.k" < m + 2) padStep
      (fun σ τ => Invariant P τ∧ τ.vars "pad.k"=σ.vars "pad.k" + 1) 40:=by
  rintro σ ⟨⟨hσb,hσp,hσkN,hσcount,hσm⟩,hσk⟩
  let i:Fin (m + 2):= ⟨σ.vars "pad.k",hσk⟩
  obtain ⟨τ,hr₁,hτp,hτb,hτm,hτi⟩:=padCoordinate_spec B M m n P i
    (filled (value P) i.val) (by simpa only [filled,List.length_ofFn] using i.isLt)
    hM hMB hmB hb σ ⟨hσb,hσp,hσm,rfl⟩
  have hτcount:=(hr₁.frame_var "pad.count" (by decide)).trans hσcount
  have h1:1 < B:=hM.trans_lt hMB
  have hiB:i.val < B:=i.isLt.trans hmB
  have hi1B:i.val + 1 < B:=lt_of_le_of_lt i.isLt hmB
  have hr₂:Run B (.assign "pad.k" (.add (.var "pad.k") (.lit 1))) τ
      (τ.setVar "pad.k" (i.val + 1)) 4:=by
    exact Run.assign (by simpa only [hτi,Bop.apply_add] using (evalB_bin
      (evalB_var (B:=B) (σ:=τ) (x:= "pad.k") (hτi ▸ hiB)) (evalB_lit h1)
      (show Bop.add.apply (τ.vars "pad.k") 1 < B by simpa [hτi] using hi1B)))
  have hfilled:Represents "pad.b" (filled (value P) (i.val + 1)) τ:=by
    rw [← filled_step]
    exact hτp
  refine ⟨_,hr₁.seq hr₂, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simpa only [Represents,arrs_setVar] using hτb
  · simpa only [Represents,arrs_setVar,vars_setVar,ite_true] using hfilled
  · change i.val + 1≤ m + 2
    exact i.isLt
  · simpa using hτcount
  · simpa using hτm
  · simp [i]

theorem padLoop_spec (B M m n:ℕ) (P:Program ℚ m n) (hM:1≤ M) (hMB:M < B)
    (hmB:m + 2 < B) (hb:∀ i,Height (P.b i) M):
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ∧
        Represents "pad.b" (List.replicate (m + 2) 0) σ∧
        σ.vars "pad.count"=m + 2∧ σ.vars "source.m"=m)
      padLoop
      (fun _ τ => Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ∧
        Represents "query.b" (List.ofFn P.b) τ∧ τ.vars "source.m"=m) (44 * (m + 2) + 6):=by
  have hlo:=Spec.forRangeZero "pad.k" "pad.count" (Invariant P) (m + 2) 40 hmB
    (fun _ h => h.2.2.1) (fun _ h => h.2.2.2.1) (padStep_spec B M m n P hM hMB hmB hb)
  refine (hlo.pre ?_).post ?_
  · rintro σ ⟨hb,hp,hcount,hm⟩
    simp_all [Invariant,Represents,filled_zero]
  · rintro σ τ _ ⟨hτ,hk⟩
    refine ⟨?_,hτ.1,hτ.2.2.2.2⟩
    have he:List.ofFn (value P)=List.ofFn (FeasibilityPadding.pad P).b:=by
      congr 1
      funext i
      exact value_eq P i
    simpa only [hk,filled_done,he] using hτ.2.1

set_option maxHeartbeats 0 in
theorem padBound_spec (B M m n:ℕ) (P:Program ℚ m n) (hM:1≤ M) (hMB:M < B)
    (hmB:m + 2 < B) (hb:∀ i,Height (P.b i) M):
    Spec B (fun σ => Represents "query.b" (List.ofFn P.b) σ∧ Extents "pad.b" (m + 2) σ∧
        σ.vars "source.m"=m) padBound
      (fun _ τ => Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ∧
        Represents "query.b" (List.ofFn P.b) τ∧ τ.vars "source.m"=m) (77 * (m + 2) + 30):=by
  have h1:1 < B:=hM.trans_lt hMB
  have h2:2 < B:=by omega
  have hm:m < B:=by omega
  have hzero:=spec_with_write_frame ["source.m", "pad.count"]
    (RamZeroArray.zeroRationalArray_spec B (m + 2) "pad.b" hmB h1)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide)
  have hlo:=padLoop_spec B M m n P hM hMB hmB hb
  rintro σ ⟨hσb,hσpad,hσm⟩
  have hs:=hσpad ".s" (by simp)
  have hn:=hσpad ".n" (by simp)
  have hd:=hσpad ".d" (by simp)
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat:=c0 (Env.vars σ "source.m") ((2:Nat)); let c2:Env:=Env.setVar σ "pad.count" c1; let c3:Nat:=Env.vars c2 "pad.count"; let c4:Env:=Env.setVar c2 "vec.n" c3; let c5:Env→ Nat→ Prop:=Run B (RamZeroArray.zeroRationalArray "pad.b") c4; let c6:Nat→ Nat→ Nat:=Nat.mul; let c7:Nat:=c0 m ((2:Nat)); let c8:Nat:=c0 (c6 ((33:Nat)) c7) ((18:Nat)); let c9:Env→ Prop:=Represents "pad.b" (@List.replicate Rat c7 (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0)))); let c10:String→ String:= @HAppend.hAppend String String String (@instHAppendOfAppend String instAppendString) "pad.b"; let c11:String:=c10 ".s"; let c12:String:=c10 ".n"; let c13:String:=c10 ".d"; let c14:String→ List Nat:=Env.arrs c4; let c15:Env→ Env→ Prop:=FieldsAgree (@List.cons String "source.m" (@List.cons String "pad.count" (@List.nil String))); let c16:Env→ Prop:=c15 c4; let c17:Env→ Prop:=fun (σ':Env) => And (c5 σ' c8) (And (And (c9 σ') (And (@Eq Nat (Env.vars σ' "vec.n") c7) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs σ' b) (c14 b)))) (And (c16 σ') (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.b"), @Eq (List Nat) (Env.arrs σ' a) (c14 a)))); let c18:Nat:=c0 (c6 ((77:Nat)) c7) ((30:Nat)); let c19:Env→ Prop:=Represents "pad.b" (@List.ofFn Rat c7 (@Program.b Rat c7 (c0 n ((2:Nat))) (@FeasibilityPadding.pad Rat (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)) (@AddMonoidWithOne.toOne Rat (@AddGroupWithOne.toAddMonoidWithOne Rat (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))) m n P))); let c20:Env→ Prop:=Represents "query.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c21:Env→ Env→ Prop:=fun (x τ:Env) => And (c19 τ) (And (c20 τ) (@Eq Nat (Env.vars τ "source.m") m)); let c22:Env→ Prop:=c21 σ; let c23:Env→ Prop:=fun (σ':Env) => And (Run B padBound σ σ' c18) (c22 σ'); let c24:Nat:=c0 (c6 ((44:Nat)) c7) ((6:Nat)); let c25:Nat→ Nat:=c0 ((1:Nat)); let c26:Expr:=Expr.add (Expr.var "source.m") (Expr.lit ((2:Nat))); let c27:Nat:=c25 (Expr.size c26); let c28:Nat:=c25 (Expr.size (Expr.var "pad.count")); let c29:Nat:=c0 c8 c24; let c30:Nat:=c0 c28 c29; @Exists.casesOn Env c17 (fun (x:@Exists Env c17) => @Exists Env c23) (RunStep.use B (fun (σ_1:Env) => And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c11)) c7) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c12)) c7) (And (@Eq Nat (@List.length Nat (Env.arrs σ_1 c13)) c7) (@Eq Nat (Env.vars σ_1 "vec.n") c7)))) (RamZeroArray.zeroRationalArray "pad.b") (fun (σ_1 τ:Env) => And (And (c9 τ) (And (@Eq Nat (Env.vars τ "vec.n") c7) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs τ b) (Env.arrs σ_1 b)))) (And (c15 σ_1 τ) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.b"), @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c8 hzero c4 ?_) fun (w:Env) (h:And (c5 w c8) (And (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") c7) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c14 b)))) (And (c16 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.b"), @Eq (List Nat) (Env.arrs w a) (c14 a))))) => let c0_1:Prop:=And (And (c9 w) (And (@Eq Nat (Env.vars w "vec.n") c7) (∀ b∉ @List.cons String c11 (@List.cons String c12 (@List.cons String c13 (@List.nil String))), @Eq (List Nat) (Env.arrs w b) (c14 b)))) (And (c16 w) (∀ a∉ Com.warrs (RamZeroArray.zeroRationalArray "pad.b"), @Eq (List Nat) (Env.arrs w a) (c14 a))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B padLoop w σ' c24) (And (c19 σ') (And (c20 σ') (@Eq Nat (Env.vars σ' "source.m") m))); @And.casesOn (c5 w c8) c0_1 (fun (x:And (c5 w c8) c0_1) => @Exists Env c23) h fun (left:c5 w c8) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c23) (RunStep.use B (fun (σ_1:Env) => And (c20 σ_1) (And (c9 σ_1) (And (@Eq Nat (Env.vars σ_1 "pad.count") c7) (@Eq Nat (Env.vars σ_1 "source.m") m)))) padLoop c21 c24 hlo w ?_) fun (w_1:Env) (h_1:And (Run B padLoop w w_1 c24) (And (c19 w_1) (And (c20 w_1) (@Eq Nat (Env.vars w_1 "source.m") m)))) => let c0_2:Prop:=And (c19 w_1) (And (c20 w_1) (@Eq Nat (Env.vars w_1 "source.m") m)); @And.casesOn (Run B padLoop w w_1 c24) c0_2 (fun (x:And (Run B padLoop w w_1 c24) c0_2) => @Exists Env c23) h_1 fun (left_1:Run B padLoop w w_1 c24) (right_1:c0_2) => @Exists.intro Env c23 w_1 (@And.intro (Run B padBound σ w_1 c18) (c22 w_1) (RunStep.mono B padBound σ w_1 (c0 c27 c30) c18 (RunStep.seq B (Com.assign "pad.count" c26) (Com.seq (Com.assign "vec.n" (Expr.var "pad.count")) (Com.seq (RamZeroArray.zeroRationalArray "pad.b") padLoop)) σ c2 w_1 c27 c30 (RunStep.assign B σ "pad.count" c26 c1 (RunStep.eval_add B σ (Expr.var "source.m") (Expr.lit ((2:Nat))) (Env.vars σ "source.m") ((2:Nat)) (RunStep.eval_var B σ "source.m" (?nAX_g4855_0_0_0)) (RunStep.eval_lit B ((2:Nat)) σ h2) (?nAX_g4855_0_0_1))) (RunStep.seq B (Com.assign "vec.n" (Expr.var "pad.count")) (Com.seq (RamZeroArray.zeroRationalArray "pad.b") padLoop) c2 c4 w_1 c28 c29 (RunStep.assign B c2 "vec.n" (Expr.var "pad.count") c3 (RunStep.eval_var B c2 "pad.count" (?nAX_g4855_0_0_2))) (RunStep.seq B (RamZeroArray.zeroRationalArray "pad.b") padLoop c4 w w_1 c8 c24 left left_1))) (?nAX_g4855_0_0_3)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4855_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4855_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4855_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4855_0_0_3 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hzero hlo
  all_goals simp_all [FieldsAgree,Represents,Extents]
  all_goals aesop

end Lax109476Proofs.RamPadBound

end

section

namespace Lax109476Proofs.RamQueryPadding

open Lax109476.LinearProgram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamFrame RationalArithmeticBounds RamEllipsoidStep RamMatrixStorage

def Output {m n:ℕ} (P:Program ℚ m n) (S:ℕ) (τ:Env):Prop:=
  Represents "pad.A" (RamMatrixStorage.flatten (FeasibilityPadding.pad P).A) τ∧
    Represents "pad.b" (List.ofFn (FeasibilityPadding.pad P).b) τ∧
    Represents "query.A" (RamMatrixStorage.flatten P.A) τ∧ Represents "query.b" (List.ofFn P.b) τ∧
    τ.vars "query.m"=m + 2∧ τ.vars "query.n"=n + 2∧ τ.vars "query.bits"=S + 4

set_option maxHeartbeats 0 in
theorem padQuery_spec (B M m n S:ℕ) (P:Program ℚ m n)
    (hM:1≤ M) (hMB:M < B) (hdim:(m + 2) * (n + 2) + m + n + 4 < B)
    (hSB:S + 4 < B) (hA:∀ i j,Height (P.A i j) M) (hb:∀ i,Height (P.b i) M):
    Spec B (Input P S) padQuery (fun _ τ => Output P S τ)
      (111 * ((m + 2) * (n + 2)) + 77 * (m + 2) + 78):=by
  have hmatrix:=spec_with_write_frame ["source.m", "source.n", "source.bits"]
    (RamPadMatrix.padMatrix_spec B M m n P hM hMB hdim hA)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hbound:=spec_with_write_frame ["source.m", "source.n", "source.bits"]
    (RamPadBound.padBound_spec B M m n P hM hMB (by omega) hb)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> decide)
  have hmB:m + 2 < B:=by omega
  have hnB:n + 2 < B:=by omega
  have hm:m < B:=by omega
  have hn:n < B:=by omega
  have hS:S < B:=by omega
  have hmatarrs:RamPadMatrix.padMatrix.warrs =
      ["pad.A.s", "pad.A.n", "pad.A.d", "pad.A.s", "pad.A.s", "pad.A.n", "pad.A.d"]:=by rfl
  have hboundarrs:RamPadBound.padBound.warrs =
      ["pad.b.s", "pad.b.n", "pad.b.d", "pad.b.s", "pad.b.s", "pad.b.n", "pad.b.d"]:=by rfl
  have h2:2 < B:=by omega
  have h4:4 < B:=by
    have hh:4≤ (m + 2) * (n + 2):=by nlinarith
    omega
  rintro σ ⟨hσA,hσb,hσpadA,hσpadb,hσm,hσn,hσbits⟩
  have hbs:=hσpadb ".s" (by simp)
  have hbn:=hσpadb ".n" (by simp)
  have hbd:=hσpadb ".d" (by simp)
  (expose_names;
    (refine let c0:Nat→ Nat→ Nat:=Nat.add; let c1:Nat→ Nat→ Nat:=Nat.mul; let c2:Nat:=c0 m ((2:Nat)); let c3:Nat:=c0 n ((2:Nat)); let c4:Nat:=c1 c2 c3; let c5:Nat→ Nat:=c0 (c1 ((111:Nat)) c4); let c6:Nat:=c5 ((36:Nat)); let c7:Program Rat (Nat.add m ((2:Nat))) (Nat.add n ((2:Nat))):= @FeasibilityPadding.pad Rat (@MulZeroClass.toZero Rat (@instMulZeroClassOfSemiring Rat Rat.semiring)) (@AddMonoidWithOne.toOne Rat (@AddGroupWithOne.toAddMonoidWithOne Rat (@Ring.toAddGroupWithOne Rat (@DivisionRing.toRing Rat Rat.instDivisionRing)))) m n P; let c8:Env→ Prop:=Represents "pad.A" (@flatten c2 c3 (@Program.A Rat c2 c3 c7)); let c9:Env→ Prop:=Represents "query.A" (@flatten m n (@Program.A Rat m n P)); let c10:Env→ Env→ Prop:=FieldsAgree (@List.cons String "source.m" (@List.cons String "source.n" (@List.cons String "source.bits" (@List.nil String)))); let c11:Env→ Prop:=c10 σ; let c12:Env→ Prop:=fun (σ':Env) => And (Run B RamPadMatrix.padMatrix σ σ' c6) (And (And (c8 σ') (And (c9 σ') (And (@Eq Nat (Env.vars σ' "source.m") m) (@Eq Nat (Env.vars σ' "source.n") n)))) (And (c11 σ') (∀ a∉ Com.warrs RamPadMatrix.padMatrix, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs σ a)))); let c13:Nat:=c1 ((77:Nat)) c2; let c14:Nat:=c0 (c5 c13) ((78:Nat)); let c15:Env→ Prop:=(fun (x τ:Env) => @Output m n P S τ) σ; let c16:Env→ Prop:=fun (σ':Env) => And (Run B padQuery σ σ' c14) (c15 σ'); let c17:Env→ Prop:=Extents "pad.A" c4; let c18:Nat:=c0 c13 ((30:Nat)); let c19:Env→ Prop:=Represents "pad.b" (@List.ofFn Rat c2 (@Program.b Rat c2 c3 c7)); let c20:Env→ Prop:=Represents "query.b" (@List.ofFn Rat m (@Program.b Rat m n P)); let c21:Env→ Prop:=Extents "pad.b" c2; let c22:Nat→ Nat:=c0 ((1:Nat)); let c23:Expr:=Expr.add (Expr.var "source.m") (Expr.lit ((2:Nat))); let c24:Nat:=c22 (Expr.size c23); let c25:Expr:=Expr.add (Expr.var "source.n") (Expr.lit ((2:Nat))); let c26:Nat:=c22 (Expr.size c25); let c27:Expr:=Expr.add (Expr.var "source.bits") (Expr.lit ((4:Nat))); let c28:Nat:=c22 (Expr.size c27); let c29:Nat:=c0 c26 c28; let c30:Nat:=c0 c24 c29; let c31:Nat:=c0 c18 c30; let c32:Com:=Com.assign "query.m" c23; let c33:Com:=Com.assign "query.n" c25; let c34:Com:=Com.assign "query.bits" c27; let c35:Com:=Com.seq c33 c34; let c36:Com:=Com.seq c32 c35; @Exists.casesOn Env c12 (fun (x:@Exists Env c12) => @Exists Env c16) (RunStep.use B (fun (σ_1:Env) => And (c9 σ_1) (And (c17 σ_1) (And (@Eq Nat (Env.vars σ_1 "source.m") m) (@Eq Nat (Env.vars σ_1 "source.n") n)))) RamPadMatrix.padMatrix (fun (σ_1 τ:Env) => And (And (c8 τ) (And (c9 τ) (And (@Eq Nat (Env.vars τ "source.m") m) (@Eq Nat (Env.vars τ "source.n") n)))) (And (c10 σ_1 τ) (∀ a∉ Com.warrs RamPadMatrix.padMatrix, @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c6 hmatrix σ ?_) fun (w:Env) (h:And (Run B RamPadMatrix.padMatrix σ w c6) (And (And (c8 w) (And (c9 w) (And (@Eq Nat (Env.vars w "source.m") m) (@Eq Nat (Env.vars w "source.n") n)))) (And (c11 w) (∀ a∉ Com.warrs RamPadMatrix.padMatrix, @Eq (List Nat) (Env.arrs w a) (Env.arrs σ a))))) => let c0_1:Prop:=And (And (c8 w) (And (c9 w) (And (@Eq Nat (Env.vars w "source.m") m) (@Eq Nat (Env.vars w "source.n") n)))) (And (c11 w) (∀ a∉ Com.warrs RamPadMatrix.padMatrix, @Eq (List Nat) (Env.arrs w a) (Env.arrs σ a))); let c1_1:Env→ Prop:=fun (σ':Env) => And (Run B RamPadBound.padBound w σ' c18) (And (And (c19 σ') (And (c20 σ') (@Eq Nat (Env.vars σ' "source.m") m))) (And (c10 w σ') (∀ a∉ Com.warrs RamPadBound.padBound, @Eq (List Nat) (Env.arrs σ' a) (Env.arrs w a)))); @And.casesOn (Run B RamPadMatrix.padMatrix σ w c6) c0_1 (fun (x:And (Run B RamPadMatrix.padMatrix σ w c6) c0_1) => @Exists Env c16) h fun (left:Run B RamPadMatrix.padMatrix σ w c6) (right:c0_1) => @Exists.casesOn Env c1_1 (fun (x:@Exists Env c1_1) => @Exists Env c16) (RunStep.use B (fun (σ_1:Env) => And (c20 σ_1) (And (c21 σ_1) (@Eq Nat (Env.vars σ_1 "source.m") m))) RamPadBound.padBound (fun (σ_1 τ:Env) => And (And (c19 τ) (And (c20 τ) (@Eq Nat (Env.vars τ "source.m") m))) (And (c10 σ_1 τ) (∀ a∉ Com.warrs RamPadBound.padBound, @Eq (List Nat) (Env.arrs τ a) (Env.arrs σ_1 a)))) c18 hbound w ?_) fun (w_1:Env) (h_1:And (Run B RamPadBound.padBound w w_1 c18) (And (And (c19 w_1) (And (c20 w_1) (@Eq Nat (Env.vars w_1 "source.m") m))) (And (c10 w w_1) (∀ a∉ Com.warrs RamPadBound.padBound, @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs w a))))) => let c0_2:Prop:=And (And (c19 w_1) (And (c20 w_1) (@Eq Nat (Env.vars w_1 "source.m") m))) (And (c10 w w_1) (∀ a∉ Com.warrs RamPadBound.padBound, @Eq (List Nat) (Env.arrs w_1 a) (Env.arrs w a))); let c1_2:Nat:=c0 (Env.vars w_1 "source.m") ((2:Nat)); let c2_1:Env:=Env.setVar w_1 "query.m" c1_2; let c3_1:Nat:=Env.vars c2_1 "source.n"; let c4_1:Nat:=c0 c3_1 ((2:Nat)); let c5_1:Env:=Env.setVar c2_1 "query.n" c4_1; let c6_1:Nat:=Env.vars c5_1 "source.bits"; let c7_1:Nat:=c0 c6_1 ((4:Nat)); let c8_1:Env:=Env.setVar c5_1 "query.bits" c7_1; @And.casesOn (Run B RamPadBound.padBound w w_1 c18) c0_2 (fun (x:And (Run B RamPadBound.padBound w w_1 c18) c0_2) => @Exists Env c16) h_1 fun (left_1:Run B RamPadBound.padBound w w_1 c18) (right_1:c0_2) => @Exists.intro Env c16 c8_1 (@And.intro (Run B padQuery σ c8_1 c14) (c15 c8_1) (RunStep.mono B padQuery σ c8_1 (c0 c6 c31) c14 (RunStep.seq B RamPadMatrix.padMatrix (Com.seq RamPadBound.padBound c36) σ w c8_1 c6 c31 left (RunStep.seq B RamPadBound.padBound c36 w w_1 c8_1 c18 c30 left_1 (RunStep.seq B c32 c35 w_1 c2_1 c8_1 c24 c29 (RunStep.assign B w_1 "query.m" c23 c1_2 (RunStep.eval_add B w_1 (Expr.var "source.m") (Expr.lit ((2:Nat))) (Env.vars w_1 "source.m") ((2:Nat)) (RunStep.eval_var B w_1 "source.m" (?nAX_g4859_0_0_0)) (RunStep.eval_lit B ((2:Nat)) w_1 h2) (?nAX_g4859_0_0_1))) (RunStep.seq B c33 c34 c2_1 c5_1 c8_1 c26 c28 (RunStep.assign B c2_1 "query.n" c25 c4_1 (RunStep.eval_add B c2_1 (Expr.var "source.n") (Expr.lit ((2:Nat))) c3_1 ((2:Nat)) (RunStep.eval_var B c2_1 "source.n" ?_) (RunStep.eval_lit B ((2:Nat)) c2_1 h2) ?_)) (RunStep.assign B c5_1 "query.bits" c27 c7_1 (RunStep.eval_add B c5_1 (Expr.var "source.bits") (Expr.lit ((4:Nat))) c6_1 ((4:Nat)) (RunStep.eval_var B c5_1 "source.bits" ?_) (RunStep.eval_lit B ((4:Nat)) c5_1 h4) ?_)))))) (?nAX_g4859_0_0_2)) ?_) <;> try dsimp +zetaDelta at *); (all_goals try dsimp +zetaDelta at *); (try case' nAX_g4859_0_0_0 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4859_0_0_1 => solve | omega | (simp <;> omega) | assumption | simp_all); (try case' nAX_g4859_0_0_2 => solve | omega | (simp <;> omega) | assumption | simp_all); (all_goals try clear h); (all_goals try clear left); (all_goals try clear h_1); (all_goals try clear left_1))
  all_goals clear hmatrix hbound
  all_goals simp_all [Input,Output,FieldsAgree,Represents,Extents,hmatarrs,hboundarrs]
  all_goals aesop
  all_goals omega

end Lax109476Proofs.RamQueryPadding

end

section

namespace Lax109476Proofs.RamPaddedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep RamMatrixStorage IntegerEncoding RationalArithmeticBounds

 theorem rationalProgram_pad {m n:ℕ} (P:Program ℤ m n):
    rationalProgram (FeasibilityPadding.pad P)=FeasibilityPadding.pad (rationalProgram P):=by
  unfold FeasibilityPadding.pad rationalProgram
  congr 1
  · funext i j
    refine Fin.addCases ?_ ?_ i
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp
    · intro i
      refine Fin.addCases ?_ ?_ j <;> intro j <;> simp [apply_ite]
  · funext i
    refine Fin.addCases ?_ ?_ i <;> intro i <;> simp
  · funext j
    refine Fin.addCases ?_ ?_ j <;> intro j <;> simp

set_option maxHeartbeats 0 in
theorem decideFeasible_spec (m n S w:ℕ) (P:Program ℤ m n) (hdim:m + n≤ S)
    (hA:∀ i j, (P.A i j).natAbs≤ 2 ^ (2 * S))
    (hb:∀ i, (P.b i).natAbs≤ 2 ^ (2 * S)) (hw:wordWidth S≤ w):
    Spec (2 ^ w) (Input P S) decideFeasible
      (fun _ τ => decide (τ.vars "search.found"=1)=FeasibilityPadding.feasible P (2 ^ (2 * (S + 4))))
      (instructionBound S):=by
  let H:=2 ^ (2 * S)
  have hH:1≤ H:=Nat.one_le_pow _ _ (by decide)
  have hwInt:RamIntegerFeasibility.wordWidth (S + 4)≤ w:=by unfold wordWidth at hw; omega
  have hwDec:RamDecoder.wordWidth (2 * S)≤ w:=by unfold wordWidth at hw; omega
  have hHB:H < 2 ^ w:=Nat.pow_lt_pow_right (by decide)
    (by unfold RamDecoder.wordWidth at hwDec; omega)
  have hdims:(m + 2) * (n + 2) + m + n + 4 < 2 ^ w:=by
    have hmn:(m + 2) * (n + 2)≤ (S + 4) ^ 2:=by
      have h:=Nat.mul_le_mul (show m + 2≤ S + 4 by omega) (show n + 2≤ S + 4 by omega)
      simpa only [pow_two] using h
    have hh:=(Nat.lt_two_pow_self (n:=(S + 4) ^ 2 + S + 5)).trans_le
      (Nat.pow_le_pow_right (by decide) (show (S + 4) ^ 2 + S + 5≤ w by unfold wordWidth at hw; omega))
    omega
  have hSB:S + 4 < 2 ^ w:=
    (Nat.lt_two_pow_self (n:=S + 4)).trans_le
      (Nat.pow_le_pow_right (by decide) (by unfold wordWidth at hw; omega))
  have hAH:∀ i j,Height ((rationalProgram P).A i j) H:=by
    intro i j
    simpa [Height,rationalProgram,H] using And.intro (hA i j) hH
  have hbH:∀ i,Height ((rationalProgram P).b i) H:=by
    intro i
    simpa [Height,rationalProgram,H] using And.intro (hb i) hH
  have hlarge:H≤ 2 ^ (2 * (S + 4)):=Nat.pow_le_pow_right (by decide) (by omega)
  obtain ⟨hpadA,hpadb⟩:=FeasibilityPadding.padded_bounds P H hH hA hb
  rintro σ ⟨hσpad,hσrows,hσrhs,hσcenter,hσshape,hσworkspace,hσnormal⟩
  obtain ⟨τ,hr₁,hτA,hτb,hτsourceA,hτsourceb,hτm,hτn,hτbits⟩:=
    RamQueryPadding.padQuery_spec (2 ^ w) H m n S (rationalProgram P)
      hH hHB hdims hSB hAH hbH σ hσpad
  have hτinput:RamFeasibilitySetup.Input (FeasibilityPadding.pad P) (S + 4) τ:=by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,hτm,hτn,hτbits⟩
    · simpa only [rationalProgram_pad] using hτA
    · simpa only [rationalProgram_pad] using hτb
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrows
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσrhs
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσcenter
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσshape
    · exact RamAdvanceState.workspace_of_run hr₁ _ hσworkspace
    · exact RamAdvanceState.extents_of_run hr₁ _ _ hσnormal
  obtain ⟨υ,hr₂,hυ⟩:=RamIntegerFeasibility.decideFeasible_uniform_spec (m + 2) (n + 2) (S + 4) w
    (FeasibilityPadding.pad P) (by omega) (by omega)
    (fun i j => (hpadA i j).trans hlarge) (fun i => (hpadb i).trans hlarge) hwInt τ hτinput
  have hprod:(m + 2) * (n + 2)≤ (S + 4) ^ 2:=by
    have h:=Nat.mul_le_mul (show m + 2≤ S + 4 by omega) (show n + 2≤ S + 4 by omega)
    simpa only [pow_two] using h
  have hm:=Nat.mul_le_mul_left 111 hprod
  have hbcount:=Nat.mul_le_mul_left 77 (show m + 2≤ S + 4 by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by unfold instructionBound; omega),hυ⟩

end Lax109476Proofs.RamPaddedFeasibility

end

section

namespace Lax109476Proofs.RamRationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalEncoding Lax109476.RationalCertificates
open Lax759944.BinaryWordEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RamRationalArrays RamEllipsoidStep IntegerEncoding

theorem decideFeasible_spec (m n:ℕ) (P:Program ℚ m n) (w:ℕ)
    (hw:wordWidth (bitSize (encodeProgram P))≤ w):
    Spec (2 ^ w) (RamFeasibilityQuery.Input P) decideFeasible
      (fun _ τ => decide (τ.vars "search.found"=1)=RationalFeasibilityDecision.feasible P)
      (instructionBound (bitSize (encodeProgram P))):=by
  let L:=bitSize (encodeProgram P)
  have hwCopy:RamDecoder.wordWidth (2 * L)≤ w:=by dsimp only [L]; unfold wordWidth at hw; omega
  have hwFeas:RamPaddedFeasibility.wordWidth L≤ w:=by dsimp only [L]; unfold wordWidth at hw; omega
  have hdim:=EncodingSize.dimension_bound P
  obtain ⟨hA,hb,hc⟩:=integerProgram_bounds P
  intro σ hσ
  obtain ⟨τ,hr₁,hτ⟩:=RamFeasibilityQuery.copyInput_spec m n P w hwCopy σ hσ
  obtain ⟨υ,hr₂,hυ⟩:=RamPaddedFeasibility.decideFeasible_spec m n L w (integerProgram P)
    hdim hA hb hwFeas τ hτ
  have hcells:=RamSolverInitialization.cells_bound P
  have hcost:=Nat.mul_le_mul_left 71 (show m * n + m≤ L by omega)
  exact ⟨υ, (hr₁.seq hr₂).mono (by dsimp only [instructionBound,L]; dsimp only [L] at hcost; omega),hυ⟩

end Lax109476Proofs.RamRationalFeasibility

end

theorem solution:∀ (m n:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (w:Nat),
  Nat.le
      (Lax109476Proofs.RamRationalFeasibility.wordWidth
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P)))
      w→
    Lax808846Proofs.Reasoning.Spec
      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
        ((2:Nat)) w)
      (@Lax109476Proofs.RamFeasibilityQuery.Input m n P) Lax109476Proofs.RamRationalFeasibility.decideFeasible
      (fun (x τ:Lax808846Proofs.Imp.Env) =>
        @Eq Bool
          (@Decidable.decide (@Eq Nat (τ.vars "search.found") ((1:Nat)))
            (instDecidableEqNat (τ.vars "search.found") ((1:Nat))))
          (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P))
      (Lax109476Proofs.RamRationalFeasibility.instructionBound
        (Lax759944.BinaryWordEncoding.bitSize (@Lax109476.RationalEncoding.encodeProgram m n P))):= @Lax109476Proofs.RamRationalFeasibility.decideFeasible_spec
