-- Prove2me | solution 1 for Lax263307Proofs.NativeSelectedBudget.exists_budget_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:00:28.53121+00:00
-- url     : https://prove2.me/submissions/3374f037-e21d-4b39-8d70-0f70834712df

import Mathlib.Tactic
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces

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

end Lax808846Proofs.Reasoning

end

section

open scoped NNReal NNRat

namespace Lax455465.RationalEncoding

open Lax455465.ProductNetwork Lax455465.ConcurrentFlow

structure FlowCertificate (n:ℕ) where

  value:ℚ≥0

  paths:List (List (Fin n) × ℚ≥0)

end Lax455465.RationalEncoding

end

section

namespace Lax455465Proofs.RamPolynomial

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem value_mono (coefficients:List ℕ) {x y:ℕ} (h:x≤ y):
    value coefficients x≤ value coefficients y:=by
  induction coefficients with
  | nil => rfl
  | cons a rest ih => exact Nat.add_le_add_left (Nat.mul_le_mul h ih) a

theorem exists_coefficients (p:Polynomial ℕ):∃ coefficients:List ℕ,
    ∀ x:ℕ,value coefficients x=p.eval x:=by
  refine Polynomial.recOnHorner p ?_ ?_ ?_
  · exact ⟨[],fun _ => by simp [value]⟩
  · intro q a _ _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    cases coefficients with
    | nil =>
      refine ⟨[a], ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp [value]
    | cons b rest =>
      refine ⟨(b + a)::rest, ?_⟩
      intro x
      rw [Polynomial.eval_add,Polynomial.eval_C, ← hcoeff x]
      simp only [value]
      omega
  · intro q _ ih
    obtain ⟨coefficients,hcoeff⟩:=ih
    refine ⟨0::coefficients, ?_⟩
    intro x
    simp only [value,Nat.zero_add,hcoeff,Polynomial.eval_mul,Polynomial.eval_X,Nat.mul_comm]

end Lax455465Proofs.RamPolynomial

end

section

namespace Lax455465Proofs.RamLpRationalRead

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning RamRational RamVirtualState
open Lax109476.RationalEncoding

def command:Com:=.seq (.assign "rat.s" (.get "vm.output" (.var "cert.cursor")))
  (.seq (.assign "rat.n" (.get "vm.output" (.add (.var "cert.cursor") (.lit 1))))
    (.seq (.assign "rat.d" (.get "vm.output" (.add (.var "cert.cursor") (.lit 2))))
      (.assign "cert.cursor" (.add (.var "cert.cursor") (.lit 3)))))

end Lax455465Proofs.RamLpRationalRead

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeMasks

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState Lax263307.WeightedIndependentSet

theorem mask_test_bit {n:ℕ} (I:Finset (Fin n)) (j:ℕ):
    (mask I).testBit j=decide (j∈I.image Fin.val):=by
  apply Bool.eq_iff_iff.mpr
  rw [decide_eq_true_iff,←Nat.mem_bitIndices,←List.mem_toFinset]
  change j∈Finset.equivBitIndices (mask I)↔ j∈I.image Fin.val
  rw [mask,Lax263307.NativeCatalog.subsetMask,Equiv.apply_symm_apply]

theorem mask_insert {n:ℕ} (I:Finset (Fin n)) (v:Fin n):
    mask (insert v I)=Nat.lor (mask I) (2^v.val):=by
  apply Nat.eq_of_testBit_eq
  intro j
  change (mask (insert v I)).testBit j=((mask I) ||| (2^v.val)).testBit j
  rw [Nat.testBit_or,mask_test_bit,mask_test_bit,Nat.testBit_two_pow]
  simp only [Finset.image_insert,Finset.mem_insert]
  by_cases he:j=v.val <;> by_cases hm:j∈I.image Fin.val <;> simp [he,hm,eq_comm]

def initialSet {n:ℕ} (I:Finset (Fin n)) (i:ℕ):Finset (Fin n):=
  I.filter fun v => v.val < i

theorem prefix_succ {n:ℕ} (I:Finset (Fin n)) (i:ℕ) (hi:i< n):
    initialSet I (i+1)=if (⟨i,hi⟩:Fin n)∈I then insert ⟨i,hi⟩ (initialSet I i) else initialSet I i:=by
  ext v
  by_cases hv:v.val=i
  · have he:v=⟨i,hi⟩:=Fin.ext hv
    subst v
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [initialSet,hm]
  · have he:v≠⟨i,hi⟩:=fun h => hv (congrArg Fin.val h)
    by_cases hm:(⟨i,hi⟩:Fin n)∈I <;> simp [hm,initialSet,he] <;> omega

end Lax263307Proofs.NativeMasks

end

section

namespace Lax263307Proofs.NativeDistanceData

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax109476.LinearProgram Lax109476.RationalEncoding
open Lax263307.DistanceProjection

structure Data {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (σ:Env):Prop where
  source:Prefix (encodeProgram P) "lp.input" σ
  center:Prefix (encodeVector x) "projection.center" σ
  oldRows:σ.vars "projection.m"=m
  oldColumns:σ.vars "projection.n"=n
  rowCount:σ.vars "lp.rows"=rows m n
  columnCount:σ.vars "lp.columns"=columns n
  matrixLength:σ.vars "projection.matrixLength"=rows m n*columns n

end Lax263307Proofs.NativeDistanceData

end

section

namespace Lax263307Proofs.NativeShoreMasks

open Lax263307 ComputedSeparators VertexSplitting

def partialMask {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:ℕ):ℕ:=
  NativeMasks.mask ((NativeMasks.initialSet S i).image f)

theorem step {r n:ℕ} (f:Fin r→ Fin n) (S:Finset (Fin r)) (i:Fin r):
    Nat.lor (partialMask f S i.val) ((if i∈S then 1 else 0)*2^(f i).val)=partialMask f S (i.val+1):=by
  simp only [partialMask]
  rw [NativeMasks.prefix_succ S i.val i.isLt]
  by_cases h:i∈S
  · simp only [h,if_true,one_mul,Finset.image_insert,NativeMasks.mask_insert]
  · simp [h]

end Lax263307Proofs.NativeShoreMasks

end

section

namespace Lax263307Proofs.NativeFlowQueryResources

open Lax455465Proofs
open Lax759944.BinaryWordEncoding
open Lax263307 ComputedSeparators VertexSplitting NativeSignedArithmetic
open scoped NNRat

theorem eval_mono (P:Polynomial ℕ) {x y:ℕ} (h:x≤ y):P.eval x≤ P.eval y:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  simpa only [hcs] using RamPolynomial.value_mono cs h

end Lax263307Proofs.NativeFlowQueryResources

end

section

namespace Lax263307Proofs.NativeCutPieces

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

structure Data {n:ℕ} (cs:List (Finset (Fin n) × Finset (Fin n))) (σ:Env):Prop where
  cuts:Prefix (NativeCutRecords.words cs) "separator.cuts" σ
  count:σ.vars "separator.count"=cs.length
  remaining:σ.vars "separator.remaining"=mask (ComputedSeparators.remaining Finset.univ cs)

end Lax263307Proofs.NativeCutPieces

end

section

namespace Lax263307Proofs.NativeQuadraticResources

open NativeQuadraticSum

theorem square_power (h:ℕ):(2^h)^2=2^(2*h):=by
  rw [←pow_mul,Nat.mul_comm h 2]

end Lax263307Proofs.NativeQuadraticResources

end

section

namespace Lax263307Proofs.NativePolynomialBudget

open Lax455465Proofs

set_option maxHeartbeats 0

theorem value_bound (cs:List ℕ) (x:ℕ):RamPolynomial.value cs x≤ cs.sum*(x+1)^cs.length:=by
  induction cs with
  | nil => simp [RamPolynomial.value]
  | cons c cs ih =>
    have hp:1≤(x+1)^cs.length:=Nat.one_le_pow _ _ (by omega)
    have hc:c≤ c*(x+1)^cs.length:=Nat.le_mul_of_pos_right _ hp
    have hi:=Nat.mul_le_mul_left x ih
    simp only [RamPolynomial.value,List.sum_cons,List.length_cons]
    calc
      c+x*RamPolynomial.value cs x≤ c+x*(cs.sum*(x+1)^cs.length):=Nat.add_le_add_left hi _
      _≤ c*(x+1)^cs.length+x*(cs.sum*(x+1)^cs.length):=Nat.add_le_add_right hc _
      _≤(c+cs.sum)*(x+1)^cs.length*(x+1):=by ring_nf; omega
      _=_:=by ring

theorem exists_majorant (P:Polynomial ℕ):
    ∃ Q e:ℕ,0< Q∧ 0< e∧ ∀ R,P.eval R≤ Q*(R+1)^e:=by
  obtain ⟨cs,hcs⟩:=RamPolynomial.exists_coefficients P
  refine ⟨cs.sum+1,cs.length+1,by omega,by omega,?_⟩
  intro R
  rw [←hcs]
  exact (value_bound cs R).trans (Nat.mul_le_mul (by omega)
    (Nat.pow_le_pow_right (by omega) (by omega)))

end Lax263307Proofs.NativePolynomialBudget

end

section

namespace Lax263307Proofs.NativePolynomialEnvelope

def Bounded (f:ℕ→ ℕ):Prop:= ∃ P:Polynomial ℕ,∀ R,f R≤ P.eval R

theorem identity:Bounded (fun R => R):= ⟨Polynomial.X,by simp⟩
theorem constant (n:ℕ):Bounded (fun _ => n):= ⟨Polynomial.C n,by simp⟩

theorem add {f g:ℕ→ ℕ} (hf:Bounded f) (hg:Bounded g):Bounded (fun R => f R+g R):=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,hQ⟩:=hg
  exact ⟨P+Q,fun R => by simpa only [Polynomial.eval_add] using Nat.add_le_add (hP R) (hQ R)⟩

theorem mul {f g:ℕ→ ℕ} (hf:Bounded f) (hg:Bounded g):Bounded (fun R => f R*g R):=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,hQ⟩:=hg
  exact ⟨P*Q,fun R => by simpa only [Polynomial.eval_mul] using Nat.mul_le_mul (hP R) (hQ R)⟩

theorem pow {f:ℕ→ ℕ} (k:ℕ) (hf:Bounded f):Bounded (fun R => f R^k):=by
  obtain ⟨P,hP⟩:=hf
  exact ⟨P^k,fun R => by simpa only [Polynomial.eval_pow] using Nat.pow_le_pow_left (hP R) k⟩

theorem eval (P:Polynomial ℕ) {f:ℕ→ ℕ} (hf:Bounded f):Bounded (fun R => P.eval (f R)):=by
  obtain ⟨Q,hQ⟩:=hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

theorem monomial {f:ℕ→ ℕ} (hf:Bounded f):
    ∃ Q e:ℕ,0< Q∧ 0< e∧ ∀ R,f R≤ Q*(R+1)^e:=by
  obtain ⟨P,hP⟩:=hf
  obtain ⟨Q,e,hQ,he,hbound⟩:=NativePolynomialBudget.exists_majorant P
  exact ⟨Q,e,hQ,he,fun R => (hP R).trans (hbound R)⟩

end Lax263307Proofs.NativePolynomialEnvelope
end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeSelectedBudget

open Lax263307 NativeCoreMachine NativePolynomialEnvelope

noncomputable abbrev _root_.AXr9520_0:= @Lax263307Proofs.NativePolynomialBudget.heightPolynomial
noncomputable abbrev _root_.AXr9520_1:= @Lax263307Proofs.NativeOraclePrecision.roundedHeight
noncomputable abbrev _root_.AXr9520_2:= @Lax263307Proofs.NativeSelectedLP.certificateHeight
noncomputable abbrev _root_.AXr9520_3:= @Lax263307Proofs.NativePolynomialEnvelope.constant
noncomputable abbrev _root_.AXr9520_4:= @Lax263307Proofs.NativePolynomialEnvelope.identity
noncomputable abbrev _root_.AXr9520_5:= @Lax263307Proofs.NativeEntryResources.coefficient
noncomputable abbrev _root_.AXr9520_6:= @Lax263307Proofs.NativePolynomialEnvelope.Bounded
noncomputable abbrev _root_.AXr9520_7:= @Lax263307Proofs.NativeSelectedLP.Program.width
noncomputable abbrev _root_.AXr9520_8:= @Lax263307Proofs.NativePolynomialEnvelope.eval
noncomputable abbrev _root_.AXr9520_9:= @Lax263307Proofs.NativeSelectedLP.Program.code
noncomputable abbrev _root_.AXr9520_10:= @Lax263307Proofs.NativeSelectedLP.Program.time
noncomputable abbrev _root_.AXr9520_11:= @Lax455465Proofs.RamVirtualConstants.allowance
noncomputable abbrev _root_.AXr9520_12:= @Lax263307Proofs.NativePolynomialEnvelope.add
noncomputable abbrev _root_.AXr9520_13:= @Lax263307Proofs.NativePolynomialEnvelope.mul
noncomputable abbrev _root_.AXr9520_14:= @Lax263307Proofs.NativePolynomialEnvelope.pow
theorem polynomial:∀ {lp flow:List Nat→ List Nat} (cfg:Lax263307Proofs.NativeCoreMachine.Config)
  (p:Lax263307Proofs.NativeSelectedLP.Program lp) (q:Lax263307Proofs.NativeSelectedNear.Program flow) (c:Nat),
  AXr9520_6 (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c):=
fun {lp flow:List Nat→ List Nat} (cfg:Lax263307Proofs.NativeCoreMachine.Config)
    (p:Lax263307Proofs.NativeSelectedLP.Program lp) (q:Lax263307Proofs.NativeSelectedNear.Program flow) (c:Nat) =>
  let c0:Nat→ Nat:=fun (R:Nat) => @Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R;
  let c1:Prop:=AXr9520_6 c0;
  let c2:Nat→ Nat→ Nat:=Nat.add;
  let c3:Nat→ Nat→ Nat:=Nat.mul;
  let c4:Nat→ Nat:=c2 ((2:Nat));
  let c5:Nat→ Nat:=c3 ((3:Nat));
  let c6:Nat→ Nat:=c3 ((6:Nat));
  let c7:Nat→ Nat→ Nat:=
    @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)));
  let c8:Nat→ Nat:=c3 ((4:Nat));
  let c9:Nat→ Nat:=c3 ((2:Nat));
  let c10:Nat→ Nat:=c3 ((5:Nat));
  let c11:Nat:=c6 (@List.length Nat (@Lax263307Proofs.NativeSelectedLP.Program.coeff lp p));
  let c12:Nat:=c8 (@List.length Lax808846.Ram.Instr (@AXr9520_9 lp p));
  let c13:Nat→ Nat:=c3 ((32:Nat));
  let c14:Nat→ Nat:=c3 ((36:Nat));
  let c15:@Polynomial Nat Nat.instSemiring:=
    Lax263307Proofs.NativeFlowBudget.widthPolynomial cfg.b
      (AXr9520_0 (@AXr9520_7 lp p))
      (@Lax263307Proofs.NativeSelectedNear.Program.width flow q)
      (@Lax263307Proofs.NativeSelectedNear.Program.time flow q)
      (@Lax263307Proofs.NativeSelectedNear.Program.output flow q)
      (@Lax263307Proofs.NativeSelectedNear.Program.code flow q);
  let c16:@Polynomial Nat Nat.instSemiring:=
    Lax263307Proofs.NativeFlowBudget.spacePolynomial cfg.b
      (AXr9520_0 (@AXr9520_7 lp p))
      (@Lax263307Proofs.NativeSelectedNear.Program.time flow q);
  let c17:@Polynomial Nat Nat.instSemiring:=
    Lax263307Proofs.NativeFlowBudget.timePolynomial cfg.b
      (AXr9520_0 (@AXr9520_7 lp p))
      (@Lax263307Proofs.NativeSelectedNear.Program.time flow q)
      (@Lax263307Proofs.NativeSelectedNear.Program.code flow q)
      (@Lax263307Proofs.NativeSelectedNear.Program.coeff flow q);
  let c18:Nat→ Nat:=c3 c;
  let c19:Nat:=c8 (@List.length Lax808846.Ram.Instr cfg.rounded);
  let c20:Nat→ Nat:=c3 ((144:Nat));
  let c21:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat→ Nat:=c7 c0;
    let c2_1:Nat:=c1 ((2:Nat));
    let c3_1:Nat:=c6 c2_1;
    let c4_1:Nat:=c2 c3_1 (c2 R R);
    let c5_1:Nat:=c3 c4_1 c0;
    let c6_1:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
    let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
    let c8:Nat:=
      c2
        (c2
          (c2
            (c3 ((100:Nat))
              (c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat))))
            ((10:Nat)))
          (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
        ((1:Nat));
    let c9_1:Nat:=c3 c6_1 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
    let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
    let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
    let c12_1:Nat→ Nat:=c3 c0;
    let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
    let c14_1:Nat:=c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R)) ((1:Nat));
    let c15_1:Nat:=
      c3 ((1000:Nat))
        (c1 ((5:Nat)));
    let c16_1:Nat:=
      c2
        (c2
          (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6_1)
            ((30:Nat)))
          c15_1)
        ((20:Nat));
    let c17_1:Nat:=c10_1 (@AXr9520_10 lp p);
    let c18_1:Nat→ Nat:=c2 (c9 (c2 (c2 c11_1 c15_1) ((1:Nat))));
    let c19_1:Nat:=
      c18
        (c7 (c2 (c2 (c2 R c14_1) R) ((1:Nat)))
          ((12:Nat)));
    c2
      (c2
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c2 (c2 R c11_1) c14_1)
                                (c2 (c3 ((200:Nat)) c0) c16_1))
                              (c3 (AXr9520_5 cfg)
                                (c1 ((4:Nat)))))
                            (c3 ((10:Nat)) c2_1))
                          (c2 (c2 c16_1 c17_1) ((10:Nat))))
                        (c2
                          (c2
                            (c2
                              (c2 (c2 (c2 (c18_1 c8) c16_1) c9_1)
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (c2 c9_1 ((1:Nat)))
                                  (@AXr9520_7 lp p)))
                              c17_1)
                            (AXr9520_11
                              (@AXr9520_9 lp p)))
                          ((100:Nat))))
                      (c2
                        (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                          ((10:Nat)))
                        ((4:Nat))))
                    c9_1)
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2 (c3 ((85:Nat)) c5_1)
                              (c3 ((87:Nat)) c4_1))
                            (c3 ((45:Nat)) c0))
                          ((54:Nat)))
                        (c2
                          (c2
                            (c2
                              (c3
                                (c2 (c3 ((12:Nat)) c9_1)
                                  ((39:Nat)))
                                c6_1)
                              c11)
                            ((29:Nat)))
                          (c2
                            (c3 (c2 c17_1 ((1:Nat)))
                              (c2 (c2 c12 (c13 c17_1)) ((104:Nat))))
                            ((18:Nat)))))
                      ((25:Nat)))
                    (c2
                      (c3
                        (c2 (c14 (c18_1 ((1:Nat))))
                          ((300:Nat)))
                        c0)
                      ((200:Nat)))))
                (@Polynomial.eval Nat Nat.instSemiring R c15))
              (@Polynomial.eval Nat Nat.instSemiring R c16))
            (@Polynomial.eval Nat Nat.instSemiring R c17))
          (c2
            (c2
              (c2
                (c18
                  (c7 (c2 (c2 (c9 R) c14_1) ((1:Nat)))
                    ((12:Nat))))
                (c3 (c5 R) R))
              (c6 R))
            ((10:Nat))))
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2 (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                      ((12:Nat)))
                    (c3 (c2 c19_1 ((1:Nat)))
                      (c2 (c2 c19 (c13 c19_1)) ((104:Nat)))))
                  ((18:Nat)))
                (c3 ((96:Nat)) (c3 R R)))
              (c20 R))
            ((78:Nat)))
          ((16:Nat))))
      ((100:Nat));
  let c22:Prop:=AXr9520_6 c21;
  let c23:Nat→ Nat:=c7 ((2:Nat));
  let c24:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c2_1:Nat:=c2 c1 (c2 R R);
    c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
      (c2
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c3 ((100:Nat))
                    (c7 (c2 (c8 R) ((2:Nat)))
                      ((3:Nat))))
                  ((10:Nat)))
                (c9
                  (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                    ((1:Nat)))))
              ((1:Nat)))
            c1)
          (c9 R))
        ((4:Nat)));
  let c25:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
    let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c3_1:Nat:=c2 c2_1 (c2 R R);
    c2
      (c2
        (c1
          (c3 c0
            (c2
              (c9
                (@Polynomial.eval Nat Nat.instSemiring
                  (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c3 ((100:Nat))
                                  (c7 (c2 (c8 R) ((2:Nat)))
                                    ((3:Nat))))
                                ((10:Nat)))
                              (c9 (c2 (c1 (c8 R)) ((1:Nat)))))
                            ((1:Nat)))
                          c2_1)
                        (c9 R))
                      ((4:Nat))))
                  (@AXr9520_7 lp p)))
              ((1:Nat)))))
        (c9 R))
      ((1:Nat));
  let c26:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c2_1:Nat:=c2 c1 (c2 R R);
    @Polynomial.eval Nat Nat.instSemiring
      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              c1)
            (c9 R))
          ((4:Nat))))
      (@AXr9520_7 lp p);
  let c27:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat:=c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
    c4 (c5 (c2 (c2 (c3 c1 c0) c1) c0));
  let c28:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (2:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.add ((2:Nat))
              (g R):=
    @AXr9520_12 fun (R:Nat) =>
      (2:Nat);
  let c29:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (3:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul ((3:Nat))
              (g R):=
    @AXr9520_13 fun (R:Nat) =>
      (3:Nat);
  let c30:Nat→ Nat:=fun (R:Nat) => c2 R ((1:Nat));
  let c31:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    c3 (c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R)) c0;
  let c32:Nat→ Nat:=fun (R:Nat) =>
    c2
      (c6
        (c7 (c2 R ((1:Nat)))
          ((2:Nat))))
      (c2 R R);
  let c33:Nat→ Nat:=fun (R:Nat) =>
    c6
      (c7 (c2 R ((1:Nat)))
        ((2:Nat)));
  let c34:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (6:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul ((6:Nat))
              (g R):=
    @AXr9520_13 fun (R:Nat) =>
      (6:Nat);
  let c35:Nat→ Nat:=fun (R:Nat) =>
    c7 (c2 R ((1:Nat)))
      ((2:Nat));
  let c36:
    ∀ (k:Nat),
      AXr9520_6 c30→
        AXr9520_6 fun (R:Nat) =>
          @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c30 R) k:=
    @AXr9520_14 c30;
  let c37:
    AXr9520_6 fun (R:Nat) =>
      Nat.add R ((1:Nat)):=
    @AXr9520_12 (fun (R:Nat) => R)
      (fun (R:Nat) => (1:Nat))
      AXr9520_4
      (AXr9520_3 ((1:Nat)));
  let c38:
    AXr9520_6 fun (R:Nat) =>
      @HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid))) (c30 R)
        ((2:Nat)):=
    c36 ((2:Nat)) c37;
  let c39:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((6:Nat))
        (c35 R):=
    @c34 c35
      (AXr9520_3 ((6:Nat))) c38;
  let c40:
    AXr9520_6 fun (R:Nat) =>
      Nat.add (c33 R) (c2 R R):=
    @AXr9520_12 c33 (fun (R:Nat) => c2 R R) c39
      (@AXr9520_12 (fun (R:Nat) => R) (fun (R:Nat) => R)
        AXr9520_4 AXr9520_4);
  let c41:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul (c32 R) (c30 R):=
    @AXr9520_13 c32 c30 c40 c37;
  let c42:
    AXr9520_6 fun (R:Nat) =>
      Nat.add ((2:Nat))
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat:=c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
        c5 (c2 (c2 (c3 c1 c0) c1) c0)):=
    @c28
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat:=c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
        c5 (c2 (c2 (c3 c1 c0) c1) c0))
      (AXr9520_3 ((2:Nat)))
      (@c29
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat:=c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
          c2 (c2 (c3 c1 c0) c1) c0)
        (AXr9520_3 ((3:Nat)))
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat:=c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
            c2 (c3 c1 c0) c1)
          c30 (@AXr9520_12 c31 c32 c41 c40) c37));
  let c43:Nat→ Nat:=fun (R:Nat) =>
    c2
      (c2
        (c2
          (c3 ((100:Nat))
            (c7 (c2 (c8 R) ((2:Nat)))
              ((3:Nat))))
          ((10:Nat)))
        (c9
          (c2
            (c2
              (c3 ((80:Nat))
                (c2 R ((1:Nat))))
              (c8 R))
            ((1:Nat)))))
      ((1:Nat));
  let c44:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((4:Nat)) R:=
    @AXr9520_13
      (fun (R:Nat) => (4:Nat)) (fun (R:Nat) => R)
      (AXr9520_3 ((4:Nat)))
      AXr9520_4;
  let c45:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (2:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul ((2:Nat))
              (g R):=
    @AXr9520_13 fun (R:Nat) =>
      (2:Nat);
  let c46:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          c3 ((80:Nat))
            (c2 R ((1:Nat))))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.add
              (c3 ((80:Nat))
                (c2 R ((1:Nat))))
              (g R):=
    @AXr9520_12 fun (R:Nat) =>
      c3 ((80:Nat))
        (c2 R ((1:Nat)));
  let c47:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((80:Nat))
        (c30 R):=
    @AXr9520_13
      (fun (R:Nat) => (80:Nat)) c30
      (AXr9520_3 ((80:Nat)))
      c37;
  let c48:
    AXr9520_6 fun (R:Nat) =>
      Nat.add
        (c2
          (c2
            (c3 ((100:Nat))
              (c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat))))
            ((10:Nat)))
          (c9
            (c2
              (c2
                (c3 ((80:Nat))
                  (c2 R ((1:Nat))))
                (c8 R))
              ((1:Nat)))))
        ((1:Nat)):=
    @AXr9520_12
      (fun (R:Nat) =>
        c2
          (c2
            (c3 ((100:Nat))
              (c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat))))
            ((10:Nat)))
          (c9
            (c2
              (c2
                (c3 ((80:Nat))
                  (c2 R ((1:Nat))))
                (c8 R))
              ((1:Nat)))))
      (fun (R:Nat) => (1:Nat))
      (@AXr9520_12
        (fun (R:Nat) =>
          c2
            (c3 ((100:Nat))
              (c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat))))
            ((10:Nat)))
        (fun (R:Nat) =>
          c9
            (c2
              (c2
                (c3 ((80:Nat))
                  (c2 R ((1:Nat))))
                (c8 R))
              ((1:Nat))))
        (@AXr9520_12
          (fun (R:Nat) =>
            c3 ((100:Nat))
              (c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat))))
          (fun (R:Nat) => (10:Nat))
          (@AXr9520_13
            (fun (R:Nat) => (100:Nat))
            (fun (R:Nat) =>
              c7 (c2 (c8 R) ((2:Nat)))
                ((3:Nat)))
            (AXr9520_3
              ((100:Nat)))
            (@AXr9520_14
              (fun (R:Nat) => c2 (c8 R) ((2:Nat)))
              ((3:Nat))
              (@AXr9520_12 c8
                (fun (R:Nat) => (2:Nat)) c44
                (AXr9520_3
                  ((2:Nat))))))
          (AXr9520_3
            ((10:Nat))))
        (@c45
          (fun (R:Nat) =>
            c2
              (c2
                (c3 ((80:Nat))
                  (c2 R ((1:Nat))))
                (c8 R))
              ((1:Nat)))
          (AXr9520_3 ((2:Nat)))
          (@AXr9520_12
            (fun (R:Nat) =>
              c2
                (c3 ((80:Nat))
                  (c2 R ((1:Nat))))
                (c8 R))
            (fun (R:Nat) => (1:Nat)) (@c46 c8 c47 c44)
            (AXr9520_3
              ((1:Nat))))))
      (AXr9520_3 ((1:Nat)));
  let c49:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((2:Nat)) R:=
    @c45 (fun (R:Nat) => R)
      (AXr9520_3 ((2:Nat)))
      AXr9520_4;
  let c50:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul (c27 R)
        (let c0:Nat:=c2 R ((1:Nat));
        c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              (c6 (c7 c0 ((2:Nat)))))
            (c9 R))
          ((4:Nat))):=
    @AXr9520_13 c27
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              (c6 (c7 c0 ((2:Nat)))))
            (c9 R))
          ((4:Nat)))
      c42
      (@AXr9520_12
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          c2
            (c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              (c6 (c7 c0 ((2:Nat)))))
            (c9 R))
        (fun (R:Nat) => (4:Nat))
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              (c6 (c7 c0 ((2:Nat)))))
          c9 (@AXr9520_12 c43 c33 c48 c39) c49)
        (AXr9520_3 ((4:Nat))));
  let c51:
    AXr9520_6 fun (R:Nat) =>
      @Polynomial.eval Nat Nat.instSemiring (c24 R) (@AXr9520_7 lp p):=
    @AXr9520_8 (@AXr9520_7 lp p) c24 c50;
  let c52:
    ∀ {g:Nat→ Nat},
      AXr9520_6 c30→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul (c30 R) (g R):=
    @AXr9520_13 c30;
  let c53:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c2_1:Nat:=c2 c1 (c2 R R);
    c2
      (c9
        (@Polynomial.eval Nat Nat.instSemiring
          (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c3 ((100:Nat))
                          (c7 (c2 (c8 R) ((2:Nat)))
                            ((3:Nat))))
                        ((10:Nat)))
                      (c9
                        (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                          ((1:Nat)))))
                    ((1:Nat)))
                  c1)
                (c9 R))
              ((4:Nat))))
          (@AXr9520_7 lp p)))
      ((1:Nat));
  let c54:
    AXr9520_6 fun (R:Nat) =>
      Nat.add
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c2_1:Nat:=c2 c1 (c2 R R);
        c9
          (@Polynomial.eval Nat Nat.instSemiring
            (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c3 ((100:Nat))
                            (c7 (c2 (c8 R) ((2:Nat)))
                              ((3:Nat))))
                          ((10:Nat)))
                        (c9
                          (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                            ((1:Nat)))))
                      ((1:Nat)))
                    c1)
                  (c9 R))
                ((4:Nat))))
            (@AXr9520_7 lp p)))
        ((1:Nat)):=
    @AXr9520_12
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c2_1:Nat:=c2 c1 (c2 R R);
        c9
          (@Polynomial.eval Nat Nat.instSemiring
            (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c3 ((100:Nat))
                            (c7 (c2 (c8 R) ((2:Nat)))
                              ((3:Nat))))
                          ((10:Nat)))
                        (c9
                          (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                            ((1:Nat)))))
                      ((1:Nat)))
                    c1)
                  (c9 R))
                ((4:Nat))))
            (@AXr9520_7 lp p)))
      (fun (R:Nat) => (1:Nat))
      (@c45 c26
        (AXr9520_3 ((2:Nat)))
        c51)
      (AXr9520_3 ((1:Nat)));
  let c55:
    AXr9520_6 fun (R:Nat) =>
      Nat.add
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c1
            (c3 c0
              (c2
                (c9
                  (@Polynomial.eval Nat Nat.instSemiring
                    (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c3 ((100:Nat))
                                    (c7 (c2 (c8 R) ((2:Nat)))
                                      ((3:Nat))))
                                  ((10:Nat)))
                                (c9 (c2 (c1 (c8 R)) ((1:Nat)))))
                              ((1:Nat)))
                            c2_1)
                          (c9 R))
                        ((4:Nat))))
                    (@AXr9520_7 lp p)))
                ((1:Nat)))))
          (c9 R))
        ((1:Nat)):=
    @AXr9520_12
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c1
            (c3 c0
              (c2
                (c9
                  (@Polynomial.eval Nat Nat.instSemiring
                    (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c3 ((100:Nat))
                                    (c7 (c2 (c8 R) ((2:Nat)))
                                      ((3:Nat))))
                                  ((10:Nat)))
                                (c9 (c2 (c1 (c8 R)) ((1:Nat)))))
                              ((1:Nat)))
                            c2_1)
                          (c9 R))
                        ((4:Nat))))
                    (@AXr9520_7 lp p)))
                ((1:Nat)))))
          (c9 R))
      (fun (R:Nat) => (1:Nat))
      (@AXr9520_12
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
          let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
          let c3_1:Nat:=c2 c2_1 (c2 R R);
          c1
            (c3 c0
              (c2
                (c9
                  (@Polynomial.eval Nat Nat.instSemiring
                    (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c3 ((100:Nat))
                                    (c7 (c2 (c8 R) ((2:Nat)))
                                      ((3:Nat))))
                                  ((10:Nat)))
                                (c9 (c2 (c1 (c8 R)) ((1:Nat)))))
                              ((1:Nat)))
                            c2_1)
                          (c9 R))
                        ((4:Nat))))
                    (@AXr9520_7 lp p)))
                ((1:Nat)))))
        c9
        (@c46
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat:=c6 (c7 c0 ((2:Nat)));
            let c2_1:Nat:=c2 c1 (c2 R R);
            c3 c0
              (c2
                (c9
                  (@Polynomial.eval Nat Nat.instSemiring
                    (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c3 ((100:Nat))
                                    (c7 (c2 (c8 R) ((2:Nat)))
                                      ((3:Nat))))
                                  ((10:Nat)))
                                (c9
                                  (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                    ((1:Nat)))))
                              ((1:Nat)))
                            c1)
                          (c9 R))
                        ((4:Nat))))
                    (@AXr9520_7 lp p)))
                ((1:Nat))))
          c47 (@c52 c53 c37 c54))
        c49)
      (AXr9520_3 ((1:Nat)));
  let c56:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat→ Nat:=c7 c0;
    let c2_1:Nat:=c6 (c1 ((2:Nat)));
    let c3_1:Nat:=c2 c2_1 (c2 R R);
    c2
      (c2
        (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0))))
          ((30:Nat)))
        (c3 ((1000:Nat))
          (c1 ((5:Nat)))))
      ((20:Nat));
  let c57:Nat→ Nat:=fun (R:Nat) =>
    c3 ((1000:Nat))
      (c7 (c2 R ((1:Nat)))
        ((5:Nat)));
  let c58:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (5:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul ((5:Nat))
              (g R):=
    @AXr9520_13 fun (R:Nat) =>
      (5:Nat);
  let c59:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((1000:Nat))
        (c7 (c2 R ((1:Nat)))
          ((5:Nat))):=
    @AXr9520_13
      (fun (R:Nat) => (1000:Nat))
      (fun (R:Nat) =>
        c7 (c2 R ((1:Nat)))
          ((5:Nat)))
      (AXr9520_3
        ((1000:Nat)))
      (c36 ((5:Nat)) c37);
  let c60:
    AXr9520_6 fun (R:Nat) =>
      Nat.add
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c7 c0;
        let c2_1:Nat:=c6 (c1 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0))))
            ((30:Nat)))
          (c3 ((1000:Nat))
            (c1 ((5:Nat)))))
        ((20:Nat)):=
    @AXr9520_12
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c7 c0;
        let c2_1:Nat:=c6 (c1 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0))))
            ((30:Nat)))
          (c3 ((1000:Nat))
            (c1 ((5:Nat)))))
      (fun (R:Nat) => (20:Nat))
      (@AXr9520_12
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat:=c6 (c7 c0 ((2:Nat)));
          let c2_1:Nat:=c2 c1 (c2 R R);
          c2 (c2 (c2 (c2 (c5 (c3 c1 R)) (c10 c1)) (c10 R)) (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0))))
            ((30:Nat)))
        c57
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat:=c6 (c7 c0 ((2:Nat)));
            let c2_1:Nat:=c2 c1 (c2 R R);
            c2 (c2 (c2 (c5 (c3 c1 R)) (c10 c1)) (c10 R)) (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0))))
          (fun (R:Nat) => (30:Nat))
          (@AXr9520_12
            (fun (R:Nat) =>
              let c0:Nat:=
                c6
                  (c7 (c2 R ((1:Nat)))
                    ((2:Nat)));
              c2 (c2 (c5 (c3 c0 R)) (c10 c0)) (c10 R))
            c27
            (@AXr9520_12
              (fun (R:Nat) =>
                let c0:Nat:=
                  c6
                    (c7 (c2 R ((1:Nat)))
                      ((2:Nat)));
                c2 (c5 (c3 c0 R)) (c10 c0))
              c10
              (@AXr9520_12
                (fun (R:Nat) =>
                  c5
                    (c3
                      (c6
                        (c7 (c2 R ((1:Nat)))
                          ((2:Nat))))
                      R))
                (fun (R:Nat) =>
                  c10
                    (c6
                      (c7 (c2 R ((1:Nat)))
                        ((2:Nat)))))
                (@c29
                  (fun (R:Nat) =>
                    c3
                      (c6
                        (c7 (c2 R ((1:Nat)))
                          ((2:Nat))))
                      R)
                  (AXr9520_3
                    ((3:Nat)))
                  (@AXr9520_13 c33 (fun (R:Nat) => R) c39
                    AXr9520_4))
                (@c58 c33
                  (AXr9520_3
                    ((5:Nat)))
                  c39))
              (@c58 (fun (R:Nat) => R)
                (AXr9520_3
                  ((5:Nat)))
                AXr9520_4))
            c42)
          (AXr9520_3
            ((30:Nat))))
        c59)
      (AXr9520_3 ((20:Nat)));
  let c61:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c2_1:Nat:=c2 c1 (c2 R R);
    @Polynomial.eval Nat Nat.instSemiring
      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
        (c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9
                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                      ((1:Nat)))))
                ((1:Nat)))
              c1)
            (c9 R))
          ((4:Nat))))
      (@AXr9520_10 lp p);
  let c62:
    AXr9520_6 fun (R:Nat) =>
      @Polynomial.eval Nat Nat.instSemiring (c24 R) (@AXr9520_10 lp p):=
    @AXr9520_8 (@AXr9520_10 lp p) c24 c50;
  let c63:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c7 c0;
          let c2_1:Nat:=c6 (c1 ((2:Nat)));
          let c3_1:Nat:=c2 c2_1 (c2 R R);
          c9
            (c2
              (c2
                (@Polynomial.eval Nat Nat.instSemiring
                  (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c3 ((100:Nat))
                                  (c7 (c2 (c8 R) ((2:Nat)))
                                    ((3:Nat))))
                                ((10:Nat)))
                              (c9
                                (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                  ((1:Nat)))))
                            ((1:Nat)))
                          c2_1)
                        (c9 R))
                      ((4:Nat))))
                  (@AXr9520_7 lp p))
                (c3 ((1000:Nat))
                  (c1 ((5:Nat)))))
              ((1:Nat))))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.add
              (let c0:Nat:=c2 R ((1:Nat));
              let c1:Nat→ Nat:=c7 c0;
              let c2_1:Nat:=c6 (c1 ((2:Nat)));
              let c3_1:Nat:=c2 c2_1 (c2 R R);
              c9
                (c2
                  (c2
                    (@Polynomial.eval Nat Nat.instSemiring
                      (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c3 ((100:Nat))
                                      (c7 (c2 (c8 R) ((2:Nat)))
                                        ((3:Nat))))
                                    ((10:Nat)))
                                  (c9
                                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                      ((1:Nat)))))
                                ((1:Nat)))
                              c2_1)
                            (c9 R))
                          ((4:Nat))))
                      (@AXr9520_7 lp p))
                    (c3 ((1000:Nat))
                      (c1 ((5:Nat)))))
                  ((1:Nat))))
              (g R):=
    @AXr9520_12 fun (R:Nat) =>
      let c0:Nat:=c2 R ((1:Nat));
      let c1:Nat→ Nat:=c7 c0;
      let c2_1:Nat:=c6 (c1 ((2:Nat)));
      let c3_1:Nat:=c2 c2_1 (c2 R R);
      c9
        (c2
          (c2
            (@Polynomial.eval Nat Nat.instSemiring
              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c3 ((100:Nat))
                              (c7 (c2 (c8 R) ((2:Nat)))
                                ((3:Nat))))
                            ((10:Nat)))
                          (c9
                            (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                              ((1:Nat)))))
                        ((1:Nat)))
                      c2_1)
                    (c9 R))
                  ((4:Nat))))
              (@AXr9520_7 lp p))
            (c3 ((1000:Nat))
              (c1 ((5:Nat)))))
          ((1:Nat)));
  let c64:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((2:Nat))
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c7 c0;
        let c2_1:Nat:=c6 (c1 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c2
            (@Polynomial.eval Nat Nat.instSemiring
              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c3 ((100:Nat))
                              (c7 (c2 (c8 R) ((2:Nat)))
                                ((3:Nat))))
                            ((10:Nat)))
                          (c9
                            (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                              ((1:Nat)))))
                        ((1:Nat)))
                      c2_1)
                    (c9 R))
                  ((4:Nat))))
              (@AXr9520_7 lp p))
            (c3 ((1000:Nat))
              (c1 ((5:Nat)))))
          ((1:Nat))):=
    @c45
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c7 c0;
        let c2_1:Nat:=c6 (c1 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c2
          (c2
            (@Polynomial.eval Nat Nat.instSemiring
              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c3 ((100:Nat))
                              (c7 (c2 (c8 R) ((2:Nat)))
                                ((3:Nat))))
                            ((10:Nat)))
                          (c9
                            (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                              ((1:Nat)))))
                        ((1:Nat)))
                      c2_1)
                    (c9 R))
                  ((4:Nat))))
              (@AXr9520_7 lp p))
            (c3 ((1000:Nat))
              (c1 ((5:Nat)))))
          ((1:Nat)))
      (AXr9520_3 ((2:Nat)))
      (@AXr9520_12
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c7 c0;
          let c2_1:Nat:=c6 (c1 ((2:Nat)));
          let c3_1:Nat:=c2 c2_1 (c2 R R);
          c2
            (@Polynomial.eval Nat Nat.instSemiring
              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c3 ((100:Nat))
                              (c7 (c2 (c8 R) ((2:Nat)))
                                ((3:Nat))))
                            ((10:Nat)))
                          (c9
                            (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                              ((1:Nat)))))
                        ((1:Nat)))
                      c2_1)
                    (c9 R))
                  ((4:Nat))))
              (@AXr9520_7 lp p))
            (c3 ((1000:Nat))
              (c1 ((5:Nat)))))
        (fun (R:Nat) => (1:Nat))
        (@AXr9520_12 c26 c57 c51 c59)
        (AXr9520_3 ((1:Nat))));
  let c65:
    ∀ {g:Nat→ Nat},
      (AXr9520_6 fun (R:Nat) =>
          (32:Nat))→
        AXr9520_6 g→
          AXr9520_6 fun (R:Nat) =>
            Nat.mul
              ((32:Nat)) (g R):=
    @AXr9520_13 fun (R:Nat) =>
      (32:Nat);
  let c66:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul ((6:Nat)) R:=
    @c34 (fun (R:Nat) => R)
      (AXr9520_3 ((6:Nat)))
      AXr9520_4;
  let c67:Nat→ Nat:=fun (R:Nat) => c3 R R;
  let c68:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul R R:=
    @AXr9520_13 (fun (R:Nat) => R) (fun (R:Nat) => R)
      AXr9520_4 AXr9520_4;
  let c69:Nat→ Nat:=fun (R:Nat) =>
    let c0:Nat:=c2 R ((1:Nat));
    let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
    let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
    let c3_1:Nat:=c2 c2_1 (c2 R R);
    c18
      (c7
        (c2
          (c2
            (c2 R
              (c2
                (c2
                  (c1
                    (c3 c0
                      (c2
                        (c9
                          (@Polynomial.eval Nat Nat.instSemiring
                            (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c3 ((100:Nat))
                                            (c7 (c2 (c8 R) ((2:Nat)))
                                              ((3:Nat))))
                                          ((10:Nat)))
                                        (c9 (c2 (c1 (c8 R)) ((1:Nat)))))
                                      ((1:Nat)))
                                    c2_1)
                                  (c9 R))
                                ((4:Nat))))
                            (@AXr9520_7 lp p)))
                        ((1:Nat)))))
                  (c9 R))
                ((1:Nat))))
            R)
          ((1:Nat)))
        ((12:Nat)));
  let c70:
    AXr9520_6 fun (R:Nat) =>
      Nat.mul c
        (let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c7
          (c2
            (c2
              (c2 R
                (c2
                  (c2
                    (c1
                      (c3 c0
                        (c2
                          (c9
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c1 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c2_1)
                                    (c9 R))
                                  ((4:Nat))))
                              (@AXr9520_7 lp p)))
                          ((1:Nat)))))
                    (c9 R))
                  ((1:Nat))))
              R)
            ((1:Nat)))
          ((12:Nat))):=
    @AXr9520_13 (fun (R:Nat) => c)
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
        let c3_1:Nat:=c2 c2_1 (c2 R R);
        c7
          (c2
            (c2
              (c2 R
                (c2
                  (c2
                    (c1
                      (c3 c0
                        (c2
                          (c9
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c1 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c2_1)
                                    (c9 R))
                                  ((4:Nat))))
                              (@AXr9520_7 lp p)))
                          ((1:Nat)))))
                    (c9 R))
                  ((1:Nat))))
              R)
            ((1:Nat)))
          ((12:Nat)))
      (AXr9520_3 c)
      (@AXr9520_14
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
          let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
          let c3_1:Nat:=c2 c2_1 (c2 R R);
          c2
            (c2
              (c2 R
                (c2
                  (c2
                    (c1
                      (c3 c0
                        (c2
                          (c9
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c1 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c2_1)
                                    (c9 R))
                                  ((4:Nat))))
                              (@AXr9520_7 lp p)))
                          ((1:Nat)))))
                    (c9 R))
                  ((1:Nat))))
              R)
            ((1:Nat)))
        ((12:Nat))
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
            let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
            let c3_1:Nat:=c2 c2_1 (c2 R R);
            c2
              (c2 R
                (c2
                  (c2
                    (c1
                      (c3 c0
                        (c2
                          (c9
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c1 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c2_1)
                                    (c9 R))
                                  ((4:Nat))))
                              (@AXr9520_7 lp p)))
                          ((1:Nat)))))
                    (c9 R))
                  ((1:Nat))))
              R)
          (fun (R:Nat) => (1:Nat))
          (@AXr9520_12
            (fun (R:Nat) =>
              let c0:Nat:=c2 R ((1:Nat));
              let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
              let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
              let c3_1:Nat:=c2 c2_1 (c2 R R);
              c2 R
                (c2
                  (c2
                    (c1
                      (c3 c0
                        (c2
                          (c9
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c1 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c2_1)
                                    (c9 R))
                                  ((4:Nat))))
                              (@AXr9520_7 lp p)))
                          ((1:Nat)))))
                    (c9 R))
                  ((1:Nat))))
            (fun (R:Nat) => R)
            (@AXr9520_12 (fun (R:Nat) => R) c25
              AXr9520_4 c55)
            AXr9520_4)
          (AXr9520_3
            ((1:Nat)))));
  @Eq.mpr c1 c22
    (@id (@Eq Prop c1 c22)
      (@congrArg (Nat→ Nat) Prop c0 c21 AXr9520_6
        (@funext Nat (fun (x:Nat) => Nat)
          (fun (x:Nat) =>
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2 (c2 x (@AXr9520_2 lp p x))
                                          (AXr9520_1
                                            (@AXr9520_7 lp p) x))
                                        (Lax263307Proofs.NativeProjectionResources.wordHeight x))
                                      (Lax263307Proofs.NativeEntryResources.amount cfg x))
                                    (Lax263307Proofs.NativeNearResources.space x))
                                  (Lax263307Proofs.NativeProjectionResources.space x
                                    (@Lax263307Proofs.NativeSelectedLP.oracleTime lp p x)))
                                (@Lax263307Proofs.NativeSelectedLP.wordHeight lp p x))
                              (c2
                                (Lax263307Proofs.NativeCutResources.wordExponent x
                                  (c2 (c9 (@AXr9520_2 lp p x))
                                    ((1:Nat))))
                                ((4:Nat))))
                            (Lax263307Proofs.NativeSelectedLP.queryBound x))
                          (@Lax263307Proofs.NativeSelectedLP.callCost lp p x))
                        (@Polynomial.eval Nat Nat.instSemiring x c15))
                      (@Polynomial.eval Nat Nat.instSemiring x c16))
                    (@Polynomial.eval Nat Nat.instSemiring x c17))
                  (Lax263307Proofs.NativeRoundedResources.space c x
                    (AXr9520_1
                      (@AXr9520_7 lp p) x)))
                (@Lax263307Proofs.NativeSelectedRounds.roundCost lp cfg p c x))
              ((100:Nat)))
          c21 fun (R:Nat) =>
          let c0:Nat:=
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2 (c2 R (@AXr9520_2 lp p R))
                              (AXr9520_1
                                (@AXr9520_7 lp p) R))
                            (Lax263307Proofs.NativeProjectionResources.wordHeight R))
                          (Lax263307Proofs.NativeEntryResources.amount cfg R))
                        (Lax263307Proofs.NativeNearResources.space R))
                      (Lax263307Proofs.NativeProjectionResources.space R
                        (@Lax263307Proofs.NativeSelectedLP.oracleTime lp p R)))
                    (@Lax263307Proofs.NativeSelectedLP.wordHeight lp p R))
                  (c2
                    (Lax263307Proofs.NativeCutResources.wordExponent R
                      (c2 (c9 (@AXr9520_2 lp p R))
                        ((1:Nat))))
                    ((4:Nat))))
                (Lax263307Proofs.NativeSelectedLP.queryBound R))
              (@Lax263307Proofs.NativeSelectedLP.callCost lp p R);
          let c1:Nat→ Nat:=c2 c0;
          let c2_1:Nat:=c1 (@Polynomial.eval Nat Nat.instSemiring R c15);
          let c3_1:Nat→ Nat:=c2 c2_1;
          let c4_1:Nat:=c3_1 (@Polynomial.eval Nat Nat.instSemiring R c16);
          let c5_1:Nat→ Nat:=c2 c4_1;
          let c6_1:Nat:=c5_1 (@Polynomial.eval Nat Nat.instSemiring R c17);
          let c7_1:Nat→ Nat:=c2 c6_1;
          let c8_1:Nat:=
            c7_1
              (Lax263307Proofs.NativeRoundedResources.space c R
                (AXr9520_1
                  (@AXr9520_7 lp p) R));
          let c9_1:Nat→ Nat:=c2 c8_1;
          let c10_1:Nat:=c9_1 (@Lax263307Proofs.NativeSelectedRounds.roundCost lp cfg p c R);
          let c11_1:Nat:=c2 R ((1:Nat));
          let c12_1:Nat→ Nat:=c7 c11_1;
          let c13_1:Nat:=c12_1 ((2:Nat));
          let c14_1:Nat:=c6 c13_1;
          let c15_1:Nat:=c2 c14_1 (c2 R R);
          let c16_1:Nat:=c3 c15_1 c11_1;
          let c17_1:Nat:=c4 (c5 (c2 (c2 c16_1 c15_1) c11_1));
          let c18_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c11_1);
          let c19_1:Nat:=
            c2
              (c2
                (c2
                  (c3 ((100:Nat))
                    (c7 (c2 (c8 R) ((2:Nat)))
                      ((3:Nat))))
                  ((10:Nat)))
                (c9 (c2 (c18_1 (c8 R)) ((1:Nat)))))
              ((1:Nat));
          let c20_1:Nat:=
            c3 c17_1 (c2 (c2 (c2 c19_1 c14_1) (c9 R)) ((4:Nat)));
          let c21:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c20_1;
          let c22:Nat:=c21 (@AXr9520_7 lp p);
          let c23_1:Nat→ Nat:=c3 c11_1;
          let c24:Nat:=c2 (c9 c22) ((1:Nat));
          let c25:Nat:=c2 (c2 (c18_1 (c23_1 c24)) (c9 R)) ((1:Nat));
          let c26:Nat:=
            c3 ((1000:Nat))
              (c12_1 ((5:Nat)));
          let c27:Nat:=
            c2
              (c2
                (c2 (c2 (c2 (c2 (c5 (c3 c14_1 R)) (c10 c14_1)) (c10 R)) c17_1)
                  ((30:Nat)))
                c26)
              ((20:Nat));
          let c28:Nat:=c21 (@AXr9520_10 lp p);
          let c29:Nat:=c2 (c2 c22 c26) ((1:Nat));
          let c30:Nat:=c9 c29;
          let c31:Nat→ Nat:=c2 c30;
          let c32:Nat→ Nat:=
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2 (c2 (c2 R c22) c25)
                            (c2 (c3 ((200:Nat)) c11_1) c27))
                          (c3 (AXr9520_5 cfg)
                            (c12_1 ((4:Nat)))))
                        (c3 ((10:Nat)) c13_1))
                      (c2 (c2 c27 c28) ((10:Nat))))
                    (c2
                      (c2
                        (c2
                          (c2 (c2 (c2 (c31 c19_1) c27) c20_1)
                            (@Polynomial.eval Nat Nat.instSemiring
                              (c2 c20_1 ((1:Nat)))
                              (@AXr9520_7 lp p)))
                          c28)
                        (AXr9520_11
                          (@AXr9520_9 lp p)))
                      ((100:Nat))))
                  (c2
                    (c2 (c23_1 (c2 c24 ((1:Nat))))
                      ((10:Nat)))
                    ((4:Nat))))
                c20_1);
          let c33:Nat→ Nat:=
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2 (c3 ((85:Nat)) c16_1)
                        (c3 ((87:Nat)) c15_1))
                      (c3 ((45:Nat)) c11_1))
                    ((54:Nat)))
                  (c2
                    (c2
                      (c2
                        (c3
                          (c2 (c3 ((12:Nat)) c20_1)
                            ((39:Nat)))
                          c17_1)
                        c11)
                      ((29:Nat)))
                    (c2
                      (c3 (c2 c28 ((1:Nat)))
                        (c2 (c2 c12 (c13 c28)) ((104:Nat))))
                      ((18:Nat)))))
                ((25:Nat)));
          let c34:Nat:=c31 ((1:Nat));
          let c35:Nat:=c14 c34;
          let c36:Nat→ Nat:=c2 c35;
          let c37:Nat:=c36 ((300:Nat));
          let c38:Nat→ Nat:=c3 c37;
          let c39:Nat:=c38 c11_1;
          let c40:Nat→ Nat:=c2 c39;
          let c41:Nat:=c40 ((200:Nat));
          let c42:Nat:=c33 c41;
          let c43:Nat:=c32 c42;
          let c44:Nat→ Nat:=c2 c43;
          let c45:Nat:=c44 (@Polynomial.eval Nat Nat.instSemiring R c15);
          let c46:Nat→ Nat:=c2 c45;
          let c47:Nat:=c46 (@Polynomial.eval Nat Nat.instSemiring R c16);
          let c48:Nat→ Nat:=c2 c47;
          let c49:Nat:=c48 (@Polynomial.eval Nat Nat.instSemiring R c17);
          let c50:Nat→ Nat:=c2 c49;
          let c51:Nat:=
            c2
              (c2
                (c2
                  (c18
                    (c7 (c2 (c2 (c9 R) c25) ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
                (c6 R))
              ((10:Nat));
          let c52:Nat:=c50 c51;
          let c53:Nat→ Nat:=c2 c52;
          let c54:Nat:=
            c18
              (c7 (c2 (c2 (c2 R c25) R) ((1:Nat)))
                ((12:Nat)));
          let c55:Nat:=
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c3 ((16:Nat))
                            (c2 (c4 (c5 (c3 R R))) (c6 R)))
                          ((12:Nat)))
                        (c3 (c2 c54 ((1:Nat)))
                          (c2 (c2 c19 (c13 c54)) ((104:Nat)))))
                      ((18:Nat)))
                    (c3 ((96:Nat)) (c3 R R)))
                  (c20 R))
                ((78:Nat)))
              ((16:Nat));
          let c56:Nat:=c53 c55;
          let c57:Nat:=
            c7 (c23 (@Lax263307Proofs.NativeSelectedLP.invocationHeight lp p R))
              ((2:Nat));
          let c58:Nat:=c57.size;
          let c59:Nat:=c14 c58;
          let c60:Nat→ Nat:=c2 c59;
          let c61:Nat:=c60 ((300:Nat));
          let c62:Nat→ Nat:=c3 c61;
          let c63:Nat:=c62 c11_1;
          let c64:Nat:=c23 c30;
          @congrFun' Nat Nat (c2 c10_1) (c2 c56)
            (@congrArg Nat (Nat→ Nat) c10_1 c56 c2
              (@congrFun' Nat Nat c9_1 c53
                (@congrArg Nat (Nat→ Nat) c8_1 c52 c2
                  (@congrFun' Nat Nat c7_1 c50
                    (@congrArg Nat (Nat→ Nat) c6_1 c49 c2
                      (@congrFun' Nat Nat c5_1 c48
                        (@congrArg Nat (Nat→ Nat) c4_1 c47 c2
                          (@congrFun' Nat Nat c3_1 c46
                            (@congrArg Nat (Nat→ Nat) c2_1 c45 c2
                              (@congrFun' Nat Nat c1 c44
                                (@congrArg Nat (Nat→ Nat) c0 c43 c2
                                  (@congrArg Nat Nat (@Lax263307Proofs.NativeSelectedLP.callCost lp p R) c42 c32
                                    (@congrArg Nat Nat
                                      (Lax263307Proofs.NativeProjectionResult.cost
                                        (c23 (@Lax263307Proofs.NativeSelectedLP.invocationHeight lp p R)) R)
                                      c41 c33
                                      (@congrFun' Nat Nat (c2 c63) c40
                                        (@congrArg Nat (Nat→ Nat) c63 c39 c2
                                          (@congrFun' Nat Nat c62 c38
                                            (@congrArg Nat (Nat→ Nat) c61 c37 c3
                                              (@congrFun' Nat Nat c60 c36
                                                (@congrArg Nat (Nat→ Nat) c59 c35 c2
                                                  (@congrArg Nat Nat c58 c34 c14
                                                    (@Eq.trans Nat c58 c64.size c34
                                                      (@congrArg Nat Nat c57 c64 Nat.size
                                                        (Lax263307Proofs.NativeQuadraticResources.square_power c29))
                                                      (@Nat.size_pow c30))))
                                                ((300:Nat))))
                                            c11_1))
                                        ((200:Nat))))))
                                (@Polynomial.eval Nat Nat.instSemiring R c15)))
                            (@Polynomial.eval Nat Nat.instSemiring R c16)))
                        (@Polynomial.eval Nat Nat.instSemiring R c17)))
                    c51))
                c55))
            ((100:Nat)))))
    (@AXr9520_12
      (fun (R:Nat) =>
        let c0:Nat:=c2 R ((1:Nat));
        let c1:Nat→ Nat:=c7 c0;
        let c2_1:Nat:=c1 ((2:Nat));
        let c3_1:Nat:=c6 c2_1;
        let c4_1:Nat:=c2 c3_1 (c2 R R);
        let c5_1:Nat:=c3 c4_1 c0;
        let c6_1:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
        let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
        let c8:Nat:=
          c2
            (c2
              (c2
                (c3 ((100:Nat))
                  (c7 (c2 (c8 R) ((2:Nat)))
                    ((3:Nat))))
                ((10:Nat)))
              (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
            ((1:Nat));
        let c9_1:Nat:=
          c3 c6_1 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
        let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
        let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
        let c12_1:Nat→ Nat:=c3 c0;
        let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
        let c14_1:Nat:=
          c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R)) ((1:Nat));
        let c15_1:Nat:=
          c3 ((1000:Nat))
            (c1 ((5:Nat)));
        let c16_1:Nat:=
          c2
            (c2
              (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6_1)
                ((30:Nat)))
              c15_1)
            ((20:Nat));
        let c17_1:Nat:=c10_1 (@AXr9520_10 lp p);
        let c18_1:Nat→ Nat:=
          c2 (c9 (c2 (c2 c11_1 c15_1) ((1:Nat))));
        let c19_1:Nat:=
          c18
            (c7 (c2 (c2 (c2 R c14_1) R) ((1:Nat)))
              ((12:Nat)));
        c2
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 R c11_1) c14_1)
                                  (c2 (c3 ((200:Nat)) c0) c16_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c16_1 c17_1) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c18_1 c8) c16_1) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c17_1)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6_1)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c17_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c17_1)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c18_1 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                  (@Polynomial.eval Nat Nat.instSemiring R c15))
                (@Polynomial.eval Nat Nat.instSemiring R c16))
              (@Polynomial.eval Nat Nat.instSemiring R c17))
            (c2
              (c2
                (c2
                  (c18
                    (c7 (c2 (c2 (c9 R) c14_1) ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
                (c6 R))
              ((10:Nat))))
          (c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c19_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c19_1)) ((104:Nat)))))
                    ((18:Nat)))
                  (c3 ((96:Nat)) (c3 R R)))
                (c20 R))
              ((78:Nat)))
            ((16:Nat))))
      (fun (R:Nat) => (100:Nat))
      (@AXr9520_12
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c7 c0;
          let c2_1:Nat:=c1 ((2:Nat));
          let c3_1:Nat:=c6 c2_1;
          let c4_1:Nat:=c2 c3_1 (c2 R R);
          let c5_1:Nat:=c3 c4_1 c0;
          let c6_1:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
          let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
          let c8:Nat:=
            c2
              (c2
                (c2
                  (c3 ((100:Nat))
                    (c7 (c2 (c8 R) ((2:Nat)))
                      ((3:Nat))))
                  ((10:Nat)))
                (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
              ((1:Nat));
          let c9_1:Nat:=
            c3 c6_1 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
          let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
          let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
          let c12_1:Nat→ Nat:=c3 c0;
          let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
          let c14_1:Nat:=
            c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R)) ((1:Nat));
          let c15_1:Nat:=
            c3 ((1000:Nat))
              (c1 ((5:Nat)));
          let c16_1:Nat:=
            c2
              (c2
                (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6_1)
                  ((30:Nat)))
                c15_1)
              ((20:Nat));
          let c17_1:Nat:=c10_1 (@AXr9520_10 lp p);
          let c18_1:Nat→ Nat:=
            c2 (c9 (c2 (c2 c11_1 c15_1) ((1:Nat))));
          c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 R c11_1) c14_1)
                                  (c2 (c3 ((200:Nat)) c0) c16_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c16_1 c17_1) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c18_1 c8) c16_1) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c17_1)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6_1)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c17_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c17_1)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c18_1 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                  (@Polynomial.eval Nat Nat.instSemiring R c15))
                (@Polynomial.eval Nat Nat.instSemiring R c16))
              (@Polynomial.eval Nat Nat.instSemiring R c17))
            (c2
              (c2
                (c2
                  (c18
                    (c7 (c2 (c2 (c9 R) c14_1) ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
                (c6 R))
              ((10:Nat))))
        (fun (R:Nat) =>
          let c0:Nat:=c2 R ((1:Nat));
          let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
          let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
          let c3_1:Nat:=c2 c2_1 (c2 R R);
          let c4_1:Nat:=
            c18
              (c7
                (c2
                  (c2
                    (c2 R
                      (c2
                        (c2
                          (c1
                            (c3 c0
                              (c2
                                (c9
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c3 ((100:Nat))
                                                    (c7
                                                      (c2 (c8 R)
                                                        ((2:Nat)))
                                                      ((3:Nat))))
                                                  ((10:Nat)))
                                                (c9
                                                  (c2 (c1 (c8 R))
                                                    ((1:Nat)))))
                                              ((1:Nat)))
                                            c2_1)
                                          (c9 R))
                                        ((4:Nat))))
                                    (@AXr9520_7 lp p)))
                                ((1:Nat)))))
                          (c9 R))
                        ((1:Nat))))
                    R)
                  ((1:Nat)))
                ((12:Nat)));
          c2
            (c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                    ((18:Nat)))
                  (c3 ((96:Nat)) (c3 R R)))
                (c20 R))
              ((78:Nat)))
            ((16:Nat)))
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat→ Nat:=c7 c0;
            let c2_1:Nat:=c1 ((2:Nat));
            let c3_1:Nat:=c6 c2_1;
            let c4_1:Nat:=c2 c3_1 (c2 R R);
            let c5_1:Nat:=c3 c4_1 c0;
            let c6:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
            let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
            let c8:Nat:=
              c2
                (c2
                  (c2
                    (c3 ((100:Nat))
                      (c7 (c2 (c8 R) ((2:Nat)))
                        ((3:Nat))))
                    ((10:Nat)))
                  (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
                ((1:Nat));
            let c9_1:Nat:=
              c3 c6 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
            let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
            let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
            let c12_1:Nat→ Nat:=c3 c0;
            let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
            let c14_1:Nat:=
              c3 ((1000:Nat))
                (c1 ((5:Nat)));
            let c15_1:Nat:=
              c2
                (c2
                  (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6)
                    ((30:Nat)))
                  c14_1)
                ((20:Nat));
            let c16_1:Nat:=c10_1 (@AXr9520_10 lp p);
            let c17_1:Nat→ Nat:=
              c2 (c9 (c2 (c2 c11_1 c14_1) ((1:Nat))));
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c11_1)
                                    (c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c15_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c15_1 c16_1) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c17_1 c8) c15_1) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c16_1)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c16_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c16_1)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c17_1 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                  (@Polynomial.eval Nat Nat.instSemiring R c15))
                (@Polynomial.eval Nat Nat.instSemiring R c16))
              (@Polynomial.eval Nat Nat.instSemiring R c17))
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
            let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
            let c3_1:Nat:=c2 c2_1 (c2 R R);
            c2
              (c2
                (c2
                  (c18
                    (c7
                      (c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
                (c6 R))
              ((10:Nat)))
          (@AXr9520_12
            (fun (R:Nat) =>
              let c0:Nat:=c2 R ((1:Nat));
              let c1:Nat→ Nat:=c7 c0;
              let c2_1:Nat:=c1 ((2:Nat));
              let c3_1:Nat:=c6 c2_1;
              let c4_1:Nat:=c2 c3_1 (c2 R R);
              let c5_1:Nat:=c3 c4_1 c0;
              let c6:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
              let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
              let c8:Nat:=
                c2
                  (c2
                    (c2
                      (c3 ((100:Nat))
                        (c7 (c2 (c8 R) ((2:Nat)))
                          ((3:Nat))))
                      ((10:Nat)))
                    (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
                  ((1:Nat));
              let c9_1:Nat:=
                c3 c6 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
              let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
              let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
              let c12_1:Nat→ Nat:=c3 c0;
              let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
              let c14_1:Nat:=
                c3 ((1000:Nat))
                  (c1 ((5:Nat)));
              let c15_1:Nat:=
                c2
                  (c2
                    (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6)
                      ((30:Nat)))
                    c14_1)
                  ((20:Nat));
              let c16_1:Nat:=c10_1 (@AXr9520_10 lp p);
              let c17:Nat→ Nat:=
                c2 (c9 (c2 (c2 c11_1 c14_1) ((1:Nat))));
              c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c11_1)
                                    (c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c15_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c15_1 c16_1) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c17 c8) c15_1) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c16_1)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c16_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c16_1)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c17 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                  (@Polynomial.eval Nat Nat.instSemiring R c15))
                (@Polynomial.eval Nat Nat.instSemiring R c16))
            (fun (R:Nat) => @Polynomial.eval Nat Nat.instSemiring R c17)
            (@AXr9520_12
              (fun (R:Nat) =>
                let c0:Nat:=c2 R ((1:Nat));
                let c1:Nat→ Nat:=c7 c0;
                let c2_1:Nat:=c1 ((2:Nat));
                let c3_1:Nat:=c6 c2_1;
                let c4_1:Nat:=c2 c3_1 (c2 R R);
                let c5_1:Nat:=c3 c4_1 c0;
                let c6:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
                let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                let c8:Nat:=
                  c2
                    (c2
                      (c2
                        (c3 ((100:Nat))
                          (c7 (c2 (c8 R) ((2:Nat)))
                            ((3:Nat))))
                        ((10:Nat)))
                      (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
                    ((1:Nat));
                let c9_1:Nat:=
                  c3 c6 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
                let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
                let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
                let c12_1:Nat→ Nat:=c3 c0;
                let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
                let c14_1:Nat:=
                  c3 ((1000:Nat))
                    (c1 ((5:Nat)));
                let c15_1:Nat:=
                  c2
                    (c2
                      (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6)
                        ((30:Nat)))
                      c14_1)
                    ((20:Nat));
                let c16:Nat:=c10_1 (@AXr9520_10 lp p);
                let c17:Nat→ Nat:=
                  c2 (c9 (c2 (c2 c11_1 c14_1) ((1:Nat))));
                c2
                  (c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c11_1)
                                    (c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c15_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c15_1 c16) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c17 c8) c15_1) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c16)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c16 ((1:Nat)))
                                (c2 (c2 c12 (c13 c16)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c17 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                  (@Polynomial.eval Nat Nat.instSemiring R c15))
              (fun (R:Nat) => @Polynomial.eval Nat Nat.instSemiring R c16)
              (@AXr9520_12
                (fun (R:Nat) =>
                  let c0:Nat:=c2 R ((1:Nat));
                  let c1:Nat→ Nat:=c7 c0;
                  let c2_1:Nat:=c1 ((2:Nat));
                  let c3_1:Nat:=c6 c2_1;
                  let c4_1:Nat:=c2 c3_1 (c2 R R);
                  let c5_1:Nat:=c3 c4_1 c0;
                  let c6:Nat:=c4 (c5 (c2 (c2 c5_1 c4_1) c0));
                  let c7_1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                  let c8:Nat:=
                    c2
                      (c2
                        (c2
                          (c3 ((100:Nat))
                            (c7 (c2 (c8 R) ((2:Nat)))
                              ((3:Nat))))
                          ((10:Nat)))
                        (c9 (c2 (c7_1 (c8 R)) ((1:Nat)))))
                      ((1:Nat));
                  let c9_1:Nat:=
                    c3 c6 (c2 (c2 (c2 c8 c3_1) (c9 R)) ((4:Nat)));
                  let c10_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c9_1;
                  let c11_1:Nat:=c10_1 (@AXr9520_7 lp p);
                  let c12_1:Nat→ Nat:=c3 c0;
                  let c13_1:Nat:=c2 (c9 c11_1) ((1:Nat));
                  let c14_1:Nat:=
                    c3 ((1000:Nat))
                      (c1 ((5:Nat)));
                  let c15:Nat:=
                    c2
                      (c2
                        (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c6)
                          ((30:Nat)))
                        c14_1)
                      ((20:Nat));
                  let c16:Nat:=c10_1 (@AXr9520_10 lp p);
                  let c17:Nat→ Nat:=
                    c2 (c9 (c2 (c2 c11_1 c14_1) ((1:Nat))));
                  c2
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c11_1)
                                    (c2 (c2 (c7_1 (c12_1 c13_1)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c15))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c15 c16) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2 (c2 (c2 (c17 c8) c15) c9_1)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c9_1 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c16)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c12_1 (c2 c13_1 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c9_1)
                    (c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c5_1)
                                (c3 ((87:Nat)) c4_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c9_1)
                                    ((39:Nat)))
                                  c6)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c16 ((1:Nat)))
                                (c2 (c2 c12 (c13 c16)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2 (c14 (c17 ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))))
                (fun (R:Nat) => @Polynomial.eval Nat Nat.instSemiring R c15)
                (@AXr9520_12
                  (fun (R:Nat) =>
                    let c0:Nat:=c2 R ((1:Nat));
                    let c1:Nat→ Nat:=c7 c0;
                    let c2_1:Nat:=c1 ((2:Nat));
                    let c3_1:Nat:=c6 c2_1;
                    let c4_1:Nat:=c2 c3_1 (c2 R R);
                    let c5_1:Nat:=c4 (c5 (c2 (c2 (c3 c4_1 c0) c4_1) c0));
                    let c6:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                    let c7:Nat:=
                      c2
                        (c2
                          (c2
                            (c3 ((100:Nat))
                              (c7 (c2 (c8 R) ((2:Nat)))
                                ((3:Nat))))
                            ((10:Nat)))
                          (c9 (c2 (c6 (c8 R)) ((1:Nat)))))
                        ((1:Nat));
                    let c8:Nat:=
                      c3 c5_1 (c2 (c2 (c2 c7 c3_1) (c9 R)) ((4:Nat)));
                    let c9_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c8;
                    let c10_1:Nat:=c9_1 (@AXr9520_7 lp p);
                    let c11:Nat→ Nat:=c3 c0;
                    let c12:Nat:=c2 (c9 c10_1) ((1:Nat));
                    let c13:Nat:=
                      c3 ((1000:Nat))
                        (c1 ((5:Nat)));
                    let c14:Nat:=
                      c2
                        (c2
                          (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c5_1)
                            ((30:Nat)))
                          c13)
                        ((20:Nat));
                    let c15:Nat:=c9_1 (@AXr9520_10 lp p);
                    c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c10_1)
                                    (c2 (c2 (c6 (c11 c12)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c14))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c14 c15) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 c10_1 c13) ((1:Nat))))
                                        c7)
                                      c14)
                                    c8)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c8 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c15)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c11 (c2 c12 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                      c8)
                  (fun (R:Nat) =>
                    let c0:Nat:=c2 R ((1:Nat));
                    let c1:Nat→ Nat:=c7 c0;
                    let c2_1:Nat:=c6 (c1 ((2:Nat)));
                    let c3_1:Nat:=c2 c2_1 (c2 R R);
                    let c4_1:Nat:=c3 c3_1 c0;
                    let c5:Nat:=c4 (c5 (c2 (c2 c4_1 c3_1) c0));
                    let c6:Nat:=
                      c3 c5
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c3 ((100:Nat))
                                      (c7 (c2 (c8 R) ((2:Nat)))
                                        ((3:Nat))))
                                    ((10:Nat)))
                                  (c9
                                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                      ((1:Nat)))))
                                ((1:Nat)))
                              c2_1)
                            (c9 R))
                          ((4:Nat)));
                    let c7:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c6;
                    let c8:Nat:=c7 (@AXr9520_10 lp p);
                    c2
                      (c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c4_1)
                                (c3 ((87:Nat)) c3_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c6)
                                    ((39:Nat)))
                                  c5)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c8 ((1:Nat)))
                                (c2 (c2 c12 (c13 c8)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                      (c2
                        (c3
                          (c2
                            (c14
                              (c2
                                (c9
                                  (c2
                                    (c2 (c7 (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat))))
                  (@AXr9520_12
                    (fun (R:Nat) =>
                      let c0:Nat:=c2 R ((1:Nat));
                      let c1:Nat→ Nat:=c7 c0;
                      let c2_1:Nat:=c1 ((2:Nat));
                      let c3_1:Nat:=c6 c2_1;
                      let c4_1:Nat:=c2 c3_1 (c2 R R);
                      let c5_1:Nat:=c4 (c5 (c2 (c2 (c3 c4_1 c0) c4_1) c0));
                      let c6:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                      let c7:Nat:=
                        c2
                          (c2
                            (c2
                              (c3 ((100:Nat))
                                (c7 (c2 (c8 R) ((2:Nat)))
                                  ((3:Nat))))
                              ((10:Nat)))
                            (c9 (c2 (c6 (c8 R)) ((1:Nat)))))
                          ((1:Nat));
                      let c8:Nat:=
                        c3 c5_1 (c2 (c2 (c2 c7 c3_1) (c9 R)) ((4:Nat)));
                      let c9_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c8;
                      let c10_1:Nat:=c9_1 (@AXr9520_7 lp p);
                      let c11:Nat→ Nat:=c3 c0;
                      let c12:Nat:=c2 (c9 c10_1) ((1:Nat));
                      let c13:Nat:=
                        c3 ((1000:Nat))
                          (c1 ((5:Nat)));
                      let c14:Nat:=
                        c2
                          (c2
                            (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c5_1)
                              ((30:Nat)))
                            c13)
                          ((20:Nat));
                      let c15:Nat:=c9_1 (@AXr9520_10 lp p);
                      c2
                        (c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c10_1)
                                    (c2 (c2 (c6 (c11 c12)) (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c14))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c14 c15) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 c10_1 c13) ((1:Nat))))
                                        c7)
                                      c14)
                                    c8)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c8 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c15)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                        (c2
                          (c2 (c11 (c2 c12 ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat))))
                    c24
                    (@AXr9520_12
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat→ Nat:=c7 c0;
                        let c2_1:Nat:=c1 ((2:Nat));
                        let c3_1:Nat:=c6 c2_1;
                        let c4_1:Nat:=c2 c3_1 (c2 R R);
                        let c5_1:Nat:=c4 (c5 (c2 (c2 (c3 c4_1 c0) c4_1) c0));
                        let c6:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                        let c7:Nat:=
                          c2
                            (c2
                              (c2
                                (c3 ((100:Nat))
                                  (c7 (c2 (c8 R) ((2:Nat)))
                                    ((3:Nat))))
                                ((10:Nat)))
                              (c9 (c2 (c6 (c8 R)) ((1:Nat)))))
                            ((1:Nat));
                        let c8:Nat:=
                          c3 c5_1
                            (c2 (c2 (c2 c7 c3_1) (c9 R)) ((4:Nat)));
                        let c9_1:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c8;
                        let c10_1:Nat:=c9_1 (@AXr9520_7 lp p);
                        let c11:Nat:=
                          c3 ((1000:Nat))
                            (c1 ((5:Nat)));
                        let c12:Nat:=
                          c2
                            (c2
                              (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c5_1)
                                ((30:Nat)))
                              c11)
                            ((20:Nat));
                        let c13:Nat:=c9_1 (@AXr9520_10 lp p);
                        c2
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c10_1)
                                    (c2
                                      (c2
                                        (c6
                                          (c3 c0
                                            (c2 (c9 c10_1) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c12))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c12 c13) ((10:Nat))))
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 c10_1 c11) ((1:Nat))))
                                        c7)
                                      c12)
                                    c8)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c8 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                c13)
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat))))
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                        let c2_1:Nat:=c2 c1 (c2 R R);
                        c2
                          (c2
                            (c3 c0
                              (c2
                                (c2
                                  (c9
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p)))
                                  ((1:Nat)))
                                ((1:Nat))))
                            ((10:Nat)))
                          ((4:Nat)))
                      (@AXr9520_12
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat→ Nat:=c7 c0;
                          let c2_1:Nat:=c1 ((2:Nat));
                          let c3_1:Nat:=c6 c2_1;
                          let c4_1:Nat:=c2 c3_1 (c2 R R);
                          let c5_1:Nat:=c4 (c5 (c2 (c2 (c3 c4_1 c0) c4_1) c0));
                          let c6:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                          let c7:@Polynomial Nat Nat.instSemiring→ Nat:=
                            @Polynomial.eval Nat Nat.instSemiring
                              (c3 c5_1
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2 (c6 (c8 R)) ((1:Nat)))))
                                        ((1:Nat)))
                                      c3_1)
                                    (c9 R))
                                  ((4:Nat))));
                          let c8:Nat:=c7 (@AXr9520_7 lp p);
                          let c9_1:Nat:=
                            c2
                              (c2
                                (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c5_1)
                                  ((30:Nat)))
                                (c3 ((1000:Nat))
                                  (c1 ((5:Nat)))))
                              ((20:Nat));
                          c2
                            (c2
                              (c2
                                (c2
                                  (c2 (c2 R c8)
                                    (c2
                                      (c2
                                        (c6
                                          (c3 c0
                                            (c2 (c9 c8) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0) c9_1))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                            (c2 (c2 c9_1 (c7 (@AXr9520_10 lp p)))
                              ((10:Nat))))
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat→ Nat:=c7 c0;
                          let c2_1:Nat:=c6 (c1 ((2:Nat)));
                          let c3_1:Nat:=c2 c2_1 (c2 R R);
                          let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                          let c5_1:Nat:=
                            c2
                              (c2
                                (c2
                                  (c3 ((100:Nat))
                                    (c7 (c2 (c8 R) ((2:Nat)))
                                      ((3:Nat))))
                                  ((10:Nat)))
                                (c9
                                  (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                    ((1:Nat)))))
                              ((1:Nat));
                          let c6:Nat:=
                            c3 c4
                              (c2 (c2 (c2 c5_1 c2_1) (c9 R)) ((4:Nat)));
                          let c7:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c6;
                          let c8:Nat:=
                            c3 ((1000:Nat))
                              (c1 ((5:Nat)));
                          c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 (c7 (@AXr9520_7 lp p)) c8)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c8)
                                        ((20:Nat))))
                                    c6)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c6 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                (c7 (@AXr9520_10 lp p)))
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                            ((100:Nat)))
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat→ Nat:=c7 c0;
                            let c2_1:Nat:=c1 ((2:Nat));
                            let c3_1:Nat:=c6 c2_1;
                            let c4_1:Nat:=c2 c3_1 (c2 R R);
                            let c5_1:Nat:=c4 (c5 (c2 (c2 (c3 c4_1 c0) c4_1) c0));
                            let c6:Nat→ Nat:=
                              c2 (c3 ((80:Nat)) c0);
                            let c7:Nat:=
                              @Polynomial.eval Nat Nat.instSemiring
                                (c3 c5_1
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c3 ((100:Nat))
                                                (c7
                                                  (c2 (c8 R) ((2:Nat)))
                                                  ((3:Nat))))
                                              ((10:Nat)))
                                            (c9
                                              (c2 (c6 (c8 R))
                                                ((1:Nat)))))
                                          ((1:Nat)))
                                        c3_1)
                                      (c9 R))
                                    ((4:Nat))))
                                (@AXr9520_7 lp p);
                            c2
                              (c2
                                (c2
                                  (c2 (c2 R c7)
                                    (c2
                                      (c2
                                        (c6
                                          (c3 c0
                                            (c2 (c9 c7) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0)
                                    (c2
                                      (c2
                                        (c2 (c2 (c2 (c2 (c5 (c3 c3_1 R)) (c10 c3_1)) (c10 R)) c5_1)
                                          ((30:Nat)))
                                        (c3 ((1000:Nat))
                                          (c1 ((5:Nat)))))
                                      ((20:Nat)))))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                              (c3 ((10:Nat)) c2_1))
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat→ Nat:=c7 c0;
                            let c2_1:Nat:=c6 (c1 ((2:Nat)));
                            let c3_1:Nat:=c2 c2_1 (c2 R R);
                            let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                            c2
                              (c2
                                (c2
                                  (c2
                                    (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                      ((30:Nat)))
                                    (c3 ((1000:Nat))
                                      (c1 ((5:Nat)))))
                                  ((20:Nat)))
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (c3 c4
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c3 ((100:Nat))
                                                  (c7
                                                    (c2 (c8 R)
                                                      ((2:Nat)))
                                                    ((3:Nat))))
                                                ((10:Nat)))
                                              (c9
                                                (c2
                                                  (c2
                                                    (c3 ((80:Nat)) c0)
                                                    (c8 R))
                                                  ((1:Nat)))))
                                            ((1:Nat)))
                                          c2_1)
                                        (c9 R))
                                      ((4:Nat))))
                                  (@AXr9520_10 lp p)))
                              ((10:Nat)))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat→ Nat:=c7 c0;
                              let c2_1:Nat:=c6 (c1 ((2:Nat)));
                              let c3_1:Nat:=c2 c2_1 (c2 R R);
                              let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                              let c5_1:Nat→ Nat:=
                                c2 (c3 ((80:Nat)) c0);
                              let c6:Nat:=
                                @Polynomial.eval Nat Nat.instSemiring
                                  (c3 c4
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c3 ((100:Nat))
                                                  (c7
                                                    (c2 (c8 R)
                                                      ((2:Nat)))
                                                    ((3:Nat))))
                                                ((10:Nat)))
                                              (c9
                                                (c2 (c5_1 (c8 R))
                                                  ((1:Nat)))))
                                            ((1:Nat)))
                                          c2_1)
                                        (c9 R))
                                      ((4:Nat))))
                                  (@AXr9520_7 lp p);
                              c2
                                (c2
                                  (c2 (c2 R c6)
                                    (c2
                                      (c2
                                        (c5_1
                                          (c3 c0
                                            (c2 (c9 c6) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0)
                                    (c2
                                      (c2
                                        (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                          ((30:Nat)))
                                        (c3 ((1000:Nat))
                                          (c1 ((5:Nat)))))
                                      ((20:Nat)))))
                                (c3 (AXr9520_5 cfg)
                                  (c1 ((4:Nat)))))
                            (fun (R:Nat) =>
                              c3 ((10:Nat))
                                (c7 (c2 R ((1:Nat)))
                                  ((2:Nat))))
                            (@AXr9520_12
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                let c1:Nat→ Nat:=c7 c0;
                                let c2_1:Nat:=c6 (c1 ((2:Nat)));
                                let c3_1:Nat:=c2 c2_1 (c2 R R);
                                let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                                let c5_1:Nat→ Nat:=
                                  c2 (c3 ((80:Nat)) c0);
                                let c6:Nat:=
                                  @Polynomial.eval Nat Nat.instSemiring
                                    (c3 c4
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c3 ((100:Nat))
                                                    (c7
                                                      (c2 (c8 R)
                                                        ((2:Nat)))
                                                      ((3:Nat))))
                                                  ((10:Nat)))
                                                (c9
                                                  (c2 (c5_1 (c8 R))
                                                    ((1:Nat)))))
                                              ((1:Nat)))
                                            c2_1)
                                          (c9 R))
                                        ((4:Nat))))
                                    (@AXr9520_7 lp p);
                                c2
                                  (c2 (c2 R c6)
                                    (c2
                                      (c2
                                        (c5_1
                                          (c3 c0
                                            (c2 (c9 c6) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  (c2 (c3 ((200:Nat)) c0)
                                    (c2
                                      (c2
                                        (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                          ((30:Nat)))
                                        (c3 ((1000:Nat))
                                          (c1 ((5:Nat)))))
                                      ((20:Nat)))))
                              (fun (R:Nat) =>
                                c3 (AXr9520_5 cfg)
                                  (c7 (c2 R ((1:Nat)))
                                    ((4:Nat))))
                              (@AXr9520_12
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                  let c2_1:Nat:=c2 c1 (c2 R R);
                                  let c3_1:Nat→ Nat:=
                                    c2 (c3 ((80:Nat)) c0);
                                  let c4:Nat:=
                                    @Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2 (c3_1 (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p);
                                  c2 (c2 R c4)
                                    (c2
                                      (c2
                                        (c3_1
                                          (c3 c0
                                            (c2 (c9 c4) ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat→ Nat:=c7 c0;
                                  let c2_1:Nat:=c6 (c1 ((2:Nat)));
                                  let c3_1:Nat:=c2 c2_1 (c2 R R);
                                  c2 (c3 ((200:Nat)) c0)
                                    (c2
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R))
                                            (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0))))
                                          ((30:Nat)))
                                        (c3 ((1000:Nat))
                                          (c1 ((5:Nat)))))
                                      ((20:Nat))))
                                (@AXr9520_12
                                  (fun (R:Nat) =>
                                    let c0:Nat:=c2 R ((1:Nat));
                                    let c1:Nat:=
                                      c6 (c7 c0 ((2:Nat)));
                                    let c2_1:Nat:=c2 c1 (c2 R R);
                                    c2 R
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                  c25
                                  (@AXr9520_12 (fun (R:Nat) => R) c26
                                    AXr9520_4 c51)
                                  c55)
                                (@AXr9520_12
                                  (fun (R:Nat) =>
                                    c3 ((200:Nat))
                                      (c2 R ((1:Nat))))
                                  c56
                                  (@AXr9520_13
                                    (fun (R:Nat) => (200:Nat)) c30
                                    (AXr9520_3
                                      ((200:Nat)))
                                    c37)
                                  c60))
                              (@AXr9520_13
                                (fun (R:Nat) => AXr9520_5 cfg)
                                (fun (R:Nat) =>
                                  c7 (c2 R ((1:Nat)))
                                    ((4:Nat)))
                                (AXr9520_3
                                  (AXr9520_5 cfg))
                                (c36 ((4:Nat)) c37)))
                            (@AXr9520_13
                              (fun (R:Nat) => (10:Nat)) c35
                              (AXr9520_3
                                ((10:Nat)))
                              c38))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat→ Nat:=c7 c0;
                              let c2_1:Nat:=c6 (c1 ((2:Nat)));
                              let c3_1:Nat:=c2 c2_1 (c2 R R);
                              let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                              c2
                                (c2
                                  (c2
                                    (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                      ((30:Nat)))
                                    (c3 ((1000:Nat))
                                      (c1 ((5:Nat)))))
                                  ((20:Nat)))
                                (@Polynomial.eval Nat Nat.instSemiring
                                  (c3 c4
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c3 ((100:Nat))
                                                  (c7
                                                    (c2 (c8 R)
                                                      ((2:Nat)))
                                                    ((3:Nat))))
                                                ((10:Nat)))
                                              (c9
                                                (c2
                                                  (c2
                                                    (c3 ((80:Nat)) c0)
                                                    (c8 R))
                                                  ((1:Nat)))))
                                            ((1:Nat)))
                                          c2_1)
                                        (c9 R))
                                      ((4:Nat))))
                                  (@AXr9520_10 lp p)))
                            (fun (R:Nat) => (10:Nat))
                            (@AXr9520_12 c56 c61 c60 c62)
                            (AXr9520_3
                              ((10:Nat)))))
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat→ Nat:=c7 c0;
                            let c2_1:Nat:=c6 (c1 ((2:Nat)));
                            let c3_1:Nat:=c2 c2_1 (c2 R R);
                            let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                            let c5_1:Nat:=
                              c2
                                (c2
                                  (c2
                                    (c3 ((100:Nat))
                                      (c7 (c2 (c8 R) ((2:Nat)))
                                        ((3:Nat))))
                                    ((10:Nat)))
                                  (c9
                                    (c2 (c2 (c3 ((80:Nat)) c0) (c8 R))
                                      ((1:Nat)))))
                                ((1:Nat));
                            let c6:Nat:=
                              c3 c4
                                (c2 (c2 (c2 c5_1 c2_1) (c9 R))
                                  ((4:Nat)));
                            let c7:@Polynomial Nat Nat.instSemiring→ Nat:= @Polynomial.eval Nat Nat.instSemiring c6;
                            let c8:Nat:=
                              c3 ((1000:Nat))
                                (c1 ((5:Nat)));
                            c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 (c7 (@AXr9520_7 lp p)) c8)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c8)
                                        ((20:Nat))))
                                    c6)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c6 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                (c7 (@AXr9520_10 lp p)))
                              (AXr9520_11
                                (@AXr9520_9 lp p)))
                          (fun (R:Nat) => (100:Nat))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat→ Nat:=c7 c0;
                              let c2_1:Nat:=c6 (c1 ((2:Nat)));
                              let c3_1:Nat:=c2 c2_1 (c2 R R);
                              let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                              let c5_1:Nat:=
                                c2
                                  (c2
                                    (c2
                                      (c3 ((100:Nat))
                                        (c7 (c2 (c8 R) ((2:Nat)))
                                          ((3:Nat))))
                                      ((10:Nat)))
                                    (c9
                                      (c2
                                        (c2 (c3 ((80:Nat)) c0) (c8 R))
                                        ((1:Nat)))))
                                  ((1:Nat));
                              let c6:Nat:=
                                c3 c4
                                  (c2 (c2 (c2 c5_1 c2_1) (c9 R))
                                    ((4:Nat)));
                              let c7:@Polynomial Nat Nat.instSemiring→ Nat:=
                                @Polynomial.eval Nat Nat.instSemiring c6;
                              let c8:Nat:=
                                c3 ((1000:Nat))
                                  (c1 ((5:Nat)));
                              c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2 (c2 (c7 (@AXr9520_7 lp p)) c8)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c8)
                                        ((20:Nat))))
                                    c6)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c6 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                                (c7 (@AXr9520_10 lp p)))
                            (fun (R:Nat) =>
                              AXr9520_11
                                (@AXr9520_9 lp p))
                            (@AXr9520_12
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                let c1:Nat→ Nat:=c7 c0;
                                let c2_1:Nat:=c6 (c1 ((2:Nat)));
                                let c3_1:Nat:=c2 c2_1 (c2 R R);
                                let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                                let c5_1:Nat:=
                                  c2
                                    (c2
                                      (c2
                                        (c3 ((100:Nat))
                                          (c7 (c2 (c8 R) ((2:Nat)))
                                            ((3:Nat))))
                                        ((10:Nat)))
                                      (c9
                                        (c2
                                          (c2 (c3 ((80:Nat)) c0)
                                            (c8 R))
                                          ((1:Nat)))))
                                    ((1:Nat));
                                let c6:Nat:=
                                  c3 c4
                                    (c2 (c2 (c2 c5_1 c2_1) (c9 R))
                                      ((4:Nat)));
                                let c7:Nat:=
                                  c3 ((1000:Nat))
                                    (c1 ((5:Nat)));
                                c2
                                  (c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2
                                            (c2
                                              (@Polynomial.eval Nat Nat.instSemiring c6
                                                (@AXr9520_7 lp p))
                                              c7)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c7)
                                        ((20:Nat))))
                                    c6)
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c2 c6 ((1:Nat)))
                                    (@AXr9520_7 lp p)))
                              c61
                              (@AXr9520_12
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat→ Nat:=c7 c0;
                                  let c2_1:Nat:=c6 (c1 ((2:Nat)));
                                  let c3_1:Nat:=c2 c2_1 (c2 R R);
                                  let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                                  let c5_1:Nat:=
                                    c2
                                      (c2
                                        (c2
                                          (c3 ((100:Nat))
                                            (c7 (c2 (c8 R) ((2:Nat)))
                                              ((3:Nat))))
                                          ((10:Nat)))
                                        (c9
                                          (c2
                                            (c2 (c3 ((80:Nat)) c0)
                                              (c8 R))
                                            ((1:Nat)))))
                                      ((1:Nat));
                                  let c6:Nat:=
                                    c3 c4
                                      (c2 (c2 (c2 c5_1 c2_1) (c9 R))
                                        ((4:Nat)));
                                  let c7:Nat:=
                                    c3 ((1000:Nat))
                                      (c1 ((5:Nat)));
                                  c2
                                    (c2
                                      (c2
                                        (c9
                                          (c2
                                            (c2
                                              (@Polynomial.eval Nat Nat.instSemiring c6
                                                (@AXr9520_7 lp p))
                                              c7)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c7)
                                        ((20:Nat))))
                                    c6)
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                  let c2_1:Nat:=c2 c1 (c2 R R);
                                  @Polynomial.eval Nat Nat.instSemiring
                                    (c2
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      ((1:Nat)))
                                    (@AXr9520_7 lp p))
                                (@AXr9520_12
                                  (fun (R:Nat) =>
                                    let c0:Nat:=c2 R ((1:Nat));
                                    let c1:Nat→ Nat:=c7 c0;
                                    let c2_1:Nat:=c6 (c1 ((2:Nat)));
                                    let c3_1:Nat:=c2 c2_1 (c2 R R);
                                    let c4:Nat:=c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0));
                                    let c5_1:Nat:=
                                      c2
                                        (c2
                                          (c2
                                            (c3 ((100:Nat))
                                              (c7 (c2 (c8 R) ((2:Nat)))
                                                ((3:Nat))))
                                            ((10:Nat)))
                                          (c9
                                            (c2
                                              (c2 (c3 ((80:Nat)) c0)
                                                (c8 R))
                                              ((1:Nat)))))
                                        ((1:Nat));
                                    let c6:Nat:=
                                      c3 ((1000:Nat))
                                        (c1 ((5:Nat)));
                                    c2
                                      (c2
                                        (c9
                                          (c2
                                            (c2
                                              (@Polynomial.eval Nat Nat.instSemiring
                                                (c3 c4
                                                  (c2 (c2 (c2 c5_1 c2_1) (c9 R))
                                                    ((4:Nat))))
                                                (@AXr9520_7 lp p))
                                              c6)
                                            ((1:Nat))))
                                        c5_1)
                                      (c2
                                        (c2
                                          (c2 (c2 (c2 (c2 (c5 (c3 c2_1 R)) (c10 c2_1)) (c10 R)) c4)
                                            ((30:Nat)))
                                          c6)
                                        ((20:Nat))))
                                  c24
                                  (@AXr9520_12
                                    (fun (R:Nat) =>
                                      let c0:Nat:=c2 R ((1:Nat));
                                      let c1:Nat→ Nat:=c7 c0;
                                      let c2_1:Nat:=
                                        c6 (c1 ((2:Nat)));
                                      let c3_1:Nat:=c2 c2_1 (c2 R R);
                                      let c4_1:Nat:=
                                        c2
                                          (c2
                                            (c2
                                              (c3 ((100:Nat))
                                                (c7
                                                  (c2 (c8 R) ((2:Nat)))
                                                  ((3:Nat))))
                                              ((10:Nat)))
                                            (c9
                                              (c2
                                                (c2 (c3 ((80:Nat)) c0)
                                                  (c8 R))
                                                ((1:Nat)))))
                                          ((1:Nat));
                                      c2
                                        (c9
                                          (c2
                                            (c2
                                              (@Polynomial.eval Nat Nat.instSemiring
                                                (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                  (c2 (c2 (c2 c4_1 c2_1) (c9 R))
                                                    ((4:Nat))))
                                                (@AXr9520_7 lp p))
                                              (c3 ((1000:Nat))
                                                (c1 ((5:Nat)))))
                                            ((1:Nat))))
                                        c4_1)
                                    c56 (@c63 c43 c64 c48) c60)
                                  c50)
                                (@AXr9520_8
                                  (@AXr9520_7 lp p)
                                  (fun (R:Nat) =>
                                    let c0:Nat:=c2 R ((1:Nat));
                                    let c1:Nat:=
                                      c6 (c7 c0 ((2:Nat)));
                                    let c2_1:Nat:=c2 c1 (c2 R R);
                                    c2
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      ((1:Nat)))
                                  (@AXr9520_12 c24
                                    (fun (R:Nat) => (1:Nat)) c50
                                    (AXr9520_3
                                      ((1:Nat))))))
                              c62)
                            (AXr9520_3
                              (AXr9520_11
                                (@AXr9520_9 lp p))))
                          (AXr9520_3
                            ((100:Nat)))))
                      (@AXr9520_12
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                          let c2_1:Nat:=c2 c1 (c2 R R);
                          c2
                            (c3 c0
                              (c2
                                (c2
                                  (c9
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p)))
                                  ((1:Nat)))
                                ((1:Nat))))
                            ((10:Nat)))
                        (fun (R:Nat) => (4:Nat))
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                            let c2_1:Nat:=c2 c1 (c2 R R);
                            c3 c0
                              (c2
                                (c2
                                  (c9
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p)))
                                  ((1:Nat)))
                                ((1:Nat))))
                          (fun (R:Nat) => (10:Nat))
                          (@c52
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                              let c2_1:Nat:=c2 c1 (c2 R R);
                              c2
                                (c2
                                  (c9
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p)))
                                  ((1:Nat)))
                                ((1:Nat)))
                            c37
                            (@AXr9520_12 c53
                              (fun (R:Nat) => (1:Nat)) c54
                              (AXr9520_3
                                ((1:Nat)))))
                          (AXr9520_3
                            ((10:Nat))))
                        (AXr9520_3
                          ((4:Nat)))))
                    c50)
                  (@AXr9520_12
                    (fun (R:Nat) =>
                      let c0:Nat:=c2 R ((1:Nat));
                      let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                      let c2_1:Nat:=c2 c1 (c2 R R);
                      let c3_1:Nat:=c3 c2_1 c0;
                      let c4:Nat:=c4 (c5 (c2 (c2 c3_1 c2_1) c0));
                      let c5:Nat:=
                        c3 c4
                          (c2
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c3 ((100:Nat))
                                        (c7 (c2 (c8 R) ((2:Nat)))
                                          ((3:Nat))))
                                      ((10:Nat)))
                                    (c9
                                      (c2
                                        (c2 (c3 ((80:Nat)) c0) (c8 R))
                                        ((1:Nat)))))
                                  ((1:Nat)))
                                c1)
                              (c9 R))
                            ((4:Nat)));
                      let c6:Nat:=
                        @Polynomial.eval Nat Nat.instSemiring c5 (@AXr9520_10 lp p);
                      c2
                        (c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c3_1)
                                (c3 ((87:Nat)) c2_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c5)
                                    ((39:Nat)))
                                  c4)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c6 ((1:Nat)))
                                (c2 (c2 c12 (c13 c6)) ((104:Nat))))
                              ((18:Nat)))))
                        ((25:Nat)))
                    (fun (R:Nat) =>
                      let c0:Nat:=c2 R ((1:Nat));
                      let c1:Nat→ Nat:=c7 c0;
                      let c2_1:Nat:=c6 (c1 ((2:Nat)));
                      let c3_1:Nat:=c2 c2_1 (c2 R R);
                      c2
                        (c3
                          (c2
                            (c14
                              (c2
                                (c9
                                  (c2
                                    (c2
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat))))
                            ((300:Nat)))
                          c0)
                        ((200:Nat)))
                    (@AXr9520_12
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                        let c2_1:Nat:=c2 c1 (c2 R R);
                        let c3_1:Nat:=c3 c2_1 c0;
                        let c4:Nat:=c4 (c5 (c2 (c2 c3_1 c2_1) c0));
                        let c5:Nat:=
                          c3 c4
                            (c2
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c3 ((100:Nat))
                                          (c7 (c2 (c8 R) ((2:Nat)))
                                            ((3:Nat))))
                                        ((10:Nat)))
                                      (c9
                                        (c2
                                          (c2 (c3 ((80:Nat)) c0)
                                            (c8 R))
                                          ((1:Nat)))))
                                    ((1:Nat)))
                                  c1)
                                (c9 R))
                              ((4:Nat)));
                        let c6:Nat:=
                          @Polynomial.eval Nat Nat.instSemiring c5
                            (@AXr9520_10 lp p);
                        c2
                          (c2
                            (c2
                              (c2 (c3 ((85:Nat)) c3_1)
                                (c3 ((87:Nat)) c2_1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                          (c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c5)
                                    ((39:Nat)))
                                  c4)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c6 ((1:Nat)))
                                (c2 (c2 c12 (c13 c6)) ((104:Nat))))
                              ((18:Nat)))))
                      (fun (R:Nat) => (25:Nat))
                      (@AXr9520_12
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat:=
                            c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
                          c2
                            (c2
                              (c2 (c3 ((85:Nat)) (c3 c1 c0))
                                (c3 ((87:Nat)) c1))
                              (c3 ((45:Nat)) c0))
                            ((54:Nat)))
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                          let c2_1:Nat:=c2 c1 (c2 R R);
                          let c3_1:Nat:=c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0));
                          let c4:Nat:=
                            c3 c3_1
                              (c2
                                (c2
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c3 ((100:Nat))
                                            (c7 (c2 (c8 R) ((2:Nat)))
                                              ((3:Nat))))
                                          ((10:Nat)))
                                        (c9
                                          (c2
                                            (c2 (c3 ((80:Nat)) c0)
                                              (c8 R))
                                            ((1:Nat)))))
                                      ((1:Nat)))
                                    c1)
                                  (c9 R))
                                ((4:Nat)));
                          let c5:Nat:=
                            @Polynomial.eval Nat Nat.instSemiring c4
                              (@AXr9520_10 lp p);
                          c2
                            (c2
                              (c2
                                (c3
                                  (c2 (c3 ((12:Nat)) c4)
                                    ((39:Nat)))
                                  c3_1)
                                c11)
                              ((29:Nat)))
                            (c2
                              (c3 (c2 c5 ((1:Nat)))
                                (c2 (c2 c12 (c13 c5)) ((104:Nat))))
                              ((18:Nat))))
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat:=
                              c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
                            c2
                              (c2 (c3 ((85:Nat)) (c3 c1 c0))
                                (c3 ((87:Nat)) c1))
                              (c3 ((45:Nat)) c0))
                          (fun (R:Nat) => (54:Nat))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat:=
                                c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R);
                              c2 (c3 ((85:Nat)) (c3 c1 c0))
                                (c3 ((87:Nat)) c1))
                            (fun (R:Nat) =>
                              c3 ((45:Nat))
                                (c2 R ((1:Nat))))
                            (@AXr9520_12
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                c3 ((85:Nat))
                                  (c3
                                    (c2 (c6 (c7 c0 ((2:Nat)))) (c2 R R))
                                    c0))
                              (fun (R:Nat) =>
                                c3 ((87:Nat))
                                  (c2
                                    (c6
                                      (c7 (c2 R ((1:Nat)))
                                        ((2:Nat))))
                                    (c2 R R)))
                              (@AXr9520_13
                                (fun (R:Nat) => (85:Nat)) c31
                                (AXr9520_3
                                  ((85:Nat)))
                                c41)
                              (@AXr9520_13
                                (fun (R:Nat) => (87:Nat)) c32
                                (AXr9520_3
                                  ((87:Nat)))
                                c40))
                            (@AXr9520_13
                              (fun (R:Nat) => (45:Nat)) c30
                              (AXr9520_3
                                ((45:Nat)))
                              c37))
                          (AXr9520_3
                            ((54:Nat))))
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                            let c2_1:Nat:=c2 c1 (c2 R R);
                            let c3_1:Nat:=c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0));
                            c2
                              (c2
                                (c3
                                  (c2
                                    (c3 ((12:Nat))
                                      (c3 c3_1
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat)))))
                                    ((39:Nat)))
                                  c3_1)
                                c11)
                              ((29:Nat)))
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                            let c2_1:Nat:=c2 c1 (c2 R R);
                            let c3_1:Nat:=
                              @Polynomial.eval Nat Nat.instSemiring
                                (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                  (c2
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c3 ((100:Nat))
                                                (c7
                                                  (c2 (c8 R) ((2:Nat)))
                                                  ((3:Nat))))
                                              ((10:Nat)))
                                            (c9
                                              (c2
                                                (c2 (c3 ((80:Nat)) c0)
                                                  (c8 R))
                                                ((1:Nat)))))
                                          ((1:Nat)))
                                        c1)
                                      (c9 R))
                                    ((4:Nat))))
                                (@AXr9520_10 lp p);
                            c2
                              (c3 (c2 c3_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c3_1)) ((104:Nat))))
                              ((18:Nat)))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                              let c2_1:Nat:=c2 c1 (c2 R R);
                              let c3_1:Nat:=c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0));
                              c2
                                (c3
                                  (c2
                                    (c3 ((12:Nat))
                                      (c3 c3_1
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat)))))
                                    ((39:Nat)))
                                  c3_1)
                                c11)
                            (fun (R:Nat) => (29:Nat))
                            (@AXr9520_12
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                let c2_1:Nat:=c2 c1 (c2 R R);
                                let c3_1:Nat:=c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0));
                                c3
                                  (c2
                                    (c3 ((12:Nat))
                                      (c3 c3_1
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat)))))
                                    ((39:Nat)))
                                  c3_1)
                              (fun (R:Nat) => c11)
                              (@AXr9520_13
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                  let c2_1:Nat:=c2 c1 (c2 R R);
                                  c2
                                    (c3 ((12:Nat))
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat)))))
                                    ((39:Nat)))
                                c27
                                (@AXr9520_12
                                  (fun (R:Nat) =>
                                    let c0:Nat:=c2 R ((1:Nat));
                                    let c1:Nat:=
                                      c6 (c7 c0 ((2:Nat)));
                                    let c2_1:Nat:=c2 c1 (c2 R R);
                                    c3 ((12:Nat))
                                      (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2
                                                      (c2
                                                        (c3 ((80:Nat))
                                                          c0)
                                                        (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c1)
                                            (c9 R))
                                          ((4:Nat)))))
                                  (fun (R:Nat) => (39:Nat))
                                  (@AXr9520_13
                                    (fun (R:Nat) => (12:Nat)) c24
                                    (AXr9520_3
                                      ((12:Nat)))
                                    c50)
                                  (AXr9520_3
                                    ((39:Nat))))
                                c42)
                              (AXr9520_3 c11))
                            (AXr9520_3
                              ((29:Nat))))
                          (@AXr9520_12
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                              let c2_1:Nat:=c2 c1 (c2 R R);
                              let c3_1:Nat:=
                                @Polynomial.eval Nat Nat.instSemiring
                                  (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                    (c2
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c3 ((100:Nat))
                                                  (c7
                                                    (c2 (c8 R)
                                                      ((2:Nat)))
                                                    ((3:Nat))))
                                                ((10:Nat)))
                                              (c9
                                                (c2
                                                  (c2
                                                    (c3 ((80:Nat)) c0)
                                                    (c8 R))
                                                  ((1:Nat)))))
                                            ((1:Nat)))
                                          c1)
                                        (c9 R))
                                      ((4:Nat))))
                                  (@AXr9520_10 lp p);
                              c3 (c2 c3_1 ((1:Nat)))
                                (c2 (c2 c12 (c13 c3_1)) ((104:Nat))))
                            (fun (R:Nat) => (18:Nat))
                            (@AXr9520_13
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                let c2_1:Nat:=c2 c1 (c2 R R);
                                c2
                                  (@Polynomial.eval Nat Nat.instSemiring
                                    (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                      (c2
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c3 ((100:Nat))
                                                    (c7
                                                      (c2 (c8 R)
                                                        ((2:Nat)))
                                                      ((3:Nat))))
                                                  ((10:Nat)))
                                                (c9
                                                  (c2
                                                    (c2
                                                      (c3 ((80:Nat))
                                                        c0)
                                                      (c8 R))
                                                    ((1:Nat)))))
                                              ((1:Nat)))
                                            c1)
                                          (c9 R))
                                        ((4:Nat))))
                                    (@AXr9520_10 lp p))
                                  ((1:Nat)))
                              (fun (R:Nat) =>
                                let c0:Nat:=c2 R ((1:Nat));
                                let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                let c2_1:Nat:=c2 c1 (c2 R R);
                                c2
                                  (c2 c12
                                    (c13
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_10 lp p))))
                                  ((104:Nat)))
                              (@AXr9520_12 c61
                                (fun (R:Nat) => (1:Nat)) c62
                                (AXr9520_3
                                  ((1:Nat))))
                              (@AXr9520_12
                                (fun (R:Nat) =>
                                  let c0:Nat:=c2 R ((1:Nat));
                                  let c1:Nat:=c6 (c7 c0 ((2:Nat)));
                                  let c2_1:Nat:=c2 c1 (c2 R R);
                                  c2 c12
                                    (c13
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_10 lp p))))
                                (fun (R:Nat) => (104:Nat))
                                (@AXr9520_12 (fun (R:Nat) => c12)
                                  (fun (R:Nat) =>
                                    let c0:Nat:=c2 R ((1:Nat));
                                    let c1:Nat:=
                                      c6 (c7 c0 ((2:Nat)));
                                    let c2_1:Nat:=c2 c1 (c2 R R);
                                    c13
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c2_1 c0) c2_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_10 lp p)))
                                  (AXr9520_3 c12)
                                  (@c65 c61
                                    (AXr9520_3
                                      ((32:Nat)))
                                    c62))
                                (AXr9520_3
                                  ((104:Nat)))))
                            (AXr9520_3
                              ((18:Nat))))))
                      (AXr9520_3
                        ((25:Nat))))
                    (@AXr9520_12
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat→ Nat:=c7 c0;
                        let c2_1:Nat:=c6 (c1 ((2:Nat)));
                        let c3_1:Nat:=c2 c2_1 (c2 R R);
                        c3
                          (c2
                            (c14
                              (c2
                                (c9
                                  (c2
                                    (c2
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat))))
                            ((300:Nat)))
                          c0)
                      (fun (R:Nat) => (200:Nat))
                      (@AXr9520_13
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat→ Nat:=c7 c0;
                          let c2_1:Nat:=c6 (c1 ((2:Nat)));
                          let c3_1:Nat:=c2 c2_1 (c2 R R);
                          c2
                            (c14
                              (c2
                                (c9
                                  (c2
                                    (c2
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat))))
                            ((300:Nat)))
                        c30
                        (@AXr9520_12
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat→ Nat:=c7 c0;
                            let c2_1:Nat:=c6 (c1 ((2:Nat)));
                            let c3_1:Nat:=c2 c2_1 (c2 R R);
                            c14
                              (c2
                                (c9
                                  (c2
                                    (c2
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat))))
                          (fun (R:Nat) => (300:Nat))
                          (@AXr9520_13
                            (fun (R:Nat) => (36:Nat))
                            (fun (R:Nat) =>
                              let c0:Nat:=c2 R ((1:Nat));
                              let c1:Nat→ Nat:=c7 c0;
                              let c2_1:Nat:=c6 (c1 ((2:Nat)));
                              let c3_1:Nat:=c2 c2_1 (c2 R R);
                              c2
                                (c9
                                  (c2
                                    (c2
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((80:Nat))
                                                            c0)
                                                          (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p))
                                      (c3 ((1000:Nat))
                                        (c1 ((5:Nat)))))
                                    ((1:Nat))))
                                ((1:Nat)))
                            (AXr9520_3
                              ((36:Nat)))
                            (@c63 (fun (R:Nat) => (1:Nat)) c64
                              (AXr9520_3
                                ((1:Nat)))))
                          (AXr9520_3
                            ((300:Nat))))
                        c37)
                      (AXr9520_3
                        ((200:Nat))))))
                (@AXr9520_8 c15 (fun (R:Nat) => R)
                  AXr9520_4))
              (@AXr9520_8 c16 (fun (R:Nat) => R)
                AXr9520_4))
            (@AXr9520_8 c17 (fun (R:Nat) => R)
              AXr9520_4))
          (@AXr9520_12
            (fun (R:Nat) =>
              let c0:Nat:=c2 R ((1:Nat));
              let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
              let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
              let c3_1:Nat:=c2 c2_1 (c2 R R);
              c2
                (c2
                  (c18
                    (c7
                      (c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
                (c6 R))
            (fun (R:Nat) => (10:Nat))
            (@AXr9520_12
              (fun (R:Nat) =>
                let c0:Nat:=c2 R ((1:Nat));
                let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                let c3_1:Nat:=c2 c2_1 (c2 R R);
                c2
                  (c18
                    (c7
                      (c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                      ((12:Nat))))
                  (c3 (c5 R) R))
              c6
              (@AXr9520_12
                (fun (R:Nat) =>
                  let c0:Nat:=c2 R ((1:Nat));
                  let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                  let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                  let c3_1:Nat:=c2 c2_1 (c2 R R);
                  c18
                    (c7
                      (c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                      ((12:Nat))))
                (fun (R:Nat) => c3 (c5 R) R)
                (@AXr9520_13 (fun (R:Nat) => c)
                  (fun (R:Nat) =>
                    let c0:Nat:=c2 R ((1:Nat));
                    let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                    let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                    let c3_1:Nat:=c2 c2_1 (c2 R R);
                    c7
                      (c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                      ((12:Nat)))
                  (AXr9520_3 c)
                  (@AXr9520_14
                    (fun (R:Nat) =>
                      let c0:Nat:=c2 R ((1:Nat));
                      let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                      let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                      let c3_1:Nat:=c2 c2_1 (c2 R R);
                      c2
                        (c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        ((1:Nat)))
                    ((12:Nat))
                    (@AXr9520_12
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                        let c3_1:Nat:=c2 c2_1 (c2 R R);
                        c2 (c9 R)
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                      (fun (R:Nat) => (1:Nat))
                      (@AXr9520_12 c9 c25 c49 c55)
                      (AXr9520_3
                        ((1:Nat))))))
                (@AXr9520_13 c5 (fun (R:Nat) => R)
                  (@c29 (fun (R:Nat) => R)
                    (AXr9520_3
                      ((3:Nat)))
                    AXr9520_4)
                  AXr9520_4))
              c66)
            (AXr9520_3
              ((10:Nat)))))
        (@AXr9520_12
          (fun (R:Nat) =>
            let c0:Nat:=c2 R ((1:Nat));
            let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
            let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
            let c3_1:Nat:=c2 c2_1 (c2 R R);
            let c4_1:Nat:=
              c18
                (c7
                  (c2
                    (c2
                      (c2 R
                        (c2
                          (c2
                            (c1
                              (c3 c0
                                (c2
                                  (c9
                                    (@Polynomial.eval Nat Nat.instSemiring
                                      (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                        (c2
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c3 ((100:Nat))
                                                      (c7
                                                        (c2 (c8 R)
                                                          ((2:Nat)))
                                                        ((3:Nat))))
                                                    ((10:Nat)))
                                                  (c9
                                                    (c2 (c1 (c8 R))
                                                      ((1:Nat)))))
                                                ((1:Nat)))
                                              c2_1)
                                            (c9 R))
                                          ((4:Nat))))
                                      (@AXr9520_7 lp p)))
                                  ((1:Nat)))))
                            (c9 R))
                          ((1:Nat))))
                      R)
                    ((1:Nat)))
                  ((12:Nat)));
            c2
              (c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                    ((18:Nat)))
                  (c3 ((96:Nat)) (c3 R R)))
                (c20 R))
              ((78:Nat)))
          (fun (R:Nat) => (16:Nat))
          (@AXr9520_12
            (fun (R:Nat) =>
              let c0:Nat:=c2 R ((1:Nat));
              let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
              let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
              let c3_1:Nat:=c2 c2_1 (c2 R R);
              let c4_1:Nat:=
                c18
                  (c7
                    (c2
                      (c2
                        (c2 R
                          (c2
                            (c2
                              (c1
                                (c3 c0
                                  (c2
                                    (c9
                                      (@Polynomial.eval Nat Nat.instSemiring
                                        (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                          (c2
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c3 ((100:Nat))
                                                        (c7
                                                          (c2 (c8 R)
                                                            ((2:Nat)))
                                                          ((3:Nat))))
                                                      ((10:Nat)))
                                                    (c9
                                                      (c2 (c1 (c8 R))
                                                        ((1:Nat)))))
                                                  ((1:Nat)))
                                                c2_1)
                                              (c9 R))
                                            ((4:Nat))))
                                        (@AXr9520_7 lp p)))
                                    ((1:Nat)))))
                              (c9 R))
                            ((1:Nat))))
                        R)
                      ((1:Nat)))
                    ((12:Nat)));
              c2
                (c2
                  (c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                    ((18:Nat)))
                  (c3 ((96:Nat)) (c3 R R)))
                (c20 R))
            (fun (R:Nat) => (78:Nat))
            (@AXr9520_12
              (fun (R:Nat) =>
                let c0:Nat:=c2 R ((1:Nat));
                let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                let c3_1:Nat:=c2 c2_1 (c2 R R);
                let c4_1:Nat:=
                  c18
                    (c7
                      (c2
                        (c2
                          (c2 R
                            (c2
                              (c2
                                (c1
                                  (c3 c0
                                    (c2
                                      (c9
                                        (@Polynomial.eval Nat Nat.instSemiring
                                          (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                            (c2
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c2
                                                        (c3
                                                          ((100:Nat))
                                                          (c7
                                                            (c2 (c8 R)
                                                              ((2:Nat)))
                                                            ((3:Nat))))
                                                        ((10:Nat)))
                                                      (c9
                                                        (c2 (c1 (c8 R))
                                                          ((1:Nat)))))
                                                    ((1:Nat)))
                                                  c2_1)
                                                (c9 R))
                                              ((4:Nat))))
                                          (@AXr9520_7 lp p)))
                                      ((1:Nat)))))
                                (c9 R))
                              ((1:Nat))))
                          R)
                        ((1:Nat)))
                      ((12:Nat)));
                c2
                  (c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                    ((18:Nat)))
                  (c3 ((96:Nat)) (c3 R R)))
              c20
              (@AXr9520_12
                (fun (R:Nat) =>
                  let c0:Nat:=c2 R ((1:Nat));
                  let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                  let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                  let c3_1:Nat:=c2 c2_1 (c2 R R);
                  let c4_1:Nat:=
                    c18
                      (c7
                        (c2
                          (c2
                            (c2 R
                              (c2
                                (c2
                                  (c1
                                    (c3 c0
                                      (c2
                                        (c9
                                          (@Polynomial.eval Nat Nat.instSemiring
                                            (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                              (c2
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c2
                                                        (c2
                                                          (c3
                                                            ((100:Nat))
                                                            (c7
                                                              (c2 (c8 R)
                                                                ((2:Nat)))
                                                              ((3:Nat))))
                                                          ((10:Nat)))
                                                        (c9
                                                          (c2 (c1 (c8 R))
                                                            ((1:Nat)))))
                                                      ((1:Nat)))
                                                    c2_1)
                                                  (c9 R))
                                                ((4:Nat))))
                                            (@AXr9520_7 lp p)))
                                        ((1:Nat)))))
                                  (c9 R))
                                ((1:Nat))))
                            R)
                          ((1:Nat)))
                        ((12:Nat)));
                  c2
                    (c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                    ((18:Nat)))
                (fun (R:Nat) => c3 ((96:Nat)) (c3 R R))
                (@AXr9520_12
                  (fun (R:Nat) =>
                    let c0:Nat:=c2 R ((1:Nat));
                    let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                    let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                    let c3_1:Nat:=c2 c2_1 (c2 R R);
                    let c4_1:Nat:=
                      c18
                        (c7
                          (c2
                            (c2
                              (c2 R
                                (c2
                                  (c2
                                    (c1
                                      (c3 c0
                                        (c2
                                          (c9
                                            (@Polynomial.eval Nat Nat.instSemiring
                                              (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                (c2
                                                  (c2
                                                    (c2
                                                      (c2
                                                        (c2
                                                          (c2
                                                            (c3
                                                              ((100:Nat))
                                                              (c7
                                                                (c2 (c8 R)
                                                                  ((2:Nat)))
                                                                ((3:Nat))))
                                                            ((10:Nat)))
                                                          (c9
                                                            (c2 (c1 (c8 R))
                                                              ((1:Nat)))))
                                                        ((1:Nat)))
                                                      c2_1)
                                                    (c9 R))
                                                  ((4:Nat))))
                                              (@AXr9520_7 lp p)))
                                          ((1:Nat)))))
                                    (c9 R))
                                  ((1:Nat))))
                              R)
                            ((1:Nat)))
                          ((12:Nat)));
                    c2
                      (c2
                        (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                      (c3 (c2 c4_1 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4_1)) ((104:Nat)))))
                  (fun (R:Nat) => (18:Nat))
                  (@AXr9520_12
                    (fun (R:Nat) =>
                      c2 (c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                        ((12:Nat)))
                    (fun (R:Nat) =>
                      let c0:Nat:=c2 R ((1:Nat));
                      let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                      let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                      let c3_1:Nat:=c2 c2_1 (c2 R R);
                      let c4:Nat:=
                        c18
                          (c7
                            (c2
                              (c2
                                (c2 R
                                  (c2
                                    (c2
                                      (c1
                                        (c3 c0
                                          (c2
                                            (c9
                                              (@Polynomial.eval Nat Nat.instSemiring
                                                (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                  (c2
                                                    (c2
                                                      (c2
                                                        (c2
                                                          (c2
                                                            (c2
                                                              (c3
                                                                ((100:Nat))
                                                                (c7
                                                                  (c2 (c8 R)
                                                                    ((2:Nat)))
                                                                  ((3:Nat))))
                                                              ((10:Nat)))
                                                            (c9
                                                              (c2 (c1 (c8 R))
                                                                ((1:Nat)))))
                                                          ((1:Nat)))
                                                        c2_1)
                                                      (c9 R))
                                                    ((4:Nat))))
                                                (@AXr9520_7 lp p)))
                                            ((1:Nat)))))
                                      (c9 R))
                                    ((1:Nat))))
                                R)
                              ((1:Nat)))
                            ((12:Nat)));
                      c3 (c2 c4 ((1:Nat)))
                        (c2 (c2 c19 (c13 c4)) ((104:Nat))))
                    (@AXr9520_12
                      (fun (R:Nat) =>
                        c3 ((16:Nat)) (c2 (c4 (c5 (c3 R R))) (c6 R)))
                      (fun (R:Nat) => (12:Nat))
                      (@AXr9520_13
                        (fun (R:Nat) => (16:Nat))
                        (fun (R:Nat) => c2 (c4 (c5 (c3 R R))) (c6 R))
                        (AXr9520_3
                          ((16:Nat)))
                        (@AXr9520_12 (fun (R:Nat) => c4 (c5 (c3 R R))) c6
                          (@c28 (fun (R:Nat) => c5 (c3 R R))
                            (AXr9520_3
                              ((2:Nat)))
                            (@c29 c67
                              (AXr9520_3
                                ((3:Nat)))
                              c68))
                          c66))
                      (AXr9520_3
                        ((12:Nat))))
                    (@AXr9520_13
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                        let c3_1:Nat:=c2 c2_1 (c2 R R);
                        c2
                          (c18
                            (c7
                              (c2
                                (c2
                                  (c2 R
                                    (c2
                                      (c2
                                        (c1
                                          (c3 c0
                                            (c2
                                              (c9
                                                (@Polynomial.eval Nat Nat.instSemiring
                                                  (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                    (c2
                                                      (c2
                                                        (c2
                                                          (c2
                                                            (c2
                                                              (c2
                                                                (c3
                                                                  ((100:Nat))
                                                                  (c7
                                                                    (c2 (c8 R)
                                                                      ((2:Nat)))
                                                                    ((3:Nat))))
                                                                ((10:Nat)))
                                                              (c9
                                                                (c2 (c1 (c8 R))
                                                                  ((1:Nat)))))
                                                            ((1:Nat)))
                                                          c2_1)
                                                        (c9 R))
                                                      ((4:Nat))))
                                                  (@AXr9520_7 lp p)))
                                              ((1:Nat)))))
                                        (c9 R))
                                      ((1:Nat))))
                                  R)
                                ((1:Nat)))
                              ((12:Nat))))
                          ((1:Nat)))
                      (fun (R:Nat) =>
                        let c0:Nat:=c2 R ((1:Nat));
                        let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                        let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                        let c3_1:Nat:=c2 c2_1 (c2 R R);
                        c2
                          (c2 c19
                            (c13
                              (c18
                                (c7
                                  (c2
                                    (c2
                                      (c2 R
                                        (c2
                                          (c2
                                            (c1
                                              (c3 c0
                                                (c2
                                                  (c9
                                                    (@Polynomial.eval Nat Nat.instSemiring
                                                      (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                        (c2
                                                          (c2
                                                            (c2
                                                              (c2
                                                                (c2
                                                                  (c2
                                                                    (c3
                                                                      ((100:Nat))
                                                                      (c7
                                                                        (c2 (c8 R)
                                                                          ((2:Nat)))
                                                                        ((3:Nat))))
                                                                    ((10:Nat)))
                                                                  (c9
                                                                    (c2 (c1 (c8 R))
                                                                      ((1:Nat)))))
                                                                ((1:Nat)))
                                                              c2_1)
                                                            (c9 R))
                                                          ((4:Nat))))
                                                      (@AXr9520_7 lp p)))
                                                  ((1:Nat)))))
                                            (c9 R))
                                          ((1:Nat))))
                                      R)
                                    ((1:Nat)))
                                  ((12:Nat))))))
                          ((104:Nat)))
                      (@AXr9520_12 c69
                        (fun (R:Nat) => (1:Nat)) c70
                        (AXr9520_3
                          ((1:Nat))))
                      (@AXr9520_12
                        (fun (R:Nat) =>
                          let c0:Nat:=c2 R ((1:Nat));
                          let c1:Nat→ Nat:=c2 (c3 ((80:Nat)) c0);
                          let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                          let c3_1:Nat:=c2 c2_1 (c2 R R);
                          c2 c19
                            (c13
                              (c18
                                (c7
                                  (c2
                                    (c2
                                      (c2 R
                                        (c2
                                          (c2
                                            (c1
                                              (c3 c0
                                                (c2
                                                  (c9
                                                    (@Polynomial.eval Nat Nat.instSemiring
                                                      (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                        (c2
                                                          (c2
                                                            (c2
                                                              (c2
                                                                (c2
                                                                  (c2
                                                                    (c3
                                                                      ((100:Nat))
                                                                      (c7
                                                                        (c2 (c8 R)
                                                                          ((2:Nat)))
                                                                        ((3:Nat))))
                                                                    ((10:Nat)))
                                                                  (c9
                                                                    (c2 (c1 (c8 R))
                                                                      ((1:Nat)))))
                                                                ((1:Nat)))
                                                              c2_1)
                                                            (c9 R))
                                                          ((4:Nat))))
                                                      (@AXr9520_7 lp p)))
                                                  ((1:Nat)))))
                                            (c9 R))
                                          ((1:Nat))))
                                      R)
                                    ((1:Nat)))
                                  ((12:Nat))))))
                        (fun (R:Nat) => (104:Nat))
                        (@AXr9520_12 (fun (R:Nat) => c19)
                          (fun (R:Nat) =>
                            let c0:Nat:=c2 R ((1:Nat));
                            let c1:Nat→ Nat:=
                              c2 (c3 ((80:Nat)) c0);
                            let c2_1:Nat:=c6 (c7 c0 ((2:Nat)));
                            let c3_1:Nat:=c2 c2_1 (c2 R R);
                            c13
                              (c18
                                (c7
                                  (c2
                                    (c2
                                      (c2 R
                                        (c2
                                          (c2
                                            (c1
                                              (c3 c0
                                                (c2
                                                  (c9
                                                    (@Polynomial.eval Nat Nat.instSemiring
                                                      (c3 (c4 (c5 (c2 (c2 (c3 c3_1 c0) c3_1) c0)))
                                                        (c2
                                                          (c2
                                                            (c2
                                                              (c2
                                                                (c2
                                                                  (c2
                                                                    (c3
                                                                      ((100:Nat))
                                                                      (c7
                                                                        (c2 (c8 R)
                                                                          ((2:Nat)))
                                                                        ((3:Nat))))
                                                                    ((10:Nat)))
                                                                  (c9
                                                                    (c2 (c1 (c8 R))
                                                                      ((1:Nat)))))
                                                                ((1:Nat)))
                                                              c2_1)
                                                            (c9 R))
                                                          ((4:Nat))))
                                                      (@AXr9520_7 lp p)))
                                                  ((1:Nat)))))
                                            (c9 R))
                                          ((1:Nat))))
                                      R)
                                    ((1:Nat)))
                                  ((12:Nat)))))
                          (AXr9520_3 c19)
                          (@c65 c69
                            (AXr9520_3
                              ((32:Nat)))
                            c70))
                        (AXr9520_3
                          ((104:Nat))))))
                  (AXr9520_3
                    ((18:Nat))))
                (@AXr9520_13
                  (fun (R:Nat) => (96:Nat)) c67
                  (AXr9520_3
                    ((96:Nat)))
                  c68))
              (@AXr9520_13
                (fun (R:Nat) => (144:Nat)) (fun (R:Nat) => R)
                (AXr9520_3
                  ((144:Nat)))
                AXr9520_4))
            (AXr9520_3
              ((78:Nat))))
          (AXr9520_3
            ((16:Nat)))))
      (AXr9520_3 ((100:Nat))))

theorem exists_budget {lp flow:List ℕ→ List ℕ} (cfg:Config) (p:NativeSelectedLP.Program lp)
    (q:NativeSelectedNear.Program flow) (c:ℕ):
    ∃ Q e:ℕ,0< Q∧ 0< e∧ ∀ R,demand cfg p q c R≤ Q*(R+1)^e:=
  monomial (polynomial cfg p q c)

end Lax263307Proofs.NativeSelectedBudget

end

theorem solution:∀ {lp flow:List Nat→ List Nat} (cfg:Lax263307Proofs.NativeCoreMachine.Config)
  (p:Lax263307Proofs.NativeSelectedLP.Program lp) (q:Lax263307Proofs.NativeSelectedNear.Program flow) (c:Nat),
  ∃ (Q:Nat) (e:Nat),
    And (Nat.lt ((0:Nat)) Q)
      (And (Nat.lt ((0:Nat)) e)
        (∀ (R:Nat),
          Nat.le (@Lax263307Proofs.NativeSelectedBudget.demand lp flow cfg p q c R)
            (Nat.mul Q
              (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                (Nat.add R
                  ((1:Nat)))
                e)))):= @Lax263307Proofs.NativeSelectedBudget.exists_budget
