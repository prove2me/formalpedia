-- Prove2me | solution 1 for Lax263307Proofs.NativeWeightedExecution.command_spec
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T14:57:45.160836+00:00
-- url     : https://prove2.me/submissions/b49d6e75-5b70-4384-81b0-ae4c5e574bb1

import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Data.NNRat.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Combinatorics.Colex
import Mathlib.Data.List.Sort
import Definitions.Def_EdgeSublinearMWIS_Main_NativeDetailedInterfaces
import Theorems.Thm_Lax263307Proofs_NativeQptasPositive_command_spec_native
import Theorems.Thm_Lax263307Proofs_NativeQptasZero_command_spec_native

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

namespace Lax263307Proofs.NativeQptasPositive
end Lax263307Proofs.NativeQptasPositive
theorem Lax263307Proofs.NativeQptasPositive.command_spec:∀ {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C) {n:Nat}
  (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)],
  @Membership.mem (SimpleGraph (Fin n)) (Set (SimpleGraph (Fin n))) (@Set.instMembership (SimpleGraph (Fin n))) (C n)
      G→
    ∀ (weights:Fin n→ Rat) (ε:Rat),
      @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
        ∀ (M w:Nat),
          Nat.le ((1:Nat)) M→
            Nat.le n M→
              (∀ (v:Fin n),Lax263307Proofs.NativeSignedArithmetic.Bounded M (weights v))→
                Lax263307Proofs.NativeSignedArithmetic.Bounded M ε→
                  Nat.lt ((0:Nat))
                      (@Lax263307Proofs.NativeQptasPositive.order n weights ε)→
                    @Lax263307Proofs.NativeQptasPositive.Bounds C i n
                        (@Lax263307Proofs.NativeQptasPositive.order n weights ε) M w ε→
                      have N:= @Lax263307Proofs.NativeQptasPositive.order n weights ε;
                      have W:= @Lax263307Proofs.NativeQptasPositive.workspace C i N ε;
                      have ext:=
                        Lax263307Proofs.NativeRootWorkspace.extent
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i) N W n;
                      Lax808846Proofs.Reasoning.Spec
                        (@HPow.hPow Nat Nat Nat
                          (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                          ((2:Nat)) w)
                        (fun (σ:Lax808846Proofs.Imp.Env) =>
                          And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                            (And
                              (Lax263307Proofs.NativeStateBounds.Bounded
                                (@HPow.hPow Nat Nat Nat
                                  (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                                  ((2:Nat)) w)
                                σ)
                              (∀ (a:String), @Eq Nat (@List.length Nat (σ.arrs a)) (ext a))))
                        (Lax263307Proofs.NativeQptasProgram.command
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.envelopeExponent C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetCoefficient C i)
                          (@Lax263307Proofs.NativeQptasImplementation.Fixed.budgetExponent C i))
                        (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                          @Eq (List Nat) τ.out
                            (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                              (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                              (@Lax263307.IndependentSetEncoding.encodeOutput n
                                (@Lax263307.WeightedAlgorithm.solve n
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.lp C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.flow C i)
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).a
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).K
                                  (@Lax263307Proofs.NativeQptasImplementation.Fixed.cfg C i).b G inst weights ε))))
                        (@Lax263307Proofs.NativeQptasPositive.cost C i n N ε):= @Lax263307Proofs.NativeQptasPositive.command_spec_native
namespace Lax263307Proofs.NativeQptasZero
end Lax263307Proofs.NativeQptasZero
theorem Lax263307Proofs.NativeQptasZero.command_spec:∀ {n:Nat} (B M:Nat),
  Nat.le ((1:Nat)) M→
    Nat.le n M→
      ∀ (cfg:Lax263307Proofs.NativeCoreMachine.Config) (C d Q e:Nat) (lp flow:List Nat→ List Nat)
        (G:SimpleGraph (Fin n)) [inst:@DecidableRel (Fin n) (Fin n) (@SimpleGraph.Adj (Fin n) G)]
        (weights:Fin n→ Rat) (ε:Rat),
        @LT.lt Rat Rat.instLT (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) ε→
          (∀ (v:Fin n),
              And (Nat.le (weights v).num.natAbs M) (Nat.le (weights v).den M))→
            And (Nat.le ε.num.natAbs M) (Nat.le ε.den M)→
              Nat.lt
                  (HAdd.hAdd
                    (HMul.hMul
                      ((2:Nat))
                      (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                        M ((4:Nat))))
                    ((3:Nat)))
                  B→
                Nat.lt
                    (HAdd.hAdd
                      (HAdd.hAdd
                        (HMul.hMul n n)
                        (HMul.hMul
                          ((3:Nat)) n))
                      ((3:Nat)))
                    B→
                  @Eq Nat
                      (∑ v:Fin n,
                        @Lax263307.WeightRounding.copies n (@Lax263307.PositiveWeights.positiveWeights n weights) ε v)
                      ((0:Nat))→
                    Lax808846Proofs.Reasoning.Spec B
                      (fun (σ:Lax808846Proofs.Imp.Env) =>
                        And (@Eq (List Nat) σ.inp (@Lax263307.IndependentSetEncoding.encodeInput n G inst weights ε))
                          (And
                            (Nat.le
                              (HAdd.hAdd
                                (HAdd.hAdd
                                  (HMul.hMul n n)
                                  (HMul.hMul
                                    ((3:Nat)) n))
                                ((3:Nat)))
                              (@List.length Nat (σ.arrs "input.data")))
                            (And (Nat.le n (@List.length Nat (σ.arrs "copy.counts")))
                              (@Eq Nat (@List.length Nat (σ.arrs "weighted.output")) n))))
                      (Lax263307Proofs.NativeQptasProgram.command cfg C d Q e)
                      (fun (σ τ:Lax808846Proofs.Imp.Env) =>
                        @Eq (List Nat) τ.out
                          (@HAppend.hAppend (List Nat) (List Nat) (List Nat)
                            (@instHAppendOfAppend (List Nat) (@List.instAppend Nat)) σ.out
                            (@Lax263307.IndependentSetEncoding.encodeOutput n
                              (@Lax263307.WeightedAlgorithm.solve n lp flow cfg.a cfg.K cfg.b G inst weights ε))))
                      (HAdd.hAdd
                        (HAdd.hAdd
                          (Lax263307Proofs.NativeBlowUp.cost n
                            ((0:Nat)))
                          (HMul.hMul
                            ((24:Nat)) n))
                        ((20:Nat))):= @Lax263307Proofs.NativeQptasZero.command_spec_native

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

def arrOf (n:ℕ) (f:ℕ→ ℕ):List ℕ:=(List.range n).map f

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

theorem Run.mono {B:ℕ} {c:Com} {σ σ':Env} {K K':ℕ} (h:Run B c σ σ' K) (hK:K≤ K'):
    Run B c σ σ' K':=by
  obtain ⟨k,hk,hbs⟩:=h; exact ⟨k,hk.trans hK,hbs⟩

end Lax808846Proofs.Reasoning

end

section

namespace Lax455465Proofs.WordSize

open Lax759944.BinaryWordEncoding

theorem bitSize_cons (x:ℕ) (xs:List ℕ):bitSize (x::xs)=x.size + 1 + bitSize xs:=by
  simp [bitSize,encode,encodeNat,Nat.size_eq_bits_len,Nat.add_comm,Nat.add_assoc]

theorem length_le (xs:List ℕ):xs.length≤ bitSize xs:=by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [bitSize_cons]; simp only [List.length_cons]; omega

theorem member_size (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x.size + 1≤ bitSize xs:=by
  induction xs with
  | nil => cases hx
  | cons y ys ih =>
    rw [bitSize_cons]
    rcases List.mem_cons.mp hx with he | ht
    · subst x; omega
    · have h:=ih ht; omega

theorem member_bound (xs:List ℕ) (x:ℕ) (hx:x∈ xs):x < 2 ^ bitSize xs:=
  (Nat.lt_size_self x).trans_le (Nat.pow_le_pow_right (by decide) (by have:=member_size xs x hx; omega))

end Lax455465Proofs.WordSize

end

section

namespace Lax263307Proofs.RecursionDepth

open Lax263307.RecursionDepth Lax263307.WeightedIndependentSet

theorem depth_le_twice_exponent (L n:ℕ) (hn:n≤ 2 ^ L):depth n≤ 2 * L:=by
  induction L generalizing n with
  | zero =>
    have:n≤ 1:=by simpa using hn
    simp [depth,this]
  | succ L ih =>
    by_cases hn₁:n≤ 1
    · simp [depth,hn₁]
    · rw [depth.eq_def n,if_neg hn₁]
      by_cases ha:2 * n / 3≤ 1
      · rw [depth.eq_def (2 * n / 3),if_pos ha]
        omega
      · rw [depth.eq_def (2 * n / 3),if_neg ha]
        have hb:2 * (2 * n / 3) / 3≤ 2 ^ L:=by
          rw [pow_succ] at hn
          omega
        have:=ih _ hb
        omega

theorem logarithmic_bound (n:ℕ):depth n≤ 2 * (Nat.log2 n + 1):=by
  apply depth_le_twice_exponent
  rw [Nat.log2_eq_log_two]
  exact (Nat.lt_pow_succ_log_self Nat.one_lt_two n).le

end Lax263307Proofs.RecursionDepth

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

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def realVector {n:ℕ} (x:Fin n→ ℚ):Fin n→ ℝ:=fun j => x j

end Lax109476.RationalCertificates

end

section

namespace Lax808846Proofs.Reasoning.Lib

open Lax808846Proofs.Imp

def upd (f:ℕ→ ℕ) (k v:ℕ):ℕ→ ℕ:=fun i => if i=k then v else f i

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

namespace Fill

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

namespace Lax263307.HeavyConditioning

open LinearRelaxation Entropy

noncomputable def probabilityFloor (n p:ℕ):ℝ:=
  1 / (2 * (n:ℝ) * p * ((Nat.log2 n:ℝ) + 1))

end Lax263307.HeavyConditioning

end

section

namespace Lax263307.RationalProjection

open Lax109476.LinearProgram Lax109476.RationalCertificates
open DistanceProjection

def Correct {m n:ℕ} (P:Program ℚ m n) (center:Fin n→ ℚ) (ρ:ℚ):
    Outcome n→ Prop
  | .near y => PrimalFeasible (toReal P) (realVector y)∧
      ∀ j, |(y j:ℝ) - (center j:ℝ)|≤ (ρ:ℝ)
  | .far a α => (∑ j, |(a j:ℝ)|)≤ 1∧
      (∀ y,PrimalFeasible (toReal P) y→ (∑ j, (a j:ℝ) * y j)≤ (α:ℝ))∧
      (ρ:ℝ) < (∑ j, (a j:ℝ) * (center j:ℝ)) - (α:ℝ)
  | .reject => ¬ IsFeasible (toReal P)

end Lax263307.RationalProjection

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

namespace Lax263307Proofs.RecursiveAlgorithm

open Lax263307.RecursiveAlgorithm Lax263307.ComputedSeparators
open Lax263307.GraphClasses Lax263307.AlgorithmParameters

theorem accuracy_budget (n:ℕ) (ε:ℚ) (hε:0 < ε):
    4≤ accuracyDenominator n ε∧
      (Lax263307.RecursionDepth.depth n:ℚ) * (4 / accuracyDenominator n ε)≤ ε:=by
  let E:= ⌈ε⁻¹⌉₊
  let d:=Lax263307.RecursionDepth.depth n
  have hE:0 < E:=Nat.ceil_pos.mpr (inv_pos.mpr hε)
  have hEq:(0:ℚ) < E:=Nat.cast_pos.mpr hE
  have hdq:(0:ℚ) < (d+1:ℕ):=Nat.cast_pos.mpr (by omega)
  have hD:4≤ accuracyDenominator n ε:=by
    change 4≤ 4 * (d+1) * E
    nlinarith only [Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hE)]
  refine ⟨hD, ?_⟩
  have hceil:ε⁻¹≤ (E:ℚ):=Nat.le_ceil _
  have hprod:1≤ ε * (E:ℚ):=by
    have hh:=mul_le_mul_of_nonneg_left hceil hε.le
    simpa only [mul_inv_cancel₀ hε.ne'] using hh
  have hdiv:1 / (E:ℚ)≤ ε:=(div_le_iff₀ hEq).mpr (by nlinarith only [hprod])
  apply le_trans _ hdiv
  change (d:ℚ) * (4 / (4 * (d+1) * E:ℕ))≤ 1 / (E:ℚ)
  push_cast
  apply (le_div_iff₀ hEq).mpr
  have hd:(0:ℚ) < (d:ℚ)+1:=by positivity
  field_simp
  ring_nf
  linarith

end Lax263307Proofs.RecursiveAlgorithm

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeRecursiveOracle

open Matrix
open Lax263307 GraphClasses AlgorithmParameters ComputedSeparators
open Lax109476.LinearProgram Lax109476.RationalCertificates

def child {n:ℕ} (lp flow:List ℕ→ List ℕ) (a K b D fuel:ℕ)
    (G:SimpleGraph (Fin n)) [DecidableRel G.Adj] (S:Finset (Fin n)) (t:ℕ):Option (Finset (Fin n)):=
  (RecursiveAlgorithm.attempt lp flow a K b D fuel (restriction G S) t).map
    (fun I => I.image (label S))

end Lax263307Proofs.NativeRecursiveOracle

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeWeightReduction

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs.RamVirtualState
open Lax263307Proofs.NativeFrontend
open Lax263307.WeightedIndependentSet Lax263307.WeightRounding

def emit:Com:=.seq (.assign "emit.count" (.var "input.n"))
  (Lax455465Proofs.RamEmitWords.command "copy.counts" 1)

def command:Com:=.seq prepare emit

open Lax109476Proofs

end Lax263307Proofs.NativeWeightReduction

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

namespace Lax263307Proofs.NativeAppendBuffer

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target index cursor count:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars count=xs.length
  counter:σ.vars index≤ xs.length
  position:σ.vars cursor=front.length+σ.vars index
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars index)) target σ

end Lax263307Proofs.NativeAppendBuffer

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

namespace Lax263307Proofs.NativeUniformWordGuards

theorem scalar (v w:ℕ) (h:v≤ w):v<2^w:=h.trans_lt Nat.lt_two_pow_self

theorem virtual (u w:ℕ) (h:2*u+4≤ w):2*(2^u)^2+3<2^w:=by
  have hpow:2^(u*2+4)≤2^w:=Nat.pow_le_pow_right (by decide) (by omega)
  rw [pow_add] at hpow
  norm_num at hpow
  rw [←pow_mul]
  have hp:=Nat.two_pow_pos (u*2)
  nlinarith only [hpow,hp]

end Lax263307Proofs.NativeUniformWordGuards

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

namespace Lax263307Proofs.NativeChildReturn

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 ComputedSeparators NativeMasks

def command:Com:=.ite (.eq (.var "recursion.return.tag") (.lit 1)) liftCommand
  (.assign "lift.mask" (.lit 0))

end Lax263307Proofs.NativeChildReturn

end

section

namespace Lax263307Proofs.NativeBlockAppend

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState

structure Invariant (source target:String) (front xs:List ℕ) (σ:Env):Prop where
  source:Prefix xs source σ
  count:σ.vars "stack.copy.length"=xs.length
  index:σ.vars "stack.i"≤ xs.length
  position:σ.vars "stack.words"=front.length+σ.vars "stack.i"
  room:front.length+xs.length≤(σ.arrs target).length
  target:Prefix (front++xs.take (σ.vars "stack.i")) target σ

end Lax263307Proofs.NativeBlockAppend

end

section

namespace Lax263307Proofs.NativeStateBounds

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

theorem initial {B:ℕ} (ext:String→ ℕ) {xs:List ℕ} (hB:0< B)
    (hx:∀ z∈xs,z< B):Bounded B (initEnv ext xs):=by
  refine ⟨fun _ => hB,?_,hx⟩
  intro a z hz
  have he:z=0:=(List.mem_replicate.mp hz).2
  simpa only [he] using hB

end Lax263307Proofs.NativeStateBounds

end

section

namespace Lax263307Proofs.NativeOracleContext

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax109476.RationalEncoding
open Lax263307 NativeCoreMachine NativeMachineSegment

def scalars:List String:= ["graph.n","catalog.count","moment.r",
  "conditioning.k","conditioning.p","algorithm.D","class.B","algorithm.load",
  "node.D","node.floorPower","node.programLength","round.limit","algorithm.roundWidth",
  "stack.words","recursion.stride","recursion.fuel","frame.length"]

end Lax263307Proofs.NativeOracleContext

end

section

namespace Lax263307Proofs.NativePolynomialEnvelope

def Bounded (f:ℕ→ ℕ):Prop:= ∃ P:Polynomial ℕ,∀ R,f R≤ P.eval R

theorem eval (P:Polynomial ℕ) {f:ℕ→ ℕ} (hf:Bounded f):Bounded (fun R => P.eval (f R)):=by
  obtain ⟨Q,hQ⟩:=hf
  exact ⟨P.comp Q,fun R => by simpa only [Polynomial.eval_comp] using NativeFlowQueryResources.eval_mono P (hQ R)⟩

end Lax263307Proofs.NativePolynomialEnvelope
end

section

namespace Lax263307Proofs.NativeInputBounds

open Lax263307.IndependentSetEncoding

open Lax263307 WeightedIndependentSet

def magnitude {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):ℕ:=2^height w ε

theorem parameter_length {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):
    (encodeParameters w ε).length=3*n+3:=by
  simp [encodeParameters,encodeRational,List.length_flatMap,List.sum_ofFn,Finset.sum_const,Nat.mul_comm]

theorem order_le_bits {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):n≤ rationalBitSize w ε:=by
  have h:=Lax455465Proofs.WordSize.length_le (encodeParameters w ε)
  rw [parameter_length] at h
  change 3*n+3≤ rationalBitSize w ε at h
  omega

theorem parameters_bound {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):
    ∀ z∈encodeParameters w ε,z< magnitude w ε:=by
  intro z hz
  exact (Lax455465Proofs.WordSize.member_bound _ _ hz).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp [height,rationalBitSize]; omega))

theorem weight_bounds {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):
    ∀ v,(w v).num.natAbs≤ magnitude w ε∧ (w v).den≤ magnitude w ε:=by
  intro v
  have hp:encodeRational (w v)⊆encodeParameters w ε:=by
    intro z hz
    apply List.mem_append_left
    apply List.mem_flatMap.mpr
    exact ⟨w v,List.mem_ofFn.mpr ⟨v,rfl⟩,hz⟩
  exact ⟨(parameters_bound w ε _ (hp (by simp [encodeRational]))).le,
    (parameters_bound w ε _ (hp (by simp [encodeRational]))).le⟩

theorem accuracy_bounds {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):
    ε.num.natAbs≤ magnitude w ε∧ ε.den≤ magnitude w ε:=by
  exact ⟨(parameters_bound w ε _ (List.mem_append_right _ (by simp [encodeRational]))).le,
    (parameters_bound w ε _ (List.mem_append_right _ (by simp [encodeRational]))).le⟩

theorem magnitude_positive {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):1≤ magnitude w ε:=
  Nat.one_le_pow _ _ (by decide)

theorem order_bound {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ):n< magnitude w ε:=by
  have h:=order_le_bits w ε
  have hp:rationalBitSize w ε+1<2^(rationalBitSize w ε+1):=Nat.lt_two_pow_self
  dsimp [magnitude,height]
  omega

theorem input_bound {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w:Fin n→ ℚ) (ε:ℚ):∀ z∈encodeInput G w ε,z< magnitude w ε:=by
  intro z hz
  simp only [encodeInput,List.mem_append,List.mem_singleton] at hz
  rcases hz with (rfl|hmatrix)|hparameters
  · exact order_bound w ε
  · simp only [List.mem_flatten,List.mem_ofFn] at hmatrix
    obtain ⟨row,⟨u,rfl⟩,hz⟩:=hmatrix
    obtain ⟨v,rfl⟩:=List.mem_ofFn.mp hz
    have hp:1< magnitude w ε:=by
      dsimp [magnitude,height]
      have h:=Nat.two_pow_pos (rationalBitSize w ε)
      rw [pow_succ]
      omega
    split_ifs <;> omega
  · exact parameters_bound w ε _ hparameters

end Lax263307Proofs.NativeInputBounds

end

section

set_option maxHeartbeats 0
set_option maxRecDepth 30000

namespace Lax263307Proofs.NativeQptasPositive

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses BlowUpClasses WeightedIndependentSet
open NativeQptasImplementation NativeRootWorkspace

theorem positive_parameters {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ) (hN:0< order weights ε):
    0< n∧ 0< WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
  have hn:0< n:=by
    by_contra hn
    have hz:n=0:=by omega
    subst n
    simpa [order] using hN
  refine ⟨hn,?_⟩
  by_contra hmax
  have hmax:WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights)≤ 0:=le_of_not_gt hmax
  have hz (v:Fin n):PositiveWeights.positiveWeights weights v=0:=by
    have hle:PositiveWeights.positiveWeights weights v≤ WeightRounding.maximumWeight (PositiveWeights.positiveWeights weights):=by
      apply Finset.le_max'; simp
    exact le_antisymm (hle.trans hmax) (le_max_right _ _)
  have hc (v:Fin n):copies weights ε v=0:=by
    simp [copies,WeightRounding.copies,WeightRounding.roundedCopies,hz v]
  have he:order weights ε=0:=by simp only [order,hc,Finset.sum_const_zero]
  omega

end Lax263307Proofs.NativeQptasPositive

end

section

namespace Lax263307Proofs.NativeFinalBounds

open Lax263307 AlgorithmParameters RecursiveAlgorithm

theorem original_order_le_copy_order {n:ℕ} (w:Fin n→ ℚ) (ε:ℚ)
    (hn:0< n) (hε:0<ε) (hε1:ε≤1) (hW:0< WeightRounding.maximumWeight w):
    n≤∑ v,WeightRounding.copies w ε v:=by
  classical
  have hmem:WeightRounding.maximumWeight w∈insert 0 (Finset.univ.image w):=
    Finset.max'_mem _ _
  obtain ⟨v,hv⟩:∃ v,w v=WeightRounding.maximumWeight w:=by
    rcases Finset.mem_insert.mp hmem with hz|himage
    · exact False.elim (by linarith)
    · obtain ⟨v,_,he⟩:=Finset.mem_image.mp himage
      exact ⟨v,he⟩
  have hquot:w v/WeightRounding.scale w ε=2*(n:ℚ)/ε:=by
    rw [hv]
    unfold WeightRounding.scale
    have hnQ:(n:ℚ)≠0:=by exact_mod_cast hn.ne'
    field_simp [hW.ne',hε.ne',hnQ]
  have hc:n≤ WeightRounding.copies w ε v:=by
    dsimp [WeightRounding.copies,WeightRounding.roundedCopies]
    apply Nat.le_floor
    rw [hquot]
    apply (le_div_iff₀ hε).mpr
    have hmul:=mul_le_mul_of_nonneg_left hε1 (show (0:ℚ)≤ n by positivity)
    nlinarith
  exact hc.trans (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ v))

end Lax263307Proofs.NativeFinalBounds

end

section

set_option maxHeartbeats 0

namespace Lax263307Proofs.NativeQptasWordBounds

open Lax263307.IndependentSetEncoding

open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation NativeQptasPositive

theorem shape_bound (n N:ℕ):n*n+N*N+3*n+3*N+100≤ shape n N:=by
  have hs:n*n+N*N+3*n+3*N+100≤ 100*(n+N+1)^2:=by
    nlinarith only [Nat.zero_le (n^2),Nat.zero_le (N^2),Nat.zero_le (n*N),Nat.zero_le n,Nat.zero_le N]
  exact hs.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_right (by omega) (by decide:2≤ 4)))

theorem accuracy_coefficient (n N:ℕ):
    3+8*(RecursionDepth.depth N+1)+2*N+RecursionDepth.depth N+40≤ shape n N:=by
  have hd:=Lax263307Proofs.RecursionDepth.logarithmic_bound N
  have hl:=Nat.log2_le_self N
  have hs:n+N+1≤ (n+N+1)^4:=le_self_pow (by omega) (by decide)
  dsimp only [shape]
  omega

theorem basic {C:GraphClass} (i:Fixed C) {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ):
    let N:=order weights ε
    let M:=NativeInputBounds.magnitude weights ε
    let w:=width i weights ε
    0< w∧ 2*M^4+3<2^w∧ n*n+3*n+3<2^w∧ n*n+N*N+n+N+3<2^w∧
      N*N+N+5<2^w∧ n+N+5<2^w∧
      3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w:=by
  dsimp only
  let N:=order weights ε
  let H:=NativeInputBounds.height weights ε
  let M:=NativeInputBounds.magnitude weights ε
  let w:=width i weights ε
  have hH:1≤ H:=by dsimp only [H,NativeInputBounds.height]; omega
  have hwidth:NativeRootWorkspace.hostHeight i.cfg (workspace i N ε)+
      NativeRootBudget.guard i.envelopeCoefficient i.envelopeExponent i.budgetCoefficient i.budgetExponent N (denominator N ε)+
      shape n N+16*H+100=w:=rfl
  have hs:=shape_bound n N
  have hscalar:n*n+N*N+3*n+3*N+100<2^w:=
    hs.trans_lt ((by omega:shape n N≤ w).trans_lt Nat.lt_two_pow_self)
  have hfrontend:2*M^4+3<2^w:=by
    have hv:=NativeUniformWordGuards.virtual (2*H) w (by omega)
    have he:(2^H)^4=(2^(2*H))^2:=by rw [←pow_mul,←pow_mul]; congr 1; omega
    simpa only [M,NativeInputBounds.magnitude,←he] using hv
  have haccuracy:3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w:=by
    have hm:1≤ M:=NativeInputBounds.magnitude_positive weights ε
    have hc:=accuracy_coefficient n N
    have hprod:3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40≤ shape n N*M:=by
      nlinarith only [hc,Nat.mul_le_mul_right M hc,hm,
        Nat.le_mul_of_pos_right (2*N+RecursionDepth.depth N+40) hm]
    have hexp:shape n N+H< w:=by omega
    calc
      _≤ shape n N*M:=hprod
      _≤ 2^(shape n N)*2^H:=Nat.mul_le_mul_right _ Nat.lt_two_pow_self.le
      _=2^(shape n N+H):=(pow_add _ _ _).symm
      _ < 2^w:=Nat.pow_lt_pow_right (by decide) hexp
  change 0< w∧ 2*M^4+3<2^w∧ n*n+3*n+3<2^w∧ n*n+N*N+n+N+3<2^w∧
    N*N+N+5<2^w∧ n+N+5<2^w∧
    3*M+8*(RecursionDepth.depth N+1)*M+2*N+RecursionDepth.depth N+40<2^w
  exact ⟨by omega,hfrontend,by omega,by omega,by omega,by omega,haccuracy⟩

theorem input {C:GraphClass} (i:Fixed C) {n:ℕ} (G:SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (weights:Fin n→ ℚ) (ε:ℚ):∀ z∈encodeInput G weights ε,z<2^width i weights ε:=by
  intro z hz
  exact (NativeInputBounds.input_bound G weights ε z hz).trans_le
    (Nat.pow_le_pow_right (by decide) (by dsimp only [width]; omega))

theorem positive {C:GraphClass} (i:Fixed C) {n:ℕ} (weights:Fin n→ ℚ) (ε:ℚ)
    (hε:0<ε) (hε1:ε<1) (hN:0< order weights ε):
    NativeQptasPositive.Bounds i n (order weights ε) (NativeInputBounds.magnitude weights ε) (width i weights ε) ε:=by
  let N:=order weights ε
  let D:=denominator N ε
  let R:=resource i N ε
  let W:=workspace i N ε
  have hp:=positive_parameters weights ε hN
  have hnN:n≤ N:=NativeFinalBounds.original_order_le_copy_order
    (PositiveWeights.positiveWeights weights) ε hp.1 hε hε1.le hp.2
  have hD:4≤ D:=(Lax263307Proofs.RecursiveAlgorithm.accuracy_budget N (ε/2) (by positivity)).1
  have hr:=i.uniform N D N (by omega) hN (Nat.le_refl N)
  change ParameterResources.resource i.cfg.a i.cfg.K i.cfg.b N D≤ R at hr
  have hNR:N≤ R:=by dsimp only [ParameterResources.resource] at hr; omega
  have hnR:n≤ R:=hnN.trans hNR
  have budget:=i.budget R
  change NativeSelectedBudget.demand i.cfg i.projection i.separator i.roundedConstant R≤ W at budget
  dsimp only [NativeSelectedBudget.demand] at budget
  have allocation:n*n+N*N+3*n+N+3≤ W:=by
    have hn2:=Nat.mul_self_le_mul_self hnR
    have hN2:=Nat.mul_self_le_mul_self hNR
    have hs:n*n+N*N+3*n+N+3≤ 10*(R+1)^2:=by nlinarith only [hn2,hN2,hnR,hNR]
    have hpow:=Nat.pow_le_pow_right (by omega:1≤ R+1) (by decide:2≤ 4)
    have hc:10≤ NativeEntryResources.coefficient i.cfg:=by dsimp only [NativeEntryResources.coefficient]; omega
    have he:10*(R+1)^2≤ NativeEntryResources.amount i.cfg R:=
      Nat.mul_le_mul hc hpow
    exact (hs.trans he).trans (by omega)
  have hb:=basic i weights ε
  refine ⟨allocation,hb.2.1,hb.2.2.1,hb.2.2.2.1,hb.2.2.2.2.1,hb.2.2.2.2.2.2,?_,?_,hb.2.2.2.2.2.1⟩
  · apply NativeUniformWordGuards.scalar
    dsimp only [width]
    omega
  · dsimp only [width]
    omega

end Lax263307Proofs.NativeQptasWordBounds

end

section

namespace Lax263307Proofs.NativeWeightedExecution

open Lax263307.IndependentSetEncoding

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax455465Proofs Lax455465Proofs.RamVirtualState
open Lax263307 GraphClasses WeightedIndependentSet
open NativeQptasImplementation

def zeroExtent (n:ℕ) (a:String):ℕ:=if a="weighted.output" then n else n*n+3*n+3

theorem command_spec {C:GraphClass} (i:Fixed C) {n:ℕ} (G:SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hG:G∈C n) (weights:Fin n→ ℚ) (ε:ℚ) (hε:0<ε) (hε1:ε<1):
    ∃ (I:Finset (Fin n)) (ext:String→ ℕ),IsApproximation G weights ε I∧
      Spec (2^NativeQptasWordBounds.width i weights ε)
        (fun σ => σ=initEnv ext (encodeInput G weights ε)) (command i)
        (fun _ τ => τ.out=encodeOutput I) (cost i weights ε):=by
  let N:=NativeQptasPositive.order weights ε
  let M:=NativeInputBounds.magnitude weights ε
  let w:=NativeQptasWordBounds.width i weights ε
  let I:=WeightedAlgorithm.solve i.lp i.flow i.cfg.a i.cfg.K i.cfg.b G weights ε
  have hM:=NativeInputBounds.magnitude_positive weights ε
  have hnM:=(NativeInputBounds.order_bound weights ε).le
  have hw:=NativeInputBounds.weight_bounds weights ε
  have hεM:=NativeInputBounds.accuracy_bounds weights ε
  have hb:=NativeQptasWordBounds.basic i weights ε
  have hinitial (ext:String→ ℕ):NativeStateBounds.Bounded (2^w) (initEnv ext (encodeInput G weights ε)):=
    NativeStateBounds.initial ext (Nat.two_pow_pos w) (NativeQptasWordBounds.input i G weights ε)
  have lengths (ext:String→ ℕ) (a:String):
      ((initEnv ext (encodeInput G weights ε)).arrs a).length=ext a:=List.length_replicate
  by_cases hz:N=0
  · let ext:=zeroExtent n
    refine ⟨I,ext,i.semantic n G hG weights ε hε hε1,?_⟩
    intro σ hσ
    subst σ
    have zero:=NativeQptasZero.command_spec (2^w) M hM hnM i.cfg i.envelopeCoefficient i.envelopeExponent
      i.budgetCoefficient i.budgetExponent i.lp i.flow G weights ε hε hw hεM hb.2.1 hb.2.2.1 hz
    obtain ⟨τ,rr,out⟩:=zero (initEnv ext (encodeInput G weights ε))
      ⟨rfl,by rw [lengths]; simp [ext,zeroExtent],by rw [lengths]; simp [ext,zeroExtent]; omega,
        by rw [lengths]; simp [ext,zeroExtent]⟩
    refine ⟨τ,rr.mono ?_,?_⟩
    · change NativeBlowUp.cost n 0+24*n+20≤ cost i weights ε
      change NativeBlowUp.cost n 0+24*n+20≤ NativeQptasPositive.cost i n N ε
      rw [hz]
      dsimp only [NativeQptasPositive.cost]
      omega
    · simpa only [initEnv,List.nil_append] using out
  · have hN:0< N:=by omega
    let W:=NativeQptasPositive.workspace i N ε
    let ext:=NativeRootWorkspace.extent i.cfg N W n
    refine ⟨I,ext,i.semantic n G hG weights ε hε hε1,?_⟩
    intro σ hσ
    subst σ
    obtain ⟨τ,rr,out⟩:=NativeQptasPositive.command_spec i G hG weights ε hε M w hM hnM hw hεM hN
      (NativeQptasWordBounds.positive i weights ε hε hε1 hN) (initEnv ext (encodeInput G weights ε))
      ⟨rfl,hinitial ext,lengths ext⟩
    exact ⟨τ,rr,by simpa only [initEnv,List.nil_append] using out⟩

end Lax263307Proofs.NativeWeightedExecution

end

theorem solution:∀ {C:Lax263307.GraphClasses.GraphClass} (i:Lax263307Proofs.NativeQptasImplementation.Fixed C) {n:ℕ}
  (G:SimpleGraph (Fin n)) [inst:DecidableRel G.Adj],
  G∈ C n→
    ∀ (weights:Fin n→ ℚ) (ε:ℚ),
      0 < ε→
        ε < 1→
          ∃ (I:Finset (Fin n)) (ext:String→ ℕ),
            Lax263307.WeightedIndependentSet.IsApproximation G weights ε I∧
              Lax808846Proofs.Reasoning.Spec (2 ^ Lax263307Proofs.NativeQptasWordBounds.width i weights ε)
                (fun (σ:Lax808846Proofs.Imp.Env) =>
                  σ=Lax808846Proofs.Imp.initEnv ext (Lax263307.IndependentSetEncoding.encodeInput G weights ε))
                (Lax263307Proofs.NativeWeightedExecution.command i)
                (fun (x τ:Lax808846Proofs.Imp.Env) => τ.out=Lax263307.IndependentSetEncoding.encodeOutput I)
                (Lax263307Proofs.NativeWeightedExecution.cost i weights ε):= @Lax263307Proofs.NativeWeightedExecution.command_spec
