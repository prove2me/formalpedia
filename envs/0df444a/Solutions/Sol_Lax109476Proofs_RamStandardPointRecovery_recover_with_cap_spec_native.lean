-- Prove2me | solution 1 for Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:13:54.350595+00:00
-- url     : https://prove2.me/submissions/7f5b3b16-f9ef-424e-8098-07a764346123

import Mathlib.Tactic
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.WellFounded
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativePhaseInterfaces
import Theorems.Thm_Lax109476Proofs_RamPointInitialization_recover_spec_native

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

namespace Lax109476Proofs.RamPointInitialization
end Lax109476Proofs.RamPointInitialization
theorem Lax109476Proofs.RamPointInitialization.recover_spec:∀ (m n S C N D w:Nat) (P:Lax109476.LinearProgram.Program Rat m n) (x:Fin n→ Rat),
  LE.le D.size C→
    LE.le
        (HAdd.hAdd
          (HMul.hMul ((4:Nat))
            C)
          ((2:Nat)))
        S→
      LE.le
          (HAdd.hAdd (Lax109476Proofs.RamRationalReconstruction.depthBound S)
            ((1:Nat)))
          N→
        LE.le (Lax109476Proofs.RamPointRecoveryBounds.wordWidth m n S) w→
          (∀ (i:Fin m) (j:Fin n),
              Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.A Rat m n P i j)
                (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                  ((2:Nat)) S))→
            (∀ (i:Fin m),
                Lax109476Proofs.RationalArithmeticBounds.Height (@Lax109476.LinearProgram.Program.b Rat m n P i)
                  (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                    ((2:Nat)) S))→
              (∀ (j:Fin n),
                  Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                    (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                      ((2:Nat)) S))→
                (∀ (j:Fin n),
                    @Eq Rat (@Lax109476.LinearProgram.Program.c Rat m n P j)
                      (@OfNat.ofNat Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))))→
                  @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                      (@Lax109476.RationalCertificates.toReal m n P) (@Lax109476.RationalCertificates.realVector n x)→
                    (∀ (i:Fin n) (y:Fin n→ Real),
                        @Lax109476.LinearProgram.PrimalFeasible Real Real.instRing Real.partialOrder m n
                            (@Lax109476.RationalCertificates.toReal m n P) y→
                          (∀ (j:Fin n),
                              @LT.lt (Fin n) (@instLTFin n) j i→
                                @Eq Real (y j) (@Rat.cast Real Real.instRatCast (x j)))→
                            @LE.le Real Real.instLE (@Rat.cast Real Real.instRatCast (x i)) (y i))→
                      (∀ (j:Fin n),
                          And (@LE.le Rat Rat.instLE (x j) (@Nat.cast Rat Rat.instNatCast D))
                            (LE.le (x j).den D))→
                        Lax808846Proofs.Reasoning.Spec
                          (@HPow.hPow Nat Nat Nat
                            (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
                            ((2:Nat)) w)
                          (fun (σ:Lax808846Proofs.Imp.Env) =>
                            And (@Lax109476Proofs.RamPointInitialization.Base m n P σ)
                              (And (Lax109476Proofs.RamRecoveryThreshold.Workspace m n σ)
                                (And (Lax109476Proofs.RamEllipsoidStep.Extents "point.x" n σ)
                                  (And (@Eq Nat (σ.vars "minimum.bound") D)
                                    (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))))
                          Lax109476Proofs.RamPointInitialization.recover
                          (fun (x_1 τ:Lax808846Proofs.Imp.Env) =>
                            And (@Lax109476Proofs.RamRecoveryThreshold.Persistent m n P x n τ)
                              (And (@Eq Nat (τ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (τ.arrs "cf.stack")) N)))
                          (HAdd.hAdd
                            (HAdd.hAdd
                              (HMul.hMul
                                ((33:Nat)) n)
                              ((22:Nat)))
                            (Lax109476Proofs.RamPointRecoveryBounds.instructionBound m n S C)):= @Lax109476Proofs.RamPointInitialization.recover_spec_native

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

open Matrix

namespace Lax109476Proofs.Elimination

lemma mulVec_lastCases_split
    {m:Type*} {F:Type*} [Semiring F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F)
    (xₙ:F)
    (x':Fin n→ F)
    (i:m):
    A.mulVec (Fin.lastCases xₙ x') i
     =(A.submatrix id Fin.castSucc i ⬝ᵥ x') + A i (Fin.last n) * xₙ:=by
  simp [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc]

lemma dotProduct_mul_right
  {F:Type*} [CommSemiring F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F):
    ((fun j:Fin n => a j * c) ⬝ᵥ x)=(a ⬝ᵥ x) * c:=by
  calc
    ((fun j:Fin n => a j * c) ⬝ᵥ x)
       =∑ j:Fin n, (a j * c) * x j:=by simp [dotProduct]
    _=∑ j:Fin n, (a j * x j) * c:=by
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring
    _=(∑ j:Fin n,a j * x j) * c:=by
          rw [← Finset.sum_mul]
    _=(a ⬝ᵥ x) * c:=by simp [dotProduct]

lemma dotProduct_scaled_inv_mul
    {F:Type*} [Field F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F)
    (hc:c ≠ 0):
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x) * c=a ⬝ᵥ x:=by
  calc
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x) * c
       =((a ⬝ᵥ x) * c⁻¹) * c:=by
            rw [dotProduct_mul_right]
    _=a ⬝ᵥ x:=by
          field_simp [hc]

lemma dotProduct_mul_inv
  {F:Type*} [Field F] {n:ℕ}
    (a x:Fin n→ F)
    (c:F):
    ((fun j:Fin n => a j * c⁻¹) ⬝ᵥ x)=(a ⬝ᵥ x) * c⁻¹:=by
  simpa using dotProduct_mul_right a x c⁻¹

lemma split_add_mul_inv
    {F:Type*} [Field F]
    (u x c:F)
    (hc:c ≠ 0):
    ((u + c * x) * c⁻¹)=u * c⁻¹ + x:=by
  calc
    ((u + c * x) * c⁻¹)
       =u * c⁻¹ + (c * x) * c⁻¹:=by ring
    _=u * c⁻¹ + x:=by
          have hx:(c * x) * c⁻¹=x:=by
            calc
              (c * x) * c⁻¹=x * (c * c⁻¹):=by ring
              _=x:=by simp [mul_inv_cancel₀ hc]
          simp [hx]

lemma mul_inv_cancel_right
    {F:Type*} [Field F]
    (a c:F)
    (hc:c ≠ 0):
    (a * c⁻¹) * c=a:=by
  calc
    (a * c⁻¹) * c=a * (c⁻¹ * c):=by ring
    _=a:=by simp [inv_mul_cancel₀ hc]

lemma upper_bound_from_linear_pos
  {F:Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c:F)
    (hc:0 < c)
    (hlin:u + c * x≤ b):
    x + u * c⁻¹≤ b * c⁻¹:=by
  have hscaled:(u + c * x) * c⁻¹≤ b * c⁻¹:=
    mul_le_mul_of_nonneg_right hlin (inv_nonneg.mpr (le_of_lt hc))
  calc
    x + u * c⁻¹=u * c⁻¹ + x:=by ring
    _=(u + c * x) * c⁻¹:=by
          symm
          exact split_add_mul_inv u x c (ne_of_gt hc)
    _≤ b * c⁻¹:=hscaled

lemma lower_bound_from_linear_neg
  {F:Type*} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    (u x b c:F)
    (hc:c < 0)
    (hlin:u + c * x≤ b):
    b * c⁻¹≤ x + u * c⁻¹:=by
  have hscaled:b * c⁻¹≤ (u + c * x) * c⁻¹:=
    mul_le_mul_of_nonpos_right hlin (inv_nonpos.mpr (le_of_lt hc))
  calc
    b * c⁻¹≤ (u + c * x) * c⁻¹:=hscaled
    _=u * c⁻¹ + x:=split_add_mul_inv u x c (ne_of_lt hc)
    _=x + u * c⁻¹:=by ring

end Lax109476Proofs.Elimination

end

section

universe u v

namespace Lax109476Proofs.Elimination

private lemma finite_bounds_witness
    {ι:Type*} [Finite ι]
    {κ:Type*} [Finite κ]
    {F:Type*} [Lattice F]
    (h_nonempty:Nonempty F)
    (lhss:ι→ F)
    (rhss:κ→ F)
    (h:∀ i j,lhss i≤ rhss j):
    ∃ x:F, ((∀ i,lhss i≤ x)∧ (∀ j,x≤ rhss j)):=by
  let:=Fintype.ofFinite ι
  let:=Fintype.ofFinite κ
  by_cases hi:Nonempty ι
  ·
    exact ⟨ Finset.univ.sup' Finset.univ_nonempty lhss,
            fun i => Finset.univ.le_sup' lhss (Finset.mem_univ i),
            fun j => Finset.sup'_le _ _ (fun i _ => h i j) ⟩
  · by_cases hj:Nonempty κ
    ·
      exact ⟨ Finset.univ.inf' Finset.univ_nonempty rhss,
              fun i => False.elim (hi ⟨i⟩),
              fun j => Finset.univ.inf'_le _ (Finset.mem_univ j) ⟩
    ·
      obtain ⟨x⟩:=h_nonempty
      exact ⟨x,fun i => False.elim (hi ⟨i⟩),
               fun j => False.elim (hj ⟨j⟩)⟩

theorem Fourier_Motzkin
  {m:Type u}
  {F:Type v}
  [Fintype m]
  [Field F] [LinearOrder F] [IsStrictOrderedRing F]
  {n:ℕ}
  (A:Matrix m (Fin (n + 1)) F)
  (b:m→ F):
  ∃ κ:Type u, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
      (∀ i j,0≤ M i j)∧
      (∀ i, (M * A) i (Fin.last n)=0)∧
      (∀ x':Fin n→ F,
        (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b↔
          ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b):=by

  let Aₙ:m→ F:=fun i => A i (Fin.last n)
  let A₀:Matrix m (Fin n) F:=A.submatrix id Fin.castSucc

  let posRow:Finset m:=Finset.univ.filter (fun i => 0 < Aₙ i)
  let negRow:Finset m:=Finset.univ.filter (fun i => Aₙ i < 0)
  let zeroRow:Finset m:=Finset.univ.filter (fun i => Aₙ i=0)

  let κ:Type _:=((↥posRow × ↥negRow) ⊕ ↥zeroRow)

  let posCoeffs:posRow -> Fin n -> F:=fun i j => A₀ i j * (Aₙ i)⁻¹
  let posb:posRow -> F:=fun i => b i * (Aₙ i)⁻¹
  let negCoeffs:negRow -> Fin n -> F:=fun i j => A₀ i j * (Aₙ i)⁻¹
  let negb:negRow -> F:=fun i => b i * (Aₙ i)⁻¹
  let zeroCoeffs:zeroRow -> Fin n -> F:=fun i j => A₀ i j
  let zerob:zeroRow -> F:=fun i => b i

  let A':Matrix κ (Fin n) F:=fun i j => match i with
    | Sum.inl (iPos,iNeg) => posCoeffs iPos j - negCoeffs iNeg j
    | Sum.inr iZero => zeroCoeffs iZero j
  let b':κ -> F:=fun i => match i with
    | Sum.inl (iPos,iNeg) => posb iPos - negb iNeg
    | Sum.inr iZero => zerob iZero

  have hlft:∀ x:Fin (n + 1)→ F,
        A.mulVec x≤ b→ A'.mulVec (fun j => x (Fin.castSucc j))≤ b':=by
    intro x hx

    let x':Fin n→ F:=fun j => x (Fin.castSucc j)
    let xₙ:=x (Fin.last n)
    intro i
    match i with
    | Sum.inl (iPos,iNeg) =>

      have h₁:xₙ≤ posb iPos - (posCoeffs iPos) ⬝ᵥ x':=by
        have hpos:0 < Aₙ iPos:=(Finset.mem_filter.mp iPos.property).2
        have hrow_pos:=hx iPos
        have hpos_ne:Aₙ iPos ≠ 0:=ne_of_gt hpos
        have hlin_pos:
            (A₀ iPos ⬝ᵥ x') + Aₙ iPos * xₙ≤ b iPos:=by
          simpa [Matrix.mulVec,dotProduct,x',xₙ,Aₙ,Fin.sum_univ_castSucc,
            add_assoc,add_left_comm,add_comm,A₀] using hrow_pos
        have hdot_pos:
            (posCoeffs iPos) ⬝ᵥ x'=(A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹:=by
          simpa [posCoeffs] using dotProduct_mul_inv (A₀ iPos) x' (Aₙ iPos)
        have hbound_pos:xₙ + (posCoeffs iPos) ⬝ᵥ x'≤ posb iPos:=by
          calc
            xₙ + (posCoeffs iPos) ⬝ᵥ x'
               =xₙ + (A₀ iPos ⬝ᵥ x') * (Aₙ iPos)⁻¹:=by rw [hdot_pos]
            _≤ b iPos * (Aₙ iPos)⁻¹:=
              upper_bound_from_linear_pos
                (A₀ iPos ⬝ᵥ x') xₙ (b iPos) (Aₙ iPos) hpos hlin_pos
            _=posb iPos:=by simp [posb]
        simpa [le_sub_iff_add_le] using hbound_pos

      have h₂:negb iNeg - (negCoeffs iNeg) ⬝ᵥ x'≤ xₙ:=by
        have hneg:Aₙ iNeg < 0:=(Finset.mem_filter.mp iNeg.property).2
        have hrow_neg:=hx iNeg
        have hneg_ne:Aₙ iNeg ≠ 0:=ne_of_lt hneg
        have hlin_neg:
            (A₀ iNeg ⬝ᵥ x') + Aₙ iNeg * xₙ≤ b iNeg:=by
          simpa [Matrix.mulVec,dotProduct,x',xₙ,Aₙ,Fin.sum_univ_castSucc,
            add_assoc,add_left_comm,add_comm,A₀] using hrow_neg
        have hdot_neg:
            (negCoeffs iNeg) ⬝ᵥ x'=(A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹:=by
          simpa [negCoeffs] using dotProduct_mul_inv (A₀ iNeg) x' (Aₙ iNeg)
        have hbound_neg:negb iNeg≤ xₙ + (negCoeffs iNeg) ⬝ᵥ x':=by
          calc
            negb iNeg=b iNeg * (Aₙ iNeg)⁻¹:=by simp [negb]
            _≤ xₙ + (A₀ iNeg ⬝ᵥ x') * (Aₙ iNeg)⁻¹:=
              lower_bound_from_linear_neg
                (A₀ iNeg ⬝ᵥ x') xₙ (b iNeg) (Aₙ iNeg) hneg hlin_neg
            _=xₙ + (negCoeffs iNeg) ⬝ᵥ x':=by rw [hdot_neg]
        simpa [sub_le_iff_le_add] using hbound_neg

      have h_combined:(posCoeffs iPos) ⬝ᵥ x' - negCoeffs iNeg ⬝ᵥ x'
                          ≤ posb iPos - negb iNeg:=by
        linarith [h₁,h₂]
      simpa [A',b',Matrix.mulVec,dotProduct,sub_mul,Finset.sum_sub_distrib] using h_combined

    | Sum.inr iZero =>

      simp only [A',b',Matrix.mulVec,zeroCoeffs,zerob]
      have hzero:Aₙ iZero=0:=(Finset.mem_filter.mp iZero.property).2
      have hzero':A iZero (Fin.last n)=0:=by simpa [Aₙ] using hzero
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,hzero',A₀,x'] using hx iZero

  have hright:∀ x':Fin n→ F,
        A'.mulVec x'≤ b'→ ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b:=by
    intro x' hsol

    let valpos:posRow→ F:=fun i => posb i - (posCoeffs i) ⬝ᵥ x'
    let valneg:negRow→ F:=fun i => negb i - (negCoeffs i) ⬝ᵥ x'

    have hbounds:∀ iNeg iPos,valneg iNeg≤ valpos iPos:=by
      intro iNeg iPos
      have:=hsol (Sum.inl (iPos,iNeg))
      dsimp [A',b'] at this
      have hlin:
          (posCoeffs iPos) ⬝ᵥ x' - (negCoeffs iNeg) ⬝ᵥ x'≤ posb iPos - negb iNeg:=by
        simpa [Matrix.mulVec,dotProduct,sub_mul,Finset.sum_sub_distrib] using this
      have hbound:
          negb iNeg - (negCoeffs iNeg) ⬝ᵥ x'≤
        posb iPos - (posCoeffs iPos) ⬝ᵥ x':=by
        linarith [hlin]
      simpa [valpos,valneg] using hbound

    obtain ⟨xₙ,h_xₙn,h_xₙp⟩:=finite_bounds_witness ⟨0⟩ valneg valpos hbounds

    let x:Fin (n + 1)→ F:=Fin.lastCases xₙ x'

    refine ⟨xₙ,fun i => ?_⟩
    by_cases hlast:Aₙ i=0

    · let iZero:zeroRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hlast⟩⟩
      have hlast':A i (Fin.last n)=0:=by simpa [Aₙ] using hlast
      simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_castSucc,hlast',x,A',b',zeroCoeffs,zerob,A₀,iZero]
        using hsol (Sum.inr iZero)
    · cases lt_or_gt_of_ne hlast with
      | inl hneg =>

        let iNeg:negRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hneg⟩⟩
        have hiNeg:(iNeg:m)=i:=rfl
        have h:=h_xₙn iNeg
        dsimp [valneg] at h
        rw [sub_le_iff_le_add] at h
        rw [add_comm] at h
        have h_scaled:=mul_le_mul_of_nonpos_right h (le_of_lt hneg)
        have h_scaled':(xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg≤ negb iNeg * Aₙ iNeg:=by
          simpa [hiNeg,add_comm] using h_scaled
        have hdot_neg:A₀ i ⬝ᵥ x'=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by
          calc
            A₀ i ⬝ᵥ x'=A₀ iNeg ⬝ᵥ x':=by simp [hiNeg]
            _=((fun j:Fin n => A₀ iNeg j * (Aₙ iNeg)⁻¹) ⬝ᵥ x') * Aₙ iNeg:=by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iNeg) x' (Aₙ iNeg) (ne_of_lt hneg)
            _=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by rfl
        calc
          A.mulVec x i
             =(A₀ i ⬝ᵥ x') + Aₙ i * xₙ:=by
                  simpa [x,A₀,Aₙ] using mulVec_lastCases_split A xₙ x' i
          _=((negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg + xₙ * Aₙ iNeg:=by
                rw [hdot_neg]
                simp [Aₙ,hiNeg,mul_comm]
          _=(xₙ + (negCoeffs iNeg) ⬝ᵥ x') * Aₙ iNeg:=by ring
          _≤ negb iNeg * Aₙ iNeg:=h_scaled'
          _=b i:=by
                calc
                  negb iNeg * Aₙ iNeg
                     =(b iNeg * (Aₙ iNeg)⁻¹) * Aₙ iNeg:=by simp [negb]
                  _=b iNeg:=by
                    simpa using mul_inv_cancel_right (b iNeg) (Aₙ iNeg) (ne_of_lt hneg)
                  _=b i:=by simp [hiNeg]
      | inr hpos =>

        let iPos:posRow:= ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hpos⟩⟩
        have hiPos:(iPos:m)=i:=rfl
        have h:=h_xₙp iPos
        dsimp [valpos] at h
        rw [le_sub_iff_add_le,add_comm] at h
        have h_scaled:=mul_le_mul_of_nonneg_right h (le_of_lt hpos)
        have h_scaled':((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos≤ posb iPos * Aₙ iPos:=by
          simpa [hiPos] using h_scaled
        have hdot_pos:A₀ i ⬝ᵥ x'=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos:=by
          calc
            A₀ i ⬝ᵥ x'=A₀ iPos ⬝ᵥ x':=by simp [hiPos]
            _=((fun j:Fin n => A₀ iPos j * (Aₙ iPos)⁻¹) ⬝ᵥ x') * Aₙ iPos:=by
                  symm
                  exact dotProduct_scaled_inv_mul (A₀ iPos) x' (Aₙ iPos) hpos.ne'
            _=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos:=by rfl
        calc
          A.mulVec x i
             =(A₀ i ⬝ᵥ x') + Aₙ i * xₙ:=by
                  simpa [x,A₀,Aₙ] using mulVec_lastCases_split A xₙ x' i
          _=((posCoeffs iPos) ⬝ᵥ x') * Aₙ iPos + xₙ * Aₙ iPos:=by
                rw [hdot_pos]
                simp [Aₙ,hiPos,mul_comm]
          _=((posCoeffs iPos) ⬝ᵥ x' + xₙ) * Aₙ iPos:=by ring
          _≤ posb iPos * Aₙ iPos:=h_scaled'
          _=b i:=by
                calc
                  posb iPos * Aₙ iPos
                     =(b iPos * (Aₙ iPos)⁻¹) * Aₙ iPos:=by simp [posb]
                  _=b iPos:=by
                    simpa using mul_inv_cancel_right (b iPos) (Aₙ iPos) hpos.ne'
                  _=b i:=by simp [hiPos]

  classical

  let M:Matrix κ m F:=fun i j =>
    match i with
    | Sum.inl (iPos,iNeg) =>
      (if (j:m)=(iPos:m) then (Aₙ iPos)⁻¹ else 0) +
      (if (j:m)=(iNeg:m) then -(Aₙ iNeg)⁻¹ else 0)
    | Sum.inr iZero =>
        if (j:m)=(iZero:m) then 1 else 0

  have hA'_eq:A'=M * A₀:=by
    ext i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      rw [Matrix.mul_apply]
      simp [A',M,posCoeffs,negCoeffs,A₀,add_mul,Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [A',M,zeroCoeffs,A₀]
  have hb'_eq:b'=M.mulVec b:=by
    ext i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      rw [Matrix.mulVec,dotProduct]
      simp [b',M,posb,negb,add_mul,Finset.sum_add_distrib]
      ring
    | inr iZero =>
      rw [Matrix.mulVec,dotProduct]
      simp [b',M,zerob]

  have hM_nonneg:∀ i j,0≤ M i j:=by
    intro i j
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      refine add_nonneg ?_ ?_
      · by_cases h:(j:m)=(iPos:m)
        · simpa [M,h] using inv_nonneg.mpr (le_of_lt (Finset.mem_filter.mp iPos.property).2)
        · simp [h]
      · by_cases h:(j:m)=(iNeg:m)
        · simpa [M,h]
            using neg_nonneg.mpr (inv_nonpos.mpr (le_of_lt (Finset.mem_filter.mp iNeg.property).2))
        · simp [h]
    | inr iZero =>
      by_cases h0:(j:m)=(iZero:m)
      · simp [M,h0]
      · simp [M,h0]

  have hM_last_zero:∀ i, (M * A) i (Fin.last n)=0:=by
    intro i
    cases i with
    | inl ij =>
      rcases ij with ⟨iPos,iNeg⟩
      have hposnz:Aₙ iPos ≠ 0:=ne_of_gt (Finset.mem_filter.mp iPos.property).2
      have hnegnz:Aₙ iNeg ≠ 0:=ne_of_lt (Finset.mem_filter.mp iNeg.property).2
      rw [Matrix.mul_apply]
      simp [M,Aₙ,hposnz,hnegnz,add_mul,Finset.sum_add_distrib]
    | inr iZero =>
      rw [Matrix.mul_apply]
      simp [M,Aₙ, (Finset.mem_filter.mp iZero.property).2]

  have h_equiv_M:∀ x':Fin n→ F,
      (M * A₀).mulVec x'≤ M.mulVec b↔
        ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b:=by
    intro x'
    constructor
    · intro hxElim
      apply hright x'
      simpa only [hA'_eq,hb'_eq] using hxElim
    · rintro ⟨t,ht⟩
      have hElim:=hlft (Fin.lastCases t x') ht
      simpa only [Fin.lastCases_castSucc,hA'_eq,hb'_eq] using hElim
  exact ⟨κ,inferInstance,M,hM_nonneg,hM_last_zero,by simpa [A₀] using h_equiv_M⟩

theorem feasibility_iff_of_projection
    {m κ:Type u} {F:Type v} [Fintype m] [Fintype κ]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F) (M:Matrix κ m F)
    (hprojection:∀ x':Fin n→ F,
      (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b↔
        ∃ t:F,A.mulVec (Fin.lastCases t x')≤ b):
    (∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
      ∃ x':Fin n→ F,
        (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b:=by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun j => x (Fin.castSucc j), (hprojection _).mpr ?_⟩
    refine ⟨x (Fin.last n), ?_⟩
    have hreconstruct:Fin.lastCases (x (Fin.last n)) (fun j => x (Fin.castSucc j))=x:=by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
    simpa only [hreconstruct] using hx
  · rintro ⟨x',hx'⟩
    obtain ⟨t,ht⟩:=(hprojection x').mp hx'
    exact ⟨Fin.lastCases t x',ht⟩

theorem Fourier_Motzkin_feasibility
    {m:Type u} {F:Type v} [Fintype m]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F):
    ∃ κ:Type u, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
      (∀ i j,0≤ M i j)∧
      (∀ i, (M * A) i (Fin.last n)=0)∧
      ((∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
        ∃ x':Fin n→ F,
          (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b):=by
  obtain ⟨κ,inst,M,hM,hzero,hprojection⟩:=Fourier_Motzkin A b
  exact ⟨κ,inst,M,hM,hzero,feasibility_iff_of_projection A b M hprojection⟩

end Lax109476Proofs.Elimination

end

section

open Matrix

namespace Lax109476Proofs.Elimination

variable {F:Type} [Field F] [LinearOrder F] [IsStrictOrderedRing F]
variable {m:Type} [Fintype m]

def Farkas1Primal {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):Prop:=
  ∃ x:Fin n→ F,A.mulVec x≤  b

def Farkas1Dual {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):Prop:=
  ∃ y:m→ F, (∀ j,0≤ y j)∧ (y ᵥ* A=0)∧ (y ⬝ᵥ b < 0)

private theorem liftDual_of_fourierMotzkin {κ:Type*} [Fintype κ] {n:ℕ}
    (A:Matrix m (Fin (n + 1)) F) (b:m→ F) (M:Matrix κ m F)
    (hM_last:∀ i, (M * A) i (Fin.last n)=0)
    (hMt_nonneg:∀ i j,0≤ (M.transpose) i j)
  (y':κ→ F)
  (hy'_nonneg:∀ j,0≤ y' j)
  (hy'_Ared:y' ᵥ* (M * (A.submatrix id Fin.castSucc))=0)
  (hy'_bred:y' ⬝ᵥ M.mulVec b < 0):
  let y:m→ F:=M.transpose.mulVec y'
  (∀ j,0≤ y j)∧ (y ᵥ* A=0)∧ (y ⬝ᵥ b < 0):=by
  have hy_nonneg:∀ j,0≤ (M.transpose.mulVec y') j:=by
    intro j
    simp only [Matrix.mulVec,dotProduct]
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hMt_nonneg j i) (hy'_nonneg i)
  have hy'_Acast:y' ᵥ* ((M * A).submatrix id Fin.castSucc)=0:=by
    have hAred_eq:M * (A.submatrix id Fin.castSucc)=(M * A).submatrix id Fin.castSucc:=by
      simpa using
        (submatrix_mul M A id id Fin.castSucc Function.bijective_id).symm
    simpa [hAred_eq] using hy'_Ared
  have hy'_MA:y' ᵥ* (M * A)=0:=by
    ext j
    refine Fin.lastCases ?_ ?_ j
    · simp [Matrix.vecMul,dotProduct,hM_last]
    · intro k
      simpa [Matrix.vecMul,dotProduct] using congr_fun hy'_Acast k
  have hyA:(M.transpose.mulVec y') ᵥ* A=0:=by
    calc
      (M.transpose.mulVec y') ᵥ* A=(y' ᵥ* M) ᵥ* A:=by
        rw [Matrix.mulVec_transpose]
      _=y' ᵥ* (M * A):=by
        rw [Matrix.vecMul_vecMul]
      _=0:=hy'_MA
  have hyb:(M.transpose.mulVec y') ⬝ᵥ b < 0:=by
    calc
      (M.transpose.mulVec y') ⬝ᵥ b=(y' ᵥ* M) ⬝ᵥ b:=by
        rw [Matrix.mulVec_transpose]
      _=y' ⬝ᵥ M.mulVec b:=by
        symm
        simpa using Matrix.dotProduct_mulVec y' M b
      _ < 0:=hy'_bred
  simpa using
    (show (∀ j,0≤ (M.transpose.mulVec y') j)∧
        ((M.transpose.mulVec y') ᵥ* A=0)∧ ((M.transpose.mulVec y') ⬝ᵥ b < 0) from
      ⟨hy_nonneg,hyA,hyb⟩)

theorem Farkas1ExhaustWith
    (eliminate:∀ (m:Type) [Fintype m] (n:ℕ)
      (A:Matrix m (Fin (n + 1)) F) (b:m→ F),
      ∃ κ:Type, ∃ _:Fintype κ, ∃ M:Matrix κ m F,
        (∀ i j,0≤ M i j)∧ (∀ i, (M * A) i (Fin.last n)=0)∧
        ((∃ x:Fin (n + 1)→ F,A.mulVec x≤ b)↔
          ∃ x':Fin n→ F, (M * (A.submatrix id Fin.castSucc)).mulVec x'≤ M.mulVec b))
    {n:ℕ} (A:Matrix m (Fin n) F) (b:m→ F):
  Farkas1Primal A b∨ Farkas1Dual A b:=by
  induction n generalizing m b with
  | zero =>
      by_cases hb:0≤ b
      · left
        refine ⟨Fin.elim0, ?_⟩
        simpa [Matrix.mulVec] using hb
      · right
        have hbi:∃ i:m,b i < 0:=by
          by_contra hbi
          apply hb
          intro i
          by_contra hnonneg
          exact hbi ⟨i,lt_of_not_ge hnonneg⟩
        rcases hbi with ⟨i,hbi⟩
        classical
        let y:m→ F:=fun j => if j=i then 1 else 0
        refine ⟨y, ?_, ?_, ?_⟩
        · intro j
          by_cases hji:j=i <;> simp [y,hji]
        · ext j
          exact j.elim0
        · have hyb:y ⬝ᵥ b=b i:=by
            simp [y,dotProduct]
          rw [hyb]
          exact hbi
  | succ n ih =>
      by_cases hP:Farkas1Primal A b
      · exact Or.inl hP
      · right
        rcases eliminate m n A b with ⟨κ,_,M,hM_nonneg,hM_last,hFM⟩
        let Ared:Matrix κ (Fin n) F:=M * (A.submatrix id Fin.castSucc)
        let bred:κ→ F:=M.mulVec b
        have hFM':Farkas1Primal A b↔ Farkas1Primal (m:=κ) Ared bred:=by
          simpa [Farkas1Primal,Ared,bred] using hFM
        have hred_noPrimal:¬ Farkas1Primal (m:=κ) Ared bred:=by
          intro h
          exact hP (hFM'.2 h)
        have hred_exhaust:Farkas1Primal (m:=κ) Ared bred∨ Farkas1Dual (m:=κ) Ared bred:=
          ih (m:=κ) (A:=Ared) (b:=bred)
        have hred_dual:Farkas1Dual (m:=κ) Ared bred:=by
          cases hred_exhaust with
          | inl h => exact False.elim (hred_noPrimal h)
          | inr h => exact h
        rcases hred_dual with ⟨y',hy'_nonneg,hy'_Ared,hy'_bred⟩
        have hMt_nonneg:∀ i j,0≤ (M.transpose) i j:=by
          intro i j
          simpa [Matrix.transpose_apply] using hM_nonneg j i
        have hdual_lift:Farkas1Dual A b:=by
          refine ⟨M.transpose.mulVec y', ?_⟩
          simpa [Ared,bred] using
            (liftDual_of_fourierMotzkin A b M hM_last hMt_nonneg y' hy'_nonneg hy'_Ared hy'_bred)
        exact hdual_lift

theorem Farkas1Exhaust {n:ℕ} (A:Matrix m (Fin n) ℝ) (b:m→ ℝ):
    Farkas1Primal A b∨ Farkas1Dual A b:=
  Farkas1ExhaustWith (fun _ _ _ A b => Fourier_Motzkin_feasibility A b) A b

theorem Farkas1ExhaustRat {n:ℕ} (A:Matrix m (Fin n) ℚ) (b:m→ ℚ):
    Farkas1Primal A b∨ Farkas1Dual A b:=
  Farkas1ExhaustWith (fun _ _ _ A b => Fourier_Motzkin_feasibility A b) A b
end Lax109476Proofs.Elimination

end

section

open scoped BigOperators

namespace Lax109476.LinearProgram

def IsBoundedAbove {m n:ℕ} (P:Program ℝ m n):Prop:=
  ∃ B:ℝ, ∀ x,PrimalFeasible P x→ primalValue P x≤ B

def IsPrimalOptimal {K:Type} [Ring K] [PartialOrder K] {m n:ℕ}
    (P:Program K m n) (x:Fin n→ K):Prop:=
  PrimalFeasible P x∧ ∀ z,PrimalFeasible P z→ primalValue P z≤ primalValue P x

end Lax109476.LinearProgram

end

section

open scoped BigOperators

namespace Lax109476Proofs.Farkas

open Lax109476.LinearProgram Lax109476.FarkasCertificate

private def augmentedMatrix {m n:ℕ} (P:Program ℝ m n):
    Matrix (Fin m ⊕ Fin n) (Fin n) ℝ:=
  Sum.elim P.A (fun k j => if k=j then -1 else 0)

private def augmentedBound {m n:ℕ} (P:Program ℝ m n):
    (Fin m ⊕ Fin n)→ ℝ:=Sum.elim P.b (fun _ => 0)

theorem farkas_certificate_exists:
    ∀ (m n:ℕ) (P:Program ℝ m n), ¬ IsFeasible P→
      ∃ y:Fin m→ ℝ,IsInfeasibilityCertificate P y:=by
  intro m n P hP
  classical
  have hno:¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P):=by
    rintro ⟨x,hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj:=hx (.inr j)
      simp [augmentedMatrix,augmentedBound,Matrix.mulVec,dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1Exhaust
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y,hy,hA,hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i),fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq:=congr_fun hA j
      simp only [Matrix.vecMul,dotProduct,Fintype.sum_sum_type,
        augmentedMatrix,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] at heq
      have hsum:(∑ k,y (Sum.inr k) * (if k=j then (-1:ℝ) else 0)) =
          -y (.inr j):=by simp
      rw [hsum] at heq
      have hid:columnValue P (fun i => y (.inl i)) j =
          ∑ i,y (.inl i) * P.A i j:=by
        simp only [columnValue,mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue,dotProduct,Fintype.sum_sum_type,
        augmentedBound,mul_comm] using hb

end Lax109476Proofs.Farkas

end

section

open scoped BigOperators

namespace Lax109476Proofs.Basic

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem transpose_identity {m n:ℕ} (P:Program ℝ m n)
    (x:Fin n→ ℝ) (y:Fin m→ ℝ):
    (∑ j,columnValue P y j * x j)=∑ i,rowValue P x i * y i:=by
  simp only [columnValue,rowValue,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem weak_duality:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x:Fin n→ ℝ) (y:Fin m→ ℝ),
      PrimalFeasible P x→ DualFeasible P y→ primalValue P x≤ dualValue P y:=by
  intro m n P x y hx hy
  calc
    primalValue P x≤ ∑ j,columnValue P y j * x j:=
      Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hy.2 j) (hx.1 j)
    _=∑ i,rowValue P x i * y i:=transpose_identity P x y
    _≤ dualValue P y:=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)

theorem farkas_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (y:Fin m→ ℝ),
      IsInfeasibilityCertificate P y→ ¬ IsFeasible P:=by
  intro m n P y hy ⟨x,hx⟩
  have hnonneg:0≤ ∑ j,columnValue P y j * x j:=
    Finset.sum_nonneg fun j _ => mul_nonneg (hy.2.1 j) (hx.1 j)
  have hle:(∑ j,columnValue P y j * x j)≤ dualValue P y:=by
    rw [transpose_identity]
    exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i)
  exact (not_lt_of_ge (hnonneg.trans hle)) hy.2.2

end Lax109476Proofs.Basic

end

section

open scoped BigOperators

namespace Lax109476Proofs.Attainment

open Lax109476.LinearProgram Lax109476.FarkasCertificate

private def thresholdProgram {m n:ℕ} (P:Program ℝ m n) (α:ℝ):
    Program ℝ (m + 1) n where
  A r j:=Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r:=Fin.lastCases (-α) P.b r
  c _:=0

private theorem threshold_column {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (m + 1)→ ℝ) (j:Fin n):
    columnValue (thresholdProgram P α) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m):=by
  simp [columnValue,thresholdProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem threshold_objective {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (m + 1)→ ℝ):
    dualValue (thresholdProgram P α) z =
      dualValue P (fun i => z i.castSucc) - α * z (Fin.last m):=by
  simp [dualValue,thresholdProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem column_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ) (j:Fin n):
    columnValue P (fun i => t * y i) j=t * columnValue P y j:=by
  simp only [columnValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dual_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ):
    dualValue P (fun i => t * y i)=t * dualValue P y:=by
  simp only [dualValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem primal_attainment:
    ∀ (m n:ℕ) (P:Program ℝ m n),IsFeasible P→ IsBoundedAbove P→
      ∃ x:Fin n→ ℝ,IsPrimalOptimal P x:=by
  intro m n P hf hb
  classical
  let S:Set ℝ:= {v | ∃ x,PrimalFeasible P x∧ primalValue P x=v}
  obtain ⟨x₀,hx₀⟩:=hf
  have hS:S.Nonempty:= ⟨primalValue P x₀,x₀,hx₀,rfl⟩
  have hbounded:BddAbove S:=by
    obtain ⟨B,hB⟩:=hb
    refine ⟨B, ?_⟩
    rintro v ⟨x,hx,rfl⟩
    exact hB x hx
  let α:ℝ:=sSup S
  let Q:=thresholdProgram P α
  have hQ:IsFeasible Q:=by
    by_contra hn
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (m + 1) n Q hn
    let y:Fin m→ ℝ:=fun i => z i.castSucc
    let t:ℝ:=z (Fin.last m)
    have hy:∀ i,0≤ y i:=fun i => hz.1 i.castSucc
    have ht:0≤ t:=hz.1 (Fin.last m)
    have hcol:∀ j,P.c j * t≤ columnValue P y j:=by
      intro j
      have h:=hz.2.1 j
      change 0≤ columnValue (thresholdProgram P α) z j at h
      rw [threshold_column] at h
      change 0≤ columnValue P y j - P.c j * t at h
      linarith
    have hgap:dualValue P y < α * t:=by
      have h:=hz.2.2
      change dualValue (thresholdProgram P α) z < 0 at h
      rw [threshold_objective] at h
      change dualValue P y - α * t < 0 at h
      linarith
    by_cases hpos:0 < t
    · let w:Fin m→ ℝ:=fun i => t⁻¹ * y i
      have hw:DualFeasible P w:=by
        refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht) (hy i), ?_⟩
        intro j
        change P.c j≤ columnValue P (fun i => t⁻¹ * y i) j
        rw [column_scale]
        calc
          P.c j=t⁻¹ * (P.c j * t):=by field_simp
          _≤ t⁻¹ * columnValue P y j:=
            mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht)
      have hsup:α≤ dualValue P w:=by
        apply csSup_le hS
        rintro v ⟨x,hx,rfl⟩
        exact Lax109476Proofs.Basic.weak_duality m n P x w hx hw
      change α≤ dualValue P (fun i => t⁻¹ * y i) at hsup
      rw [dual_scale] at hsup
      have hscaled:=mul_le_mul_of_nonneg_left hsup ht
      have heq:t * (t⁻¹ * dualValue P y)=dualValue P y:=by field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0:t=0:=le_antisymm (le_of_not_gt hpos) ht
      have hcert:IsInfeasibilityCertificate P y:=by
        refine ⟨hy, ?_, ?_⟩
        · intro j
          simpa only [ht0,mul_zero] using hcol j
        · simpa only [ht0,mul_zero] using hgap
      exact Lax109476Proofs.Basic.farkas_soundness m n P y hcert ⟨x₀,hx₀⟩
  obtain ⟨x,hx⟩:=hQ
  have hxP:PrimalFeasible P x:=by
    refine ⟨hx.1, ?_⟩
    intro i
    simpa [Q,thresholdProgram,rowValue] using hx.2 i.castSucc
  have hlower:α≤ primalValue P x:=by
    have h:=hx.2 (Fin.last m)
    simpa [Q,thresholdProgram,rowValue,primalValue,Finset.sum_neg_distrib] using h
  refine ⟨x,hxP, ?_⟩
  intro w hw
  exact (le_csSup hbounded (show primalValue P w∈ S from ⟨w,hw,rfl⟩)).trans hlower

end Lax109476Proofs.Attainment

end

section

open scoped BigOperators

namespace Lax109476Proofs.Duality

open Lax109476.LinearProgram Lax109476.FarkasCertificate

theorem row_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ) (i:Fin m):rowValue P (fun j => t * d j) i=t * rowValue P d i:=by
  simp only [rowValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem objective_scale {m n:ℕ} (P:Program ℝ m n) (d:Fin n→ ℝ)
    (t:ℝ):primalValue P (fun j => t * d j)=t * primalValue P d:=by
  simp only [primalValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem row_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ)
    (i:Fin m):rowValue P (fun j => x j + d j) i=rowValue P x i + rowValue P d i:=by
  simp [rowValue,mul_add,Finset.sum_add_distrib]

theorem objective_add {m n:ℕ} (P:Program ℝ m n) (x d:Fin n→ ℝ):
    primalValue P (fun j => x j + d j)=primalValue P x + primalValue P d:=by
  simp [primalValue,mul_add,Finset.sum_add_distrib]

private def multiplierProgram {m n:ℕ} (P:Program ℝ m n) (α:ℝ):
    Program ℝ (n + 1) m where
  A r i:=Fin.lastCases (P.b i) (fun j => -P.A i j) r
  b r:=Fin.lastCases α (fun j => -P.c j) r
  c _:=0

private theorem multiplier_row {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (y:Fin m→ ℝ) (j:Fin n):
    rowValue (multiplierProgram P α) y j.castSucc=-columnValue P y j:=by
  simp [rowValue,columnValue,multiplierProgram,Finset.sum_neg_distrib]

private theorem multiplier_last {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (y:Fin m→ ℝ):
    rowValue (multiplierProgram P α) y (Fin.last n)=dualValue P y:=by
  simp [rowValue,dualValue,multiplierProgram]

private theorem certificate_column {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (n + 1)→ ℝ) (i:Fin m):
    columnValue (multiplierProgram P α) z i =
      -rowValue P (fun j => z j.castSucc) i + P.b i * z (Fin.last n):=by
  simp [columnValue,rowValue,multiplierProgram,Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

private theorem certificate_objective {m n:ℕ} (P:Program ℝ m n)
    (α:ℝ) (z:Fin (n + 1)→ ℝ):
    dualValue (multiplierProgram P α) z =
      -primalValue P (fun j => z j.castSucc) + α * z (Fin.last n):=by
  simp [dualValue,primalValue,multiplierProgram,Fin.sum_univ_castSucc,
    Finset.sum_neg_distrib]

theorem optimal_dual_multipliers:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x:Fin n→ ℝ),IsPrimalOptimal P x→
      ∃ y:Fin m→ ℝ,DualFeasible P y∧ primalValue P x=dualValue P y:=by
  intro m n P x hx
  classical
  let Q:=multiplierProgram P (primalValue P x)
  have hQ:IsFeasible Q:=by
    by_contra hQ
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (n + 1) m Q hQ
    let d:Fin n→ ℝ:=fun j => z j.castSucc
    let t:ℝ:=z (Fin.last n)
    have hd:∀ j,0≤ d j:=fun j => hz.1 j.castSucc
    have ht:0≤ t:=hz.1 (Fin.last n)
    have hrow:∀ i,rowValue P d i≤ P.b i * t:=by
      intro i
      have h:=hz.2.1 i
      change 0≤ columnValue (multiplierProgram P (primalValue P x)) z i at h
      rw [certificate_column] at h
      change 0≤ -rowValue P d i + P.b i * t at h
      linarith
    have hobj:primalValue P x * t < primalValue P d:=by
      have h:=hz.2.2
      change dualValue (multiplierProgram P (primalValue P x)) z < 0 at h
      rw [certificate_objective] at h
      change -primalValue P d + primalValue P x * t < 0 at h
      linarith
    by_cases hpos:0 < t
    · let w:Fin n→ ℝ:=fun j => t⁻¹ * d j
      have hw:PrimalFeasible P w:=by
        refine ⟨fun j => mul_nonneg (inv_nonneg.mpr ht) (hd j), ?_⟩
        intro i
        change rowValue P (fun j => t⁻¹ * d j) i≤ P.b i
        rw [row_scale]
        calc
          t⁻¹ * rowValue P d i≤ t⁻¹ * (P.b i * t):=
            mul_le_mul_of_nonneg_left (hrow i) (inv_nonneg.mpr ht)
          _=P.b i:=by field_simp
      have hbest:=hx.2 w hw
      change primalValue P (fun j => t⁻¹ * d j)≤ primalValue P x at hbest
      rw [objective_scale] at hbest
      have hscaled:=mul_le_mul_of_nonneg_left hbest ht
      have heq:t * (t⁻¹ * primalValue P d)=primalValue P d:=by
        field_simp
      rw [heq] at hscaled
      nlinarith
    · have ht0:t=0:=le_antisymm (le_of_not_gt hpos) ht
      have hw:PrimalFeasible P (fun j => x j + d j):=by
        refine ⟨fun j => add_nonneg (hx.1.1 j) (hd j), ?_⟩
        intro i
        rw [row_add]
        have hi:=hrow i
        rw [ht0,mul_zero] at hi
        linarith [hx.1.2 i]
      have hbest:=hx.2 _ hw
      rw [objective_add] at hbest
      rw [ht0,mul_zero] at hobj
      linarith
  obtain ⟨y,hy⟩:=hQ
  have hdual:DualFeasible P y:=by
    refine ⟨hy.1, ?_⟩
    intro j
    have h:=hy.2 j.castSucc
    change rowValue (multiplierProgram P (primalValue P x)) y j.castSucc≤ _ at h
    rw [multiplier_row] at h
    simp only [Q,multiplierProgram,Fin.lastCases_castSucc] at h
    linarith
  refine ⟨y,hdual,le_antisymm
    (Lax109476Proofs.Basic.weak_duality m n P x y hx.1 hdual) ?_⟩
  have h:=hy.2 (Fin.last n)
  change rowValue (multiplierProgram P (primalValue P x)) y (Fin.last n)≤ _ at h
  rw [multiplier_last] at h
  simpa only [Q,multiplierProgram,Fin.lastCases_last] using h

theorem strong_duality:
    ∀ (m n:ℕ) (P:Program ℝ m n),IsFeasible P→ IsBoundedAbove P→
      ∃ (x:Fin n→ ℝ) (y:Fin m→ ℝ),
        PrimalFeasible P x∧ DualFeasible P y∧ primalValue P x=dualValue P y:=by
  intro m n P hf hb
  obtain ⟨x,hx⟩:=Lax109476Proofs.Attainment.primal_attainment m n P hf hb
  obtain ⟨y,hy,heq⟩:=Lax109476Proofs.Duality.optimal_dual_multipliers m n P x hx
  exact ⟨x,y,hx.1,hy,heq⟩

end Lax109476Proofs.Duality

end

section

namespace Lax109476.RationalCertificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate Lax109476.RecessionDirection

def IsCorrectOutcome {m n:ℕ} (P:Program ℚ m n):Certificate m n→ Prop
  | .optimal x _ => IsPrimalOptimal (toReal P) (realVector x)
  | .infeasible _ => ¬ IsFeasible (toReal P)
  | .unbounded _ _ => IsFeasible (toReal P)∧ ¬ IsBoundedAbove (toReal P)

end Lax109476.RationalCertificates

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate

private def augmentedMatrix {m n:ℕ} (P:Program ℚ m n):
    Matrix (Fin m ⊕ Fin n) (Fin n) ℚ:=
  Sum.elim P.A (fun k j => if k=j then -1 else 0)

private def augmentedBound {m n:ℕ} (P:Program ℚ m n):
    (Fin m ⊕ Fin n)→ ℚ:=Sum.elim P.b (fun _ => 0)

theorem rational_farkas_exists {m n:ℕ} (P:Program ℚ m n)
    (hP:¬ ∃ x,PrimalFeasible P x):
    ∃ y:Fin m→ ℚ,IsInfeasibilityCertificate P y:=by
  classical
  have hno:¬ Lax109476Proofs.Elimination.Farkas1Primal
      (augmentedMatrix P) (augmentedBound P):=by
    rintro ⟨x,hx⟩
    apply hP
    refine ⟨x, ?_, ?_⟩
    · intro j
      have hj:=hx (.inr j)
      simp [augmentedMatrix,augmentedBound,Matrix.mulVec,dotProduct] at hj
      linarith
    · intro i
      exact hx (.inl i)
  rcases Lax109476Proofs.Elimination.Farkas1ExhaustRat
      (augmentedMatrix P) (augmentedBound P) with hp | ⟨y,hy,hA,hb⟩
  · exact False.elim (hno hp)
  · refine ⟨fun i => y (.inl i),fun i => hy (.inl i), ?_, ?_⟩
    · intro j
      have heq:=congr_fun hA j
      simp only [Matrix.vecMul,dotProduct,Fintype.sum_sum_type,
        augmentedMatrix,Sum.elim_inl,Sum.elim_inr,Pi.zero_apply] at heq
      have hsum:(∑ k,y (Sum.inr k) * (if k=j then (-1:ℚ) else 0)) =
          -y (.inr j):=by simp
      rw [hsum] at heq
      have hid:columnValue P (fun i => y (.inl i)) j =
          ∑ i,y (.inl i) * P.A i j:=by
        simp only [columnValue,mul_comm]
      rw [hid]
      linarith [hy (.inr j)]
    · simpa [dualValue,dotProduct,Fintype.sum_sum_type,
        augmentedBound,mul_comm] using hb

theorem cast_feasible {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ)
    (hx:PrimalFeasible P x):PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℚ)
    exact_mod_cast hx.1 j
  · intro i
    have h:=(Rat.cast_le (K:=ℝ)).mpr (hx.2 i)
    simpa [rowValue,toReal,realVector] using h

theorem cast_farkas {m n:ℕ} (P:Program ℚ m n) (y:Fin m→ ℚ)
    (hy:IsInfeasibilityCertificate P y):
    IsInfeasibilityCertificate (toReal P) (realVector y):=by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    have h:=(Rat.cast_nonneg (K:=ℝ)).mpr (hy.2.1 j)
    simpa [columnValue,toReal,realVector] using h
  · have h:=(Rat.cast_lt_zero (K:=ℝ)).mpr hy.2.2
    simpa [dualValue,toReal,realVector] using h

theorem rational_feasibility:
    ∀ (m n:ℕ) (P:Program ℚ m n),IsFeasible (toReal P)→
      ∃ x:Fin n→ ℚ,PrimalFeasible P x:=by
  intro m n P hf
  by_contra h
  obtain ⟨y,hy⟩:=rational_farkas_exists P h
  exact Lax109476Proofs.Basic.farkas_soundness m n (toReal P)
    (realVector y) (cast_farkas P y hy) hf

theorem finite_rational_feasibility {ι κ:Type} [Fintype ι] [Fintype κ]
    (A:Matrix κ ι ℚ) (b:κ→ ℚ) (x:ι→ ℝ)
    (hx:∀ j,0≤ x j)
    (hrows:∀ i, (∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ)):
    ∃ z:ι→ ℚ, (∀ j,0≤ z j)∧ ∀ i, (∑ j,A i j * z j)≤ b i:=by
  classical
  let s:=Fintype.equivFin ι
  let t:=Fintype.equivFin κ
  let P:Program ℚ (Fintype.card κ) (Fintype.card ι):=
    ⟨fun i j => A (t.symm i) (s.symm j),fun i => b (t.symm i),fun _ => 0⟩
  have hP:IsFeasible (toReal P):=by
    refine ⟨fun j => x (s.symm j),fun j => hx _, ?_⟩
    intro i
    change (∑ j, (A (t.symm i) (s.symm j):ℝ) * x (s.symm j))≤ (b (t.symm i):ℝ)
    have heq:=Fintype.sum_equiv s.symm
      (fun j => (A (t.symm i) (s.symm j):ℝ) * x (s.symm j))
      (fun j => (A (t.symm i) j:ℝ) * x j) (fun _ => rfl)
    exact heq.le.trans (hrows _)
  obtain ⟨z,hz⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility _ _ P hP
  refine ⟨fun j => z (s j),fun j => hz.1 _, ?_⟩
  intro i
  calc
    _=∑ j,A i (s.symm j) * z j:=
      Fintype.sum_equiv s _ _ (fun j => by simp)
    _≤ _:=by simpa [P,rowValue] using hz.2 (t i)

end Lax109476Proofs.RationalFeasibility

end

section

open scoped BigOperators

namespace Lax109476Proofs.Recession

open Lax109476.LinearProgram Lax109476.RecessionDirection

private def directionProgram {m n:ℕ} (P:Program ℝ m n):
    Program ℝ (m + 1) n where
  A r j:=Fin.lastCases (-P.c j) (fun i => P.A i j) r
  b r:=Fin.lastCases (-1) (fun _ => 0) r
  c _:=0

private theorem direction_column {m n:ℕ} (P:Program ℝ m n)
    (z:Fin (m + 1)→ ℝ) (j:Fin n):
    columnValue (directionProgram P) z j =
      columnValue P (fun i => z i.castSucc) j - P.c j * z (Fin.last m):=by
  simp [columnValue,directionProgram,Fin.sum_univ_castSucc,sub_eq_add_neg]

private theorem column_scale {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (t:ℝ) (j:Fin n):
    columnValue P (fun i => t * y i) j=t * columnValue P y j:=by
  simp only [columnValue,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem recession_existence:
    ∀ (m n:ℕ) (P:Program ℝ m n), ¬ IsBoundedAbove P→
      ∃ d:Fin n→ ℝ,IsImprovingDirection P d:=by
  intro m n P hb
  let Q:=directionProgram P
  have hQ:IsFeasible Q:=by
    by_contra hn
    obtain ⟨z,hz⟩:=Lax109476Proofs.Farkas.farkas_certificate_exists
      (m + 1) n Q hn
    let y:Fin m→ ℝ:=fun i => z i.castSucc
    let t:ℝ:=z (Fin.last m)
    have hy:∀ i,0≤ y i:=fun i => hz.1 i.castSucc
    have ht:0 < t:=by
      have h:=hz.2.2
      change dualValue (directionProgram P) z < 0 at h
      simpa [dualValue,directionProgram,Fin.sum_univ_castSucc,t] using h
    have hcol:∀ j,P.c j * t≤ columnValue P y j:=by
      intro j
      have h:=hz.2.1 j
      change 0≤ columnValue (directionProgram P) z j at h
      rw [direction_column] at h
      change 0≤ columnValue P y j - P.c j * t at h
      linarith
    let w:Fin m→ ℝ:=fun i => t⁻¹ * y i
    have hw:DualFeasible P w:=by
      refine ⟨fun i => mul_nonneg (inv_nonneg.mpr ht.le) (hy i), ?_⟩
      intro j
      change P.c j≤ columnValue P (fun i => t⁻¹ * y i) j
      rw [column_scale]
      calc
        P.c j=t⁻¹ * (P.c j * t):=by field_simp
        _≤ t⁻¹ * columnValue P y j:=
          mul_le_mul_of_nonneg_left (hcol j) (inv_nonneg.mpr ht.le)
    exact hb ⟨dualValue P w,fun x hx =>
      Lax109476Proofs.Basic.weak_duality m n P x w hx hw⟩
  obtain ⟨d,hd⟩:=hQ
  refine ⟨d,hd.1, ?_, ?_⟩
  · intro i
    have h:=hd.2 i.castSucc
    simpa [Q,directionProgram,rowValue] using h
  · have h:=hd.2 (Fin.last m)
    have hvalue:-primalValue P d≤ -1:=by
      simpa [Q,directionProgram,rowValue,primalValue,Finset.sum_neg_distrib] using h
    linarith

end Lax109476Proofs.Recession

end

section

open scoped BigOperators

namespace Lax109476Proofs.CertificateExistence

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RecessionDirection
open Lax109476Proofs.RationalFeasibility

private def pairMatrix {m n:ℕ} (P:Program ℚ m n):
    Matrix (Fin m ⊕ (Fin n ⊕ Bool)) (Fin n ⊕ Fin m) ℚ
  | .inl i => Sum.elim (P.A i) (fun _ => 0)
  | .inr (.inl j) => Sum.elim (fun _ => 0) (fun i => -P.A i j)
  | .inr (.inr false) => Sum.elim P.c (fun i => -P.b i)
  | .inr (.inr true) => Sum.elim (fun j => -P.c j) P.b

private def pairBound {m n:ℕ} (P:Program ℚ m n):
    (Fin m ⊕ (Fin n ⊕ Bool))→ ℚ
  | .inl i => P.b i
  | .inr (.inl j) => -P.c j
  | .inr (.inr _) => 0

private theorem rational_matching_pair {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℝ) (y:Fin m→ ℝ)
    (hx:PrimalFeasible (toReal P) x) (hy:DualFeasible (toReal P) y)
    (heq:primalValue (toReal P) x=dualValue (toReal P) y):
    ∃ xr:Fin n→ ℚ, ∃ yr:Fin m→ ℚ,
      PrimalFeasible P xr∧ DualFeasible P yr∧ primalValue P xr=dualValue P yr:=by
  let z:(Fin n ⊕ Fin m)→ ℝ:=Sum.elim x y
  have hz:∀ j,0≤ z j:=by
    intro j
    cases j with
    | inl j => exact hx.1 j
    | inr i => exact hy.1 i
  have hrows:∀ i, (∑ j, (pairMatrix P i j:ℝ) * z j)≤ (pairBound P i:ℝ):=by
    intro i
    cases i with
    | inl i => simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,rowValue,toReal] using hx.2 i
    | inr i =>
      cases i with
      | inl j =>
        simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,columnValue,toReal,
          Finset.sum_neg_distrib] using neg_le_neg (hy.2 j)
      | inr b =>
        cases b
        · have h:primalValue (toReal P) x - dualValue (toReal P) y≤ 0:=by rw [heq]; simp
          simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,primalValue,dualValue,
            toReal,Finset.sum_neg_distrib,sub_eq_add_neg] using h
        · have h:-primalValue (toReal P) x + dualValue (toReal P) y≤ 0:=by rw [heq]; simp
          simpa [pairMatrix,pairBound,z,Fintype.sum_sum_type,primalValue,dualValue,
            toReal,Finset.sum_neg_distrib] using h
  obtain ⟨zr,hzr,hr⟩:=finite_rational_feasibility (pairMatrix P) (pairBound P) z hz hrows
  let xr:Fin n→ ℚ:=fun j => zr (.inl j)
  let yr:Fin m→ ℚ:=fun i => zr (.inr i)
  refine ⟨xr,yr, ⟨fun j => hzr _, ?_⟩, ⟨fun i => hzr _, ?_⟩, ?_⟩
  · intro i
    simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,rowValue] using hr (.inl i)
  · intro j
    have h:=hr (.inr (.inl j))
    have h':-columnValue P yr j≤ -P.c j:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,yr,columnValue,
        Finset.sum_neg_distrib] using h
    exact neg_le_neg_iff.mp h'
  · have h₁:=hr (.inr (.inr false))
    have h₂:=hr (.inr (.inr true))
    have hg₁:primalValue P xr - dualValue P yr≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,yr,primalValue,
        dualValue,Finset.sum_neg_distrib,sub_eq_add_neg] using h₁
    have hg₂:-primalValue P xr + dualValue P yr≤ 0:=by
      simpa [pairMatrix,pairBound,Fintype.sum_sum_type,xr,yr,primalValue,
        dualValue,Finset.sum_neg_distrib] using h₂
    linarith

private theorem sum_scale {ι:Type} [Fintype ι] (a d:ι→ ℝ) (t:ℝ):
    (∑ j,a j * (t * d j))=t * ∑ j,a j * d j:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem rational_improving_direction {m n:ℕ} (P:Program ℚ m n)
    (d:Fin n→ ℝ) (hd:IsImprovingDirection (toReal P) d):
    ∃ dr:Fin n→ ℚ,IsImprovingDirection P dr:=by
  let A:Matrix (Fin m ⊕ Unit) (Fin n) ℚ:=Sum.elim P.A (fun _ j => -P.c j)
  let b:(Fin m ⊕ Unit)→ ℚ:=Sum.elim (fun _ => 0) (fun _ => -1)
  let t:=(primalValue (toReal P) d)⁻¹
  let z:=fun j => t * d j
  have ht:0 < t:=inv_pos.mpr hd.2.2
  have hz:∀ j,0≤ z j:=fun j => mul_nonneg ht.le (hd.1 j)
  have hrows:∀ i, (∑ j, (A i j:ℝ) * z j)≤ (b i:ℝ):=by
    intro i
    cases i with
    | inl i =>
      simp only [A,b,z,Sum.elim_inl,Rat.cast_zero]
      rw [sum_scale]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (hd.2.1 i)
    | inr _ =>
      simp only [A,b,z,Sum.elim_inr,Rat.cast_neg,Rat.cast_one,neg_mul,
        Finset.sum_neg_distrib]
      rw [sum_scale]
      change -(t * primalValue (toReal P) d)≤ -1
      dsimp [t]
      rw [inv_mul_cancel₀ (ne_of_gt hd.2.2)]
  obtain ⟨dr,hdr,hr⟩:=finite_rational_feasibility A b z hz hrows
  refine ⟨dr,hdr, ?_, ?_⟩
  · intro i
    exact hr (.inl i)
  · have h:-primalValue P dr≤ -1:=by
      simpa [A,b,primalValue,Finset.sum_neg_distrib] using hr (.inr ())
    linarith

theorem certificate_existence:
    ∀ (m n:ℕ) (P:Program ℚ m n), ∃ certificate:Certificate m n,
      IsValidCertificate P certificate:=by
  intro m n P
  classical
  by_cases hf:IsFeasible (toReal P)
  · by_cases hb:IsBoundedAbove (toReal P)
    · obtain ⟨x,y,hx,hy,heq⟩:=
        Lax109476Proofs.Duality.strong_duality m n (toReal P) hf hb
      obtain ⟨xr,yr,hxr,hyr,heqr⟩:=rational_matching_pair P x y hx hy heq
      exact ⟨.optimal xr yr,hxr,hyr,heqr⟩
    · obtain ⟨xr,hxr⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility m n P hf
      obtain ⟨d,hd⟩:=Lax109476Proofs.Recession.recession_existence m n (toReal P) hb
      obtain ⟨dr,hdr⟩:=rational_improving_direction P d hd
      exact ⟨.unbounded xr dr,hxr,hdr⟩
  · have hq:¬ ∃ x:Fin n→ ℚ,PrimalFeasible P x:=by
      rintro ⟨x,hx⟩
      exact hf ⟨realVector x,cast_feasible P x hx⟩
    obtain ⟨y,hy⟩:=rational_farkas_exists P hq
    exact ⟨.infeasible y,hy⟩

end Lax109476Proofs.CertificateExistence

end

section

open scoped BigOperators

namespace Lax109476Proofs.Certificates

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RecessionDirection Lax109476.RationalCertificates
open Lax109476Proofs.Duality

theorem recession_soundness:
    ∀ (m n:ℕ) (P:Program ℝ m n) (x d:Fin n→ ℝ),
      PrimalFeasible P x→ IsImprovingDirection P d→ ¬ IsBoundedAbove P:=by
  intro m n P x d hx hd ⟨B,hB⟩
  have hbase:=hB x hx
  have hpos:0 < primalValue P d:=hd.2.2
  let t:=(B - primalValue P x) / primalValue P d + 1
  have ht:0≤ t:=by
    dsimp [t]
    exact add_nonneg (div_nonneg (sub_nonneg.mpr hbase) (le_of_lt hpos)) (by norm_num)
  let z:Fin n→ ℝ:=fun j => x j + t * d j
  have hz:PrimalFeasible P z:=by
    refine ⟨fun j => add_nonneg (hx.1 j) (mul_nonneg ht (hd.1 j)), ?_⟩
    intro i
    change rowValue P (fun j => x j + t * d j) i≤ P.b i
    rw [row_add,row_scale]
    have hdir:t * rowValue P d i≤ 0:=
      mul_nonpos_of_nonneg_of_nonpos ht (hd.2.1 i)
    linarith [hx.2 i]
  have hval:primalValue P z=B + primalValue P d:=by
    change primalValue P (fun j => x j + t * d j)=_
    rw [objective_add,objective_scale]
    dsimp [t]
    field_simp [ne_of_gt hpos]
    ring
  have hbound:=hB z hz
  rw [hval] at hbound
  linarith [hd.2.2]

private theorem cast_row {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (i:Fin m):
    rowValue (toReal P) (realVector x) i=(rowValue P x i:ℚ):=by
  simp [rowValue,toReal,realVector]

private theorem cast_column {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (j:Fin n):
    columnValue (toReal P) (realVector y) j=(columnValue P y j:ℚ):=by
  simp [columnValue,toReal,realVector]

private theorem cast_primal {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ):
    primalValue (toReal P) (realVector x)=(primalValue P x:ℚ):=by
  simp [primalValue,toReal,realVector]

private theorem cast_dual {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ):
    dualValue (toReal P) (realVector y)=(dualValue P y:ℚ):=by
  simp [dualValue,toReal,realVector]

private theorem cast_feasible {m n:ℕ} (P:Program ℚ m n)
    (x:Fin n→ ℚ) (hx:PrimalFeasible P x):
    PrimalFeasible (toReal P) (realVector x):=by
  constructor
  · intro j
    change (0:ℝ)≤ (x j:ℚ)
    exact_mod_cast hx.1 j
  · intro i
    rw [cast_row]
    change ((rowValue P x i:ℚ):ℝ)≤ (P.b i:ℚ)
    exact_mod_cast hx.2 i

private theorem cast_dual_feasible {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:DualFeasible P y):
    DualFeasible (toReal P) (realVector y):=by
  constructor
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    change ((P.c j:ℚ):ℝ)≤ (columnValue P y j:ℚ)
    exact_mod_cast hy.2 j

private theorem cast_farkas {m n:ℕ} (P:Program ℚ m n)
    (y:Fin m→ ℚ) (hy:IsInfeasibilityCertificate P y):
    IsInfeasibilityCertificate (toReal P) (realVector y):=by
  refine ⟨?_, ?_, ?_⟩
  · intro i
    change (0:ℝ)≤ (y i:ℚ)
    exact_mod_cast hy.1 i
  · intro j
    rw [cast_column]
    exact_mod_cast hy.2.1 j
  · rw [cast_dual]
    exact_mod_cast hy.2.2

private theorem cast_direction {m n:ℕ} (P:Program ℚ m n)
    (d:Fin n→ ℚ) (hd:IsImprovingDirection P d):
    IsImprovingDirection (toReal P) (realVector d):=by
  refine ⟨?_, ?_, ?_⟩
  · intro j
    change (0:ℝ)≤ (d j:ℚ)
    exact_mod_cast hd.1 j
  · intro i
    rw [cast_row]
    exact_mod_cast hd.2.1 i
  · rw [cast_primal]
    exact_mod_cast hd.2.2

theorem certificate_soundness:
    ∀ (m n:ℕ) (P:Program ℚ m n) (certificate:Certificate m n),
      IsValidCertificate P certificate→ IsCorrectOutcome P certificate:=by
  intro m n P certificate h
  cases certificate with
  | optimal x y =>
      rcases h with ⟨hx,hy,heq⟩
      have hxR:=cast_feasible P x hx
      have hyR:=cast_dual_feasible P y hy
      have heqR:primalValue (toReal P) (realVector x) =
          dualValue (toReal P) (realVector y):=by
        rw [cast_primal,cast_dual,heq]
      refine ⟨hxR, ?_⟩
      intro z hz
      rw [heqR]
      exact Lax109476Proofs.Basic.weak_duality m n (toReal P)
        z (realVector y) hz hyR
  | infeasible y =>
      exact Lax109476Proofs.Basic.farkas_soundness m n
        (toReal P) (realVector y) (cast_farkas P y h)
  | unbounded x d =>
      have hxR:=cast_feasible P x h.1
      exact ⟨⟨realVector x,hxR⟩,
        Lax109476Proofs.Certificates.recession_soundness m n (toReal P)
          (realVector x) (realVector d) hxR (cast_direction P d h.2)⟩

end Lax109476Proofs.Certificates

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.StandardForm

variable {ι E:Type*} [Fintype ι] [AddCommGroup E] [Module ℚ E]

noncomputable def support (x:ι→ ℚ):Finset ι:=by
  classical
  exact Finset.univ.filter (fun i => x i ≠ 0)

theorem mem_support (x:ι→ ℚ) (i:ι):i∈ support x↔ x i ≠ 0:=by
  classical
  simp [support]

section Matrices

variable {κ:Type*} [Fintype κ] [DecidableEq ι]

theorem gram_det_ne_zero (C:Matrix κ ι ℚ)
    (hC:LinearIndependent ℚ C.col):(Cᵀ * C).det ≠ 0:=by
  classical
  have hc:=Matrix.mulVec_injective_iff.mpr hC
  have hg:Function.Injective (Cᵀ * C).mulVec:=by
    intro x y hxy
    let z:=x - y
    have hz:(Cᵀ * C) *ᵥ z=0:=by
      simp only [z,Matrix.mulVec_sub,hxy,sub_self]
    have hnorm:dotProduct (C *ᵥ z) (C *ᵥ z)=0:=by
      have heq:dotProduct z ((Cᵀ * C) *ᵥ z) =
          dotProduct (C *ᵥ z) (C *ᵥ z):=by
        rw [← Matrix.mulVec_mulVec,Matrix.dotProduct_mulVec,Matrix.vecMul_transpose]
      rw [← heq,hz,dotProduct_zero]
    have hcz:C *ᵥ z=0:=by
      funext i
      exact (Finset.sum_mul_self_eq_zero_iff Finset.univ (C *ᵥ z)).mp hnorm i
        (Finset.mem_univ i)
    have hz0:z=0:=hc (by simpa using hcz)
    exact sub_eq_zero.mp hz0
  exact ((Cᵀ * C).isUnit_iff_isUnit_det.mp
    (Matrix.mulVec_injective_iff_isUnit.mp hg)).ne_zero

theorem gram_recovers (C:Matrix κ ι ℚ) (b:κ→ ℚ) (x:ι→ ℚ)
    (hx:C *ᵥ x=b):(Cᵀ * C) *ᵥ x=Cᵀ *ᵥ b:=by
  rw [← Matrix.mulVec_mulVec,hx]

end Matrices

end Lax109476Proofs.StandardForm

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

theorem determinant_bound {ι:Type*} [Fintype ι] [DecidableEq ι]
    (A:Matrix ι ι ℤ) (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H):
    A.det.natAbs≤ (Fintype.card ι).factorial * H ^ Fintype.card ι:=by
  have hentry:∀ i j, |A i j|≤ (H:ℤ):=by
    intro i j
    simpa only [Int.natCast_natAbs] using (Int.ofNat_le.mpr (hA i j))
  have hd:|A.det|≤ ((Fintype.card ι).factorial:ℤ) * (H:ℤ) ^ Fintype.card ι:=by
    rw [Matrix.det_apply']
    calc
      _≤ ∑ σ:Equiv.Perm ι, |(Equiv.Perm.sign σ:ℤ) * ∏ i,A (σ i) i|:=
        Finset.abs_sum_le_sum_abs _ _
      _=∑ σ:Equiv.Perm ι, ∏ i, |A (σ i) i|:=by
        congr 1
        funext σ
        have hs:|(Equiv.Perm.sign σ:ℤ)|=1:=by
          exact Int.isUnit_iff_abs_eq.mp (Equiv.Perm.sign σ).isUnit
        rw [abs_mul,hs,one_mul,Finset.abs_prod]
      _≤ ∑ _σ:Equiv.Perm ι, ∏ _i:ι, (H:ℤ):=by
        apply Finset.sum_le_sum
        intro σ _
        exact Finset.prod_le_prod (fun _ _ => abs_nonneg _) (fun i _ => hentry _ i)
      _=_:=by simp [Fintype.card_perm]
  have hd':(A.det.natAbs:ℤ)≤
      ((Fintype.card ι).factorial * H ^ Fintype.card ι:ℕ):=by
    simpa only [Int.natCast_natAbs,Nat.cast_mul,Nat.cast_pow] using hd
  exact Int.ofNat_le.mp hd'

end Lax109476Proofs.DeterminantBounds

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.SmallFeasiblePoint

open StandardForm DeterminantBounds

variable {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]

theorem integer_system_coordinate_bound (A:Matrix ι ι ℤ) (b:ι→ ℤ)
    (x:ι→ ℚ) (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H) (hdet:A.det ≠ 0)
    (hx:(A.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial * H ^ Fintype.card ι∧
      (x j).den≤ (Fintype.card ι).factorial * H ^ Fintype.card ι:=by
  let Q:Matrix ι ι ℚ:=A.map (fun z => (z:ℚ))
  let r:ι→ ℚ:=fun i => (b i:ℚ)
  have hxr:Q *ᵥ x=r:=hx
  have hcr:Q.det • x=Q.cramer r:=by
    rw [Matrix.cramer_eq_adjugate_mulVec, ← hxr,Matrix.mulVec_mulVec,
      Matrix.adjugate_mul,Matrix.smul_mulVec,Matrix.one_mulVec]
  have hd:(A.det:ℚ) ≠ 0:=by exact_mod_cast hdet
  intro j
  have hupdate:Q.updateCol j r =
      (A.updateCol j b).map (fun z => (z:ℚ)):=
    (Matrix.map_updateCol (M:=A) (j:=j) (c:=b) (fun z => (z:ℚ))).symm
  have heq:(A.det:ℚ) * x j=((A.updateCol j b).det:ℚ):=by
    have h:=congrFun hcr j
    simpa only [Pi.smul_apply,smul_eq_mul,Matrix.cramer_apply,hupdate,
      Q, ← Int.cast_det] using h
  have hxj:x j=((A.updateCol j b).det:ℚ) / (A.det:ℚ):=by
    apply (eq_div_iff hd).mpr
    simpa only [mul_comm] using heq
  rw [hxj]
  obtain ⟨hn,hdn⟩:=integer_ratio_num_den_bound (A.updateCol j b).det A.det hdet
  refine ⟨hn.trans (determinant_bound _ H ?_),
    hdn.trans (determinant_bound A H hA)⟩
  intro i k
  simp only [Matrix.updateCol_apply]
  split_ifs <;> first | exact hb i | exact hA i k

theorem integer_gram_entry_bound (C:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hC:∀ i j, (C i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H):
    (∀ i j, ((Cᵀ * C) i j).natAbs≤ Fintype.card κ * H ^ 2)∧
      (∀ i, ((Cᵀ *ᵥ b) i).natAbs≤ Fintype.card κ * H ^ 2):=by
  constructor
  · intro i j
    calc
      _≤ ∑ k, (C k i * C k j).natAbs:=Int.natAbs_sum_le _ _
      _≤ ∑ _k:κ,H ^ 2:=by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul,pow_two]
        exact Nat.mul_le_mul (hC k i) (hC k j)
      _=_:=by simp
  · intro i
    calc
      _≤ ∑ k, (C k i * b k).natAbs:=Int.natAbs_sum_le _ _
      _≤ ∑ _k:κ,H ^ 2:=by
        apply Finset.sum_le_sum
        intro k _
        rw [Int.natAbs_mul,pow_two]
        exact Nat.mul_le_mul (hC k i) (hb k)
      _=_:=by simp

theorem independent_integer_coordinate_bound (C:Matrix κ ι ℤ) (b:κ→ ℤ)
    (x:ι→ ℚ) (H:ℕ) (hC:∀ i j, (C i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H)
    (hind:LinearIndependent ℚ (C.map (fun z => (z:ℚ))).col)
    (hx:(C.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι∧
      (x j).den≤ (Fintype.card ι).factorial *
        (Fintype.card κ * H ^ 2) ^ Fintype.card ι:=by
  let Q:Matrix κ ι ℚ:=C.map (fun z => (z:ℚ))
  have hmap:(Cᵀ * C).map (fun z => (z:ℚ))=Qᵀ * Q:=by
    ext i j
    simp [Matrix.mul_apply,Q]
  have hright:(Qᵀ *ᵥ fun i => (b i:ℚ)) =
      fun i => ((Cᵀ *ᵥ b) i:ℚ):=by
    ext i
    simp [Matrix.mulVec,dotProduct,Q]
  have hdet:(Cᵀ * C).det ≠ 0:=by
    intro h
    have hz:((Cᵀ * C).det:ℚ)=0:=by simp [h]
    rw [Int.cast_det,hmap] at hz
    exact gram_det_ne_zero Q hind hz
  have hgram:((Cᵀ * C).map (fun z => (z:ℚ))) *ᵥ x =
      fun i => ((Cᵀ *ᵥ b) i:ℚ):=by
    rw [hmap,gram_recovers Q _ x hx,hright]
  obtain ⟨hentries,hbound⟩:=integer_gram_entry_bound C b H hC hb
  exact integer_system_coordinate_bound (Cᵀ * C) (Cᵀ *ᵥ b) x
    (Fintype.card κ * H ^ 2) hentries hbound hdet hgram

end Lax109476Proofs.SmallFeasiblePoint

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates RationalFeasibility

theorem rational_magnitude_bound (q:ℚ) (B:ℕ) (hq:q.num.natAbs≤ B):
    |(q:ℝ)|≤ (B:ℝ):=by
  have hd:(0:ℝ) < q.den:=by exact_mod_cast q.den_pos
  have hd₁:(1:ℝ)≤ q.den:=by exact_mod_cast q.den_pos
  have hn:|(q.num:ℝ)|≤ (B:ℝ):=by
    have h:(q.num.natAbs:ℝ)≤ (B:ℝ):=by exact_mod_cast hq
    simpa only [Nat.cast_natAbs,Int.cast_abs] using h
  have heq:|(q:ℝ)|=|(q.num:ℝ)| / q.den:=by
    conv_lhs => rw [← q.num_div_den]
    simp only [Rat.cast_div,Rat.cast_intCast,Rat.cast_natCast,abs_div,
      abs_of_pos hd]
  rw [heq]
  apply (div_le_iff₀ hd).mpr
  exact hn.trans (by simpa using mul_le_mul_of_nonneg_left hd₁ (Nat.cast_nonneg B))

end Lax109476Proofs.Relaxation

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

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

open scoped BigOperators

namespace Lax109476Proofs.RationalMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates

def minimizationProgram {m n:ℕ} (P:Program ℚ m n) (j:Fin n):Program ℚ m n:=
  { P with c:=fun k => if k=j then -1 else 0 }

theorem minimization_value {m n:ℕ} (P:Program ℚ m n) (j:Fin n)
    (y:Fin n→ ℝ):primalValue (toReal (minimizationProgram P j)) y=-y j:=by
  simp [primalValue,toReal,minimizationProgram,apply_ite]

theorem exists_coordinate_minimum {m n:ℕ} (P:Program ℚ m n) (j:Fin n)
    (hf:IsFeasible (toReal P)):
    ∃ x:Fin n→ ℚ,PrimalFeasible (toReal P) (realVector x)∧
      ∀ y,PrimalFeasible (toReal P) y→ (x j:ℝ)≤ y j:=by
  let Q:=minimizationProgram P j
  have hfeas:IsFeasible (toReal Q):=hf
  have hbound:IsBoundedAbove (toReal Q):=by
    refine ⟨0,fun y hy => ?_⟩
    rw [minimization_value]
    exact neg_nonpos.mpr (hy.1 j)
  obtain ⟨cert,hv⟩:=Lax109476Proofs.CertificateExistence.certificate_existence m n Q
  have hc:=Lax109476Proofs.Certificates.certificate_soundness m n Q cert hv
  cases cert with
  | optimal x y =>
    refine ⟨x,hc.1,fun z hz => ?_⟩
    have h:=hc.2 z hz
    change primalValue (toReal (minimizationProgram P j)) z≤
      primalValue (toReal (minimizationProgram P j)) (realVector x) at h
    rw [minimization_value,minimization_value] at h
    exact neg_le_neg_iff.mp h
  | infeasible y => exact False.elim (hc hfeas)
  | unbounded x d => exact False.elim (hc.2 hbound)

end Lax109476Proofs.RationalMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicSupport

open StandardForm

def LexMinimum {m n:ℕ} (C:Matrix (Fin m) (Fin n) ℚ) (b:Fin m→ ℚ)
    (x:Fin n→ ℚ):Prop:=
  Feasible C b x∧ ∀ y,Feasible C b y→ ∀ i,
    (∀ j,j < i→ y j=x j)→ x i≤ y i

theorem lexMinimum_independent {m n:ℕ} (C:Matrix (Fin m) (Fin n) ℚ)
    (b:Fin m→ ℚ) (x:Fin n→ ℚ) (hx:LexMinimum C b x):
    LinearIndepOn ℚ C.col (support x:Set (Fin n)):=by
  classical
  by_contra hdep
  obtain ⟨g,hg,j₀,hj₀,hgj₀⟩:=not_linearIndepOn_finset_iff.mp hdep
  let d:Fin n→ ℚ:=fun j => if j∈ support x then g j else 0
  have hd:C *ᵥ d=0:=by
    have hsum:(∑ j,d j • C.col j)=0:=by
      simpa [d, ← Finset.sum_filter] using hg
    simpa [Matrix.mulVec_eq_sum,Matrix.col] using hsum
  let s:=Finset.univ.filter (fun j => d j ≠ 0)
  have hs:s.Nonempty:= ⟨j₀,by simp [s,d,hj₀,hgj₀]⟩
  have hpos:∀ j∈ s,0 < x j:=by
    intro j hj
    have hdj:d j ≠ 0:=(Finset.mem_filter.mp hj).2
    have hxs:j∈ support x:=by
      by_contra hn
      exact hdj (by simp [d,hn])
    exact lt_of_le_of_ne (hx.1.1 j) ((mem_support x j).mp hxs).symm
  obtain ⟨p,hp,hratio⟩:=s.exists_min_image (fun j => x j / |d j|) hs
  let t:=x p / |d p|
  have hdp:0 < |d p|:=abs_pos.mpr (Finset.mem_filter.mp hp).2
  have ht:0 < t:=div_pos (hpos p hp) hdp
  have hmove:∀ j, |t * d j|≤ x j:=by
    intro j
    by_cases hdj:d j=0
    · simpa [hdj] using hx.1.1 j
    · have hj:j∈ s:=by simp [s,hdj]
      have hr:=hratio j hj
      rw [abs_mul,abs_of_pos ht]
      exact (le_div_iff₀ (abs_pos.mpr hdj)).mp hr
  let yPlus:Fin n→ ℚ:=fun j => x j + t * d j
  let yMinus:Fin n→ ℚ:=fun j => x j - t * d j
  have hyPlus:Feasible C b yPlus:=by
    constructor
    · intro j
      have h:=abs_le.mp (hmove j)
      dsimp [yPlus]
      linarith
    · change C *ᵥ (x + t • d)=b
      rw [Matrix.mulVec_add,Matrix.mulVec_smul,hd,smul_zero,add_zero,hx.1.2]
  have hyMinus:Feasible C b yMinus:=by
    constructor
    · intro j
      exact sub_nonneg.mpr ((le_abs_self _).trans (hmove j))
    · change C *ᵥ (x - t • d)=b
      rw [Matrix.mulVec_sub,Matrix.mulVec_smul,hd,smul_zero,sub_zero,hx.1.2]
  let i:=s.min' hs
  have hi:i∈ s:=s.min'_mem hs
  have hprior:∀ j,j < i→ d j=0:=by
    intro j hj
    by_contra hdj
    have hjs:j∈ s:=by simp [s,hdj]
    exact (not_le_of_gt hj) (s.min'_le j hjs)
  have hplus:=hx.2 yPlus hyPlus i (by intro j hj; simp [yPlus,hprior j hj])
  have hminus:=hx.2 yMinus hyMinus i (by intro j hj; simp [yMinus,hprior j hj])
  have hzero:t * d i=0:=by dsimp [yPlus,yMinus] at hplus hminus; linarith
  have hdi:d i=0:=(mul_eq_zero.mp hzero).resolve_left (ne_of_gt ht)
  exact (Finset.mem_filter.mp hi).2 hdi

end Lax109476Proofs.LexicographicSupport

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicMinima

open Lax109476.LinearProgram Lax109476.RationalCertificates
open RationalMinima

def fixedPrefix {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ) (k:ℕ):
    Program ℚ (m + (n + n)) n where
  A:=Fin.addCases P.A (Fin.addCases
    (fun i j => if i.val < k then if j=i then 1 else 0 else 0)
    (fun i j => if i.val < k then if j=i then -1 else 0 else 0))
  b:=Fin.addCases P.b (Fin.addCases
    (fun i => if i.val < k then x i else 0)
    (fun i => if i.val < k then -x i else 0))
  c:=P.c

theorem fixedPrefix_feasible {m n:ℕ} (P:Program ℚ m n) (x:Fin n→ ℚ)
    (k:ℕ) (y:Fin n→ ℝ):
    PrimalFeasible (toReal (fixedPrefix P x k)) y↔
      PrimalFeasible (toReal P) y∧ ∀ j,j.val < k→ y j=(x j:ℝ):=by
  have hrow:∀ i:Fin m,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.castAdd (n + n) i)=rowValue (toReal P) y i:=by
    intro i
    simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix]
  have hpos:∀ j:Fin n,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.castAdd n j))=if j.val < k then y j else 0:=by
    intro j
    by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix,hj,apply_ite]
  have hneg:∀ j:Fin n,rowValue (toReal (fixedPrefix P x k)) y
      (Fin.natAdd m (Fin.natAdd n j))=if j.val < k then -y j else 0:=by
    intro j
    by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,rowValue,toReal,fixedPrefix,hj,apply_ite]
  constructor
  · rintro ⟨hy,hr⟩
    refine ⟨⟨hy,fun i => ?_⟩,fun j hj => ?_⟩
    · have h:=hr (Fin.castAdd (n + n) i)
      rw [hrow] at h
      simpa [toReal,fixedPrefix] using h
    · have hp:=hr (Fin.natAdd m (Fin.castAdd n j))
      have hn:=hr (Fin.natAdd m (Fin.natAdd n j))
      rw [hpos] at hp
      rw [hneg] at hn
      simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj] at hp hn
      linarith
  · rintro ⟨⟨hy,hr⟩,hprefix⟩
    refine ⟨hy,fun i => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hrow]
      simpa [toReal,fixedPrefix] using hr i
    · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [hpos]
        by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj,hprefix j]
      · rw [hneg]
        by_cases hj:j.val < k <;> simp [-Fin.natAdd_eq_addNat,toReal,fixedPrefix,hj,hprefix j]

theorem exists_partial_lex_minimum {m n:ℕ} (P:Program ℚ m n)
    (hf:IsFeasible (toReal P)) (k:ℕ) (hk:k≤ n):
    ∃ x:Fin n→ ℚ,PrimalFeasible (toReal P) (realVector x)∧
      ∀ i,i.val < k→ ∀ y,PrimalFeasible (toReal P) y→
        (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i:=by
  induction k with
  | zero =>
    obtain ⟨x,hx⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility m n P hf
    exact ⟨x,RationalFeasibility.cast_feasible P x hx,fun i hi => by omega⟩
  | succ k ih =>
    obtain ⟨x,hx,hlex⟩:=ih (by omega)
    let i:Fin n:= ⟨k,by omega⟩
    have hQ:IsFeasible (toReal (fixedPrefix P x k)):=
      ⟨realVector x, (fixedPrefix_feasible P x k _).mpr ⟨hx,fun _ _ => rfl⟩⟩
    obtain ⟨z,hz,hzmin⟩:=exists_coordinate_minimum (fixedPrefix P x k) i hQ
    obtain ⟨hzP,hzpref⟩:=(fixedPrefix_feasible P x k _).mp hz
    refine ⟨z,hzP,fun j hj y hy hprior => ?_⟩
    by_cases hjk:j.val < k
    · have hzpref':∀ l,l.val < k→ (z l:ℝ)=(x l:ℝ):=hzpref
      rw [hzpref' j hjk]
      apply hlex j hjk y hy
      intro l hlj
      rw [← hzpref' l (by exact lt_trans hlj hjk)]
      exact hprior l hlj
    · have hji:j=i:=Fin.ext (by dsimp [i]; omega)
      subst j
      apply hzmin y
      apply (fixedPrefix_feasible P x k y).mpr
      refine ⟨hy,fun l hl => ?_⟩
      have he:(z l:ℝ)=(x l:ℝ):=hzpref l hl
      rw [← he]
      exact hprior l hl

theorem equationProgram_feasible {m n:ℕ} (C:Matrix (Fin m) (Fin n) ℚ)
    (b:Fin m→ ℚ) (y:Fin n→ ℝ):
    PrimalFeasible (toReal (equationProgram C b)) y↔
      (∀ j,0≤ y j)∧ (C.map (fun q => (q:ℝ))) *ᵥ y=fun i => (b i:ℝ):=by
  have hpos:∀ i:Fin m,rowValue (toReal (equationProgram C b)) y
      (Fin.castAdd m i)=(C.map (fun q => (q:ℝ)) *ᵥ y) i:=by
    intro i
    have ha:(equationProgram C b).A (Fin.castAdd m i)=C i:=by
      dsimp only [equationProgram]
      exact Fin.addCases_left (motive:=fun _:Fin (m + m) => Fin n→ ℚ)
        (left:=C) (right:=fun i j => -C i j) i
    change (∑ j, ((equationProgram C b).A (Fin.castAdd m i) j:ℝ) * y j)=_
    rw [ha]
    rfl
  have hneg:∀ i:Fin m,rowValue (toReal (equationProgram C b)) y
      (Fin.natAdd m i)=-(C.map (fun q => (q:ℝ)) *ᵥ y) i:=by
    intro i
    have ha:(equationProgram C b).A (Fin.natAdd m i)=(fun j => -C i j):=by
      dsimp only [equationProgram]
      exact Fin.addCases_right (motive:=fun _:Fin (m + m) => Fin n→ ℚ)
        (left:=C) (right:=fun i j => -C i j) i
    change (∑ j, ((equationProgram C b).A (Fin.natAdd m i) j:ℝ) * y j)=_
    rw [ha]
    simp [Matrix.mulVec,Matrix.map,dotProduct,Finset.sum_neg_distrib]
  constructor
  · rintro ⟨hy,hr⟩
    refine ⟨hy,funext (fun i => ?_)⟩
    have hp:=hr (Fin.castAdd m i)
    have hn:=hr (Fin.natAdd m i)
    rw [hpos] at hp
    rw [hneg] at hn
    simp [-Fin.natAdd_eq_addNat,toReal,equationProgram] at hp hn
    linarith
  · rintro ⟨hy,he⟩
    refine ⟨hy,fun i => ?_⟩
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [hpos,he]
      simp [toReal,equationProgram]
    · rw [hneg,he]
      simp [-Fin.natAdd_eq_addNat,toReal,equationProgram]

theorem cast_standard_feasible {m n:ℕ} (C:Matrix (Fin m) (Fin n) ℚ)
    (b:Fin m→ ℚ) (x:Fin n→ ℚ):
    LexicographicSupport.Feasible C b x↔
      PrimalFeasible (toReal (equationProgram C b)) (realVector x):=by
  rw [equationProgram_feasible]
  have hcast:(C.map (fun q => (q:ℝ))) *ᵥ realVector x =
      fun i => ((C *ᵥ x) i:ℝ):=by
    funext i
    simp [Matrix.mulVec,Matrix.map,realVector,dotProduct,Rat.cast_sum]
  rw [hcast]
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨fun j => (Rat.cast_nonneg (K:=ℝ)).mpr (hx j),by rw [he]⟩
  · rintro ⟨hx,he⟩
    refine ⟨fun j => (Rat.cast_nonneg (K:=ℝ)).mp (hx j),funext (fun i => ?_)⟩
    exact Rat.cast_injective (congrFun he i)

end Lax109476Proofs.LexicographicMinima

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.LexicographicBounds

open StandardForm LexicographicSupport LexicographicMinima SmallFeasiblePoint
open Lax109476.LinearProgram Lax109476.RationalCertificates

theorem independent_support_coordinate_bound {m n:ℕ}
    (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℤ) (z:Fin n→ ℚ)
    (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hz:(A.map (fun a => (a:ℚ))) *ᵥ z=fun i => (b i:ℚ))
    (hind:LinearIndepOn ℚ (A.map (fun a => (a:ℚ))).col (support z:Set (Fin n))):
    ∀ j, (z j).num.natAbs≤ coordinateCap m n H∧ (z j).den≤ coordinateCap m n H:=by
  classical
  let s:=support z
  let C:Matrix (Fin m) s ℤ:=fun i j => A i j.1
  have hcpos:∀ i j, (C i j).natAbs≤ H:=fun i j => hA i j.1
  have hcind:LinearIndependent ℚ (C.map (fun a => (a:ℚ))).col:=hind
  have hceq:(C.map (fun a => (a:ℚ))) *ᵥ (fun j:s => z j.1) =
      fun i => (b i:ℚ):=by
    ext i
    change (∑ j:s, (A i j.1:ℚ) * z j.1)=(b i:ℚ)
    calc
      _=∑ j∈ s, (A i j:ℚ) * z j:=Finset.sum_coe_sort s _
      _=∑ j, (A i j:ℚ) * z j:=by
        apply Finset.sum_subset (Finset.subset_univ s)
        intro j _ hj
        have hzj:z j=0:=by simpa [s,mem_support] using hj
        simp [hzj]
      _=_:=congrFun hz i
  have hbnd:=independent_integer_coordinate_bound C b (fun j:s => z j.1)
    H hcpos hb hcind hceq
  have hk:Fintype.card s≤ n:=by
    simpa using Fintype.card_le_of_injective (Subtype.val:s→ Fin n) Subtype.val_injective
  have hbound:(Fintype.card s).factorial *
      (Fintype.card (Fin m) * H ^ 2) ^ Fintype.card s≤ coordinateCap m n H:=by
    unfold coordinateCap
    simp only [Fintype.card_fin]
    apply Nat.mul_le_mul (Nat.factorial_le hk)
    exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbpos:0 < coordinateCap m n H:=by unfold coordinateCap; positivity
  intro j
  by_cases hj:j∈ s
  · exact ⟨(hbnd ⟨j,hj⟩).1.trans hbound, (hbnd ⟨j,hj⟩).2.trans hbound⟩
  · have hzj:z j=0:=by simpa [s,mem_support] using hj
    simp only [hzj,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    omega

theorem exists_bounded_lex_point {m n:ℕ} (C:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℤ) (H:ℕ) (hC:∀ i j, (C i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x,Feasible (C.map (fun a => (a:ℚ))) (fun i => (b i:ℚ)) x):
    ∃ x:Fin n→ ℚ,
      Feasible (C.map (fun a => (a:ℚ))) (fun i => (b i:ℚ)) x∧
      (∀ j, (x j).num.natAbs≤ coordinateCap m n H∧ (x j).den≤ coordinateCap m n H)∧
      ∀ i, ∀ y,PrimalFeasible
        (toReal (equationProgram (C.map (fun a => (a:ℚ))) (fun i => (b i:ℚ)))) y→
        (∀ j,j < i→ y j=(x j:ℝ))→ (x i:ℝ)≤ y i:=by
  let A:=C.map (fun a => (a:ℚ))
  let d:=fun i => (b i:ℚ)
  obtain ⟨x₀,hx₀⟩:=hf
  have hfP:IsFeasible (toReal (equationProgram A d)):=
    ⟨realVector x₀, (cast_standard_feasible A d x₀).mp hx₀⟩
  obtain ⟨x,hx,hlex⟩:=exists_partial_lex_minimum (equationProgram A d) hfP n le_rfl
  have hxf:=(cast_standard_feasible A d x).mpr hx
  have hlexRat:LexMinimum A d x:=by
    refine ⟨hxf,fun y hy i hprior => ?_⟩
    have h:=hlex i i.isLt (realVector y) ((cast_standard_feasible A d y).mp hy)
      (fun j hj => by change (y j:ℝ)=(x j:ℝ); rw [hprior j hj])
    exact (Rat.cast_le (K:=ℝ)).mp h
  have hind:=lexMinimum_independent A d x hlexRat
  refine ⟨x,hxf,independent_support_coordinate_bound C b x H hC hb hxf.2 hind, ?_⟩
  exact fun i => hlex i i.isLt

end Lax109476Proofs.LexicographicBounds

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

open scoped BigOperators

namespace Lax109476Proofs.RationalArithmeticBounds

open DeterminantBounds RationalSizeBounds
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding

theorem height_mono (q:ℚ) {B C:ℕ} (hq:Height q B) (hBC:B≤ C):Height q C:=
  ⟨hq.1.trans hBC,hq.2.trans hBC⟩

theorem height_neg (q:ℚ) (B:ℕ) (hq:Height q B):Height (-q) B:=by
  simpa only [Height,Rat.neg_num,Rat.neg_den,Int.natAbs_neg] using hq

end Lax109476Proofs.RationalArithmeticBounds

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

end Lax109476Proofs.RamRecoveryThreshold

end

section

open scoped Matrix

namespace Lax109476Proofs.RamStandardPointRecovery

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open RationalArithmeticBounds LexicographicMinima LexicographicSupport LexicographicBounds
open RamRecoveryThreshold

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_with_cap_spec (m n H S K N w D:ℕ) (C:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℤ)
    (hC:∀ i j, (C i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hH:H≤ 2 ^ S) (hcapLE:coordinateCap m n H≤ D) (hK:D.size≤ K) (hS:4 * K + 2≤ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamPointRecoveryBounds.wordWidth (m + m) n S≤ w)
    (hf:∃ x,Feasible (C.map (fun z => (z:ℚ))) (fun i => (b i:ℚ)) x):
    Spec (2 ^ w) (fun σ => RamPointInitialization.Base (program C b) σ∧
      Workspace (m + m) n σ∧ RamEllipsoidStep.Extents "point.x" n σ∧
      σ.vars "minimum.bound"=D∧ (σ.arrs "cf.stack").length=N)
      RamPointInitialization.recover
      (fun _ τ => ∃ x:Fin n→ ℚ,Persistent (program C b) x n τ∧
        Feasible (C.map (fun z => (z:ℚ))) (fun i => (b i:ℚ)) x∧
        ∀ j,Height (x j) (coordinateCap m n H))
      (33 * n + 22 + RamPointRecoveryBounds.instructionBound (m + m) n S K):=by
  have hpow:1≤ 2 ^ S:=Nat.one_le_pow _ _ (by decide)
  have hD:D≤ 2 ^ S:=(Nat.lt_size_self D).le.trans
    (Nat.pow_le_pow_right (by decide) (by omega:D.size≤ S))
  have hcap:=hcapLE.trans hD
  obtain ⟨x,hx,hxBound,hlex⟩:=exists_bounded_lex_point C b H hC hb hf
  have hA:∀ i j,Height ((program C b).A i j) (2 ^ S):=by
    intro i j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · change Height (Fin.addCases (motive:=fun _:Fin (m + m) => Fin n→ ℚ)
        (fun i j => (C i j:ℚ)) (fun i j => -(C i j:ℚ)) (Fin.castAdd m i) j) (2 ^ S)
      rw [Fin.addCases_left (motive:=fun _:Fin (m + m) => Fin n→ ℚ)]
      exact ⟨by simpa using (hC i j).trans hH,by simpa using hpow⟩
    · change Height (Fin.addCases (motive:=fun _:Fin (m + m) => Fin n→ ℚ)
        (fun i j => (C i j:ℚ)) (fun i j => -(C i j:ℚ)) (Fin.natAdd m i) j) (2 ^ S)
      rw [Fin.addCases_right (motive:=fun _:Fin (m + m) => Fin n→ ℚ)]
      apply height_neg
      exact ⟨by simpa using (hC i j).trans hH,by simpa using hpow⟩
  have hbound:∀ i,Height ((program C b).b i) (2 ^ S):=by
    intro i
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simp only [program,equationProgram,Fin.addCases_left]
      exact ⟨by simpa using (hb i).trans hH,by simpa using hpow⟩
    · simp only [program,equationProgram,Fin.addCases_right]
      apply height_neg
      exact ⟨by simpa using (hb i).trans hH,by simpa using hpow⟩
  have hxHeight:∀ j,Height (x j) (2 ^ S):=fun j => height_mono _ (hxBound j) hcap
  have hxD:∀ j,x j≤ D∧ (x j).den≤ D:=by
    intro j
    refine ⟨?_, (hxBound j).2.trans hcapLE⟩
    have he:=Relaxation.rational_magnitude_bound (x j) (coordinateCap m n H) (hxBound j).1
    exact ((Rat.cast_le (K:=ℝ)).mp ((le_abs_self _).trans he)).trans (by exact_mod_cast hcapLE)
  have hr:=RamPointInitialization.recover_spec (m + m) n S K N D w (program C b) x
    hK hS hN hw hA hbound hxHeight (by intro j; rfl) ((cast_standard_feasible _ _ x).mp hx) hlex hxD
  refine hr.post ?_
  rintro σ τ _ ⟨hτ,_,_⟩
  exact ⟨x,hτ,hx,hxBound⟩

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem recover_spec (m n H S K N w:ℕ) (C:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℤ)
    (hC:∀ i j, (C i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hH:H≤ 2 ^ S) (hK:(coordinateCap m n H).size≤ K) (hS:4 * K + 2≤ S)
    (hN:RamRationalReconstruction.depthBound S + 1≤ N)
    (hw:RamPointRecoveryBounds.wordWidth (m + m) n S≤ w)
    (hf:∃ x,Feasible (C.map (fun z => (z:ℚ))) (fun i => (b i:ℚ)) x):
    Spec (2 ^ w) (fun σ => RamPointInitialization.Base (program C b) σ∧
      Workspace (m + m) n σ∧ RamEllipsoidStep.Extents "point.x" n σ∧
      σ.vars "minimum.bound"=coordinateCap m n H∧ (σ.arrs "cf.stack").length=N)
      RamPointInitialization.recover
      (fun _ τ => ∃ x:Fin n→ ℚ,Persistent (program C b) x n τ∧
        Feasible (C.map (fun z => (z:ℚ))) (fun i => (b i:ℚ)) x∧
        ∀ j,Height (x j) (coordinateCap m n H))
      (33 * n + 22 + RamPointRecoveryBounds.instructionBound (m + m) n S K):=by
  exact recover_with_cap_spec m n H S K N w (coordinateCap m n H) C b hC hb hH le_rfl hK hS hN hw hf

end Lax109476Proofs.RamStandardPointRecovery

end

theorem solution:∀ (m n H S K N w D:Nat) (C:Matrix (Fin m) (Fin n) Int) (b:Fin m→ Int),
  (∀ (i:Fin m) (j:Fin n),Nat.le (C i j).natAbs H)→
    (∀ (i:Fin m),Nat.le (b i).natAbs H)→
      Nat.le H
          (@HPow.hPow Nat Nat Nat (@instHPow Nat Nat (@NPow.toPow Nat (@Monoid.toNPow Nat Nat.instMonoid)))
            ((2:Nat)) S)→
        Nat.le (Lax109476Proofs.LexicographicBounds.coordinateCap m n H) D→
          Nat.le D.size K→
            Nat.le
                (Nat.add
                  (Nat.mul
                    ((4:Nat)) K)
                  ((2:Nat)))
                S→
              Nat.le
                  (Nat.add
                    (Lax109476Proofs.RamRationalReconstruction.depthBound S)
                    ((1:Nat)))
                  N→
                Nat.le
                    (Lax109476Proofs.RamPointRecoveryBounds.wordWidth
                      (Nat.add m m) n S)
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
                            (Nat.add m m) n
                            (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) σ)
                          (And
                            (Lax109476Proofs.RamRecoveryThreshold.Workspace
                              (Nat.add m m) n σ)
                            (And (Lax109476Proofs.RamEllipsoidStep.Extents "point.x" n σ)
                              (And (@Eq Nat (σ.vars "minimum.bound") D)
                                (@Eq Nat (@List.length Nat (σ.arrs "cf.stack")) N)))))
                      Lax109476Proofs.RamPointInitialization.recover
                      (fun (x τ:Lax808846Proofs.Imp.Env) =>
                        ∃ (x:Fin n→ Rat),
                          And
                            (@Lax109476Proofs.RamRecoveryThreshold.Persistent
                              (Nat.add m m) n
                              (@Lax109476Proofs.RamStandardPointRecovery.program m n C b) x n τ)
                            (And
                              (@Lax109476Proofs.LexicographicSupport.Feasible m n
                                (@Matrix.map (Fin m) (Fin n) Int Rat C fun (z:Int) => @Int.cast Rat Rat.instIntCast z)
                                (fun (i:Fin m) => @Int.cast Rat Rat.instIntCast (b i)) x)
                              (∀ (j:Fin n),
                                Lax109476Proofs.RationalArithmeticBounds.Height (x j)
                                  (Lax109476Proofs.LexicographicBounds.coordinateCap m n H))))
                      (Nat.add
                        (Nat.add
                          (Nat.mul
                            ((33:Nat)) n)
                          ((22:Nat)))
                        (Lax109476Proofs.RamPointRecoveryBounds.instructionBound
                          (Nat.add m m) n S K)):= @Lax109476Proofs.RamStandardPointRecovery.recover_with_cap_spec
