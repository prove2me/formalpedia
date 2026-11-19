-- Prove2me | solution 1 for Lax109476Proofs.RationalFeasibilityDecision.feasible_correct_native
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T15:27:15.425598+00:00
-- url     : https://prove2.me/submissions/b07d6763-a1d8-4f15-9ebe-61b6bfb770fd

import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Order.WellFounded
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.Size
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.List.FinRange
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Fin.Tuple.Basic
import Definitions.Def_EdgeSublinearMWIS_Main_NativeBlockInterfaces

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

theorem Farkas1ExhaustRat {n:ℕ} (A:Matrix m (Fin n) ℚ) (b:m→ ℚ):
    Farkas1Primal A b∨ Farkas1Dual A b:=
  Farkas1ExhaustWith (fun _ _ _ A b => Fourier_Motzkin_feasibility A b) A b
end Lax109476Proofs.Elimination

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

end Lax109476Proofs.RationalFeasibility

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

private theorem positive_relation (v:ι→ E) (s:Finset ι)
    (h:¬ LinearIndepOn ℚ v (s:Set ι)):
    ∃ d:ι→ ℚ, (∀ i,i∉ s→ d i=0)∧
      (∑ i,d i • v i)=0∧ ∃ i∈ s,0 < d i:=by
  classical
  obtain ⟨g,hg,i,hi,hgi⟩:=not_linearIndepOn_finset_iff.mp h
  let f:ι→ ℚ:=fun j => if j∈ s then g j else 0
  have hf:(∑ j,f j • v j)=0:=by
    simpa [f, ← Finset.sum_filter] using hg
  by_cases hp:0 < g i
  · exact ⟨f,by intro j hj; simp [f,hj],hf,i,hi,
      by simpa [f,hi] using hp⟩
  · refine ⟨-f, ?_, ?_,i,hi, ?_⟩
    · intro j hj
      simp [f,hj]
    · simp only [Pi.neg_apply,neg_smul,Finset.sum_neg_distrib,hf,neg_zero]
    · simp only [Pi.neg_apply,f,if_pos hi]
      exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hp) hgi)

theorem exists_independent_support (v:ι→ E) (b:E)
    (h:∃ x:ι→ ℚ, (∀ i,0≤ x i)∧ ∑ i,x i • v i=b):
    ∃ x:ι→ ℚ, (∀ i,0≤ x i)∧ (∑ i,x i • v i)=b∧
      LinearIndepOn ℚ v (support x:Set ι):=by
  classical
  let S:Set (ι→ ℚ):= {x | (∀ i,0≤ x i)∧ ∑ i,x i • v i=b}
  let x:=Function.argminOn (fun x:ι→ ℚ => (support x).card) S h
  have hx:x∈ S:=Function.argminOn_mem _ S h
  have hmin:∀ y∈ S, (support x).card≤ (support y).card:=
    fun y hy => Function.argminOn_le (fun x:ι→ ℚ => (support x).card) S hy
  refine ⟨x,hx.1,hx.2, ?_⟩
  by_contra hdep
  obtain ⟨d,hd,hsum,i₀,hi₀,hdi₀⟩:=positive_relation v (support x) hdep
  let s:=(support x).filter (fun i => 0 < d i)
  obtain ⟨i,hi,hratio⟩:=s.exists_min_image (fun j => x j / d j)
    ⟨i₀,by simp [s,hi₀,hdi₀]⟩
  have his:i∈ support x:=(Finset.mem_filter.mp hi).1
  have hdi:0 < d i:=(Finset.mem_filter.mp hi).2
  let t:=x i / d i
  have ht:0≤ t:=div_nonneg (hx.1 i) hdi.le
  let y:ι→ ℚ:=fun j => x j - t * d j
  have hypos:∀ j,0≤ y j:=by
    intro j
    by_cases hj:0 < d j
    · have hjs:j∈ support x:=by
        by_contra hn
        rw [hd j hn] at hj
        exact (lt_irrefl 0) hj
      have hr:=hratio j (Finset.mem_filter.mpr ⟨hjs,hj⟩)
      exact sub_nonneg.mpr ((le_div_iff₀ hj).mp hr)
    · exact sub_nonneg.mpr ((mul_nonpos_of_nonneg_of_nonpos ht
        (le_of_not_gt hj)).trans (hx.1 j))
  have hyb:(∑ j,y j • v j)=b:=by
    simp only [y,sub_smul,mul_smul,Finset.sum_sub_distrib,
      ← Finset.smul_sum,hsum,smul_zero,sub_zero]
    exact hx.2
  have hyi:y i=0:=by simp [y,t,ne_of_gt hdi]
  have hsub:support y ⊆ (support x).erase i:=by
    intro j hj
    have hyj:=(mem_support y j).mp hj
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro heq
      subst j
      exact hyj hyi
    · by_contra hn
      have hxj:x j=0:=by simpa [mem_support] using hn
      exact hyj (by simp [y,hxj,hd j hn])
  have hc:=(hmin y ⟨hypos,hyb⟩).trans (Finset.card_le_card hsub)
  have hlt:=Finset.card_erase_lt_of_mem his
  omega

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

namespace Lax109476Proofs.RationalRounding

theorem roundDown_le (q:ℚ) (D:ℕ) (hD:0 < D):roundDown q D≤ q:=by
  unfold roundDown
  apply (div_le_iff₀ (by exact_mod_cast hD)).mpr
  exact Int.floor_le _

theorem lt_roundDown_add (q:ℚ) (D:ℕ) (hD:0 < D):
    q < roundDown q D + 1 / D:=by
  have hp:(0:ℚ) < D:=by exact_mod_cast hD
  unfold roundDown
  rw [← add_div,lt_div_iff₀ hp]
  exact Int.lt_floor_add_one _

theorem roundDown_error (q:ℚ) (D:ℕ) (hD:0 < D):
    0≤ (q:ℝ) - (roundDown q D:ℝ)∧
      (q:ℝ) - (roundDown q D:ℝ) < 1 / (D:ℝ):=by
  have h₁:(roundDown q D:ℝ)≤ (q:ℝ):=by
    exact_mod_cast roundDown_le q D hD
  have h₂:(q:ℝ) < (roundDown q D:ℝ) + 1 / (D:ℝ):=by
    have h:=(Rat.cast_lt (K:=ℝ)).mpr (lt_roundDown_add q D hD)
    simpa only [Rat.cast_add,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using h
  constructor <;> linarith

theorem roundDown_vector_error (n:ℕ) (x:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    (∑ i, ((x i:ℝ) - (roundDown (x i) D:ℝ)) ^ 2)≤
      (n:ℝ) * (1 / (D:ℝ)) ^ 2:=by
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  calc
    _≤ ∑ _i:Fin n, (1 / (D:ℝ)) ^ 2:=by
      apply Finset.sum_le_sum
      intro i _
      obtain ⟨h₁,h₂⟩:=roundDown_error (x i) D hD
      nlinarith [show (0:ℝ) < 1 / (D:ℝ) by positivity]
    _=_:=by simp

theorem sqrtUpper_bounds (q:ℚ) (hq:0≤ q) (D:ℕ) (hD:0 < D):
    Real.sqrt (q:ℝ)≤ (sqrtUpper q D:ℝ)∧
      (sqrtUpper q D:ℝ) < Real.sqrt (q:ℝ) + 2 / (D:ℝ):=by
  let c:=Nat.ceil (q * (D:ℚ) ^ 2)
  let s:=Nat.sqrt c
  have hqR:(0:ℝ)≤ q:=by exact_mod_cast hq
  have hDR:(0:ℝ) < D:=by exact_mod_cast hD
  have hcl:(q:ℝ) * (D:ℝ) ^ 2≤ c:=by
    have h:q * (D:ℚ) ^ 2≤ (c:ℚ):=Nat.le_ceil _
    have h':=(Rat.cast_le (K:=ℝ)).mpr h
    simpa only [Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast] using h'
  have hcu:(c:ℝ) < (q:ℝ) * (D:ℝ) ^ 2 + 1:=by
    have h:(c:ℚ) < q * (D:ℚ) ^ 2 + 1:=
      Nat.ceil_lt_add_one (show (0:ℚ)≤ q * (D:ℚ) ^ 2 by positivity)
    have h':=(Rat.cast_lt (K:=ℝ)).mpr h
    simpa only [Rat.cast_add,Rat.cast_mul,Rat.cast_pow,Rat.cast_natCast,
      Rat.cast_one] using h'
  have hsl:(s:ℝ) ^ 2≤ c:=by
    have h:s ^ 2≤ c:=Nat.sqrt_le' c
    have h':=(Nat.cast_le (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow] using h'
  have hsu:(c:ℝ) < ((s:ℝ) + 1) ^ 2:=by
    have h:c < (s + 1) ^ 2:=Nat.lt_succ_sqrt' c
    have h':=(Nat.cast_lt (α:=ℝ)).mpr h
    simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using h'
  have hs:(0:ℝ)≤ s:=Nat.cast_nonneg _
  have hroot:=Real.sq_sqrt hqR
  have hrootpos:=Real.sqrt_nonneg (q:ℝ)
  have hsqr:(Real.sqrt (q:ℝ) * (D:ℝ)) ^ 2=(q:ℝ) * (D:ℝ) ^ 2:=by
    rw [mul_pow,hroot]
  have hl:Real.sqrt (q:ℝ) * D≤ (s:ℝ) + 1:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hcl,hsu,hsqr,ht,hs]
  have hu:(s:ℝ) + 1 < Real.sqrt (q:ℝ) * D + 2:=by
    have ht:0≤ Real.sqrt (q:ℝ) * (D:ℝ):=mul_nonneg hrootpos (le_of_lt hDR)
    nlinarith only [hsl,hcu,hsqr,ht,hs,
      sq_nonneg ((s:ℝ) - Real.sqrt (q:ℝ) * D)]
  have heq:(sqrtUpper q D:ℝ)=((s:ℝ) + 1) / D:=by
    simp [sqrtUpper,c,s]
  rw [heq]
  constructor
  · exact (le_div_iff₀ hDR).mpr hl
  · calc
      _ < (Real.sqrt (q:ℝ) * D + 2) / D:=
        (div_lt_div_iff_of_pos_right hDR).mpr hu
      _=_:=by field_simp

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

theorem exists_bounded_integer_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hA:∀ i j, (A i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (A.map (fun z => (z:ℚ))) *ᵥ x=fun i => (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (A.map (fun z => (z:ℚ))) *ᵥ x=(fun i => (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι∧
        (x j).den≤ (Fintype.card ι).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by
  classical
  obtain ⟨x,hxpos,hxeq⟩:=hf
  have hrep:(∑ j,x j • (A.map (fun z => (z:ℚ))).col j) =
      fun i => (b i:ℚ):=by
    ext i
    simpa [Matrix.col,Matrix.mulVec,dotProduct,mul_comm] using congrFun hxeq i
  obtain ⟨z,hzpos,hzeq,hind⟩:=exists_independent_support
    (A.map (fun z => (z:ℚ))).col (fun i => (b i:ℚ)) ⟨x,hxpos,hrep⟩
  let s:=support z
  let C:Matrix κ s ℤ:=fun i j => A i j.1
  have hcpos:∀ i j, (C i j).natAbs≤ H:=fun i j => hA i j.1
  have hcind:LinearIndependent ℚ (C.map (fun a => (a:ℚ))).col:=hind
  have hzfull:(A.map (fun a => (a:ℚ))) *ᵥ z=fun i => (b i:ℚ):=by
    ext i
    simpa [Matrix.col,Matrix.mulVec,dotProduct,mul_comm] using congrFun hzeq i
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
      _=_:=congrFun hzfull i
  have hbnd:=independent_integer_coordinate_bound C b (fun j:s => z j.1)
    H hcpos hb hcind hceq
  have hk:Fintype.card s≤ Fintype.card ι:=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hbound:(Fintype.card s).factorial *
      (Fintype.card κ * H ^ 2) ^ Fintype.card s≤
      (Fintype.card ι).factorial * (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by
    apply Nat.mul_le_mul (Nat.factorial_le hk)
    exact (Nat.pow_le_pow_left (Nat.le_add_right _ _) _).trans
      (Nat.pow_le_pow_right (by omega) hk)
  have hbpos:0 < (Fintype.card ι).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ Fintype.card ι:=by positivity
  refine ⟨z,hzpos,hzfull, ?_⟩
  intro j
  by_cases hj:j∈ s
  · exact ⟨(hbnd ⟨j,hj⟩).1.trans hbound, (hbnd ⟨j,hj⟩).2.trans hbound⟩
  · have hzj:z j=0:=by simpa [s,mem_support] using hj
    simp only [hzj,Rat.num_zero,Rat.den_zero,Int.natAbs_zero]
    omega

theorem exists_bounded_integer_inequality_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (A i j).natAbs≤ H)
    (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      ∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ)∧
        (x j).den≤ (Fintype.card ι + Fintype.card κ).factorial *
          (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ):=by
  classical
  let C:Matrix κ (ι ⊕ κ) ℤ:=fun i =>
    Sum.elim (A i) (fun k => if i=k then 1 else 0)
  have hC:∀ i j, (C i j).natAbs≤ H:=by
    intro i j
    cases j with
    | inl j => exact hA i j
    | inr k => simp only [C,Sum.elim_inr]; split_ifs <;> simp_all
  obtain ⟨x,hxpos,hxrows⟩:=hf
  let z:(ι ⊕ κ)→ ℚ:=Sum.elim x (fun i => (b i:ℚ) - ∑ j, (A i j:ℚ) * x j)
  have hzpos:∀ j,0≤ z j:=by
    intro j
    cases j with
    | inl j => exact hxpos j
    | inr i => exact sub_nonneg.mpr (hxrows i)
  have hzeq:(C.map (fun z => (z:ℚ))) *ᵥ z=fun i => (b i:ℚ):=by
    ext i
    simp [Matrix.mulVec,Matrix.map,dotProduct,C,z,Fintype.sum_sum_type]
  obtain ⟨w,hwpos,hweq,hwbnd⟩:=exists_bounded_integer_point C b H hC hb
    ⟨z,hzpos,hzeq⟩
  refine ⟨fun j => w (.inl j),fun j => hwpos _, ?_, ?_⟩
  · intro i
    have h:=congrFun hweq i
    have heq:(∑ j, (A i j:ℚ) * w (.inl j)) + w (.inr i)=(b i:ℚ):=by
      simpa [Matrix.mulVec,Matrix.map,dotProduct,C,Fintype.sum_sum_type] using h
    linarith [hwpos (.inr i)]
  · intro j
    simpa only [Fintype.card_sum] using hwbnd (.inl j)

theorem exists_capped_integer_inequality_point (A:Matrix κ ι ℤ) (b:κ→ ℤ)
    (H K:ℕ) (hH:1≤ H) (hK:Fintype.card ι + Fintype.card κ≤ K)
    (hA:∀ i j, (A i j).natAbs≤ H) (hb:∀ i, (b i).natAbs≤ H)
    (hf:∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      ∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ)):
    ∃ x:ι→ ℚ, (∀ j,0≤ x j)∧
      (∀ i, (∑ j, (A i j:ℚ) * x j)≤ (b i:ℚ))∧
      ∀ j, (x j).num.natAbs≤ K.factorial * (K * H ^ 2 + 1) ^ K∧
        (x j).den≤ K.factorial * (K * H ^ 2 + 1) ^ K:=by
  obtain ⟨x,hxpos,hxrows,hxbnd⟩:=exists_bounded_integer_inequality_point A b H hH hA hb hf
  have hr:Fintype.card κ≤ K:=by omega
  have hbound:(Fintype.card ι + Fintype.card κ).factorial *
      (Fintype.card κ * H ^ 2 + 1) ^ (Fintype.card ι + Fintype.card κ)≤
      K.factorial * (K * H ^ 2 + 1) ^ K:=by
    apply Nat.mul_le_mul (Nat.factorial_le hK)
    have hbase:Fintype.card κ * H ^ 2 + 1≤ K * H ^ 2 + 1:=
      Nat.add_le_add_right (Nat.mul_le_mul_right (H ^ 2) hr) 1
    exact (Nat.pow_le_pow_left hbase _).trans
      (Nat.pow_le_pow_right (by omega) hK)
  exact ⟨x,hxpos,hxrows,fun j =>
    ⟨(hxbnd j).1.trans hbound, (hxbnd j).2.trans hbound⟩⟩

end Lax109476Proofs.SmallFeasiblePoint

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSizeBounds

variable {ι:Type*} [Fintype ι]

theorem commonDenominator_pos (q:ι→ ℚ):0 < commonDenominator q:=by
  exact Finset.prod_pos (fun i _ => (q i).den_pos)

theorem denominator_dvd (q:ι→ ℚ) (i:ι):(q i).den ∣ commonDenominator q:=by
  classical
  exact Finset.dvd_prod_of_mem (fun i => (q i).den) (Finset.mem_univ i)

theorem clearedNumerator_cast (q:ι→ ℚ) (i:ι):
    (clearedNumerator q i:ℚ)=(commonDenominator q:ℚ) * q i:=by
  have hdiv:(commonDenominator q:ℚ) =
      (commonDenominator q / (q i).den:ℕ) * ((q i).den:ℚ):=by
    exact_mod_cast (Nat.div_mul_cancel (denominator_dvd q i)).symm
  rw [clearedNumerator,Int.cast_mul,Int.cast_natCast]
  conv_rhs => rw [← (q i).num_div_den,hdiv]
  have hd:((q i).den:ℚ) ≠ 0:=by exact_mod_cast (q i).den_ne_zero
  field_simp

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

end Lax109476Proofs.EncodingSize

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerEncoding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.RationalEncoding Lax759944.BinaryWordEncoding
open RationalSizeBounds EncodingSize

def scaledProgram {m n:ℕ} (P:Program ℚ m n) (s:ℚ):Program ℚ m n where
  A i j:=s * P.A i j
  b i:=s * P.b i
  c j:=s * P.c j

theorem integerProgram_eq_scaled {m n:ℕ} (P:Program ℚ m n):
    rationalProgram (integerProgram P)=scaledProgram P (programDenominator P):=by
  unfold rationalProgram integerProgram scaledProgram
  congr 1
  · funext i j
    exact clearedNumerator_cast (programData P) (.inl (i,j))
  · funext i
    exact clearedNumerator_cast (programData P) (.inr (.inl i))
  · funext j
    exact clearedNumerator_cast (programData P) (.inr (.inr j))

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

namespace Lax109476Proofs.IntegerCertificates

open Lax109476.LinearProgram Lax109476.RationalCertificates
open Lax109476.FarkasCertificate Lax109476.RecessionDirection
open IntegerEncoding SmallFeasiblePoint

def BoundedVector {ι:Type*} (B:ℕ) (x:ι→ ℚ):Prop:=
  ∀ i, (x i).num.natAbs≤ B∧ (x i).den≤ B

def BoundedCertificate {m n:ℕ} (B:ℕ):Certificate m n→ Prop
  | .optimal x y => BoundedVector B x∧ BoundedVector B y
  | .infeasible y => BoundedVector B y
  | .unbounded x d => BoundedVector B x∧ BoundedVector B d

private theorem sum_scale {ι:Type*} [Fintype ι] (a x:ι→ ℚ) (t:ℚ):
    (∑ i,a i * (t * x i))=t * ∑ i,a i * x i:=by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalized_small_infeasibility_certificate {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H) (y:Fin m→ ℚ)
    (hy:IsInfeasibilityCertificate (rationalProgram P) y):
    ∃ yr:Fin m→ ℚ,IsValidCertificate (rationalProgram P) (.infeasible yr)∧
      BoundedCertificate (n:=n) (coordinateCap m n H) (.infeasible yr)∧
        dualValue (rationalProgram P) yr≤ -1:=by
  let A:Matrix (Fin n ⊕ Unit) (Fin m) ℤ:=
    Sum.elim (fun j i => -P.A i j) (fun _ => P.b)
  let b:(Fin n ⊕ Unit)→ ℤ:=Sum.elim (fun _ => 0) (fun _ => -1)
  let t:=(-dualValue (rationalProgram P) y)⁻¹
  let z:=fun i => t * y i
  have ht:0 < t:=inv_pos.mpr (neg_pos.mpr hy.2.2)
  have hzpos:∀ i,0≤ z i:=fun i => mul_nonneg ht.le (hy.1 i)
  have hzrows:∀ j, (∑ i, (A j i:ℚ) * z i)≤ (b j:ℚ):=by
    intro j
    cases j with
    | inl j =>
      simp only [A,b,z,Sum.elim_inl,Int.cast_neg,Int.cast_zero]
      rw [sum_scale]
      simp only [neg_mul,Finset.sum_neg_distrib]
      exact mul_nonpos_of_nonneg_of_nonpos ht.le (neg_nonpos.mpr (hy.2.1 j))
    | inr _ =>
      simp only [A,b,z,Sum.elim_inr,Int.cast_neg,Int.cast_one]
      rw [sum_scale]
      change t * dualValue (rationalProgram P) y≤ -1
      dsimp [t]
      rw [inv_neg,neg_mul,inv_mul_cancel₀ (ne_of_lt hy.2.2)]
  have hmat:∀ j i, (A j i).natAbs≤ H:=by
    intro j i
    cases j with
    | inl j => simpa [A] using hA i j
    | inr _ => exact hb i
  have hbound:∀ j, (b j).natAbs≤ H:=by
    intro j
    cases j <;> simp [b,hH]
  obtain ⟨w,hwpos,hwrows,hwsize⟩:=exists_capped_integer_inequality_point A b H
    (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_sum,Fintype.card_fin,Fintype.card_unit]; omega)
    hmat hbound ⟨z,hzpos,hzrows⟩
  refine ⟨w, ⟨hwpos, ?_, ?_⟩,hwsize, ?_⟩
  · intro j
    have h:-columnValue (rationalProgram P) w j≤ 0:=by
      simpa [A,b,columnValue,rationalProgram,Finset.sum_neg_distrib] using hwrows (.inl j)
    linarith
  · have h:dualValue (rationalProgram P) w≤ -1:=by
      simpa [A,b,dualValue,rationalProgram] using hwrows (.inr ())
    linarith
  · simpa [A,b,dualValue,rationalProgram] using hwrows (.inr ())

end Lax109476Proofs.IntegerCertificates

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.Relaxation

open Lax109476.LinearProgram Lax109476.FarkasCertificate
open Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates RationalFeasibility

def RelaxedFeasible {m n:ℕ} (P:Program ℝ m n) (ε:ℝ) (x:Fin n→ ℝ):Prop:=
  (∀ j, -ε≤ x j)∧ ∀ i,rowValue P x i≤ P.b i + ε

theorem farkas_excludes_relaxation {m n:ℕ} (P:Program ℝ m n)
    (y:Fin m→ ℝ) (B H ε:ℝ) (_hB:0≤ B) (hH:0≤ H) (hε:0≤ ε)
    (hy:IsInfeasibilityCertificate P y) (hdual:dualValue P y≤ -1)
    (hyB:∀ i,y i≤ B) (hAH:∀ i j, |P.A i j|≤ H)
    (hgap:ε * ((m:ℝ) * B + (n:ℝ) * m * H * B) < 1):
    ¬ ∃ x,RelaxedFeasible P ε x:=by
  have hysum:(∑ i,y i)≤ (m:ℝ) * B:=by
    calc
      _≤ ∑ _i:Fin m,B:=Finset.sum_le_sum (fun i _ => hyB i)
      _=_:=by simp
  have hcol:∀ j,columnValue P y j≤ (m:ℝ) * H * B:=by
    intro j
    calc
      _≤ ∑ _i:Fin m,H * B:=by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul ((le_abs_self _).trans (hAH i j)) (hyB i) (hy.1 i) hH
      _=_:=by simp; ring
  have hcolsum:(∑ j,columnValue P y j)≤ (n:ℝ) * m * H * B:=by
    calc
      _≤ ∑ _j:Fin n, ((m:ℝ) * H * B):=Finset.sum_le_sum (fun j _ => hcol j)
      _=_:=by simp; ring
  rintro ⟨x,hx⟩
  have hlo:-ε * ∑ j,columnValue P y j≤ ∑ j,columnValue P y j * x j:=by
    calc
      _=∑ j,columnValue P y j * -ε:=by rw [← Finset.sum_mul]; ring
      _≤ _:=Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (hx.1 j) (hy.2.1 j))
  have hup:(∑ j,columnValue P y j * x j)≤ dualValue P y + ε * ∑ i,y i:=by
    rw [Lax109476Proofs.Basic.transpose_identity]
    calc
      _≤ ∑ i, (P.b i + ε) * y i:=Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hx.2 i) (hy.1 i))
      _=_:=by simp [dualValue,add_mul,Finset.sum_add_distrib,Finset.mul_sum]
  have hlob:=mul_le_mul_of_nonpos_left hcolsum (neg_nonpos.mpr hε)
  have hupb:=add_le_add hdual (mul_le_mul_of_nonneg_left hysum hε)
  have hcontr:=(hlob.trans hlo).trans (hup.trans hupb)
  nlinarith

theorem row_perturbation_bound {m n:ℕ} (P:Program ℝ m n)
    (x e:Fin n→ ℝ) (H r:ℝ) (hH:0≤ H) (_hr:0≤ r)
    (hA:∀ i j, |P.A i j|≤ H) (he:∀ j, |e j|≤ r) (i:Fin m):
    |rowValue P (x + e) i - rowValue P x i|≤ (n:ℝ) * H * r:=by
  have hrow:rowValue P (x + e) i - rowValue P x i=∑ j,P.A i j * e j:=by
    simp [rowValue,mul_add,Finset.sum_add_distrib]
  rw [hrow]
  calc
    _≤ ∑ j, |P.A i j * e j|:=Finset.abs_sum_le_sum_abs _ _
    _≤ ∑ _j:Fin n,H * r:=by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact mul_le_mul (hA i j) (he j) (abs_nonneg _) hH
    _=_:=by simp; ring

theorem perturbation_feasible {m n:ℕ} (P:Program ℝ m n)
    (x e:Fin n→ ℝ) (H r ε:ℝ) (hH:0≤ H) (hr:0≤ r)
    (hrε:r≤ ε) (hrowε:(n:ℝ) * H * r≤ ε)
    (hA:∀ i j, |P.A i j|≤ H) (he:∀ j, |e j|≤ r)
    (hx:PrimalFeasible P x):RelaxedFeasible P ε (x + e):=by
  constructor
  · intro j
    have h:=(abs_le.mp (he j)).1
    change -ε≤ x j + e j
    linarith [hx.1 j]
  · intro i
    have h:=(abs_le.mp (row_perturbation_bound P x e H r hH hr hA he i)).2
    linarith [hx.2 i]

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

theorem relaxation_gap (m n H B:ℕ):
    (1 / (relaxationDenominator m n H B:ℝ)) *
      ((m:ℝ) * B + (n:ℝ) * m * H * B) < 1:=by
  let G:ℝ:=(m:ℝ) * B + (n:ℝ) * m * H * B
  have hG:0≤ G:=by dsimp [G]; positivity
  have hden:0 < 2 * (G + 1):=by linarith
  change (1 / (relaxationDenominator m n H B:ℝ)) * G < 1
  have hd:(relaxationDenominator m n H B:ℝ)=2 * (G + 1):=by
    simp [relaxationDenominator,G]
  rw [hd,one_div,inv_mul_eq_div]
  exact (div_lt_one hden).mpr (by linarith)

theorem integer_relaxation_infeasible {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:¬ IsFeasible (toReal (rationalProgram P))):
    ¬ ∃ x,RelaxedFeasible (toReal (rationalProgram P))
      (1 / (relaxationDenominator m n H (coordinateCap m n H):ℝ)) x:=by
  have hrat:¬ ∃ x:Fin n→ ℚ,PrimalFeasible (rationalProgram P) x:=by
    rintro ⟨x,hx⟩
    exact hf ⟨realVector x,cast_feasible _ x hx⟩
  obtain ⟨y,hy⟩:=rational_farkas_exists (rationalProgram P) hrat
  obtain ⟨yr,hyr,hsize,hdual⟩:=normalized_small_infeasibility_certificate
    P H hH hA hb y hy
  let B:=coordinateCap m n H
  have hyreal:=cast_farkas (rationalProgram P) yr hyr
  have hdy:dualValue (toReal (rationalProgram P)) (realVector yr)≤ -1:=by
    have h:=(Rat.cast_le (K:=ℝ)).mpr hdual
    simpa [dualValue,toReal,rationalProgram,realVector] using h
  have hmag:∀ i,realVector yr i≤ (B:ℝ):=fun i =>
    (le_abs_self _).trans (rational_magnitude_bound (yr i) B (hsize i).1)
  have ha:∀ i j, |(toReal (rationalProgram P)).A i j|≤ (H:ℝ):=by
    intro i j
    have h:((P.A i j).natAbs:ℝ)≤ (H:ℝ):=by exact_mod_cast hA i j
    simpa [toReal,rationalProgram,Nat.cast_natAbs,Int.cast_abs] using h
  apply farkas_excludes_relaxation _ (realVector yr) (B:ℝ) (H:ℝ) _
    (by positivity) (by positivity) (by positivity) hyreal hdy hmag ha
  exact relaxation_gap m n H B

theorem bounded_real_feasible_point {m n:ℕ} (P:Program ℤ m n)
    (H:ℕ) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):
    ∃ x:Fin n→ ℝ,PrimalFeasible (toReal (rationalProgram P)) x∧
      ∀ j, |x j|≤ (coordinateCap m n H:ℝ):=by
  obtain ⟨x,hx⟩:=Lax109476Proofs.RationalFeasibility.rational_feasibility
    m n (rationalProgram P) hf
  obtain ⟨yr,hypos,hyrows,hysize⟩:=SmallFeasiblePoint.exists_capped_integer_inequality_point
    (P.A:Matrix (Fin m) (Fin n) ℤ) P.b H (2 * (m + n) + 2) hH
    (by simp only [Fintype.card_fin]; omega) hA hb ⟨x,hx⟩
  have hy:PrimalFeasible (rationalProgram P) yr:= ⟨hypos,hyrows⟩
  exact ⟨realVector yr,cast_feasible _ yr hy,
    fun j => rational_magnitude_bound (yr j) _ (hysize j).1⟩

theorem coordinate_bound_of_ball {n:ℕ} (e:Fin n→ ℝ) (r:ℝ) (hr:0≤ r)
    (he:dotProduct e e≤ r ^ 2) (j:Fin n):|e j|≤ r:=by
  have hj:e j * e j≤ dotProduct e e:=
    Finset.single_le_sum (fun i _ => mul_self_nonneg (e i)) (Finset.mem_univ j)
  nlinarith [sq_abs (e j),abs_nonneg (e j)]

noncomputable def cubeRadius (n:ℕ) (H ε:ℝ):ℝ:=ε / ((n:ℝ) * H + 1)

theorem cubeRadius_bounds (n:ℕ) (H ε:ℝ) (hH:0≤ H) (hε:0 < ε):
    0 < cubeRadius n H ε∧ cubeRadius n H ε≤ ε∧
      (n:ℝ) * H * cubeRadius n H ε≤ ε:=by
  have hnH:0≤ (n:ℝ) * H:=by positivity
  have hden:0 < (n:ℝ) * H + 1:=by linarith
  refine ⟨div_pos hε hden, ?_, ?_⟩
  · exact (div_le_iff₀ hden).mpr (by nlinarith)
  · dsimp [cubeRadius]
    rw [← mul_div_assoc]
    exact (div_le_iff₀ hden).mpr (by nlinarith)

theorem ball_in_relaxation {m n:ℕ} (P:Program ℝ m n) (H ε:ℝ)
    (hH:0≤ H) (hε:0 < ε) (hA:∀ i j, |P.A i j|≤ H)
    (x:Fin n→ ℝ) (hx:PrimalFeasible P x):
    ∀ e:Fin n→ ℝ,dotProduct e e≤ (cubeRadius n H ε) ^ 2→
      RelaxedFeasible P ε (x + e):=by
  obtain ⟨hr,hrε,hnHr⟩:=cubeRadius_bounds n H ε hH hε
  intro e he
  exact perturbation_feasible P x e H _ ε hH hr.le hrε hnHr hA
    (fun j => coordinate_bound_of_ball e _ hr.le he j) hx

end Lax109476Proofs.Relaxation

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.RationalSeparation

open Lax109476.RationalCertificates

theorem firstViolation_none {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ):
    firstViolation A b c=none↔ ∀ i,rowValue A c i≤ b i:=by
  simp [firstViolation,List.find?_eq_none,not_lt]

theorem firstViolation_violates {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i):b i < rowValue A c i:=by
  have hp:=List.find?_some h
  simpa using hp

theorem integer_normal_norm {n:ℕ} (a:Fin n→ ℤ) (ha:a ≠ 0):
    1≤ (fun j => (a j:ℝ)) ⬝ᵥ (fun j => (a j:ℝ)):=by
  obtain ⟨j,hj⟩:∃ j,a j ≠ 0:=by
    by_contra! h
    exact ha (funext h)
  have habs:(1:ℝ)≤ |(a j:ℝ)|:=by
    have h:(1:ℕ)≤ (a j).natAbs:=Int.natAbs_pos.mpr hj
    have hh:(1:ℝ)≤ ((a j).natAbs:ℝ):=by exact_mod_cast h
    simpa [Nat.cast_natAbs,Int.cast_abs] using hh
  have hsq:(1:ℝ)≤ (a j:ℝ) * (a j:ℝ):=by nlinarith [sq_abs (a j:ℝ)]
  exact hsq.trans (Finset.single_le_sum (fun k _ => mul_self_nonneg (a k:ℝ))
    (Finset.mem_univ j))

theorem violation_retains_points {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i) (x:Fin n→ ℝ)
    (hx:(∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ)):
    realVector (rationalRow A i) ⬝ᵥ (x - realVector c) < 0:=by
  have hc:=(Rat.cast_lt (K:=ℝ)).mpr (firstViolation_violates A b c i h)
  have hid:realVector (rationalRow A i) ⬝ᵥ (x - realVector c) =
      (∑ j, (A i j:ℝ) * x j) - (rowValue A c i:ℝ):=by
    simp [realVector,rationalRow,dotProduct,rowValue,mul_sub,Finset.sum_sub_distrib]
  rw [hid]
  linarith

theorem zero_row_infeasible {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (i:Fin m)
    (h:firstViolation A b c=some i) (hzero:A i=0):
    ¬ ∃ x:Fin n→ ℝ, ∀ k, (∑ j, (A k j:ℝ) * x j)≤ (b k:ℝ):=by
  have hv:=firstViolation_violates A b c i h
  have hneg:b i < 0:=by simpa [rowValue,hzero] using hv
  rintro ⟨x,hx⟩
  have hi:=hx i
  have hpos:(0:ℝ)≤ (b i:ℝ):=by simpa [hzero] using hi
  exact (not_lt_of_ge hpos) ((Rat.cast_lt_zero (K:=ℝ)).mpr hneg)

end Lax109476Proofs.RationalSeparation

end

section

namespace Lax109476Proofs.EllipsoidStep

noncomputable def centralCutForm (n r t:ℝ):ℝ:=
  (n + 1) ^ 2 / n ^ 2 * (t + 1 / (n + 1)) ^ 2 +
    (n ^ 2 - 1) / n ^ 2 * (r - t ^ 2)

theorem centralCutForm_le_one (n r t:ℝ) (hn:2≤ n)
    (hr:r≤ 1) (ht₁:-1≤ t) (ht₂:t≤ 0):
    centralCutForm n r t≤ 1:=by
  have hnpos:0 < n:=by linarith
  have hnzero:n ≠ 0:=ne_of_gt hnpos
  have hnplus:n + 1 ≠ 0:=by linarith
  have hid:centralCutForm n r t =
      ((n ^ 2 - 1) * r + 2 * (n + 1) * t * (t + 1) + 1) / n ^ 2:=by
    unfold centralCutForm
    field_simp
    ring
  rw [hid]
  apply (div_le_one (sq_pos_of_pos hnpos)).mpr
  have hcoeff:0≤ n ^ 2 - 1:=by nlinarith
  have hrad:=mul_le_mul_of_nonneg_left hr hcoeff
  have htprod:t * (t + 1)≤ 0:=
    mul_nonpos_of_nonpos_of_nonneg ht₂ (by linarith)
  have hterm:2 * (n + 1) * (t * (t + 1))≤ 0:=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) htprod
  nlinarith

noncomputable def determinantFactor (n:ℕ):ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) ^ (n - 1) *
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2

theorem determinantFactor_pos (n:ℕ) (hn:2≤ n):0 < determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  unfold determinantFactor
  apply mul_pos
  · apply pow_pos
    apply div_pos <;> nlinarith
  · apply sq_pos_of_pos
    apply div_pos <;> linarith

theorem log_determinantFactor_le (n:ℕ) (hn:2≤ n):
    Real.log (determinantFactor n)≤ -1 / ((n:ℝ) + 1):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hdiff:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  let a:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let b:=(n:ℝ) / ((n:ℝ) + 1)
  have ha:0 < a:=div_pos (sq_pos_of_pos hnp) hdiff
  have hb:0 < b:=div_pos hnp hplus
  have hlogA:=Real.log_le_sub_one_of_pos ha
  have hlogB:=Real.log_le_sub_one_of_pos hb
  have hk:((n - 1:ℕ):ℝ)=(n:ℝ) - 1:=by
    rw [Nat.cast_sub (by omega),Nat.cast_one]
  have heqA:((n - 1:ℕ):ℝ) * (a - 1)=1 / ((n:ℝ) + 1):=by
    rw [hk]
    dsimp [a]
    field_simp
    ring
  have heqB:2 * (b - 1)=-2 / ((n:ℝ) + 1):=by
    dsimp [b]
    field_simp
    ring
  have hA:=mul_le_mul_of_nonneg_left hlogA (Nat.cast_nonneg (n - 1))
  have hB:=mul_le_mul_of_nonneg_left hlogB (show (0:ℝ)≤ 2 by norm_num)
  rw [heqA] at hA
  rw [heqB] at hB
  change Real.log (a ^ (n - 1) * b ^ 2)≤ _
  rw [Real.log_mul (ne_of_gt (pow_pos ha _)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow,Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  calc
    _≤ 1 / ((n:ℝ) + 1) + -2 / ((n:ℝ) + 1):=add_le_add hA hB
    _=-1 / ((n:ℝ) + 1):=by ring

open Matrix

theorem enlarged_shrink_bound (n:ℕ) (hn:2≤ n) (δ:ℝ) (hδ:0≤ δ)
    (hδsmall:δ≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):
    (1 + δ) ^ n * Real.sqrt (determinantFactor n)≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnp:0 < (n:ℝ):=by linarith
  have hplus:0 < (n:ℝ) + 1:=by linarith
  have hbase:0 < 1 + δ:=by linarith
  have hsqrt:=Real.sqrt_pos.mpr (determinantFactor_pos n hn)
  have hlogbase:Real.log (1 + δ)≤ δ:=by
    simpa using Real.log_le_sub_one_of_pos hbase
  have hlogshrink:Real.log (Real.sqrt (determinantFactor n))≤
      -1 / (2 * ((n:ℝ) + 1)):=by
    rw [Real.log_sqrt (le_of_lt (determinantFactor_pos n hn))]
    calc
      _≤ (-1 / ((n:ℝ) + 1)) / 2:=
        div_le_div_of_nonneg_right (log_determinantFactor_le n hn) (by norm_num)
      _=_:=by field_simp
  have hδmul:(n:ℝ) * δ≤ 1 / (4 * ((n:ℝ) + 1)):=by
    calc
      _≤ (n:ℝ) * (1 / (4 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hδsmall (le_of_lt hnp)
      _=_:=by field_simp
  have hlogbound:Real.log ((1 + δ) ^ n * Real.sqrt (determinantFactor n))≤
      -1 / (4 * ((n:ℝ) + 1)):=by
    rw [Real.log_mul (ne_of_gt (pow_pos hbase n)) (ne_of_gt hsqrt),Real.log_pow]
    calc
      _≤ (n:ℝ) * δ + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add (mul_le_mul_of_nonneg_left hlogbase (le_of_lt hnp)) hlogshrink
      _≤ 1 / (4 * ((n:ℝ) + 1)) + -1 / (2 * ((n:ℝ) + 1)):=
        add_le_add hδmul (le_refl _)
      _=_:=by field_simp; ring
  simpa only [Real.exp_log (mul_pos (pow_pos hbase n) hsqrt)] using
    Real.exp_le_exp.mpr hlogbound

theorem iterated_shrink_bound (n:ℕ) (v:ℕ→ ℝ)
    (hstep:∀ k,v (k + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k)
    (k:ℕ):
    v k≤ Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0:=by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v k:=hstep k
        _≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) *
            (Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))) * v 0):=
          mul_le_mul_of_nonneg_left ih (le_of_lt (Real.exp_pos _))
        _=_:=by
          rw [← mul_assoc, ← Real.exp_add]
          congr 2
          push_cast
          ring

end Lax109476Proofs.EllipsoidStep

end

section

namespace Lax109476Proofs.EllipsoidRounding

open Matrix

theorem symmetric_form {ι:Type} [Fintype ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (u v:ι→ ℝ):
    u ⬝ᵥ (A *ᵥ v)=v ⬝ᵥ (A *ᵥ u):=by
  have ht:Aᵀ=A:=(Matrix.isHermitian_iff_isSymm.mp hA).eq
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,ht,dotProduct_comm]

theorem quadratic_error_bound {n:ℕ} (E:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (hE:∀ i j, |E i j|≤ ε) (x:Fin n→ ℝ):
    |x ⬝ᵥ (E *ᵥ x)|≤ (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have hcs:(∑ i, |x i|) ^ 2≤ (n:ℝ) * (x ⬝ᵥ x):=by
    have h:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _:Fin n => (1:ℝ)) (fun i => |x i|)
    simpa [dotProduct,sq_abs,pow_two] using h
  calc
    _=|∑ i, ∑ j,x i * E i j * x j|:=by
      simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,mul_assoc]
    _≤ ∑ i, ∑ j, |x i * E i j * x j|:=by
      exact (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _≤ ∑ i, ∑ j,ε * |x i| * |x j|:=by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      simp only [abs_mul]
      calc
        _≤ |x i| * ε * |x j|:=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hE i j) (abs_nonneg _)) (abs_nonneg _)
        _=_:=by ring
    _=ε * (∑ i, |x i|) ^ 2:=by
      simp only [Finset.mul_sum,Finset.sum_mul,pow_two]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _≤ ε * ((n:ℝ) * (x ⬝ᵥ x)):=mul_le_mul_of_nonneg_left hcs hε
    _=_:=by ring

theorem posDef_of_quadratic_le {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.IsHermitian)
    (hAB:∀ x,x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ (B *ᵥ x)):B.PosDef:=by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hB
  intro x hx
  have hpos:0 < x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.dotProduct_mulVec_pos hx
  simpa using hpos.trans_le (hAB x)

theorem inverse_variational_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (x y:ι→ ℝ):
    2 * (x ⬝ᵥ y) - y ⬝ᵥ (A *ᵥ y)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:A *ᵥ (A⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hnonneg:0≤ (y - A⁻¹ *ᵥ x) ⬝ᵥ (A *ᵥ (y - A⁻¹ *ᵥ x)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (y - A⁻¹ *ᵥ x)
  rw [Matrix.mulVec_sub,hcancel,sub_dotProduct,dotProduct_sub,
    dotProduct_sub,symmetric_form hA.1 (A⁻¹ *ᵥ x) y,hcancel,
    dotProduct_comm y x,dotProduct_comm (A⁻¹ *ᵥ x) x] at hnonneg
  linarith

theorem inverse_quadratic_antitone {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef)
    (hAB:∀ y,y ⬝ᵥ (A *ᵥ y)≤ y ⬝ᵥ (B *ᵥ y)) (x:ι→ ℝ):
    x ⬝ᵥ (B⁻¹ *ᵥ x)≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
  have hcancel:B *ᵥ (B⁻¹ *ᵥ x)=x:=by
    rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv B
      ((Matrix.isUnit_iff_isUnit_det B).mp hB.isUnit),Matrix.one_mulVec]
  have hvar:=inverse_variational_bound hA x (B⁻¹ *ᵥ x)
  have hle:=hAB (B⁻¹ *ᵥ x)
  rw [hcancel,dotProduct_comm (B⁻¹ *ᵥ x) x] at hle
  linarith

def realShape {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ):
    Matrix (Fin n) (Fin n) ℝ:=fun i j => (A i j:ℝ)

theorem enlargement_sandwich {n:ℕ} (A R:Matrix (Fin n) (Fin n) ℝ)
    (ε:ℝ) (hε:0≤ ε) (herr:∀ i j, |R i j - A i j|≤ ε)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (A *ᵥ x)≤ x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)∧
      x ⬝ᵥ ((R + ((n:ℝ) * ε) • 1) *ᵥ x)≤
        x ⬝ᵥ (A *ᵥ x) + 2 * (n:ℝ) * ε * (x ⬝ᵥ x):=by
  have h:=quadratic_error_bound (R - A) ε hε herr x
  rw [Matrix.sub_mulVec,dotProduct_sub] at h
  have hh:=abs_le.mp h
  simp only [Matrix.add_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_add,dotProduct_smul,smul_eq_mul]
  constructor <;> linarith [hh.1,hh.2]

theorem roundedShape_sandwich {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape A *ᵥ x)≤ x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)∧
      x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
        x ⬝ᵥ (realShape A *ᵥ x) + (2 * (n:ℝ) / D) * (x ⬝ᵥ x):=by
  let R:Matrix (Fin n) (Fin n) ℝ:=
    fun i j => (RationalRounding.roundDown (A i j) D:ℝ)
  have herr:∀ i j, |R i j - realShape A i j|≤ 1 / (D:ℝ):=by
    intro i j
    have h:=RationalRounding.roundDown_error (A i j) D hD
    dsimp [R,realShape]
    rw [abs_of_nonpos (by linarith [h.1])]
    linarith [h.2]
  have hid:realShape (roundedShape A D)=R + ((n:ℝ) * (1 / D)) • 1:=by
    ext i j
    change ((RationalRounding.roundDown (A i j) D +
      ((n:ℚ) / D) * (if i=j then 1 else 0):ℚ):ℝ) =
      (RationalRounding.roundDown (A i j) D:ℝ) +
        ((n:ℝ) * (1 / D)) * (if i=j then 1 else 0)
    split_ifs <;> simp [div_eq_mul_inv]
  rw [hid]
  simpa only [mul_one_div] using
    enlargement_sandwich (realShape A) R (1 / D) (by positivity) herr x

theorem roundedShape_isHermitian {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:A.IsSymm) (D:ℕ):(realShape (roundedShape A D)).IsHermitian:=by
  rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
  intro i j
  simp [realShape,roundedShape,hA.apply i j,Matrix.one_apply,eq_comm]

theorem roundedShape_posDef {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape A D)).PosDef:=by
  have hsym:A.IsSymm:=by
    apply Matrix.IsSymm.ext
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    dsimp [realShape] at h
    exact_mod_cast h
  exact posDef_of_quadratic_le hA (roundedShape_isHermitian A hsym D)
    (fun x => (roundedShape_sandwich A D hD x).1)

theorem roundedShape_contains {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (hA:(realShape A).PosDef) (D:ℕ) (hD:0 < D) (x:Fin n→ ℝ)
    (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1):
    x ⬝ᵥ ((realShape (roundedShape A D))⁻¹ *ᵥ x)≤ 1:=
  (inverse_quadratic_antitone hA (roundedShape_posDef A hA D hD)
    (fun y => (roundedShape_sandwich A D hD y).1) x).trans hx

theorem roundedShape_relative_bound {n:ℕ} (A:Matrix (Fin n) (Fin n) ℚ)
    (D:ℕ) (hD:0 < D) (lowerBound η:ℝ) (hη:0≤ η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ η * lowerBound) (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedShape A D) *ᵥ x)≤
      (1 + η) * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  have hxx:0≤ x ⬝ᵥ x:=by
    simpa using dotProduct_star_self_nonneg x
  have herror:=mul_le_mul_of_nonneg_right hprecision hxx
  have hrelative:=mul_le_mul_of_nonneg_left (hlower x) hη
  have hround:=(roundedShape_sandwich A D hD x).2
  nlinarith only [herror,hrelative,hround]

theorem inverse_smul {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (k:ℝ) (hk:k ≠ 0):
    (k • A)⁻¹=k⁻¹ • A⁻¹:=by
  apply Matrix.inv_eq_right_inv
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),
    inv_mul_cancel₀ hk,one_smul]

theorem inverse_form_upper_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x)) (x:ι→ ℝ):
    x ⬝ᵥ (A⁻¹ *ᵥ x)≤ lowerBound⁻¹ * (x ⬝ᵥ x):=by
  have hI:(1:Matrix ι ι ℝ).PosDef:=Matrix.PosDef.one
  have hlI:(lowerBound • (1:Matrix ι ι ℝ)).PosDef:=hI.smul hl
  have horder:∀ y,y ⬝ᵥ ((lowerBound • (1:Matrix ι ι ℝ)) *ᵥ y)≤
      y ⬝ᵥ (A *ᵥ y):=by
    intro y
    simpa only [Matrix.smul_mulVec,Matrix.one_mulVec,dotProduct_smul,
      smul_eq_mul] using hbound y
  have h:=inverse_quadratic_antitone hlI hA horder x
  rw [inverse_smul hI lowerBound (ne_of_gt hl)] at h
  simpa only [inv_one,Matrix.smul_mulVec,Matrix.one_mulVec,
    dotProduct_smul,smul_eq_mul] using h

theorem center_displacement_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ (A *ᵥ (x + e))≤ (1 + η) ^ 2:=by
  have hnonneg:0≤ (η • x - e) ⬝ᵥ (A *ᵥ (η • x - e)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (η • x - e)
  simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
    dotProduct_sub,smul_dotProduct,dotProduct_smul,smul_eq_mul,
    symmetric_form hA.1 e x] at hnonneg
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hA.1 e x]
  have hb₁:=mul_le_mul_of_nonneg_left hx (show 0≤ η ^ 2 + η by positivity)
  have hb₂:=mul_le_mul_of_nonneg_left he (show 0≤ 1 + η by positivity)
  nlinarith only [hnonneg,hb₁,hb₂,hη]

theorem enlargedShape_contains_displaced {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (η:ℝ) (hη:0 < η)
    (x e:ι→ ℝ) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1)
    (he:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ η ^ 2):
    (x + e) ⬝ᵥ ((((1 + η) ^ 2) • A)⁻¹ *ᵥ (x + e))≤ 1:=by
  have hk:0 < (1 + η) ^ 2:=by positivity
  rw [inverse_smul hA _ (ne_of_gt hk),Matrix.smul_mulVec,
    dotProduct_smul,smul_eq_mul]
  calc
    _≤ ((1 + η) ^ 2)⁻¹ * (1 + η) ^ 2:=
      mul_le_mul_of_nonneg_left (center_displacement_bound hA.inv η hη x e hx he)
        (inv_nonneg.mpr (le_of_lt hk))
    _=1:=inv_mul_cancel₀ (ne_of_gt hk)

theorem roundedCenter_error {n:ℕ} {A:Matrix (Fin n) (Fin n) ℝ}
    (hA:A.PosDef) (lowerBound:ℝ) (hl:0 < lowerBound)
    (hbound:∀ x,lowerBound * (x ⬝ᵥ x)≤ x ⬝ᵥ (A *ᵥ x))
    (c:Fin n→ ℚ) (D:ℕ) (hD:0 < D):
    let e:Fin n→ ℝ:=fun i => (c i:ℝ) - RationalRounding.roundDown (c i) D
    e ⬝ᵥ (A⁻¹ *ᵥ e)≤ lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2):=by
  dsimp only
  apply (inverse_form_upper_bound hA lowerBound hl hbound _).trans
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hl))
  simpa only [dotProduct, ← pow_two] using
    RationalRounding.roundDown_vector_error n c D hD

end Lax109476Proofs.EllipsoidRounding

end

section

namespace Lax109476Proofs.EllipsoidBounds

open Matrix EllipsoidRounding

theorem form_cauchy_schwarz {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosDef) (a x:ι→ ℝ) (ha:a ≠ 0):
    (x ⬝ᵥ (A *ᵥ a)) ^ 2≤ (a ⬝ᵥ (A *ᵥ a)) * (x ⬝ᵥ (A *ᵥ x)):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnonneg:0≤ (q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg (q • x - t • a)
  have hid:(q • x - t • a) ⬝ᵥ (A *ᵥ (q • x - t • a)) =
      q * (q * (x ⬝ᵥ (A *ᵥ x)) - t ^ 2):=by
    simp only [Matrix.mulVec_sub,Matrix.mulVec_smul,sub_dotProduct,
      dotProduct_sub,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.1 a x]
    dsimp [q,t]
    ring
  rw [hid] at hnonneg
  have h:=nonneg_of_mul_nonneg_right hnonneg hq
  change t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x))
  linarith

noncomputable def realCutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℝ)
    (a:Fin n→ ℝ):Matrix (Fin n) (Fin n) ℝ:=
  ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) •
    (A - (2 / (((n:ℝ) + 1) * (a ⬝ᵥ (A *ᵥ a)))) •
      Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a))

theorem realShape_cutShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    realShape (cutShape n A a)=realCutShape n (realShape A) (fun i => (a i:ℝ)):=by
  ext i j
  simp [realShape,cutShape,realCutShape,Matrix.smul_apply,Matrix.sub_apply,
    Matrix.vecMulVec,Matrix.mulVec,dotProduct,Rat.cast_sum,smul_eq_mul]

theorem realCutShape_sandwich (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    ((n:ℝ) / ((n:ℝ) + 1)) ^ 2 * (x ⬝ᵥ (A *ᵥ x))≤
      x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
    x ⬝ᵥ (realCutShape n A a *ᵥ x)≤
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)) * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let t:=x ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hα:0 < α:=by dsimp [α]; apply div_pos <;> nlinarith
  have hβ:0≤ β:=by dsimp [β]; positivity
  have hcs:t ^ 2≤ q * (x ⬝ᵥ (A *ᵥ x)):=form_cauchy_schwarz hA a x ha
  have hcs':t ^ 2 / q≤ x ⬝ᵥ (A *ᵥ x):=(div_le_iff₀ hq).mpr (by nlinarith)
  have hterm:0≤ β * (t ^ 2 / q):=by positivity
  have htermUpper:=mul_le_mul_of_nonneg_left hcs' hβ
  have hid:x ⬝ᵥ (realCutShape n A a *ᵥ x) =
      α * ((x ⬝ᵥ (A *ᵥ x)) - β * (t ^ 2 / q)):=by
    simp only [realCutShape,Matrix.smul_mulVec,Matrix.sub_mulVec,
      Matrix.vecMulVec_mulVec,dotProduct_smul,dotProduct_sub,
      smul_eq_mul]
    dsimp [α,β,q,t]
    simp only [dotProduct_comm (A *ᵥ a) x,div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  have hfactor:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  rw [hid, ← hfactor]
  constructor
  · have h:=mul_le_mul_of_nonneg_left htermUpper (le_of_lt hα)
    nlinarith only [h]
  · have h:=mul_nonneg (le_of_lt hα) hterm
    nlinarith only [h]

theorem realCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):(realCutShape n A a).PosDef:=by
  have hsym:(realCutShape n A a).IsHermitian:=by
    rw [Matrix.isHermitian_iff_isSymm,Matrix.IsSymm.ext_iff]
    intro i j
    have h:=(Matrix.isHermitian_iff_isSymm.mp hA.1).apply i j
    simp [realCutShape,Matrix.smul_apply,Matrix.sub_apply,Matrix.vecMulVec,
      smul_eq_mul,h,mul_comm]
  apply Matrix.PosDef.of_dotProduct_mulVec_pos hsym
  intro x hx
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by positivity
  have hxx:0 < x ⬝ᵥ (A *ᵥ x):=by simpa using hA.dotProduct_mulVec_pos hx
  simpa using (mul_pos hp hxx).trans_le (realCutShape_sandwich n hn A hA a x ha).1

theorem realCutShape_inverse (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a)⁻¹ =
      (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) •
        (A⁻¹ + (2 / (((n:ℝ) - 1) * (a ⬝ᵥ (A *ᵥ a)))) •
          Matrix.vecMulVec a a):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnzero:(n:ℝ) ≠ 0:=by linarith
  have hminus:(n:ℝ) - 1 ≠ 0:=by linarith
  have hplus:(n:ℝ) + 1 ≠ 0:=by linarith
  have hdiff:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hAA:A * A⁻¹=1:=Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)
  have hrow:(A *ᵥ a) ᵥ* A⁻¹=a:=by
    rw [Matrix.vecMul_mulVec, (Matrix.isHermitian_iff_isSymm.mp hA.1).eq,
      hAA,Matrix.vecMul_one]
  have hcross:Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) * Matrix.vecMulVec a a =
      (a ⬝ᵥ (A *ᵥ a)) • Matrix.vecMulVec (A *ᵥ a) a:=by
    rw [Matrix.vecMulVec_mul_vecMulVec,dotProduct_comm]
    ext i j
    simp [Matrix.vecMulVec,smul_eq_mul,mul_assoc,mul_comm,mul_left_comm]
  apply Matrix.inv_eq_right_inv
  unfold realCutShape
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  have hc:(((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
      ((n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1))=1:=by field_simp
  rw [hc,one_smul]
  simp only [mul_add,sub_mul,Matrix.smul_mul,Matrix.mul_smul,smul_smul]
  rw [hAA,hcross,Matrix.mul_vecMulVec,Matrix.vecMulVec_mul,hrow]
  simp only [smul_smul]
  ext i j
  simp only [Matrix.add_apply,Matrix.sub_apply,Matrix.smul_apply,smul_eq_mul]
  field_simp
  ring

theorem det_realCutShape (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (realCutShape n A a).det=A.det * EllipsoidStep.determinantFactor n:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  let q:=a ⬝ᵥ (A *ᵥ a)
  let α:=(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)
  let β:=2 / ((n:ℝ) + 1)
  have hq:q ≠ 0:=by
    have hp:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hfactor:A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a) =
      A * (1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)):=by
    rw [mul_sub,Matrix.mul_one,Matrix.mul_smul,Matrix.mul_vecMulVec]
  have hdet:(1 - (β / q) • Matrix.vecMulVec a (A *ᵥ a)).det=1 - β:=by
    have h:=Matrix.det_one_add_replicateCol_mul_replicateRow
      (ι:=Unit) a (-(β / q) • (A *ᵥ a))
    have hd:a ⬝ᵥ (-(β / q) • (A *ᵥ a))=-β:=by
      rw [dotProduct_smul]
      change -(β / q) * q=-β
      field_simp
    have hd':(-(β / q) • (A *ᵥ a)) ⬝ᵥ a=-β:=by
      rw [dotProduct_comm]
      exact hd
    rw [hd'] at h
    simpa [← Matrix.vecMulVec_eq Unit,sub_eq_add_neg,neg_smul] using h
  have hform:realCutShape n A a =
      α • (A - (β / q) • Matrix.vecMulVec (A *ᵥ a) (A *ᵥ a)):=by
    dsimp [realCutShape,α,β,q]
    congr 2
    congr 1
    simp only [div_eq_mul_inv,_root_.mul_inv_rev]
    ring
  rw [hform,Matrix.det_smul,Fintype.card_fin,hfactor,Matrix.det_mul,hdet]
  have hαβ:α * (1 - β)=((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    dsimp [α,β]
    have hp:(n:ℝ) + 1 ≠ 0:=by linarith
    have hd:(n:ℝ) ^ 2 - 1 ≠ 0:=by nlinarith
    field_simp
    ring
  unfold EllipsoidStep.determinantFactor
  calc
    _=A.det * (α ^ (n - 1) * (α * (1 - β))):=by
      nth_rewrite 1 [show n=(n - 1) + 1 by omega]
      rw [pow_succ]
      ring
    _=_:=by rw [hαβ]

theorem realCutShape_quadratic (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z) =
      EllipsoidStep.centralCutForm n (x ⬝ᵥ (A⁻¹ *ᵥ x))
        ((a ⬝ᵥ x) / Real.sqrt q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  let s:=1 / (((n:ℝ) + 1) * Real.sqrt q)
  let z:=x + s • (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hzz:z ⬝ᵥ (A⁻¹ *ᵥ z) =
      x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q:=by
    dsimp [z]
    simp only [Matrix.mulVec_add,Matrix.mulVec_smul,hc,add_dotProduct,
      dotProduct_add,dotProduct_smul,smul_dotProduct,smul_eq_mul,
      symmetric_form hA.inv.1 (A *ᵥ a) x,dotProduct_comm x a,
      dotProduct_comm (A *ᵥ a) a]
    dsimp [q]
    ring
  have haz:a ⬝ᵥ z=a ⬝ᵥ x + s * q:=by
    simp [z,q,dotProduct_add,dotProduct_smul]
  change z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)=_
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    dotProduct_smul,dotProduct_add,smul_eq_mul,dotProduct_comm z a]
  rw [hzz,haz]
  simp only [op_smul_eq_smul,smul_eq_mul]
  change (((n:ℝ) ^ 2 - 1) / (n:ℝ) ^ 2) *
    ((x ⬝ᵥ (A⁻¹ *ᵥ x) + 2 * s * (a ⬝ᵥ x) + s ^ 2 * q) +
      (2 / (((n:ℝ) - 1) * q)) * (((a ⬝ᵥ x) + s * q) * ((a ⬝ᵥ x) + s * q)))=_
  dsimp [s,EllipsoidStep.centralCutForm]
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  rw [← htsq]
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem realCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0) (hx:x ⬝ᵥ (A⁻¹ *ᵥ x)≤ 1) (hcut:a ⬝ᵥ x≤ 0):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    z ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ z)≤ 1:=by
  dsimp only
  rw [realCutShape_quadratic n hn A hA a x ha]
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  have hav:A *ᵥ a ≠ 0:=by
    intro h
    have h':=hc
    rw [h,Matrix.mulVec_zero] at h'
    exact ha h'.symm
  have hcs:=form_cauchy_schwarz hA.inv (A *ᵥ a) x hav
  rw [hc,dotProduct_comm x a,dotProduct_comm (A *ᵥ a) a] at hcs
  have hcs':((a ⬝ᵥ x) / Real.sqrt q) ^ 2≤ x ⬝ᵥ (A⁻¹ *ᵥ x):=by
    rw [div_pow,Real.sq_sqrt (le_of_lt hq)]
    apply (div_le_iff₀ hq).mpr
    simpa [q,mul_comm] using hcs
  have ht:-1≤ (a ⬝ᵥ x) / Real.sqrt q:=by nlinarith
  exact EllipsoidStep.centralCutForm_le_one n _ _ (by exact_mod_cast hn)
    hx ht (div_nonpos_of_nonpos_of_nonneg hcut (le_of_lt hs))

theorem roundedCutShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D):
    (realShape (roundedShape (cutShape n A a) D)).PosDef:=by
  apply roundedShape_posDef _ _ D hD
  rw [realShape_cutShape]
  exact realCutShape_posDef n hn (realShape A) hA _ ha

theorem roundedCutShape_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:(fun i => (a i:ℝ)) ≠ 0) (D:ℕ) (hD:0 < D)
    (x:Fin n→ ℝ) (hx:x ⬝ᵥ ((realShape A)⁻¹ *ᵥ x)≤ 1)
    (hcut:(fun i => (a i:ℝ)) ⬝ᵥ x≤ 0):
    let ar:Fin n→ ℝ:=fun i => (a i:ℝ)
    let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
    let z:=x + (1 / (((n:ℝ) + 1) * Real.sqrt q)) • (realShape A *ᵥ ar)
    z ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ z)≤ 1:=by
  have hQ:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA _ ha
  apply roundedShape_contains _ hQ D hD
  rw [realShape_cutShape]
  exact realCutShape_contains n hn (realShape A) hA _ x ha hx hcut

theorem realCutShape_coarse_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a x:Fin n→ ℝ)
    (ha:a ≠ 0):
    (1 / 4:ℝ) * (x ⬝ᵥ (A *ᵥ x))≤ x ⬝ᵥ (realCutShape n A a *ᵥ x)∧
      x ⬝ᵥ (realCutShape n A a *ᵥ x)≤ 2 * (x ⬝ᵥ (A *ᵥ x)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hxx:0≤ x ⬝ᵥ (A *ᵥ x):=by
    simpa using hA.posSemidef.dotProduct_mulVec_nonneg x
  have hp:0 < (n:ℝ) + 1:=by linarith
  have hd:0 < (n:ℝ) ^ 2 - 1:=by nlinarith
  have hratio:(1 / 2:ℝ)≤ (n:ℝ) / ((n:ℝ) + 1):=
    (le_div_iff₀ hp).mpr (by linarith)
  have hlo:(1 / 4:ℝ)≤ ((n:ℝ) / ((n:ℝ) + 1)) ^ 2:=by
    nlinarith
  have hhi:(n:ℝ) ^ 2 / ((n:ℝ) ^ 2 - 1)≤ 2:=
    (div_le_iff₀ hd).mpr (by nlinarith)
  have h:=realCutShape_sandwich n hn A hA a x ha
  exact ⟨(mul_le_mul_of_nonneg_right hlo hxx).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right hhi hxx)⟩

theorem dyadic_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (2:ℝ) ^ (l + s + n + 1)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hpow:(0:ℝ) < 2 ^ (l + s + n + 1):=by positivity
  apply (div_le_iff₀ hpow).mpr
  simp only [pow_add,pow_one]
  have hl:(2:ℝ) ^ l ≠ 0:=by positivity
  have hs:(2:ℝ) ^ s ≠ 0:=by positivity
  field_simp
  nlinarith

end Lax109476Proofs.EllipsoidBounds

end

section

namespace Lax109476Proofs.EllipsoidCenter

open Matrix EllipsoidRounding EllipsoidBounds
open Lax109476.RationalCertificates

theorem cut_direction_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0):
    (A *ᵥ a) ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ (A *ᵥ a)) =
      (((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * (a ⬝ᵥ (A *ᵥ a)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnm:(n:ℝ) - 1 ≠ 0:=by linarith
  have hq:a ⬝ᵥ (A *ᵥ a) ≠ 0:=by
    have hp:0 < a ⬝ᵥ (A *ᵥ a):=by simpa using hA.dotProduct_mulVec_pos ha
    exact ne_of_gt hp
  have hc:A⁻¹ *ᵥ (A *ᵥ a)=a:=by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul A
      ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit),Matrix.one_mulVec]
  rw [realCutShape_inverse n hn A hA a ha]
  simp only [Matrix.smul_mulVec,Matrix.add_mulVec,Matrix.vecMulVec_mulVec,
    hc,dotProduct_smul,dotProduct_add,smul_eq_mul,
    op_smul_eq_smul,dotProduct_comm (A *ᵥ a) a]
  field_simp
  ring

theorem center_approximation_form (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r:ℝ) (hr:0 < r):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e) =
      ((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2:=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hnz:(n:ℝ) ≠ 0:=by linarith
  have hnp:(n:ℝ) + 1 ≠ 0:=by linarith
  have hrz:r ≠ 0:=ne_of_gt hr
  dsimp only
  simp only [Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [cut_direction_form n hn A hA a ha]
  change _=((r - Real.sqrt q) / ((n:ℝ) * r)) ^ 2
  generalize ht:Real.sqrt q=t
  have htpos:0 < t:=ht ▸ Real.sqrt_pos.mpr hq
  have htsq:t ^ 2=q:=by rw [← ht,Real.sq_sqrt (le_of_lt hq)]
  change (1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
    ((1 / (((n:ℝ) + 1) * r) - 1 / (((n:ℝ) + 1) * t)) *
      ((((n:ℝ) + 1) ^ 2 / (n:ℝ) ^ 2) * q))=_
  rw [← htsq]
  have htz:t ≠ 0:=ne_of_gt htpos
  field_simp
  ring

theorem center_approximation_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℝ) (hA:A.PosDef) (a:Fin n→ ℝ)
    (ha:a ≠ 0) (r ε:ℝ)
    (hr:Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ r)
    (herr:r - Real.sqrt (a ⬝ᵥ (A *ᵥ a))≤ ε):
    let q:=a ⬝ᵥ (A *ᵥ a)
    let e:=(1 / (((n:ℝ) + 1) * r) -
      1 / (((n:ℝ) + 1) * Real.sqrt q)) • (A *ᵥ a)
    e ⬝ᵥ ((realCutShape n A a)⁻¹ *ᵥ e)≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=by
  let q:=a ⬝ᵥ (A *ᵥ a)
  have hq:0 < q:=by simpa [q] using hA.dotProduct_mulVec_pos ha
  have hs:0 < Real.sqrt q:=Real.sqrt_pos.mpr hq
  have hrp:0 < r:=hs.trans_le hr
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have ht:0≤ r - Real.sqrt q:=by linarith
  have hε:0≤ ε:=ht.trans herr
  have hsquare:q≤ r ^ 2:=by nlinarith [Real.sq_sqrt (le_of_lt hq)]
  dsimp only
  rw [center_approximation_form n hn A hA a ha r hrp,div_pow,mul_pow]
  change (r - Real.sqrt q) ^ 2 / ((n:ℝ) ^ 2 * r ^ 2)≤ _
  calc
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * r ^ 2):=
      div_le_div_of_nonneg_right (by nlinarith) (by positivity)
    _≤ ε ^ 2 / ((n:ℝ) ^ 2 * q):=
      div_le_div_of_nonneg_left (sq_nonneg ε) (by positivity)
        (mul_le_mul_of_nonneg_left hsquare (sq_nonneg _))

theorem form_add_le_two {ι:Type} [Fintype ι] [DecidableEq ι]
    {B:Matrix ι ι ℝ} (hB:B.PosDef) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (B *ᵥ (u + v))≤
      2 * (u ⬝ᵥ (B *ᵥ u)) + 2 * (v ⬝ᵥ (B *ᵥ v)):=by
  have h:0≤ (u - v) ⬝ᵥ (B *ᵥ (u - v)):=by
    simpa using hB.posSemidef.dotProduct_mulVec_nonneg (u - v)
  simp only [Matrix.mulVec_sub,sub_dotProduct,dotProduct_sub,
    symmetric_form hB.1 v u] at h
  simp only [Matrix.mulVec_add,add_dotProduct,dotProduct_add,
    symmetric_form hB.1 v u]
  linarith

noncomputable def exactCenter (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ):Fin n→ ℝ:=
  realVector c -
    (1 / (((n:ℝ) + 1) * Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
      (realShape A *ᵥ realVector a)

theorem cast_direction_form (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ):
    ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ)=realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
  simp [dotProduct,Matrix.mulVec,realShape,realVector,Rat.cast_sum]

theorem approximateCenter_difference (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a c:Fin n→ ℚ) (D:ℕ):
    exactCenter n A a c - realVector (approximateCenter n A a c D) =
      (1 / (((n:ℝ) + 1) * (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ)) -
        1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
        (realShape A *ᵥ realVector a):=by
  ext i
  simp [exactCenter,approximateCenter,realVector,realShape,Matrix.mulVec,
    dotProduct,Rat.cast_sum,smul_eq_mul]
  ring

theorem roundedCenter_total_error (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound η:ℝ) (hl:0 < lowerBound)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ η ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ η ^ 2 / 4):
    let e:=exactCenter n A a c - realVector (roundedCenter n A a c D)
    e ⬝ᵥ ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ e)≤ η ^ 2:=by
  let ar:=realVector a
  let q:=ar ⬝ᵥ (realShape A *ᵥ ar)
  let Q:=realShape (roundedShape (cutShape n A a) D)
  let e₁:=exactCenter n A a c - realVector (approximateCenter n A a c D)
  let e₂:=realVector (approximateCenter n A a c D) - realVector (roundedCenter n A a c D)
  have hq:0 < q:=by simpa [q,ar] using hA.dotProduct_mulVec_pos ha
  have hqrat:0≤ a ⬝ᵥ (A *ᵥ a):=by
    have hp:(0:ℝ)≤ ((a ⬝ᵥ (A *ᵥ a):ℚ):ℝ):=by
      rw [cast_direction_form]
      exact le_of_lt hq
    exact_mod_cast hp
  have hQ:Q.PosDef:=roundedCutShape_posDef n hn A hA a ha D hD
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA ar ha
  have horder:∀ y,y ⬝ᵥ (realShape (cutShape n A a) *ᵥ y)≤ y ⬝ᵥ (Q *ᵥ y):=
    fun y => (roundedShape_sandwich (cutShape n A a) D hD y).1
  have h₁:e₁ ⬝ᵥ (Q⁻¹ *ᵥ e₁)≤ η ^ 2 / 4:=by
    apply (inverse_quadratic_antitone hC hQ horder e₁).trans
    rw [realShape_cutShape]
    obtain ⟨hr,herr⟩:=RationalRounding.sqrtUpper_bounds (a ⬝ᵥ (A *ᵥ a)) hqrat D hD
    rw [cast_direction_form] at hr herr
    have hb:=center_approximation_error n hn (realShape A) hA ar ha
      (RationalRounding.sqrtUpper (a ⬝ᵥ (A *ᵥ a)) D:ℝ) (2 / D) hr (by linarith)
    change e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤ _
    have hid:(2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q) =
        4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 * q):=by ring
    have hb':e₁ ⬝ᵥ ((realCutShape n (realShape A) ar)⁻¹ *ᵥ e₁)≤
        (2 / (D:ℝ)) ^ 2 / ((n:ℝ) ^ 2 * q):=by
      dsimp [e₁]
      rw [approximateCenter_difference]
      exact hb
    exact hb'.trans (hid ▸ hsqrt)
  have h₂:e₂ ⬝ᵥ (Q⁻¹ *ᵥ e₂)≤ η ^ 2 / 4:=by
    have h:=roundedCenter_error hQ lowerBound hl hlower (approximateCenter n A a c D) D hD
    exact h.trans hgrid
  have he:exactCenter n A a c - realVector (roundedCenter n A a c D)=e₁ + e₂:=by
    dsimp [e₁,e₂]
    abel
  dsimp only
  rw [he]
  have h:=form_add_le_two hQ.inv e₁ e₂
  linarith

theorem realShape_roundedStepShape (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (η:ℚ):
    realShape (roundedStepShape n A a D η) =
      ((1 + (η:ℝ)) ^ 2) • realShape (roundedShape (cutShape n A a) D):=by
  ext i j
  simp [realShape,roundedStepShape,Matrix.smul_apply,smul_eq_mul]

theorem roundedStepShape_posDef (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η):(realShape (roundedStepShape n A a D η)).PosDef:=by
  rw [realShape_roundedStepShape]
  apply (roundedCutShape_posDef n hn A hA a ha D hD).smul
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  positivity

theorem roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (lowerBound:ℝ) (hl:0 < lowerBound) (η:ℚ) (hη:0 < η)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x))
    (hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4)
    (hgrid:lowerBound⁻¹ * ((n:ℝ) * (1 / D) ^ 2)≤ (η:ℝ) ^ 2 / 4)
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  have hQ:=roundedCutShape_posDef n hn A hA a ha D hD
  have he:=roundedCenter_total_error n hn A hA a c ha D hD lowerBound η hl hlower hsqrt hgrid
  have hxe:(x - exactCenter n A a c) ⬝ᵥ
      ((realShape (roundedShape (cutShape n A a) D))⁻¹ *ᵥ
        (x - exactCenter n A a c))≤ 1:=by
    have h:=roundedCutShape_contains n hn A hA a ha D hD (x - realVector c) hx hcut
    have hid:x - exactCenter n A a c=x - realVector c +
        (1 / (((n:ℝ) + 1) *
          Real.sqrt (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))) •
            (realShape A *ᵥ realVector a):=by
      unfold exactCenter
      abel
    rw [hid]
    exact h
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have h:=enlargedShape_contains_displaced hQ η hp
    (x - exactCenter n A a c)
    (exactCenter n A a c - realVector (roundedCenter n A a c D)) hxe he
  rw [realShape_roundedStepShape]
  simpa only [sub_add_sub_cancel] using h

end Lax109476Proofs.EllipsoidCenter

end

section

namespace Lax109476Proofs.EllipsoidPrecision

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter
open Lax109476.RationalCertificates

theorem gridDenominator_pos (l s n:ℕ):0 < gridDenominator l s n:=by
  unfold gridDenominator
  positivity

theorem grid_shape_precision (l s n:ℕ):
    2 * (n:ℝ) / (gridDenominator l s n:ℝ)≤
      ((2:ℝ) ^ s)⁻¹ * ((2:ℝ) ^ l)⁻¹:=by
  have hp:(2:ℝ) ^ (l + s + n + 1)≤ (gridDenominator l s n:ℝ):=by
    unfold gridDenominator
    exact_mod_cast Nat.pow_le_pow_right (show 0 < 2 by decide)
      (show l + s + n + 1≤ l + s + n + 3 by omega)
  exact (div_le_div_of_nonneg_left (by positivity) (by positivity) hp).trans
    (dyadic_shape_precision l s n)

theorem dyadic_center_precision (l s n:ℕ):
    4 / (((gridDenominator l s n:ℕ):ℝ) ^ 2 * ((2:ℝ) ^ l)⁻¹)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4∧
    (((2:ℝ) ^ l)⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤
        (((2:ℝ) ^ s)⁻¹) ^ 2 / 4:=by
  let L:=(2:ℝ) ^ l
  let S:=(2:ℝ) ^ s
  let N:=(2:ℝ) ^ (n + 3)
  have hL:1≤ L:=one_le_pow₀ (by norm_num)
  have hS:0 < S:=by dsimp [S]; positivity
  have hN:8≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    have h:=one_le_pow₀ (show (1:ℝ)≤ 2 by norm_num) (n:=n)
    linarith
  have hn:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have hnN:8 * (n:ℝ)≤ N:=by
    dsimp [N]
    rw [pow_add]
    norm_num only [show (2:ℝ) ^ 3=8 by norm_num]
    nlinarith
  have hLN:N ^ 2≤ L * N ^ 2:=by
    simpa using mul_le_mul_of_nonneg_right hL (sq_nonneg N)
  have hid:(gridDenominator l s n:ℝ)=L * S * N:=by
    simp only [gridDenominator,Nat.cast_pow,Nat.cast_ofNat]
    dsimp [L,S,N]
    rw [show l + s + n + 3=l + s + (n + 3) by omega,pow_add,pow_add]
  have hLz:L ≠ 0:=by linarith
  have hSz:S ≠ 0:=ne_of_gt hS
  have hNz:N ≠ 0:=by linarith
  change 4 / ((gridDenominator l s n:ℝ) ^ 2 * L⁻¹)≤ (S⁻¹) ^ 2 / 4∧
    (L⁻¹)⁻¹ * ((n:ℝ) * (1 / (gridDenominator l s n:ℝ)) ^ 2)≤ (S⁻¹) ^ 2 / 4
  rw [hid,inv_inv]
  constructor
  · field_simp
    nlinarith only [hN,hLN]
  · field_simp
    nlinarith only [hN,hnN,hLN]

theorem exactCut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
  have he:((2:ℝ) ^ (l + 2))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
    rw [pow_add]
    norm_num
  rw [he]
  calc
    _=(1 / 4:ℝ) * (((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)):=by ring
    _≤ (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x)):=
      mul_le_mul_of_nonneg_left (hbound x) (by norm_num)
    _≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      rw [realShape_cutShape]
      exact (realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha).1

theorem cut_lower_bound (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ):
    ((2:ℝ) ^ (l + 2))⁻¹ * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=
  (exactCut_lower_bound n hn A hA a ha l hbound x).trans
    (roundedShape_sandwich (cutShape n A a) D hD x).1

theorem uniform_roundedStep_contains (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a c:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l s:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x))
    (x:Fin n→ ℝ)
    (hx:(x - realVector c) ⬝ᵥ ((realShape A)⁻¹ *ᵥ (x - realVector c))≤ 1)
    (hcut:realVector a ⬝ᵥ (x - realVector c)≤ 0):
    let D:=gridDenominator (l + 2) s n
    let η:ℚ:=1 / (2:ℚ) ^ s
    (x - realVector (roundedCenter n A a c D)) ⬝ᵥ
      ((realShape (roundedStepShape n A a D η))⁻¹ *ᵥ
        (x - realVector (roundedCenter n A a c D)))≤ 1:=by
  let D:=gridDenominator (l + 2) s n
  let η:ℚ:=1 / (2:ℚ) ^ s
  let lowerBound:=((2:ℝ) ^ (l + 2))⁻¹
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hη:0 < η:=by dsimp [η]; positivity
  have hl:0 < lowerBound:=by dsimp [lowerBound]; positivity
  have hcast:(η:ℝ)=((2:ℝ) ^ s)⁻¹:=by simp [η]
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hlower:=cut_lower_bound n hn A hA a ha D hD l hbound
  have hq:lowerBound≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by
    have he:lowerBound=(1 / 4:ℝ) * ((2:ℝ) ^ l)⁻¹:=by
      dsimp [lowerBound]
      rw [pow_add]
      norm_num
    have hp:0≤ ((2:ℝ) ^ l)⁻¹:=by positivity
    have h:=hbound (realVector a)
    have h':=mul_le_mul_of_nonneg_left hanorm hp
    rw [he]
    nlinarith only [h,h',hp]
  have hprec:=dyadic_center_precision (l + 2) s n
  have hsqrt:4 / ((n:ℝ) ^ 2 * (D:ℝ) ^ 2 *
      (realVector a ⬝ᵥ (realShape A *ᵥ realVector a)))≤ (η:ℝ) ^ 2 / 4:=by
    rw [hcast]
    apply le_trans _ hprec.1
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    have hn₂:1≤ (n:ℝ) ^ 2:=by nlinarith
    have hprod:=mul_le_mul_of_nonneg_left hq (sq_nonneg (D:ℝ))
    have hqp:0≤ realVector a ⬝ᵥ (realShape A *ᵥ realVector a):=by linarith
    have h:=mul_le_mul_of_nonneg_right hn₂
      (mul_nonneg (sq_nonneg (D:ℝ)) hqp)
    nlinarith only [hprod,h]
  apply roundedStep_contains n hn A hA a c ha D hD lowerBound hl η hη hlower hsqrt
  · simpa only [hcast] using hprec.2
  · exact hx
  · exact hcut

end Lax109476Proofs.EllipsoidPrecision

end

section

namespace Lax109476Proofs.EllipsoidDeterminant

open Matrix EllipsoidRounding

theorem eigenvalue_le_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.IsHermitian) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)) (i:ι):
    hA.eigenvalues i≤ k:=by
  let v:ι→ ℝ:=(hA.eigenvectorBasis i).ofLp
  have hv:v ≠ 0:=by
    intro h
    apply hA.eigenvectorBasis.toBasis.ne_zero i
    ext j
    exact congrFun h j
  have hxx:0 < v ⬝ᵥ v:=by
    simpa using (dotProduct_star_self_pos_iff (v:=v)).mpr hv
  have he:A *ᵥ v=hA.eigenvalues i • v:=hA.mulVec_eigenvectorBasis i
  have h:=hbound v
  rw [he,dotProduct_smul,smul_eq_mul] at h
  exact (mul_le_mul_iff_of_pos_right hxx).mp h

theorem det_le_pow_of_form_bound {ι:Type} [Fintype ι] [DecidableEq ι]
    {A:Matrix ι ι ℝ} (hA:A.PosSemidef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (A *ᵥ x)≤ k * (x ⬝ᵥ x)):
    A.det≤ k ^ Fintype.card ι:=by
  rw [hA.1.det_eq_prod_eigenvalues]
  simpa [RCLike.ofReal_real_eq_id] using Finset.prod_le_prod
    (s:=Finset.univ (α:=ι)) (g:=fun _ => k)
    (fun i _ => hA.eigenvalues_nonneg i)
    (fun i _ => eigenvalue_le_of_form_bound hA.1 k hbound i)

theorem det_le_relative_pow {ι:Type} [Fintype ι] [DecidableEq ι]
    {A B:Matrix ι ι ℝ} (hA:A.PosDef) (hB:B.PosDef) (k:ℝ)
    (hbound:∀ x,x ⬝ᵥ (B *ᵥ x)≤ k * (x ⬝ᵥ (A *ᵥ x))):
    B.det≤ k ^ Fintype.card ι * A.det:=by
  open scoped MatrixOrder in
  have hsqrt:∃ R:Matrix ι ι ℝ,R.IsHermitian∧ IsUnit R∧ R * R=A:=by
    let R:=CFC.sqrt A
    have hRR:R * R=A:=by
      simpa only [pow_two] using CFC.sq_sqrt A hA.posSemidef.nonneg
    have hu:IsUnit (R * R):=hRR.symm ▸ hA.isUnit
    exact ⟨R, (CFC.sqrt_nonneg A).posSemidef.1,
      isUnit_of_mul_isUnit_left hu,hRR⟩
  obtain ⟨R,hR,hu,hRR⟩:=hsqrt
  have hRinv:R⁻¹.IsHermitian:=hR.inv
  have hRi:IsUnit R⁻¹:=Matrix.isUnit_nonsing_inv_iff.mpr hu
  have hRRi:R * R⁻¹=1:=Matrix.mul_nonsing_inv R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  have hRiR:R⁻¹ * R=1:=Matrix.nonsing_inv_mul R
    ((Matrix.isUnit_iff_isUnit_det R).mp hu)
  let C:=R⁻¹ * B * R⁻¹
  have hC:C.PosDef:=by
    simpa only [hRinv.eq] using hB.conjTranspose_mul_mul_same
      (Matrix.mulVec_injective_of_isUnit hRi)
  have hid:R⁻¹ * A * R⁻¹=1:=by
    rw [← hRR, ← Matrix.mul_assoc,hRiR,Matrix.one_mul,hRRi]
  have hform (M:Matrix ι ι ℝ) (x:ι→ ℝ):
      x ⬝ᵥ ((R⁻¹ * M * R⁻¹) *ᵥ x) =
        (R⁻¹ *ᵥ x) ⬝ᵥ (M *ᵥ (R⁻¹ *ᵥ x)):=by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact (symmetric_form hRinv x (M *ᵥ (R⁻¹ *ᵥ x))).trans (dotProduct_comm _ _)
  have hb:∀ x,x ⬝ᵥ (C *ᵥ x)≤ k * (x ⬝ᵥ x):=by
    intro x
    have h:=hbound (R⁻¹ *ᵥ x)
    rw [← hform B x, ← hform A x,hid,Matrix.one_mulVec] at h
    exact h
  have hc:=det_le_pow_of_form_bound hC.posSemidef k hb
  have hdet:B.det=C.det * A.det:=by
    dsimp [C]
    rw [Matrix.det_mul,Matrix.det_mul, ← hRR,Matrix.det_mul]
    have hd:R.det * (R⁻¹).det=1:=by
      rw [← Matrix.det_mul,hRRi,Matrix.det_one]
    calc
      _=B.det * (R.det * (R⁻¹).det) ^ 2:=by rw [hd]; ring
      _=_:=by ring
  rw [hdet]
  exact mul_le_mul_of_nonneg_right hc (le_of_lt hA.det_pos)

end Lax109476Proofs.EllipsoidDeterminant

end

section

namespace Lax109476Proofs.EllipsoidIteration

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision
open EllipsoidDeterminant Lax109476.RationalCertificates

theorem stepAccuracy_pos (n:ℕ):0 < stepAccuracy n:=by
  unfold stepAccuracy
  positivity

theorem stepAccuracy_small (n:ℕ) (hn:2≤ n):
    (stepAccuracy n:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)):=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:0 < 8 * (n:ℝ) * ((n:ℝ) + 1):=by positivity
  have h₁:(n:ℝ)≤ (2:ℝ) ^ n:=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n)).le
  have h₂:(n:ℝ) + 1≤ (2:ℝ) ^ (n + 1):=by
    exact_mod_cast (Nat.lt_two_pow_self (n:=n + 1)).le
  have hprod:=mul_le_mul h₁ h₂ (by positivity) (by positivity)
  have he:(2:ℝ) ^ (2 * n + 4)=8 * ((2:ℝ) ^ n * (2:ℝ) ^ (n + 1)):=by
    rw [← pow_add,show 2 * n + 4=(n + (n + 1)) + 3 by omega,pow_add]
    norm_num
    ring
  have hb:8 * (n:ℝ) * ((n:ℝ) + 1)≤ (2:ℝ) ^ (2 * n + 4):=by
    rw [he]
    nlinarith only [hprod]
  simp only [stepAccuracy,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
  exact div_le_div_of_nonneg_left (by norm_num) hp hb

theorem storedShape_relative_bound (n:ℕ) (A:Matrix (Fin n) (Fin n) ℚ)
    (a:Fin n→ ℚ) (D:ℕ) (hD:0 < D) (η:ℚ) (hη:0≤ η)
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound)
    (x:Fin n→ ℝ):
    x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + (η:ℝ)) ^ 3 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
  have hp:(0:ℝ)≤ η:=by exact_mod_cast hη
  have h:=roundedShape_relative_bound (cutShape n A a) D hD lowerBound η hp hlower hprecision x
  rw [realShape_roundedStepShape]
  simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
  calc
    _≤ (1 + (η:ℝ)) ^ 2 *
        ((1 + (η:ℝ)) * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))):=
      mul_le_mul_of_nonneg_left h (sq_nonneg _)
    _=_:=by ring

theorem storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (ha:realVector a ≠ 0) (D:ℕ) (hD:0 < D)
    (η:ℚ) (hη:0 < η)
    (hsmall:(η:ℝ)≤ 1 / (8 * (n:ℝ) * ((n:ℝ) + 1)))
    (lowerBound:ℝ)
    (hlower:∀ x:Fin n→ ℝ,lowerBound * (x ⬝ᵥ x)≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x))
    (hprecision:2 * (n:ℝ) / D≤ (η:ℝ) * lowerBound):
    Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
  have hp:(0:ℝ) < η:=by exact_mod_cast hη
  have hη₁:(η:ℝ)≤ 1:=by
    have hh:1 / (8 * (n:ℝ) * ((n:ℝ) + 1))≤ 1:=
      (div_le_one (by positivity)).mpr (by nlinarith)
    exact hsmall.trans hh
  have hscalar:(1 + (η:ℝ)) ^ 3≤ (1 + 2 * (η:ℝ)) ^ 2:=by
    have hsq:(η:ℝ) ^ 2≤ η:=by nlinarith
    have hcube:=mul_le_mul_of_nonneg_left hsq (le_of_lt hp)
    nlinarith only [hcube,hp,sq_nonneg (η:ℝ)]
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hP:=roundedStepShape_posDef n hn A hA a ha D hD η hη
  have hrelative:∀ x,x ⬝ᵥ (realShape (roundedStepShape n A a D η) *ᵥ x)≤
      (1 + 2 * (η:ℝ)) ^ 2 * (x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)):=by
    intro x
    have hnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
      simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
    exact (storedShape_relative_bound n A a D hD η (le_of_lt hη) lowerBound hlower hprecision x).trans
      (mul_le_mul_of_nonneg_right hscalar hnonneg)
  have hdet:=det_le_relative_pow hC hP ((1 + 2 * (η:ℝ)) ^ 2) hrelative
  rw [Fintype.card_fin] at hdet
  have hpow:((1 + 2 * (η:ℝ)) ^ 2) ^ n=((1 + 2 * (η:ℝ)) ^ n) ^ 2:=by
    rw [← pow_mul, ← pow_mul,Nat.mul_comm]
  have hsqrt:Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
      (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realShape (cutShape n A a)).det:=by
    have h:=Real.sqrt_le_sqrt hdet
    rw [hpow,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,
      abs_of_nonneg (by positivity)] at h
    exact h
  have hδ:2 * (η:ℝ)≤ 1 / (4 * (n:ℝ) * ((n:ℝ) + 1)):=by
    calc
      _≤ 2 * (1 / (8 * (n:ℝ) * ((n:ℝ) + 1))):=
        mul_le_mul_of_nonneg_left hsmall (by norm_num)
      _=_:=by
        simp only [div_eq_mul_inv,_root_.mul_inv_rev]
        norm_num
        ring
  have hshrink:=EllipsoidStep.enlarged_shrink_bound n hn (2 * (η:ℝ))
    (by positivity) hδ
  rw [realShape_cutShape] at hsqrt
  change Real.sqrt (realShape (roundedStepShape n A a D η)).det≤
    (1 + 2 * (η:ℝ)) ^ n * Real.sqrt (realCutShape n (realShape A) (realVector a)).det at hsqrt
  rw [det_realCutShape n hn (realShape A) hA (realVector a) ha] at hsqrt
  rw [Real.sqrt_mul (le_of_lt hA.det_pos)] at hsqrt
  calc
    _≤ ((1 + 2 * (η:ℝ)) ^ n * Real.sqrt (EllipsoidStep.determinantFactor n)) *
        Real.sqrt (realShape A).det:=by nlinarith only [hsqrt]
    _≤ _:=mul_le_mul_of_nonneg_right hshrink (Real.sqrt_nonneg _)

theorem uniform_storedStep_shrink (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)):
    Real.sqrt (realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))).det≤
      Real.exp (-1 / (4 * ((n:ℝ) + 1))) * Real.sqrt (realShape A).det:=by
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hprec:=grid_shape_precision (l + 2) (2 * n + 4) n
  have hcast:(stepAccuracy n:ℝ)=((2:ℝ) ^ (2 * n + 4))⁻¹:=by
    simp [stepAccuracy]
  apply storedStep_shrink n hn A hA a ha _ (gridDenominator_pos _ _ _)
    (stepAccuracy n) (stepAccuracy_pos n) (stepAccuracy_small n hn)
    (((2:ℝ) ^ (l + 2))⁻¹) (exactCut_lower_bound n hn A hA a ha l hbound)
  simpa only [hcast] using hprec

theorem uniform_storedStep_bounds (n:ℕ) (hn:2≤ n)
    (A:Matrix (Fin n) (Fin n) ℚ) (hA:(realShape A).PosDef)
    (a:Fin n→ ℚ) (hanorm:1≤ realVector a ⬝ᵥ realVector a)
    (l:ℕ) (hbound:∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ l)⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape A *ᵥ x)) (x:Fin n→ ℝ):
    let P:=realShape (roundedStepShape n A a
      (gridDenominator (l + 2) (2 * n + 4) n) (stepAccuracy n))
    (1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤ x ⬝ᵥ (P *ᵥ x)∧
      x ⬝ᵥ (P *ᵥ x)≤ 4 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
  let D:=gridDenominator (l + 2) (2 * n + 4) n
  let η:=stepAccuracy n
  have hD:0 < D:=gridDenominator_pos _ _ _
  have hp:(0:ℝ) < η:=by exact_mod_cast stepAccuracy_pos n
  have ha:realVector a ≠ 0:=by
    intro h
    rw [h,dotProduct_zero] at hanorm
    norm_num at hanorm
  have hη:(η:ℝ)≤ 1 / 8:=by
    have hnR:(2:ℝ)≤ n:=by exact_mod_cast hn
    apply (stepAccuracy_small n hn).trans
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  have hC:(realShape (cutShape n A a)).PosDef:=by
    rw [realShape_cutShape]
    exact realCutShape_posDef n hn (realShape A) hA (realVector a) ha
  have hR:=roundedCutShape_posDef n hn A hA a ha D hD
  have hnonneg:0≤ x ⬝ᵥ (realShape (roundedShape (cutShape n A a) D) *ᵥ x):=by
    simpa using hR.posSemidef.dotProduct_mulVec_nonneg x
  have hcutnonneg:0≤ x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x):=by
    simpa using hC.posSemidef.dotProduct_mulVec_nonneg x
  have hfactor:1≤ (1 + (η:ℝ)) ^ 2:=by nlinarith
  have hfactorUpper:(1 + (η:ℝ)) ^ 3≤ 2:=by
    calc
      _≤ (9 / 8:ℝ) ^ 3:=pow_le_pow_left₀ (by positivity) (by linarith) 3
      _≤ _:=by norm_num
  have hprec:2 * (n:ℝ) / D≤ (η:ℝ) * ((2:ℝ) ^ (l + 2))⁻¹:=by
    simpa [η,stepAccuracy] using grid_shape_precision (l + 2) (2 * n + 4) n
  have hrelative:=storedShape_relative_bound n A a D hD η (le_of_lt (stepAccuracy_pos n))
    _ (exactCut_lower_bound n hn A hA a ha l hbound) hprec x
  have hcoarse:=realCutShape_coarse_bounds n hn (realShape A) hA (realVector a) x ha
  have hcoarse':(1 / 4:ℝ) * (x ⬝ᵥ (realShape A *ᵥ x))≤
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)∧
      x ⬝ᵥ (realShape (cutShape n A a) *ᵥ x)≤ 2 * (x ⬝ᵥ (realShape A *ᵥ x)):=by
    rw [realShape_cutShape]
    exact hcoarse
  dsimp only
  constructor
  · apply hcoarse'.1.trans
    apply (roundedShape_sandwich (cutShape n A a) D hD x).1.trans
    rw [realShape_roundedStepShape]
    simp only [Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul]
    exact le_mul_of_one_le_left hnonneg hfactor
  · apply hrelative.trans
    have h:=mul_le_mul_of_nonneg_right hfactorUpper hcutnonneg
    nlinarith only [h,hcoarse'.2]

end Lax109476Proofs.EllipsoidIteration

end

section

namespace Lax109476Proofs.EllipsoidSequence

open Matrix EllipsoidRounding EllipsoidBounds EllipsoidCenter EllipsoidPrecision EllipsoidIteration
open Lax109476.RationalCertificates

def shapes (n:ℕ) (a:ℕ→ Fin n→ ℚ):ℕ→ Matrix (Fin n) (Fin n) ℚ
  | 0 => 1
  | k + 1 => roundedStepShape n (shapes n a k) (a k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)

def centers (n:ℕ) (a:ℕ→ Fin n→ ℚ) (c₀:Fin n→ ℚ):ℕ→ Fin n→ ℚ
  | 0 => c₀
  | k + 1 => roundedCenter n (shapes n a k) (a k) (centers n a c₀ k)
      (gridDenominator (2 * k + 2) (2 * n + 4) n)

theorem shapes_invariant (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    (realShape (shapes n a k)).PosDef∧
    ∀ x:Fin n→ ℝ,
      ((2:ℝ) ^ (2 * k))⁻¹ * (x ⬝ᵥ x)≤ x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)∧
        x ⬝ᵥ (realShape (shapes n a k) *ᵥ x)≤ (4:ℝ) ^ k * (x ⬝ᵥ x):=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      rw [hid]
      exact ⟨Matrix.PosDef.one,by simp⟩
  | succ k ih =>
      have hne:realVector (a k) ≠ 0:=by
        intro h
        have hh:=ha k
        rw [h,dotProduct_zero] at hh
        norm_num at hh
      constructor
      · exact roundedStepShape_posDef n hn _ ih.1 _ hne _
          (gridDenominator_pos _ _ _) _ (stepAccuracy_pos n)
      · intro x
        have hs:=uniform_storedStep_bounds n hn (shapes n a k) ih.1 (a k) (ha k)
          (2 * k) (fun y => (ih.2 y).1) x
        have he:((2:ℝ) ^ (2 * (k + 1)))⁻¹=(1 / 4:ℝ) * ((2:ℝ) ^ (2 * k))⁻¹:=by
          rw [show 2 * (k + 1)=2 * k + 2 by omega,pow_add]
          norm_num
        constructor
        · rw [he]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).1 (show (0:ℝ)≤ 1 / 4 by norm_num)
          change _≤ x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)
          nlinarith only [hh,hs.1]
        · change x ⬝ᵥ (realShape (roundedStepShape n (shapes n a k) (a k)
            (gridDenominator (2 * k + 2) (2 * n + 4) n) (stepAccuracy n)) *ᵥ x)≤ _
          rw [pow_succ]
          have hh:=mul_le_mul_of_nonneg_left (ih.2 x).2 (show (0:ℝ)≤ 4 by norm_num)
          nlinarith only [hh,hs.2]

theorem shapes_shrink (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (k:ℕ):
    Real.sqrt (realShape (shapes n a k)).det≤
      Real.exp (-(k:ℝ) / (4 * ((n:ℝ) + 1))):=by
  let v:=fun j => Real.sqrt (realShape (shapes n a j)).det
  have hstep:∀ j,v (j + 1)≤ Real.exp (-1 / (4 * ((n:ℝ) + 1))) * v j:=by
    intro j
    have hi:=shapes_invariant n hn a ha j
    exact uniform_storedStep_shrink n hn (shapes n a j) hi.1 (a j) (ha j)
      (2 * j) (fun x => (hi.2 x).1)
  have h:=EllipsoidStep.iterated_shrink_bound n v hstep k
  have hid:realShape (shapes n a 0)=1:=by
    ext i j
    simp [shapes,realShape,Matrix.one_apply,apply_ite]
  simpa only [v,hid,Matrix.det_one,Real.sqrt_one,mul_one] using h

theorem preserves_points_up_to (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (x:Fin n→ ℝ) (hx:(x - realVector c₀) ⬝ᵥ (x - realVector c₀)≤ 1)
    (k:ℕ)
    (hcut:∀ j < k,realVector (a j) ⬝ᵥ (x - realVector (centers n a c₀ j))≤ 0):
    (x - realVector (centers n a c₀ k)) ⬝ᵥ
      ((realShape (shapes n a k))⁻¹ *ᵥ (x - realVector (centers n a c₀ k)))≤ 1:=by
  induction k with
  | zero =>
      have hid:realShape (shapes n a 0)=1:=by
        ext i j
        simp [shapes,realShape,Matrix.one_apply,apply_ite]
      simpa only [centers,hid,inv_one,Matrix.one_mulVec] using hx
  | succ k ih =>
      have hi:=shapes_invariant n hn a ha k
      exact uniform_roundedStep_contains n hn (shapes n a k) hi.1 (a k) (centers n a c₀ k)
        (ha k) (2 * k) (2 * n + 4) (fun y => (hi.2 y).1) x
        (ih (fun j hj => hcut j (by omega))) (hcut k (by omega))

theorem shapes_below_threshold (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (B:ℕ):
    Real.sqrt (realShape (shapes n a (thresholdSteps n B))).det <
      (((2:ℝ) ^ B)⁻¹) ^ n:=by
  have htarget:0 < (((2:ℝ) ^ B)⁻¹) ^ n:=by positivity
  have hlog:Real.log (2:ℝ)≤ 1:=by
    have h:=Real.log_le_sub_one_of_pos (show (0:ℝ) < 2 by norm_num)
    linarith
  have hlogtarget:Real.log ((((2:ℝ) ^ B)⁻¹) ^ n) =
      -((B * n:ℕ):ℝ) * Real.log 2:=by
    rw [Real.log_pow,Real.log_inv,Real.log_pow]
    push_cast
    ring
  have he:-(thresholdSteps n B:ℝ) / (4 * ((n:ℝ) + 1)) =
      -(((B * n:ℕ):ℝ) + 1):=by
    have hp:(n:ℝ) + 1 ≠ 0:=by positivity
    unfold thresholdSteps
    push_cast
    field_simp
  have hlt:-(((B * n:ℕ):ℝ) + 1) < -((B * n:ℕ):ℝ) * Real.log 2:=by
    have h:=mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg (B * n))
    linarith
  have h:=shapes_shrink n hn a ha (thresholdSteps n B)
  rw [he] at h
  apply h.trans_lt
  rw [← Real.exp_log htarget,hlogtarget]
  exact Real.exp_lt_exp.mpr hlt

end Lax109476Proofs.EllipsoidSequence

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidBall

open Matrix EllipsoidRounding EllipsoidDeterminant

variable {ι:Type} [Fintype ι] [DecidableEq ι]

theorem quadratic_parallelogram (A:Matrix ι ι ℝ) (u v:ι→ ℝ):
    (u + v) ⬝ᵥ (A *ᵥ (u + v)) + (u - v) ⬝ᵥ (A *ᵥ (u - v)) =
      2 * (u ⬝ᵥ (A *ᵥ u)) + 2 * (v ⬝ᵥ (A *ᵥ v)):=by
  simp only [Matrix.mulVec_add,Matrix.mulVec_sub,add_dotProduct,sub_dotProduct,
    dotProduct_add,dotProduct_sub]
  ring

theorem inverse_form_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    ∀ u:ι→ ℝ,u ⬝ᵥ (A⁻¹ *ᵥ u)≤ (r ^ 2)⁻¹ * (u ⬝ᵥ u):=by
  intro u
  by_cases hu:u=0
  · simp [hu]
  have hnorm:0 < u ⬝ᵥ u:=by
    simpa using (dotProduct_star_self_pos_iff (v:=u)).mpr hu
  let t:=r / Real.sqrt (u ⬝ᵥ u)
  let e:=t • u
  have ht:0 < t:=div_pos hr (Real.sqrt_pos.mpr hnorm)
  have hsq:(Real.sqrt (u ⬝ᵥ u)) ^ 2=u ⬝ᵥ u:=Real.sq_sqrt hnorm.le
  have he:e ⬝ᵥ e=r ^ 2:=by
    simp only [e,smul_dotProduct,dotProduct_smul,smul_eq_mul]
    dsimp [t]
    field_simp
    nlinarith
  have hp:=hball e he.le
  have hm:=hball (-e) (by simpa using he.le)
  have hbase:0≤ (z - c) ⬝ᵥ (A⁻¹ *ᵥ (z - c)):=
    hA.inv.posSemidef.dotProduct_mulVec_nonneg _
  have hid:=quadratic_parallelogram A⁻¹ (z - c) e
  have hp':((z - c) + e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) + e))≤ 1:=by
    have heq:(z - c) + e=z + e - c:=by abel_nf
    rw [heq]
    exact hp
  have hm':((z - c) - e) ⬝ᵥ (A⁻¹ *ᵥ ((z - c) - e))≤ 1:=by
    have heq:(z - c) - e=z + -e - c:=by abel_nf
    rw [heq]
    exact hm
  have hqe:e ⬝ᵥ (A⁻¹ *ᵥ e)≤ 1:=by linarith
  have hqe':t ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ 1:=by
    simpa only [e,Matrix.mulVec_smul,smul_dotProduct,dotProduct_smul,
      smul_eq_mul, ← mul_assoc, ← pow_two] using hqe
  have htform:t ^ 2=r ^ 2 / (u ⬝ᵥ u):=by
    dsimp [t]
    rw [div_pow,hsq]
  rw [htform,div_mul_eq_mul_div] at hqe'
  have hscale:r ^ 2 * (u ⬝ᵥ (A⁻¹ *ᵥ u))≤ u ⬝ᵥ u:=
    (div_le_one hnorm).mp hqe'
  rw [inv_mul_eq_div]
  exact (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa [mul_comm] using hscale)

theorem sqrt_det_lower_bound_of_ball {A:Matrix ι ι ℝ} (hA:A.PosDef)
    (z c:ι→ ℝ) (r:ℝ) (hr:0 < r)
    (hball:∀ e:ι→ ℝ,e ⬝ᵥ e≤ r ^ 2→
      (z + e - c) ⬝ᵥ (A⁻¹ *ᵥ (z + e - c))≤ 1):
    r ^ Fintype.card ι≤ Real.sqrt A.det:=by
  have hbound:=inverse_form_bound_of_ball hA z c r hr hball
  have hdet:=det_le_pow_of_form_bound hA.inv.posSemidef ((r ^ 2)⁻¹) hbound
  rw [Matrix.det_nonsing_inv,Ring.inverse_eq_inv,inv_pow] at hdet
  have ha:=hA.det_pos
  have hrpow:0 < (r ^ 2) ^ Fintype.card ι:=pow_pos (sq_pos_of_pos hr) _
  have hd:(r ^ 2) ^ Fintype.card ι≤ A.det:=(inv_le_inv₀ ha hrpow).mp hdet
  have hs:=Real.sq_sqrt ha.le
  have hsr:=Real.sqrt_nonneg A.det
  have hrr:(r ^ Fintype.card ι) ^ 2=(r ^ 2) ^ Fintype.card ι:=by ring
  nlinarith [pow_nonneg hr.le (Fintype.card ι)]

end Lax109476Proofs.EllipsoidBall

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidTermination

open Lax109476.RationalCertificates
open EllipsoidRounding EllipsoidSequence EllipsoidBall

theorem cannot_retain_ball (n:ℕ) (hn:2≤ n) (a:ℕ→ Fin n→ ℚ)
    (ha:∀ k,1≤ realVector (a k) ⬝ᵥ realVector (a k)) (c₀:Fin n→ ℚ)
    (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector c₀) ⬝ᵥ (z + e - realVector c₀)≤ 1):
    ¬ ∀ k < thresholdSteps n B, ∀ e:Fin n→ ℝ,
      e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      realVector (a k) ⬝ᵥ (z + e - realVector (centers n a c₀ k))≤ 0:=by
  intro hcut
  let K:=thresholdSteps n B
  have hshape:=(shapes_invariant n hn a ha K).1
  have hball:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e - realVector (centers n a c₀ K)) ⬝ᵥ
        ((realShape (shapes n a K))⁻¹ *ᵥ (z + e - realVector (centers n a c₀ K)))≤ 1:=by
    intro e he
    exact preserves_points_up_to n hn a ha c₀ (z + e) (hunit e he) K
      (fun j hj => hcut j hj e he)
  have hlo:=sqrt_det_lower_bound_of_ball hshape z (realVector (centers n a c₀ K))
    (((2:ℝ) ^ B)⁻¹) (by positivity) hball
  have hhi:=shapes_below_threshold n hn a ha B
  simp only [Fintype.card_fin] at hlo
  exact (not_lt_of_ge hlo) hhi

end Lax109476Proofs.EllipsoidTermination

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.EllipsoidSearch

open Lax109476.RationalCertificates
open RationalSeparation EllipsoidRounding EllipsoidCenter EllipsoidPrecision
open EllipsoidIteration EllipsoidSequence EllipsoidTermination

@[simp] theorem cacheState_eq {n:ℕ}
    (state:Matrix (Fin n) (Fin n) ℚ × (Fin n→ ℚ)):cacheState state=state:=by
  apply Prod.ext
  · funext i j
    simp [cacheState,Vector.get]
    rfl
  · funext i
    simp [cacheState,Vector.get]
    rfl

def normalSchedule {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (k:ℕ):Fin n→ ℚ:=selectedNormal A b (trajectory A b k).2

theorem fallbackNormal_norm (n:ℕ) (hn:0 < n):
    1≤ realVector (fallbackNormal n) ⬝ᵥ realVector (fallbackNormal n):=by
  let a:Fin n→ ℤ:=fun j => if j.val=0 then 1 else 0
  have ha:a ≠ 0:=by
    intro h
    have hz:=congrFun h ⟨0,hn⟩
    simp [a] at hz
  have hc:realVector (fallbackNormal n) =
      (fun j:Fin n => (if j.val=0 then 1 else 0:ℝ)):=by
    funext j
    change ((if j.val=0 then 1 else 0:ℚ):ℝ)=_
    split_ifs <;> norm_num
  rw [hc]
  simpa [a,apply_ite] using integer_normal_norm a ha

theorem selectedNormal_norm {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (c:Fin n→ ℚ) (hn:0 < n):
    1≤ realVector (selectedNormal A b c) ⬝ᵥ realVector (selectedNormal A b c):=by
  unfold selectedNormal
  split
  · exact fallbackNormal_norm n hn
  · split_ifs with hz
    · exact fallbackNormal_norm n hn
    · change 1≤ (fun j => (A _ j:ℝ)) ⬝ᵥ (fun j => (A _ j:ℝ))
      exact integer_normal_norm _ hz

theorem trajectory_eq_sequences {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (k:ℕ):
    (trajectory A b k).1=shapes n (normalSchedule A b) k∧
      (trajectory A b k).2=centers n (normalSchedule A b) 0 k:=by
  induction k with
  | zero => exact ⟨rfl,rfl⟩
  | succ k ih =>
    simp only [trajectory,nextState,shapes,centers,cacheState_eq]
    have ha:selectedNormal A b (trajectory A b k).2=normalSchedule A b k:=rfl
    rw [ha,ih.1,ih.2]
    exact ⟨rfl,rfl⟩

theorem findFirst_eq_find (p:ℕ→ Bool) (start count:ℕ):
    findFirst p start count=(List.range' start count).find? p:=by
  induction count generalizing start with
  | zero => simp [findFirst]
  | succ count ih =>
    cases hp:p start <;> simp [findFirst,List.range'_succ,ih,hp]

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

theorem findIteration_eq_find {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ) (b:Fin m→ ℚ)
    (K:ℕ):findIteration A b K =
      (List.range (K + 1)).find? (fun k => decide (firstViolation A b (trajectory A b k).2=none)):=by
  change scanStates A b 0 (K + 1) (trajectory A b 0)=_
  rw [scanStates_eq_findFirst,findFirst_eq_find,List.range_eq_range']

theorem foundIteration_feasible {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (K k:ℕ) (h:findIteration A b K=some k):
    ∀ i,rowValue A (trajectory A b k).2 i≤ b i:=by
  rw [findIteration_eq_find] at h
  have hp:=List.find?_some h
  have hv:firstViolation A b (trajectory A b k).2=none:=by simpa using hp
  exact (firstViolation_none A b _).mp hv

theorem noIteration_violated {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (K:ℕ) (h:findIteration A b K=none):
    ∀ k≤ K,firstViolation A b (trajectory A b k).2 ≠ none:=by
  rw [findIteration_eq_find] at h
  have hp:=List.find?_eq_none.mp h
  intro k hk
  simpa using hp k (List.mem_range.mpr (by omega))

theorem search_finds_ball {m n:ℕ} (A:Matrix (Fin m) (Fin n) ℤ)
    (b:Fin m→ ℚ) (hn:2≤ n) (z:Fin n→ ℝ) (B:ℕ)
    (hunit:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      (z + e) ⬝ᵥ (z + e)≤ 1)
    (hfeas:∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ B)⁻¹) ^ 2→
      ∀ i, (∑ j, (A i j:ℝ) * (z + e) j)≤ (b i:ℝ)):
    ∃ k,findIteration A b (thresholdSteps n B)=some k:=by
  by_contra h
  have hnone:findIteration A b (thresholdSteps n B)=none:=by
    cases hfind:findIteration A b (thresholdSteps n B) with
    | none => rfl
    | some k => exact False.elim (h ⟨k,hfind⟩)
  have hnorm:∀ k,1≤ realVector (normalSchedule A b k) ⬝ᵥ
      realVector (normalSchedule A b k):=fun k => selectedNormal_norm A b _ (by omega)
  have hzero:realVector (0:Fin n→ ℚ)=0:=by funext j; simp [realVector]
  apply cannot_retain_ball n hn (normalSchedule A b) hnorm 0 z B
    (by simpa only [hzero,sub_zero] using hunit)
  intro k hk e he
  have hvne:=noIteration_violated A b _ hnone k (by omega)
  cases hv:firstViolation A b (trajectory A b k).2 with
  | none => exact False.elim (hvne hv)
  | some i =>
    have haz:A i ≠ 0:=by
      intro haz
      apply zero_row_infeasible A b _ i hv haz
      exact ⟨z + e,hfeas e he⟩
    have hnormal:normalSchedule A b k=rationalRow A i:=by
      simp [normalSchedule,selectedNormal,hv,haz]
    have hcenter:=(trajectory_eq_sequences A b k).2
    rw [hnormal, ← hcenter]
    exact (violation_retains_points A b _ i hv (z + e) (hfeas e he i)).le

end Lax109476Proofs.EllipsoidSearch

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.NormalizedFeasibility

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation

theorem normalized_iff_relaxed {m n:ℕ} (P:Program ℤ m n) (R:ℕ) (ε:ℚ)
    (z:Fin n→ ℝ):
    (∀ i, (∑ j, (normalizedMatrix P R i j:ℝ) * z j)≤ (normalizedBound P ε i:ℝ))↔
      RelaxedFeasible (toReal (rationalProgram P)) (ε:ℝ) ((R:ℝ) • z):=by
  constructor
  · intro h
    constructor
    · intro j
      have hj:=h (Fin.natAdd m j)
      have hh:-(R:ℝ) * z j≤ (ε:ℝ):=by
        simpa [normalizedMatrix,normalizedBound,apply_ite] using hj
      change -(ε:ℝ)≤ (R:ℝ) * z j
      linarith
    · intro i
      have hi:=h (Fin.castAdd n i)
      simpa [normalizedMatrix,normalizedBound,rowValue,toReal,
        rationalProgram,Finset.mul_sum,mul_assoc,mul_left_comm] using hi
  · rintro ⟨hnonneg,hrows⟩ i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [normalizedMatrix,normalizedBound,rowValue,toReal,
        rationalProgram,Finset.mul_sum,mul_assoc,mul_left_comm] using hrows i
    · intro j
      have hj:-(R:ℝ) * z j≤ (ε:ℝ):=by
        have h:=hnonneg j
        change -(ε:ℝ)≤ (R:ℝ) * z j at h
        linarith
      simpa [normalizedMatrix,normalizedBound,apply_ite] using hj

theorem outerScale_pos (n B:ℕ):0 < outerScale n B:=by
  unfold outerScale
  positivity

theorem outerScale_large (n B:ℕ):
    (n:ℝ) * (B:ℝ) ^ 2≤ (outerScale n B:ℝ) ^ 2 / 16:=by
  have hn:(n:ℝ)≤ ((n:ℝ) + 1) ^ 2:=by nlinarith
  have hb:(B:ℝ) ^ 2≤ ((B:ℝ) + 1) ^ 2:=by
    nlinarith [(Nat.cast_nonneg B:(0:ℝ)≤ B)]
  have h:=mul_le_mul hn hb (sq_nonneg (B:ℝ)) (sq_nonneg ((n:ℝ) + 1))
  simp only [outerScale,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  nlinarith

theorem scaled_point_norm {n:ℕ} (x:Fin n→ ℝ) (B:ℕ)
    (hx:∀ j, |x j|≤ (B:ℝ)):
    ((outerScale n B:ℝ)⁻¹ • x) ⬝ᵥ ((outerScale n B:ℝ)⁻¹ • x)≤ 1 / 16:=by
  have hr:(0:ℝ) < outerScale n B:=by exact_mod_cast outerScale_pos n B
  have hs:x ⬝ᵥ x≤ (n:ℝ) * (B:ℝ) ^ 2:=by
    calc
      _≤ ∑ _j:Fin n, (B:ℝ) ^ 2:=by
        apply Finset.sum_le_sum
        intro j _
        nlinarith [(abs_le.mp (hx j)).1, (abs_le.mp (hx j)).2]
      _=_:=by simp
  have hlarge:=outerScale_large n B
  simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
  rw [← mul_assoc, ← pow_two,inv_pow,inv_mul_eq_div]
  apply (div_le_iff₀ (sq_pos_of_pos hr)).mpr
  linarith

theorem ball_inside_unit {n:ℕ} (z:Fin n→ ℝ) (hz:z ⬝ᵥ z≤ 1 / 16)
    (r:ℝ) (hr:0≤ r) (hrsmall:r≤ 1 / 2):
    ∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ r ^ 2→ (z + e) ⬝ᵥ (z + e)≤ 1:=by
  intro e he
  have h:=EllipsoidCenter.form_add_le_two
    (show (1:Matrix (Fin n) (Fin n) ℝ).PosDef from Matrix.PosDef.one) z e
  simp only [Matrix.one_mulVec] at h
  nlinarith

theorem precisionDenominator_pos (m n H:ℕ):0 < precisionDenominator m n H:=by
  unfold precisionDenominator relaxationDenominator
  positivity

theorem ballDenominator_pos (m n H:ℕ):0 < ballDenominator m n H:=by
  unfold ballDenominator
  exact Nat.mul_pos (Nat.mul_pos (precisionDenominator_pos _ _ _) (by omega))
    (outerScale_pos _ _)

theorem ballDenominator_ge_two (m n H:ℕ):2≤ ballDenominator m n H:=by
  have hD:2≤ precisionDenominator m n H:=by
    unfold precisionDenominator relaxationDenominator
    omega
  exact hD.trans ((Nat.le_mul_of_pos_right _ (by omega:0 < n * H + 1)).trans
    (Nat.le_mul_of_pos_right _ (outerScale_pos _ _)))

theorem dyadic_radius_bound (m n H:ℕ):
    ((2:ℝ) ^ ballExponent m n H)⁻¹≤ 1 / (ballDenominator m n H:ℝ):=by
  have hN:(0:ℝ) < ballDenominator m n H:=by exact_mod_cast ballDenominator_pos m n H
  have hpow:(0:ℝ) < 2 ^ ballExponent m n H:=by positivity
  rw [one_div]
  apply (inv_le_inv₀ hpow hN).mpr
  exact_mod_cast (Nat.lt_size_self (ballDenominator m n H)).le

theorem dyadic_radius_small (m n H:ℕ):
    ((2:ℝ) ^ ballExponent m n H)⁻¹≤ 1 / 2:=by
  have hN:(0:ℝ) < ballDenominator m n H:=by exact_mod_cast ballDenominator_pos m n H
  have hN₂:(2:ℝ)≤ ballDenominator m n H:=by exact_mod_cast ballDenominator_ge_two m n H
  apply (dyadic_radius_bound m n H).trans
  rw [one_div]
  simpa only [one_div] using (inv_le_inv₀ hN (by norm_num:(0:ℝ) < 2)).mpr hN₂

theorem normalized_feasible_ball {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):
    ∃ z:Fin n→ ℝ,
      (∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ ballExponent m n H)⁻¹) ^ 2→
        (z + e) ⬝ᵥ (z + e)≤ 1)∧
      ∀ e:Fin n→ ℝ,e ⬝ᵥ e≤ (((2:ℝ) ^ ballExponent m n H)⁻¹) ^ 2→
        ∀ i, (∑ j, (normalizedMatrix P (outerScale n (coordinateCap m n H)) i j:ℝ) *
          (z + e) j)≤ (normalizedBound P (1 / (precisionDenominator m n H:ℚ)) i:ℝ):=by
  let B:=coordinateCap m n H
  let R:=outerScale n B
  let D:=precisionDenominator m n H
  let ε:ℝ:=1 / (D:ℝ)
  let r:=((2:ℝ) ^ ballExponent m n H)⁻¹
  obtain ⟨x,hx,hxb⟩:=bounded_real_feasible_point P H hH hA hb hf
  let z:=(R:ℝ)⁻¹ • x
  have hR:(0:ℝ) < R:=by exact_mod_cast outerScale_pos n B
  have hD:(0:ℝ) < D:=by exact_mod_cast precisionDenominator_pos m n H
  have hε:0 < ε:=by dsimp [ε]; positivity
  have hHR:(0:ℝ)≤ H:=by positivity
  have hAR:∀ i j, |(toReal (rationalProgram P)).A i j|≤ (H:ℝ):=by
    intro i j
    have h:((P.A i j).natAbs:ℝ)≤ (H:ℝ):=by exact_mod_cast hA i j
    simpa [toReal,rationalProgram,Nat.cast_natAbs,Int.cast_abs] using h
  have hrad:r≤ cubeRadius n (H:ℝ) ε / (R:ℝ):=by
    have hid:cubeRadius n (H:ℝ) ε / (R:ℝ)=1 / (ballDenominator m n H:ℝ):=by
      dsimp only [cubeRadius,ε]
      rw [div_div,div_div]
      congr 1
      simp only [ballDenominator,D,R,B,Nat.cast_mul,Nat.cast_add,Nat.cast_one,mul_assoc]
    rw [hid]
    exact dyadic_radius_bound m n H
  refine ⟨z,ball_inside_unit z (scaled_point_norm x B hxb) r
    (by dsimp [r]; positivity) (dyadic_radius_small m n H), ?_⟩
  intro e he
  change e ⬝ᵥ e≤ r ^ 2 at he
  have hrscale:(R:ℝ) * r≤ cubeRadius n (H:ℝ) ε:=by
    have h:=(le_div_iff₀ hR).mp hrad
    simpa [mul_comm] using h
  have heR:((R:ℝ) • e) ⬝ᵥ ((R:ℝ) • e)≤ (cubeRadius n (H:ℝ) ε) ^ 2:=by
    simp only [smul_dotProduct,dotProduct_smul,smul_eq_mul]
    have h:=mul_le_mul_of_nonneg_left he (sq_nonneg (R:ℝ))
    have hrpos:0≤ r:=by dsimp [r]; positivity
    have hrhopos:=(cubeRadius_bounds n (H:ℝ) ε hHR hε).1
    have hs:((R:ℝ) * r) ^ 2≤ (cubeRadius n (H:ℝ) ε) ^ 2:=
      pow_le_pow_left₀ (mul_nonneg hR.le hrpos) hrscale 2
    nlinarith
  have hrelax:=ball_in_relaxation (toReal (rationalProgram P)) (H:ℝ) ε
    hHR hε hAR x hx ((R:ℝ) • e) heR
  have hscale:(R:ℝ) • (z + e)=x + (R:ℝ) • e:=by
    simp only [z,smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt hR),one_smul]
  apply (normalized_iff_relaxed P R (1 / (D:ℚ)) (z + e)).mpr
  simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,hscale] using hrelax

end Lax109476Proofs.NormalizedFeasibility

end

section

open scoped BigOperators Matrix

namespace Lax109476Proofs.IntegerFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding IntegerCertificates Relaxation NormalizedFeasibility
open EllipsoidSearch EllipsoidSequence

theorem feasible_of_feasible {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H)
    (hf:IsFeasible (toReal (rationalProgram P))):feasible P H=true:=by
  obtain ⟨z,hunit,hball⟩:=normalized_feasible_ball P H hH hA hb hf
  obtain ⟨k,hk⟩:=search_finds_ball
    (normalizedMatrix P (outerScale n (coordinateCap m n H)))
    (normalizedBound P (1 / (precisionDenominator m n H:ℚ))) hn z
    (ballExponent m n H) hunit hball
  simp only [feasible,iterationResult,hk,Option.isSome_some]

theorem feasible_sound {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H) (h:feasible P H=true):
    IsFeasible (toReal (rationalProgram P)):=by
  let R:=outerScale n (coordinateCap m n H)
  let D:=precisionDenominator m n H
  let A:=normalizedMatrix P R
  let b:=normalizedBound P (1 / (D:ℚ))
  cases hi:iterationResult P H with
  | none => simp [feasible,hi] at h
  | some k =>
    have hr:=foundIteration_feasible A b (thresholdSteps n (ballExponent m n H)) k hi
    let x:=realVector (trajectory A b k).2
    have hrreal:∀ i, (∑ j, (A i j:ℝ) * x j)≤ (b i:ℝ):=by
      intro i
      have h:=(Rat.cast_le (K:=ℝ)).mpr (hr i)
      simpa [RationalSeparation.rowValue,x,realVector] using h
    have hrelax:=(normalized_iff_relaxed P R (1 / (D:ℚ)) x).mp hrreal
    by_contra hf
    apply integer_relaxation_infeasible P H hH hA hb hf
    refine ⟨(R:ℝ) • x, ?_⟩
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast,D,precisionDenominator] using hrelax

theorem feasible_correct {m n:ℕ} (P:Program ℤ m n) (H:ℕ)
    (hn:2≤ n) (hH:1≤ H) (hA:∀ i j, (P.A i j).natAbs≤ H)
    (hb:∀ i, (P.b i).natAbs≤ H):
    feasible P H=true↔ IsFeasible (toReal (rationalProgram P)):=
  ⟨feasible_sound P H hH hA hb,feasible_of_feasible P H hn hH hA hb⟩

end Lax109476Proofs.IntegerFeasibilityDecision

end

section

open scoped BigOperators

namespace Lax109476Proofs.FeasibilityPadding

open Lax109476.LinearProgram Lax109476.RationalCertificates
open IntegerEncoding

theorem extend_feasible {m n:ℕ} (P:Program ℝ m n) (x:Fin n→ ℝ)
    (hx:PrimalFeasible P x):
    PrimalFeasible (pad P) (Fin.addCases x (fun _ => 0)):=by
  constructor
  · intro j
    refine Fin.addCases ?_ ?_ j
    · intro j
      simpa using hx.1 j
    · intro j
      simp
  · intro i
    refine Fin.addCases ?_ ?_ i
    · intro i
      simpa [pad,rowValue,Fin.sum_univ_add] using hx.2 i
    · intro i
      simp [pad,rowValue,Fin.sum_univ_add]

theorem restrict_feasible {m n:ℕ} (P:Program ℝ m n) (x:Fin (n + 2)→ ℝ)
    (hx:PrimalFeasible (pad P) x):
    PrimalFeasible P (fun j => x (Fin.castAdd 2 j)):=by
  constructor
  · intro j
    exact hx.1 (Fin.castAdd 2 j)
  · intro i
    simpa [pad,rowValue,Fin.sum_univ_add] using hx.2 (Fin.castAdd 2 i)

theorem pad_feasible_iff {m n:ℕ} (P:Program ℝ m n):
    IsFeasible (pad P)↔ IsFeasible P:=by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨_,restrict_feasible P x hx⟩
  · rintro ⟨x,hx⟩
    exact ⟨_,extend_feasible P x hx⟩

theorem cast_pad {m n:ℕ} (P:Program ℤ m n):
    toReal (rationalProgram (pad P))=pad (toReal (rationalProgram P)):=by
  unfold pad toReal rationalProgram
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

theorem feasible_correct {m n:ℕ} (P:Program ℤ m n) (H:ℕ) (hH:1≤ H)
    (hA:∀ i j, (P.A i j).natAbs≤ H) (hb:∀ i, (P.b i).natAbs≤ H):
    feasible P H=true↔ IsFeasible (toReal (rationalProgram P)):=by
  obtain ⟨ha,hb⟩:=padded_bounds P H hH hA hb
  rw [feasible,IntegerFeasibilityDecision.feasible_correct (pad P) H (by omega) hH ha hb,
    cast_pad,pad_feasible_iff]

end Lax109476Proofs.FeasibilityPadding

end

section

open scoped BigOperators

namespace Lax109476Proofs.RationalFeasibilityDecision

open Lax109476.LinearProgram Lax109476.RationalCertificates Lax109476.RationalEncoding
open Lax759944.BinaryWordEncoding
open IntegerEncoding EncodingSize NormalizedFeasibility EllipsoidSequence IterationBudget

theorem scaled_real_feasible_iff {m n:ℕ} (P:Program ℚ m n) (s:ℚ)
    (hs:0 < s) (x:Fin n→ ℝ):
    PrimalFeasible (toReal (scaledProgram P s)) x↔ PrimalFeasible (toReal P) x:=by
  have hsR:(0:ℝ) < (s:ℝ):=by exact_mod_cast hs
  have hrow:∀ i,rowValue (toReal (scaledProgram P s)) x i =
      (s:ℝ) * rowValue (toReal P) x i:=by
    intro i
    simp only [rowValue,toReal,scaledProgram,Rat.cast_mul,Finset.mul_sum,mul_assoc]
  constructor
  · rintro ⟨hxpos,hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    have h:=hxrows i
    rw [hrow] at h
    have hi:(s:ℝ) * rowValue (toReal P) x i≤ (s:ℝ) * (P.b i:ℝ):=by
      simpa [toReal,scaledProgram] using h
    exact (mul_le_mul_iff_of_pos_left hsR).mp hi
  · rintro ⟨hxpos,hxrows⟩
    refine ⟨hxpos, ?_⟩
    intro i
    rw [hrow]
    simpa [toReal,scaledProgram] using (mul_le_mul_iff_of_pos_left hsR).mpr (hxrows i)

theorem integerProgram_feasible_iff {m n:ℕ} (P:Program ℚ m n):
    IsFeasible (toReal (rationalProgram (integerProgram P)))↔ IsFeasible (toReal P):=by
  rw [integerProgram_eq_scaled]
  have hs:0 < (programDenominator P:ℚ):=by
    exact_mod_cast RationalSizeBounds.commonDenominator_pos (programData P)
  exact exists_congr (fun x => scaled_real_feasible_iff P _ hs x)

theorem coefficient_bounds {m n:ℕ} (P:Program ℚ m n):
    (∀ i j, ((integerProgram P).A i j).natAbs≤ 2 ^ (2 * sizeParameter P))∧
      (∀ i, ((integerProgram P).b i).natAbs≤ 2 ^ (2 * sizeParameter P)):=by
  obtain ⟨hA,hb,_⟩:=integerProgram_bounds P
  have hp:2 ^ (2 * bitSize (encodeProgram P))≤ 2 ^ (2 * sizeParameter P):=
    Nat.pow_le_pow_right (by decide) (by unfold sizeParameter; omega)
  exact ⟨fun i j => (hA i j).trans hp,fun i => (hb i).trans hp⟩

theorem feasible_correct {m n:ℕ} (P:Program ℚ m n):
    feasible P=true↔ IsFeasible (toReal P):=by
  obtain ⟨hA,hb⟩:=coefficient_bounds P
  have hH:1≤ 2 ^ (2 * sizeParameter P):=by
    have hp:0 < 2 ^ (2 * sizeParameter P):=by positivity
    omega
  rw [feasible,FeasibilityPadding.feasible_correct _ _ hH hA hb,
    integerProgram_feasible_iff]

end Lax109476Proofs.RationalFeasibilityDecision

end

theorem solution:∀ {m n:Nat} (P:Lax109476.LinearProgram.Program Rat m n),
  Iff (@Eq Bool (@Lax109476Proofs.RationalFeasibilityDecision.feasible m n P) Bool.true)
    (@Lax109476.LinearProgram.IsFeasible m n (@Lax109476.RationalCertificates.toReal m n P)):= @Lax109476Proofs.RationalFeasibilityDecision.feasible_correct
