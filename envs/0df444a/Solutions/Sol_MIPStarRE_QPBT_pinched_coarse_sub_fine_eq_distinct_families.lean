-- Prove2me | solution 1 for MIPStarRE.QPBT.pinched_coarse_sub_fine_eq_distinct_families
-- status  : ACCEPTED   (prove)
-- author  : @Dengnifer
-- created : 2026-10-27T23:38:59.396515+00:00
-- url     : https://prove2.me/submissions/c639c227-57a6-4ff4-8d97-22a4074e5c3d

-- Generated proof for MIPStarRE.QPBT.pinched_coarse_sub_fine_eq_distinct_families.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/- Source helpers from QPBT/Games/DistanceTheorems/Support.lean. -/
/-!
# Finite-dimensional operator estimates for state-dependent distance

This module contains finite-dimensional operator and finite-sum identities used
by the paper-facing distance theorems. It introduces no new mathematical
assumptions or source-facing statements.

## References

- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:295-395`
- `references/ldt-paper/preliminaries.tex:649-666`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT.DistanceCalculus

open LIDT.MIPStarRE.LDT LIDT.MIPStarRE.Quantum
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective



























/-- The state quadratic form is additive over finite sums of operators. This is
the formalization-only identity `lem:distance-qform-finset-sum`, used to expand
the relabeled overlaps in `lem:ld-sandwich`; detailed source proof
`references/neexp-paper/05_quantum_preliminaries.tex:952-999`. -/
theorem stateQForm_finset_sum {β ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : EuclideanSpace ℂ ι) (s : Finset β) (M : β → _root_.LIDT.MIPStarRE.Quantum.Op ι) :
    _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (∑ b ∈ s, M b) = ∑ b ∈ s, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (M b) := by
  simp [_root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm, _root_.MIPStarRE.QPBT.applyOperatorToState]































































end MIPStarRE.QPBT.DistanceCalculus

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem solution {R₁ R₂ Γ₂ ι : Type*}
    [Fintype R₁] [DecidableEq R₁] [Fintype R₂] [DecidableEq R₂]
    [Fintype Γ₂] [DecidableEq Γ₂] [Fintype ι] [DecidableEq ι]
    (P : _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (G opposite : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ₂ ι) (eval : Γ₂ → R₂)
    (ψ : EuclideanSpace ℂ (ι × ι)) :
    (∑ b : R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron ((opposite.postprocess eval).effect b)
        (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a))) -
      (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
        (∑ a : R₁, P.effect a * G.effect g * P.effect a))) =
    ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
      if eval g = eval g' then
        ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g')
          (P.effect a * G.effect g * P.effect a)) else 0 := by
  classical
  set F : Γ₂ → Γ₂ → ℝ := fun g g' => ∑ a : R₁, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
    (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g') (P.effect a * G.effect g * P.effect a)) with hF
  -- the coarse term is the sum of the fine terms over the fibers
  have hcoarse : ∀ b : R₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ
      (_root_.MIPStarRE.QPBT.heteroKron ((opposite.postprocess eval).effect b)
        (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a)) =
      ∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g' := by
    intro b
    have hmid : (∑ a : R₁, P.effect a * (G.postprocess eval).effect b * P.effect a) =
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b),
          ∑ a : R₁, P.effect a * G.effect g * P.effect a := by
      simp only [_root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect, Finset.mul_sum,
        Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [hmid, _root_.LIDT.MIPStarRE.Quantum.Measurement.postprocess_effect,
      _root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_left, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [hF]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  -- the fibers of the evaluation map assemble into the colliding pairs
  have hfib : (∑ b : R₂, ∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
      ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g') =
      ∑ g' : Γ₂, ∑ g : Γ₂, if eval g = eval g' then F g g' else 0 := by
    have hstep : ∀ b : R₂, (∑ g' ∈ Finset.univ.filter (fun g' : Γ₂ => eval g' = b),
        ∑ g ∈ Finset.univ.filter (fun g : Γ₂ => eval g = b), F g g') =
        ∑ g' : Γ₂, ∑ g : Γ₂,
          if eval g' = b then (if eval g = b then F g g' else 0) else 0 := by
      intro b
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun g' _ => ?_
      by_cases h : eval g' = b
      · simp [h, Finset.sum_filter]
      · simp [h]
    rw [Finset.sum_congr rfl fun b _ => hstep b]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (eval g')
      (fun b => if eval g = b then F g g' else 0)]
    simp
  -- splitting off the diagonal
  have hsplit : ∀ g g' : Γ₂, (if eval g = eval g' then F g g' else 0) =
      (if g = g' then F g' g' else 0) +
        (if g = g' then 0 else if eval g = eval g' then F g g' else 0) := by
    intro g g'
    by_cases h : g = g'
    · subst h
      simp
    · simp [h]
  have hdiag : (∑ g' : Γ₂, ∑ g : Γ₂, if g = g' then F g' g' else 0) =
      ∑ g : Γ₂, F g g := by
    refine Finset.sum_congr rfl fun g' _ => ?_
    rw [Finset.sum_ite_eq' Finset.univ g' (fun _ => F g' g')]
    simp
  have hfine : (∑ g : Γ₂, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm ψ (_root_.MIPStarRE.QPBT.heteroKron (opposite.effect g)
      (∑ a : R₁, P.effect a * G.effect g * P.effect a))) = ∑ g : Γ₂, F g g := by
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [hF]
    rw [_root_.MIPStarRE.QPBT.DistanceCalculus.heteroKron_finset_sum_right, _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm_finset_sum]
  rw [Finset.sum_congr rfl fun b _ => hcoarse b, hfib, hfine]
  rw [Finset.sum_congr rfl fun g' _ =>
    Finset.sum_congr rfl fun g _ => hsplit g g']
  simp only [Finset.sum_add_distrib]
  rw [hdiag]
  have hcomm : (∑ g' : Γ₂, ∑ g : Γ₂, if g = g' then 0 else
      if eval g = eval g' then F g g' else 0) =
      ∑ g : Γ₂, ∑ g' : Γ₂, if g = g' then 0 else
        if eval g = eval g' then F g g' else 0 := Finset.sum_comm
  rw [hcomm]
  simp only [hF]
  ring
