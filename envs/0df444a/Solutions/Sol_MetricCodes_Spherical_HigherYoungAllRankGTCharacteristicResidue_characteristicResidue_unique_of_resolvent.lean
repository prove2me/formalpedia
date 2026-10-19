-- Prove2me | solution 1 for MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue.characteristicResidue_unique_of_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:44.831113+00:00
-- url     : https://prove2.me/submissions/30ac6bf4-11ed-493c-84f5-dac40500b2a3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option autoImplicit false
set_option maxHeartbeats 1800000
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 500000
open scoped BigOperators
open MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (nodes : ι → ℝ) (hinjective : Function.Injective nodes)
    (numerator : Polynomial ℝ) (weight : ι → ℝ)
    (hresolvent : ∀ z : ℝ, (∀ i : ι, z ≠ nodes i) →
      numerator.eval z /
          (Lagrange.nodal (Finset.univ : Finset ι) nodes).eval z =
        ∑ i : ι, weight i / (z - nodes i))
    (i : ι) :
    weight i = numerator.eval (nodes i) /
      (Lagrange.nodal (Finset.univ : Finset ι) nodes).derivative.eval
        (nodes i) := by
  classical
  let characteristic : Polynomial ℝ :=
    Lagrange.nodal (Finset.univ : Finset ι) nodes
  have hderivative (j : ι) :
      characteristic.derivative.eval (nodes j) ≠ 0 := by
    intro hzero
    have hweight := Lagrange.nodalWeight_ne_zero
      (s := (Finset.univ : Finset ι)) (v := nodes)
      hinjective.injOn (Finset.mem_univ j)
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ j)] at hweight
    exact hweight (by simp [characteristic, hzero])
  let values : ι → ℝ := fun j =>
    weight j * characteristic.derivative.eval (nodes j)
  let interpolation : Polynomial ℝ :=
    Lagrange.interpolate (Finset.univ : Finset ι) nodes values
  have hinterpolation (z : ℝ) (hz : ∀ j : ι, z ≠ nodes j) :
      interpolation.eval z / characteristic.eval z =
        ∑ j : ι, weight j / (z - nodes j) := by
    have hz' : ∀ j ∈ (Finset.univ : Finset ι), z ≠ nodes j := by
      intro j _
      exact hz j
    have hvalue := Lagrange.eval_interpolate_not_at_node
      (s := (Finset.univ : Finset ι)) (v := nodes) (x := z)
      values hz'
    have hnonzero : characteristic.eval z ≠ 0 :=
      Lagrange.eval_nodal_not_at_node hz'
    change
      (Lagrange.interpolate (Finset.univ : Finset ι) nodes values).eval z /
          characteristic.eval z = _
    rw [hvalue, mul_div_cancel_left₀ _ hnonzero]
    apply Finset.sum_congr rfl
    intro j _
    rw [Lagrange.nodalWeight_eq_eval_derivative_nodal
      (Finset.mem_univ j)]
    dsimp [values]
    change
      (characteristic.derivative.eval (nodes j))⁻¹ *
        (z - nodes j)⁻¹ *
        (weight j * characteristic.derivative.eval (nodes j)) =
        weight j / (z - nodes j)
    have hsub : z - nodes j ≠ 0 := sub_ne_zero.mpr (hz j)
    field_simp [hderivative j, hsub]
  have hpoly : numerator = interpolation := by
    apply Polynomial.eq_of_infinite_eval_eq
    refine (Set.finite_range nodes).infinite_compl.mono ?_
    intro z hz
    have haway : ∀ j : ι, z ≠ nodes j := by
      intro j heq
      exact hz ⟨j, heq.symm⟩
    have hnonzero : characteristic.eval z ≠ 0 :=
      Lagrange.eval_nodal_not_at_node
        (fun j _ => haway j)
    exact (div_left_inj' hnonzero).mp
      ((hresolvent z haway).trans (hinterpolation z haway).symm)
  apply (eq_div_iff (hderivative i)).2
  calc
    weight i * characteristic.derivative.eval (nodes i) = values i := rfl
    _ = interpolation.eval (nodes i) :=
      (Lagrange.eval_interpolate_at_node values hinjective.injOn
        (Finset.mem_univ i)).symm
    _ = numerator.eval (nodes i) := by rw [hpoly]
end MetricCodes.Spherical.HigherYoungAllRankGTCharacteristicResidue
