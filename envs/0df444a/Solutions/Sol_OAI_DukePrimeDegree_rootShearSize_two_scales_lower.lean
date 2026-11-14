-- Prove2me | solution 1 for OAI.DukePrimeDegree.rootShearSize_two_scales_lower
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-13T06:41:35.243206+00:00
-- url     : https://prove2.me/submissions/c4d78271-8afe-46d0-9a85-a116dd3dc1ea

import Mathlib
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_RootShearing
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Polynomial shearing along a root subgroup

The exact matrix formula is the algebraic part of the low-entropy
argument: conjugation by a root unipotent is quadratic in its parameter.
The exceptional case is precisely the centralizer, and commuting with a
single nonzero root element already characterizes that case.
-/

open scoped BigOperators Classical
open Filter

namespace DukePrimeDegree

open PrimeDegreePackets

/-- The quadratic root-shearing formula, for arbitrary matrix indices. -/
theorem root_conjugation_entry {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (r s : Fin n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s =
      g.1 r s + (if r = i then t * g.1 j s else 0) -
        (if s = j then t * g.1 r i else 0) -
        (if r = i ∧ s = j then t ^ 2 * g.1 j i else 0) := by
  rw [root_mul_entry, root_left_mul_entry, root_left_mul_entry]
  by_cases hr : r = i <;> by_cases hs : s = j
  all_goals simp only [hr, hs, ite_true, if_true, ite_false, if_false, true_and, false_and]
  all_goals ring

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingScale
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A first scale for noncentral root shearing

Every matrix outside a root centralizer has a finite positive first time
at which its conjugation displacement reaches a prescribed size. Before
that time all matrix entries remain uniformly controlled. This is the
stopping-time normalization used for the polynomial shearing argument.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma entry_sub_le_rootShearSize {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) (r s : Fin n) :
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      rootShearSize hij g t := by
  have hs : |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 r s - g.1 r s| ≤
      ∑ u : Fin n, |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u| :=
    Finset.single_le_sum (f := fun u : Fin n =>
      |(Matrix.SpecialLinearGroup.transvection hij t * g *
        Matrix.SpecialLinearGroup.transvection hij (-t)).1 r u - g.1 r u|)
      (fun u _ => abs_nonneg _) (Finset.mem_univ s)
  apply hs.trans
  exact Finset.single_le_sum (f := fun u : Fin n => ∑ v : Fin n,
    |(Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 u v - g.1 u v|)
    (fun u _ => Finset.sum_nonneg (fun v _ => abs_nonneg _))
    (Finset.mem_univ r)

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingCentralizer
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Centralizer limits of normalized shearing trajectories

Uniform control before the first shearing time bounds the quadratic
coefficient. Since the shearing times diverge, the diagonal disturbance
vanishes. Every convergent terminal matrix therefore lies in the root
centralizer. These conclusions use actual special-linear matrices.
-/

open Set Filter
open scoped BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets

lemma root_conjugation_pivot {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (t : ℝ) :
    (Matrix.SpecialLinearGroup.transvection hij t * g *
      Matrix.SpecialLinearGroup.transvection hij (-t)).1 i j - g.1 i j =
      t * (g.1 j j - g.1 i i) - t ^ 2 * g.1 j i := by
  rw [root_conjugation_entry]
  simp only [ite_true, if_true, and_self]
  ring

end DukePrimeDegree

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingProfile
attribute [-instance] _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A positive displacement at one of two annuli

The normalized scale consists of a fixed linear coefficient, the square
root of a quadratic coefficient, and the remaining linear coefficients.
The latter already give a displacement; otherwise the quadratic pivot
cannot cancel at both of the chosen scales.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace DukePrimeDegree

theorem quadratic_two_scales_quarter (a b u v ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1) (ha : |a| ≤ 1)
    (hnorm : 1 / 4 ≤ max |a| |b|)
    (hu : ρ ≤ |u|) (huone : |u| ≤ 1) (hv : 16 / ρ ≤ |v|) :
    ρ / 8 ≤ |a * u - b * u ^ 2| ∨ |v| ≤ |a * v - b * v ^ 2| := by
  by_cases hbsmall : |b| < ρ / 8
  · left
    have hbquarter : |b| < 1 / 4 := by linarith
    have hage : 1 / 4 ≤ |a| := (le_max_iff.mp hnorm).resolve_right hbquarter.not_ge
    have hu2 : |u| ^ 2 ≤ 1 := by nlinarith [sq_nonneg (|u| - 1)]
    have hbu : |b| * |u| ^ 2 ≤ ρ / 8 := by
      have h := mul_le_mul_of_nonneg_left hu2 (abs_nonneg b)
      nlinarith
    have hAu : ρ / 4 ≤ |a| * |u| := by
      have h1 := mul_le_mul_of_nonneg_right hage (abs_nonneg u)
      nlinarith
    have hrev := abs_add_le (a * u - b * u ^ 2) (b * u ^ 2)
    rw [sub_add_cancel, abs_mul, abs_mul, abs_pow] at hrev
    linarith
  · right
    have hbge : ρ / 8 ≤ |b| := le_of_not_gt hbsmall
    have hρv : 16 ≤ ρ * |v| := by
      have h := (div_le_iff₀ hρ).mp hv
      nlinarith
    have hmul := mul_le_mul_of_nonneg_right hρv (abs_nonneg v)
    have hquad := mul_le_mul_of_nonneg_right hbge (sq_nonneg |v|)
    have htwo : 2 * |v| ≤ |b| * |v| ^ 2 := by nlinarith
    have hlin : |a| * |v| ≤ |v| := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right ha (abs_nonneg v)
    have hrev := abs_add_le (a * v - b * v ^ 2) (-(a * v))
    rw [show (a * v - b * v ^ 2) + -(a * v) = -(b * v ^ 2) by ring,
      abs_neg, abs_mul, abs_pow, abs_neg, abs_mul] at hrev
    linarith

theorem shearing_profile_two_scales (a b L u v ρ : ℝ)
    (hnorm : max |a| (Real.sqrt |b| + L) = 1)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hu : ρ ≤ |u|) (huone : |u| ≤ 1) (hv : 16 / ρ ≤ |v|) :
    ρ / 8 ≤ max |a * u - b * u ^ 2| (|u| * L) ∨
    ρ / 8 ≤ max |a * v - b * v ^ 2| (|v| * L) := by
  by_cases hLlarge : 1 / 2 ≤ L
  · left
    have hmul := mul_le_mul_of_nonneg_left hLlarge (abs_nonneg u)
    have hlow : ρ / 8 ≤ |u| * L := by linarith
    exact hlow.trans (le_max_right _ _)
  · have ha : |a| ≤ 1 := (le_max_left _ _).trans_eq hnorm
    have hquarter : 1 / 4 ≤ max |a| |b| := by
      by_cases haquarter : 1 / 4 ≤ |a|
      · exact haquarter.trans (le_max_left _ _)
      · have ha1 : |a| < 1 := by linarith
        have hu1 : 1 ≤ Real.sqrt |b| + L :=
          (le_max_iff.mp hnorm.ge).resolve_left ha1.not_ge
        have hbquarter : 1 / 4 ≤ |b| := by
          nlinarith [Real.sq_sqrt (abs_nonneg b), Real.sqrt_nonneg |b|]
        exact hbquarter.trans (le_max_right _ _)
    rcases quadratic_two_scales_quarter a b u v ρ hρ hρone ha hquarter hu huone hv with h | h
    · exact Or.inl (h.trans (le_max_left _ _))
    · have hvρ : ρ / 8 ≤ |v| := by
        have h := (div_le_iff₀ hρ).mp hv
        nlinarith [sq_nonneg ρ]
      exact Or.inr (hvρ.trans (h.trans (le_max_left _ _)))

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingNormalizedProfile
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.OAI.DukePrimeDegree.EliminationChain.word_zeroTime _root_.OAI.DukePrimeDegree.matrixLogLength_inv _root_.OAI.DukePrimeDegree.matrixLogLength_one
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The normalized profile of an actual return matrix

The algebraic profile is the actual pivot displacement together with
the remaining linear coefficients. Its normalization agrees with the
previously defined shearing scale, and its size is controlled by the
matrix displacement.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

lemma rootShearSize_nonneg {n : ℕ} {i j : Fin n} (hij : i ≠ j) (g : G n) (u : ℝ) :
    0 ≤ rootShearSize hij g u :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _

theorem rootShearingOffDiagonalSize_mul_le {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (u : ℝ) :
    |u| * rootShearingOffDiagonalSize i j g ≤ 2 * (n : ℝ) * rootShearSize hij g u := by
  unfold rootShearingOffDiagonalSize
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _k : Fin n, 2 * rootShearSize hij g u := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk : k = i ∨ k = j
      · simp only [hk, ite_true, if_true, mul_zero]
        linarith [rootShearSize_nonneg hij g u]
      · have hki : k ≠ i := fun h => hk (Or.inl h)
        have hkj : k ≠ j := fun h => hk (Or.inr h)
        have hr : |u| * |g.val j k| ≤ rootShearSize hij g u := by
          simpa [root_conjugation_entry, hkj, abs_mul] using
            entry_sub_le_rootShearSize hij g u i k
        have hc : |u| * |g.val k i| ≤ rootShearSize hij g u := by
          simpa [root_conjugation_entry, hki, abs_mul] using
            entry_sub_le_rootShearSize hij g u k j
        simp only [hk, ite_false, if_false, mul_add]
        linarith
    _ = _ := by simp <;> ring

theorem rootShearing_raw_profile_le_size {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (u : ℝ) :
    max |u * (g.val j j - g.val i i) - u ^ 2 * g.val j i|
      (|u| * rootShearingOffDiagonalSize i j g) ≤ 2 * (n : ℝ) * rootShearSize hij g u := by
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_iff.mpr (Fin.pos i))
  have hp : |u * (g.val j j - g.val i i) - u ^ 2 * g.val j i| ≤ rootShearSize hij g u := by
    simpa only [← root_conjugation_pivot hij g u] using entry_sub_le_rootShearSize hij g u i j
  apply max_le
  · have hS := rootShearSize_nonneg hij g u
    nlinarith
  · exact rootShearingOffDiagonalSize_mul_le hij g u

theorem rootShearing_normalized_profile_identity {n : ℕ} (i j : Fin n) (g : G n)
    (hk : 0 < rootShearingKappa i j g) :
    max |(g.val j j - g.val i i) / rootShearingKappa i j g|
      (Real.sqrt |g.val j i / (rootShearingKappa i j g) ^ 2| +
        rootShearingOffDiagonalSize i j g / rootShearingKappa i j g) = 1 := by
  rw [abs_div, abs_of_pos hk, abs_div, abs_pow, abs_of_pos hk,
    Real.sqrt_div (abs_nonneg _), Real.sqrt_sq_eq_abs, abs_of_pos hk,
    ← add_div, max_div_div_right hk.le]
  exact div_self hk.ne'

theorem rootShearing_normalized_profile_le_size {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hk : 0 < rootShearingKappa i j g) (u : ℝ) :
    max |((g.val j j - g.val i i) / rootShearingKappa i j g) *
        (rootShearingKappa i j g * u) -
        (g.val j i / (rootShearingKappa i j g) ^ 2) * (rootShearingKappa i j g * u) ^ 2|
      (|rootShearingKappa i j g * u| *
        (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g)) ≤
      2 * (n : ℝ) * rootShearSize hij g u := by
  have hp : ((g.val j j - g.val i i) / rootShearingKappa i j g) *
      (rootShearingKappa i j g * u) -
      (g.val j i / (rootShearingKappa i j g) ^ 2) * (rootShearingKappa i j g * u) ^ 2 =
      u * (g.val j j - g.val i i) - u ^ 2 * g.val j i := by
    field_simp [hk.ne']
  have hL : |rootShearingKappa i j g * u| *
      (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g) =
      |u| * rootShearingOffDiagonalSize i j g := by
    rw [abs_mul, abs_of_pos hk]
    field_simp [hk.ne']
  rw [hp, hL]
  exact rootShearing_raw_profile_le_size hij g u

end DukePrimeDegree

end

end OAI
end

section
-- module Solutions.OAIQ244_DUKE.DukePrimeDegree_Dynamics_ShearingTwoAnnuli
attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A uniform positive displacement at one of two annular returns

The normalized profile is the actual matrix profile. Consequently the
two-scale cancellation estimate gives a positive lower bound independent
of the return matrix, while the scale bound controls every intervening
shearing parameter.
-/

noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootShearSize_two_scales_lower_oai {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hk : 0 < rootShearingKappa i j g) (r s ρ : ℝ)
    (hρ : 0 < ρ) (hρone : ρ ≤ 1)
    (hrlo : ρ ≤ |rootShearingKappa i j g * r|)
    (hrhi : |rootShearingKappa i j g * r| ≤ 1)
    (hslo : 16 / ρ ≤ |rootShearingKappa i j g * s|) :
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g r ∨
    ρ / (16 * (n : ℝ)) ≤ rootShearSize hij g s := by
  have hn : 0 < (n : ℝ) := by exact_mod_cast Fin.pos i
  have h := shearing_profile_two_scales
    ((g.val j j - g.val i i) / rootShearingKappa i j g)
    (g.val j i / (rootShearingKappa i j g) ^ 2)
    (rootShearingOffDiagonalSize i j g / rootShearingKappa i j g)
    (rootShearingKappa i j g * r) (rootShearingKappa i j g * s) ρ
    (rootShearing_normalized_profile_identity i j g hk) hρ hρone hrlo hrhi hslo
  have hbound (u : ℝ) := rootShearing_normalized_profile_le_size hij g hk u
  rcases h with h | h
  · left
    have hle := h.trans (hbound r)
    apply (div_le_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mpr
    nlinarith
  · right
    have hle := h.trans (hbound s)
    apply (div_le_iff₀ (by positivity : 0 < 16 * (n : ℝ))).mpr
    nlinarith

end DukePrimeDegree

end

end OAI
end

theorem solution : type_of% @OAI.DukePrimeDegree.rootShearSize_two_scales_lower_oai := @OAI.DukePrimeDegree.rootShearSize_two_scales_lower_oai
