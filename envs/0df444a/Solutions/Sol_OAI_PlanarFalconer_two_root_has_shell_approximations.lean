-- Prove2me | solution 1 for OAI.PlanarFalconer.two_root_has_shell_approximations
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:26:15.647599+00:00
-- url     : https://prove2.me/submissions/7fad1ae6-9824-4a20-b987-e520eb410f4f

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_actual_profile_regularization
import Theorems.Thm_OAI_PlanarFalconer_two_root_restored_removed_mass_bound
import Theorems.Thm_OAI_PlanarFalconer_uniform_independent_class_equation27

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.dist_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side)
    {z w : Plane} (hz : z ∈ Q.carrier) (hw : w ∈ Q.carrier) :
    dist z w ≤ 2 * Q.side := by
  have h0 : |z 0 - w 0| ≤ Q.side := by
    apply abs_le.mpr; constructor <;> linarith [hz.1,hz.2.1,hw.1,hw.2.1]
  have h1 : |z 1 - w 1| ≤ Q.side := by
    apply abs_le.mpr; constructor <;>
      linarith [hz.2.2.1,hz.2.2.2,hw.2.2.1,hw.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq z w
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h0
  have hs1 := sq_le_sq₀ (abs_nonneg _) hQ |>.mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [dist_nonneg (x := z) (y := w)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side_pos (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : List (Bool × Bool)) : 0 < (Q.descendant p).side := by
  induction p generalizing Q with
  | nil => exact hQ
  | cons a p ih => exact ih _ (Q.child_side_pos hQ a.1 a.2)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem DyadicSquare.descendant_side (Q : DyadicSquare) (p : List (Bool × Bool)) :
    (Q.descendant p).side = Q.side / (2 : ℝ)^p.length := by
  induction p generalizing Q with
  | nil => simp [descendant]
  | cons a p ih =>
    simp only [descendant, ih, child, List.length_cons, pow_succ]
    ring

theorem plane_coordinate_dist_le (z x : Plane) (i : Fin 2) :
    |z i - x i| ≤ dist z x := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le z x i

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_ScaledDyadicPacking
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem DyadicSquare.center_mem (Q : DyadicSquare) (hQ : 0 < Q.side) : Q.center ∈ Q.carrier := by
  simp only [center,carrier,mem_ofPred_eq,Matrix.cons_val_zero,Matrix.cons_val_one]
  constructor
  · linarith
  · exact ⟨by linarith,by linarith,by linarith⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicClasses
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem leafUnion_subset (Q : DyadicSquare) (hQ : 0 < Q.side)
    (L : Finset (List (Bool × Bool))) : leafUnion Q L ⊆ Q.carrier := by
  intro z hz
  obtain ⟨p,_,hp⟩ := mem_iUnion₂.mp hz
  exact Q.descendant_subset hQ p hp

theorem normalizedClass_apply (Q : DyadicSquare) (μ : Measure Plane)
    (L : Finset (List (Bool × Bool))) (f : List (Bool × Bool) → List ℕ) (T : List ℕ)
    (S : Set Plane) :
    normalizedClass Q μ L f T S =
      (μ (leafUnion Q (classLeaves L f T)))⁻¹ *
        μ (S ∩ leafUnion Q (classLeaves L f T)) := by
  simp only [normalizedClass, classMeasure, univ_inter,
    Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply' (leafUnion_measurable Q _)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PrefixMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.descendant_append (Q : DyadicSquare) (p q : CellPath) :
    Q.descendant (p++q) = (Q.descendant p).descendant q := by
  induction p generalizing Q with
  | nil => rfl
  | cons a p ih => exact ih (Q.child a.1 a.2)

theorem DyadicSquare.descendant_subset_take (Q : DyadicSquare) (hQ : 0 < Q.side)
    (p : CellPath) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset (Q.descendant_side_pos hQ _) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem measurable_stripCount {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) :
    Measurable (fun ω : Plane => stripCount S v W ω) := by
  classical
  have he : (fun ω : Plane => stripCount S v W ω) =
      fun ω => ∑ i ∈ S, if |planeDot (v i) ω| ≤ W then (1:ℕ) else 0 := by
    funext ω
    simp [stripCount]
  rw [he]
  apply Finset.measurable_sum
  intro i _
  apply Measurable.ite _ measurable_const measurable_const
  apply measurableSet_le _ measurable_const
  have hc : Continuous (fun ω : Plane => |planeDot (v i) ω|) := by
    unfold planeDot
    fun_prop
  exact hc.measurable

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem parallelTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W (-ω) = parallelTestCount Q ρ g p P W ω := by
  have he : quarterTurn (-ω) = -quarterTurn ω := by ext i; fin_cases i <;> simp [quarterTurn]
  unfold parallelTestCount
  rw [he,stripCount_neg]

theorem projectionTestCount_neg (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    projectionTestCount Q ρ p u P W (-ω) = projectionTestCount Q ρ p u P W ω :=
  stripCount_neg _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStripIntervals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem cos_strip_near_zero {x c t : ℝ} (hc : Real.cos c = 0)
    (hs : |Real.sin c| = 1) (hnear : |x-c| ≤ Real.pi/2)
    (ht : |Real.cos x| ≤ t) : |x-c| ≤ Real.pi/2*t := by
  have hh := Real.mul_abs_le_abs_sin hnear
  have he : |Real.sin (x-c)| = |Real.cos x| := by
    rw [Real.sin_sub,hc,mul_zero,zero_sub,abs_neg,abs_mul,hs,mul_one]
  rw [he] at hh
  have hp := Real.pi_pos
  have hi : (2/Real.pi:ℝ)*Real.pi = 2 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_right (hh.trans ht) hp.le]

theorem cos_strip_four_intervals {x t : ℝ} (hx : -Real.pi ≤ x ∧ x ≤ 3*Real.pi)
    (ht : |Real.cos x| ≤ t) :
    |x-(-Real.pi/2)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2+Real.pi)| ≤ Real.pi/2*t ∨
    |x-(Real.pi/2+2*Real.pi)| ≤ Real.pi/2*t := by
  have hp := Real.pi_pos
  by_cases h0 : x ≤ 0
  · left
    apply cos_strip_near_zero _ _ _ ht
    · simp [neg_div,Real.cos_neg]
    · simp [neg_div,Real.sin_neg]
    · rw [abs_le]; constructor <;> linarith
  by_cases h1 : x ≤ Real.pi
  · right; left
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith
  by_cases h2 : x ≤ 2*Real.pi
  · right; right; left
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith
  · right; right; right
    apply cos_strip_near_zero (by simp) (by simp) _ ht
    rw [abs_le]; constructor <;> linarith

theorem volume_cos_strip {a t : ℝ} (ha : -Real.pi ≤ a ∧ a ≤ Real.pi) (ht : 0 ≤ t) :
    volume {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-a)| ≤ t} ≤
      ENNReal.ofReal (4*Real.pi*t) := by
  let r := Real.pi/2*t
  let c0 := a-Real.pi/2
  let c1 := a+Real.pi/2
  let c2 := a+(Real.pi/2+Real.pi)
  let c3 := a+(Real.pi/2+2*Real.pi)
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hsub : {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-a)| ≤ t} ⊆
      Icc (c0-r) (c0+r) ∪ Icc (c1-r) (c1+r) ∪
      Icc (c2-r) (c2+r) ∪ Icc (c3-r) (c3+r) := by
    intro θ hθ
    have hx : -Real.pi ≤ θ-a ∧ θ-a ≤ 3*Real.pi := by
      obtain ⟨⟨h0,h1⟩,hs⟩ := hθ
      constructor <;> linarith [Real.pi_pos]
    rcases cos_strip_four_intervals hx hθ.2 with h|h|h|h
    · left; left; left
      rw [abs_le] at h
      dsimp [c0,r]; constructor <;> linarith
    · left; left; right
      rw [abs_le] at h
      dsimp [c1,r]; constructor <;> linarith
    · left; right
      rw [abs_le] at h
      dsimp [c2,r]; constructor <;> linarith
    · right
      rw [abs_le] at h
      dsimp [c3,r]; constructor <;> linarith
  calc
    _ ≤ volume (Icc (c0-r) (c0+r) ∪ Icc (c1-r) (c1+r) ∪
        Icc (c2-r) (c2+r) ∪ Icc (c3-r) (c3+r)) := measure_mono hsub
    _ ≤ ((volume (Icc (c0-r) (c0+r))+volume (Icc (c1-r) (c1+r)))+
        volume (Icc (c2-r) (c2+r)))+volume (Icc (c3-r) (c3+r)) := by
      apply (measure_union_le _ _).trans
      gcongr
      apply (measure_union_le _ _).trans
      gcongr
      exact measure_union_le _ _
    _ = ENNReal.ofReal (4*Real.pi*t) := by
      simp only [Real.volume_Icc]
      have he (c : ℝ) : c+r-(c-r) = 2*r := by ring
      simp only [he]
      rw [← ENNReal.ofReal_add (by positivity) (by positivity),← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp [r]
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularStripMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem planeDot_sourceDirection_complex (z : ℂ) (θ : ℝ) :
    planeDot (Complex.orthonormalBasisOneI.repr z) (sourceDirection θ) =
      ‖z‖*Real.cos (θ-Complex.arg z) := by
  simp only [planeDot,sourceDirection,Complex.orthonormalBasisOneI_repr_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im,mul_zero,
    sub_zero,add_zero,zero_add,mul_one]
  rw [Real.cos_sub]
  have hc := Complex.norm_mul_cos_arg z
  have hs := Complex.norm_mul_sin_arg z
  rw [← hc,← hs]
  ring

theorem measurableSet_directionStrip (z : Plane) (W : ℝ) :
    MeasurableSet {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} := by
  apply measurableSet_le _ measurable_const
  have hc : Continuous (fun ω : UnitCircle => |planeDot z (ω:Plane)|) := by
    unfold planeDot
    fun_prop
  exact hc.measurable

theorem sourceArcLength_strip_linear (z : Plane) (hz : z ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤
      ENNReal.ofReal (4*Real.pi*(W/‖z‖)) := by
  let c := Complex.orthonormalBasisOneI.repr.symm z
  have hc : Complex.orthonormalBasisOneI.repr c = z := by exact Complex.orthonormalBasisOneI.repr.apply_symm_apply z
  have hn : ‖c‖ = ‖z‖ := Complex.orthonormalBasisOneI.repr.symm.norm_map z
  have hp : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have he (θ : ℝ) : |planeDot z (sourceDirection θ)| ≤ W ↔
      |Real.cos (θ-Complex.arg c)| ≤ W/‖z‖ := by
    rw [← hc,planeDot_sourceDirection_complex,abs_mul,abs_of_nonneg (norm_nonneg c),hn,hc]
    simpa only [mul_comm] using (le_div_iff₀ (a := |Real.cos (θ-Complex.arg c)|) (b := W) hp).symm
  rw [sourceArcLength,Measure.map_apply continuous_sourceUnitDirection.measurable
    (measurableSet_directionStrip z W),Measure.restrict_apply
    ((measurableSet_directionStrip z W).preimage continuous_sourceUnitDirection.measurable)]
  have hset : sourceUnitDirection ⁻¹' {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ∩
      Ioc 0 (2*Real.pi) =
      {θ : ℝ | θ ∈ Ioc 0 (2*Real.pi) ∧ |Real.cos (θ-Complex.arg c)| ≤ W/‖z‖} := by
    ext θ
    simp only [mem_inter_iff,mem_preimage,mem_ofPred_eq,sourceUnitDirection,he]
    exact and_comm
  rw [hset]
  exact volume_cos_strip ⟨(Complex.neg_pi_lt_arg c).le,Complex.arg_le_pi c⟩
    (div_nonneg hW hp.le)

theorem sourceArcLength_univ : sourceArcLength univ = ENNReal.ofReal (2*Real.pi) := by
  rw [sourceArcLength,Measure.map_apply continuous_sourceUnitDirection.measurable MeasurableSet.univ]
  simp

theorem sourceArcLength_strip (z : Plane) (hz : z ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤
      ENNReal.ofReal (4*Real.pi*min 1 (W/‖z‖)) := by
  by_cases h : W/‖z‖ ≤ 1
  · rw [min_eq_right h]
    exact sourceArcLength_strip_linear z hz hW
  · rw [min_eq_left (le_of_not_ge h)]
    calc
      _ ≤ sourceArcLength univ := measure_mono (subset_univ _)
      _ = ENNReal.ofReal (2*Real.pi) := sourceArcLength_univ
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by nlinarith [Real.pi_pos])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularCountMean
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem sourceArcLength_strip_le_bound (z : Plane) {W : ℝ} (hW : 0 ≤ W) :
    sourceArcLength {ω : UnitCircle | |planeDot z (ω:Plane)| ≤ W} ≤ stripHitBound W z := by
  by_cases hz : z=0
  · simp only [stripHitBound,ite_eq_left hz]
    exact (measure_mono (subset_univ _)).trans_eq sourceArcLength_univ
  · simpa only [stripHitBound,ite_eq_right hz] using sourceArcLength_strip z hz hW

theorem stripCount_lintegral {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) :
    (∫⁻ ω : UnitCircle, (stripCount S v W (ω:Plane):ℝ≥0∞) ∂sourceArcLength) =
      ∑ i ∈ S, sourceArcLength {ω : UnitCircle | |planeDot (v i) (ω:Plane)| ≤ W} := by
  classical
  let f : ι → UnitCircle → ℝ≥0∞ := fun i =>
    {ω : UnitCircle | |planeDot (v i) (ω:Plane)| ≤ W}.indicator (fun _ => 1)
  have he (ω : UnitCircle) : (stripCount S v W (ω:Plane):ℝ≥0∞) = ∑ i ∈ S, f i ω := by
    rw [stripCount,Finset.card_filter,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : |planeDot (v i) (ω:Plane)| ≤ W <;> simp [hi,f]
  simp_rw [he]
  rw [lintegral_finsetSum S (fun i _ => measurable_const.indicator (measurableSet_directionStrip (v i) W))]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_indicator (measurableSet_directionStrip (v i) W)]
  simp

theorem stripCount_mean_bound {ι : Type*} (S : Finset ι) (v : ι → Plane) {W : ℝ} (hW : 0 ≤ W) :
    (∫⁻ ω : UnitCircle, (stripCount S v W (ω:Plane):ℝ≥0∞) ∂sourceArcLength) ≤
      ∑ i ∈ S, stripHitBound W (v i) := by
  rw [stripCount_lintegral]
  exact Finset.sum_le_sum (fun i _ => sourceArcLength_strip_le_bound (v i) hW)

theorem stripCount_exceptional_bound {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength {ω : UnitCircle | T < (stripCount S v W (ω:Plane):ℝ)} ≤
      (∑ i ∈ S, stripHitBound W (v i))/ENNReal.ofReal T := by
  have hm : Measurable (fun ω : UnitCircle => (stripCount S v W (ω:Plane):ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ => (n:ℝ≥0∞))).comp
      ((measurable_stripCount S v W).comp continuous_subtype_val.measurable)
  have hsub : {ω : UnitCircle | T < (stripCount S v W (ω:Plane):ℝ)} ⊆
      {ω : UnitCircle | ENNReal.ofReal T ≤ (stripCount S v W (ω:Plane):ℝ≥0∞)} := by
    intro ω hω
    simpa using ENNReal.ofReal_le_ofReal hω.le
  apply (measure_mono hsub).trans
  apply (meas_ge_le_lintegral_div hm.aemeasurable
    (by positivity : ENNReal.ofReal T ≠ 0) ENNReal.ofReal_ne_top).trans
  gcongr
  exact stripCount_mean_bound S v hW

theorem planeDot_quarterTurn (z ω : Plane) :
    planeDot z (quarterTurn ω) = -planeDot (quarterTurn z) ω := by
  simp [planeDot,quarterTurn]

theorem parallelTestCount_as_strip (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W : ℝ) (ω : Plane) :
    parallelTestCount Q ρ g p P W ω =
      stripCount (parallelTestCells Q ρ g p P)
        (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) W ω := by
  classical
  simp only [parallelTestCount,stripCount,planeDot_quarterTurn,abs_neg]

theorem parallelGoodSet_compl_bound (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength (parallelGoodSet Q ρ g p P W T)ᶜ ≤
      (∑ c ∈ parallelTestCells Q ρ g p P,
        stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)))/
          ENNReal.ofReal T := by
  have he : (parallelGoodSet Q ρ g p P W T)ᶜ =
      {ω : UnitCircle | T < (stripCount (parallelTestCells Q ρ g p P)
        (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) W (ω:Plane):ℝ)} := by
    ext ω
    simp [parallelGoodSet,parallelTestCount_as_strip]
  rw [he]
  exact stripCount_exceptional_bound _ _ hW hT

theorem projectionGoodSet_compl_bound (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) {W T : ℝ} (hW : 0 ≤ W) (hT : 0 < T) :
    sourceArcLength (projectionGoodSet Q ρ p u P W T)ᶜ ≤
      (∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
        stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center))/
          ENNReal.ofReal T := by
  have he : (projectionGoodSet Q ρ p u P W T)ᶜ =
      {ω : UnitCircle | T < (stripCount
        ((projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P))
        (fun cc => (Q.descendant cc.1).center-(Q.descendant cc.2).center) W (ω:Plane):ℝ)} := by
    ext ω
    simp [projectionGoodSet,projectionTestCount]
  rw [he]
  exact stripCount_exceptional_bound _ _ hW hT

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicCenterSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.center_separation (P Q : DyadicSquare)
    (hs : P.side = Q.side) (hd : Disjoint P.carrier Q.carrier) :
    P.side ≤ dist P.center Q.center := by
  by_contra h
  have hh : dist P.center Q.center < P.side := lt_of_not_ge h
  have h0 := abs_lt.mp ((plane_coordinate_dist_le P.center Q.center 0).trans_lt hh)
  have h1 := abs_lt.mp ((plane_coordinate_dist_le P.center Q.center 1).trans_lt hh)
  simp only [DyadicSquare.center,WithLp.ofLp_toLp,Matrix.cons_val_zero,
    Matrix.cons_val_one] at h0 h1
  let z : Plane := WithLp.toLp 2 ![(P.x+Q.x+P.side)/2,(P.y+Q.y+P.side)/2]
  have hP : z ∈ P.carrier := by
    simp only [DyadicSquare.carrier,mem_ofPred_eq,z,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · linarith
    · exact ⟨by linarith,by linarith,by linarith⟩
  have hQ : z ∈ Q.carrier := by
    simp only [DyadicSquare.carrier,mem_ofPred_eq,z,Matrix.cons_val_zero,
      Matrix.cons_val_one]
    constructor
    · linarith
    · exact ⟨by linarith,by linarith,by linarith⟩
  exact Set.disjoint_left.mp hd hP hQ

theorem dyadic_centers_separated (Q : DyadicSquare) (hQ : 0 < Q.side)
    {n : ℕ} {p q : List (Bool × Bool)} (hp : p.length = n) (hq : q.length = n) (hne : p ≠ q) :
    Q.side/(2:ℝ)^n ≤ dist (Q.descendant p).center (Q.descendant q).center := by
  have hs : (Q.descendant p).side = (Q.descendant q).side := by
    rw [Q.descendant_side,Q.descendant_side,hp,hq]
  have hh := (Q.descendant p).center_separation (Q.descendant q) hs
    (Q.descendants_disjoint hQ (hp.trans hq.symm) hne)
  simpa only [Q.descendant_side,hp] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicInverseDistance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem inverse_distance_dyadic {d : ℝ} (hd : 0 < d) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ d) :
    1/d ≤ (2:ℝ)^g + ∑ j ∈ Finset.range k,
      if d < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply (div_le_iff₀ hd).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hcoarse : 1/(2:ℝ)^(g+k) ≤ d
    · have hh := ih hcoarse
      have hnon : 0 ≤ (if d < 1/(2:ℝ)^(g+k) then (2:ℝ)^(g+k+1) else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hcoarse)]
      have hfine : 1/d ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hd).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if d < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hg : 0 < (2:ℝ)^g := by positivity
      linarith

theorem sum_inverse_distance_dyadic {ι : Type*} (S : Finset ι) (d : ι → ℝ)
    (g k : ℕ) (hd : ∀ i ∈ S, 0 < d i) (hmin : ∀ i ∈ S, 1/(2:ℝ)^(g+k) ≤ d i) :
    ∑ i ∈ S, 1/d i ≤ (S.card:ℝ)*(2:ℝ)^g +
      ∑ j ∈ Finset.range k, ((S.filter fun i => d i < 1/(2:ℝ)^(g+j)).card:ℝ)*(2:ℝ)^(g+j+1) := by
  classical
  calc
    _ ≤ ∑ i ∈ S, ((2:ℝ)^g + ∑ j ∈ Finset.range k,
        if d i < 1/(2:ℝ)^(g+j) then (2:ℝ)^(g+j+1) else 0) :=
      Finset.sum_le_sum (fun i hi => inverse_distance_dyadic (hd i hi) g k (hmin i hi))
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_comm]
      simp only [Finset.sum_const,nsmul_eq_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_filter]
      simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDyadicSum
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem parallel_inverse_distance_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {g p : ℕ} (hgp : g ≤ p) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center ≤
      ((parallelTestCells Q ρ g p P).card:ℝ)*(2:ℝ)^g +
        ∑ j ∈ Finset.range (p-g),
          ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ)*
            (2:ℝ)^(g+j+1) := by
  classical
  let S := (parallelTestCells Q ρ g p P).erase P
  let d := fun c => dist (Q.descendant c).center (Q.descendant P).center
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  have hsep (c : CellPath) (hc : c ∈ S) : 1/(2:ℝ)^p ≤ d c := by
    have hc' := Finset.mem_of_mem_erase hc
    have hl := (mem_dyadicPaths p c).mp (Finset.mem_filter.mp hc').1
    simpa only [hQ] using dyadic_centers_separated Q hside hl hP (Finset.ne_of_mem_erase hc)
  have hd (c : CellPath) (hc : c ∈ S) : 0 < d c :=
    lt_of_lt_of_le (by positivity : 0 < 1/(2:ℝ)^p) (hsep c hc)
  have hh := sum_inverse_distance_dyadic S d g (p-g) hd (fun c hc => by
    simpa only [Nat.add_sub_of_le hgp] using hsep c hc)
  apply hh.trans
  apply add_le_add
  · apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact_mod_cast Finset.card_le_card (Finset.erase_subset P (parallelTestCells Q ρ g p P))
  · apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro c hc
    obtain ⟨hc,hdc⟩ := Finset.mem_filter.mp hc
    have hc' := Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)
    exact Finset.mem_filter.mpr ⟨hc'.1,hc'.2.1,hdc⟩

theorem parallel_inverse_distance_profile (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam : ℝ)
    (hpack : ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ x : Plane, ∀ C₀ : ℝ, 0 ≤ C₀ →
      ((occupiedCenterCells Q ρ p x (C₀/(2:ℝ)^g)).card:ℝ) ≤
        (4*(C₀+1)^2)*((2:ℝ)^N)^(m p-m g+6*lam))
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center ≤
      484*(((2:ℝ)^N)^(m p-m g+6*lam)*(2:ℝ)^g +
        ∑ j ∈ Finset.range (p-g),
          ((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1)) := by
  classical
  apply (parallel_inverse_distance_sum Q hQ ρ hgp hP).trans
  rw [mul_add,Finset.mul_sum]
  apply add_le_add
  · have hh := hpack g p hgp hpN (Q.descendant P).center 10 (by norm_num)
    change ((parallelTestCells Q ρ g p P).card:ℝ) ≤ _ at hh
    norm_num at hh
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ (2:ℝ)^g)
  · apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hh := hpack (g+j) p (by omega) hpN (Q.descendant P).center 1 (by norm_num)
    norm_num at hh
    have hpos : 0 ≤ ((2:ℝ)^N)^(m p-m (g+j)+6*lam) := by positivity
    have hh' : ((occupiedCenterCells Q ρ p (Q.descendant P).center (1/(2:ℝ)^(g+j))).card:ℝ) ≤
        484*((2:ℝ)^N)^(m p-m (g+j)+6*lam) := by
      simp only [one_div]
      linarith
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right hh' (by positivity : 0 ≤ (2:ℝ)^(g+j+1))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ClassPruning
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem retainedClassUnion_mass (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    (N B : ℕ) (t : ℝ≥0∞) : μ (retainedClassUnion Q μ N B t) =
      ∑ T ∈ retainedClassLabels Q μ N B t,
        classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ := by
  classical
  simp only [classMeasure,Measure.restrict_apply_univ]
  apply measure_biUnion_finset
  · intro T _ U _ hne
    apply leafUnion_disjoint Q hQ (N := N)
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact fun q hq => (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact classLeaves_disjoint _ _ hne
  · intro T _; exact leafUnion_measurable Q _

theorem retainedClass_mass_sum_le_one (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (N B : ℕ) (t : ℝ≥0∞) :
    (∑ T ∈ retainedClassLabels Q μ N B t,
      classMeasure Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T univ) ≤ 1 := by
  rw [← retainedClassUnion_mass Q hQ μ N B t]
  exact prob_le_one

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_FrostmanProfileCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal

theorem fixed_constant_absorbed {lam : ℝ} (hlam : 0 < lam) (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C ≤ ((2:ℝ)^N)^lam := by
  have hb : 1 < (2:ℝ)^lam := Real.one_lt_rpow (by norm_num) hlam
  obtain ⟨N₀,hN₀⟩ := pow_unbounded_of_one_lt C hb
  refine ⟨N₀,fun N hN => ?_⟩
  have hh := hN₀.le.trans (pow_le_pow_right₀ hb.le hN)
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm,
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Potential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem finiteMin_le {ι : Type*} {s : Finset ι} (f : ι → ℝ)
    {i : ι} (hi : i ∈ s) : finiteMin s f ≤ f i := by
  rw [finiteMin, dite_eq_left ⟨i, hi⟩]
  exact Finset.inf'_le f hi

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_Ledger
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Finset

theorem intervalMin_le (A : ℕ → ℝ) {a t i : ℕ} (hai : a ≤ i) (hit : i ≤ t) :
    intervalMin A a t ≤ A i := finiteMin_le A (Finset.mem_Icc.mpr ⟨hai,hit⟩)

theorem height_nonneg (A : ℕ → ℝ) {a p : ℕ} (hap : a ≤ p) :
    0 ≤ height A a p := sub_nonneg.mpr (intervalMin_le A hap le_rfl)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularProfileSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_power_as_R {N : ℕ} (hN : 0 < N) (n : ℕ) :
    (2:ℝ)^n = ((2:ℝ)^N)^((n:ℝ)/(N:ℝ)) := by
  rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
  have hn : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have he : (N:ℝ)*((n:ℝ)/(N:ℝ)) = n := mul_div_cancel₀ (n : ℝ) hn
  rw [he,Real.rpow_natCast]

theorem angular_profile_weight (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam : ℝ) {g h p : ℕ} (hgh : g ≤ h) (hhp : h ≤ p) :
    (((2:ℝ)^N)^(m p-m h+6*lam)*(2:ℝ)^h)/(2:ℝ)^p ≤
      ((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  let R : ℝ := (2:ℝ)^N
  have hRp : 0 < R := by dsimp [R]; positivity
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num)
  rw [dyadic_power_as_R hN h,dyadic_power_as_R hN p,
    ← Real.rpow_add hRp,← Real.rpow_sub hRp]
  apply Real.rpow_le_rpow_of_exponent_le hR
  have hh := intervalMin_le (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) hgh hhp
  dsimp [height]
  linarith

theorem angular_profile_dyadic_sum (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam : ℝ) {g p : ℕ} (hgp : g ≤ p) :
    ((((2:ℝ)^N)^(m p-m g+6*lam)*(2:ℝ)^g +
      ∑ j ∈ Finset.range (p-g),
        ((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1)))/(2:ℝ)^p ≤
      (1+2*(p-g:ℕ))*((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  let Z := ((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam)
  rw [add_div,Finset.sum_div]
  have hbase := angular_profile_weight m hN lam (g := g) le_rfl hgp
  have hsum : (∑ j ∈ Finset.range (p-g),
      (((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j+1))/(2:ℝ)^p) ≤
        (p-g:ℕ)*(2*Z) := by
    calc
      _ ≤ ∑ _j ∈ Finset.range (p-g), (2*Z) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_range.mp hj
        have hh := angular_profile_weight m hN lam (g := g) (h := g+j) (p := p) (by omega) (by omega)
        rw [pow_succ]
        have he : (((2:ℝ)^N)^(m p-m (g+j)+6*lam)*((2:ℝ)^(g+j)*2))/(2:ℝ)^p =
            2*((((2:ℝ)^N)^(m p-m (g+j)+6*lam)*(2:ℝ)^(g+j))/(2:ℝ)^p) := by ring
        rw [he]
        simp only [Nat.cast_add] at hh
        change _ ≤ Z at hh
        linarith
      _ = _ := by simp
  change _ ≤ (1+2*(p-g:ℕ))*Z
  change _ ≤ Z at hbase
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularMeanAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem stripHitBound_sum_diagonal {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (a : ι) (v : ι → Plane) (ha : v a = 0)
    (hv : ∀ i ∈ S.erase a, v i ≠ 0) {W : ℝ} (hW : 0 ≤ W) :
    ∑ i ∈ S, stripHitBound W (v i) ≤
      ENNReal.ofReal (2*Real.pi+4*Real.pi*W*(∑ i ∈ S.erase a, 1/‖v i‖)) := by
  have hh : ∑ i ∈ S.erase a, stripHitBound W (v i) ≤
      ∑ i ∈ S.erase a, ENNReal.ofReal (4*Real.pi*W*(1/‖v i‖)) := by
    apply Finset.sum_le_sum
    intro i hi
    rw [stripHitBound,ite_eq_right (hv i hi)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ 4*Real.pi*(W/‖v i‖) := mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = _ := by ring
  have he : (∑ i ∈ S.erase a, ENNReal.ofReal (4*Real.pi*W*(1/‖v i‖))) =
      ENNReal.ofReal (4*Real.pi*W*(∑ i ∈ S.erase a, 1/‖v i‖)) := by
    rw [Finset.mul_sum,ENNReal.ofReal_sum_of_nonneg]
    intro i _; positivity
  rw [he] at hh
  calc
    _ ≤ ∑ i ∈ insert a (S.erase a), stripHitBound W (v i) :=
      Finset.sum_le_sum_of_subset (by intro i hi; by_cases h : i=a <;> simp [h,hi])
    _ = ENNReal.ofReal (2*Real.pi) + ∑ i ∈ S.erase a, stripHitBound W (v i) := by
      rw [Finset.sum_insert (Finset.notMem_erase a S),ha]
      simp [stripHitBound]
    _ ≤ _ := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity)]
      exact add_le_add_right hh _

theorem parallel_strip_sum_inverse (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (g p : ℕ) {P : CellPath} (hP : P.length = p)
    {W : ℝ} (hW : 0 ≤ W) :
    ∑ c ∈ parallelTestCells Q ρ g p P,
      stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) ≤
      ENNReal.ofReal (2*Real.pi+4*Real.pi*W*
        (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
          1/dist (Q.descendant c).center (Q.descendant P).center)) := by
  classical
  have hh := stripHitBound_sum_diagonal (parallelTestCells Q ρ g p P) P
    (fun c => quarterTurn ((Q.descendant c).center-(Q.descendant P).center))
    (by simp [quarterTurn]) ?_ hW
  · simpa only [norm_quarterTurn,dist_eq_norm] using hh
  intro c hc hz
  have hl := (mem_dyadicPaths p c).mp (Finset.mem_filter.mp (Finset.mem_of_mem_erase hc)).1
  have hs := dyadic_centers_separated Q hQ hl hP (Finset.ne_of_mem_erase hc)
  have hn : dist (Q.descendant c).center (Q.descendant P).center = 0 := by
    rw [dist_eq_norm,← norm_quarterTurn,hz,norm_zero]
  rw [hn] at hs
  exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^p)) hs

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ProjectionAngularGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem stripHitBound_quarterTurn (W : ℝ) (z : Plane) :
    stripHitBound W (quarterTurn z) = stripHitBound W z := by
  have hz : quarterTurn z = 0 ↔ z = 0 := by
    rw [← norm_eq_zero, norm_quarterTurn,norm_eq_zero]
  simp only [stripHitBound,hz,norm_quarterTurn]

theorem projection_center_mem (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (p u : ℕ) (P : CellPath) {c : CellPath}
    (hc : c ∈ projectionTestCells Q ρ p u P) :
    (Q.descendant c).center ∈ (Q.descendant P).carrier := by
  rw [← (Finset.mem_filter.mp hc).2.2]
  exact Q.descendant_subset_take hQ c p
    ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))

theorem projection_cells_subset_parallel (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p)
    {a : CellPath} (ha : a ∈ projectionTestCells Q ρ p u P) :
    projectionTestCells Q ρ p u P ⊆ parallelTestCells Q ρ p u a := by
  classical
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  intro c hc
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.1,?_⟩
  have hd := (Q.descendant P).dist_le (Q.descendant_side_pos hside P).le
    (projection_center_mem Q hside ρ p u P hc) (projection_center_mem Q hside ρ p u P ha)
  rw [Q.descendant_side,hP,hQ] at hd
  change dist (Q.descendant c).center (Q.descendant a).center < _
  exact hd.trans_lt (by
    rw [mul_one_div]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity))

theorem projection_cells_subset_ball (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p) :
    projectionTestCells Q ρ p u P ⊆
      occupiedCenterCells Q ρ u (Q.descendant P).center (3/(2:ℝ)^p) := by
  classical
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  intro c hc
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hc).1,(Finset.mem_filter.mp hc).2.1,?_⟩
  have hd := (Q.descendant P).dist_le (Q.descendant_side_pos hside P).le
    (projection_center_mem Q hside ρ p u P hc)
    ((Q.descendant P).center_mem (Q.descendant_side_pos hside P))
  rw [Q.descendant_side,hP,hQ] at hd
  change dist (Q.descendant c).center (Q.descendant P).center < _
  exact hd.trans_lt (by
    rw [mul_one_div]
    exact div_lt_div_of_pos_right (by norm_num) (by positivity))

theorem projection_strip_sum_rows (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) (p u : ℕ) {P : CellPath} (hP : P.length = p) (W : ℝ) :
    ∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
      stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ≤
    ∑ a ∈ projectionTestCells Q ρ p u P,
      ∑ c ∈ parallelTestCells Q ρ p u a,
        stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant a).center)) := by
  classical
  change (∑ cc ∈ (projectionTestCells Q ρ p u P) ×ˢ (projectionTestCells Q ρ p u P),
    stripHitBound W ((Q.descendant cc.1).center-(Q.descendant cc.2).center)) ≤ _
  rw [Finset.sum_product]
  apply Finset.sum_le_sum
  intro a ha
  have he (c : CellPath) :
      stripHitBound W ((Q.descendant a).center-(Q.descendant c).center) =
      stripHitBound W (quarterTurn ((Q.descendant c).center-(Q.descendant a).center)) := by
    rw [stripHitBound_quarterTurn]
    simp only [stripHitBound,sub_eq_zero,norm_sub_rev]
    simp only [eq_comm]
  simp_rw [he]
  exact Finset.sum_le_sum_of_subset (projection_cells_subset_parallel Q hQ ρ p u hP ha)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RegularizationSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Filter
open scoped Topology ENNReal

theorem fixed_polynomial_subpower (k : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ((4*(N:ℝ)+1)^k) ≤ ((2:ℝ)^N)^e := by
  have hb : 1 < (2:ℝ)^e := Real.one_lt_rpow (by norm_num) he
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt k hb).const_mul ((5:ℝ)^k)
  have hevent : ∀ᶠ N : ℕ in atTop, (5:ℝ)^k*((N:ℝ)^k/((2:ℝ)^e)^N) < 1 := by
    exact ht.eventually (gt_mem_nhds (by simp : (5:ℝ)^k*0 < (1:ℝ)))
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  refine ⟨max 1 N₀,?_⟩
  intro N hN
  have hN1 : 1 ≤ (N:ℝ) := by exact_mod_cast ((le_max_left 1 N₀).trans hN)
  have hh := hN₀ N ((le_max_right 1 N₀).trans hN)
  rw [← mul_div_assoc] at hh
  have hp : 0 < ((2:ℝ)^e)^N := by positivity
  have hpol : (4*(N:ℝ)+1)^k ≤ (5:ℝ)^k*(N:ℝ)^k := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by positivity) (by linarith) k
  have hbound := hpol.trans ((div_lt_one hp).mp hh).le
  rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),mul_comm e (N:ℝ),
    Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)] at hbound
  exact hbound

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularUniformAbsorption
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem fixed_linear_subpower (C : ℝ) (hC : 0 ≤ C) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, C*(1+2*(N:ℝ)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,hN₁⟩ := fixed_constant_absorbed (half_pos he) C
  obtain ⟨N₂,hN₂⟩ := fixed_polynomial_subpower 1 (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hc := hN₁ N ((le_max_left _ _).trans hN)
  have hp := hN₂ N ((le_max_right _ _).trans hN)
  simp only [pow_one] at hp
  have hlin : 1+2*(N:ℝ) ≤ ((2:ℝ)^N)^(e/2) := by
    have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
    linarith
  calc
    _ ≤ C*((2:ℝ)^N)^(e/2) := mul_le_mul_of_nonneg_left hlin hC
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem angular_ratio_absorption {N : ℕ} {K lam sig C : ℝ}
    (hlam : 0 < lam) (hsig : 0 < sig)
    (hC : C ≤ ((2:ℝ)^N)^(lam+sig)) :
    (C*((2:ℝ)^N)^(K+1000*sig+12*lam))/
        ((2:ℝ)^N)^(K+2000*(lam+sig)) ≤ ((2:ℝ)^N)^(-(lam+sig)) := by
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ ≤ (((2:ℝ)^N)^(lam+sig)*((2:ℝ)^N)^(K+1000*sig+12*lam))/
        ((2:ℝ)^N)^(K+2000*(lam+sig)) := by gcongr
    _ = ((2:ℝ)^N)^((lam+sig)+(K+1000*sig+12*lam)-(K+2000*(lam+sig))) := by
      rw [← Real.rpow_add hRp,← Real.rpow_sub hRp]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ParallelExceptional
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem regularized_parallel_inverse_scaled (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    (∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
      1/dist (Q.descendant c).center (Q.descendant P).center)/(2:ℝ)^p ≤
      484*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam) := by
  have hpack := hr.packing
  simp only [hQ,div_one] at hpack
  have hi := parallel_inverse_distance_profile Q hQ ρ m N lam hpack hgp hpN hP
  have hs := angular_profile_dyadic_sum m hN lam hgp
  have hn : ((p-g:ℕ):ℝ) ≤ N := by exact_mod_cast (show p-g ≤ N by omega)
  have hp : 0 < (2:ℝ)^p := by positivity
  apply (div_le_div_of_nonneg_right hi hp.le).trans
  rw [mul_div_assoc]
  calc
    _ ≤ 484*((1+2*(p-g:ℕ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+6*lam)) :=
      mul_le_mul_of_nonneg_left hs (by norm_num)
    _ ≤ _ := by rw [← mul_assoc]; gcongr

theorem regularized_parallel_strip_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam sig : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    (hlam : 0 < lam) (hsig : 0 < sig)
    {g p : ℕ} (hgp : g ≤ p) (hpN : p ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ c ∈ parallelTestCells Q ρ g p P,
      stripHitBound (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
        (quarterTurn ((Q.descendant c).center-(Q.descendant P).center)) ≤
      ENNReal.ofReal ((3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+1000*sig+6*lam)) := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  apply (parallel_strip_sum_inverse Q hside ρ g p hP (by positivity)).trans
  apply ENNReal.ofReal_le_ofReal
  let K := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p
  have hi := regularized_parallel_inverse_scaled Q hQ ρ hr hN hgp hpN hP
  change _ ≤ 484*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+6*lam) at hi
  have hRp : 0 < (2:ℝ)^N := by positivity
  have he : ((2:ℝ)^N)^(1000*sig)*((2:ℝ)^N)^(K+6*lam) =
      ((2:ℝ)^N)^(K+1000*sig+6*lam) := by rw [← Real.rpow_add hRp]; congr 1; ring
  have hK : 0 ≤ K := height_nonneg _ hgp
  have hz : 1 ≤ ((2:ℝ)^N)^(K+1000*sig+6*lam) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  have hn : 1 ≤ 1+2*(N:ℝ) := by have := Nat.cast_nonneg (α := ℝ) N; linarith
  have hb := mul_le_mul_of_nonneg_left hi
    (by positivity : 0 ≤ 8*Real.pi*((2:ℝ)^N)^(1000*sig))
  have hid : 8*Real.pi*((2:ℝ)^N)^(1000*sig)*
      (484*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+6*lam)) =
      3872*Real.pi*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam) := by
    calc
      _ = 3872*Real.pi*(1+2*(N:ℝ))*
        (((2:ℝ)^N)^(1000*sig)*((2:ℝ)^N)^(K+6*lam)) := by ring
      _ = _ := by rw [he]
  rw [hid] at hb
  have hdiag : 2*Real.pi ≤ 2*Real.pi*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam) := by
    calc
      _ ≤ 2*Real.pi*(1+2*(N:ℝ)) := le_mul_of_one_le_right (by positivity) hn
      _ ≤ _ := le_mul_of_one_le_right (by positivity) hz
  change _ ≤ (3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^(K+1000*sig+6*lam)
  calc
    _ = 2*Real.pi+8*Real.pi*((2:ℝ)^N)^(1000*sig)*
      ((∑ c ∈ (parallelTestCells Q ρ g p P).erase P,
        1/dist (Q.descendant c).center (Q.descendant P).center)/(2:ℝ)^p) := by ring
    _ ≤ _ := by linarith

theorem uniform_parallel_exceptional {lam sig : ℝ} (hlam : 0 < lam) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (B : ℕ) (δ : ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ g p : ℕ, g ≤ p → p ≤ N → ∀ P : CellPath, P.length = p →
      sourceArcLength (parallelGoodSet Q ρ g p P
        (2/(2:ℝ)^p*((2:ℝ)^N)^(1000*sig))
        (((2:ℝ)^N)^(height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p+2000*(lam+sig))))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨N₁,hN₁⟩ := fixed_linear_subpower (3874*Real.pi) (by positivity) (add_pos hlam hsig)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ ρ m B δ hr g p hgp hpN P hP
  have hNpos : 0 < N := by omega
  let K := height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) g p
  have hb := regularized_parallel_strip_sum Q hQ ρ hr hNpos hlam hsig hgp hpN hP
  apply (parallelGoodSet_compl_bound Q ρ g p P (by positivity) (by positivity)).trans
  apply (ENNReal.div_le_div_right hb _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc := hN₁ N ((le_max_right _ _).trans hN)
  apply le_trans _ (angular_ratio_absorption (K := K) hlam hsig hc)
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num))
  dsimp [K]; linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionExceptional
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem regularized_projection_card (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m)
    {p u : ℕ} (hpu : p ≤ u) (huN : u ≤ N) {P : CellPath} (hP : P.length = p) :
    ((projectionTestCells Q ρ p u P).card:ℝ) ≤
      64*((2:ℝ)^N)^(m u-m p+6*lam) := by
  have hc : ((projectionTestCells Q ρ p u P).card:ℝ) ≤
      ((occupiedCenterCells Q ρ u (Q.descendant P).center (3/(2:ℝ)^p)).card:ℝ) :=
    Nat.cast_le.mpr (Finset.card_le_card (projection_cells_subset_ball Q hQ ρ p u hP))
  have hp := hr.packing p u hpu huN (Q.descendant P).center 3 (by norm_num)
  norm_num [hQ] at hp
  exact hc.trans hp

theorem regularized_projection_strip_sum (Q : DyadicSquare) (hQ : Q.side = 1)
    (ρ : Measure Plane) {m : ℝ → ℝ} {N B : ℕ} {δ lam sig : ℝ}
    (hr : RegularizedProfileData Q ρ N B δ lam m) (hN : 0 < N)
    (hlam : 0 < lam) (hsig : 0 < sig)
    {p u : ℕ} (hpu : p ≤ u) (huN : u ≤ N) {P : CellPath} (hP : P.length = p) :
    ∑ cc ∈ (projectionTestCells Q ρ p u P).product (projectionTestCells Q ρ p u P),
      stripHitBound (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
        ((Q.descendant cc.1).center-(Q.descendant cc.2).center) ≤
      ENNReal.ofReal ((247936*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
        (m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+12*lam)) := by
  apply (projection_strip_sum_rows Q hQ ρ p u hP _).trans
  let Z := (3874*Real.pi)*(1+2*(N:ℝ))*((2:ℝ)^N)^
    (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+6*lam)
  have hz : 0 ≤ Z := by dsimp [Z]; positivity
  have hh : (∑ a ∈ projectionTestCells Q ρ p u P,
      ∑ c ∈ parallelTestCells Q ρ p u a,
        stripHitBound (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
          (quarterTurn ((Q.descendant c).center-(Q.descendant a).center))) ≤
      ∑ _a ∈ projectionTestCells Q ρ p u P, ENNReal.ofReal Z := by
    apply Finset.sum_le_sum
    intro a ha
    exact regularized_parallel_strip_sum Q hQ ρ hr hN hlam hsig hpu huN
      ((mem_dyadicPaths u a).mp (Finset.mem_filter.mp ha).1)
  apply hh.trans
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hc := mul_le_mul_of_nonneg_right (regularized_projection_card Q hQ ρ hr hpu huN hP) hz
  apply hc.trans_eq
  dsimp [Z]
  have hRp : 0 < (2:ℝ)^N := by positivity
  calc
    _ = (247936*Real.pi)*(1+2*(N:ℝ))*
      (((2:ℝ)^N)^(m u-m p+6*lam)*((2:ℝ)^N)^
        (height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+1000*sig+6*lam)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hRp]
      congr 2
      ring

theorem uniform_projection_exceptional {lam sig : ℝ} (hlam : 0 < lam) (hsig : 0 < sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (B : ℕ) (δ : ℝ),
      RegularizedProfileData Q ρ N B δ lam m →
      ∀ p u : ℕ, p ≤ u → u ≤ N → ∀ P : CellPath, P.length = p →
      sourceArcLength (projectionGoodSet Q ρ p u P
        (2/(2:ℝ)^u*((2:ℝ)^N)^(1000*sig))
        (((2:ℝ)^N)^(m u-m p+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p u+2000*(lam+sig))))ᶜ ≤
          ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨N₁,hN₁⟩ := fixed_linear_subpower (247936*Real.pi) (by positivity) (add_pos hlam hsig)
  refine ⟨max 1 N₁,?_⟩
  intro N hN Q hQ ρ m B δ hr p u hpu huN P hP
  have hb := regularized_projection_strip_sum Q hQ ρ hr (by omega) hlam hsig hpu huN hP
  apply (projectionGoodSet_compl_bound Q ρ p u P (by positivity) (by positivity)).trans
  apply (ENNReal.div_le_div_right hb _).trans
  rw [← ENNReal.ofReal_div_of_pos (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  exact angular_ratio_absorption hlam hsig (hN₁ N ((le_max_right _ _).trans hN))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngularRegularization
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem actual_angular_regularization (Q : DyadicSquare) (hQ : Q.side = 1)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam sig : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) (hsig : 0 < sig)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      let B := N/H
      let t := ENNReal.ofReal (((2:ℝ)^N)^(-lam))
      let L := regularizationLeaves Q μ N
      let F := regularizationLabel Q μ N B
      (retainedClassLabels Q μ N B t).card ≤ (4*N+1)^(2*H+1) ∧
      μ (retainedClassUnion Q μ N B t)ᶜ ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        (((4*N+1)^(2*H+1):ℕ):ENNReal)*t ∧
      ∀ T ∈ retainedClassLabels Q μ N B t,
        t ≤ classMeasure Q μ L F T univ ∧
        ∃ m : ℝ → ℝ,
          RegularizedProfileData Q (normalizedClass Q μ L F T) N B δ lam m ∧
          SourceAngularBounds Q (normalizedClass Q μ L F T) m N lam sig := by
  have hside : 0 < Q.side := by rw [hQ]; norm_num
  obtain ⟨H,N₁,hH,hHbound,hreg⟩ := actual_profile_regularization Q hside μ hcarry hC hlam hball
  obtain ⟨N₂,hpar⟩ := uniform_parallel_exceptional hlam hsig
  obtain ⟨N₃,hproj⟩ := uniform_projection_exceptional hlam hsig
  refine ⟨H,max N₁ (max N₂ N₃),hH,hHbound,?_⟩
  intro N hN
  have hNmax : max N₂ N₃ ≤ N := (le_max_right _ _).trans hN
  obtain ⟨hc,hd,hr⟩ := hreg N ((le_max_left _ _).trans hN)
  refine ⟨hc,hd,?_⟩
  intro T hT
  obtain ⟨hmass,m,hm⟩ := hr T hT
  exact ⟨hmass,m,hm,⟨hpar N ((le_max_left _ _).trans hNmax) Q hQ _ m _ δ hm,
    hproj N ((le_max_right _ _).trans hNmax) Q hQ _ m _ δ hm⟩⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngleMaskPeriodicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem thickening_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (r x : ℝ) :
    x+T ∈ thickening r G ↔ x ∈ thickening r G := by
  constructor
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    refine mem_thickening_iff.mpr ⟨z-T,?_,?_⟩
    · exact (hG (z-T)).mp (by simpa using hz)
    · simpa only [Real.dist_eq] using (show |x-(z-T)| < r by
        convert hd using 1; simp only [Real.dist_eq]; congr 1; ring)
  · intro hx
    obtain ⟨z,hz,hd⟩ := mem_thickening_iff.mp hx
    exact mem_thickening_iff.mpr ⟨z+T,(hG z).mpr hz,by simpa using hd⟩

theorem thickenedIndicator_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) :
    Function.Periodic (thickenedIndicator G η) T := by
  intro x
  classical
  simp only [thickenedIndicator,Set.indicator_apply,thickening_periodic hG]

theorem smoothAngleMask_periodic {G : Set ℝ} {T : ℝ}
    (hG : ∀ x : ℝ, x+T ∈ G ↔ x ∈ G) (η : ℝ) (hη : 0 < η) :
    Function.Periodic (smoothAngleMask G η hη) T := by
  intro x
  unfold smoothAngleMask
  simp only [convolution_def]
  apply integral_congr_ae
  filter_upwards [] with t
  have hp := thickenedIndicator_periodic hG η (x-t)
  rw [show x+T-t = (x-t)+T by ring,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskCoordinates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_periodic (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    Function.Periodic (sourceTestMask G d hd) (2*Real.pi) := by
  apply smoothAngleMask_periodic
  intro θ
  have he : sourceUnitDirection (θ+2*Real.pi) = sourceUnitDirection θ := by
    apply Subtype.ext
    simp only [sourceUnitDirection,sourceDirection,Real.cos_add_two_pi,Real.sin_add_two_pi]
  simp only [mem_preimage,he]

theorem circleTestMask_comp (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) (θ : ℝ) :
    circleTestMask G d hd (sourceUnitDirection θ) = sourceTestMask G d hd θ := by
  unfold circleTestMask
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := (sourceTestMask_periodic G d hd).int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleMaskSupport
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem circleTestMask_antipodal {G : Set UnitCircle}
    (hG : ∀ dir : UnitCircle, circleAntipode dir ∈ G ↔ dir ∈ G)
    (d : ℝ) (hd : 0 < d) (dir : UnitCircle) :
    circleTestMask G d hd (circleAntipode dir) = circleTestMask G d hd dir := by
  have hp : Function.Periodic (sourceTestMask G d hd) Real.pi := by
    apply smoothAngleMask_periodic
    intro θ
    simpa only [mem_preimage,sourceUnitDirection_add_pi] using hG (sourceUnitDirection θ)
  rw [← sourceUnitDirection_sourceAngle dir,← sourceUnitDirection_add_pi,
    circleTestMask_comp,circleTestMask_comp,hp]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualClassFamilies
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem actual_class_family (Q : DyadicSquare) (hQ : Q.side = 1)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (hcarry : μ Q.carrierᶜ = 0)
    {δ C lam sig : ℝ} (hC : 0 ≤ C) (hlam : 0 < lam) (hsig : 0 < sig)
    (hball : ∀ x : Plane, ∀ r > 0, μ (ball x r) ≤ ENNReal.ofReal (C*r^(1+δ))) :
    ∃ H N₀ : ℕ, 0 < H ∧ (H:ℝ) ≤ 1/lam+2 ∧ ∀ N ≥ N₀,
      ∃ m : List ℕ → ℝ → ℝ, ActualClassFamily Q μ N H δ lam sig m := by
  classical
  obtain ⟨H,N₀,hH,hHbound,hr⟩ := actual_angular_regularization Q hQ μ hcarry hC hlam hsig hball
  refine ⟨H,N₀,hH,hHbound,?_⟩
  intro N hN
  obtain ⟨hc,hd,hp⟩ := hr N hN
  let S := retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let m : List ℕ → ℝ → ℝ := fun T => if hT : T ∈ S then Classical.choose (hp T hT).2 else fun _ => 0
  refine ⟨m,⟨hc,hd,fun T hT => (hp T hT).1,?_⟩⟩
  intro T hT
  change T ∈ S at hT
  simpa only [m, dite_eq_left hT] using Classical.choose_spec (hp T hT).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_TotalVariation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem totalVariation_sub_of_add {α : Type*} [MeasurableSpace α]
    (τ σ ρ : Measure α) [IsFiniteMeasure τ] [IsFiniteMeasure σ] [IsFiniteMeasure ρ]
    (h : τ = σ+ρ) : (τ.toSignedMeasure-σ.toSignedMeasure).totalVariation = ρ := by
  have heq : τ.toSignedMeasure = σ.toSignedMeasure+ρ.toSignedMeasure := by
    calc
      τ.toSignedMeasure = (σ+ρ).toSignedMeasure := Measure.toSignedMeasure_congr h
      _ = σ.toSignedMeasure+ρ.toSignedMeasure := Measure.toSignedMeasure_add σ ρ
  rw [heq, add_sub_cancel_left, SignedMeasure.totalVariation_eq_variation,
    Measure.variation_toSignedMeasure]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualClassMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem coe_actualClassMass (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    (actualClassMass Q μ N B T : ENNReal) = μ (actualClassDomain Q μ N B T) :=
  ENNReal.coe_toNNReal (measure_ne_top μ _)

instance actualClassMeasure_instFinite (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) : IsFiniteMeasure (actualClassMeasure Q μ N B T) := by
  constructor
  change (normalizedClass Q μ (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) univ < ∞
  rw [normalizedClass_apply,univ_inter]
  change (μ (actualClassDomain Q μ N B T))⁻¹ * μ (actualClassDomain Q μ N B T) < ∞
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · simp [h]
  · rw [ENNReal.inv_mul_cancel h (measure_ne_top μ _)]
    exact ENNReal.one_lt_top

theorem actualClassMass_smul_measure (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) :
    actualClassMass Q μ N B T • actualClassMeasure Q μ N B T =
      μ.restrict (actualClassDomain Q μ N B T) := by
  rw [ENNReal.smul_def,coe_actualClassMass]
  simp only [actualClassMeasure,normalizedClass,classMeasure,Measure.restrict_apply_univ]
  change μ (actualClassDomain Q μ N B T) •
    ((μ (actualClassDomain Q μ N B T))⁻¹ • μ.restrict (actualClassDomain Q μ N B T)) = _
  by_cases h : μ (actualClassDomain Q μ N B T) = 0
  · rw [h,zero_smul,Measure.restrict_eq_zero.mpr h]
  · rw [smul_smul,ENNReal.mul_inv_cancel h (measure_ne_top μ _),one_smul]

theorem actualClassMass_sum_le_one (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) [IsProbabilityMeasure μ] (N B : ℕ) (t : ENNReal) :
    (∑ T ∈ retainedClassLabels Q μ N B t, (actualClassMass Q μ N B T : ℝ)) ≤ 1 := by
  have h := retainedClass_mass_sum_le_one Q hQ μ N B t
  simp only [classMeasure,Measure.restrict_apply_univ] at h
  change (∑ T ∈ retainedClassLabels Q μ N B t, μ (actualClassDomain Q μ N B T)) ≤ 1 at h
  simp_rw [← coe_actualClassMass Q μ N B] at h
  exact_mod_cast h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterMaskFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem actualClassMeasure_carry (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) :
    actualClassMeasure Q μ N B T Q.carrierᶜ = 0 := by
  rw [actualClassMeasure,normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem descriptorGoodSet_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) (dir : UnitCircle) :
    circleAntipode dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b ↔
      dir ∈ descriptorGoodSet Q ρ m N lam sig J i P b := by
  cases b with
  | parallel g p =>
    change (parallelTestCount Q ρ g p P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [parallelTestCount_neg]
    rfl
  | projection p u =>
    change (projectionTestCount Q ρ p u P _ (-(dir:Plane)):ℝ) ≤ _ ↔ _
    rw [projectionTestCount_neg]
    rfl

theorem spatialAnchorMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d)
    (hG : ∀ P : CellPath, ∀ dir : UnitCircle, circleAntipode dir ∈ G P ↔ dir ∈ G P)
    (x : Plane) (dir : UnitCircle) :
    spatialAnchorMask Q ρ n G d hd x (circleAntipode dir) = spatialAnchorMask Q ρ n G d hd x dir := by
  classical
  unfold spatialAnchorMask
  apply Finset.sum_congr rfl
  intro P _
  rw [circleTestMask_antipodal (hG P)]

theorem descriptorSpatialMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    descriptorSpatialMask Q ρ m N lam sig J i b x (circleAntipode dir) =
      descriptorSpatialMask Q ρ m N lam sig J i b x dir :=
  spatialAnchorMask_antipodal Q ρ _ _ _ _ (fun P dir => descriptorGoodSet_antipodal Q ρ m N lam sig J i P b dir) x dir

theorem descriptorListMask_antipodal (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) (dir : UnitCircle) :
    descriptorListMask Q ρ m N lam sig J i S x (circleAntipode dir) =
      descriptorListMask Q ρ m N lam sig J i S x dir := by
  unfold descriptorListMask
  apply Finset.prod_congr rfl
  intro b _
  exact descriptorSpatialMask_antipodal Q ρ m N lam sig J i b x dir

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RootEndpointData
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

namespace RootEndpointData

theorem mask_bounds (d : RootEndpointData) (hQ : 0 < d.Q.side)
    (N : ℕ) (sig : ℝ) (x : Plane) (dir : UnitCircle) :
    0 ≤ d.mask N sig x dir ∧ d.mask N sig x dir ≤ 1 :=
  descriptorListMask_bounds _ hQ _ _ _ _ _ _ _ _ _ _

end RootEndpointData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_RootPairSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem rootPairMask_bounds (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) (z : Plane × Plane) :
    0 ≤ rootPairMask d e N sig z ∧ rootPairMask d e N sig z ≤ 1 := by
  have h₁ := d.mask_bounds hd N sig z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := e.mask_bounds he N sig z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,(mul_le_of_le_one_left h₂.1 h₁.2).trans h₂.2⟩

theorem rootSpatialWeight_le (d e : RootEndpointData) (hd : 0 < d.Q.side) (he : 0 < e.Q.side)
    (N : ℕ) (sig : ℝ) {δ : ℝ} (hδ : 0 < δ) {z : Plane × Plane} (hz : δ ≤ dist z.1 z.2) :
    rootSpatialWeight d e N sig z ≤ δ^(-(1/2:ℝ)) := by
  apply (mul_le_of_le_one_right (Real.rpow_nonneg dist_nonneg _)
    (rootPairMask_bounds d e hd he N sig z).2).trans
  exact Real.rpow_le_rpow_of_nonpos hδ hz (by norm_num)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_RootWeightedDistance
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal

theorem rootWeightedPair_le (d e : RootEndpointData) (N : ℕ) (sig : ℝ)
    (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    rootWeightedPair d e N sig ≤ ENNReal.ofReal (δ^(-(1/2:ℝ))) • d.ρ.prod e.ρ := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [hsep] with z hz
  exact ENNReal.ofReal_le_ofReal (rootSpatialWeight_le d e hd he N sig hδ hz)

theorem rootWeightedPair_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedPair d e N sig) := by
  constructor
  apply (Measure.le_iff.mp (rootWeightedPair_le d e N sig hd he hδ hsep) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem rootWeightedDistance_isFinite (d e : RootEndpointData) [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (N : ℕ) (sig : ℝ) (hd : 0 < d.Q.side) (he : 0 < e.Q.side) {δ : ℝ} (hδ : 0 < δ)
    (hsep : ∀ᵐ z ∂d.ρ.prod e.ρ, δ ≤ dist z.1 z.2) :
    IsFiniteMeasure (rootWeightedDistance d e N sig) := by
  let := rootWeightedPair_isFinite d e N sig hd he hδ hsep
  unfold rootWeightedDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem DyadicSquare.dist_center_le_three_quarters (Q : DyadicSquare)
    (hQ : 0 ≤ Q.side) {x : Plane} (hx : x ∈ Q.carrier) :
    dist x Q.center ≤ 3/4*Q.side := by
  have h0 : |x 0 - Q.center 0| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.1, hx.2.1]
  have h1 : |x 1 - Q.center 1| ≤ Q.side/2 := by
    simp only [DyadicSquare.center, WithLp.ofLp_toLp, Matrix.cons_val_one, Matrix.cons_val_zero]
    apply abs_le.mpr
    constructor <;> linarith [hx.2.2.1, hx.2.2.2]
  have hs := EuclideanSpace.dist_sq_eq x Q.center
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at hs
  have hs0 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h0
  have hs1 := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ Q.side/2)).mpr h1
  rw [sq_abs] at hs0 hs1
  nlinarith [sq_nonneg Q.side, dist_nonneg (x := x) (y := Q.center)]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterRootEquation21
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter

namespace RootShellData

theorem ofOuter_measure (Q₁ Q₂ : DyadicSquare) (ρ ν : Measure Plane)
    (m₁ m₂ : ℝ → ℝ) (N : ℕ) (lam₁ lam₂ sig kap : ℝ) (c : ℕ) (U V : DyadicSquare) :
    (ofOuter Q₁ Q₂ ρ ν m₁ m₂ N lam₁ lam₂ sig kap c U V).measure =
      Measure.map (fun z : Plane × Plane => dist z.1 z.2)
        ((ρ.prod ν).withDensity (fun z => ENNReal.ofReal
          ((dist z.1 z.2)^(-(1/2:ℝ)) *
            (outerEndpointMask Q₁ ρ m₁ N lam₁ sig kap c z.1 (sourceRadialUnit z.2 z.1) *
             outerEndpointMask Q₂ ν m₂ N lam₂ sig kap c z.2 (sourceRadialUnit z.2 z.1))))) := rfl

end RootShellData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ReachedStateRecursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

namespace PolicyBranch
variable {A : ℕ → ℝ} {N q n : ℕ} {sig : ℝ}

@[simp] theorem extend_last_state (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).state (n+1) = u := ite_eq_right (by omega)

@[simp] theorem extend_last_label (b : PolicyBranch A N q sig n)
    {u : BranchState} {l : BranchLabel} (hu : u.Valid N sig)
    (hstep : BranchStep A N q sig (b.state n) l u) :
    (b.extend hu hstep).label n = l := ite_eq_right (Nat.lt_irrefl n)

end PolicyBranch

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_Shells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set ComplexConjugate
open scoped ENNReal

theorem fourier_energy_even (μ : Measure ℝ) (r : ℝ) :
    ‖charFun μ (-r)‖^2 = ‖charFun μ r‖^2 := by
  rw [charFun_neg]
  simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedOuterShell
attribute [-instance] _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem separated_unit_roots_distance (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center)
    (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (x y : Plane) (hx : x ∈ (Q 0).carrier) (hy : y ∈ (Q 1).carrier) :
    90 ≤ dist x y ∧ dist x y ≤ 2010 := by
  have hx' := (Q 0).dist_center_le_three_quarters (by rw [hQ 0]; norm_num) hx
  have hy' := (Q 1).dist_center_le_three_quarters (by rw [hQ 1]; norm_num) hy
  rw [hQ 0] at hx'
  rw [hQ 1] at hy'
  have hl := dist_triangle4 (Q 0).center x y (Q 1).center
  have hu := dist_triangle4 x (Q 0).center (Q 1).center y
  rw [dist_comm (Q 0).center x] at hl
  rw [dist_comm (Q 1).center y] at hu
  constructor <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RestoredMaskCoverage
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem sourceRadialUnit_swap {x y : Plane} (hxy : x ≠ y) :
    sourceRadialUnit y x = circleAntipode (sourceRadialUnit x y) := by
  apply Subtype.ext
  change sourceRadialVector y x = -sourceRadialVector x y
  simp only [sourceRadialVector,ite_eq_right hxy,ite_eq_right hxy.symm]
  rw [← neg_sub y x,norm_neg,smul_neg]

theorem outerEndpointMask_radial_swap (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) (c : ℕ) (z x y : Plane) :
    outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit y x) =
      outerEndpointMask Q ρ m N lam sig kap c z (sourceRadialUnit x y) := by
  by_cases hxy : x = y
  · subst y; rfl
  · rw [sourceRadialUnit_swap hxy]
    exact descriptorListMask_antipodal _ _ _ _ _ _ _ _ _ _ _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RestoredShellCandidates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem weightedProductInput_finite (μ ν : Measure Plane) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {r : ℝ} (hr : 0 < r) (hsep : ∀ᵐ z ∂μ.prod ν, r ≤ dist z.1 z.2) :
    IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight) := by
  constructor
  rw [withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  apply lt_of_le_of_lt (b := ENNReal.ofReal (r^(-1/2:ℝ))) _ ENNReal.ofReal_lt_top
  calc
    _ ≤ ∫⁻ _ : Plane × Plane, ENNReal.ofReal (r^(-1/2:ℝ)) ∂μ.prod ν := by
      apply lintegral_mono_ae
      filter_upwards [hsep] with z hz
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos hr hz (by norm_num))
    _ = _ := by simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RestorationSubpower
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ENNReal

theorem restoration_polynomial_bound (H : ℕ) {e : ℝ} (he : 0 < e) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      ((4*(N:ℝ)+1)^(2*H+1)*((N:ℝ)+1)*(((N:ℝ)+1)^3+1)) ≤ ((2:ℝ)^N)^e := by
  obtain ⟨N₁,h₁⟩ := fixed_constant_absorbed (half_pos he) 2
  obtain ⟨N₂,h₂⟩ := fixed_polynomial_subpower (2*H+5) (half_pos he)
  refine ⟨max N₁ N₂,?_⟩
  intro N hN
  have hn : 0 ≤ (N:ℝ) := Nat.cast_nonneg N
  have hb : (N:ℝ)+1 ≤ 4*(N:ℝ)+1 := by linarith
  have hpow : ((N:ℝ)+1)^3+1 ≤ 2*(4*(N:ℝ)+1)^3 := by nlinarith [pow_le_pow_left₀ (by positivity) hb 3]
  calc
    _ ≤ (4*(N:ℝ)+1)^(2*H+1)*(4*(N:ℝ)+1)*(2*(4*(N:ℝ)+1)^3) := by gcongr
    _ = 2*(4*(N:ℝ)+1)^(2*H+5) := by
      rw [show 2*H+5 = (2*H+1)+1+3 by omega,pow_add,pow_add,pow_one]
      ring
    _ ≤ ((2:ℝ)^N)^(e/2)*((2:ℝ)^N)^(e/2) :=
      mul_le_mul (h₁ N ((le_max_left _ _).trans hN)) (h₂ N ((le_max_right _ _).trans hN)) (by positivity) (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

theorem restorationArcBound_decay (H : ℕ) {lam sig : ℝ} (he : 0 < lam+sig) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      restorationArcBound N H lam sig ≤ ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)/2)) := by
  obtain ⟨N₀,h₀⟩ := restoration_polynomial_bound H (half_pos he)
  refine ⟨N₀,?_⟩
  intro N hN
  have hp : 0 < (2:ℝ)^N := by positivity
  have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h₀ N hN)
    (Real.rpow_nonneg hp.le (-(lam+sig))))
  have hr : ((2:ℝ)^N)^((lam+sig)/2)*((2:ℝ)^N)^(-(lam+sig)) = ((2:ℝ)^N)^(-(lam+sig)/2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hr] at hh
  rw [ENNReal.ofReal_mul (by positivity)] at hh
  have hc : ENNReal.ofReal ((4*(N:ℝ)+1)^(2*H+1)*((N:ℝ)+1)*(((N:ℝ)+1)^3+1)) =
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal) := by
    norm_cast
  rw [hc] at hh
  exact hh

theorem restorationDiscardBound_decay (H : ℕ) {lam : ℝ} (hlam : 0 < lam) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      restorationDiscardBound N H lam ≤ ENNReal.ofReal (((2:ℝ)^N)^(-2:ℝ))+
        ENNReal.ofReal (((2:ℝ)^N)^(-lam/2)) := by
  obtain ⟨N₀,h₀⟩ := fixed_polynomial_subpower (2*H+1) (half_pos hlam)
  refine ⟨N₀,?_⟩
  intro N hN
  apply add_le_add_right
  have hp : 0 < (2:ℝ)^N := by positivity
  have hh := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (h₀ N hN) (Real.rpow_nonneg hp.le (-lam)))
  have hr : ((2:ℝ)^N)^(lam/2)*((2:ℝ)^N)^(-lam) = ((2:ℝ)^N)^(-lam/2) := by
    rw [← Real.rpow_add hp]; congr 1; ring
  rw [hr] at hh
  rw [ENNReal.ofReal_mul (by positivity)] at hh
  have hc : ENNReal.ofReal ((4*(N:ℝ)+1)^(2*H+1)) = (((4*N+1)^(2*H+1):ℕ):ENNReal) := by norm_cast
  rw [hc] at hh
  exact hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_RestorationPowerRate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ENNReal

theorem restoration_power_rate (H₁ H₂ : ℕ) {lam sig p q : ℝ}
    (hlam : 0 < lam) (hsig : 0 < sig) (hpq : p.HolderConjugate q) :
    ∃ eta : ℝ, 0 < eta ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ C K : ENNReal,
      C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p)) ≤
      (C*(4+2*K))*ENNReal.ofReal (((2:ℝ)^N)^(-eta)) := by
  have ha : 0 < 1-1/p := by
    have hh := hpq.one_div_add_one_div
    have hq := one_div_pos.mpr hpq.symm.pos
    linarith
  let eta := min 2 (min (lam/2) ((lam+sig)*(1-1/p)/2))
  have heta : 0 < eta := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  obtain ⟨N₁,h₁⟩ := restorationDiscardBound_decay H₁ hlam
  obtain ⟨N₂,h₂⟩ := restorationDiscardBound_decay H₂ hlam
  obtain ⟨N₃,h₃⟩ := restorationArcBound_decay H₁ (add_pos hlam hsig)
  obtain ⟨N₄,h₄⟩ := restorationArcBound_decay H₂ (add_pos hlam hsig)
  refine ⟨eta,heta,max (max N₁ N₂) (max N₃ N₄),?_⟩
  intro N hN C K
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans ((le_max_left _ _).trans hN)
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans ((le_max_left _ _).trans hN)
  have hN₃ : N₃ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN₄ : N₄ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let Z := ENNReal.ofReal (((2:ℝ)^N)^(-eta))
  have hpow (e : ℝ) (he : eta ≤ e) : ENNReal.ofReal (((2:ℝ)^N)^(-e)) ≤ Z :=
    ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (neg_le_neg he))
  have h2 := hpow 2 (min_le_left _ _)
  have hl := hpow (lam/2) ((min_le_right _ _).trans (min_le_left _ _))
  have harc : (ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)/2)))^(1-1/p) ≤ Z := by
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) ha.le,← Real.rpow_mul (by positivity)]
    have he : -(lam+sig)/2*(1-1/p) = -((lam+sig)*(1-1/p)/2) := by ring
    rw [he]
    exact hpow _ ((min_le_right _ _).trans (min_le_right _ _))
  have hd₁ : restorationDiscardBound N H₁ lam ≤ Z+Z := by
    apply (h₁ N hN₁).trans
    simpa only [neg_div] using add_le_add h2 hl
  have hd₂ : restorationDiscardBound N H₂ lam ≤ Z+Z := by
    apply (h₂ N hN₂).trans
    simpa only [neg_div] using add_le_add h2 hl
  have hw₁ : (restorationArcBound N H₁ lam sig)^(1-1/p) ≤ Z :=
    (ENNReal.rpow_le_rpow (h₃ N hN₃) ha.le).trans harc
  have hw₂ : (restorationArcBound N H₂ lam sig)^(1-1/p) ≤ Z :=
    (ENNReal.rpow_le_rpow (h₄ N hN₄) ha.le).trans harc
  calc
    _ ≤ C*((Z+Z)+(Z+Z)+K*Z+K*Z) := by gcongr
    _ = (C*(4+2*K))*Z := by ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_ShellMixtures
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem norm_weighted_sum_sq_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0) (z : ι → ℂ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ ∑ i ∈ s, (c i : ℝ) * ‖z i‖^2 := by
  have hn : ‖∑ i ∈ s, (c i : ℝ) • z i‖ ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖ := by
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg (NNReal.coe_nonneg _)] using
      norm_sum_le s (fun i => (c i : ℝ) • z i)
  have hs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
    (f := fun i => (c i : ℝ)) (g := fun i => (c i : ℝ)*‖z i‖^2)
    (r := fun i => (c i : ℝ)*‖z i‖)
    (fun _ _ => NNReal.coe_nonneg _) (fun _ _ => by positivity)
    (fun _ _ => by nlinarith)
  have hg : 0 ≤ ∑ i ∈ s, (c i : ℝ)*‖z i‖^2 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hsq : ‖∑ i ∈ s, (c i : ℝ) • z i‖^2 ≤ (∑ i ∈ s, (c i : ℝ)*‖z i‖)^2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) hn 2
  exact hsq.trans (hs.trans (by nlinarith))

theorem charFun_weighted_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (r : ℝ) :
    charFun (∑ i ∈ s, c i • τ i) r = ∑ i ∈ s, (c i : ℝ) • charFun (τ i) r := by
  simp only [charFun_eq_integral_innerProbChar]
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_smul_nnreal_measure _ _
  · intro i hi
    exact (BoundedContinuousFunction.innerProbChar r).integrable _

theorem shellEnergy_weighted_sum_le {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ ∑ i ∈ s, (c i : ℝ)*shellEnergy (τ i) N := by
  have hi : IntegrableOn (fun r => ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2) (dyadicShell N) volume :=
    integrable_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)
  have hpoint (r : ℝ) : ‖charFun (∑ i ∈ s, c i • τ i) r‖^2 ≤
      ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 := by
    rw [charFun_weighted_sum]
    exact norm_weighted_sum_sq_le s c _ hc
  unfold shellEnergy
  calc
    _ ≤ ∫ r in dyadicShell N, ∑ i ∈ s, (c i : ℝ)*‖charFun (τ i) r‖^2 :=
      integral_mono (shell_energy_integrable _ N) hi hpoint
    _ = _ := by
      rw [integral_finsetSum s (fun i _ => (shell_energy_integrable (τ i) N).const_mul _)]
      simp_rw [integral_const_mul]

theorem shellEnergy_weighted_sum_uniform {ι : Type*} (s : Finset ι) (c : ι → ℝ≥0)
    (τ : ι → Measure ℝ) [∀ i, IsFiniteMeasure (τ i)] (N : ℕ)
    (hc : (∑ i ∈ s, (c i : ℝ)) ≤ 1) {C : ℝ} (hC : 0 ≤ C)
    (hτ : ∀ i ∈ s, shellEnergy (τ i) N ≤ C) :
    shellEnergy (∑ i ∈ s, c i • τ i) N ≤ C := by
  apply (shellEnergy_weighted_sum_le s c τ N hc).trans
  calc
    _ ≤ ∑ i ∈ s, (c i : ℝ)*C := Finset.sum_le_sum (fun i hi =>
      mul_le_mul_of_nonneg_left (hτ i hi) (NNReal.coe_nonneg _))
    _ = (∑ i ∈ s, (c i : ℝ))*C := (Finset.sum_mul ..).symm
    _ ≤ C := by nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootCandidates
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.actualClassMeasure_instFinite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem restoredTwoRootCandidate_totalVariation (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure ((μ.prod ν).withDensity distanceWeight)]
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) :
    let h := restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β
    letI := h.1
    letI := h.2
    ((weightedDistance (μ.prod ν)).toSignedMeasure-
      (restoredTwoRootCandidate Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).toSignedMeasure).totalVariation =
      restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β := by
  let := (restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).1
  let := (restoredTwoRootCandidate_finite Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β).2
  exact totalVariation_sub_of_add _ _ _ (restoredTwoRootCandidate_decomposition Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootClassMixture
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem twoRootClassMeasure_mask (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    (m₀ m₁ : List ℕ → ℝ → ℝ) (N B₀ B₁ : ℕ) (lam sig kap β : ℝ)
    (a : List ℕ × List ℕ) :
    twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
      (((actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2)).withDensity
        (fun z => distanceWeight z * twoRootPairMask Q₀ Q₁ (actualClassMeasure Q₀ μ N B₀ a.1)
          (actualClassMeasure Q₁ ν N B₁ a.2) (m₀ a.1) (m₁ a.2) N lam sig kap β z)).map
            (fun z => dist z.1 z.2) := by
  unfold twoRootClassMeasure
  rw [RootShellData.ofOuter_measure]
  congr 2
  funext z
  simp only [twoRootPairMask,distanceWeight,outerEndpointMask_radial_swap]
  simp only [neg_div]
  exact ENNReal.ofReal_mul (Real.rpow_nonneg (dist_nonneg : 0 ≤ dist z.1 z.2) _)

theorem twoRootClassCoefficient_sum_le_one (Q₀ Q₁ : DyadicSquare)
    (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (N B₀ B₁ : ℕ) (lam : ℝ) :
    (∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
      (twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a : ℝ)) ≤ 1 := by
  have h₀ := actualClassMass_sum_le_one Q₀ hQ₀ μ N B₀ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  have h₁ := actualClassMass_sum_le_one Q₁ hQ₁ ν N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  simp only [retainedRootPairs,twoRootClassCoefficient,NNReal.coe_mul]
  rw [Finset.product_eq_sprod,Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  exact (mul_le_mul h₀ h₁ (Finset.sum_nonneg (fun _ _ => NNReal.coe_nonneg _)) zero_le_one).trans_eq (mul_one 1)

theorem twoRootClassCoefficient_prod (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (N B₀ B₁ : ℕ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      (actualClassMeasure Q₀ μ N B₀ a.1).prod (actualClassMeasure Q₁ ν N B₁ a.2) =
        (μ.prod ν).restrict (actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2) := by
  rw [← Measure.prod_restrict,← actualClassMass_smul_measure Q₀ μ N B₀ a.1,
    ← actualClassMass_smul_measure Q₁ ν N B₁ a.2,
    Measure.prod_smul_left,Measure.prod_smul_right,smul_smul]
  rfl

theorem twoRootClassCoefficient_measure (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) (a : List ℕ × List ℕ) :
    twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
      twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a =
        ((μ.prod ν).withDensity (fun z => distanceWeight z *
          twoRootRetainedMask Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a z)).map
            (fun z => dist z.1 z.2) := by
  rw [twoRootClassMeasure_mask,
    ← Measure.map_smul]
  congr 1
  rw [ENNReal.smul_def,← withDensity_smul_measure,← ENNReal.smul_def,twoRootClassCoefficient_prod]
  rw [← withDensity_indicator ((measurableSet_actualClassDomain ..).prod (measurableSet_actualClassDomain ..))]
  congr 1
  funext z
  classical
  unfold twoRootRetainedMask
  by_cases h : z ∈ actualClassDomain Q₀ μ N B₀ a.1 ×ˢ actualClassDomain Q₁ ν N B₁ a.2
  · simp only [Set.indicator_of_mem h]
  · simp only [Set.indicator_of_notMem h,mul_zero]

theorem restoredTwoRootCandidate_eq_sum (Q₀ Q₁ : DyadicSquare) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) :
    restoredTwoRootCandidate Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β =
      ∑ a ∈ retainedRootPairs Q₀ Q₁ μ ν N B₀ B₁ lam,
        twoRootClassCoefficient Q₀ Q₁ μ ν N B₀ B₁ a •
          twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a := by
  simp_rw [twoRootClassCoefficient_measure]
  unfold restoredTwoRootCandidate restoredTwoRootMask
  simp_rw [Finset.mul_sum]
  rw [← Measure.map_finset_sum (by fun_prop)]
  congr 1
  ext S hS
  simp only [withDensity_apply _ hS,Measure.finsetSum_apply]
  exact lintegral_finsetSum _ (fun a _ =>
    (show Measurable distanceWeight by unfold distanceWeight; fun_prop).mul
      (measurable_twoRootRetainedMask ..))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootMixtureFinite
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem twoRootClassMeasure_isFinite (Q₀ Q₁ : DyadicSquare)
    (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (m₀ m₁ : List ℕ → ℝ → ℝ)
    (N B₀ B₁ : ℕ) (lam sig kap β : ℝ) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ x ∈ Q₀.carrier, ∀ y ∈ Q₁.carrier, r ≤ dist x y)
    (a : List ℕ × List ℕ) :
    IsFiniteMeasure (twoRootClassMeasure Q₀ Q₁ μ ν m₀ m₁ N B₀ B₁ lam sig kap β a) := by
  have hx : ∀ᵐ x ∂actualClassMeasure Q₀ μ N B₀ a.1, x ∈ Q₀.carrier :=
    actualClassMeasure_carry Q₀ hQ₀ μ N B₀ a.1
  have hy : ∀ᵐ y ∂actualClassMeasure Q₁ ν N B₁ a.2, y ∈ Q₁.carrier :=
    actualClassMeasure_carry Q₁ hQ₁ ν N B₁ a.2
  dsimp only [twoRootClassMeasure,RootShellData.ofOuter,RootShellData.measure,RootEndpointData.ofOuter]
  apply rootWeightedDistance_isFinite _ _ N sig hQ₀ hQ₁ hr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hx,
    Measure.quasiMeasurePreserving_snd.ae hy] with z hz₀ hz₁
  exact hsep z.1 hz₀ z.2 hz₁

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoSidedShell
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem shellEnergy_eq_twice_positive (μ : Measure ℝ) [IsFiniteMeasure μ] (N : ℕ) :
    shellEnergy μ N = 2 *
      ∫ r in Icc ((2:ℝ)^((N:ℝ)-1)) ((2:ℝ)^((N:ℝ)+1)), ‖charFun μ r‖^2 := by
  let a := (2:ℝ)^((N:ℝ)-1)
  let b := (2:ℝ)^((N:ℝ)+1)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hsets : dyadicShell N = Icc a b ∪ Icc (-b) (-a) := by
    ext r
    change (a ≤ |r| ∧ |r| ≤ b) ↔ (a ≤ r ∧ r ≤ b) ∨ (-b ≤ r ∧ r ≤ -a)
    rcases le_total 0 r with h | h
    · rw [abs_of_nonneg h]
      constructor
      · exact Or.inl
      · rintro (h | h)
        · exact h
        · exfalso; linarith
    · rw [abs_of_nonpos h]
      constructor
      · intro h; right; constructor <;> linarith
      · rintro (h | h)
        · exfalso; linarith
        · constructor <;> linarith
  have hdis : Disjoint (Icc a b) (Icc (-b) (-a)) := by
    apply Set.disjoint_left.mpr
    intro r h₀ h₁
    have := h₀.1
    have := h₁.2
    linarith
  have hi (c d : ℝ) : IntegrableOn (fun r => ‖charFun μ r‖^2) (Icc c d) :=
    (continuous_charFun.norm.pow 2).continuousOn.integrableOn_compact isCompact_Icc
  have hneg : (∫ r in Icc (-b) (-a), ‖charFun μ r‖^2) =
      ∫ r in Icc a b, ‖charFun μ r‖^2 := by
    have hemb : MeasurableEmbedding (fun x : ℝ => -x) := (Homeomorph.neg ℝ).measurableEmbedding
    have h := hemb.setIntegral_map
      (μ := (volume : Measure ℝ)) (fun r => ‖charFun μ r‖^2) (Icc (-b) (-a))
    rw [Measure.map_neg_eq_self] at h
    have hp : (fun x : ℝ => -x) ⁻¹' Icc (-b) (-a) = Icc a b := by
      ext x
      simp only [mem_preimage,mem_Icc]
      constructor <;> intro h <;> constructor <;> linarith
    simpa only [hp,fourier_energy_even] using h
  rw [shellEnergy,hsets,setIntegral_union hdis measurableSet_Icc (hi a b) (hi (-b) (-a)),hneg]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootShellDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ENNReal

theorem uniform_two_root_shell_decay {δ β lam sig kap : ℝ}
    (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ N₀ : ℕ, 0 < N₀ ∧ ∀ N ≥ N₀,
      ∀ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) →
      100 ≤ dist (Q 0).center (Q 1).center → dist (Q 0).center (Q 1).center ≤ 2000 →
      ∀ μ ν : Measure Plane, ∀ [IsProbabilityMeasure μ] [IsProbabilityMeasure ν],
      ∀ H₀ H₁ : ℕ, 0 < H₀ → 0 < H₁ → H₀ ≤ N → H₁ ≤ N →
      ∀ m₀ m₁ : List ℕ → ℝ → ℝ,
      ActualClassFamily (Q 0) μ N H₀ δ lam sig m₀ → ActualClassFamily (Q 1) ν N H₁ δ lam sig m₁ →
      shellEnergy (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β) N ≤
        2*((2:ℝ)^N)^(-β/2) := by
  obtain ⟨N₀,hN₀,h₀⟩ := uniform_independent_class_equation27 hδ hδ1 hβ hlam hlamδ hsig
    hkap hkapβ hgap hratio hΨ hpos hs hone
  refine ⟨N₀,hN₀,?_⟩
  intro N hN Q hQ hlo hhi μ ν instμ instν H₀ H₁ hH₀ hH₁ hNH₀ hNH₁ m₀ m₁ hf₀ hf₁
  have hQ₀ : 0 < (Q 0).side := by rw [hQ 0]; norm_num
  have hQ₁ : 0 < (Q 1).side := by rw [hQ 1]; norm_num
  have hsep : ∀ x ∈ (Q 0).carrier, ∀ y ∈ (Q 1).carrier, 90 ≤ dist x y :=
    fun x hx y hy => (separated_unit_roots_distance Q hQ hlo hhi x y hx hy).1
  let : ∀ classPair : List ℕ × List ℕ, IsFiniteMeasure
      (twoRootClassMeasure (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β classPair) :=
    fun classPair => twoRootClassMeasure_isFinite (Q 0) (Q 1) hQ₀ hQ₁ μ ν
      m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β (by norm_num : (0:ℝ) < 90) hsep classPair
  rw [restoredTwoRootCandidate_eq_sum]
  apply shellEnergy_weighted_sum_uniform _ _ _ N
    (twoRootClassCoefficient_sum_le_one (Q 0) (Q 1) hQ₀ hQ₁ μ ν N (N/H₀) (N/H₁) lam) (by positivity)
  intro a ha
  have ha := Finset.mem_product.mp ha
  let ρ : Fin 2 → Measure Plane := ![actualClassMeasure (Q 0) μ N (N/H₀) a.1,
    actualClassMeasure (Q 1) ν N (N/H₁) a.2]
  let mass : Fin 2 → ℝ → ℝ := ![m₀ a.1,m₁ a.2]
  let B : Fin 2 → ℕ := ![N/H₀,N/H₁]
  have hcarry (l : Fin 2) : ρ l (Q l).carrierᶜ = 0 := by
    fin_cases l
    · exact actualClassMeasure_carry (Q 0) hQ₀ μ N (N/H₀) a.1
    · exact actualClassMeasure_carry (Q 1) hQ₁ ν N (N/H₁) a.2
  have hB (l : Fin 2) : 0 < B l := by
    fin_cases l
    · exact Nat.div_pos hNH₀ hH₀
    · exact Nat.div_pos hNH₁ hH₁
  have hp (l : Fin 2) : RegularizedProfileData (Q l) (ρ l) N (B l) δ lam (mass l) := by
    fin_cases l
    · exact (hf₀.profiles a.1 ha.1).1
    · exact (hf₁.profiles a.2 ha.2).1
  have hpair := h₀ N hN Q ρ mass hQ hcarry hlo hhi B hB hp
  rw [shellEnergy_eq_twice_positive]
  exact mul_le_mul_of_nonneg_left hpair (by norm_num)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootApproximations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

theorem dyadic_negative_power (e : ℝ) (N : ℕ) :
    ((2:ℝ)^N)^(-e) = (2:ℝ)^(-e*(N:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem hasShellApproximations_of_eventual (τ : FiniteMeasure ℝ)
    {eta gamma Ctv Cshell : ℝ} (heta : 0 < eta) (hgamma : 0 < gamma)
    (hCtv : 0 < Ctv) (hCshell : 0 < Cshell) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ∃ σ : FiniteMeasure ℝ,
      variationDistance τ σ ≤ ENNReal.ofReal (Ctv*(2:ℝ)^(-eta*(N:ℝ))) ∧
        shellEnergy σ N ≤ Cshell*(2:ℝ)^(-gamma*(N:ℝ))) :
    HasShellApproximations τ := by
  classical
  let σ : ℕ → FiniteMeasure ℝ := fun N => if hn : N₀ ≤ N then Classical.choose (h N hn) else 0
  refine ⟨σ,eta,gamma,Ctv,Cshell,heta,hgamma,hCtv,hCshell,N₀,?_⟩
  intro N hN
  dsimp only [σ]
  rw [dite_eq_left hN]
  exact Classical.choose_spec (h N hN)

theorem two_root_has_shell_approximations_oai (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center) (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (μ ν : ProbabilityMeasure Plane) (hμQ : (μ:Measure Plane) (Q 0).carrierᶜ = 0)
    (hνQ : (ν:Measure Plane) (Q 1).carrierᶜ = 0)
    {δ β lam sig kap C₀ C₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hball₀ : ∀ x : Plane, ∀ r > 0, (μ:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₀*r^(1+δ)))
    (hball₁ : ∀ x : Plane, ∀ r > 0, (ν:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₁*r^(1+δ)))
    {p q : ℝ} (hpq : p.HolderConjugate q) {K : ENNReal} (hK : K ≠ ⊤)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ hτ : IsFiniteMeasure (weightedDistance ((μ:Measure Plane).prod ν)),
      HasShellApproximations ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ := by
  have hQ₀ : 0 < (Q 0).side := by rw [hQ 0]; norm_num
  have hQ₁ : 0 < (Q 1).side := by rw [hQ 1]; norm_num
  have hsep : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane), 90 ≤ dist z.1 z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμQ,
      Measure.quasiMeasurePreserving_snd.ae hνQ] with z hx hy
    exact (separated_unit_roots_distance Q hQ hlo hhi z.1 z.2 hx hy).1
  let := weightedProductInput_finite (μ:Measure Plane) (ν:Measure Plane) (by norm_num : (0:ℝ) < 90) hsep
  let τ : FiniteMeasure ℝ := ⟨weightedDistance ((μ:Measure Plane).prod ν),(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  refine ⟨(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)),?_⟩
  change HasShellApproximations τ
  obtain ⟨H₀,N₀,hH₀,_,hf₀⟩ := actual_class_family (Q 0) (hQ 0) (μ:Measure Plane) hμQ hC₀ hlam hsig hball₀
  obtain ⟨H₁,N₁,hH₁,_,hf₁⟩ := actual_class_family (Q 1) (hQ 1) (ν:Measure Plane) hνQ hC₁ hlam hsig hball₁
  obtain ⟨NS,hNS,hshell⟩ := uniform_two_root_shell_decay hδ hδ1 hβ hlam hlamδ hsig
    hkap hkapβ hgap hratio hΨ hpos hs hone
  obtain ⟨eta,heta,NR,hrate⟩ := restoration_power_rate H₀ H₁ hlam hsig hpq
  let D := ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ))*(4+2*K)
  have hD : D ≠ ⊤ := by dsimp only [D]; finiteness
  have hDbound : D ≤ ENNReal.ofReal (D.toReal+1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)
  apply hasShellApproximations_of_eventual τ heta (show 0 < β/2 by rw [hβ]; positivity)
    (show 0 < D.toReal+1 by positivity) (by norm_num : (0:ℝ) < 2)
    (max (max NS NR) (max (max N₀ N₁) (max H₀ H₁)))
  intro N hN
  obtain ⟨m₀,hm₀⟩ := hf₀ N (by omega)
  obtain ⟨m₁,hm₁⟩ := hf₁ N (by omega)
  have hfinite := restoredTwoRootCandidate_finite (Q 0) (Q 1) hQ₀ hQ₁ (μ:Measure Plane) (ν:Measure Plane)
    m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β
  let := hfinite.1
  let := hfinite.2
  let σ : FiniteMeasure ℝ := ⟨restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β,(by first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability))⟩
  refine ⟨σ,?_,?_⟩
  · have hweight : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane), distanceWeight z ≤
        ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ)) := by
      filter_upwards [hsep] with z hz
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by norm_num))
    have hremoved := two_root_restored_removed_mass_bound (Q 0) (Q 1) hQ₀ hQ₁ μ ν m₀ m₁
      (by omega : 0 < N) δ lam sig hkap β hm₀ hm₁ hpq hK hμrad hνrad hweight
    have hrate' := hrate N (by omega) (ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ))) K
    change ((weightedDistance ((μ:Measure Plane).prod ν)).toSignedMeasure -
      (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β).toSignedMeasure).totalVariation univ ≤ _
    rw [restoredTwoRootCandidate_totalVariation (Q 0) (Q 1) hQ₀ hQ₁]
    apply (hremoved.trans hrate').trans
    change D*ENNReal.ofReal (((2:ℝ)^N)^(-eta)) ≤ _
    rw [dyadic_negative_power,ENNReal.ofReal_mul (show 0 ≤ D.toReal+1 by positivity)]
    exact mul_le_mul_left hDbound _
  · have hb := hshell N (by omega) Q hQ hlo hhi (μ:Measure Plane) (ν:Measure Plane)
      H₀ H₁ hH₀ hH₁ (by omega) (by omega) m₀ m₁ hm₀ hm₁
    change shellEnergy (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β) N ≤ _
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    simpa only [neg_div] using (dyadic_negative_power (β/2) N).symm

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.two_root_has_shell_approximations_oai := @OAI.PlanarFalconer.two_root_has_shell_approximations_oai
