-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_distance_low_band
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:12:53.857103+00:00
-- url     : https://prove2.me/submissions/df34dc11-dfea-4cc6-860e-69128bf7a0f4

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002

section
-- module Solutions.OAIQ038_FA.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SmoothAngleMask
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Function ContinuousLinearMap
open scoped Convolution Topology ContDiff

theorem smoothAngleMask_support (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    Function.support (smoothAngleMask G η hη) ⊆ thickening (3*η) G := by
  intro x hx
  obtain ⟨a,ha,b,hb,hab⟩ := support_convolution_subset (lsmul ℝ ℝ) hx
  rw [(angleBump η hη).support_normed_eq] at ha
  have hb' : b ∈ thickening (2*η) G := by
    by_contra hn
    exact hb (Set.indicator_of_notMem hn (fun _ : ℝ => (1:ℝ)))
  obtain ⟨z,hz,hbz⟩ := mem_thickening_iff.mp hb'
  apply mem_thickening_iff.mpr
  refine ⟨z,hz,?_⟩
  change dist a 0 < η at ha
  rw [← hab]
  have he : dist (a+b) b = dist a 0 := by simp [dist_eq_norm]
  have hd := dist_triangle (a+b) b z
  rw [he] at hd
  linarith

theorem smoothAngleMask_tsupport (G : Set ℝ) (η : ℝ) (hη : 0 < η) :
    tsupport (smoothAngleMask G η hη) ⊆ thickening (4*η) G := by
  exact (closure_mono (smoothAngleMask_support G η hη)).trans
    ((closure_thickening_subset_cthickening (3*η) G).trans
      (cthickening_subset_thickening' (by positivity) (by linarith) G))

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem DyadicSquare.cover_children (Q : DyadicSquare) :
    Q.carrier = ((Q.child false false).carrier ∪ (Q.child false true).carrier) ∪
      ((Q.child true false).carrier ∪ (Q.child true true).carrier) := by
  ext z
  simp only [carrier, child, Bool.false_eq_true, ↓reduceIte,
    add_zero, mem_ofPred_eq, mem_union]
  constructor
  · intro hz
    by_cases hx : z 0 < Q.x + Q.side / 2 <;>
      by_cases hy : z 1 < Q.y + Q.side / 2
    · exact Or.inl (Or.inl ⟨hz.1,hx,hz.2.2.1,hy⟩)
    · exact Or.inl (Or.inr ⟨hz.1,hx,by linarith,by linarith [hz.2.2.2]⟩)
    · exact Or.inr (Or.inl ⟨by linarith,by linarith [hz.2.1],hz.2.2.1,hy⟩)
    · exact Or.inr (Or.inr ⟨by linarith,by linarith [hz.2.1],
        by linarith,by linarith [hz.2.2.2]⟩)
  · intro hz
    rcases hz with (hz | hz) | (hz | hz) <;>
      refine ⟨by linarith [hz.1,hz.2.1], by linarith [hz.1,hz.2.1],
        by linarith [hz.2.2.1,hz.2.2.2], by linarith [hz.2.2.1,hz.2.2.2]⟩

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

theorem DyadicSquare.mem_descendant_at_depth (Q : DyadicSquare) (n : ℕ)
    {z : Plane} (hz : z ∈ Q.carrier) :
    ∃ p ∈ dyadicPaths n, z ∈ (Q.descendant p).carrier := by
  induction n generalizing Q with
  | zero => exact ⟨[],by simp, hz⟩
  | succ n ih =>
    have step (i j : Bool) (hz : z ∈ (Q.child i j).carrier) :
        ∃ p ∈ dyadicPaths (n+1), z ∈ (Q.descendant p).carrier := by
      obtain ⟨p,hp,hz⟩ := ih _ hz
      exact ⟨(i,j) :: p,by simpa using hp,hz⟩
    rw [Q.cover_children] at hz
    rcases hz with (hz | hz) | (hz | hz)
    · exact step false false hz
    · exact step false true hz
    · exact step true false hz
    · exact step true true hz

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem planeDot_abs_le (v w : Plane) : |planeDot v w| ≤ ‖v‖*‖w‖ := by
  have hv := EuclideanSpace.real_norm_sq_eq v
  have hw := EuclideanSpace.real_norm_sq_eq w
  simp only [Fin.sum_univ_two] at hv hw
  have hsq : (planeDot v w)^2 ≤ ‖v‖^2*‖w‖^2 := by
    rw [hv,hw]
    unfold planeDot
    nlinarith [sq_nonneg (v 0*w 1-v 1*w 0)]
  have hp : 0 ≤ ‖v‖*‖w‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  nlinarith [sq_abs (planeDot v w),abs_nonneg (planeDot v w)]

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

theorem stripCount_transfer {ι : Type*} (S : Finset ι) (v : ι → Plane)
    {W W' D d : ℝ} (hD : 0 ≤ D) (hv : ∀ i ∈ S, ‖v i‖ ≤ D)
    {ω ω' : Plane} (hd : dist ω ω' ≤ d) (hgap : W'+D*d ≤ W) :
    stripCount S v W' ω' ≤ stripCount S v W ω := by
  classical
  apply Finset.card_le_card
  intro i hi
  obtain ⟨hi,hstrip⟩ := Finset.mem_filter.mp hi
  refine Finset.mem_filter.mpr ⟨hi,?_⟩
  have he : planeDot (v i) ω = planeDot (v i) ω' + planeDot (v i) (ω-ω') := by
    simp [planeDot]; ring
  have hn : ‖ω-ω'‖ ≤ d := by simpa only [dist_eq_norm] using hd
  calc
    |planeDot (v i) ω| ≤ |planeDot (v i) ω'|+|planeDot (v i) (ω-ω')| := by
      rw [he]; exact abs_add_le _ _
    _ ≤ W'+D*d := add_le_add hstrip ((planeDot_abs_le _ _).trans
      (mul_le_mul (hv i hi) hn (norm_nonneg _) hD))
    _ ≤ W := hgap

theorem continuous_quarterTurn : Continuous quarterTurn := by
  unfold quarterTurn
  fun_prop

theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem quarterTurn_sub (v w : Plane) : quarterTurn (v-w) = quarterTurn v-quarterTurn w := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

theorem measurable_parallelGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (parallelGoodSet Q ρ g p P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp
    (continuous_quarterTurn.measurable.comp continuous_subtype_val.measurable)

theorem measurable_projectionGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (p u : ℕ) (P : CellPath) (W threshold : ℝ) : MeasurableSet (projectionGoodSet Q ρ p u P W threshold) := by
  apply measurableSet_le _ measurable_const
  apply (measurable_of_countable (fun n : ℕ => (n:ℝ))).comp
  exact (measurable_stripCount _ _ W).comp continuous_subtype_val.measurable

theorem parallelTestCount_transfer (Q : DyadicSquare) (ρ : Measure Plane)
    (g p : ℕ) (P : CellPath) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(10/(2:ℝ)^g)*d ≤ W) :
    parallelTestCount Q ρ g p P W' ω' ≤ parallelTestCount Q ρ g p P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 10/(2:ℝ)^g) _ _ hgap
  · intro c hc
    have hh : ‖(Q.descendant c).center-(Q.descendant P).center‖ < 10/(2:ℝ)^g := by
      simpa only [mem_ball,dist_eq_norm] using (Finset.mem_filter.mp hc).2.2
    exact hh.le
  · simpa only [dist_eq_norm,← quarterTurn_sub,norm_quarterTurn] using hd

theorem projectionTestCount_transfer (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (p u : ℕ) {P : CellPath} (hP : P.length = p) {W W' d : ℝ} {ω ω' : Plane}
    (hd : dist ω ω' ≤ d) (hgap : W'+(2*Q.side/(2:ℝ)^p)*d ≤ W) :
    projectionTestCount Q ρ p u P W' ω' ≤ projectionTestCount Q ρ p u P W ω := by
  classical
  apply stripCount_transfer _ _ (by positivity : 0 ≤ 2*Q.side/(2:ℝ)^p) _ hd hgap
  intro cc hcc
  have hmem {c : CellPath} (hc : c ∈ projectionTestCells Q ρ p u P) :
      (Q.descendant c).center ∈ (Q.descendant P).carrier := by
    rw [← (Finset.mem_filter.mp hc).2.2]
    exact Q.descendant_subset_take hQ c p ((Q.descendant c).center_mem (Q.descendant_side_pos hQ c))
  have hh := (Q.descendant P).dist_le (Q.descendant_side_pos hQ P).le
    (hmem (Finset.mem_product.mp hcc).1) (hmem (Finset.mem_product.mp hcc).2)
  simpa only [dist_eq_norm,Q.descendant_side,hP,mul_div_assoc] using hh

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularWidths
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceAngularWidth_gap (N : ℕ) (sig : ℝ) {J : ℕ} (hJ : 0 < J) (i n : ℕ) :
    sourceAngularWidth N sig J i n-sourceAngularWidth N sig J (i+1) n =
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
  have hj : (J:ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  simp only [sourceAngularWidth,Nat.cast_add,Nat.cast_one]
  field_simp
  ring

theorem uniform_angular_width_gap {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) (C : ℝ) (hC : 0 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ g n : ℕ, g ≤ n → ∀ i : ℕ,
      sourceAngularWidth N sig J (i+1) n+
        (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      sourceAngularWidth N sig J i n := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (by positivity : 0 < 950*sig) (C*(J:ℝ))
  refine ⟨N₀,?_⟩
  intro N hN g n hgn i
  have hj : 0 < (J:ℝ) := by exact_mod_cast hJ
  have hRp : 0 < (2:ℝ)^N := by positivity
  have hconst := mul_le_mul_of_nonneg_right (hN₀ N hN)
    (by positivity : 0 ≤ ((2:ℝ)^N)^(50*sig))
  have he : ((2:ℝ)^N)^(950*sig)*((2:ℝ)^N)^(50*sig) =
      ((2:ℝ)^N)^(1000*sig) := by rw [← Real.rpow_add hRp]; congr 1; ring
  rw [he] at hconst
  have hp : (2:ℝ)^g*(2:ℝ)^(n-g) = (2:ℝ)^n := by rw [← pow_add,Nat.add_sub_of_le hgn]
  have hb : (C/(2:ℝ)^g)*sourceAngularRadius N sig (n-g) ≤
      ((2:ℝ)^N)^(1000*sig)/((J:ℝ)*(2:ℝ)^n) := by
    calc
      _ ≤ (C/(2:ℝ)^g)*(1/(2:ℝ)^(n-g)*((2:ℝ)^N)^(50*sig)) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)
      _ = (C*(J:ℝ)*((2:ℝ)^N)^(50*sig))/((J:ℝ)*(2:ℝ)^n) := by
        rw [← hp]
        field_simp
      _ ≤ _ := div_le_div_of_nonneg_right hconst (by positivity)
  rw [← sourceAngularWidth_gap N sig hJ i n] at hb
  linarith

theorem uniform_parallel_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (p-g) →
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) ω' ≤
      parallelTestCount Q ρ g p P (sourceAngularWidth N sig J i p) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (10*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i ω ω' hdist
  apply parallelTestCount_transfer Q ρ g p P hdist
  convert hN₀ N hN g p hgp i using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem uniform_projection_width_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) {C₀ : ℝ} (hC₀ : 0 ≤ C₀) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (ω ω' : Plane),
      dist ω ω' ≤ C₀*sourceAngularRadius N sig (u-p) →
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) ω' ≤
      projectionTestCount Q ρ p u P (sourceAngularWidth N sig J i u) ω := by
  obtain ⟨N₀,hN₀⟩ := uniform_angular_width_gap hsig hJ (2*C₀) (by positivity)
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i ω ω' hdist
  apply projectionTestCount_transfer Q (by rw [hQ]; norm_num) ρ p u hP hdist
  rw [hQ]
  convert hN₀ N hN p u hpu i using 1
  all_goals try with_reducible_and_instances rfl
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_support_transfer {G H : Set UnitCircle} {d : ℝ} (hd : 0 < d)
    (htransfer : ∀ (dir : UnitCircle), dir ∈ G → ∀ dir' : UnitCircle, dist (dir:Plane) (dir':Plane) ≤ d → dir' ∈ H) :
    tsupport (sourceTestMask G d hd) ⊆ sourceUnitDirection ⁻¹' H := by
  intro θ hθ
  obtain ⟨φ,hφ,hclose⟩ := mem_thickening_iff.mp (smoothAngleMask_tsupport _ _ _ hθ)
  apply htransfer (sourceUnitDirection φ) hφ (sourceUnitDirection θ)
  change dist (sourceDirection φ) (sourceDirection θ) ≤ d
  have hh := sourceDirection_dist_le φ θ
  rw [dist_comm θ φ] at hclose
  exact hh.trans (by linarith only [hclose, hd])

theorem uniform_parallel_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare) (ρ : Measure Plane),
      ∀ g p : ℕ, g ≤ p → ∀ (P : CellPath) (i : ℕ) (T : ℝ),
      tsupport (sourceParallelMask N sig J i Q ρ g p P T) ⊆
        sourceUnitDirection ⁻¹' parallelGoodSet Q ρ g p P (sourceAngularWidth N sig J (i+1) p) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_parallel_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q ρ g p hgp P i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (parallelTestCount Q ρ g p P (sourceAngularWidth N sig J (i+1) p) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q ρ g p hgp P i dir dir' (by simpa using hdist))).trans hdir

theorem uniform_projection_mask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 → ∀ (ρ : Measure Plane),
      ∀ p u : ℕ, p ≤ u → ∀ P : CellPath, P.length = p → ∀ (i : ℕ) (T : ℝ),
      tsupport (sourceProjectionMask N sig J i Q ρ p u P T) ⊆
        sourceUnitDirection ⁻¹' projectionGoodSet Q ρ p u P (sourceAngularWidth N sig J (i+1) u) T := by
  obtain ⟨N₀,hN₀⟩ := uniform_projection_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ p u hpu P hP i T
  apply sourceTestMask_support_transfer
  intro dir hdir dir' hdist
  change (projectionTestCount Q ρ p u P (sourceAngularWidth N sig J (i+1) u) (dir':Plane):ℝ) ≤ T
  exact (Nat.cast_le.mpr (hN₀ N hN Q hQ ρ p u hpu P hP i dir dir' (by simpa using hdist))).trans hdir

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SpatialAnchorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem ae_occupied_anchor (Q : DyadicSquare) (ρ : Measure Plane) (hcarry : ρ Q.carrierᶜ = 0) (n : ℕ) :
    ∀ᵐ x ∂ρ, ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier := by
  have hroot : ∀ᵐ x ∂ρ, x ∈ Q.carrier := ae_iff.mpr hcarry
  have hz : ∀ᵐ x ∂ρ, ∀ P : CellPath, ρ (Q.descendant P).carrier = 0 → x ∉ (Q.descendant P).carrier := by
    apply ae_all_iff.mpr
    intro P
    by_cases h : ρ (Q.descendant P).carrier = 0
    · filter_upwards [show ∀ᵐ x ∂ρ, x ∉ (Q.descendant P).carrier from by simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using h] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h' => (h h').elim)
  filter_upwards [hroot,hz] with x hx hzero
  obtain ⟨P,hP,hx⟩ := Q.mem_descendant_at_depth n hx
  refine ⟨P,Finset.mem_filter.mpr ⟨hP,?_⟩,hx⟩
  exact bot_lt_iff_ne_bot.mpr (fun he => hzero P he hx)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InteriorPolicy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem finiteArgmin_spec {S : Finset ℕ} (hS : S.Nonempty) (f : ℕ → ℝ) :
    finiteArgmin S f ∈ S ∧ ∀ j ∈ S, f (finiteArgmin S f) ≤ f j := by
  rw [finiteArgmin,dite_eq_left hS]
  have hs := Classical.choose_spec (Finset.exists_mem_eq_inf' hS f)
  refine ⟨hs.1,?_⟩
  intro j hj
  rw [← hs.2]
  exact Finset.inf'_le f hj

theorem policyBlock_nonempty {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    (policyBlock N q k).Nonempty := by
  apply Finset.nonempty_Ico.mpr
  have he : (k+1)*q = k*q+q := by ring
  omega

theorem policyRepresentative_spec (A : ℕ → ℝ) {N q k : ℕ} (hq : 0 < q) (hk : k*q ≤ N) :
    k*q ≤ policyRepresentative A N q k ∧ policyRepresentative A N q k < (k+1)*q ∧
      policyRepresentative A N q k ≤ N ∧
      ∀ n ∈ policyBlock N q k, A (policyRepresentative A N q k) ≤ A n := by
  have hh := finiteArgmin_spec (policyBlock_nonempty hq hk) A
  have hm := Finset.mem_Ico.mp hh.1
  refine ⟨hm.1,lt_of_lt_of_le hm.2 (min_le_left _ _),?_,hh.2⟩
  exact Nat.le_of_lt_succ (lt_of_lt_of_le hm.2 (min_le_right _ _))

theorem policyBlocks_mem {N q a t k : ℕ} (h : k ∈ policyBlocks N q a t) :
    k ≤ N/q ∧ a+q ≤ k*q ∧ (k+1)*q ≤ t-q+1 := by
  obtain ⟨hk,hl,hr⟩ := Finset.mem_filter.mp h
  exact ⟨Nat.le_of_lt_succ (Finset.mem_range.mp hk),hl,hr⟩

theorem policy_left_block {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    ∃ k ∈ policyBlocks N q a t, k*q ≤ a+2*q := by
  let k := (a+2*q-1)/q
  have hlo := Nat.div_mul_le_self (a+2*q-1) q
  have hhi := Nat.lt_mul_div_succ (a+2*q-1) hq
  have hprod : (k+1)*q = k*q+q := by ring
  change k*q ≤ a+2*q-1 at hlo
  have hceil : a+q ≤ k*q := by
    rw [Nat.mul_comm q] at hhi
    change a+2*q-1 < (k+1)*q at hhi
    omega
  have hend : (k+1)*q ≤ t-q+1 := by omega
  have hkn : k*q ≤ N := by omega
  refine ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_,hceil,hend⟩,by omega⟩
  exact Nat.lt_succ_of_le ((Nat.le_div_iff_mul_le hq).mpr hkn)

theorem policyBlocks_nonempty {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N) (hwide : a+100*q < t) :
    (policyBlocks N q a t).Nonempty := by
  obtain ⟨k,hk,_⟩ := policy_left_block hq ht hwide
  exact ⟨k,hk⟩

theorem policyDepth_interior (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    a+q ≤ policyDepth A N q a t ∧ policyDepth A N q a t ≤ t-q := by
  have hkey := (finiteArgmin_spec hne (fun k => A (policyRepresentative A N q k))).1
  have hb := policyBlocks_mem hkey
  have hrep := policyRepresentative_spec A hq ((Nat.le_div_iff_mul_le hq).mp hb.1)
  exact ⟨hb.2.1.trans hrep.1,Nat.le_of_lt_succ (hrep.2.1.trans_le hb.2.2)⟩

theorem policy_move_length (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    (hne : (policyBlocks N q a t).Nonempty) :
    let p := policyDepth A N q a t
    let l := min (p-a) (t-p)
    q ≤ l ∧ a ≤ p-l ∧ p+l ≤ t := by
  have hh := policyDepth_interior A hq hne
  dsimp only
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_PolicyDescriptors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem policyOrigins_mono {N q a a' t t' : ℕ} (ha : a ≤ a') (ht : t' ≤ t) :
    policyOrigins N q a' t' ⊆ policyOrigins N q a t := by
  intro z hz
  obtain ⟨hz,ha',ht',hwide⟩ := Finset.mem_filter.mp hz
  exact Finset.mem_filter.mpr ⟨hz,ha.trans ha',ht'.trans ht,hwide⟩

theorem policyDescriptorList_mono (A : ℕ → ℝ) {N q a a' t t' : ℕ}
    (ha : a ≤ a') (ht : t' ≤ t) :
    policyDescriptorList A N q a' t' ⊆ policyDescriptorList A N q a t := by
  intro d hd
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  exact Finset.mem_biUnion.mpr ⟨z,policyOrigins_mono ha ht hz,hd⟩

theorem originDescriptor_anchor (A : ℕ → ℝ) {N q b u : ℕ} {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) : descriptorAnchor d = policyDepth A N q b u := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    rfl
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d; rfl
    · simp at hd

theorem originDescriptor_length (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) {d : PolicyDescriptor}
    (hd : d ∈ originDescriptors A N q b u) :
    0 < descriptorLength d ∧ b ≤ descriptorAnchor d-descriptorLength d ∧
      descriptorAnchor d+descriptorLength d ≤ u := by
  have hne := policyBlocks_nonempty hq huN hwide
  have hp := policyDepth_interior A hq hne
  have hl := policy_move_length A hq hne
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,hg,rfl⟩ := Finset.mem_image.mp hd
    have hg := Finset.mem_Ico.mp hg
    dsimp only [descriptorLength,descriptorAnchor] at *
    omega
  · split_ifs at hd with h
    · have he := Finset.mem_singleton.mp hd
      subst d
      dsimp only [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_origin (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) :
    ∃ b u : ℕ, a ≤ b ∧ u ≤ t ∧ b+100*q < u ∧
      descriptorAnchor d = policyDepth A N q b u ∧ 0 < descriptorLength d ∧
      b ≤ descriptorAnchor d-descriptorLength d ∧ descriptorAnchor d+descriptorLength d ≤ u := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,hb,hu,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  exact ⟨z.1,z.2,hb,hu,hwide,originDescriptor_anchor A hd,
    originDescriptor_length A hq huN hwide hd⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem measurable_descriptorGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (P : CellPath) (b : PolicyDescriptor) :
    MeasurableSet (descriptorGoodSet Q ρ m N lam sig J i P b) := by
  cases b with
  | parallel g p => exact measurable_parallelGoodSet _ _ _ _ _ _ _
  | projection p u => exact measurable_projectionGoodSet _ _ _ _ _ _ _

theorem policyDescriptor_valid (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N)
    {b : PolicyDescriptor} (hb : b ∈ policyDescriptorList A N q a t) : ValidDescriptor N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,ValidDescriptor] at hpos hbound ⊢ <;> omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceGoodSet
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem measurable_endpointDescriptorGood (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (d : PolicyDescriptor) :
    MeasurableSet (endpointDescriptorGood Q ρ m N lam sig J i d) := by
  simp only [endpointDescriptorGood, ofPred_forall]
  apply MeasurableSet.iInter
  intro P
  apply MeasurableSet.iInter
  intro _
  exact ((Q.descendant P).measurable.preimage measurable_fst).himp
    ((measurable_descriptorGoodSet Q ρ m N lam sig J i P d).preimage measurable_snd)

theorem measurable_positiveDistanceGoodSet (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N q a t : ℕ) (lam sig : ℝ) (J i : ℕ) :
    MeasurableSet (positiveDistanceGoodSet Q ρ m N q a t lam sig J i) := by
  simp only [positiveDistanceGoodSet, ofPred_forall]
  apply Finset.measurableSet_biInter
  intro d _
  exact ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_fst.prodMk measurable_pairRadialUnit)).inter
    ((measurable_endpointDescriptorGood Q ρ m N lam sig J i d).preimage
    (measurable_snd.prodMk measurable_pairRadialUnit))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_InheritedSymbolSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem uniform_descriptorAngleMask_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Q : DyadicSquare, Q.side = 1 →
    ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ) (b : PolicyDescriptor),
    ValidDescriptor N b → ∀ (P : CellPath), P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b) →
    ∀ x ∈ (Q.descendant P).carrier,
    tsupport (descriptorAngleMask Q ρ m N lam sig J i b x) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_parallel_mask_support hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_projection_mask_support hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ m lam i b hb P hP x hx
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have he : descriptorAngleMask Q ρ m N lam sig J i b x =
      sourceTestMask (descriptorGoodSet Q ρ m N lam sig J i P b)
        (sourceAngularRadius N sig (descriptorLength b)) (sourceAngularRadius_pos _ _ _) := by
    funext θ
    exact (spatialAnchorMask_eq Q hQpos ρ _ _ _ _ hP hx _).trans (circleTestMask_comp _ _ _ _)
  rw [he]
  have hlen := (mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1
  cases b with
  | parallel g p => exact h₁ N ((le_max_left _ _).trans hN) Q ρ g p hb.1 P i _
  | projection p u => exact h₂ N ((le_max_right _ _).trans hN) Q hQ ρ p u hb.1 P hlen i _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

namespace PositiveDistanceData

theorem measurable_good (d : PositiveDistanceData) : MeasurableSet d.good :=
  measurable_positiveDistanceGoodSet _ _ _ _ _ _ _ _ _ _ _

theorem distance_prod (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] :
    d.distance.prod e.distance = Measure.map
      (fun z : (Plane × Plane) × (Plane × Plane) =>
        (dist z.1.1 z.1.2, dist z.2.1 z.2.2)) (d.pair.prod e.pair) :=
  Measure.map_prod_map _ _ (continuous_fst.dist continuous_snd).measurable
    (continuous_fst.dist continuous_snd).measurable

theorem distance_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (w : ℝ) :
    (d.distance.prod d.distance) {z : ℝ × ℝ | |z.1-z.2| ≤ w} =
      (d.pair.prod d.pair) {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ w} := by
  rw [distance_prod,Measure.map_apply (by fun_prop) (by measurability)]
  rfl

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceJetSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ComplexConjugate

theorem endpointDescriptorGood_of_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ)
    (d : PolicyDescriptor) (x : Plane) (dir : UnitCircle) (P : CellPath)
    (hP : P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor d))
    (hx : x ∈ (Q.descendant P).carrier)
    (hg : dir ∈ descriptorGoodSet Q ρ m N lam sig J i P d) :
    (x,dir) ∈ endpointDescriptorGood Q ρ m N lam sig J i d := by
  intro P' hP' hx'
  have hlen := (mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1
  have hlen' := (mem_dyadicPaths _ P').mp hP'
  have he : P' = P := by
    by_contra hne
    exact Set.disjoint_left.mp (Q.descendants_disjoint hQ (hlen'.trans hlen.symm) hne) hx' hx
  simpa only [he] using hg

theorem ae_all_occupied_pair (Q : DyadicSquare) (ρ : Measure Plane) [SFinite ρ]
    (hcarry : ρ Q.carrierᶜ = 0) :
    ∀ᵐ z ∂ρ.prod ρ, ∀ n : ℕ,
      (∃ P ∈ occupiedAnchorPaths Q ρ n, z.1 ∈ (Q.descendant P).carrier) ∧
      (∃ P ∈ occupiedAnchorPaths Q ρ n, z.2 ∈ (Q.descendant P).carrier) := by
  have ha : ∀ᵐ x ∂ρ, ∀ n : ℕ,
      ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor Q ρ hcarry n)
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae ha,
    Measure.quasiMeasurePreserving_snd.ae ha] with z hz₁ hz₂
  exact fun n => ⟨hz₁ n,hz₂ n⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceMasks
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

namespace PositiveDistanceData

theorem minimalMask_bounds (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (z : Plane × Plane) : 0 ≤ d.minimalMask z ∧ d.minimalMask z ≤ 1 := by
  have h₁ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.1 (sourceRadialUnit z.2 z.1)
  have h₂ := descriptorListMask_bounds d.Q hQ d.ρ d.mass d.N d.lam d.sig d.J d.i
    (policyDescriptorList (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)
    z.2 (sourceRadialUnit z.2 z.1)
  exact ⟨mul_nonneg h₁.1 h₂.1,
    (mul_le_mul_of_nonneg_right h₁.2 h₂.1).trans (by simpa only [one_mul] using h₂.2)⟩

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_SourceStrongSeparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem dyadic_strong_separation_endpoints (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {s : ℝ}
    (hp : P.side ≤ s) (hq : Q.side ≤ s)
    (hl : 100*s ≤ dist P.center Q.center) (hu : dist P.center Q.center ≤ 2000*s)
    {x y : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier) :
    96*s ≤ dist x y ∧ dist x y ≤ 2004*s := by
  have hx' := P.dist_le hP.le hx (P.center_mem hP)
  have hy' := Q.dist_le hQ.le hy (Q.center_mem hQ)
  have ht₁ := dist_triangle P.center x Q.center
  have ht₂ := dist_triangle x y Q.center
  have ht₃ := dist_triangle x P.center y
  have ht₄ := dist_triangle P.center Q.center y
  rw [dist_comm P.center x] at ht₁
  rw [dist_comm Q.center y] at ht₄
  constructor <;> linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_PositiveDistanceWeight
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem separated_distance_ratio (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) :
    96 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ∧
    dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ)) ≤ 2004 := by
  have h := dyadic_strong_separation_endpoints _ _
    (d.Q.descendant_side_pos hQ d.X) (d.Q.descendant_side_pos hQ d.Y)
    hs.1 hs.2.1 hs.2.2.1 hs.2.2.2 hx hy
  exact ⟨(le_div_iff₀ (by positivity)).mpr h.1,
    (div_le_iff₀ (by positivity)).mpr h.2⟩

theorem spatialWeight_le_one (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {z : Plane × Plane}
    (hx : z.1 ∈ (d.Q.descendant d.X).carrier)
    (hy : z.2 ∈ (d.Q.descendant d.Y).carrier) : d.spatialWeight z ≤ 1 := by
  have hr := d.separated_distance_ratio hQ hs hx hy
  have hpow := Real.rpow_le_one_of_one_le_of_nonpos (by linarith :
    1 ≤ dist z.1 z.2 / (2:ℝ)^(-(d.a:ℝ))) (by norm_num : -(1/2:ℝ) ≤ 0)
  exact (mul_le_of_le_one_left (d.minimalMask_bounds hQ z).1 hpow).trans
    (d.minimalMask_bounds hQ z).2

theorem ae_cellPair_mem (d : PositiveDistanceData) [SFinite d.ρ] :
    ∀ᵐ z ∂d.cellPair, z.1 ∈ (d.Q.descendant d.X).carrier ∧
      z.2 ∈ (d.Q.descendant d.Y).carrier := by
  exact (Measure.quasiMeasurePreserving_fst.ae
    (ae_restrict_mem (d.Q.descendant d.X).measurable)).and
    (Measure.quasiMeasurePreserving_snd.ae
      (ae_restrict_mem (d.Q.descendant d.Y).measurable))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_WeightedDistancePushforward
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weightedPair_le (d : PositiveDistanceData) [SFinite d.ρ] (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) :
    d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.cellPair := by
  rw [← withDensity_const]
  apply withDensity_mono
  filter_upwards [d.ae_cellPair_mem] with z hz
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_of_le_one_right (by positivity) (d.spatialWeight_le_one hQ hs hz.1 hz.2)

theorem weightedPair_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedPair := by
  constructor
  apply (Measure.le_iff.mp (d.weightedPair_le hQ hs) univ MeasurableSet.univ).trans_lt
  rw [Measure.smul_apply,smul_eq_mul]
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top _ _)

theorem weightedDistance_isFinite (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) : IsFiniteMeasure d.weightedDistance := by
  let := d.weightedPair_isFinite hQ hs
  unfold weightedDistance
  first | infer_instance | exact Measure.isProbabilityMeasure_map (by first | fun_prop | assumption | (apply Measurable.aemeasurable; solve_by_elim) | (apply Continuous.aemeasurable; solve_by_elim) | (apply MeasureTheory.MeasurePreserving.aemeasurable; solve_by_elim) | (apply MeasureTheory.Measure.QuasiMeasurePreserving.aemeasurable; solve_by_elim) | (apply Measurable.aemeasurable; measurability) | measurability)

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_WeightedDistanceNestedSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_weighted_distance_nested_support {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ], N₀ ≤ d.N → d.sig = sig → d.J = J →
      d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, ∀ᵐ z ∂d.cellPair, d.spatialWeight z ≠ 0 →
        z ∈ ({d with t := v, i := d.i+1} : PositiveDistanceData).good := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorAngleMask_support hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hcarry hq ht v hv
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have ha : ∀ᵐ z ∂d.cellPair, ∀ n : ℕ,
      (∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, z.1 ∈ (d.Q.descendant P).carrier) ∧
      (∃ P ∈ occupiedAnchorPaths d.Q d.ρ n, z.2 ∈ (d.Q.descendant P).carrier) :=
    (ae_mono (Measure.prod_mono (μ' := d.ρ) (ν' := d.ρ)
      Measure.restrict_le_self Measure.restrict_le_self)) (ae_all_occupied_pair d.Q d.ρ hcarry)
  filter_upwards [ha] with z hz hn
  have hm : d.minimalMask z ≠ 0 := (mul_ne_zero_iff.mp hn).2
  have hm₁ := (mul_ne_zero_iff.mp hm).1
  have hm₂ := (mul_ne_zero_iff.mp hm).2
  intro b hb
  have hb' := policyDescriptorList_mono (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) (le_refl d.a) hv hb
  have hvalid := policyDescriptor_valid _ hq ht hb'
  have hmask (x : Plane)
      (hx : ∃ P ∈ occupiedAnchorPaths d.Q d.ρ (descriptorAnchor b), x ∈ (d.Q.descendant P).carrier)
      (hmx : descriptorSpatialMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b x
        (sourceRadialUnit z.2 z.1) ≠ 0) :
      (x,sourceRadialUnit z.2 z.1) ∈ endpointDescriptorGood
        d.Q d.ρ d.mass d.N d.lam d.sig d.J (d.i+1) b := by
    obtain ⟨P,hP,hx⟩ := hx
    apply endpointDescriptorGood_of_occupied d.Q hQpos d.ρ d.mass d.N d.lam d.sig d.J
      (d.i+1) b x _ P hP hx
    have hh := h₀ d.N hN d.Q hQ d.ρ d.mass d.lam d.i b hvalid P hP x hx
    rw [← hsig',← hJ'] at hh
    have hmem : sourceAngle (sourceRadialUnit z.2 z.1) ∈
        tsupport (descriptorAngleMask d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i b x) := by
      apply subset_tsupport
      simpa only [Function.mem_support,descriptorAngleMask,sourceUnitDirection_sourceAngle] using hmx
    simpa only [mem_preimage,sourceUnitDirection_sourceAngle] using hh hmem
  exact ⟨hmask z.1 (hz _).1 (Finset.prod_ne_zero_iff.mp hm₁ b hb'),
    hmask z.2 (hz _).2 (Finset.prod_ne_zero_iff.mp hm₂ b hb')⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_WeightedDistanceNestedDomination
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem weightedDistance_le_nested (d : PositiveDistanceData) [SFinite d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (v : ℕ)
    (hgood : ∀ᵐ z ∂d.cellPair, d.spatialWeight z ≠ 0 →
      z ∈ ({d with t := v,i := d.i+1} : PositiveDistanceData).good) :
    d.weightedDistance ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) •
      ({d with t := v,i := d.i+1} : PositiveDistanceData).distance := by
  let e : PositiveDistanceData := {d with t := v,i := d.i+1}
  have hp : d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • e.pair := by
    change d.weightedPair ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.cellPair.restrict e.good
    rw [← withDensity_const,← withDensity_indicator e.measurable_good]
    apply withDensity_mono
    filter_upwards [d.ae_cellPair_mem,hgood] with z hz hg
    by_cases hw : d.spatialWeight z = 0
    · simp only [hw,mul_zero,ENNReal.ofReal_zero]
      exact zero_le
    · rw [Set.indicator_of_mem (hg hw)]
      exact ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (by positivity)
        (d.spatialWeight_le_one hQ hs hz.1 hz.2))
  have h := Measure.map_mono hp (continuous_fst.dist continuous_snd).measurable
  simpa only [weightedDistance,distance,
    Measure.map_smul] using h

end PositiveDistanceData

theorem uniform_weighted_distance_nested_domination {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, d.weightedDistance ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) •
        ({d with t := v,i := d.i+1} : PositiveDistanceData).distance := by
  obtain ⟨N₀,h₀⟩ := uniform_weighted_distance_nested_support hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hs hcarry hq ht v hv
  exact d.weightedDistance_le_nested (hQ.symm ▸ zero_lt_one) hs v
    (h₀ d hN hsig' hJ' hQ hcarry hq ht v hv)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFourierDifference
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory ComplexConjugate

theorem integral_distanceDifferenceMeasure (μ : Measure ℝ) (F : ℝ → ℂ)
    (hF : StronglyMeasurable F) :
    (∫ s, F s ∂distanceDifferenceMeasure μ) = ∫ z, F (z.1-z.2) ∂μ.prod μ :=
  integral_map_of_stronglyMeasurable (by fun_prop) hF

theorem charFun_distanceDifferenceMeasure (μ : Measure ℝ) [IsFiniteMeasure μ] (r : ℝ) :
    charFun (distanceDifferenceMeasure μ) r = (‖charFun μ r‖^2:ℂ) := by
  rw [charFun_apply_real,integral_distanceDifferenceMeasure μ _ (by fun_prop)]
  have he : (fun z : ℝ × ℝ => Complex.exp ((r*(z.1-z.2):ℝ)*Complex.I)) =
      fun z => Complex.exp ((r*z.1:ℝ)*Complex.I) *
        conj (Complex.exp ((r*z.2:ℝ)*Complex.I)) := by
    funext z
    rw [← Complex.exp_conj,← Complex.exp_add]
    congr 1
    simp only [map_mul,Complex.conj_ofReal,Complex.conj_I,Complex.ofReal_sub,Complex.ofReal_mul]
    ring
  simp only [Complex.ofReal_mul] at he
  rw [he,integral_prod_mul (fun x : ℝ => Complex.exp ((r:ℂ)*x*Complex.I))
    (fun y : ℝ => conj (Complex.exp ((r:ℂ)*y*Complex.I))),integral_conj,← charFun_apply_real,Complex.mul_conj]
  exact_mod_cast Complex.normSq_eq_norm_sq (charFun μ r)

theorem integral_charFun_scale_swap (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    (∫ s, charFun μ (A*s) ∂ν) = ∫ r, charFun ν (A*r) ∂μ := by
  simp only [charFun_apply_real]
  rw [integral_integral_swap]
  · apply integral_congr_ae
    filter_upwards with r
    apply integral_congr_ae
    filter_upwards with s
    congr 2
    push_cast
    ring
  · exact (integrable_const (1:ℝ)).mono (by fun_prop)
      (by filter_upwards with z; simp [Function.uncurry,Complex.norm_exp])

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem distanceSincKernel_nonneg (u s : ℝ) : 0 ≤ distanceSincKernel u s := sq_nonneg _

theorem distanceSincKernel_le_one (u s : ℝ) : distanceSincKernel u s ≤ 1 := by
  have h := Real.abs_sinc_le_one (u*s)
  dsimp [distanceSincKernel]
  exact (sq_abs _).symm.trans_le ((pow_le_pow_left₀ (abs_nonneg _) h 2).trans_eq (by norm_num))

theorem continuous_distanceSincKernel (u : ℝ) : Continuous (distanceSincKernel u) :=
  (Real.continuous_sinc.comp (continuous_const.mul continuous_id)).pow 2

theorem interval_exp_eq_sinc (u s : ℝ) :
    (∫ r in -u..u, Complex.exp ((r*s:ℝ)*Complex.I)) =
      ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  by_cases hs : s = 0
  · simp [hs]
    ring
  have h := intervalIntegral.integral_comp_mul_right
    (fun t : ℝ => Complex.exp (t*Complex.I)) (a := -u) (b := u) hs
  rw [neg_mul,integral_exp_mul_I_eq_sinc] at h
  rw [h]
  simp only [Complex.real_smul,Complex.ofReal_inv,Complex.ofReal_mul,
    Complex.ofReal_ofNat]
  have hs' : (s:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFrequencyBox
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_mass {u : ℝ} (hu : 0 ≤ u) :
    distanceFrequencyBox u univ = ENNReal.ofReal (2*u) := by
  simp only [distanceFrequencyBox,Measure.restrict_apply_univ,Real.volume_Ioc]
  apply (ENNReal.ofReal_eq_ofReal_iff (sub_nonneg.mpr (neg_le_self hu))
    (mul_nonneg (by norm_num) hu)).2
  ring

theorem distanceFrequencyBox_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceFrequencyBox u) s = ((2*u*Real.sinc (u*s):ℝ):ℂ) := by
  rw [charFun_apply_real]
  change (∫ r in Ioc (-u) u, Complex.exp ((s:ℂ)*r*Complex.I)) = _
  rw [← intervalIntegral.integral_of_le (by linarith : -u ≤ u)]
  simpa only [Complex.ofReal_mul,mul_comm (s:ℂ)] using interval_exp_eq_sinc u s

theorem distanceFrequencyBox_difference_charFun {u : ℝ} (hu : 0 ≤ u) (s : ℝ) :
    charFun (distanceDifferenceMeasure (distanceFrequencyBox u)) s =
      (((2*u)^2 * distanceSincKernel u s:ℝ):ℂ) := by
  rw [charFun_distanceDifferenceMeasure,distanceFrequencyBox_charFun hu,
    Complex.norm_real,Real.norm_eq_abs,← Complex.ofReal_pow,sq_abs]
  congr 1
  dsimp [distanceSincKernel]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincSpectralIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem charFun_sq_integrable_finite (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (A : ℝ) :
    Integrable (fun r => ‖charFun μ (A*r)‖^2) ν := by
  apply (integrable_const ((μ.real univ)^2)).mono
  · exact ((measurable_charFun.comp (measurable_const.mul measurable_id)).norm.pow_const 2).aestronglyMeasurable
  · filter_upwards with r
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_charFun_le _) 2

theorem distanceSincKernel_spectral_identity (μ : Measure ℝ) [IsFiniteMeasure μ]
    {u : ℝ} (hu : 0 ≤ u) (A : ℝ) :
    (2*u)^2 * (∫ s, distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
  have h := integral_charFun_scale_swap
    (distanceDifferenceMeasure (distanceFrequencyBox u)) (distanceDifferenceMeasure μ) A
  simp only [distanceFrequencyBox_difference_charFun hu,charFun_distanceDifferenceMeasure] at h
  have hr : (∫ s, (2*u)^2 * distanceSincKernel u (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ r, ‖charFun μ (A*r)‖^2 ∂distanceDifferenceMeasure (distanceFrequencyBox u) := by
    apply Complex.ofReal_injective
    simpa only [← Complex.ofReal_pow,integral_complex_ofReal] using h
  rwa [integral_const_mul] at hr

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceFrequencyMajorant
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceFrequencyBox_two_lower :
    (2:ℝ≥0∞) • volume.restrict (Icc (-1:ℝ) 1) ≤
      distanceDifferenceMeasure (distanceFrequencyBox 2) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [distanceDifferenceMeasure,Measure.map_apply (by fun_prop) hS,
    Measure.prod_apply (hS.preimage (by fun_prop))]
  have hsub : distanceFrequencyBox 1 ≤ distanceFrequencyBox 2 :=
    Measure.restrict_mono (Ioc_subset_Ioc (by norm_num) (by norm_num)) le_rfl
  calc
    _ = ∫⁻ _x, volume (S ∩ Icc (-1:ℝ) 1) ∂distanceFrequencyBox 1 := by
      rw [lintegral_const,distanceFrequencyBox_mass (by norm_num),
        Measure.smul_apply,Measure.restrict_apply hS,smul_eq_mul]
      norm_num
      exact mul_comm _ _
    _ ≤ ∫⁻ x, distanceFrequencyBox 2 ((fun y : ℝ => x-y) ⁻¹' S) ∂distanceFrequencyBox 1 := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioc] with x hx
      rw [distanceFrequencyBox,Measure.restrict_apply (hS.preimage (by fun_prop))]
      rw [← (volume.measurePreserving_sub_left x).measure_preimage
        (hS.inter measurableSet_Icc).nullMeasurableSet]
      apply measure_mono
      intro y hy
      refine ⟨hy.1,?_,?_⟩ <;> dsimp at * <;> linarith [hy.2.1,hy.2.2,hx.1,hx.2]
    _ ≤ _ := lintegral_mono' hsub (fun _ => le_rfl)

theorem distanceSincKernel_two_decay (s : ℝ) :
    distanceSincKernel 2 s ≤ 4/(1+|s|)^2 := by
  have hden : 0 < (1+|s|)^2 := by positivity
  apply (le_div_iff₀ hden).mpr
  by_cases hs : |s| ≤ 1
  · have h := distanceSincKernel_le_one 2 s
    have hn := distanceSincKernel_nonneg 2 s
    nlinarith [abs_nonneg s,mul_le_mul_of_nonneg_right h (sq_nonneg (1+|s|))]
  · have hs' : 1 < |s| := lt_of_not_ge hs
    have hn : s ≠ 0 := by intro h; norm_num [h] at hs'
    have he : distanceSincKernel 2 s * (2*s)^2 = (Real.sin (2*s))^2 := by
      rw [distanceSincKernel,Real.sinc_of_ne_zero (mul_ne_zero (by norm_num) hn),div_pow]
      field_simp
    have hb : (Real.sin (2*s))^2 ≤ 1 := by
      have h := pow_le_pow_left₀ (abs_nonneg _) (Real.abs_sin_le_one (2*s)) 2
      simpa only [sq_abs,one_pow] using h
    have hn' := distanceSincKernel_nonneg 2 s
    have hsq : (1+|s|)^2 ≤ 4*s^2 := by nlinarith [sq_abs s]
    have hm := mul_le_mul_of_nonneg_left hsq hn'
    nlinarith

theorem frequency_band_le_sinc (μ : Measure ℝ) [IsFiniteMeasure μ] (A : ℝ) :
    (∫ r in Icc (-1:ℝ) 1, ‖charFun μ (A*r)‖^2) ≤
      8 * ∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ := by
  have hi := charFun_sq_integrable_finite μ (distanceDifferenceMeasure (distanceFrequencyBox 2)) A
  have h := integral_mono_measure distanceFrequencyBox_two_lower
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖charFun μ (A*r)‖)) hi
  rw [integral_smul_measure,smul_eq_mul,ENNReal.toReal_ofNat,
    ← distanceSincKernel_spectral_identity μ (by norm_num : (0:ℝ) ≤ 2) A] at h
  norm_num at h
  linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceSincCollision
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem integral_scale_Icc (f : ℝ → ℝ) {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) :
    A * (∫ r in Icc (-u) u, f (A*r)) = ∫ r in Icc (-A*u) (A*u), f r := by
  rw [integral_Icc_eq_integral_Ioc,integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : -u ≤ u),
    ← intervalIntegral.integral_of_le (by nlinarith : -A*u ≤ A*u)]
  have h := intervalIntegral.smul_integral_comp_mul_left f (a := -u) (b := u) A
  simpa only [smul_eq_mul,mul_neg,neg_mul] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_DistanceBandKernelBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem distanceBandKernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 ≤ A) :
    Integrable (fun z : ℝ × ℝ => 1/(1+A*|z.1-z.2|)^2) (μ.prod μ) := by
  apply (integrable_const (1:ℝ)).mono (by apply Measurable.aestronglyMeasurable; fun_prop)
  filter_upwards with z
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity),norm_one]
  apply (div_le_one (by positivity : 0 < (1+A*|z.1-z.2|)^2)).mpr
  nlinarith [mul_nonneg hA (abs_nonneg (z.1-z.2))]

theorem distance_band_kernel_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      32*A * ∫ z : ℝ × ℝ, 1/(1+A*|z.1-z.2|)^2 ∂μ.prod μ := by
  have h := mul_le_mul_of_nonneg_left (frequency_band_le_sinc μ A) hA.le
  rw [integral_scale_Icc (fun r => ‖charFun μ r‖^2) hA (by norm_num : (0:ℝ) ≤ 1)] at h
  simp only [mul_one] at h
  have he : (∫ s, distanceSincKernel 2 (A*s) ∂distanceDifferenceMeasure μ) =
      ∫ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ∂μ.prod μ :=
    integral_map_of_stronglyMeasurable (by fun_prop)
      (((continuous_distanceSincKernel 2).comp (continuous_const.mul continuous_id)).stronglyMeasurable)
  rw [he] at h
  have hi : Integrable (fun z : ℝ × ℝ => distanceSincKernel 2 (A*(z.1-z.2))) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono (by
      exact ((continuous_distanceSincKernel 2).comp
        (continuous_const.mul (continuous_fst.sub continuous_snd))).aestronglyMeasurable)
    filter_upwards with z
    rw [Real.norm_eq_abs,abs_of_nonneg (distanceSincKernel_nonneg _ _),norm_one]
    exact distanceSincKernel_le_one _ _
  have hk := integral_mono hi ((distanceBandKernel_integrable μ hA.le).const_mul 4)
    (show ∀ z : ℝ × ℝ, distanceSincKernel 2 (A*(z.1-z.2)) ≤
      4*(1/(1+A*|z.1-z.2|)^2) from by
      intro z
      simpa only [abs_mul,abs_of_pos hA,mul_one_div] using
        distanceSincKernel_two_decay (A*(z.1-z.2)))
  rw [integral_const_mul] at hk
  have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ A*8 by positivity)
  nlinarith

theorem distance_band_kernel_bound_ennreal (μ : Measure ℝ) [IsFiniteMeasure μ]
    {A : ℝ} (hA : 0 < A) :
    ENNReal.ofReal (∫ r in Icc (-A) A, ‖charFun μ r‖^2) ≤
      ENNReal.ofReal (32*A) *
        ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+A*|z.1-z.2|)^2) ∂μ.prod μ := by
  have h := ENNReal.ofReal_le_ofReal (distance_band_kernel_bound μ hA)
  rw [ENNReal.ofReal_mul (by positivity),ofReal_integral_eq_lintegral_ofReal
    (distanceBandKernel_integrable μ hA.le) (Filter.Eventually.of_forall (fun _ => by positivity))] at h
  exact h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_Bins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem diagonal_bin_mass_le {ι : Type*} [Countable ι]
    (μ : Measure ℝ) [IsFiniteMeasure μ] (I : ι → Set ℝ)
    (hmeas : ∀ i, MeasurableSet (I i))
    (hdisj : Pairwise fun i j => Disjoint (I i) (I j)) (w : ℝ)
    (hdiam : ∀ i x, x ∈ I i → ∀ y, y ∈ I i → |x-y| ≤ w) :
    (∑' i, (μ (I i))^2) ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
  have hd : Pairwise fun i j => Disjoint (I i ×ˢ I i) (I j ×ˢ I j) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hi hj
    exact Set.disjoint_left.mp (hdisj hij) hi.1 hj.1
  calc
    (∑' i, (μ (I i))^2) = ∑' i, (μ.prod μ) (I i ×ˢ I i) := by
      simp only [Measure.prod_prod, pow_two]
    _ = (μ.prod μ) (⋃ i, I i ×ˢ I i) :=
      (measure_iUnion hd (fun i => (hmeas i).prod (hmeas i))).symm
    _ ≤ (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} := by
      apply measure_mono
      intro z hz
      obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hz
      exact hdiam i z.1 hi.1 z.2 hi.2

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_disjoint {w : ℝ} (hw : 0 < w) :
    Pairwise fun i j => Disjoint (realBin w i) (realBin w j) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with h | h
  · have hc : ((i+1 : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast (show i+1 ≤ j by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxj.1.trans' hm)) hxi.2
  · have hc : ((j+1 : ℤ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast (show j+1 ≤ i by omega)
    have hm := mul_le_mul_of_nonneg_right hc hw.le
    exact (not_lt_of_ge (hxi.1.trans' hm)) hxj.2

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

theorem real_bin_collision_bound (μ : Measure ℝ) [IsFiniteMeasure μ]
    {w : ℝ} (hw : 0 < w) :
    (∑' j : ℤ, (μ (realBin w j))^2) ≤
      (μ.prod μ) {z : ℝ × ℝ | |z.1-z.2| ≤ w} :=
  diagonal_bin_mass_le μ (realBin w) (realBin_measurable w) (realBin_disjoint hw) w
    (fun j _ hx _ hy => realBin_diameter w j hx hy)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinOffsets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem ennreal_offset_cauchy (a b : ℤ → ℝ≥0∞) (h : ℤ) :
    (∑' j : ℤ, a j*b (j-h)) ≤
      (∑' j : ℤ, (a j)^2)^(1/2 : ℝ) * (∑' j : ℤ, (b j)^2)^(1/2 : ℝ) := by
  have hpq : (2:ℝ).HolderConjugate 2 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq (Measure.count : Measure ℤ) hpq
    (measurable_of_countable a).aemeasurable
    (measurable_of_countable (fun j => b (j-h))).aemeasurable
  simp only [lintegral_count, ENNReal.rpow_two] at hh
  have he : (∑' j : ℤ, (b (j-h))^2) = ∑' j : ℤ, (b j)^2 :=
    (Equiv.subRight h).tsum_eq (fun j => (b j)^2)
  simpa only [one_div, he, Pi.mul_apply] using hh

 theorem realBin_cover {w : ℝ} (hw : 0 < w) (x : ℝ) :
    x ∈ realBin w ⌊x/w⌋ := by
  constructor
  · exact (le_div_iff₀ hw).mp (Int.floor_le (x/w))
  · simpa only [Int.cast_add,Int.cast_one] using
      (div_lt_iff₀ hw).mp (Int.lt_floor_add_one (x/w))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_BinKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem half_le_abs_int_add_half (h : ℤ) : (1/2:ℝ) ≤ |(h:ℝ)+1/2| := by
  by_cases hh : 0 ≤ h
  · have hr : (0:ℝ) ≤ h := by exact_mod_cast hh
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have hr : (h:ℝ) ≤ -1 := by exact_mod_cast (show h ≤ -1 by omega)
    rw [abs_of_nonpos (by linarith)]
    linarith

 theorem realBin_kernel_bound {w x y : ℝ} (hw : 0 < w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    1/(1+|x-y|/w)^2 ≤ 4/(((i-j:ℤ):ℝ)+1/2)^2 := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hd : |(((i-j:ℤ):ℝ)+1/2)| ≤ 2*(1+|x-y|/w) := by
    rw [abs_le]
    have h1 := neg_abs_le ((x-y)/w)
    have h2 := le_abs_self ((x-y)/w)
    rw [abs_div,abs_of_pos hw,sub_div] at h1 h2
    simp only [Int.cast_sub]
    constructor <;> linarith [div_nonneg (abs_nonneg (x-y)) hw.le]
  have hpos : 0 < 1+|x-y|/w := by positivity
  have hh := half_le_abs_int_add_half (i-j)
  have hsq : 0 < ((((i-j:ℤ):ℝ)+1/2)^2) := by
    nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2))]
  apply (div_le_div_iff₀ (sq_pos_of_pos hpos) hsq).mpr
  nlinarith [sq_abs ((((i-j:ℤ):ℝ)+1/2)), sq_nonneg (2*(1+|x-y|/w)-|(((i-j:ℤ):ℝ)+1/2)|)]

 theorem binKernelConstant_ne_top : binKernelConstant ≠ ∞ := by
  have hs := (Real.summable_one_div_int_add_rpow (1/2) 2).mpr (by norm_num)
  have ht : Summable (fun h : ℤ => 4/((h:ℝ)+1/2)^2) := by
    simpa only [Real.rpow_two,sq_abs,mul_one_div] using hs.mul_left 4
  exact ht.tsum_ofReal_ne_top

 theorem weighted_offset_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (c : ℤ → ℝ≥0∞) :
    (∫⁻ z : ℝ × ℝ, ∑' h : ℤ, ∑' j : ℤ,
      (realBin w j ×ˢ realBin w (j-h)).indicator (fun _ => c h) z ∂μ.prod ν) ≤
      (∑' h : ℤ, c h) * (binL2Norm μ w * binL2Norm ν w) := by
  have hm (h j : ℤ) : Measurable ((realBin w j ×ˢ realBin w (j-h)).indicator
      (fun _ : ℝ × ℝ => c h)) :=
    measurable_const.indicator ((realBin_measurable w j).prod (realBin_measurable w (j-h)))
  rw [lintegral_tsum (fun h => (Measurable.tsum (fun j => hm h j)).aemeasurable)]
  simp_rw [lintegral_tsum (fun j => (hm _ j).aemeasurable)]
  simp_rw [lintegral_indicator_const ((realBin_measurable w _).prod (realBin_measurable w _)),
    Measure.prod_prod, ENNReal.tsum_mul_left]
  calc
    _ ≤ ∑' h : ℤ, c h * (binL2Norm μ w * binL2Norm ν w) := by
      apply ENNReal.tsum_le_tsum
      intro h
      exact mul_le_mul_right (ennreal_offset_cauchy (fun j => μ (realBin w j))
        (fun j => ν (realBin w j)) h) (c h)
    _ = _ := ENNReal.tsum_mul_right

 theorem real_bin_decaying_kernel_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/w)^2) ∂μ.prod ν) ≤
      binKernelConstant * (binL2Norm μ w * binL2Norm ν w) := by
  apply le_trans (lintegral_mono (fun z => ?_))
    (weighted_offset_kernel_bound μ ν w binKernelWeight)
  let i : ℤ := ⌊z.1/w⌋
  let j : ℤ := ⌊z.2/w⌋
  have hi := realBin_cover hw z.1
  have hj := realBin_cover hw z.2
  have he : i-(i-j)=j := by omega
  have hz : z ∈ realBin w i ×ˢ realBin w (i-(i-j)) := ⟨hi,by simpa only [he] using hj⟩
  calc
    _ ≤ binKernelWeight (i-j) := ENNReal.ofReal_le_ofReal (realBin_kernel_bound hw hi hj)
    _ = (realBin w i ×ˢ realBin w (i-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z := (indicator_of_mem hz (fun _ : ℝ × ℝ => binKernelWeight (i-j))).symm
    _ ≤ ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-(i-j))).indicator
        (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z :=
      ENNReal.le_tsum (f := fun index : ℤ =>
        (realBin w index ×ˢ realBin w (index-(i-j))).indicator
          (fun _ : ℝ × ℝ => binKernelWeight (i-j)) z) i
    _ ≤ ∑' h : ℤ, ∑' k : ℤ, (realBin w k ×ˢ realBin w (k-h)).indicator
        (fun _ : ℝ × ℝ => binKernelWeight h) z :=
      ENNReal.le_tsum (f := fun offset : ℤ => ∑' index : ℤ,
        (realBin w index ×ˢ realBin w (index-offset)).indicator
          (fun _ : ℝ × ℝ => binKernelWeight offset) z) (i-j)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem binL2Norm_mul_self (μ : Measure ℝ) (w : ℝ) :
    binL2Norm μ w * binL2Norm μ w = ∑' j : ℤ, (μ (realBin w j))^2 := by
  unfold binL2Norm
  rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
  norm_num

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_PositiveDistanceBins
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_pos (d : PositiveDistanceData) : 0 < d.width := by
  unfold width; positivity

theorem levelMass_pos (d : PositiveDistanceData) : 0 < d.levelMass := by
  unfold levelMass; positivity

theorem normalization_pos (d : PositiveDistanceData) : 0 < d.normalization := by
  apply ENNReal.ofReal_pos.mpr
  exact div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)

theorem normalization_ne_top (d : PositiveDistanceData) : d.normalization ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem normalization_inv (d : PositiveDistanceData) :
    d.normalization⁻¹ = ENNReal.ofReal
      (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) := by
  rw [normalization,← ENNReal.ofReal_inv_of_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) (pow_pos d.levelMass_pos _)),
    inv_div,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_eq_mul_inv]

theorem coincidence_ne_top (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≠ ∞ :=
  ENNReal.mul_ne_top d.normalization_ne_top (measure_ne_top _ _)

theorem unnormalized_coincidence (d : PositiveDistanceData) :
    d.normalization⁻¹ * d.coincidence =
      (d.pair.prod d.pair)
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width} := by
  rw [coincidence,← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt d.normalization_pos) d.normalization_ne_top,one_mul]

theorem bin_norm_sq_le_coincidence (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width * binL2Norm d.distance d.width ≤
      ENNReal.ofReal (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) * d.coincidence := by
  rw [← d.normalization_inv,d.unnormalized_coincidence,binL2Norm_mul_self]
  apply (real_bin_collision_bound d.distance d.width_pos).trans
  rw [d.distance_collision]
  apply measure_mono
  intro z hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ d.width at hz
  change |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width
  exact hz.trans (by nlinarith [d.width_pos])

theorem bin_norm_le_coincidence_sqrt (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    binL2Norm d.distance d.width ≤
      (d.normalization⁻¹ * d.coincidence)^(1/2:ℝ) := by
  have h := d.bin_norm_sq_le_coincidence
  rw [← d.normalization_inv] at h
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ] (ht : d.t = e.t) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ((d.normalization⁻¹*d.coincidence)^(1/2:ℝ) *
        (e.normalization⁻¹*e.coincidence)^(1/2:ℝ)) := by
  have hw : d.width = e.width := by simp only [width,ht]
  apply (real_bin_decaying_kernel_bound d.distance e.distance d.width_pos).trans
  apply mul_le_mul_right
  exact mul_le_mul' d.bin_norm_le_coincidence_sqrt (hw ▸ e.bin_norm_le_coincidence_sqrt)

theorem common_profile_distance_kernel_bound (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        (d.coincidence*e.coincidence)^(1/2:ℝ) := by
  have h := distance_kernel_bound d e ht
  rw [← hn] at h
  simp only [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0:ℝ) ≤ 1/2)] at h ⊢
  have he (x : ℝ≥0∞) : x^(1/2:ℝ)*x^(1/2:ℝ) = x := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  have hr (x y z : ℝ≥0∞) : (x*y)*(x*z) = (x*x)*(y*z) := by ring
  rw [hr,he,d.normalization_inv] at h
  simpa only [mul_assoc] using h

theorem common_profile_distance_kernel_max (d e : PositiveDistanceData)
    [IsFiniteMeasure d.ρ] [IsFiniteMeasure e.ρ]
    (ht : d.t = e.t) (hn : d.normalization = e.normalization) :
    (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+|z.1-z.2|/d.width)^2)
      ∂d.distance.prod e.distance) ≤
      binKernelConstant * ENNReal.ofReal
        (d.levelMass^4 * (2:ℝ)^(-((d.t:ℝ)-d.a))) *
        max d.coincidence e.coincidence := by
  apply (common_profile_distance_kernel_bound d e ht hn).trans
  apply mul_le_mul_right
  have h := ENNReal.rpow_le_rpow (mul_le_mul'
    (le_max_left d.coincidence e.coincidence) (le_max_right d.coincidence e.coincidence))
    (by norm_num : (0:ℝ) ≤ 1/2)
  rw [← pow_two,← ENNReal.rpow_two,← ENNReal.rpow_mul] at h
  norm_num at h
  simpa only [le_max_iff] using h

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_PositiveDistanceSpatialKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem width_kernel (d : PositiveDistanceData) (z : ℝ × ℝ) :
    1/(1+|z.1-z.2|/d.width)^2 = 1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2 := by
  simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
    Real.rpow_natCast,div_eq_mul_inv,inv_inv,mul_comm]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_WeightedDistancePositiveKernel
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem normalized_weight_kernel_factor (d : PositiveDistanceData) :
    ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
      ENNReal.ofReal (d.levelMass^(-2:ℤ)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)) *
      ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) = 1 := by
  have he : (2:ℝ)^((d.t:ℝ)-d.a) * d.levelMass^(-2:ℤ) * d.levelMass^(-2:ℤ) *
      (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) = 1 := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2)]
    norm_num only [zpow_neg,zpow_ofNat]
    have hm := d.levelMass_pos.ne'
    have hp : (2:ℝ)^((d.t:ℝ)-d.a) ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) _).ne'
    field_simp
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity),he,ENNReal.ofReal_one]

theorem normalized_dominated_distance_kernel (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.distance) :
    ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
      (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2) ∂μ.prod μ) ≤
        binKernelConstant * d.coincidence := by
  let F : ℝ × ℝ → ℝ≥0∞ := fun z => ENNReal.ofReal (1/(1+(2:ℝ)^d.t*|z.1-z.2|)^2)
  have hp := Measure.prod_mono hμ hμ
  rw [Measure.prod_smul_left,Measure.prod_smul_right,smul_smul] at hp
  have h := lintegral_mono' hp (fun z => le_refl (F z))
  rw [lintegral_smul_measure] at h
  have hb := d.common_profile_distance_kernel_max d rfl rfl
  simp only [max_self] at hb
  simp_rw [d.width_kernel] at hb
  have h₁ := mul_le_mul_right h (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)))
  have h₂ := mul_le_mul_right hb (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) *
    ENNReal.ofReal (d.levelMass^(-2:ℤ)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)))
  have hh : ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) * (∫⁻ z, F z ∂μ.prod μ) ≤
      (ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) * ENNReal.ofReal (d.levelMass^(-2:ℤ)) *
        ENNReal.ofReal (d.levelMass^(-2:ℤ))) *
      (binKernelConstant * ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((d.t:ℝ)-d.a))) * d.coincidence) := by
    apply le_trans ?_ h₂
    simpa only [smul_eq_mul,mul_assoc,F] using h₁
  have he (a b c k l D : ℝ≥0∞) : (a*b*c)*(k*l*D) = (a*b*c*l)*(k*D) := by ring
  rw [he,d.normalized_weight_kernel_factor,one_mul] at hh
  exact hh

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_ActualDistanceLowBand
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem dominated_distance_band (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : μ ≤ ENNReal.ofReal (d.levelMass^(-2:ℤ)) • d.distance) :
    (2:ℝ)^(-(d.a:ℝ)) *
      (∫ r in Icc (-((2:ℝ)^d.t)) ((2:ℝ)^d.t), ‖charFun μ r‖^2) ≤
        (32*binKernelConstant.toReal) * d.coincidence.toReal := by
  have h := mul_le_mul_right (distance_band_kernel_bound_ennreal μ
    (by positivity : 0 < (2:ℝ)^d.t)) (ENNReal.ofReal ((2:ℝ)^(-(d.a:ℝ))))
  have hkernel := mul_le_mul_right (d.normalized_dominated_distance_kernel μ hμ) (32:ℝ≥0∞)
  have he : (2:ℝ)^(-(d.a:ℝ))*(32*(2:ℝ)^d.t) = 32*(2:ℝ)^((d.t:ℝ)-d.a) := by
    rw [mul_left_comm,← Real.rpow_natCast,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    congr 2
    ring
  have hc : ENNReal.ofReal ((2:ℝ)^(-(d.a:ℝ))) * ENNReal.ofReal (32*(2:ℝ)^d.t) =
      32*ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)) := by
    rw [← ENNReal.ofReal_mul (by positivity),he,ENNReal.ofReal_mul (by norm_num)]
    norm_num
  rw [← mul_assoc,hc,mul_assoc] at h
  have hh := h.trans hkernel
  have hr := ENNReal.toReal_mono
    (ENNReal.mul_ne_top (by norm_num) (ENNReal.mul_ne_top binKernelConstant_ne_top d.coincidence_ne_top)) hh
  rw [ENNReal.toReal_mul,ENNReal.toReal_ofReal (by positivity),
    ENNReal.toReal_ofReal (integral_nonneg (fun r => sq_nonneg ‖charFun μ r‖)),
    ENNReal.toReal_mul,ENNReal.toReal_mul] at hr
  norm_num only [ENNReal.toReal_ofNat] at hr
  simpa only [mul_assoc] using hr

end PositiveDistanceData

theorem uniform_actual_distance_low_band_oai {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      N₀ ≤ d.N → d.sig = sig → d.J = J → d.Q.side = 1 →
      d.StronglySeparated → d.ρ d.Q.carrierᶜ = 0 → 0 < d.q → d.t ≤ d.N →
      ∀ v ≤ d.t, (2:ℝ)^(-(d.a:ℝ)) *
        (∫ r in Icc (-((2:ℝ)^v)) ((2:ℝ)^v), ‖charFun d.weightedDistance r‖^2) ≤
          (32*binKernelConstant.toReal) *
            ({d with t := v,i := d.i+1} : PositiveDistanceData).coincidence.toReal := by
  obtain ⟨N₀,h₀⟩ := uniform_weighted_distance_nested_domination hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hN hsig' hJ' hQ hs hcarry hq ht v hv
  let := d.weightedDistance_isFinite (by rw [hQ]; norm_num) hs
  exact ({d with t := v,i := d.i+1} : PositiveDistanceData).dominated_distance_band
    d.weightedDistance (h₀ d hN hsig' hJ' hQ hs hcarry hq ht v hv)

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_distance_low_band_oai := @OAI.PlanarFalconer.uniform_actual_distance_low_band_oai
