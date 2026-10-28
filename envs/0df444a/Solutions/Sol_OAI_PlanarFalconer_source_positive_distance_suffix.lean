-- Prove2me | solution 1 for OAI.PlanarFalconer.source_positive_distance_suffix
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:10:33.519341+00:00
-- url     : https://prove2.me/submissions/71bc72fa-d2ce-4dac-96bc-0d1f2db12871

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_uniform_actual_suffix_local_bins

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_SuffixAngularRadius
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem dyadic_ratio_le_radius {a p l N : ℕ} {sig : ℝ}
    (hsig : 0 ≤ sig) (hl : a+l ≤ p) :
    (2:ℝ)^a/(2:ℝ)^p ≤ sourceAngularRadius N sig l := by
  have hpow : (2:ℝ)^a*(2:ℝ)^l ≤ (2:ℝ)^p := by
    rw [← pow_add]
    exact pow_le_pow_right₀ (by norm_num) hl
  have hsub : (2:ℝ)^a/(2:ℝ)^p ≤ 1/(2:ℝ)^l := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    simpa only [one_mul] using hpow
  have hR : 1 ≤ ((2:ℝ)^N)^(50*sig) :=
    Real.one_le_rpow (one_le_pow₀ (by norm_num)) (by positivity)
  apply le_min
  · exact (div_le_one (by positivity)).mpr
      (pow_le_pow_right₀ (by norm_num) (by omega))
  · exact hsub.trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hR (by positivity : 0 ≤ 1/(2:ℝ)^l))

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
-- module Solutions.OAIQ038_FA.Falconer_Estimates_ActualOuterMasks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceSmoothingLevels_pos {sig kap : ℝ} (hsig : 0 < sig) (hkap : 0 < kap) :
    0 < sourceSmoothingLevels sig kap := by
  unfold sourceSmoothingLevels
  exact Nat.ceil_pos.mpr (by positivity)

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

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

theorem distance_apply (d : PositiveDistanceData) {s : Set ℝ} (hs : MeasurableSet s) :
    d.distance s = d.cellPair {z | dist z.1 z.2 ∈ s ∧ z ∈ d.good} := by
  rw [distance,Measure.map_apply (continuous_fst.dist continuous_snd).measurable hs,
    pair,Measure.restrict_apply ((continuous_fst.dist continuous_snd).measurable hs)]
  rfl

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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_GraphDirectionStability
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

 theorem endpoint_direction_dist_le {x y c d : Plane} (hxy : y ≠ x) (hcd : d ≠ c) :
    dist (sourceRadialUnit x y) (sourceRadialUnit c d) ≤
      2*(dist x c + dist y d)/dist x y := by
  change dist (sourceRadialVector x y) (sourceRadialVector c d) ≤ _
  simp only [sourceRadialVector, ite_eq_right hxy, ite_eq_right hcd]
  have hn := normalized_vector_dist_le (y-x) (d-c) (sub_ne_zero.mpr hxy) (sub_ne_zero.mpr hcd)
  have hd : dist (y-x) (d-c) ≤ dist x c + dist y d := by
    rw [dist_eq_norm, show (y-x)-(d-c) = (y-d)-(x-c) by abel]
    exact (norm_sub_le _ _).trans_eq (by rw [dist_eq_norm,dist_eq_norm]; ring)
  have he : ‖y-x‖ = dist x y := by rw [dist_eq_norm, norm_sub_rev]
  rw [he] at hn ⊢
  exact hn.trans (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num))
    (dist_nonneg))

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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_Bins
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem realBin_measurable (w : ℝ) (j : ℤ) : MeasurableSet (realBin w j) :=
  measurableSet_Ico

theorem realBin_diameter (w : ℝ) (j : ℤ) {x y : ℝ}
    (hx : x ∈ realBin w j) (hy : y ∈ realBin w j) : |x-y| ≤ w := by
  simp only [realBin, Set.mem_Ico, Int.cast_add, Int.cast_one] at hx hy
  apply abs_le.mpr
  constructor <;> nlinarith

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

 theorem offset_rectangles_mass_le (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (w : ℝ) (h : ℤ) :
    (μ.prod ν) (⋃ j : ℤ, realBin w j ×ˢ realBin w (j-h)) ≤
      binL2Norm μ w * binL2Norm ν w := by
  apply (measure_iUnion_le _).trans
  simp only [Measure.prod_prod]
  exact ennreal_offset_cauchy (fun j => μ (realBin w j)) (fun j => ν (realBin w j)) h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_BinBands
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

 theorem realBin_band_offset {w C s₀ x y : ℝ} (hw : 0 < w)
    (hb : |x-y-s₀| ≤ C*w) {i j : ℤ}
    (hi : x ∈ realBin w i) (hj : y ∈ realBin w j) :
    i-j-⌊s₀/w⌋ ∈ bandOffsets C := by
  have hi1 : (i:ℝ) ≤ x/w := (le_div_iff₀ hw).mpr hi.1
  have hi2 : x/w < (i:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hi.2
  have hj1 : (j:ℝ) ≤ y/w := (le_div_iff₀ hw).mpr hj.1
  have hj2 : y/w < (j:ℝ)+1 := by
    simpa only [Int.cast_add,Int.cast_one] using (div_lt_iff₀ hw).mpr hj.2
  have hm1 := Int.floor_le (s₀/w)
  have hm2 := Int.lt_floor_add_one (s₀/w)
  have hb' : |x/w-y/w-s₀/w| ≤ C := by
    rw [← sub_div,← sub_div,abs_div,abs_of_pos hw]
    exact (div_le_iff₀ hw).mpr hb
  obtain ⟨hl,hu⟩ := abs_le.mp hb'
  have hC := Nat.le_ceil C
  apply Finset.mem_Icc.mpr
  constructor
  · have h : -((⌈C⌉₊:ℕ):ℝ)-2 ≤ (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) := by linarith
    exact_mod_cast h
  · have h : (i:ℝ)-(j:ℝ)-(⌊s₀/w⌋:ℝ) ≤ ((⌈C⌉₊:ℕ):ℝ)+2 := by linarith
    exact_mod_cast h

 theorem real_bin_shifted_band_bound (μ ν : Measure ℝ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] {w : ℝ} (hw : 0 < w) (C s₀ : ℝ) :
    (μ.prod ν) {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ≤
      ((bandOffsets C).card : ℝ≥0∞) * (binL2Norm μ w * binL2Norm ν w) := by
  let m : ℤ := ⌊s₀/w⌋
  have hs : {z : ℝ × ℝ | |z.1-z.2-s₀| ≤ C*w} ⊆
      ⋃ h ∈ bandOffsets C, ⋃ j : ℤ, realBin w j ×ˢ realBin w (j-(h+m)) := by
    intro z hz
    let i : ℤ := ⌊z.1/w⌋
    let j : ℤ := ⌊z.2/w⌋
    have hi := realBin_cover hw z.1
    have hj := realBin_cover hw z.2
    refine mem_iUnion.mpr ⟨i-j-m,mem_iUnion.mpr ⟨realBin_band_offset hw hz hi hj,?_⟩⟩
    apply mem_iUnion.mpr
    refine ⟨i,hi,?_⟩
    have he : i-(i-j-m+m)=j := by omega
    simpa only [he] using hj
  calc
    _ ≤ (μ.prod ν) (⋃ h ∈ bandOffsets C, ⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_mono hs
    _ ≤ ∑ h ∈ bandOffsets C, (μ.prod ν) (⋃ j : ℤ,
        realBin w j ×ˢ realBin w (j-(h+m))) := measure_biUnion_finset_le _ _
    _ ≤ ∑ _h ∈ bandOffsets C, binL2Norm μ w * binL2Norm ν w :=
      Finset.sum_le_sum (fun h _ => offset_rectangles_mass_le μ ν w (h+m))
    _ = _ := by simp

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
-- module Solutions.OAIQ038_FA.Falconer_Measures_FiniteMeasureProducts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem finite_measure_prod_sum {α β ι κ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (S : Finset ι) (T : Finset κ) (μ : ι → Measure α) (ν : κ → Measure β)
    [∀ i, IsFiniteMeasure (μ i)] [∀ j, IsFiniteMeasure (ν j)] :
    (∑ i ∈ S, μ i).prod (∑ j ∈ T, ν j) = ∑ i ∈ S, ∑ j ∈ T, (μ i).prod (ν j) := by
  apply Measure.ext_prod
  intro s t hs ht
  simp only [Measure.prod_prod,Measure.finsetSum_apply,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem finite_measure_restrict_sum {α ι : Type*} [MeasurableSpace α]
    (S : Finset ι) (μ : ι → Measure α) (A : Set α) :
    (∑ i ∈ S, μ i).restrict A = ∑ i ∈ S, (μ i).restrict A := by
  ext s hs
  simp only [Measure.restrict_apply hs,Measure.finsetSum_apply]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Geometry_FiniteBinComparison
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem ennreal_sq_bound_sqrt {x y F : ℝ≥0∞} (h : x^2 ≤ F*y^2) :
    x ≤ F^(1/2:ℝ)*y := by
  have hh := ENNReal.rpow_le_rpow h (by norm_num : (0:ℝ) ≤ 1/2)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)] at hh
  simp only [← ENNReal.rpow_two,← ENNReal.rpow_mul] at hh
  norm_num at hh
  exact hh

theorem bin_cross_from_squares (α β : Measure ℝ) (w : ℝ) {F a b : ℝ≥0∞}
    (ha : (binL2Norm α w)^2 ≤ F*a^2) (hb : (binL2Norm β w)^2 ≤ F*b^2) :
    (∑' k : ℤ, α (realBin w k)*β (realBin w k)) ≤ F*(a*b) := by
  have hcross := ennreal_offset_cauchy (fun k => α (realBin w k))
    (fun k => β (realBin w k)) 0
  simp only [sub_zero] at hcross
  have hh := hcross.trans (mul_le_mul' (ennreal_sq_bound_sqrt ha) (ennreal_sq_bound_sqrt hb))
  have hs : F^(1/2:ℝ)*F^(1/2:ℝ) = F := by
    rw [← ENNReal.rpow_add_of_nonneg (1/2) (1/2) (by norm_num) (by norm_num)]
    norm_num
  apply hh.trans_eq
  calc
    _ = (F^(1/2:ℝ)*F^(1/2:ℝ))*(a*b) := mul_mul_mul_comm _ _ _ _
    _ = _ := by rw [hs]

theorem finite_bin_collision_comparison {ι : Type*} (S : Finset ι)
    (α β : ι → Measure ℝ) [∀ i, IsFiniteMeasure (α i)] [∀ i, IsFiniteMeasure (β i)]
    (w : ℝ) (E : Set (ℝ × ℝ)) (F : ℝ≥0∞)
    (hnorm : ∀ i ∈ S, (binL2Norm (α i) w)^2 ≤ F*((β i) univ)^2)
    (hcoarse : ∀ i ∈ S, ∀ j ∈ S,
      (∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0) →
      ((β i).prod (β j)) E = (β i univ)*(β j univ)) :
    (binL2Norm (∑ i ∈ S, α i) w)^2 ≤
      F*((∑ i ∈ S, β i).prod (∑ i ∈ S, β i)) E := by
  classical
  have hpair (i : ι) (hi : i ∈ S) (j : ι) (hj : j ∈ S) :
      (∑' k : ℤ, α i (realBin w k)*α j (realBin w k)) ≤ F*((β i).prod (β j)) E := by
    by_cases hh : ∃ k : ℤ, α i (realBin w k) ≠ 0 ∧ α j (realBin w k) ≠ 0
    · rw [hcoarse i hi j hj hh]
      exact bin_cross_from_squares _ _ w (hnorm i hi) (hnorm j hj)
    · have hz (k : ℤ) : α i (realBin w k)*α j (realBin w k) = 0 := by
        by_cases hi0 : α i (realBin w k) = 0
        · simp [hi0]
        · have hj0 : α j (realBin w k) = 0 := by
            by_contra hj0
            exact hh ⟨k,hi0,hj0⟩
          simp [hj0]
      simp only [hz,tsum_zero,zero_le]
  rw [pow_two,binL2Norm_mul_self]
  simp only [Measure.finsetSum_apply,pow_two,Finset.sum_mul,Finset.mul_sum]
  simp_rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i ∈ S, ∑ j ∈ S, F*((β i).prod (β j)) E :=
      Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpair i hi j hj
    _ = _ := by
      rw [finite_measure_prod_sum]
      simp only [Measure.finsetSum_apply,Finset.mul_sum]

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

theorem unnormalized_coincidence (d : PositiveDistanceData) :
    d.normalization⁻¹ * d.coincidence =
      (d.pair.prod d.pair)
        {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100*d.width} := by
  rw [coincidence,← mul_assoc,
    ENNReal.inv_mul_cancel (ne_of_gt d.normalization_pos) d.normalization_ne_top,one_mul]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicIntegralSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem DyadicSquare.biUnion_descendants (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) : (⋃ P ∈ dyadicPaths n, (Q.descendant P).carrier) = Q.carrier := by
  ext x
  constructor
  · intro hx
    obtain ⟨P, _, hx⟩ := mem_iUnion₂.mp hx
    exact Q.descendant_subset hQ P hx
  · intro hx
    obtain ⟨P, hP, hxP⟩ := Q.mem_descendant_at_depth n hx
    exact mem_iUnion₂.mpr ⟨P, hP, hxP⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasureSplitting
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

 theorem DyadicSquare.measure_split_occupied (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (n : ℕ) :
    ρ.restrict Q.carrier =
      ∑ P ∈ occupiedAnchorPaths Q ρ n, ρ.restrict (Q.descendant P).carrier := by
  classical
  have hall : ρ.restrict Q.carrier =
      ∑ P ∈ dyadicPaths n, ρ.restrict (Q.descendant P).carrier := by
    rw [← Q.biUnion_descendants hQ n]
    rw [Measure.restrict_biUnion_finset]
    · rw [Measure.sum_fintype]
      exact Finset.sum_coe_sort (dyadicPaths n) (fun P => ρ.restrict (Q.descendant P).carrier)
    · intro P hP S hS hne
      exact Q.descendants_disjoint hQ
        (((mem_dyadicPaths n P).mp hP).trans ((mem_dyadicPaths n S).mp hS).symm) hne
    · exact fun P => (Q.descendant P).measurable
  rw [hall]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro P hP hnot
  apply Measure.restrict_eq_zero.mpr
  by_contra hne
  exact hnot (Finset.mem_filter.mpr ⟨hP,bot_lt_iff_ne_bot.mpr hne⟩)

 theorem occupied_absolute_measure_sum (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) (A : CellPath) (n : ℕ) :
    (∑ P ∈ (occupiedAnchorPaths (Q.descendant A) ρ n).image (fun c => A++c),
      ρ.restrict (Q.descendant P).carrier) = ρ.restrict (Q.descendant A).carrier := by
  classical
  rw [Finset.sum_image (fun _ _ _ _ he => List.append_cancel_left he)]
  simp only [DyadicSquare.descendant_append]
  exact ((Q.descendant A).measure_split_occupied (Q.descendant_side_pos hQ A) ρ n).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_ProjectionCellPartition
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem projectionTestCells_eq_image (Q : DyadicSquare) (ρ : Measure Plane)
    {p u : ℕ} (hpu : p ≤ u) {P : CellPath} (hP : P.length = p) :
    projectionTestCells Q ρ p u P =
      (occupiedAnchorPaths (Q.descendant P) ρ (u-p)).image (fun c => P++c) := by
  classical
  ext C
  constructor
  · intro hC
    obtain ⟨hC,hpos,htake⟩ := Finset.mem_filter.mp hC
    have hlen := (mem_dyadicPaths _ _).mp hC
    refine Finset.mem_image.mpr ⟨C.drop p,?_,?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hlen]),?_⟩
      simpa only [← Q.descendant_append,← htake,List.take_append_drop] using hpos
    · rw [← htake,List.take_append_drop]
  · intro hmem
    obtain ⟨D,hD,rfl⟩ := Finset.mem_image.mp hmem
    obtain ⟨hD,hpos⟩ := Finset.mem_filter.mp hD
    have hlen := (mem_dyadicPaths _ _).mp hD
    apply Finset.mem_filter.mpr
    refine ⟨(mem_dyadicPaths _ _).mpr (by simp [hP,hlen,Nat.add_sub_of_le hpu]),?_,?_⟩
    · simpa only [Q.descendant_append] using hpos
    · simpa only [← hP] using (List.take_left : (P++D).take P.length = P)

theorem projection_measure_split (Q : DyadicSquare) (hQ : 0 < Q.side)
    (ρ : Measure Plane) {p u : ℕ} (hpu : p ≤ u)
    {P : CellPath} (hP : P.length = p) :
    ρ.restrict (Q.descendant P).carrier =
      ∑ C ∈ projectionTestCells Q ρ p u P, ρ.restrict (Q.descendant C).carrier := by
  rw [projectionTestCells_eq_image Q ρ hpu hP]
  exact (occupied_absolute_measure_sum Q hQ ρ P (u-p)).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_MinimalDescriptorLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem originDescriptor_length_le_anchor (A : ℕ → ℝ) {N q b u : ℕ}
    {d : PolicyDescriptor} (hd : d ∈ originDescriptors A N q b u) :
    descriptorLength d ≤ descriptorAnchor d := by
  obtain hd | hd := Finset.mem_union.mp hd
  · obtain ⟨g,_,rfl⟩ := Finset.mem_image.mp hd
    exact Nat.sub_le _ _
  · split_ifs at hd with h
    · obtain rfl := Finset.mem_singleton.mp hd
      dsimp [descriptorLength,descriptorAnchor]
      omega
    · simp at hd

theorem policyDescriptor_twice_length (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {d : PolicyDescriptor}
    (hd : d ∈ policyDescriptorList A N q a t) :
    a + 2*descriptorLength d ≤ t := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,ht,hw⟩ := Finset.mem_filter.mp hz
  have hu := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hl := originDescriptor_length A hq hu hw hd
  have hp := originDescriptor_length_le_anchor A hd
  omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixDescriptors
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem policyDescriptor_anchor_le_end (A : ℕ → ℝ) {N q a t : ℕ}
    (hq : 0 < q) {b : PolicyDescriptor}
    (hb : b ∈ policyDescriptorList A N q a t) : descriptorAnchor b ≤ t := by
  obtain ⟨_,u,_,hut,_,_,_,_,hu⟩ := policyDescriptor_origin A hq hb
  omega

theorem DyadicSquare.eq_take_of_mem (Q : DyadicSquare) (hQ : 0 < Q.side)
    {P C : CellPath} {n : ℕ} (hP : P.length = n) (hn : n ≤ C.length)
    {x : Plane} (hxP : x ∈ (Q.descendant P).carrier)
    (hxC : x ∈ (Q.descendant C).carrier) : P = C.take n := by
  by_contra hne
  have hl : P.length = (C.take n).length := by simp [hP,List.length_take,hn]
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ hl hne) hxP
    (Q.descendant_subset_take hQ C n hxC)

theorem DyadicSquare.same_ancestor (Q : DyadicSquare) (hQ : 0 < Q.side)
    {P C : CellPath} {n : ℕ} (hP : P.length = n) (hn : n ≤ C.length)
    {x y : Plane} (hxP : x ∈ (Q.descendant P).carrier)
    (hxC : x ∈ (Q.descendant C).carrier) (hyC : y ∈ (Q.descendant C).carrier) :
    y ∈ (Q.descendant P).carrier := by
  rw [Q.eq_take_of_mem hQ hP hn hxP hxC]
  exact Q.descendant_subset_take hQ C n hyC

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixDirectionGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set

theorem fine_cell_direction_dist (P Q : DyadicSquare)
    (hP : 0 < P.side) (hQ : 0 < Q.side) {a p : ℕ}
    (hp : P.side ≤ 1/(2:ℝ)^p) (hq : Q.side ≤ 1/(2:ℝ)^p)
    {x y x' y' : Plane} (hx : x ∈ P.carrier) (hy : y ∈ Q.carrier)
    (hx' : x' ∈ P.carrier) (hy' : y' ∈ Q.carrier)
    (hs : 96/(2:ℝ)^a ≤ dist x y) (hne : x' ≠ y') :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^a/(2:ℝ)^p := by
  have hdist : 0 < dist x y := (by positivity : 0 < 96/(2:ℝ)^a).trans_le hs
  have hxy : x ≠ y := dist_pos.mp hdist
  have hb := endpoint_direction_dist_le hxy hne
  rw [dist_comm y x] at hb
  have hxmove := P.dist_le hP.le hx hx'
  have hymove := Q.dist_le hQ.le hy hy'
  have hnum : 2*(dist y y'+dist x x') ≤ 8/(2:ℝ)^p := by
    calc
      _ ≤ 2*(2*Q.side+2*P.side) :=
        mul_le_mul_of_nonneg_left (add_le_add hymove hxmove) (by norm_num)
      _ ≤ 2*(2*(1/(2:ℝ)^p)+2*(1/(2:ℝ)^p)) := by gcongr
      _ = _ := by ring
  have hscale : 8/(2:ℝ)^p/(96/(2:ℝ)^a) ≤ (2:ℝ)^a/(2:ℝ)^p := by
    have hratio : 0 < (2:ℝ)^a/(2:ℝ)^p := by positivity
    have he : 8/(2:ℝ)^p/(96/(2:ℝ)^a) = ((2:ℝ)^a/(2:ℝ)^p)/12 := by field_simp; ring
    rw [he]
    linarith only [hratio]
  exact hb.trans ((div_le_div₀ (by positivity) hnum (by positivity) hs).trans hscale)

namespace PositiveDistanceData

theorem fine_endpoints_separated (d : PositiveDistanceData) (hQ : 0 < d.Q.side)
    (hs : d.StronglySeparated) {P C : CellPath}
    (hP : P.take d.a = d.X) (hC : C.take d.a = d.Y)
    {x y : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier) :
    96/(2:ℝ)^d.a ≤ dist x y := by
  have hh := (d.separated_distance_ratio hQ hs (z := (x,y))
    (hP ▸ d.Q.descendant_subset_take hQ P d.a hx)
    (hC ▸ d.Q.descendant_subset_take hQ C d.a hy)).1
  have hh' := (le_div_iff₀ (by positivity : 0 < (2:ℝ)^(-(d.a:ℝ)))).mp hh
  simpa only [Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,div_eq_mul_inv] using hh'

theorem fine_directions (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    (hs : d.StronglySeparated) {p : ℕ} {P C : CellPath}
    (hP : P.length = p) (hC : C.length = p)
    (hPX : P.take d.a = d.X) (hCY : C.take d.a = d.Y)
    {x y x' y' : Plane} (hx : x ∈ (d.Q.descendant P).carrier)
    (hy : y ∈ (d.Q.descendant C).carrier)
    (hx' : x' ∈ (d.Q.descendant P).carrier) (hy' : y' ∈ (d.Q.descendant C).carrier) :
    dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤ (2:ℝ)^d.a/(2:ℝ)^p := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hs' := d.fine_endpoints_separated hside hs hPX hCY hx' hy'
  exact fine_cell_direction_dist _ _ (d.Q.descendant_side_pos hside P)
    (d.Q.descendant_side_pos hside C)
    (by simp only [DyadicSquare.descendant_side,hQ,hP,le_refl])
    (by simp only [DyadicSquare.descendant_side,hQ,hC,le_refl]) hx hy hx' hy'
    (d.fine_endpoints_separated hside hs hPX hCY hx hy)
    (dist_pos.mp ((by positivity : 0 < 96/(2:ℝ)^d.a).trans_le hs'))

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixRetainedPairs
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem suffix_retained_spec (d : PositiveDistanceData) {p : ℕ} {c : CellPath × CellPath}
    (hc : c ∈ d.suffixRetained p) :
    c.1.length = p ∧ c.2.length = p ∧ c.1.take d.a = d.X ∧ c.2.take d.a = d.Y ∧
      ∃ x ∈ (d.Q.descendant c.1).carrier, ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good := by
  classical
  obtain ⟨hc,hw⟩ := Finset.mem_filter.mp hc
  obtain ⟨h₁,h₂⟩ := Finset.mem_product.mp hc
  exact ⟨(mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₁).1,
    (mem_dyadicPaths _ _).mp (Finset.mem_filter.mp h₂).1,
    (Finset.mem_filter.mp h₁).2.2,(Finset.mem_filter.mp h₂).2.2,hw⟩

theorem cellPair_split_suffix (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.cellPair = ∑ c ∈ d.suffixRectangles p, (d.suffixData c).cellPair := by
  change (d.ρ.restrict (d.Q.descendant d.X).carrier).prod
    (d.ρ.restrict (d.Q.descendant d.Y).carrier) = _
  rw [projection_measure_split d.Q hQ d.ρ hap hX,
    projection_measure_split d.Q hQ d.ρ hap hY,finite_measure_prod_sum]
  simp only [suffixRectangles,cellPair]
  exact (Finset.sum_product (projectionTestCells d.Q d.ρ d.a p d.X)
    (projectionTestCells d.Q d.ρ d.a p d.Y)
    (fun c : CellPath × CellPath => (d.ρ.restrict (d.Q.descendant c.1).carrier).prod
      (d.ρ.restrict (d.Q.descendant c.2).carrier))).symm

theorem pair_zero_of_no_witness (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] (c : CellPath × CellPath)
    (hw : ¬ ∃ x ∈ (d.Q.descendant c.1).carrier,
      ∃ y ∈ (d.Q.descendant c.2).carrier, (x,y) ∈ d.good) : (d.suffixData c).pair = 0 := by
  apply Measure.restrict_eq_zero.mpr
  change ((d.ρ.restrict (d.Q.descendant c.1).carrier).prod
    (d.ρ.restrict (d.Q.descendant c.2).carrier)) d.good = 0
  rw [Measure.prod_restrict,Measure.restrict_apply d.measurable_good]
  have he : d.good ∩ ((d.Q.descendant c.1).carrier ×ˢ (d.Q.descendant c.2).carrier) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    exact hw ⟨z.1,hz.2.1,z.2,hz.2.2,hz.1⟩
  rw [he,measure_empty]

theorem pair_split_retained (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.pair = ∑ c ∈ d.suffixRetained p, (d.suffixData c).pair := by
  classical
  rw [pair,d.cellPair_split_suffix hQ hap hX hY,finite_measure_restrict_sum]
  change (∑ c ∈ d.suffixRectangles p, (d.suffixData c).pair) = _
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro c hc hn
  apply d.pair_zero_of_no_witness c
  intro hw
  exact hn (Finset.mem_filter.mpr ⟨hc,hw⟩)

theorem distance_split_retained (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a) :
    d.distance = ∑ c ∈ d.suffixRetained p, (d.suffixData c).distance := by
  rw [distance,d.pair_split_retained hQ hap hX hY,Measure.map_finset_sum (by fun_prop)]
  rfl

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixBinGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal
namespace PositiveDistanceData

theorem suffix_distance_variation (d : PositiveDistanceData) (hQ : d.Q.side = 1)
    {p : ℕ} {c : CellPath × CellPath} (hP : c.1.length = p) (hC : c.2.length = p)
    {z z' : Plane × Plane}
    (hz : z.1 ∈ (d.Q.descendant c.1).carrier ∧ z.2 ∈ (d.Q.descendant c.2).carrier)
    (hz' : z'.1 ∈ (d.Q.descendant c.1).carrier ∧ z'.2 ∈ (d.Q.descendant c.2).carrier) :
    |dist z.1 z.2-dist z'.1 z'.2| ≤ 4/(2:ℝ)^p := by
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have h₁ := (d.Q.descendant c.1).dist_le (d.Q.descendant_side_pos hside _).le hz.1 hz'.1
  have h₂ := (d.Q.descendant c.2).dist_le (d.Q.descendant_side_pos hside _).le hz.2 hz'.2
  rw [DyadicSquare.descendant_side,hP,hQ] at h₁
  rw [DyadicSquare.descendant_side,hC,hQ] at h₂
  have hh := dist_dist_dist_le z.1 z.2 z'.1 z'.2
  rw [Real.dist_eq] at hh
  exact hh.trans ((add_le_add h₁ h₂).trans_eq (by ring))

theorem distance_bin_witness (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (w : ℝ) (k : ℤ) (hm : d.distance (realBin w k) ≠ 0) :
    ∃ z : Plane × Plane, dist z.1 z.2 ∈ realBin w k ∧
      z.1 ∈ (d.Q.descendant d.X).carrier ∧ z.2 ∈ (d.Q.descendant d.Y).carrier := by
  rw [d.distance_apply (realBin_measurable w k)] at hm
  obtain ⟨z,hz,hcells⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hm
    (d.ae_cellPair_mem.filter_mono (ae_mono Measure.restrict_le_self))
  exact ⟨z,hz.1,hcells⟩

theorem shared_bin_full_coarse_collision (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : d.Q.side = 1) {p : ℕ} (hpt : p ≤ d.t)
    {c b : CellPath × CellPath} (hc : c ∈ d.suffixRetained p) (hb : b ∈ d.suffixRetained p)
    (hbin : ∃ k : ℤ, (d.suffixData c).distance (realBin d.width k) ≠ 0 ∧
      (d.suffixData b).distance (realBin d.width k) ≠ 0) :
    ((d.suffixFullDistance c).prod (d.suffixFullDistance b))
      {z : ℝ × ℝ | |z.1-z.2| ≤ 100/(2:ℝ)^p} =
        (d.suffixFullDistance c univ)*(d.suffixFullDistance b univ) := by
  obtain ⟨hC₁,hC₂,_⟩ := d.suffix_retained_spec hc
  obtain ⟨hB₁,hB₂,_⟩ := d.suffix_retained_spec hb
  obtain ⟨k,hkc,hkb⟩ := hbin
  obtain ⟨x,hxbin,hx⟩ := (d.suffixData c).distance_bin_witness d.width k hkc
  obtain ⟨y,hybin,hy⟩ := (d.suffixData b).distance_bin_witness d.width k hkb
  have hxy := realBin_diameter d.width k hxbin hybin
  have hw : d.width ≤ 1/(2:ℝ)^p := by
    simp only [width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),Real.rpow_natCast,one_div]
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num) hpt)
  have hgood : ∀ᵐ z ∂(d.suffixData c).cellPair.prod (d.suffixData b).cellPair,
      |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100/(2:ℝ)^p := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (d.suffixData c).ae_cellPair_mem,
      Measure.quasiMeasurePreserving_snd.ae (d.suffixData b).ae_cellPair_mem] with z hz hz'
    have h₁ := d.suffix_distance_variation hQ hC₁ hC₂ hz hx
    have h₂ := d.suffix_distance_variation hQ hB₁ hB₂ hz' hy
    obtain ⟨ha,hb⟩ := abs_le.mp h₁
    obtain ⟨hc,hd⟩ := abs_le.mp h₂
    obtain ⟨he,hf⟩ := abs_le.mp hxy
    apply abs_le.mpr
    simp only [div_eq_mul_inv,one_mul] at ha hb hc hd hw ⊢
    constructor <;> linarith [show 0 < ((2:ℝ)^p)⁻¹ by positivity]
  rw [suffixFullDistance,suffixFullDistance,Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_apply (by fun_prop) (by measurability)]
  change ((d.suffixData c).cellPair.prod (d.suffixData b).cellPair)
    {z | |dist z.1.1 z.1.2-dist z.2.1 z.2.2| ≤ 100/(2:ℝ)^p} = _
  rw [measure_congr (Filter.eventuallyEq_univ.mpr hgood),← univ_prod_univ,Measure.prod_prod]
  simp only [Measure.map_apply (continuous_fst.dist continuous_snd).measurable MeasurableSet.univ,preimage_univ]

end PositiveDistanceData

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorGoodTransfer
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_descriptor_good_transfer {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
      ∀ (ρ : Measure Plane) (m : ℝ → ℝ) (lam : ℝ) (i : ℕ)
        (b : PolicyDescriptor), ValidDescriptor N b →
      ∀ P : CellPath, P.length = descriptorAnchor b → ∀ ω ω' : UnitCircle,
      dist ω ω' ≤ sourceAngularRadius N sig (descriptorLength b) →
      ω ∈ descriptorGoodSet Q ρ m N lam sig J i P b →
      ω' ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) P b := by
  obtain ⟨N₁,h₁⟩ := uniform_parallel_width_transfer hsig hJ (C₀ := 1) zero_le_one
  obtain ⟨N₂,h₂⟩ := uniform_projection_width_transfer hsig hJ (C₀ := 1) zero_le_one
  refine ⟨max N₁ N₂,?_⟩
  intro N hN Q hQ ρ m lam i b hb P hP ω ω' hd hg
  obtain ⟨hN₁, hN₂⟩ := max_le_iff.mp hN
  change dist (ω:Plane) (ω':Plane) ≤ _ at hd
  cases b with
  | parallel g p =>
    dsimp only [descriptorGoodSet,parallelGoodSet,Set.mem_ofPred_eq] at hg ⊢
    change (_ : ℝ) ≤ _ at hg ⊢
    apply le_trans (Nat.cast_le.mpr (h₁ N hN₁
      Q ρ g p hb.1 P i ω ω' (by simpa only [descriptorLength,one_mul] using hd))) hg
  | projection p u =>
    dsimp only [descriptorGoodSet,projectionGoodSet,Set.mem_ofPred_eq] at hg ⊢
    change (_ : ℝ) ≤ _ at hg ⊢
    apply le_trans (Nat.cast_le.mpr (h₂ N hN₂
      Q hQ ρ p u hb.1 P hP i ω ω' (by simpa only [descriptorLength,one_mul] using hd))) hg

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixGoodTransport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_suffix_good_transport {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      ∀ p : ℕ, d.a ≤ p → p ≤ d.t → d.t ≤ d.N →
      ∀ P C : CellPath, P.length = p → C.length = p →
      P.take d.a = d.X → C.take d.a = d.Y →
      ∀ x ∈ (d.Q.descendant P).carrier, ∀ y ∈ (d.Q.descendant C).carrier,
      (x,y) ∈ d.good → ∀ x' ∈ (d.Q.descendant P).carrier,
      ∀ y' ∈ (d.Q.descendant C).carrier,
      (x',y') ∈ ({d with t := p, i := d.i+1} : PositiveDistanceData).good := by
  obtain ⟨N₀,hN₀⟩ := uniform_descriptor_good_transfer hsig hJ
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq p hap hpt htN P C hP hC hPX hCY x hx y hy hg x' hx' y' hy'
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hmove := d.fine_directions hQ hs hP hC hPX hCY hx hy hx' hy'
  intro b hb
  have hb' := policyDescriptorList_mono (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) le_rfl hpt hb
  have hbg := hg b hb'
  have hanchor : descriptorAnchor b ≤ p :=
    policyDescriptor_anchor_le_end _ hq hb
  have hl := policyDescriptor_twice_length (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq hb
  dsimp only at hl
  have hrad : dist (sourceRadialUnit y x) (sourceRadialUnit y' x') ≤
      sourceAngularRadius d.N sig (descriptorLength b) :=
    hmove.trans (dyadic_ratio_le_radius hsig.le (by omega))
  have hvalid := policyDescriptor_valid (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (hpt.trans htN) hb
  have htransfer (A : CellPath) (hA : A.length = descriptorAnchor b)
      (hAω : sourceRadialUnit y x ∈ descriptorGoodSet d.Q d.ρ d.mass d.N d.lam d.sig d.J d.i A b) :
      sourceRadialUnit y' x' ∈ descriptorGoodSet d.Q d.ρ d.mass d.N d.lam d.sig d.J (d.i+1) A b := by
    rw [hsig',hJ'] at hAω ⊢
    exact hN₀ d.N hN d.Q hQ d.ρ d.mass d.lam d.i b hvalid A hA _ _ hrad hAω
  constructor
  · intro A hA hxA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.1 A hA
    exact d.Q.same_ancestor hside hlen (by omega) hxA hx' hx
  · intro A hA hyA
    have hlen := (mem_dyadicPaths _ _).mp hA
    apply htransfer A hlen
    apply hbg.2 A hA
    exact d.Q.same_ancestor hside hlen (by omega) hyA hy' hy

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixCoarseDomination
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
namespace PositiveDistanceData

theorem suffix_full_pair_le_coarse (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hgood : ∀ c ∈ d.suffixRetained p, ∀ x ∈ (d.Q.descendant c.1).carrier,
      ∀ y ∈ (d.Q.descendant c.2).carrier,
      (x,y) ∈ ({d with t := p,i := d.i+1} : PositiveDistanceData).good) :
    (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair) ≤
      ({d with t := p,i := d.i+1} : PositiveDistanceData).pair := by
  classical
  let e : PositiveDistanceData := {d with t := p,i := d.i+1}
  have hle : (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair) ≤ d.cellPair := by
    rw [d.cellPair_split_suffix hQ hap hX hY]
    intro s
    simp only [Measure.finsetSum_apply]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have he : (∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair).restrict e.good =
      ∑ c ∈ d.suffixRetained p, (d.suffixData c).cellPair := by
    rw [finite_measure_restrict_sum]
    apply Finset.sum_congr rfl
    intro c hc
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [(d.suffixData c).ae_cellPair_mem] with z hz
    exact hgood c hc z.1 hz.1 z.2 hz.2
  rw [← he]
  exact Measure.restrict_mono_measure hle e.good

theorem suffix_full_distance_le_coarse (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) {p : ℕ} (hap : d.a ≤ p)
    (hX : d.X.length = d.a) (hY : d.Y.length = d.a)
    (hgood : ∀ c ∈ d.suffixRetained p, ∀ x ∈ (d.Q.descendant c.1).carrier,
      ∀ y ∈ (d.Q.descendant c.2).carrier,
      (x,y) ∈ ({d with t := p,i := d.i+1} : PositiveDistanceData).good) :
    (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c) ≤
      ({d with t := p,i := d.i+1} : PositiveDistanceData).distance := by
  have hh := Measure.map_mono (d.suffix_full_pair_le_coarse hQ hap hX hY hgood)
    (continuous_fst.dist continuous_snd).measurable
  rw [Measure.map_finset_sum (by fun_prop)] at hh
  exact hh

end PositiveDistanceData

theorem uniform_suffix_coarse_domination {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ (d : PositiveDistanceData) [IsFiniteMeasure d.ρ],
      d.sig = sig → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated →
      0 < d.q → d.X.length = d.a → d.Y.length = d.a →
      ∀ p : ℕ, d.a ≤ p → p ≤ d.t → d.t ≤ d.N →
      (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c) ≤
        ({d with t := p,i := d.i+1} : PositiveDistanceData).distance := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_good_transport hsig hJ
  refine ⟨N₀,?_⟩
  intro d _ hsig' hJ' hN hQ hs hq hX hY p hap hpt htN
  apply d.suffix_full_distance_le_coarse (by rw [hQ]; norm_num) hap hX hY
  intro c hc x' hx' y' hy'
  obtain ⟨hP,hC,hPX,hCY,x,hx,y,hy,hg⟩ := d.suffix_retained_spec hc
  exact hN₀ d hsig' hJ' hN hQ hs hq p hap hpt htN c.1 c.2 hP hC hPX hCY x hx y hy hg x' hx' y' hy'

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixBinAssembly
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_bin_assembly {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let p := policyDepth (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
      d.a+d.t < 2*p →
      (binL2Norm d.distance d.width)^2 ≤
        (((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
          (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
            2000*(d.lam+sig)+12*d.lam))) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₁,h₁⟩ := uniform_actual_suffix_local_bins hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_suffix_coarse_domination hsig hJ
  refine ⟨max N₁ N₂,?_⟩
  intro d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi p hsuffix
  have := hprof.probability
  have hside : 0 < d.Q.side := by rw [hQ]; norm_num
  have hp := policyDepth_interior (fun n => d.mass n-(n:ℝ)/(d.N:ℝ)) hq
    (policyBlocks_nonempty hq htN hw)
  have hap : d.a ≤ p := by dsimp [p]; omega
  have hpt : p ≤ d.t := by dsimp [p]; omega
  let e : PositiveDistanceData := {d with t := p,i := d.i+1}
  let E : Set (ℝ × ℝ) := {z | |z.1-z.2| ≤ 100/(2:ℝ)^p}
  let F : ℝ≥0∞ := ((bandOffsets 3).card : ℝ≥0∞)*ENNReal.ofReal (((2:ℝ)^d.N)^
    (-(d.mass d.t-d.mass p)+height (fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)) p d.t+
      2000*(d.lam+sig)+12*d.lam))
  have hnorm := h₁ d hsig' hJ' ((le_max_left _ _).trans hN) hQ hs hq B δ hprof hw htN hi hsuffix
  have hdom := h₂ d hsig' hJ' ((le_max_right _ _).trans hN) hQ hs hq hX hY p hap hpt htN
  have hbin := finite_bin_collision_comparison (d.suffixRetained p)
    (fun c => (d.suffixData c).distance) d.suffixFullDistance d.width E F hnorm
    (fun c hc b hb hcommon => d.shared_bin_full_coarse_collision hQ hpt hc hb hcommon)
  rw [← d.distance_split_retained hside hap hX hY] at hbin
  have he : (e.distance.prod e.distance) E = e.normalization⁻¹*e.coincidence := by
    have hwidth : 100/(2:ℝ)^p = 100*e.width := by
      simp only [e,PositiveDistanceData.width,Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
        Real.rpow_natCast,div_eq_mul_inv]
    change (e.distance.prod e.distance) {z | |z.1-z.2| ≤ 100/(2:ℝ)^p} = _
    rw [hwidth,e.distance_collision,e.unnormalized_coincidence]
  calc
    _ ≤ F*((∑ c ∈ d.suffixRetained p, d.suffixFullDistance c).prod
        (∑ c ∈ d.suffixRetained p, d.suffixFullDistance c)) E := hbin
    _ ≤ F*(e.distance.prod e.distance) E := mul_le_mul' le_rfl (Measure.prod_mono hdom hdom E)
    _ = _ := by rw [he]; dsimp only [F,e]; ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixNormalization
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

theorem coincidence_le_bin_sq (d : PositiveDistanceData) [IsFiniteMeasure d.ρ] :
    d.coincidence ≤ d.normalization * (((bandOffsets 100).card : ℝ≥0∞)*
      (binL2Norm d.distance d.width)^2) := by
  have hh := real_bin_shifted_band_bound d.distance d.distance d.width_pos 100 0
  simp only [sub_zero,← pow_two] at hh
  rw [d.distance_collision] at hh
  exact mul_le_mul' le_rfl hh

theorem suffix_normalization_ratio (d : PositiveDistanceData) (p : ℕ) :
    d.normalization * ({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ =
      ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p)) := by
  rw [normalization_inv]
  change ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-d.a)/d.levelMass^4) *
    ENNReal.ofReal (d.levelMass^4*(2:ℝ)^(-((p:ℝ)-d.a))) = _
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have hm : d.levelMass^4 ≠ 0 := pow_ne_zero _ d.levelMass_pos.ne'
  calc
    _ = (2:ℝ)^((d.t:ℝ)-d.a)*(2:ℝ)^(-((p:ℝ)-d.a)) := by field_simp [d.levelMass_pos.ne']
    _ = _ := by
      rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring

theorem suffix_normalized_from_bins (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (p : ℕ) (F : ℝ≥0∞)
    (hbin : (binL2Norm d.distance d.width)^2 ≤
      F*({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹ *
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence) :
    d.coincidence ≤ ((bandOffsets 100).card : ℝ≥0∞)*F*
      ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p))*
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  have hh := d.coincidence_le_bin_sq.trans
    (mul_le_mul' le_rfl (mul_le_mul' le_rfl hbin))
  apply hh.trans_eq
  calc
    _ = ((bandOffsets 100).card : ℝ≥0∞)*F*
        (d.normalization*({d with t := p,i := d.i+1} : PositiveDistanceData).normalization⁻¹)*
        ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by ring
    _ = _ := by rw [d.suffix_normalization_ratio]

end PositiveDistanceData

theorem suffix_profile_power_identity (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (p t : ℕ) (loss : ℝ) :
    ((2:ℝ)^N)^(-(m t-m p)+height (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p t+loss)*
      (2:ℝ)^((t:ℝ)-p) =
      ((2:ℝ)^N)^((m p-(p:ℝ)/(N:ℝ))-intervalMin (fun n : ℕ => m n-(n:ℝ)/(N:ℝ)) p t+loss) := by
  have hnr : (N:ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hscale : (2:ℝ)^((t:ℝ)-p) = ((2:ℝ)^N)^(((t:ℝ)-p)/(N:ℝ)) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
    congr 1
    field_simp
  rw [hscale,← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
  congr 1
  unfold height
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ActualSuffixReduction
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_reduction_explicit {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ 2255*ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+2000*(d.lam+sig)+12*d.lam)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₀,hN₀⟩ := uniform_suffix_bin_assembly hsig hJ
  refine ⟨N₀,?_⟩
  intro d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi A p hsuffix
  have := hprof.probability
  have hb := hN₀ d hsig' hJ' hN hQ hs hq hX hY B δ hprof hw htN hi hsuffix
  have hn := d.suffix_normalized_from_bins p _ hb
  have hpow : ((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam)*
      (2:ℝ)^((d.t:ℝ)-p) =
      ((2:ℝ)^d.N)^(A p-intervalMin A p d.t+2000*(d.lam+sig)+12*d.lam) := by
    simpa only [A,add_assoc] using suffix_profile_power_identity d.mass
      (by omega : 0 < d.N) p d.t (2000*(d.lam+sig)+12*d.lam)
  have hc : ((bandOffsets 100).card : ℝ≥0∞)*((bandOffsets 3).card : ℝ≥0∞) = 2255 := by
    norm_num [bandOffsets] <;> (rw [show Int.toNat 205 = 205 from rfl, show Int.toNat 11 = 11 from rfl]; norm_num)
  apply hn.trans_eq
  congr 1
  calc
    _ = (((bandOffsets 100).card : ℝ≥0∞)*((bandOffsets 3).card : ℝ≥0∞))*
        (ENNReal.ofReal (((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam))*
          ENNReal.ofReal ((2:ℝ)^((d.t:ℝ)-p))) := by ring
    _ = 2255*ENNReal.ofReal
        (((2:ℝ)^d.N)^(-(d.mass d.t-d.mass p)+height A p d.t+2000*(d.lam+sig)+12*d.lam)*
          (2:ℝ)^((d.t:ℝ)-p)) := by
      rw [hc,← ENNReal.ofReal_mul (by positivity)]
    _ = _ := by rw [hpow]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SuffixPowerLoss
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem uniform_suffix_coefficient_absorption {sig eps : ℝ}
    (hsig : 0 ≤ sig) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a lam : ℝ, 0 ≤ lam →
      2255*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) ≤
        ((2:ℝ)^N)^(a+4000*(lam+sig)+eps) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed heps 2255
  refine ⟨N₀,?_⟩
  intro N hN a lam hlam
  calc
    _ ≤ ((2:ℝ)^N)^eps*((2:ℝ)^N)^(a+2000*(lam+sig)+12*lam) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (by positivity)
    _ = ((2:ℝ)^N)^(eps+(a+2000*(lam+sig)+12*lam)) := by
      rw [← Real.rpow_add (by positivity : 0 < (2:ℝ)^N)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (one_le_pow₀ (by norm_num)) (by linarith)

theorem uniform_actual_suffix_reduction {sig eps : ℝ} (hsig : 0 < sig)
    (heps : 0 < eps) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData, d.sig = sig → d.J = J →
      N₀ ≤ d.N → d.Q.side = 1 → d.StronglySeparated → 0 < d.q → 0 ≤ d.lam →
      d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i ≤ J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+4000*(d.lam+sig)+eps)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₁,h₁⟩ := uniform_suffix_reduction_explicit hsig hJ
  obtain ⟨N₂,h₂⟩ := uniform_suffix_coefficient_absorption hsig.le heps
  refine ⟨max N₁ N₂,?_⟩
  intro d hsig' hJ' hN hQ hs hq hlam hX hY B δ hprof hw htN hi A p hsuffix
  apply (h₁ d hsig' hJ' ((le_max_left _ _).trans hN) hQ hs hq hX hY B δ hprof hw htN hi hsuffix).trans
  apply mul_le_mul' _ le_rfl
  have hh := ENNReal.ofReal_le_ofReal (h₂ d.N ((le_max_right _ _).trans hN)
    (A p-intervalMin A p d.t) d.lam hlam)
  simpa only [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2255),ENNReal.ofReal_ofNat] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_SourceSuffixReduction
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem source_positive_distance_suffix_oai {lam sig kap eps : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap) (heps : 0 < eps) :
    ∃ N₀ : ℕ, ∀ d : PositiveDistanceData,
      d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
      d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 →
      d.StronglySeparated → d.X.length = d.a → d.Y.length = d.a →
      ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
      d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
      let A := fun n : ℕ => d.mass n-(n:ℝ)/(d.N:ℝ)
      let p := policyDepth A d.N d.q d.a d.t
      d.a+d.t < 2*p →
      d.coincidence ≤ ENNReal.ofReal (((2:ℝ)^d.N)^
        (A p-intervalMin A p d.t+4000*(lam+sig)+eps)) *
          ({d with t := p,i := d.i+1} : PositiveDistanceData).coincidence := by
  obtain ⟨N₀,hN₀⟩ := uniform_actual_suffix_reduction hsig heps
    (sourceSmoothingLevels_pos hsig hkap)
  refine ⟨N₀,?_⟩
  intro d hlam' hsig' hq' hJ' hN hQ hs hX hY B δ hprof hw htN hi A p hsuffix
  have hq : 0 < d.q := by
    rw [hq']
    exact sourcePolicyBlock_pos (by omega : 0 < d.N) hkap
  have hh := hN₀ d hsig' hJ' hN hQ hs hq (hlam' ▸ hlam) hX hY B δ hprof hw htN
    (by omega : d.i ≤ sourceSmoothingLevels sig kap) hsuffix
  simpa only [hlam'] using hh

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.source_positive_distance_suffix_oai := @OAI.PlanarFalconer.source_positive_distance_suffix_oai
