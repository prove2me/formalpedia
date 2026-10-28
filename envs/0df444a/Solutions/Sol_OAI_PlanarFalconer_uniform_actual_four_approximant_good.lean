-- Prove2me | solution 1 for OAI.PlanarFalconer.uniform_actual_four_approximant_good
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:15:35.874645+00:00
-- url     : https://prove2.me/submissions/d7bf00d9-eddc-45be-8013-9f8937003381

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

theorem stripCount_neg {ι : Type*} (S : Finset ι) (v : ι → Plane) (W : ℝ) (ω : Plane) :
    stripCount S v W (-ω) = stripCount S v W ω := by
  classical
  have he (i : ι) : planeDot (v i) (-ω) = -planeDot (v i) ω := by simp [planeDot]; ring
  simp only [stripCount,he,abs_neg]

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

theorem norm_quarterTurn (v : Plane) : ‖quarterTurn v‖ = ‖v‖ := by
  simpa using norm_quarterTurn_add 0 v

theorem quarterTurn_sub (v w : Plane) : quarterTurn (v-w) = quarterTurn v-quarterTurn w := by
  ext i
  fin_cases i <;> simp [quarterTurn]
  ring

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

theorem circleTestMask_angular_contDiff (G : Set UnitCircle) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (fun θ => circleTestMask G d hd (sourceUnitDirection θ)) := by
  simpa only [circleTestMask_comp] using sourceTestMask_contDiff G d hd

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

theorem spatialAnchorMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (n : ℕ)
    (G : CellPath → Set UnitCircle) (d : ℝ) (hd : 0 < d) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => spatialAnchorMask Q ρ n G d hd x (sourceUnitDirection θ)) := by
  by_cases hx : ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier
  · obtain ⟨P,hP,hx⟩ := hx
    simpa only [spatialAnchorMask_eq Q hQ ρ n G d hd hP hx] using circleTestMask_angular_contDiff (G P) d hd
  · push Not at hx
    simp only [spatialAnchorMask_zero Q ρ n G d hd hx]
    exact contDiff_const

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
-- module Solutions.OAIQ038_FA.Falconer_Fourier_SymbolProductBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

 theorem iteratedDeriv_tsupport {f : ℝ → ℝ} (j : ℕ) :
    tsupport (iteratedDeriv j f) ⊆ tsupport f := by
  induction j with
  | zero => simp
  | succ j ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

 theorem product_iteratedDeriv_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (f : ι → ℝ → ℝ) {b : ι} (hb : b ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (fun x => ∏ i ∈ S, f i x)) ⊆ tsupport (f b) := by
  apply (iteratedDeriv_tsupport j).trans
  have he : (fun x => ∏ i ∈ S, f i x) =
      fun x => f b x * ∏ i ∈ S.erase b, f i x := by
    funext x
    exact (Finset.mul_prod_erase S (fun i => f i x) hb).symm
  rw [he]
  exact tsupport_mul_subset_left

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem policyDescriptor_valid (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) (ht : t ≤ N)
    {b : PolicyDescriptor} (hb : b ∈ policyDescriptorList A N q a t) : ValidDescriptor N b := by
  obtain ⟨s,u,_,hut,_,_,hpos,_,hbound⟩ := policyDescriptor_origin A hq hb
  cases b <;> simp only [descriptorLength,descriptorAnchor,ValidDescriptor] at hpos hbound ⊢ <;> omega

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskSymmetry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Fourier_NormalizedSymbolFactors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

theorem smooth_iteratedDeriv {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (k : ℕ) :
    ContDiff ℝ ∞ (iteratedDeriv k f) := by
  induction k with
  | zero => simpa using hf
  | succ k ih => rw [iteratedDeriv_succ]; exact (contDiff_infty_iff_deriv.mp ih).2

 theorem normalizedMaskFactor_contDiff {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w)
    (d : ℝ) (k : ℕ) : ContDiff ℝ ∞ (normalizedMaskFactor w d k) :=
  contDiff_const.mul (smooth_iteratedDeriv hw k)

 theorem normalizedMaskFactor_support (w : ℝ → ℝ) (d : ℝ) (k : ℕ) :
    tsupport (normalizedMaskFactor w d k) ⊆ tsupport w :=
  tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedAngularSymbols
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem descriptorAngleMask_contDiff (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (b : PolicyDescriptor) (x : Plane) :
    ContDiff ℝ ∞ (descriptorAngleMask Q ρ m N lam sig J i b x) :=
  spatialAnchorMask_contDiff Q hQ _ _ _ _ _ _

 theorem inheritedMaskProduct_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) :
    ContDiff ℝ ∞ (inheritedMaskProduct S b k Q ρ m N lam sig J i x) := by
  apply contDiff_prod
  intro a _
  exact normalizedMaskFactor_contDiff (descriptorAngleMask_contDiff Q hQ ρ m N lam sig J i (b a) (x a)) _ _

 theorem inheritedMaskProduct_support {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ)
    (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) {a : ι} (ha : a ∈ S) (j : ℕ) :
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      tsupport (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a)) :=
  (product_iteratedDeriv_support S _ ha j).trans (normalizedMaskFactor_support _ _ _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_InheritedCircleRegularity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff Topology

 theorem periodic_iteratedDeriv {f : ℝ → ℝ} {p : ℝ} (hp : Function.Periodic f p) (j : ℕ) :
    Function.Periodic (iteratedDeriv j f) p := by
  have he : (fun x => f (x+p)) = f := funext hp
  have hh := iteratedDeriv_comp_add_const j f p
  rw [he] at hh
  intro x
  exact (congrFun hh x).symm

 theorem inheritedMaskProduct_periodic {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (x : ι → Plane) :
    Function.Periodic (inheritedMaskProduct S b k Q ρ m N lam sig J i x) Real.pi := by
  have hp a : Function.Periodic (descriptorAngleMask Q ρ m N lam sig J i (b a) (x a)) Real.pi := by
    intro θ
    exact (congrArg (descriptorSpatialMask Q ρ m N lam sig J i (b a) (x a))
      (sourceUnitDirection_add_pi θ)).trans (descriptorSpatialMask_antipodal _ _ _ _ _ _ _ _ _ _ _)
  intro θ
  apply Finset.prod_congr rfl
  intro a _
  unfold normalizedMaskFactor
  rw [periodic_iteratedDeriv (hp a) (k a) θ]

 theorem periodic_sourceAngle {f : ℝ → ℝ} (hf : Function.Periodic f (2*Real.pi)) (θ : ℝ) :
    f (sourceAngle (sourceUnitDirection θ)) = f θ := by
  rw [sourceAngle_sourceUnitDirection]
  have he := Complex.arg_cos_add_sin_mul_I_sub θ
  simp only [← Complex.ofReal_cos,← Complex.ofReal_sin] at he
  rw [sub_eq_iff_eq_add] at he
  rw [he]
  have hp := hf.int_mul ⌊(Real.pi-θ)/(2*Real.pi)⌋
  simpa only [mul_comm,add_comm] using hp θ

 theorem inheritedCircleSymbol_comp {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) (θ : ℝ) :
    inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ) =
      h x * (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x) θ : ℂ) := by
  have hp := (inheritedMaskProduct_periodic S b k Q ρ m N lam sig J i (fun _ => x)).nat_mul 2
  have hp' : Function.Periodic (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x))
      (2*Real.pi) := by simpa using hp
  unfold inheritedCircleSymbol
  rw [periodic_sourceAngle hp']

 theorem inheritedCircleSymbol_contDiff {ι : Type*} (S : Finset ι) (b : ι → PolicyDescriptor)
    (k : ι → ℕ) (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane) (m : ℝ → ℝ)
    (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    ContDiff ℝ ∞ (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) := by
  simp only [inheritedCircleSymbol_comp]
  exact contDiff_const.mul (Complex.ofRealCLM.contDiff.comp
    (inheritedMaskProduct_contDiff S b k Q hQ ρ m N lam sig J i (fun _ => x)))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationarySineChart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

 theorem stationarySineInverse_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineInverse u := by
  have hi : ContDiffAt ℝ ∞ (fun x : ℝ => x/2) u := contDiffAt_id.div_const 2
  have hh : ContDiffAt ℝ ∞ Real.arcsin (u/2) :=
    Real.contDiffAt_arcsin (by linarith [hu.1]) (by linarith [hu.2])
  have ht : ContDiffAt ℝ ∞ (fun x : ℝ => Real.arcsin (x/2)) u :=
    ContDiffAt.comp (f := fun x : ℝ => x/2) (g := Real.arcsin) u hh hi
  exact contDiffAt_const.mul ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryChartCutoffs
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff Topology

 theorem stationaryCutoff_tsupport : tsupport (stationaryCutoff : ℝ → ℝ) = Icc (-1:ℝ) 1 := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryCutoff]

 theorem stationaryChartCutoff_tsupport :
    tsupport (stationaryChartCutoff : ℝ → ℝ) = Icc (-3/2:ℝ) (3/2) := by
  rw [ContDiffBump.tsupport_eq,Real.closedBall_eq_Icc]
  norm_num [stationaryChartCutoff]

 theorem stationaryChartCutoff_one {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    stationaryChartCutoff u = 1 := by
  apply ContDiffBump.one_of_mem_closedBall
  simpa [Real.closedBall_eq_Icc,stationaryChartCutoff] using hu

 theorem contDiff_localized_real {χ f : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hf : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ f x) :
    ContDiff ℝ ∞ (fun x => χ x * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.mul (hf x hx)
  · have he : (fun y => χ y * f y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hx] with y hy
      simp only [image_eq_zero_of_notMem_tsupport hy,zero_mul]
    exact contDiffAt_const.congr_of_eventuallyEq he

 theorem stationarySineJacobian_contDiffAt {u : ℝ} (hu : u ∈ Ioo (-2:ℝ) 2) :
    ContDiffAt ℝ ∞ stationarySineJacobian u := by
  have hp : 0 < 1-u^2/4 := by nlinarith [hu.1,hu.2]
  have hf : ContDiffAt ℝ ∞ (fun u : ℝ => 1-u^2/4) u :=
    contDiffAt_const.sub ((contDiffAt_id.pow 2).div_const 4)
  exact (hf.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'

 theorem extendedStationaryInverse_contDiff : ContDiff ℝ ∞ extendedStationaryInverse := by
  apply contDiff_localized_real stationaryChartCutoff.contDiff
  intro u hu
  rw [stationaryChartCutoff_tsupport] at hu
  exact stationarySineInverse_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem stationaryWeight_contDiff : ContDiff ℝ ∞ stationaryWeight := by
  apply contDiff_localized_real stationaryCutoff.contDiff
  intro u hu
  rw [stationaryCutoff_tsupport] at hu
  exact stationarySineJacobian_contDiffAt ⟨by linarith [hu.1],by linarith [hu.2]⟩

 theorem extendedStationaryInverse_eq {u : ℝ} (hu : u ∈ Icc (-1:ℝ) 1) :
    extendedStationaryInverse u = stationarySineInverse u := by
  simp [extendedStationaryInverse,stationaryChartCutoff_one hu]

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

 theorem uniform_inheritedMaskProduct_support {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (x : ι → Plane) (j : ℕ),
    ∀ a ∈ S, ValidDescriptor N (b a) → ∀ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)),
    x a ∈ (Q.descendant P).carrier →
    tsupport (iteratedDeriv j (inheritedMaskProduct S b k Q ρ m N lam sig J i x)) ⊆
      sourceUnitDirection ⁻¹' descriptorGoodSet Q ρ m N lam sig J (i+1) P (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_descriptorAngleMask_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i x j a ha hb P hP hx
  exact (inheritedMaskProduct_support S b k Q ρ m N lam sig J i x ha j).trans
    (h₀ N hN Q hQ ρ m lam i (b a) hb P hP (x a) hx)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology

namespace AngularDifferentialExpr

theorem sum_apply (ps : List AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (sum ps).apply f x = (ps.map (fun p => p.apply f x)).sum := by
  induction ps with
  | nil => simp [sum, apply]
  | cons p ps ih => simp [sum, apply, ih]

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularDifferentialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff Topology
namespace AngularDifferentialExpr

theorem iteratedDeriv_tsupport (k : ℕ) (f : ℝ → ℂ) :
    tsupport (iteratedDeriv k f) ⊆ tsupport f := by
  induction k with
  | zero => simp
  | succ k ih => rw [iteratedDeriv_succ]; exact tsupport_deriv_subset.trans ih

theorem apply_tsupport (p : AngularDifferentialExpr) (f : ℝ → ℂ) :
    tsupport (p.apply f) ⊆ tsupport f := by
  induction p generalizing f with
  | term c k => exact tsupport_mul_subset_right.trans (iteratedDeriv_tsupport k f)
  | add p q hp hq => exact (tsupport_add (p.apply f) (q.apply f)).trans (Set.union_subset (hp f) (hq f))
  | comp p q hp hq => exact (hp (q.apply f)).trans (hq f)

end AngularDifferentialExpr
end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryJetOperators
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem extendedStationaryInverse_zero : extendedStationaryInverse 0 = 0 := by
  rw [extendedStationaryInverse_eq (by norm_num)]
  simp [stationarySineInverse]

 theorem stationaryAmplitude_jet (n : ℕ) {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    iteratedDeriv n (stationaryAmplitude f) 0 = stationaryJet n f := by
  have hw : ContDiff ℝ ∞ (fun u => (stationaryWeight u : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp stationaryWeight_contDiff
  have hfn : ContDiffAt ℝ n (f ∘ extendedStationaryInverse) 0 :=
    ((hf.comp extendedStationaryInverse_contDiff).of_le
      (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  have hwn : ContDiffAt ℝ n (fun u => (stationaryWeight u : ℂ)) 0 :=
    (hw.of_le (by exact_mod_cast (le_top : (n:ℕ∞) ≤ ⊤))).contDiffAt
  change iteratedDeriv n (fun u => (stationaryWeight u : ℂ) *
    (f ∘ extendedStationaryInverse) u) 0 = _
  rw [iteratedDeriv_fun_mul hwn hfn]
  unfold stationaryJet
  apply Finset.sum_congr rfl
  intro k hk
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hf.contDiffAt
    extendedStationaryInverse_contDiff.contDiffAt
      (WithTop.coe_le_coe.mpr (show ((n-k:ℕ):ℕ∞) ≤ ⊤ from le_top))]
  simp only [extendedStationaryInverse_zero,Complex.real_smul]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryDifferentialExpr
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

theorem angularFiniteSum_apply {α : Type*} (s : Finset α)
    (p : α → AngularDifferentialExpr) (f : ℝ → ℂ) (x : ℝ) :
    (angularFiniteSum s p).apply f x = ∑ a ∈ s, (p a).apply f x := by
  simp [angularFiniteSum, AngularDifferentialExpr.sum_apply, List.map_map,
    Finset.sum_map_toList, Function.comp_def]

theorem stationaryJetExpr_apply (n : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (stationaryJetExpr n).apply f x = stationaryJet n (fun u => f (u+x)) := by
  simp only [stationaryJetExpr, angularFiniteSum_apply, AngularDifferentialExpr.apply,
    stationaryJet, iteratedDeriv_comp_add_const, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

theorem directStationaryExpr_apply (j : ℕ) (f : ℝ → ℂ) (x : ℝ) :
    (directStationaryExpr j).apply f x = directStationaryOperator j f x := by
  simp [directStationaryExpr, AngularDifferentialExpr.apply, stationaryJetExpr_apply,
    directStationaryOperator, stationaryLeadingConstant]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleDirectCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff

 theorem fresnelCoefficient_half {Λ : ℝ} (hΛ : 0 < Λ) :
    fresnelCoefficient (Λ/2) = ((Λ^(-1/2:ℝ):ℝ):ℂ) *
      ((Real.sqrt (2*Real.pi):ℂ)*Complex.exp (-(Real.pi:ℂ)/4*Complex.I)) := by
  have he : Real.pi/(Λ/2) = (2*Real.pi)/Λ := by ring
  have hp : (Real.pi/(Λ/2))^(1/2:ℝ) = Λ^(-1/2:ℝ)*Real.sqrt (2*Real.pi) := by
    rw [he,Real.div_rpow (by positivity) hΛ.le,Real.sqrt_eq_rpow]
    rw [show (-1/2:ℝ) = -(1/2:ℝ) by ring,Real.rpow_neg hΛ.le]
    ring
  simp only [fresnelCoefficient,hp,Complex.ofReal_mul]
  ring

 theorem quadratic_coefficient_normalization (k : ℕ) {Λ : ℝ} (hΛ : 0 < Λ) (d : ℂ) :
    ((((k.factorial:ℝ)⁻¹*(Real.pi^2/(Λ/2))^k):ℝ):ℂ)*Complex.I^k *
      (((-2*(Real.pi:ℂ)*Complex.I)^(2*k))⁻¹*d) =
    ((Λ⁻¹:ℝ):ℂ)^k * (((k.factorial:ℝ)⁻¹:ℝ):ℂ) * (-Complex.I/2)^k*d := by
  have hp : (Real.pi:ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hΛ' : (Λ:ℂ) ≠ 0 := by exact_mod_cast hΛ.ne'
  have he : (((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹) =
      ((Λ⁻¹:ℝ):ℂ)*(-Complex.I/2) := by
    push_cast
    field_simp
    simp [Complex.I_sq]
  calc
    _ = (((k.factorial:ℝ)⁻¹:ℝ):ℂ) *
        ((((Real.pi^2/(Λ/2):ℝ):ℂ)*Complex.I*((-2*(Real.pi:ℂ)*Complex.I)^2)⁻¹)^k) * d := by
      simp only [Complex.ofReal_mul,Complex.ofReal_pow,mul_pow,inv_pow,pow_mul]
      ring
    _ = _ := by rw [he,mul_pow]; ring

 theorem stationary_expansion_direct_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fresnelCoefficient (Λ/2) * stationaryDerivativeExpansion f n Λ =
      ((Λ^(-1/2:ℝ):ℝ):ℂ) * ∑ j ∈ Finset.range (n+1),
        ((Λ⁻¹:ℝ):ℂ)^j * directStationaryOperator j f 0 := by
  rw [fresnelCoefficient_half hΛ,stationaryDerivativeExpansion,mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [quadratic_coefficient_normalization j hΛ,stationaryAmplitude_jet (2*j) hf]
  simp only [directStationaryOperator,add_zero]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FullCircleStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_operators {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*directStationaryOperator j f 0) +
      conj (Complex.exp (Complex.I*(Λ:ℂ))*((Λ^(-1/2:ℝ):ℝ):ℂ)*
        (∑ j ∈ Finset.range (n+1), ((Λ⁻¹:ℝ):ℂ)^j*
          directStationaryOperator j (fun θ => conj (f (θ+Real.pi))) 0)) := by
  have hfs : ContDiff ℝ ∞ (fun θ => conj (f (θ+Real.pi))) :=
    Complex.conjCLE.contDiff.comp (hf.comp (contDiff_id.add contDiff_const))
  unfold fullCircleStationaryExpansion
  rw [stationary_expansion_direct_operators hΛ hf,stationary_expansion_direct_operators hΛ hfs]
  simp only [mul_assoc]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_SignedStationaryExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open scoped ContDiff ComplexConjugate

 theorem fullCircleStationaryExpansion_signed {Λ : ℝ} (hΛ : 0 < Λ)
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm true j f Λ) +
      (∑ j ∈ Finset.range (n+1), signedStationaryTerm false j f Λ) := by
  rw [fullCircleStationaryExpansion_operators hΛ hf]
  simp only [signedStationaryTerm,stationarySign,signedStationaryJet,normalizedStationaryJet,
    ↓reduceIte,Bool.false_eq_true,one_mul,neg_one_mul,
    map_mul,map_sum,map_pow,Complex.conj_ofReal,← Complex.exp_conj,Complex.conj_I,
    Complex.ofReal_neg,Finset.mul_sum,mul_assoc]
  simp [neg_mul,mul_neg]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryProductIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem fullCircleStationaryExpansion_sum {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f)
    {Λ : ℝ} (hΛ : 0 < Λ) (n : ℕ) :
    fullCircleStationaryExpansion Λ f n =
      ∑ p ∈ stationarySignedIndices n, signedStationaryTerm p.1 p.2 f Λ := by
  rw [fullCircleStationaryExpansion_signed hΛ hf]
  simp [stationarySignedIndices,Finset.sum_product,add_comm]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryPairSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate Topology

 theorem normalizedStationaryJet_support (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ)
    (hn : normalizedStationaryJet j f θ Λ ≠ 0) : θ ∈ tsupport f := by
  have hd : directStationaryOperator j f θ ≠ 0 := by
    intro hz
    exact hn (by simp [normalizedStationaryJet,hz])
  apply (directStationaryExpr j).apply_tsupport f
  apply subset_tsupport
  simpa only [Function.mem_support,directStationaryExpr_apply] using hd

 theorem signedStationaryJet_support (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ)
    (hn : signedStationaryJet plus j f θ Λ ≠ 0) :
    (if plus then θ else θ+Real.pi) ∈ tsupport f := by
  cases plus
  · simp only [signedStationaryJet,Bool.false_eq_true,↓reduceIte,map_ne_zero] at hn
    have hh := normalizedStationaryJet_support j (fun t => conj (f (t+Real.pi))) θ Λ hn
    have hc : tsupport (fun t => conj (f (t+Real.pi))) ⊆ tsupport (fun t => f (t+Real.pi)) :=
      tsupport_comp_subset (show conj (0:ℂ) = 0 by simp) _
    exact tsupport_comp_subset_preimage f (continuous_id.add continuous_const) (hc hh)
  · simp only [signedStationaryJet,↓reduceIte] at hn ⊢
    exact normalizedStationaryJet_support j f θ Λ hn

 theorem inheritedCircleSymbol_mask_support {ι : Type*} (S : Finset ι)
    (b : ι → PolicyDescriptor) (k : ι → ℕ) (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (h : Plane → ℂ) (x : Plane) :
    tsupport (fun θ => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection θ)) ⊆
      tsupport (inheritedMaskProduct S b k Q ρ m N lam sig J i (fun _ => x)) := by
  apply closure_mono
  intro θ ht
  simp only [Function.mem_support,inheritedCircleSymbol_comp] at ht ⊢
  intro hz
  exact ht (by simp [hz])

 theorem pair_tsupport_left_right (f g : ℝ → ℂ) :
    tsupport (fun t => f t*conj (g t)) ⊆ tsupport f ∩ tsupport g := by
  exact subset_inter tsupport_mul_subset_left
    (tsupport_mul_subset_right.trans (tsupport_comp_subset (show conj (0:ℂ) = 0 by simp) g))

 theorem uniform_actual_pair_jet_good {sig : ℝ} (hsig : 0 < sig) {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ {ι : Type} [DecidableEq ι],
    ∀ (S : Finset ι) (b : ι → PolicyDescriptor) (k : ι → ℕ),
    ∀ Q : DyadicSquare, Q.side = 1 → ∀ (ρ : Measure Plane) (m : ℝ → ℝ)
    (lam : ℝ) (i : ℕ) (h : Plane → ℂ) (x y : Plane) (plus : Bool) (j : ℕ) (θ Λ : ℝ),
    let f := fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection t) *
      conj (inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection t))
    signedStationaryJet plus j f θ Λ ≠ 0 →
    ∀ a ∈ S, ValidDescriptor N (b a) →
    ∀ Px Py : CellPath,
    Px ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)) →
    Py ∈ occupiedAnchorPaths Q ρ (descriptorAnchor (b a)) →
    x ∈ (Q.descendant Px).carrier → y ∈ (Q.descendant Py).carrier →
    sourceUnitDirection θ ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) Px (b a) ∧
    sourceUnitDirection θ ∈ descriptorGoodSet Q ρ m N lam sig J (i+1) Py (b a) := by
  obtain ⟨N₀,h₀⟩ := uniform_inheritedMaskProduct_support hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN ι inst S b k Q hQ ρ m lam i h x y plus j θ Λ f hn a ha hb Px Py hPx hPy hx hy
  have ht := signedStationaryJet_support plus j f θ Λ hn
  have hpair := pair_tsupport_left_right
    (fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h x (sourceUnitDirection t))
    (fun t => inheritedCircleSymbol S b k Q ρ m N lam sig J i h y (sourceUnitDirection t)) ht
  have hmx := inheritedCircleSymbol_mask_support S b k Q ρ m N lam sig J i h x hpair.1
  have hmy := inheritedCircleSymbol_mask_support S b k Q ρ m N lam sig J i h y hpair.2
  have hgx := h₀ N hN S b k Q hQ ρ m lam i (fun _ => x) 0 a ha hb Px hPx hx
  have hgy := h₀ N hN S b k Q hQ ρ m lam i (fun _ => y) 0 a ha hb Py hPy hy
  simp only [iteratedDeriv_zero] at hgx hgy
  have hh := And.intro (hgx hmx) (hgy hmy)
  change sourceUnitDirection (if plus then θ else θ+Real.pi) ∈
      descriptorGoodSet Q ρ m N lam sig J (i+1) Px (b a) ∧
    sourceUnitDirection (if plus then θ else θ+Real.pi) ∈
      descriptorGoodSet Q ρ m N lam sig J (i+1) Py (b a) at hh
  cases plus
  · simpa only [Bool.false_eq_true,↓reduceIte,sourceUnitDirection_add_pi,
      descriptorGoodSet_antipodal] using hh
  · simpa only [↓reduceIte] using hh

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_InheritedPolicyState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

 theorem policyDescriptor_anchor_gt_left (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q)
    {d : PolicyDescriptor} (hd : d ∈ policyDescriptorList A N q a t) : a < descriptorAnchor d := by
  obtain ⟨z,hz,hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨hz,ha,_,hwide⟩ := Finset.mem_filter.mp hz
  have huN : z.2 ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  rw [originDescriptor_anchor A hd]
  omega

 theorem minimal_policy_list_survives (A : ℕ → ℝ) {N q a₀ t₀ a b v : ℕ}
    (hq : 0 < q) (hleft : a₀ ≤ b) (hright : v ≤ t₀) (hdepth : a ≤ b) :
    policyDescriptorList A N q b v ⊆ remainingPolicyDescriptors A N q a₀ t₀ a := by
  intro d hd
  exact Finset.mem_filter.mpr ⟨policyDescriptorList_mono A hleft hright hd,
    hdepth.trans_lt (policyDescriptor_anchor_gt_left A hq hd)⟩

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

theorem uniform_actual_pair_minimal_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
    ∀ (ρ : Measure Plane) [SFinite ρ], ρ Q.carrierᶜ = 0 →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Finset PolicyDescriptor) (k : PolicyDescriptor → ℕ),
    remainingPolicyDescriptors (fun n => m n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S →
    ∀ (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ᵐ z ∂ρ.prod ρ, ∀ (plus : Bool) (j : ℕ) (θ Λ : ℝ),
    sourceRadialUnit z.2 z.1 = sourceUnitDirection θ →
    signedStationaryJet plus j
      (fun t => inheritedCircleSymbol S id k Q ρ m N lam sig J i h z.1 (sourceUnitDirection t) *
        conj (inheritedCircleSymbol S id k Q ρ m N lam sig J i h z.2 (sourceUnitDirection t))) θ Λ ≠ 0 →
    z ∈ positiveDistanceGoodSet Q ρ m N q b v lam sig J (i+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_jet_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h
  have hmin := (minimal_policy_list_survives (fun n => m n-(n:ℝ)/(N:ℝ))
    hq hl hr hab).trans hS
  filter_upwards [ae_all_occupied_pair Q ρ hcarry] with z hz
  intro plus j θ Λ hdir hn d hd
  obtain ⟨⟨Px,hPx,hx⟩,⟨Py,hPy,hy⟩⟩ := hz (descriptorAnchor d)
  have hg := h₀ N hN S id k Q hQ ρ m lam i h z.1 z.2 plus j θ Λ hn d (hmin hd)
    (policyDescriptor_valid _ hq hv hd) Px Py hPx hPy hx hy
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  rw [← hdir] at hg
  exact ⟨endpointDescriptorGood_of_occupied Q hQpos ρ m N lam sig J (i+1) d z.1 _ Px hPx hx hg.1,
    endpointDescriptorGood_of_occupied Q hQpos ρ m N lam sig J (i+1) d z.2 _ Py hPy hy hg.2⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_StationaryApproximantSupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff ComplexConjugate

theorem signedStationaryJet_comp_add_const (plus : Bool) (j : ℕ) (f : ℝ → ℂ) (θ Λ : ℝ) :
    signedStationaryJet plus j (fun t => f (t+θ)) 0 Λ = signedStationaryJet plus j f θ Λ := by
  cases plus <;> simp only [signedStationaryJet,normalizedStationaryJet,directStationaryOperator,
    Bool.false_eq_true,↓reduceIte,add_zero]
  congr 3
  congr 1
  funext t
  rw [add_right_comm]

theorem angularPairStationary_eq_zero_of_jets (β : Plane → UnitCircle → ℂ)
    (x y : Plane) (hd : 0 < ‖x-y‖) (r : ℝ) (hr : 0 < r) (n : ℕ)
    (hβ : ∀ z, ContDiff ℝ ∞ (fun t => β z (sourceUnitDirection t)))
    (hz : ∀ plus j, signedStationaryJet plus j
      (fun t => β x (sourceUnitDirection t)*conj (β y (sourceUnitDirection t)))
      (angularPairAngle x y) (r*‖x-y‖) = 0) :
    angularPairStationary β n x y r = 0 := by
  let f := fun t => β x (sourceUnitDirection t)*conj (β y (sourceUnitDirection t))
  have hf : ContDiff ℝ ∞ f := (hβ x).mul (Complex.conjCLE.contDiff.comp (hβ y))
  change fullCircleStationaryExpansion (r*‖x-y‖) (fun t => f (t+angularPairAngle x y)) n = 0
  rw [fullCircleStationaryExpansion_sum
    (show ContDiff ℝ ∞ (fun t => f (t+angularPairAngle x y)) from
      hf.comp (contDiff_id.add contDiff_const)) (mul_pos hr hd)]
  apply Finset.sum_eq_zero
  intro pair _
  simp only [signedStationaryTerm,signedStationaryJet_comp_add_const]
  rw [show signedStationaryJet pair.1 pair.2 f (angularPairAngle x y) (r*‖x-y‖) = 0 from hz _ _]
  exact mul_zero _

theorem uniform_actual_pair_approximant_good {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicSquare), Q.side = 1 →
    ∀ (ρ : Measure Plane) [SFinite ρ], ρ Q.carrierᶜ = 0 →
    ∀ (m : ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Finset PolicyDescriptor) (k : PolicyDescriptor → ℕ),
    remainingPolicyDescriptors (fun n => m n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S →
    ∀ (lam : ℝ) (i : ℕ) (h : Plane → ℂ),
    ∀ᵐ z ∂ρ.prod ρ, ∀ (n : ℕ) (r : ℝ), 0 < r → z.1 ≠ z.2 →
    angularPairStationary (inheritedCircleSymbol S id k Q ρ m N lam sig J i h) n z.1 z.2 r ≠ 0 →
    z ∈ positiveDistanceGoodSet Q ρ m N q b v lam sig J (i+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_minimal_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ _ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h
  filter_upwards [h₀ N hN Q hQ ρ hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h]
    with z hz
  intro n r hpos hne hn
  by_contra hbad
  apply hn
  apply angularPairStationary_eq_zero_of_jets _ _ _ (norm_pos_iff.mpr (sub_ne_zero.mpr hne)) r hpos n
    (inheritedCircleSymbol_contDiff _ _ _ _ (by rw [hQ]; norm_num) _ _ _ _ _ _ _ _)
  intro plus j
  by_contra hj
  apply hbad
  exact hz plus j (angularPairAngle z.1 z.2) _
    (sourceUnitDirection_sourceAngle (sourceRadialUnit z.2 z.1)).symm hj

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_FourSpatialPairMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem measurePreserving_fourSpatialPair (μ : Fin 4 → Measure Plane)
    [∀ i, IsFiniteMeasure (μ i)] :
    MeasurePreserving fourSpatialPairEquiv (Measure.pi μ)
      ((μ 0).prod (μ 1) |>.prod ((μ 2).prod (μ 3))) := by
  apply MeasurePreserving.symm fourSpatialPairEquiv.symm
  refine ⟨fourSpatialPairEquiv.symm.measurable, (Measure.pi_eq fun s hs => ?_).symm⟩
  rw [Measure.map_apply fourSpatialPairEquiv.symm.measurable (MeasurableSet.univ_pi hs)]
  have he : fourSpatialPairEquiv.symm ⁻¹' Set.pi univ s =
      (s 0 ×ˢ s 1) ×ˢ (s 2 ×ˢ s 3) := by
    ext z
    simp only [mem_preimage,mem_pi,mem_univ,true_implies,mem_prod]
    constructor
    · intro h
      exact ⟨⟨h 0,h 1⟩,⟨h 2,h 3⟩⟩
    · intro h i
      fin_cases i
      · exact h.1.1
      · exact h.1.2
      · exact h.2.1
      · exact h.2.2
  rw [he,Measure.prod_prod,Measure.prod_prod,Measure.prod_prod,Fin.prod_univ_four]
  ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_FourStationarySupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem pair_ae_four_restrictions (ρ ν : Measure Plane) [IsFiniteMeasure ρ] [IsFiniteMeasure ν]
    (X : Fin 4 → Set Plane) (P Q : Plane × Plane → Prop)
    (hP : ∀ᵐ z ∂ρ.prod ρ, P z) (hQ : ∀ᵐ z ∂ν.prod ν, Q z) :
    ∀ᵐ x ∂Measure.pi (fun i => (![ρ,ρ,ν,ν] i).restrict (X i)),
      P (x 0,x 1) ∧ Q (x 2,x 3) := by
  let μ : Fin 4 → Measure Plane := fun i => (![ρ,ρ,ν,ν] i).restrict (X i)
  let : ∀ i, IsFiniteMeasure (μ i) := by
    intro i; fin_cases i <;> dsimp [μ] <;> infer_instance
  have hP' : ∀ᵐ z ∂(μ 0).prod (μ 1), P z :=
    (ae_mono (Measure.prod_mono (μ' := ρ) (ν' := ρ) Measure.restrict_le_self Measure.restrict_le_self)) hP
  have hQ' : ∀ᵐ z ∂(μ 2).prod (μ 3), Q z :=
    (ae_mono (Measure.prod_mono (μ' := ν) (ν' := ν) Measure.restrict_le_self Measure.restrict_le_self)) hQ
  have hpq : ∀ᵐ z ∂((μ 0).prod (μ 1)).prod ((μ 2).prod (μ 3)), P z.1 ∧ Q z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hP',
      Measure.quasiMeasurePreserving_snd.ae hQ'] with z hz₁ hz₂
    exact ⟨hz₁,hz₂⟩
  exact (measurePreserving_fourSpatialPair μ).quasiMeasurePreserving.ae hpq

theorem stationary_spatial_good_of_pair_good (β γ : Plane → UnitCircle → ℂ)
    (G H : Set (Plane × Plane)) (x : Fin 4 → Plane)
    (hβ : ∀ n r, 0 < r → x 0 ≠ x 1 → angularPairStationary β n (x 0) (x 1) r ≠ 0 → (x 0,x 1) ∈ G)
    (hγ : ∀ n r, 0 < r → x 2 ≠ x 3 → angularPairStationary γ n (x 2) (x 3) r ≠ 0 → (x 2,x 3) ∈ H)
    {Ψ : ℝ → ℝ} (hs : ∀ t, Ψ t ≠ 0 → 0 < t) (n : ℕ) (v : ℝ)
    (hx : x 0 ≠ x 1) (hy : x 2 ≠ x 3)
    (hn : angularStationarySpatialKernel β γ n v Ψ x ≠ 0) :
    (x 0,x 1) ∈ G ∧ (x 2,x 3) ∈ H := by
  by_contra hbad
  apply hn
  unfold angularStationarySpatialKernel
  have hz : (∫ r : ℝ, Ψ (r/(2:ℝ)^v) •
      (angularPairStationary β n (x 0) (x 1) r * angularPairStationary γ n (x 2) (x 3) r)) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with r
    by_cases hp : Ψ (r/(2:ℝ)^v) = 0
    · simp [hp]
    · have hr : 0 < r := (div_pos_iff.mp (hs _ hp)).resolve_right (fun hz => (not_lt_of_ge (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) v)) hz.2) |>.1
      by_contra hne
      apply hbad
      constructor
      · apply hβ n r hr hx
        intro hz
        exact hne (by simp [hz])
      · apply hγ n r hr hy
        intro hz
        exact hne (by simp [hz])
  rw [hz,smul_zero]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualFourStationarySupport
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory

theorem uniform_actual_four_approximant_good_oai {sig : ℝ} (hsig : 0 < sig)
    {J : ℕ} (hJ : 0 < J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : Fin 2 → DyadicSquare), (∀ l, (Q l).side = 1) →
    ∀ (ρ : Fin 2 → Measure Plane) [∀ l, IsFiniteMeasure (ρ l)],
    (∀ l, ρ l (Q l).carrierᶜ = 0) →
    ∀ (m : Fin 2 → ℝ → ℝ) (q a₀ t₀ a b v : ℕ), 0 < q → a₀ ≤ b → v ≤ t₀ →
    a ≤ b → v ≤ N →
    ∀ (S : Fin 2 → Finset PolicyDescriptor) (k : Fin 2 → PolicyDescriptor → ℕ),
    (∀ l, remainingPolicyDescriptors (fun n => m l n-(n:ℝ)/(N:ℝ)) N q a₀ t₀ a ⊆ S l) →
    ∀ (lam : Fin 2 → ℝ) (i : Fin 2 → ℕ) (h : Fin 2 → Plane → ℂ) (X : Fin 4 → Set Plane),
    let β := fun l => inheritedCircleSymbol (S l) id (k l) (Q l) (ρ l) (m l) N (lam l) sig J (i l) (h l)
    ∀ᵐ x ∂Measure.pi (fun j => (![ρ 0,ρ 0,ρ 1,ρ 1] j).restrict (X j)),
    ∀ (n : ℕ) (w : ℝ) (Ψ : ℝ → ℝ), (∀ t, Ψ t ≠ 0 → 0 < t) →
    x 0 ≠ x 1 → x 2 ≠ x 3 → angularStationarySpatialKernel (β 0) (β 1) n w Ψ x ≠ 0 →
    (x 0,x 1) ∈ positiveDistanceGoodSet (Q 0) (ρ 0) (m 0) N q b v (lam 0) sig J (i 0+1) ∧
    (x 2,x 3) ∈ positiveDistanceGoodSet (Q 1) (ρ 1) (m 1) N q b v (lam 1) sig J (i 1+1) := by
  obtain ⟨N₀,h₀⟩ := uniform_actual_pair_approximant_good hsig hJ
  refine ⟨N₀,?_⟩
  intro N hN Q hQ ρ inst hcarry m q a₀ t₀ a b v hq hl hr hab hv S k hS lam i h X
  have hp (l : Fin 2) := h₀ N hN (Q l) (hQ l) (ρ l) (hcarry l) (m l)
    q a₀ t₀ a b v hq hl hr hab hv (S l) (k l) (hS l) (lam l) (i l) (h l)
  have hh := pair_ae_four_restrictions (ρ 0) (ρ 1) X _ _ (hp 0) (hp 1)
  filter_upwards [hh] with x hx
  intro n w Ψ hs hx₁ hx₂ hn
  exact stationary_spatial_good_of_pair_good _ _ _ _ x hx.1 hx.2 hs n w hx₁ hx₂ hn

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.uniform_actual_four_approximant_good_oai := @OAI.PlanarFalconer.uniform_actual_four_approximant_good_oai
