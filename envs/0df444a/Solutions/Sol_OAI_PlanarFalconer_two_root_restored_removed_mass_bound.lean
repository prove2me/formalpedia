-- Prove2me | solution 1 for OAI.PlanarFalconer.two_root_restored_removed_mass_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:26:38.568931+00:00
-- url     : https://prove2.me/submissions/4d90a1bc-8493-431b-9ad6-55c410cb493f

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
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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

theorem smoothAngleMask_eq_one (G : Set ℝ) (η : ℝ) (hη : 0 < η) {x : ℝ} (hx : x ∈ G) :
    smoothAngleMask G η hη x = 1 := by
  have hi : thickenedIndicator G η x = 1 := by
    apply Set.indicator_of_mem
    exact mem_thickening_iff.mpr ⟨x,hx,by simpa using mul_pos (by norm_num : (0:ℝ)<2) hη⟩
  rw [smoothAngleMask,← hi]
  apply ContDiffBump.normed_convolution_eq_right
  intro y hy
  rw [hi]
  apply Set.indicator_of_mem
  apply mem_thickening_iff.mpr
  refine ⟨x,hx,?_⟩
  change dist y x < η at hy
  linarith

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

theorem continuous_quarterTurn : Continuous quarterTurn := by
  unfold quarterTurn
  fun_prop

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
-- module Solutions.OAIQ038_FA.Falconer_Angular_AngularWidths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem sourceAngularWidth_zero (N : ℕ) (sig : ℝ) (J n : ℕ) :
    sourceAngularWidth N sig J 0 n = 2/(2:ℝ)^n*((2:ℝ)^N)^(1000*sig) := by
  simp [sourceAngularWidth]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_ActualAngleMasks
attribute [-instance] _root_.OAI.PlanarFalconer.unitCircle_compactSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff Topology

theorem sourceTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {θ : ℝ} (hθ : sourceUnitDirection θ ∈ G) : sourceTestMask G d hd θ = 1 :=
  smoothAngleMask_eq_one _ _ _ hθ

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

theorem circleTestMask_eq_one (G : Set UnitCircle) (d : ℝ) (hd : 0 < d)
    {dir : UnitCircle} (hdir : dir ∈ G) : circleTestMask G d hd dir = 1 := by
  apply sourceTestMask_eq_one
  simpa only [sourceUnitDirection_sourceAngle] using hdir

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

theorem circleTestMask_failure_le (G : Set UnitCircle) (hG : MeasurableSet G)
    (d : ℝ) (hd : 0 < d) :
    sourceArcLength {dir | circleTestMask G d hd dir ≠ 1} ≤ sourceArcLength Gᶜ := by
  rw [measure_eq_iInf {dir | circleTestMask G d hd dir ≠ 1}]
  refine iInf_le_of_le Gᶜ (iInf_le_of_le ?_ (iInf_le_of_le hG.compl le_rfl))
  intro dir hdir hmem
  exact hdir (circleTestMask_eq_one G d hd hmem)

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

theorem originDescriptors_card (A : ℕ → ℝ) {N q b u : ℕ} (hq : 0 < q)
    (huN : u ≤ N) (hwide : b+100*q < u) : (originDescriptors A N q b u).card ≤ N+1 := by
  classical
  have hp := policyDepth_interior A hq (policyBlocks_nonempty hq huN hwide)
  unfold originDescriptors
  apply (Finset.card_union_le _ _).trans
  have hfirst : ((Finset.Ico (policyDepth A N q b u-min (policyDepth A N q b u-b)
      (u-policyDepth A N q b u)) (policyDepth A N q b u)).image
      (fun g => PolicyDescriptor.parallel g (policyDepth A N q b u))).card ≤ N := by
    apply Finset.card_image_le.trans
    rw [Nat.card_Ico]
    omega
  split_ifs <;> simp only [Finset.card_singleton,Finset.card_empty] <;> omega

theorem policyDescriptorList_card (A : ℕ → ℝ) {N q a t : ℕ} (hq : 0 < q) :
    (policyDescriptorList A N q a t).card ≤ (N+1)^3 := by
  classical
  calc
    _ ≤ ∑ z ∈ policyOrigins N q a t, (originDescriptors A N q z.1 z.2).card := Finset.card_biUnion_le
    _ ≤ ∑ _z ∈ policyOrigins N q a t, (N+1) := by
      apply Finset.sum_le_sum
      intro z hz
      obtain ⟨hz,_,_,hwide⟩ := Finset.mem_filter.mp hz
      have huN := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_product.mp hz).2)
      exact originDescriptors_card A hq huN hwide
    _ = (policyOrigins N q a t).card*(N+1) := by simp
    _ ≤ ((N+1)*(N+1))*(N+1) := by
      apply Nat.mul_le_mul_right
      exact (Finset.card_filter_le _ _).trans (by simp)
    _ = (N+1)^3 := by ring

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

theorem descriptorGoodSet_exceptional (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ)
    (ha : SourceAngularBounds Q ρ m N lam sig) {b : PolicyDescriptor} (hb : ValidDescriptor N b)
    {P : CellPath} (hP : P.length = descriptorAnchor b) :
    sourceArcLength (descriptorGoodSet Q ρ m N lam sig J 0 P b)ᶜ ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  cases b with
  | parallel g p => simpa only [descriptorGoodSet,sourceAngularWidth_zero] using ha.parallel g p hb.1 hb.2 P hP
  | projection p u => simpa only [descriptorGoodSet,sourceAngularWidth_zero] using ha.projection p u hb.1 hb.2 P hP

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

theorem sourcePolicyBlock_pos {N : ℕ} (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) :
    0 < sourcePolicyBlock N kap := by
  unfold sourcePolicyBlock
  exact Nat.ceil_pos.mpr (by positivity)

theorem outerDescriptorList_valid (m : ℝ → ℝ) {N q c : ℕ} (hq : 0 < q) (hc : c ≤ N) :
    ∀ b ∈ outerDescriptorList m N q c, ValidDescriptor N b := by
  intro b hb
  obtain rfl | hb := Finset.mem_insert.mp hb
  · exact ⟨Nat.zero_le c,hc⟩
  · exact policyDescriptor_valid _ hq le_rfl hb

theorem outerDescriptorList_card (m : ℝ → ℝ) {N q c : ℕ} (hq : 0 < q) :
    (outerDescriptorList m N q c).card ≤ (N+1)^3+1 := by
  exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (policyDescriptorList_card _ hq) 1)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Recursion_DescriptorMaskFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem descriptor_mask_failure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ) (ha : SourceAngularBounds Q ρ m N lam sig)
    {b : PolicyDescriptor} (hb : ValidDescriptor N b) {x : Plane}
    (hx : ∃ P ∈ occupiedAnchorPaths Q ρ (descriptorAnchor b), x ∈ (Q.descendant P).carrier) :
    sourceArcLength {dir | descriptorSpatialMask Q ρ m N lam sig J 0 b x dir ≠ 1} ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  obtain ⟨P,hP,hx⟩ := hx
  simp only [descriptorSpatialMask,spatialAnchorMask_eq Q hQ ρ _ _ _ _ hP hx]
  apply (circleTestMask_failure_le _ (measurable_descriptorGoodSet _ _ _ _ _ _ _ _ _ _) _ _).trans
  exact descriptorGoodSet_exceptional Q ρ m N lam sig J ha hb
    ((mem_dyadicPaths _ P).mp (Finset.mem_filter.mp hP).1)

theorem listMask_failure_subset (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J i : ℕ) (S : Finset PolicyDescriptor) (x : Plane) :
    {dir | descriptorListMask Q ρ m N lam sig J i S x dir ≠ 1} ⊆
      ⋃ b ∈ S, {dir | descriptorSpatialMask Q ρ m N lam sig J i b x dir ≠ 1} := by
  intro dir hdir
  by_contra hn
  have hh : ∀ b ∈ S, descriptorSpatialMask Q ρ m N lam sig J i b x dir = 1 := by
    intro b hb
    by_contra h
    exact hn (mem_iUnion.mpr ⟨b,mem_iUnion.mpr ⟨hb,h⟩⟩)
  exact hdir (by simp only [descriptorListMask,Finset.prod_eq_one hh])

theorem ae_listMask_failure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (hcarry : ρ Q.carrierᶜ = 0) (m : ℝ → ℝ) (N : ℕ) (lam sig : ℝ) (J : ℕ)
    (ha : SourceAngularBounds Q ρ m N lam sig) (S : Finset PolicyDescriptor)
    (hS : ∀ b ∈ S, ValidDescriptor N b) :
    ∀ᵐ x ∂ρ, sourceArcLength {dir | descriptorListMask Q ρ m N lam sig J 0 S x dir ≠ 1} ≤
      (S.card:ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  have hx : ∀ᵐ x ∂ρ, ∀ n : ℕ, ∃ P ∈ occupiedAnchorPaths Q ρ n, x ∈ (Q.descendant P).carrier :=
    ae_all_iff.mpr (fun n => ae_occupied_anchor Q ρ hcarry n)
  filter_upwards [hx] with x hx
  apply (measure_mono (listMask_failure_subset Q ρ m N lam sig J 0 S x)).trans
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _b ∈ S, ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
      apply Finset.sum_le_sum
      intro b hb
      exact descriptor_mask_failure_bound Q hQ ρ m N lam sig J ha (hS b hb) (hx _)
    _ = _ := by simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_MaskLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem removed_pushforward_mass_le {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α)
    (f : α → β) (hf : Measurable f) (w m : α → ℝ≥0∞)
    (bad : Set α) (C : ℝ≥0∞)
    (hbound : ∀ᵐ x ∂μ, w x ≤ C)
    (hout : ∀ᵐ x ∂μ, x ∉ bad → m x = 1) :
    (μ.withDensity (fun x => w x*(1-m x))).map f univ ≤ C*μ bad := by
  rw [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc
    (∫⁻ x, w x*(1-m x) ∂μ) ≤ ∫⁻ x, bad.indicator (fun _ => C) x ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hbound,hout] with x hx houtx
      by_cases hxb : x ∈ bad
      · rw [Set.indicator_of_mem hxb]
        calc
          w x*(1-m x) ≤ w x*1 := mul_le_mul_right tsub_le_self _
          _ ≤ C := by simpa only [mul_one] using hx
      · rw [Set.indicator_of_notMem hxb, houtx hxb, tsub_self, mul_zero]
    _ ≤ C*μ bad := lintegral_indicator_const_le bad C

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_BoundedDualDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem exists_bounded_normalized_dual_density {X : Type*} [MeasurableSpace X]
    (μ : Measure X) (F : X → ℝ≥0∞) (hF : Measurable F) {p q : ℝ}
    (hpq : p.HolderConjugate q)
    {B : ℝ≥0∞} (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hN0 : (∫⁻ x, F x^p ∂μ) ≠ 0) (hNtop : (∫⁻ x, F x^p ∂μ) ≠ ∞) :
    ∃ h : X → ℝ≥0∞, Measurable h ∧ (∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x, h x ≤ C) ∧
      (∫⁻ x, h x^q ∂μ) = 1 ∧
      (∫⁻ x, F x*h x ∂μ) = (∫⁻ x, F x^p ∂μ)^(1/p) := by
  let N := ∫⁻ x, F x^p ∂μ
  let h : X → ℝ≥0∞ := fun x => F x^(p-1) * N^(-1/q)
  have hp1 : 0 < p-1 := sub_pos.mpr (Real.holderConjugate_iff.mp hpq).1
  have hc : N^(-1/q) ≠ ∞ := ENNReal.rpow_ne_top_of_ne_zero hN0 hNtop
  refine ⟨h, by dsimp [h]; fun_prop, ?_, ?_, ?_⟩
  · refine ⟨B^(p-1) * N^(-1/q), ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hp1.le hB) hc, ?_⟩
    intro x
    exact mul_le_mul_left (ENNReal.rpow_le_rpow (hFB x) hp1.le) _
  · have he (x : X) : h x^q = F x^p * N⁻¹ := by
      dsimp [h]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hpq.symm.nonneg,
        ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,hpq.sub_one_mul_conj]
      rw [show (-1/q)*q = -1 by field_simp [hpq.symm.pos.ne'], ENNReal.rpow_neg_one]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hN0),
      ENNReal.mul_inv_cancel hN0 hNtop]
  · have he (x : X) : F x*h x = F x^p * N^(-1/q) := by
      dsimp [h]
      have hr := ENNReal.rpow_add_of_nonneg (x := F x) 1 (p-1) zero_le_one hp1.le
      rw [show (1 : ℝ)+(p-1)=p by ring, ENNReal.rpow_one] at hr
      rw [← mul_assoc, ← hr]
    simp_rw [he]
    rw [lintegral_mul_const' _ _ hc]
    change N * N^(-1/q) = N^(1/p)
    conv_lhs => lhs; rw [← ENNReal.rpow_one N]
    rw [← ENNReal.rpow_add _ _ hN0 hNtop]
    congr 1
    have ht := hpq.one_div_add_one_div
    norm_num at ht
    simp only [neg_div,one_div]
    linarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_FiniteLpIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuous_integral_Lp_of_le {X : Type*} [MeasurableSpace X]
    (μ ν : Measure X) [IsFiniteMeasure μ] (hμν : μ ≤ ν)
    {q : ℝ≥0∞} (hq : 1 ≤ q) [Fact (1 ≤ q)] :
    Continuous (fun f : Lp ℝ q ν => ∫ x, f x ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro f
  have hmem (g : Lp ℝ q ν) : MemLp g q μ := (Lp.memLp g).mono_measure hμν
  have ht : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν) (𝓝 f) (𝓝 0) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm' id f).mp tendsto_id
  let C : ℝ≥0∞ := μ univ ^ (1 - 1 / q.toReal)
  have hC : C ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg _ (measure_ne_top μ univ)
    by_cases hqt : q = ∞
    · simp [hqt]
    · have hqr : 1 ≤ q.toReal := by exact_mod_cast (ENNReal.toReal_mono hqt hq)
      exact sub_nonneg.mpr ((div_le_one (by linarith)).mpr hqr)
  have htC : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) q ν * C)
      (𝓝 f) (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ht (Or.inr hC)
  have ht1 : Tendsto (fun g : Lp ℝ q ν => eLpNorm (⇑g - ⇑f) 1 μ) (𝓝 f) (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htC
    · exact fun _ => bot_le
    · intro g
      calc
        eLpNorm (⇑g - ⇑f) 1 μ ≤ eLpNorm (⇑g - ⇑f) q μ * C := by
          simpa [C] using eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq
            ((hmem g).sub (hmem f)).aestronglyMeasurable
        _ ≤ eLpNorm (⇑g - ⇑f) q ν * C :=
          mul_le_mul_left (eLpNorm_mono_measure _ hμν) _
  exact tendsto_integral_of_L1' f (hmem f).aestronglyMeasurable
    (Eventually.of_forall (fun g => (hmem g).integrable hq)) ht1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_TestNormRepresentation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_test_bound (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hN : sourceTestNorm q γ ≠ ∞)
    (F : BoundedContinuousFunction UnitCircle ℝ) :
    ‖∫ ω, F ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal *
      (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal := by
  have hf : MemLp F (ENNReal.ofReal q) sourceArcLength :=
    (memLp_top_of_bound F.continuous.aestronglyMeasurable ‖F‖
      (Eventually.of_forall F.norm_coe_le_norm)).mono_exponent le_top
  have haux (a : ℝ) (ha : (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal < a) :
      ‖∫ ω, F ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal * a := by
    have ha0 : 0 < a := lt_of_le_of_lt ENNReal.toReal_nonneg ha
    let G : BoundedContinuousFunction UnitCircle ℝ := a⁻¹ • F
    have hG : eLpNorm G (ENNReal.ofReal q) sourceArcLength ≤ 1 := by
      change eLpNorm (a⁻¹ • (F : UnitCircle → ℝ)) _ _ ≤ _
      rw [eLpNorm_const_smul]
      have hn : eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤ ENNReal.ofReal a :=
        (ENNReal.le_ofReal_iff_toReal_le hf.eLpNorm_ne_top ha0.le).mpr ha.le
      calc
        ‖a⁻¹‖ₑ * eLpNorm F (ENNReal.ofReal q) sourceArcLength ≤
            ENNReal.ofReal a⁻¹ * ENNReal.ofReal a := by
          rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)]
          exact mul_le_mul_right hn _
        _ = 1 := by rw [← ENNReal.ofReal_mul (inv_nonneg.mpr ha0.le), inv_mul_cancel₀ ha0.ne', ENNReal.ofReal_one]
    have hb : ENNReal.ofReal ‖∫ ω, G ω ∂γ‖ ≤ sourceTestNorm q γ :=
      le_iSup_of_le G (le_iSup_of_le hG le_rfl)
    have hb' := (ENNReal.ofReal_le_iff_le_toReal hN).mp hb
    change ‖∫ ω, a⁻¹ • F ω ∂γ‖ ≤ _ at hb'
    rw [integral_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha0)] at hb'
    calc
      ‖∫ ω, F ω ∂γ‖ = a * (a⁻¹ * ‖∫ ω, F ω ∂γ‖) := by
        rw [← mul_assoc, mul_inv_cancel₀ ha0.ne', one_mul]
      _ ≤ a * (sourceTestNorm q γ).toReal := mul_le_mul_of_nonneg_left hb' ha0.le
      _ = _ := mul_comm _ _
  apply ge_of_tendsto (f := fun a : ℝ => (sourceTestNorm q γ).toReal * a)
    ((continuous_const.mul continuous_id).continuousAt.tendsto.mono_left
      (show 𝓝[>] (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal ≤
        𝓝 (eLpNorm F (ENNReal.ofReal q) sourceArcLength).toReal from nhdsWithin_le_nhds))
  filter_upwards [self_mem_nhdsWithin] with a ha
  exact haux a ha

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_TestNormMeasurable
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_measurable_test_bound (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : sourceTestNorm q γ ≠ ∞)
    (f : UnitCircle → ℝ) (hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength)) :
    ‖∫ ω, f ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal *
      (eLpNorm f (ENNReal.ofReal q) sourceArcLength).toReal := by
  let μ := γ + sourceArcLength
  let Q := ENNReal.ofReal q
  have hQ : 1 ≤ Q := by simpa [Q] using ENNReal.ofReal_le_ofReal hq
  let : Fact (1 ≤ Q) := ⟨hQ⟩
  have hγ : γ ≤ μ := le_add_of_nonneg_right bot_le
  have hν : sourceArcLength ≤ μ := le_add_of_nonneg_left bot_le
  have hν' : sourceArcLength ≤ (1 : ℝ≥0∞) • μ := by simpa using hν
  let R : Lp ℝ Q μ →L[ℝ] Lp ℝ Q sourceArcLength :=
    Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν'
  have hR (g : Lp ℝ Q μ) : R g =ᵐ[sourceArcLength] g :=
    Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hν' g
  have hd := BoundedContinuousFunction.toLp_denseRange ℝ μ ℝ (show Q ≠ ∞ from ENNReal.ofReal_ne_top)
  have hclosed : IsClosed {g : Lp ℝ Q μ | ‖∫ ω, g ω ∂γ‖ ≤
      (sourceTestNorm q γ).toReal * ‖R g‖} :=
    isClosed_le (continuous_integral_Lp_of_le γ μ hγ hQ).norm
      (continuous_const.mul R.continuous.norm)
  have hall (g : Lp ℝ Q μ) : ‖∫ ω, g ω ∂γ‖ ≤ (sourceTestNorm q γ).toReal * ‖R g‖ := by
    apply (hclosed.closure_subset_iff (s := Set.range (BoundedContinuousFunction.toLp Q μ ℝ))).mpr ?_ (hd g)
    rintro _ ⟨F, rfl⟩
    have hF := BoundedContinuousFunction.coeFn_toLp Q μ ℝ F
    have hi := integral_congr_ae (hγ.absolutelyContinuous.ae_eq hF)
    have hn : ‖R (BoundedContinuousFunction.toLp Q μ ℝ F)‖ =
        (eLpNorm F Q sourceArcLength).toReal := by
      rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq hF))]
    change ‖∫ ω, (BoundedContinuousFunction.toLp Q μ ℝ F) ω ∂γ‖ ≤ _
    rw [hi, hn]
    exact sourceTestNorm_test_bound γ hN F
  have hg := hall (hf.toLp f)
  have he := hf.coeFn_toLp
  rw [integral_congr_ae (hγ.absolutelyContinuous.ae_eq he)] at hg
  have hn : ‖R (hf.toLp f)‖ = (eLpNorm f Q sourceArcLength).toReal := by
    rw [Lp.norm_def, eLpNorm_congr_ae ((hR _).trans (hν.absolutelyContinuous.ae_eq he))]
  rwa [hn] at hg

theorem sourceTestNorm_absolutelyContinuous (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {q : ℝ} (hq : 1 ≤ q) (hN : sourceTestNorm q γ ≠ ∞) : γ ≪ sourceArcLength := by
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hνs
  let f : UnitCircle → ℝ := s.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength) :=
    memLp_indicator_const _ hs _ (Or.inr (measure_ne_top _ _))
  have hb := sourceTestNorm_measurable_test_bound γ hq hN f hf
  have he : f =ᵐ[sourceArcLength] 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hνs] with x hx
    exact Set.indicator_of_notMem hx _
  rw [eLpNorm_congr_ae he, eLpNorm_zero, ENNReal.toReal_zero, mul_zero] at hb
  have hi : (∫ x, f x ∂γ) = (γ s).toReal := by
    simp [f, integral_indicator hs, measureReal_def]
  rw [hi, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg] at hb
  exact ((ENNReal.toReal_eq_zero_iff _).mp (le_antisymm hb ENNReal.toReal_nonneg)).resolve_right
    (measure_ne_top γ s)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_TestNormDensity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_bounded_density_lower (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceTestNorm q γ ≠ ∞)
    (F : UnitCircle → ℝ≥0∞) (hF : Measurable F) {B : ℝ≥0∞}
    (hB : B ≠ ∞) (hFB : ∀ x, F x ≤ B)
    (hFR : ∀ᵐ x ∂sourceArcLength, F x ≤ γ.rnDeriv sourceArcLength x) :
    (∫⁻ x, F x^p ∂sourceArcLength)^(1/p) ≤ sourceTestNorm q γ := by
  have hq : 1 ≤ q := (Real.holderConjugate_iff.mp hpq.symm).1.le
  have hAC := sourceTestNorm_absolutelyContinuous γ hq hN
  have hmass : (∫⁻ x, F x^p ∂sourceArcLength) ≠ ∞ := by
    apply ne_of_lt
    calc
      (∫⁻ x, F x^p ∂sourceArcLength) ≤ ∫⁻ _, B^p ∂sourceArcLength :=
        lintegral_mono (fun x => ENNReal.rpow_le_rpow (hFB x) hpq.nonneg)
      _ < ∞ := by
        rw [lintegral_const]
        exact ENNReal.mul_lt_top (ENNReal.rpow_ne_top_of_nonneg hpq.nonneg hB).lt_top
          (measure_lt_top sourceArcLength univ)
  by_cases hzero : (∫⁻ x, F x^p ∂sourceArcLength) = 0
  · rw [hzero, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpq.pos)]
    exact bot_le
  obtain ⟨h, hh, ⟨C, hC, hhC⟩, hnorm, hpair⟩ :=
    exists_bounded_normalized_dual_density sourceArcLength F hF hpq hB hFB hzero hmass
  have hht (x : UnitCircle) : h x ≠ ∞ := ne_of_lt ((hhC x).trans_lt hC.lt_top)
  have hen (x : UnitCircle) : ‖(h x).toReal‖ₑ = h x := by
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hht x)]
  have hm : MemLp (fun x => (h x).toReal) (ENNReal.ofReal q) (γ + sourceArcLength) :=
    (memLp_top_of_bound hh.ennreal_toReal.aestronglyMeasurable C.toReal
      (Eventually.of_forall (fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
        exact ENNReal.toReal_mono hC (hhC x)))).mono_exponent le_top
  have hn : eLpNorm (fun x => (h x).toReal) (ENNReal.ofReal q) sourceArcLength = 1 := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.symm.nonneg]
    simp_rw [hen]
    rw [hnorm, ENNReal.one_rpow]
  have hb := sourceTestNorm_measurable_test_bound γ hq hN (fun x => (h x).toReal) hm
  rw [hn, ENNReal.toReal_one, mul_one] at hb
  have hi : Integrable (fun x => (h x).toReal) γ :=
    (hm.mono_measure (le_add_of_nonneg_right bot_le)).integrable
      (by simpa using ENNReal.ofReal_le_ofReal hq)
  have hlin : (∫⁻ x, h x ∂γ) ≤ sourceTestNorm q γ := by
    have he : ENNReal.ofReal ‖∫ x, (h x).toReal ∂γ‖ = ∫⁻ x, h x ∂γ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => ENNReal.toReal_nonneg)),
        ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))]
      exact lintegral_congr (fun x => ENNReal.ofReal_toReal (hht x))
    rw [← he]
    exact (ENNReal.ofReal_le_iff_le_toReal hN).mpr hb
  rw [← hpair]
  calc
    (∫⁻ x, F x * h x ∂sourceArcLength) ≤
        ∫⁻ x, γ.rnDeriv sourceArcLength x * h x ∂sourceArcLength :=
      lintegral_mono_ae (hFR.mono (fun x hx => mul_le_mul_left hx _))
    _ = ∫⁻ x, h x ∂γ := by
      have he := lintegral_withDensity_eq_lintegral_mul sourceArcLength
        (Measure.measurable_rnDeriv γ sourceArcLength) hh
      rw [Measure.withDensity_rnDeriv_eq γ sourceArcLength hAC] at he
      exact he.symm
    _ ≤ _ := hlin

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadonLpDensity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_rnDeriv_eLpNorm_le (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceTestNorm q γ ≠ ∞) :
    eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength ≤
      sourceTestNorm q γ := by
  let R := γ.rnDeriv sourceArcLength
  let F : ℕ → UnitCircle → ℝ := fun n x => min (R x).toReal n
  have hm (n : ℕ) : Measurable (F n) :=
    (Measure.measurable_rnDeriv γ sourceArcLength).ennreal_toReal.min measurable_const
  have hpos (n : ℕ) (x : UnitCircle) : 0 ≤ F n x :=
    le_min ENNReal.toReal_nonneg (Nat.cast_nonneg _)
  have hb (n : ℕ) : eLpNorm (F n) (ENNReal.ofReal p) sourceArcLength ≤ sourceTestNorm q γ := by
    have h := sourceTestNorm_bounded_density_lower γ hpq hN
      (fun x => ENNReal.ofReal (F n x)) (hm n).ennreal_ofReal ENNReal.ofReal_ne_top
      (fun x => ENNReal.ofReal_le_ofReal (min_le_right _ _))
      (Eventually.of_forall (fun x =>
        (ENNReal.ofReal_le_ofReal (min_le_left _ _)).trans (ENNReal.ofReal_toReal_le)))
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.nonneg]
    simpa only [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg (hpos n _)] using h
  apply Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (Eventually.of_forall hb)
    (fun index => (hm index).aestronglyMeasurable)
  apply Eventually.of_forall
  intro x
  obtain ⟨n, hn⟩ := exists_nat_ge (R x).toReal
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop n] with m hm
  exact (min_eq_left (hn.trans (by exact_mod_cast hm))).symm

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_ExtendedDensityNorm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_le_rnDeriv_norm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hAC : γ ≪ sourceArcLength) :
    sourceTestNorm q γ ≤
      eLpNorm (fun x => (γ.rnDeriv sourceArcLength x).toReal) (ENNReal.ofReal p) sourceArcLength := by
  let R := γ.rnDeriv sourceArcLength
  have hm : Measurable R := Measure.measurable_rnDeriv _ _
  have hn : eLpNorm (fun x => (R x).toReal) (ENNReal.ofReal p) sourceArcLength =
      (∫⁻ x, R x^p ∂sourceArcLength)^(1/p) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.nonneg]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top γ sourceArcLength] with x hx
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hx.ne]
  rw [hn]
  apply iSup_le
  intro F
  apply iSup_le
  intro hF
  have hG : Measurable (fun x => ‖F x‖ₑ) := F.continuous.enorm.measurable
  have hq : (∫⁻ x, ‖F x‖ₑ^q ∂sourceArcLength)^(1/q) ≤ 1 := by
    rwa [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hpq.symm.nonneg] at hF
  have hb := enorm_integral_le_lintegral_enorm (μ := γ) (fun x => F x)
  rw [← ofReal_norm] at hb
  have he : (∫⁻ x, ‖F x‖ₑ ∂γ) = ∫⁻ x, R x * ‖F x‖ₑ ∂sourceArcLength := by
    have h := lintegral_withDensity_eq_lintegral_mul sourceArcLength hm hG
    rw [Measure.withDensity_rnDeriv_eq γ sourceArcLength hAC] at h
    exact h
  rw [he] at hb
  have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq sourceArcLength hpq hm.aemeasurable hG.aemeasurable
  exact hb.trans (hh.trans ((mul_le_mul_right hq _).trans_eq (mul_one _)))

theorem sourceTestNorm_eq_densityNorm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    sourceTestNorm q γ = sourceDensityNorm p γ := by
  unfold sourceDensityNorm
  split_ifs with hAC
  · apply le_antisymm (sourceTestNorm_le_rnDeriv_norm γ hpq hAC)
    by_cases hN : sourceTestNorm q γ = ∞
    · rw [hN]; exact le_top
    · exact sourceTestNorm_rnDeriv_eLpNorm_le γ hpq hN
  · by_contra h
    exact hAC (sourceTestNorm_absolutelyContinuous γ
      (Real.holderConjugate_iff.mp hpq.symm).1.le h)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialCapMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem source_measure_set_le_densityNorm (γ : Measure UnitCircle) [IsFiniteMeasure γ]
    {p q : ℝ} (hpq : p.HolderConjugate q) (hN : sourceDensityNorm p γ ≠ ∞)
    (S : Set UnitCircle) (hS : MeasurableSet S) :
    γ S ≤ sourceDensityNorm p γ * (sourceArcLength S)^(1-1/p) := by
  have hT : sourceTestNorm q γ ≠ ∞ := by rwa [sourceTestNorm_eq_densityNorm γ hpq]
  let f : UnitCircle → ℝ := S.indicator (fun _ => 1)
  have hf : MemLp f (ENNReal.ofReal q) (γ + sourceArcLength) :=
    memLp_indicator_const _ hS _ (Or.inr (measure_ne_top _ _))
  have hb := sourceTestNorm_measurable_test_bound γ
    (Real.holderConjugate_iff.mp hpq.symm).1.le hT f hf
  have hi : ‖∫ x, f x ∂γ‖ = (γ S).toReal := by
    simp [f, integral_indicator hS, measureReal_def, Real.norm_eq_abs]
  have hn : eLpNorm f (ENNReal.ofReal q) sourceArcLength = (sourceArcLength S)^(1/q) := by
    simp only [f, eLpNorm_indicator_const₀ hS.nullMeasurableSet (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne'
      ENNReal.ofReal_ne_top, enorm_one, one_mul, ENNReal.toReal_ofReal hpq.symm.nonneg]
  rw [hi, hn] at hb
  have he : (1:ℝ)/q = 1-1/p := by linarith [hpq.one_div_add_one_div]
  have ht : (sourceArcLength S)^(1/q) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (one_div_nonneg.mpr hpq.symm.nonneg) (measure_ne_top _ _)
  have hb' := ENNReal.ofReal_le_ofReal hb
  rwa [ENNReal.ofReal_toReal (measure_ne_top _ _), ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hT, ENNReal.ofReal_toReal ht, he, sourceTestNorm_eq_densityNorm γ hpq] at hb'

theorem radial_cap_mass_bound (ν : Measure Plane) [IsFiniteMeasure ν] (x : Plane)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K w : ℝ≥0∞} (hK : K ≠ ∞)
    (hN : sourceDensityNorm p (ν.map (sourceRadialUnit x)) ≤ K)
    (S : Set UnitCircle) (hS : MeasurableSet S) (hSw : sourceArcLength S ≤ w) :
    ν (sourceRadialUnit x ⁻¹' S) ≤ K * w^(1-1/p) := by
  have hexp : 0 ≤ 1-1/p := by
    have he := hpq.one_div_add_one_div
    have hq := one_div_nonneg.mpr hpq.symm.nonneg
    linarith
  rw [← Measure.map_apply (measurable_sourceRadialUnit x) hS]
  exact (source_measure_set_le_densityNorm _ hpq (hN.trans_lt hK.lt_top).ne S hS).trans
    (mul_le_mul' hN (ENNReal.rpow_le_rpow hSw hexp))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialFailureMass
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem measurableSet_radialFailure (S : Plane → Set UnitCircle)
    (hS : MeasurableSet {z : Plane × UnitCircle | z.2 ∈ S z.1}) :
    MeasurableSet (radialFailure S) :=
  hS.preimage (measurable_fst.prodMk measurable_sourceRadialUnit_joint)

theorem radial_failure_mass_le (μ ν : ProbabilityMeasure Plane)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K w : ℝ≥0∞} (hK : K ≠ ∞)
    (hN : ∀ᵐ x ∂(μ : Measure Plane), sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (S : Plane → Set UnitCircle)
    (hS : MeasurableSet {z : Plane × UnitCircle | z.2 ∈ S z.1})
    (hSw : ∀ᵐ x ∂(μ : Measure Plane), sourceArcLength (S x) ≤ w) :
    ((μ : Measure Plane).prod ν) (radialFailure S) ≤ K*w^(1-1/p) := by
  rw [Measure.prod_apply (measurableSet_radialFailure S hS)]
  calc
    (∫⁻ x, (ν : Measure Plane) (Prod.mk x ⁻¹' radialFailure S) ∂(μ : Measure Plane)) ≤
        ∫⁻ _, K*w^(1-1/p) ∂(μ : Measure Plane) := by
      apply lintegral_mono_ae
      filter_upwards [hN, hSw] with x hx hw
      have hSx : MeasurableSet (S x) := hS.preimage (measurable_const.prodMk measurable_id)
      exact radial_cap_mass_bound ν x hpq hK hx (S x) hSx hw
    _ = _ := by simp

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Estimates_OuterMaskFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem outerEntry_le (m₁ m₂ : ℝ → ℝ) (N : ℕ) (β : ℝ) : outerEntry m₁ m₂ N β ≤ N := by
  apply Finset.sup_le
  intro n hn
  exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hn).1)

theorem actualClassMeasure_carry (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane) (N B : ℕ) (T : List ℕ) :
    actualClassMeasure Q μ N B T Q.carrierᶜ = 0 := by
  rw [actualClassMeasure,normalizedClass_apply]
  have he : Q.carrierᶜ ∩ leafUnion Q (classLeaves (regularizationLeaves Q μ N) (regularizationLabel Q μ N B) T) = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro x hx
    exact hx.1 (leafUnion_subset Q hQ _ hx.2)
  rw [he,measure_empty,mul_zero]

theorem measurableSet_outerAllEntryFailure (Q : DyadicSquare) (ρ : Measure Plane)
    (m : ℝ → ℝ) (N : ℕ) (lam sig kap : ℝ) :
    MeasurableSet {z : Plane × UnitCircle | z.2 ∈ outerAllEntryFailure Q ρ m N lam sig kap z.1} := by
  have he : {z : Plane × UnitCircle | z.2 ∈ outerAllEntryFailure Q ρ m N lam sig kap z.1} =
      ⋃ c ∈ Finset.range (N+1), {z : Plane × UnitCircle | outerEndpointMask Q ρ m N lam sig kap c z.1 z.2 ≠ 1} := by
    ext z
    simp only [outerAllEntryFailure,mem_ofPred_eq,mem_iUnion]
  rw [he]
  exact Finset.measurableSet_biUnion _ (fun entry _ =>
    (measurableSet_eq_fun (measurable_outerEndpointMask Q ρ m N lam sig kap entry)
      measurable_const).compl)

theorem ae_outerAllEntryFailure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (ρ : Measure Plane)
    (hcarry : ρ Q.carrierᶜ = 0) (m : ℝ → ℝ) {N : ℕ} (hN : 0 < N)
    (lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (ha : SourceAngularBounds Q ρ m N lam sig) :
    ∀ᵐ x ∂ρ, sourceArcLength (outerAllEntryFailure Q ρ m N lam sig kap x) ≤
      ((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  have hq := sourcePolicyBlock_pos hN hkap
  have hcard (entry : ℕ) :
      ((outerDescriptorList m N (sourcePolicyBlock N kap) entry).card : ENNReal) ≤
        (((N+1)^3+1 : ℕ) : ENNReal) := by
    exact_mod_cast outerDescriptorList_card m hq (c := entry)
  have hx : ∀ᵐ x ∂ρ, ∀ c : ℕ, c ≤ N → sourceArcLength
      {dir | outerEndpointMask Q ρ m N lam sig kap c x dir ≠ 1} ≤
        (((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
    apply ae_all_iff.mpr
    intro c
    by_cases hc : c ≤ N
    · filter_upwards [ae_listMask_failure_bound Q hQ ρ hcarry m N lam sig (sourceSmoothingLevels sig kap) ha
        (outerDescriptorList m N (sourcePolicyBlock N kap) c) (outerDescriptorList_valid m hq hc)] with x hx
      intro _
      exact hx.trans (mul_le_mul_left (hcard c) _)
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hc h))
  filter_upwards [hx] with x hx
  apply (measure_biUnion_finset_le _ _).trans
  calc
    _ ≤ ∑ _c ∈ Finset.range (N+1), (((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
      apply Finset.sum_le_sum
      intro c hc
      exact hx c (Nat.le_of_lt_succ (Finset.mem_range.mp hc))
    _ = _ := by simp [mul_assoc]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Angular_RetainedAngularFailure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem ae_actualClassMeasure_imp (Q : DyadicSquare) (μ : Measure Plane) [IsFiniteMeasure μ]
    (N B : ℕ) (T : List ℕ) (P : Plane → Prop)
    (hP : ∀ᵐ x ∂actualClassMeasure Q μ N B T, P x) :
    ∀ᵐ x ∂μ, x ∈ actualClassDomain Q μ N B T → P x := by
  apply (ae_restrict_iff' (measurableSet_actualClassDomain Q μ N B T)).mp
  simp only [actualClassMeasure,normalizedClass,classMeasure,Measure.restrict_apply_univ] at hP
  change ∀ᵐ x ∂(μ (actualClassDomain Q μ N B T))⁻¹ • μ.restrict (actualClassDomain Q μ N B T), P x at hP
  exact (Measure.ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr (measure_ne_top μ _))).mp hP

theorem measurableSet_retainedAngularFailure (Q : DyadicSquare) (μ : Measure Plane)
    (m : List ℕ → ℝ → ℝ) (N B : ℕ) (lam sig kap : ℝ) :
    MeasurableSet {z : Plane × UnitCircle | z.2 ∈ retainedAngularFailure Q μ m N B lam sig kap z.1} := by
  have he : {z : Plane × UnitCircle | z.2 ∈ retainedAngularFailure Q μ m N B lam sig kap z.1} =
      ⋃ T ∈ retainedClassLabels Q μ N B (ENNReal.ofReal (((2:ℝ)^N)^(-lam))),
        {z : Plane × UnitCircle | z.1 ∈ actualClassDomain Q μ N B T ∧
          z.2 ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N B T) (m T) N lam sig kap z.1} := by
    ext z
    simp only [retainedAngularFailure,mem_ofPred_eq,mem_iUnion]
  rw [he]
  apply Finset.measurableSet_biUnion
  intro T _
  exact ((measurableSet_actualClassDomain Q μ N B T).preimage measurable_fst).inter
    (measurableSet_outerAllEntryFailure _ _ _ _ _ _ _)

theorem ae_retainedAngularFailure_bound (Q : DyadicSquare) (hQ : 0 < Q.side) (μ : Measure Plane)
    [IsProbabilityMeasure μ] (m : List ℕ → ℝ → ℝ) {N H : ℕ} (hN : 0 < N)
    (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (hf : ActualClassFamily Q μ N H δ lam sig m) :
    ∀ᵐ x ∂μ, sourceArcLength (retainedAngularFailure Q μ m N (N/H) lam sig kap x) ≤
      (((4*N+1)^(2*H+1):ℕ):ENNReal)*((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*
        ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig))) := by
  classical
  let S := retainedClassLabels Q μ N (N/H) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let w := ((N+1:ℕ):ENNReal)*(((N+1)^3+1:ℕ):ENNReal)*ENNReal.ofReal (((2:ℝ)^N)^(-(lam+sig)))
  have hx : ∀ᵐ x ∂μ, ∀ T : List ℕ, T ∈ S → x ∈ actualClassDomain Q μ N (N/H) T →
      sourceArcLength (outerAllEntryFailure Q (actualClassMeasure Q μ N (N/H) T) (m T) N lam sig kap x) ≤ w := by
    apply ae_all_iff.mpr
    intro T
    by_cases hT : T ∈ S
    · filter_upwards [ae_actualClassMeasure_imp Q μ N (N/H) T _
        (ae_outerAllEntryFailure_bound Q hQ _ (actualClassMeasure_carry Q hQ μ N (N/H) T) (m T)
          hN lam sig hkap (hf.profiles T hT).2)] with x hx
      exact fun _ => hx
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (hT h))
  filter_upwards [hx] with x hx
  have hb : sourceArcLength (retainedAngularFailure Q μ m N (N/H) lam sig kap x) ≤ (S.card:ENNReal)*w := by
    apply (measure_biUnion_finset_le _ _).trans
    calc
      _ ≤ ∑ _T ∈ S, w := by
        apply Finset.sum_le_sum
        intro T hT
        by_cases hdom : x ∈ actualClassDomain Q μ N (N/H) T
        · apply (measure_mono (fun _ h => h.2)).trans
          exact hx T hT hdom
        · have he : {dir | x ∈ actualClassDomain Q μ N (N/H) T ∧
              dir ∈ outerAllEntryFailure Q (actualClassMeasure Q μ N (N/H) T) (m T) N lam sig kap x} = ∅ := by
            ext dir; simp [hdom]
          rw [he,measure_empty]
          exact zero_le
      _ = _ := by simp
  apply hb.trans
  simpa only [w,mul_assoc] using
    mul_le_mul_left (show (S.card:ENNReal) ≤ (((4*N+1)^(2*H+1):ℕ):ENNReal) from by dsimp only [S]; exact_mod_cast hf.count) w

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
-- module Solutions.OAIQ038_FA.Falconer_Shells_RestoredMaskCoverage
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootMaskCoverage
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem restoredTwoRootMask_one_outside (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side) (μ ν : Measure Plane)
    (m₁ m₂ : List ℕ → ℝ → ℝ) (N B₁ B₂ : ℕ) (lam sig kap β : ℝ) (z : Plane × Plane)
    (hx : z.1 ∈ retainedClassUnion Q₀ μ N B₁ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hy : z.2 ∈ retainedClassUnion Q₁ ν N B₂ (ENNReal.ofReal (((2:ℝ)^N)^(-lam))))
    (hf₁ : sourceRadialUnit z.1 z.2 ∉ retainedAngularFailure Q₀ μ m₁ N B₁ lam sig kap z.1)
    (hf₂ : sourceRadialUnit z.2 z.1 ∉ retainedAngularFailure Q₁ ν m₂ N B₂ lam sig kap z.2) :
    restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β z = 1 := by
  obtain ⟨T,hT,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨U,hU,hy⟩ := mem_iUnion₂.mp hy
  rw [restoredTwoRootMask_on_pair Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N B₁ B₂ lam sig kap β (a := (T,U)) (z := z) (Finset.mem_product.mpr ⟨hT,hU⟩) ⟨hx,hy⟩]
  let c := outerEntry (m₁ T) (m₂ U) N β
  have hc : c ∈ Finset.range (N+1) := Finset.mem_range.mpr (Nat.lt_succ_of_le (outerEntry_le _ _ _ _))
  have h₁ : outerEndpointMask Q₀ (actualClassMeasure Q₀ μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    exact hf₁ (mem_iUnion₂.mpr ⟨T,hT,hx,mem_iUnion₂.mpr ⟨c,hc,hn⟩⟩)
  have h₂ : outerEndpointMask Q₁ (actualClassMeasure Q₁ ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2) = 1 := by
    by_contra hn
    apply hf₂
    refine mem_iUnion₂.mpr ⟨U,hU,hy,mem_iUnion₂.mpr ⟨c,hc,?_⟩⟩
    simpa only [Set.mem_ofPred_eq,outerEndpointMask_radial_swap] using hn
  change ENNReal.ofReal (outerEndpointMask Q₀ (actualClassMeasure Q₀ μ N B₁ T) (m₁ T) N lam sig kap c z.1 (sourceRadialUnit z.1 z.2)*
    outerEndpointMask Q₁ (actualClassMeasure Q₁ ν N B₂ U) (m₂ U) N lam sig kap c z.2 (sourceRadialUnit z.1 z.2)) = 1
  rw [h₁,h₂,mul_one,ENNReal.ofReal_one]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Shells_TwoRootRestoration
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem two_root_restored_removed_mass_bound_oai (Q₀ Q₁ : DyadicSquare) (hQ₀ : 0 < Q₀.side) (hQ₁ : 0 < Q₁.side)
    (μ ν : ProbabilityMeasure Plane) (m₁ m₂ : List ℕ → ℝ → ℝ)
    {N H₁ H₂ : ℕ} (hN : 0 < N) (δ lam sig : ℝ) {kap : ℝ} (hkap : 0 < kap) (β : ℝ)
    (hf₁ : ActualClassFamily Q₀ μ N H₁ δ lam sig m₁) (hf₂ : ActualClassFamily Q₁ ν N H₂ δ lam sig m₂)
    {p q : ℝ} (hpq : p.HolderConjugate q) {K C : ENNReal} (hK : K ≠ ∞)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    (hweight : ∀ᵐ z ∂(μ:Measure Plane).prod ν, distanceWeight z ≤ C) :
    restoredTwoRootRemoved Q₀ Q₁ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β univ ≤
      C*(restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p)) := by
  let A := retainedClassUnion Q₀ μ N (N/H₁) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let B := retainedClassUnion Q₁ ν N (N/H₂) (ENNReal.ofReal (((2:ℝ)^N)^(-lam)))
  let S := retainedAngularFailure Q₀ μ m₁ N (N/H₁) lam sig kap
  let T := retainedAngularFailure Q₁ ν m₂ N (N/H₂) lam sig kap
  let bad : Set (Plane × Plane) := ((Aᶜ ×ˢ univ ∪ univ ×ˢ Bᶜ) ∪ radialFailure S) ∪ Prod.swap ⁻¹' radialFailure T
  have hS := measurableSet_retainedAngularFailure Q₀ μ m₁ N (N/H₁) lam sig kap
  have hT := measurableSet_retainedAngularFailure Q₁ ν m₂ N (N/H₂) lam sig kap
  have hbS := radial_failure_mass_le μ ν hpq hK hμrad S hS
    (ae_retainedAngularFailure_bound Q₀ hQ₀ μ m₁ hN δ lam sig hkap hf₁)
  have hbT := radial_failure_mass_le ν μ hpq hK hνrad T hT
    (ae_retainedAngularFailure_bound Q₁ hQ₁ ν m₂ hN δ lam sig hkap hf₂)
  have hswap : ((μ:Measure Plane).prod (ν:Measure Plane)) (Prod.swap ⁻¹' radialFailure T) =
      ((ν:Measure Plane).prod (μ:Measure Plane)) (radialFailure T) := by
    rw [← Measure.map_apply measurable_swap (measurableSet_radialFailure T hT),Measure.prod_swap]
  have hbad : ((μ:Measure Plane).prod (ν:Measure Plane)) bad ≤
      restorationDiscardBound N H₁ lam+restorationDiscardBound N H₂ lam+
        K*(restorationArcBound N H₁ lam sig)^(1-1/p)+K*(restorationArcBound N H₂ lam sig)^(1-1/p) := by
    calc
      _ ≤ (((μ:Measure Plane).prod (ν:Measure Plane)) (Aᶜ ×ˢ (univ : Set Plane))+((μ:Measure Plane).prod (ν:Measure Plane)) ((univ : Set Plane) ×ˢ Bᶜ)+
          ((μ:Measure Plane).prod (ν:Measure Plane)) (radialFailure S))+((μ:Measure Plane).prod (ν:Measure Plane)) (Prod.swap ⁻¹' radialFailure T) := by
        apply (measure_union_le _ _).trans
        apply add_le_add
        · apply (measure_union_le _ _).trans
          exact add_le_add (measure_union_le _ _) le_rfl
        · exact le_rfl
      _ ≤ _ := by
        simp only [Measure.prod_prod,measure_univ,mul_one,one_mul,hswap]
        exact add_le_add (add_le_add (add_le_add hf₁.discarded hf₂.discarded) hbS) hbT
  apply (removed_pushforward_mass_le ((μ:Measure Plane).prod (ν:Measure Plane)) (fun z => dist z.1 z.2) (by fun_prop)
    distanceWeight (restoredTwoRootMask Q₀ Q₁ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β) bad C hweight ?_).trans
  · exact mul_le_mul_right hbad C
  · apply Filter.Eventually.of_forall
    intro z hz
    have hx : z.1 ∈ A := by
      by_contra hn
      exact hz (Or.inl (Or.inl (Or.inl ⟨hn,mem_univ _⟩)))
    have hy : z.2 ∈ B := by
      by_contra hn
      exact hz (Or.inl (Or.inl (Or.inr ⟨mem_univ _,hn⟩)))
    have hfS : sourceRadialUnit z.1 z.2 ∉ S z.1 := by
      intro h
      exact hz (Or.inl (Or.inr h))
    have hfT : sourceRadialUnit z.2 z.1 ∉ T z.2 := by
      intro h
      exact hz (Or.inr h)
    exact restoredTwoRootMask_one_outside Q₀ Q₁ hQ₀ hQ₁ μ ν m₁ m₂ N (N/H₁) (N/H₂) lam sig kap β z hx hy hfS hfT

end PlanarFalconer

end OAI
end

theorem solution : type_of% @OAI.PlanarFalconer.two_root_restored_removed_mass_bound_oai := @OAI.PlanarFalconer.two_root_restored_removed_mass_bound_oai
