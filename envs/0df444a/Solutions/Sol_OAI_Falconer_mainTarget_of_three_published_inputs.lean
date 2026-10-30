-- Prove2me | solution 1 for OAI.Falconer.mainTarget_of_three_published_inputs
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:28:10.573997+00:00
-- url     : https://prove2.me/submissions/225be126-8b65-4527-ad43-8462bf335a0e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_PlanarFalconer_finite_radial_testNorm_integral
import Theorems.Thm_OAI_PlanarFalconer_two_root_has_shell_approximations
import Theorems.Thm_OAI_Falconer_prepared_pair_of_lower_dimensions
import Theorems.Thm_OAI_Falconer_prepared_pair_positive_distance

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_GridCount
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Candidate grid counts in any ambient dimension

The remaining unknown cell in a retained graph edge is confined to a small
ball. Its integer coordinate labels therefore lie in a product of short
integer intervals. This gives the dimension-dependent degree factor.
-/

namespace Falconer

/-- A finite family in a coordinate box has at most `(2L+1)^d` labels. -/
theorem grid_box_card {d L : ℕ} (S : Finset (Fin d → ℤ)) (w : Fin d → ℤ)
    (hS : ∀ z ∈ S, ∀ i, |z i - w i| ≤ (L : ℤ)) :
    S.card ≤ (2 * L + 1)^d := by
  classical
  let shift : (Fin d → ℤ) → (Fin d → ℤ) := fun z i => z i - w i
  have hi : Function.Injective shift := by
    intro u v huv
    funext i
    have hi := congrFun huv i
    dsimp [shift] at hi
    omega
  have hsub : S.image shift ⊆
      Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ)) := by
    intro z hz
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hz
    apply Fintype.mem_piFinset.mpr
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (hS u hu i))
  have hcard : (Finset.Icc (-(L : ℤ)) (L : ℤ)).card = 2 * L + 1 := by
    rw [Int.card_Icc]
    omega
  calc
    S.card = (S.image shift).card := (Finset.card_image_of_injective S hi).symm
    _ ≤ (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) (L : ℤ))).card :=
      Finset.card_le_card hsub
    _ = (2 * L + 1)^d := by simp [Fintype.card_piFinset, hcard]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularTubes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A perpendicular tube test occupies two small direction caps

The centers are the two directions of the actual tested displacement.
This gives the angular measure bound used in the parallel-test average.
-/

namespace Falconer
open MeasureTheory Set Metric
open scoped ENNReal
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem norm_perpendicularPart_sq {w : E} (hw : ‖w‖ = 1) (v : E) :
    ‖perpendicularPart w v‖^2 = ‖v‖^2-(inner ℝ w v)^2 := by
  have h := norm_sub_sq_real v (inner ℝ w v • w)
  rw [real_inner_smul_right,real_inner_comm v w,norm_smul,hw,
    mul_one,Real.norm_eq_abs,sq_abs] at h
  dsimp only [perpendicularPart]
  rw [real_inner_comm v w]
  nlinarith

theorem unit_close_of_perpendicular {w u : E} (hw : ‖w‖ = 1) (hu : ‖u‖ = 1)
    (hinner : 0 ≤ inner ℝ w u) :
    ‖w-u‖ ≤ 2*‖perpendicularPart w u‖ := by
  have hsq := norm_sub_sq_real w u
  have hp := norm_perpendicularPart_sq hw u
  have ha : inner ℝ w u ≤ 1 := by
    have h := (le_abs_self (inner ℝ w u)).trans (abs_real_inner_le_norm w u)
    simpa only [hw,hu,mul_one] using h
  rw [hw,hu] at hsq
  rw [hu] at hp
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (show 0 ≤ 4*inner ℝ w u+2 by linarith)
  nlinarith [norm_nonneg (w-u),norm_nonneg (perpendicularPart w u)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_Capacity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer

theorem effective_nonnegative {t : CapacityTree} (h : t.nonnegative) :
    0 ≤ t.effective := by
  induction t with
  | leaf c => exact h
  | node c t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    obtain ⟨hc,h₀,h₁,h₂,h₃⟩ := h
    exact le_min hc (by linarith [ih₀ h₀,ih₁ h₁,ih₂ h₂,ih₃ h₃])

theorem split_four {c₀ c₁ c₂ c₃ m : ℝ}
    (h₀ : 0 ≤ c₀) (h₁ : 0 ≤ c₁) (h₂ : 0 ≤ c₂) (h₃ : 0 ≤ c₃)
    (hm : 0 ≤ m) (htotal : m ≤ c₀+c₁+c₂+c₃) :
    ∃ m₀ m₁ m₂ m₃ : ℝ,
      (0 ≤ m₀ ∧ m₀ ≤ c₀) ∧ (0 ≤ m₁ ∧ m₁ ≤ c₁) ∧
      (0 ≤ m₂ ∧ m₂ ≤ c₂) ∧ (0 ≤ m₃ ∧ m₃ ≤ c₃) ∧
      m₀+m₁+m₂+m₃ = m := by
  let s := c₀+c₁+c₂+c₃
  by_cases hs : s = 0
  · have hm0 : m = 0 := by dsimp [s] at hs; linarith
    exact ⟨0,0,0,0,⟨le_rfl,h₀⟩,⟨le_rfl,h₁⟩,⟨le_rfl,h₂⟩,⟨le_rfl,h₃⟩,by simp [hm0]⟩
  · have hspos : 0 < s := by dsimp [s] at *; positivity
    have hb (c : ℝ) (hc : 0 ≤ c) : 0 ≤ m*c/s ∧ m*c/s ≤ c := by
      constructor
      · positivity
      · apply (div_le_iff₀ hspos).mpr
        dsimp [s]
        nlinarith
    refine ⟨m*c₀/s,m*c₁/s,m*c₂/s,m*c₃/s,hb _ h₀,hb _ h₁,hb _ h₂,hb _ h₃,?_⟩
    field_simp
    dsimp [s]

theorem routes_of_le_effective (t : CapacityTree) (hn : t.nonnegative)
    (m : ℝ) (hm : 0 ≤ m) (hcap : m ≤ t.effective) : Routes t m := by
  induction t generalizing m with
  | leaf c => exact Routes.leaf hm hcap
  | node c t₀ t₁ t₂ t₃ ih₀ ih₁ ih₂ ih₃ =>
    obtain ⟨hc,hn₀,hn₁,hn₂,hn₃⟩ := hn
    obtain ⟨hmcap,hmsum⟩ := le_min_iff.mp hcap
    obtain ⟨m₀,m₁,m₂,m₃,⟨hp₀,hu₀⟩,⟨hp₁,hu₁⟩,⟨hp₂,hu₂⟩,⟨hp₃,hu₃⟩,hs⟩ :=
      split_four (effective_nonnegative hn₀) (effective_nonnegative hn₁)
        (effective_nonnegative hn₂) (effective_nonnegative hn₃) hm hmsum
    exact Routes.node hm hmcap hs (ih₀ hn₀ m₀ hp₀ hu₀) (ih₁ hn₁ m₁ hp₁ hu₁)
      (ih₂ hn₂ m₂ hp₂ hu₂) (ih₃ hn₃ m₃ hp₃ hu₃)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_Content
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal NNReal

theorem content_le_cover {X : Type*} [EMetricSpace X] (s : ℝ) (E : Set X)
    (U : ℕ → Set X) (hU : E ⊆ ⋃ n, U n) :
    hausdorffContent s E ≤ ∑' n, (Metric.ediam (U n))^s :=
  iInf_le_of_le U (iInf_le _ hU)

theorem cover_diameter_bound {X : Type*} [EMetricSpace X] {s : ℝ} (hs : 0 < s)
    (U : ℕ → Set X) {r : ℝ≥0∞}
    (hcost : (∑' n, (Metric.ediam (U n))^s) ≤ r^s) (n : ℕ) :
    Metric.ediam (U n) ≤ r := by
  apply (ENNReal.rpow_le_rpow_iff hs).mp
  exact (ENNReal.le_tsum n).trans hcost

theorem hausdorffMeasure_zero_of_content_zero {X : Type*} [EMetricSpace X]
    [MeasurableSpace X] [BorelSpace X]
    {s : ℝ} (hs : 0 < s) (E : Set X) (hzero : hausdorffContent s E = 0) :
    Measure.hausdorffMeasure s E = 0 := by
  rw [Measure.hausdorffMeasure_apply]
  apply le_antisymm _ bot_le
  refine iSup_le fun r => iSup_le fun hr => ?_
  apply le_of_forall_gt
  intro ε hε
  have hrpow : 0 < r^s := by positivity
  have hc : hausdorffContent s E < min ε (r^s) := by
    rw [hzero]
    exact lt_min hε hrpow
  obtain ⟨U,hU⟩ := iInf_lt_iff.mp hc
  obtain ⟨hcover,hcost⟩ := iInf_lt_iff.mp hU
  have hdiam : ∀ n, Metric.ediam (U n) ≤ r :=
    cover_diameter_bound hs U (hcost.le.trans (min_le_right _ _))
  calc
    _ ≤ ∑' n, ⨆ _ : (U n).Nonempty, (Metric.ediam (U n))^s :=
      iInf_le_of_le U (iInf_le_of_le hcover (iInf_le _ hdiam))
    _ ≤ ∑' n, (Metric.ediam (U n))^s :=
      ENNReal.tsum_le_tsum (fun _ => iSup_le fun _ => le_rfl)
    _ < ε := hcost.trans_le (min_le_left _ _)

theorem content_positive_of_lt_dimH {X : Type*} [EMetricSpace X]
    (E : Set X) {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E) :
    0 < hausdorffContent (s : ℝ) E := by
  let : MeasurableSpace X := borel X
  let : BorelSpace X := ⟨rfl⟩
  by_contra h
  have hc : hausdorffContent (s : ℝ) E = 0 := le_antisymm (not_lt.mp h) bot_le
  have hz := hausdorffMeasure_zero_of_content_zero (by exact_mod_cast hs) E hc
  have ht := hausdorffMeasure_of_lt_dimH hd
  rw [hz] at ht
  exact ENNReal.zero_ne_top ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_ContentBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Metric
open scoped ENNReal NNReal

theorem content_le_diameter {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (E : Set X) :
    hausdorffContent s E ≤ (Metric.ediam E)^s := by
  classical
  let U : ℕ → Set X := fun n => if n = 0 then E else ∅
  have hcover : E ⊆ ⋃ n, U n := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨0,by simpa [U] using hx⟩
  calc
    hausdorffContent s E ≤ ∑' n, (Metric.ediam (U n))^s := content_le_cover s E U hcover
    _ = (Metric.ediam E)^s := by
      rw [tsum_eq_single 0]
      · simp [U]
      · intro n hn
        simp [U,hn,ENNReal.zero_rpow_of_pos hs]

theorem content_finite_of_bounded {X : Type*} [MetricSpace X]
    {s : ℝ} (hs : 0 < s) {E : Set X} (hE : Bornology.IsBounded E) :
    hausdorffContent s E < ∞ :=
  (content_le_diameter hs E).trans_lt
    (lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hs.le hE.ediam_ne_top))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_DistanceSet
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set

theorem distanceSet_eq_image (E : Set Plane) :
    distanceSet E = (fun z : Plane × Plane => dist z.1 z.2) '' (E ×ˢ E) := by
  ext r
  constructor
  · rintro ⟨x,hx,y,hy,hr⟩
    exact ⟨(x,y), ⟨hx,hy⟩, hr⟩
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩,hr⟩
    exact ⟨x,hx,y,hy,hr⟩

theorem distanceSet_isCompact {E : Set Plane} (hE : IsCompact E) :
    IsCompact (distanceSet E) := by
  rw [distanceSet_eq_image]
  exact (hE.prod hE).image (continuous_fst.dist continuous_snd)

theorem distanceSet_measurable {E : Set Plane} (hE : IsCompact E) :
    MeasurableSet (distanceSet E) :=
  (distanceSet_isCompact hE).measurableSet

theorem positive_volume_of_carried_absolutelyContinuous
    (D : Set ℝ) (τ : Measure ℝ) (hmass : 0 < τ univ)
    (hcarried : τ Dᶜ = 0) (hac : τ ≪ volume) : 0 < volume D := by
  by_contra h
  have hzero : volume D = 0 := le_antisymm (not_lt.mp h) bot_le
  have hτ : τ D = 0 := hac hzero
  have hz := measure_union_null hτ hcarried
  have : τ univ = 0 := by simpa only [union_compl_self] using hz
  exact (ne_of_gt hmass) this

theorem distanceSet_positive_of_measure (E : Set Plane) (τ : Measure ℝ)
    (hmass : 0 < τ univ) (hcarried : τ (distanceSet E)ᶜ = 0) (hac : τ ≪ volume) :
    0 < volume (distanceSet E) :=
  positive_volume_of_carried_absolutelyContinuous (distanceSet E) τ hmass hcarried hac

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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

theorem DyadicSquare.ediam_le (Q : DyadicSquare) (hQ : 0 ≤ Q.side) :
    ediam Q.carrier ≤ ENNReal.ofReal (2 * Q.side) := by
  apply Metric.ediam_le
  intro z hz w hw
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (Q.dist_le hQ hz hw)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_GeometricCapacity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem contentOuter_apply {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (U : Set X) :
    contentOuter s hs U = hausdorffContent s U := by
  rw [contentOuter, OuterMeasure.ofFunction_apply]
  rfl

theorem content_union_le {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) (U V : Set X) :
    hausdorffContent s (U ∪ V) ≤ hausdorffContent s U + hausdorffContent s V := by
  simpa only [← contentOuter_apply hs] using (measure_union_le (μ := contentOuter s hs) U V)

@[simp] theorem content_empty {X : Type*} [EMetricSpace X]
    {s : ℝ} (hs : 0 < s) : hausdorffContent s (∅ : Set X) = 0 := by
  rw [← contentOuter_apply hs]
  exact measure_empty

theorem occupiedCapacity_nonneg (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 ≤ Q.side) : 0 ≤ occupiedCapacity E s Q := by
  unfold occupiedCapacity
  split_ifs <;> positivity

theorem geometricTree_nonnegative (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) :
    (geometricTree E s Q K).nonnegative := by
  induction K generalizing Q with
  | zero => exact occupiedCapacity_nonneg E s Q hQ.le
  | succ K ih =>
    exact ⟨occupiedCapacity_nonneg E s Q hQ.le,
      ih _ (Q.child_side_pos hQ _ _), ih _ (Q.child_side_pos hQ _ _),
      ih _ (Q.child_side_pos hQ _ _), ih _ (Q.child_side_pos hQ _ _)⟩

theorem content_le_occupiedCapacity (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) (hQ : 0 < Q.side) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((2 : ℝ)^s * occupiedCapacity E s Q) := by
  classical
  by_cases h : (E ∩ Q.carrier).Nonempty
  · rw [occupiedCapacity, ite_eq_left h, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hQ.le]
    calc
      hausdorffContent s (E ∩ Q.carrier) ≤ (ediam (E ∩ Q.carrier))^s :=
        content_le_diameter hs _
      _ ≤ (ENNReal.ofReal (2 * Q.side))^s :=
        ENNReal.rpow_le_rpow ((ediam_mono inter_subset_right).trans (Q.ediam_le hQ.le)) hs.le
      _ = ENNReal.ofReal ((2 * Q.side)^s) := by
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le]
  · rw [not_nonempty_iff_eq_empty.mp h, content_empty hs,
      occupiedCapacity, ite_eq_right h, mul_zero, ENNReal.ofReal_zero]

theorem content_le_children (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      hausdorffContent s (E ∩ (Q.child false false).carrier) +
      hausdorffContent s (E ∩ (Q.child false true).carrier) +
      hausdorffContent s (E ∩ (Q.child true false).carrier) +
      hausdorffContent s (E ∩ (Q.child true true).carrier) := by
  rw [Q.cover_children, inter_union_distrib_left,
    inter_union_distrib_left, inter_union_distrib_left]
  exact (content_union_le hs _ _).trans (by
    have h0 := content_union_le hs (E ∩ (Q.child false false).carrier)
      (E ∩ (Q.child false true).carrier)
    have h1 := content_union_le hs (E ∩ (Q.child true false).carrier)
      (E ∩ (Q.child true true).carrier)
    simpa only [add_assoc] using add_le_add h0 h1)

theorem content_le_geometric_effective (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) :
    hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((2 : ℝ)^s * (geometricTree E s Q K).effective) := by
  induction K generalizing Q with
  | zero => exact content_le_occupiedCapacity E hs Q hQ
  | succ K ih =>
    have hn (i j : Bool) := effective_nonnegative
      (geometricTree_nonnegative E s (Q.child i j) (Q.child_side_pos hQ i j) K)
    have hsum := add_le_add
      (add_le_add (add_le_add (ih _ (Q.child_side_pos hQ false false))
        (ih _ (Q.child_side_pos hQ false true)))
        (ih _ (Q.child_side_pos hQ true false)))
        (ih _ (Q.child_side_pos hQ true true))
    have hcost := (content_le_children E hs Q).trans hsum
    simp only [geometricTree, CapacityTree.effective]
    have h00 := hn false false
    have h01 := hn false true
    have h10 := hn true false
    have h11 := hn true true
    have hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
        ENNReal.ofReal ((2 : ℝ)^s * (a+b)) =
          ENNReal.ofReal ((2 : ℝ)^s*a) + ENNReal.ofReal ((2 : ℝ)^s*b) := by
      intro a b ha hb
      rw [mul_add, ENNReal.ofReal_add (by positivity) (by positivity)]
    by_cases h : occupiedCapacity E s Q ≤
        (geometricTree E s (Q.child false false) K).effective +
        (geometricTree E s (Q.child false true) K).effective +
        (geometricTree E s (Q.child true false) K).effective +
        (geometricTree E s (Q.child true true) K).effective
    · rw [min_eq_left h]
      exact content_le_occupiedCapacity E hs Q hQ
    · rw [min_eq_right (le_of_not_ge h), hadd _ _ (by positivity) h11,
        hadd _ _ (by positivity) h10, hadd _ _ h00 h01]
      exact hcost

theorem exists_uniform_geometric_routes (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∀ K : ℕ, Routes (geometricTree E s Q K) c := by
  have hs' : 0 < (s : ℝ) := by exact_mod_cast hs
  have hp := content_positive_of_lt_dimH E hs hd
  have hf := content_finite_of_bounded hs' hE.isBounded
  have hF : 0 < (2 : ℝ)^(s : ℝ) := by positivity
  let c := (hausdorffContent (s : ℝ) E).toReal / (2 : ℝ)^(s : ℝ)
  have hc : 0 < c := div_pos (ENNReal.toReal_pos (ne_of_gt hp) (ne_of_lt hf)) hF
  refine ⟨c,hc,fun K => routes_of_le_effective _
    (geometricTree_nonnegative E s Q hQ K) c hc.le ?_⟩
  have hb := content_le_geometric_effective E hs' Q hQ K
  rw [inter_eq_left.mpr hEQ] at hb
  have hn := effective_nonnegative (geometricTree_nonnegative E s Q hQ K)
  have hr := ENNReal.toReal_mono (by simp :
    ENNReal.ofReal ((2 : ℝ)^(s : ℝ) * (geometricTree E s Q K).effective) ≠ ∞) hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hF.le hn)] at hr
  exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hr)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem measure_zero_of_disjoint_carrier {X : Type*} [MeasurableSpace X]
    (μ : Measure X) {A B : Set X} (hAB : Disjoint A B) (hμ : μ Bᶜ = 0) :
    μ A = 0 :=
  measure_mono_null (fun _ hx hy => Set.disjoint_left.mp hAB hx hy) hμ

theorem four_measures_on_branch (Q : DyadicSquare)
    (μ : Bool → Bool → Measure Plane)
    (hμ : ∀ i j, μ i j (Q.child i j).carrierᶜ = 0)
    (i j : Bool) {A : Set Plane} (hA : A ⊆ (Q.child i j).carrier) :
    (μ false false + μ false true + μ true false + μ true true) A = μ i j A := by
  have hz (k l : Bool) (h : (i,j) ≠ (k,l)) : μ k l A = 0 :=
    measure_zero_of_disjoint_carrier _ ((Q.children_disjoint h).mono_left hA) (hμ k l)
  cases i <;> cases j <;>
    simp only [Measure.add_apply] <;>
    simp [hz false false, hz false true, hz true false, hz true true]

theorem routes_mass_bounds {t : CapacityTree} {m : ℝ} (h : Routes t m) :
    0 ≤ m ∧ m ≤ t.rootCapacity := by
  cases h with
  | leaf hm hc => exact ⟨hm,hc⟩
  | node hm hc _ _ _ _ _ => exact ⟨hm,hc⟩

theorem measure_from_geometric_routes (E : Set Plane) (s : ℝ)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (K : ℕ) (m : ℝ)
    (hroute : Routes (geometricTree E s Q K) m) :
    ∃ μ : Measure Plane, μ univ = ENNReal.ofReal m ∧
      μ (E ∩ Q.carrier)ᶜ = 0 ∧ DyadicMassBounds s Q K μ := by
  classical
  induction K generalizing Q m with
  | zero =>
    have hm := (routes_mass_bounds hroute).1
    have hc : m ≤ occupiedCapacity E s Q := (routes_mass_bounds hroute).2
    by_cases h : (E ∩ Q.carrier).Nonempty
    · obtain ⟨x,hx⟩ := h
      refine ⟨ENNReal.ofReal m • Measure.dirac x, by simp, ?_, ?_⟩
      · simp [Measure.smul_apply, hx]
      · intro p hp
        have : p = [] := by cases p <;> simp_all
        subst p
        change (ENNReal.ofReal m • Measure.dirac x) Q.carrier ≤ ENNReal.ofReal (Q.side^s)
        rw [occupiedCapacity, ite_eq_left ⟨x,hx⟩] at hc
        simpa [Measure.smul_apply, Measure.dirac_apply' _ Q.measurable, hx.2] using
          ENNReal.ofReal_le_ofReal hc
    · have hm0 : m = 0 := by rw [occupiedCapacity, ite_eq_right h] at hc; linarith
      refine ⟨0,by simp [hm0],by simp,?_⟩
      intro p hp
      simp
  | succ K ih =>
    cases hroute with
    | node hm hc hsum hr00 hr01 hr10 hr11 =>
      obtain ⟨μ00,hm00,hc00,hb00⟩ := ih _ (Q.child_side_pos hQ false false) _ hr00
      obtain ⟨μ01,hm01,hc01,hb01⟩ := ih _ (Q.child_side_pos hQ false true) _ hr01
      obtain ⟨μ10,hm10,hc10,hb10⟩ := ih _ (Q.child_side_pos hQ true false) _ hr10
      obtain ⟨μ11,hm11,hc11,hb11⟩ := ih _ (Q.child_side_pos hQ true true) _ hr11
      let μ : Bool → Bool → Measure Plane := fun i j =>
        if i then (if j then μ11 else μ10) else (if j then μ01 else μ00)
      have hcarry : ∀ i j, μ i j (E ∩ (Q.child i j).carrier)ᶜ = 0 := by
        intro i j; cases i <;> cases j <;> assumption
      have hchild : ∀ i j, μ i j (Q.child i j).carrierᶜ = 0 := by
        intro i j
        exact measure_mono_null (compl_subset_compl.mpr inter_subset_right) (hcarry i j)
      have hparent : ∀ i j, μ i j (E ∩ Q.carrier)ᶜ = 0 := by
        intro i j
        apply measure_mono_null _ (hcarry i j)
        exact compl_subset_compl.mpr (inter_subset_inter_right E (Q.child_subset hQ.le i j))
      have hbounds : ∀ i j, DyadicMassBounds s (Q.child i j) K (μ i j) := by
        intro i j; cases i <;> cases j <;> assumption
      let ν := μ00 + μ01 + μ10 + μ11
      have hmass : ν univ = ENNReal.ofReal m := by
        simp only [ν, Measure.add_apply, hm00,hm01,hm10,hm11]
        rw [← ENNReal.ofReal_add (routes_mass_bounds hr00).1 (routes_mass_bounds hr01).1,
          ← ENNReal.ofReal_add (add_nonneg (routes_mass_bounds hr00).1
            (routes_mass_bounds hr01).1) (routes_mass_bounds hr10).1,
          ← ENNReal.ofReal_add (add_nonneg (add_nonneg (routes_mass_bounds hr00).1
            (routes_mass_bounds hr01).1) (routes_mass_bounds hr10).1)
            (routes_mass_bounds hr11).1, hsum]
      refine ⟨ν,hmass,?_,?_⟩
      · change (μ false false + μ false true + μ true false + μ true true) _ = 0
        simp only [Measure.add_apply, hparent, add_zero]
      · intro p hp
        cases p with
        | nil =>
          have hcap : occupiedCapacity E s Q ≤ Q.side^s := by
            unfold occupiedCapacity; split_ifs
            · exact le_rfl
            · positivity
          exact (measure_mono (subset_univ _)).trans (hmass ▸ ENNReal.ofReal_le_ofReal
            (hc.trans hcap))
        | cons a p =>
          change (μ false false + μ false true + μ true false + μ true true)
            ((Q.child a.1 a.2).descendant p).carrier ≤ _
          rw [four_measures_on_branch Q μ hchild a.1 a.2
            ((Q.child a.1 a.2).descendant_subset (Q.child_side_pos hQ a.1 a.2) p)]
          exact hbounds a.1 a.2 p (by simpa using Nat.le_of_succ_le_succ hp)

theorem exists_dyadic_probability_sequence (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E)
    (Q : DyadicSquare) (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∃ ζ : ℕ → ProbabilityMeasure Plane,
      ∀ K, (ζ K : Measure Plane) Eᶜ = 0 ∧
        ∀ p : List (Bool × Bool), p.length ≤ K →
          (ζ K : Measure Plane) (Q.descendant p).carrier ≤
            ENNReal.ofReal (c⁻¹ * (Q.descendant p).side^(s : ℝ)) := by
  classical
  obtain ⟨c,hc,hr⟩ := exists_uniform_geometric_routes E hE hs hd Q hQ hEQ
  choose μ hmass hcarry hb using fun K =>
    measure_from_geometric_routes E s Q hQ K c (hr K)
  have hprob (K : ℕ) : IsProbabilityMeasure (ENNReal.ofReal c⁻¹ • μ K) := by
    constructor
    rw [Measure.smul_apply, smul_eq_mul, hmass K,
      ← ENNReal.ofReal_mul (by positivity), inv_mul_cancel₀ hc.ne', ENNReal.ofReal_one]
  let ζ : ℕ → ProbabilityMeasure Plane := fun K => ⟨ENNReal.ofReal c⁻¹ • μ K,hprob K⟩
  refine ⟨c,hc,ζ,fun K => ⟨?_,?_⟩⟩
  · have he : μ K Eᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_left) (hcarry K)
    simp [ζ, Measure.smul_apply, he]
  · intro p hp
    change (ENNReal.ofReal c⁻¹ • μ K) _ ≤ _
    rw [Measure.smul_apply, smul_eq_mul, ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right (hb K p hp) _

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicPacking
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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

theorem DyadicSquare.box_measurable (Q : DyadicSquare) : MeasurableSet Q.box :=
  measurableSet_Ico.prod measurableSet_Ico

theorem DyadicSquare.box_area (Q : DyadicSquare) :
    (volume.prod volume) Q.box = ENNReal.ofReal Q.side * ENNReal.ofReal Q.side := by
  simp [box, Measure.prod_prod, Real.volume_Ico]

theorem DyadicSquare.boxes_disjoint (Q : DyadicSquare) (hQ : 0 < Q.side)
    {p q : List (Bool × Bool)} (hlen : p.length = q.length) (hne : p ≠ q) :
    Disjoint (Q.descendant p).box (Q.descendant q).box := by
  apply Set.disjoint_left.mpr
  intro z hp hq
  exact Set.disjoint_left.mp (Q.descendants_disjoint hQ hlen hne)
    ((pairToPlane_mem _ _).mpr hp) ((pairToPlane_mem _ _).mpr hq)

theorem plane_coordinate_dist_le (z x : Plane) (i : Fin 2) :
    |z i - x i| ≤ dist z x := by
  simpa only [Real.dist_eq] using PiLp.dist_apply_le z x i

theorem box_subset_of_meets_ball (Q : DyadicSquare) (x : Plane) {r w : ℝ}
    (hside : Q.side = w) (hr : r ≤ w)
    (hmeet : (Q.carrier ∩ ball x r).Nonempty) :
    Q.box ⊆ Icc (x 0-2*w) (x 0+2*w) ×ˢ Icc (x 1-2*w) (x 1+2*w) := by
  obtain ⟨z,hz,hball⟩ := hmeet
  have h0 := (plane_coordinate_dist_le z x 0).trans_lt hball
  have h1 := (plane_coordinate_dist_le z x 1).trans_lt hball
  have hx0 := abs_lt.mp h0
  have hx1 := abs_lt.mp h1
  intro u hu
  simp only [DyadicSquare.box, mem_prod, mem_Ico] at hu
  simp only [DyadicSquare.carrier, mem_ofPred_eq] at hz
  simp only [mem_prod, mem_Icc]
  rw [hside] at hz hu
  constructor <;> constructor <;> linarith [hu.1.1,hu.1.2,hu.2.1,hu.2.2,
    hz.1,hz.2.1,hz.2.2.1,hz.2.2.2,hx0.1,hx0.2,hx1.1,hx1.2]

theorem dyadic_ball_card_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (n : ℕ) (x : Plane) {r : ℝ} (hr : r ≤ Q.side/(2 : ℝ)^n) :
    (cellsMeeting Q n x r).card ≤ 16 := by
  classical
  let S := (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty
  let w := Q.side/(2 : ℝ)^n
  have hw : 0 < w := by dsimp [w]; positivity
  have hlen {path : List (Bool × Bool)} (hp : path ∈ S) : path.length = n :=
    (mem_dyadicPaths n path).mp (Finset.mem_filter.mp hp).1
  have hside {path : List (Bool × Bool)} (hp : path ∈ S) :
      (Q.descendant path).side = w := by
    rw [Q.descendant_side, hlen hp]
  have hdis : PairwiseDisjoint (S : Set (List (Bool × Bool)))
      (fun p => (Q.descendant p).box) := by
    intro p hp q hq hpq
    exact Q.boxes_disjoint hQ ((hlen hp).trans (hlen hq).symm) hpq
  have harea : (∑ p ∈ S, ENNReal.ofReal w * ENNReal.ofReal w) ≤
      ENNReal.ofReal (4*w) * ENNReal.ofReal (4*w) := by
    calc
      _ = ∑ p ∈ S, (volume.prod volume) (Q.descendant p).box := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [DyadicSquare.box_area, hside hp]
      _ = (volume.prod volume) (⋃ p ∈ S, (Q.descendant p).box) :=
        (measure_biUnion_finset hdis (fun p _ => (Q.descendant p).box_measurable)).symm
      _ ≤ (volume.prod volume)
          (Icc (x 0-2*w) (x 0+2*w) ×ˢ Icc (x 1-2*w) (x 1+2*w)) := by
        apply measure_mono
        intro u hu
        obtain ⟨p,hp,hu⟩ := mem_iUnion₂.mp hu
        exact box_subset_of_meets_ball _ x (hside hp) hr
          (Finset.mem_filter.mp hp).2 hu
      _ = _ := by
        rw [Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
        congr 2 <;> ring
  have hreal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) harea
  simp only [Finset.sum_const, nsmul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast, ENNReal.toReal_ofReal hw.le,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ 4*w)] at hreal
  have hcard : (S.card : ℝ) ≤ 16 := by
    by_contra h
    have hpos := mul_pos (show 0 < (S.card : ℝ)-16 by linarith) (mul_pos hw hw)
    nlinarith [hreal]

  exact_mod_cast hcard

theorem dyadic_ball_measure_le (Q : DyadicSquare) (hQ : 0 < Q.side)
    (μ : Measure Plane) (hcarry : μ Q.carrierᶜ = 0)
    (s C : ℝ) (hC : 0 ≤ C) (n : ℕ)
    (hb : ∀ p : List (Bool × Bool), p.length = n →
      μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(Q.descendant p).side^s))
    (x : Plane) {r : ℝ} (hr : r ≤ Q.side/(2 : ℝ)^n) :
    μ (ball x r) ≤ ENNReal.ofReal (16*C*(Q.side/(2 : ℝ)^n)^s) := by
  classical
  let S := (dyadicPaths n).filter fun p =>
    ((Q.descendant p).carrier ∩ ball x r).Nonempty
  have hcover : ball x r ⊆ (⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ := by
    intro z hz
    by_cases hQz : z ∈ Q.carrier
    · obtain ⟨p,hp,hzp⟩ := Q.mem_descendant_at_depth n hQz
      exact Or.inl (mem_iUnion₂.mpr ⟨p,Finset.mem_filter.mpr ⟨hp,⟨z,hzp,hz⟩⟩,hzp⟩)
    · exact Or.inr hQz
  calc
    μ (ball x r) ≤ μ ((⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ) := measure_mono hcover
    _ ≤ μ (⋃ p ∈ S, (Q.descendant p).carrier) + μ Q.carrierᶜ := measure_union_le _ _
    _ = μ (⋃ p ∈ S, (Q.descendant p).carrier) := by rw [hcarry, add_zero]
    _ ≤ ∑ p ∈ S, μ (Q.descendant p).carrier := measure_biUnion_finset_le _ _
    _ ≤ ∑ p ∈ S, ENNReal.ofReal (C*(Q.side/(2 : ℝ)^n)^s) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := (mem_dyadicPaths n p).mp (Finset.mem_filter.mp hp).1
      simpa only [Q.descendant_side, hl] using hb p hl
    _ ≤ (16 : ℝ≥0∞) * ENNReal.ofReal (C*(Q.side/(2 : ℝ)^n)^s) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast dyadic_ball_card_le Q hQ n x hr) _
    _ = _ := by
      rw [show (16 : ℝ≥0∞) = ENNReal.ofReal (16 : ℝ) by norm_num,
        ← ENNReal.ofReal_mul' (mul_nonneg hC (Real.rpow_nonneg (by positivity) _))]
      congr 1
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_WeakLimit
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem compact_carried_probabilities (E : Set Plane) (hE : IsCompact E) :
    IsCompact {μ : ProbabilityMeasure Plane | (μ : Measure Plane) Eᶜ = 0} := by
  have compactBound := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ => 0) (K := fun _ => E) tendsto_const_nhds (fun _ => hE)
    (Or.inr monotone_const)
  simpa only [le_zero_iff, forall_const, ProbabilityMeasure.null_iff_toMeasure_null]
    using compactBound

theorem exists_carried_weak_subsequence (E : Set Plane) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure Plane) (hμ : ∀ K, (μ K : Measure Plane) Eᶜ = 0) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ζ) :=
  (compact_carried_probabilities E hE).tendsto_subseq hμ

theorem weak_limit_ball_bound (μ : ℕ → ProbabilityMeasure Plane)
    (ζ : ProbabilityMeasure Plane) (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hlim : Tendsto (μ ∘ φ) atTop (𝓝 ζ))
    (x : Plane) (r : ℝ) (B : ℝ≥0∞)
    (hbound : ∀ᶠ K in atTop, (μ K : Measure Plane) (ball x r) ≤ B) :
    (ζ : Measure Plane) (ball x r) ≤ B := by
  have h := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim (G := ball x r) isOpen_ball
  apply h.trans
  have hb := hφ.tendsto_atTop.eventually hbound
  exact (liminf_le_liminf hb).trans_eq (liminf_const B)

theorem frostman_of_eventual_ball_bounds (E : Set Plane) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure Plane) (hμ : ∀ K, (μ K : Measure Plane) Eᶜ = 0)
    (s C : ℝ)
    (hbound : ∀ x : Plane, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∀ x : Plane, ∀ r > 0,
        (ζ : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  obtain ⟨ζ,hζ,φ,hφ,hlim⟩ := exists_carried_weak_subsequence E hE μ hμ
  exact ⟨ζ,hζ,fun x r hr => weak_limit_ball_bound μ ζ φ hφ hlim x r _ (hbound x r hr)⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_Frostman
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem exists_containing_square (E : Set Plane) (hE : IsCompact E) :
    ∃ Q : DyadicSquare, 0 < Q.side ∧ E ⊆ Q.carrier := by
  obtain ⟨R,hR,hbound⟩ := hE.isBounded.exists_pos_norm_lt
  refine ⟨⟨-R,-R,2*R⟩,by positivity,?_⟩
  intro z hz
  have h0 : |z 0| < R := (PiLp.norm_apply_le z 0).trans_lt (hbound z hz)
  have h1 : |z 1| < R := (PiLp.norm_apply_le z 1).trans_lt (hbound z hz)
  obtain ⟨h0l,h0r⟩ := abs_lt.mp h0
  obtain ⟨h1l,h1r⟩ := abs_lt.mp h1
  change -R ≤ z 0 ∧ z 0 < -R+2*R ∧ -R ≤ z 1 ∧ z 1 < -R+2*R
  exact ⟨h0l.le,by linarith,h1l.le,by linarith⟩

theorem exists_dyadic_scale {L r : ℝ} (hL : 0 < L) (hr : 0 < r) (hrL : r ≤ L) :
    ∃ n : ℕ, r ≤ L/(2 : ℝ)^n ∧ L/(2 : ℝ)^n < 2*r := by
  obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one
    (div_pos hr hL) ((div_le_one hL).mpr hrL)
    (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
  have hh := (div_le_iff₀ hL).mp hhi
  have hl := (lt_div_iff₀ hL).mp hlo
  simp only [div_pow, one_pow, pow_succ] at hh hl
  refine ⟨n,by simpa only [one_div, mul_comm, ← div_eq_mul_inv] using hh,?_⟩
  have heq : 1/(2 : ℝ)^n*(1/2)*L = (L/(2 : ℝ)^n)/2 := by ring
  rw [heq] at hl
  linarith

theorem eventual_ball_bounds_of_dyadic (Q : DyadicSquare) (hQ : 0 < Q.side)
    (s : ℝ) (hs : 0 < s) (c : ℝ) (hc : 0 < c)
    (μ : ℕ → ProbabilityMeasure Plane)
    (hcarry : ∀ K, (μ K : Measure Plane) Q.carrierᶜ = 0)
    (hb : ∀ K, ∀ p : List (Bool × Bool), p.length ≤ K →
      (μ K : Measure Plane) (Q.descendant p).carrier ≤
        ENNReal.ofReal (c⁻¹*(Q.descendant p).side^s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Plane, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  let C := max (16*c⁻¹*(2 : ℝ)^s) (Q.side^s)⁻¹
  have hside : 0 < Q.side^s := Real.rpow_pos_of_pos hQ s
  have hC : 0 < C := (inv_pos.mpr hside).trans_le (le_max_right _ _)
  refine ⟨C,hC,fun x r hr => ?_⟩
  by_cases hrQ : r ≤ Q.side
  · obtain ⟨n,hrn,hnr⟩ := exists_dyadic_scale hQ hr hrQ
    filter_upwards [eventually_ge_atTop n] with K hK
    have hball := dyadic_ball_measure_le Q hQ (μ K) (hcarry K) s c⁻¹
      (by positivity) n (fun p hp => hb K p (hp ▸ hK)) x hrn
    apply hball.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ Q.side/(2 : ℝ)^n) hnr.le hs.le
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le] at hp
    calc
      16*c⁻¹*(Q.side/(2 : ℝ)^n)^s ≤ 16*c⁻¹*((2 : ℝ)^s*r^s) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = (16*c⁻¹*(2 : ℝ)^s)*r^s := by ring
      _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply Filter.Eventually.of_forall
    intro K
    have hpow := Real.rpow_le_rpow hQ.le (le_of_not_ge hrQ) hs.le
    have hlarge : 1 ≤ C*r^s := by
      calc
        1 = (Q.side^s)⁻¹ * Q.side^s := (inv_mul_cancel₀ hside.ne').symm
        _ ≤ (Q.side^s)⁻¹*r^s := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      (μ K : Measure Plane) (ball x r) ≤ (μ K : Measure Plane) univ := measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C*r^s) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlarge

theorem frostman_probability (E : Set Plane) (hE : IsCompact E)
    {s : ℝ≥0} (hs : 0 < s) (hd : (s : ℝ≥0∞) < dimH E) :
    ∃ ζ : ProbabilityMeasure Plane, (ζ : Measure Plane) Eᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x : Plane, ∀ r > 0,
        (ζ : Measure Plane) (ball x r) ≤ ENNReal.ofReal (C*r^(s : ℝ)) := by
  obtain ⟨Q,hQ,hEQ⟩ := exists_containing_square E hE
  obtain ⟨c,hc,μ,hμ⟩ := exists_dyadic_probability_sequence E hE hs hd Q hQ hEQ
  have hcarry : ∀ K, (μ K : Measure Plane) Q.carrierᶜ = 0 := fun K =>
    measure_mono_null (compl_subset_compl.mpr hEQ) (hμ K).1
  obtain ⟨C,hC,hball⟩ := eventual_ball_bounds_of_dyadic Q hQ s
    (by exact_mod_cast hs) c hc μ hcarry (fun K => (hμ K).2)
  obtain ⟨ζ,hζ,hbound⟩ := frostman_of_eventual_ball_bounds E hE μ (fun K => (hμ K).1) s C hball
  exact ⟨ζ,hζ,C,hC,hbound⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem noAtoms_of_ball_bound (μ : Measure Plane) {s C : ℝ}
    (hs : 0 < s) (hb : BallBound μ s C) : NullSingletonClass μ := by
  constructor
  intro x
  have hlim : Tendsto (fun r : ℝ => ENNReal.ofReal (C*r^s)) (𝓝[>] 0) (𝓝 0) := by
    have hcont : Continuous (fun r : ℝ => ENNReal.ofReal (C*r^s)) := ENNReal.continuous_ofReal.comp
      (continuous_const.mul (Real.continuous_rpow_const hs.le))
    simpa [Real.zero_rpow hs.ne'] using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  apply le_antisymm _ bot_le
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (measure_mono (singleton_subset_iff.mpr (mem_ball_self hr))).trans (hb x r hr)

theorem energyScale_pos (n : ℕ) : 0 < energyScale n := by
  unfold energyScale
  positivity

theorem riesz_kernel_majorant (x y : Plane) {u : ℝ} (hu : 0 < u) (hxy : x ≠ y) :
    (edist x y)^(-u) ≤ 1 + ∑' n : ℕ, energyMajorantTerm x u n y := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have heq : (edist x y)^(-u) = ENNReal.ofReal ((dist x y)^(-u)) := by
    rw [edist_dist, ENNReal.ofReal_rpow_of_pos hd]
  rw [heq]
  by_cases hlarge : 1 ≤ dist x y
  · have hle : (dist x y)^(-u) ≤ 1 := by
      simpa using Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1)
        hlarge (neg_nonpos.mpr hu.le)
    exact (show ENNReal.ofReal ((dist x y)^(-u)) ≤ 1 by
      simpa using ENNReal.ofReal_le_ofReal hle).trans (le_add_right le_rfl)
  · obtain ⟨n,hlo,hhi⟩ := exists_nat_pow_near_of_lt_one hd (le_of_not_ge hlarge)
      (by norm_num : (0 : ℝ) < 1/2) (by norm_num : (1/2 : ℝ) < 1)
    have hlo' : energyScale n/2 < dist x y := by
      simpa [energyScale,pow_succ,div_eq_mul_inv] using hlo
    have hball : y ∈ ball x (2*energyScale n) := by
      rw [mem_ball, dist_comm]
      have hpos := energyScale_pos n
      change dist x y ≤ energyScale n at hhi
      linarith
    have hpoint : (edist x y)^(-u) ≤ energyMajorantTerm x u n y := by
      rw [heq, energyMajorantTerm, indicator_of_mem hball]
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos
        (div_pos (energyScale_pos n) (by norm_num)) hlo'.le (by linarith))
    rw [heq] at hpoint
    exact hpoint.trans ((ENNReal.le_tsum (f := fun index : ℕ =>
      energyMajorantTerm x u index y) n).trans (le_add_left le_rfl))

theorem energy_scale_identity (n : ℕ) (u s C : ℝ) :
    (energyScale n/2)^(-u) * (C*(2*energyScale n)^s) =
      ((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n := by
  have ha : (0 : ℝ) < 1/2 := by norm_num
  have hn := energyScale_pos n
  have hadd : (energyScale n)^(-u)*(energyScale n)^s = (energyScale n)^(s-u) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  have hpow : (energyScale n)^(s-u) = ((1/2 : ℝ)^(s-u))^n := by
    rw [energyScale, ← Real.rpow_natCast_mul ha.le, mul_comm,
      Real.rpow_mul_natCast ha.le]
  rw [show energyScale n/2 = energyScale n*(1/2) by ring,
    Real.mul_rpow hn.le ha.le,
    Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn.le]
  calc
    _ = ((1/2 : ℝ)^(-u)*C*2^s) * ((energyScale n)^(-u)*(energyScale n)^s) := by ring
    _ = _ := by rw [hadd,hpow]

theorem energy_term_integral_le (μ : Measure Plane) {s C : ℝ}
    (hb : BallBound μ s C) (x : Plane) (u : ℝ) (n : ℕ) :
    (∫⁻ y, energyMajorantTerm x u n y ∂μ) ≤
      ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s) *
        (ENNReal.ofReal ((1/2 : ℝ)^(s-u)))^n := by
  rw [energyMajorantTerm, lintegral_indicator_const measurableSet_ball]
  calc
    _ ≤ ENNReal.ofReal ((energyScale n/2)^(-u)) *
        ENNReal.ofReal (C*(2*energyScale n)^s) :=
      mul_le_mul_right (hb x _ (mul_pos (by norm_num) (energyScale_pos n))) _
    _ = ENNReal.ofReal (((1/2 : ℝ)^(-u)*C*2^s) * ((1/2 : ℝ)^(s-u))^n) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg
        (div_nonneg (energyScale_pos n).le (by norm_num)) _), energy_scale_identity]
    _ = _ := by
      rw [ENNReal.ofReal_mul' (by positivity), ENNReal.ofReal_pow (by positivity)]

theorem riesz_potential_uniform_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : BallBound μ s C) :
    ∃ B : ℝ≥0∞, B < ∞ ∧ ∀ x, rieszPotential μ u x ≤ B := by
  let := noAtoms_of_ball_bound μ (hu.trans hus) hb
  let a : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(s-u))
  let D : ℝ≥0∞ := ENNReal.ofReal ((1/2 : ℝ)^(-u)*C*2^s)
  have ha : a < 1 := by
    exact ENNReal.ofReal_lt_one.mpr (Real.rpow_lt_one (by norm_num) (by norm_num) (sub_pos.mpr hus))
  have hsum : (∑' n : ℕ, a^n) < ∞ := tsum_geometric_lt_top.mpr ha
  refine ⟨μ univ + D * ∑' n : ℕ, a^n,
    ENNReal.add_lt_top.mpr ⟨measure_lt_top μ univ,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hsum⟩,?_⟩
  intro x
  have hm (n : ℕ) : Measurable (energyMajorantTerm x u n) :=
    measurable_const.indicator measurableSet_ball
  have hxy : ∀ᵐ y ∂μ, x ≠ y := by
    rw [ae_iff]
    simp
  calc
    rieszPotential μ u x ≤ ∫⁻ y, 1 + ∑' n : ℕ, energyMajorantTerm x u n y ∂μ := by
      apply lintegral_mono_ae
      filter_upwards [hxy] with y hy
      exact riesz_kernel_majorant x y hu hy
    _ = μ univ + ∑' n : ℕ, ∫⁻ y, energyMajorantTerm x u n y ∂μ := by
      rw [lintegral_add_left measurable_const, lintegral_tsum (fun n => (hm n).aemeasurable)]
      simp
    _ ≤ μ univ + ∑' n : ℕ, D*a^n :=
      add_le_add_right (ENNReal.tsum_le_tsum (fun n => energy_term_integral_le μ hb x u n)) _
    _ = _ := by rw [ENNReal.tsum_mul_left]

theorem rieszEnergy_lt_top_of_ball_bound (μ : Measure Plane) [IsFiniteMeasure μ]
    {s C u : ℝ} (hu : 0 < u) (hus : u < s) (hb : BallBound μ s C) :
    rieszEnergy μ u < ∞ := by
  obtain ⟨B,hB,hpot⟩ := riesz_potential_uniform_bound μ hu hus hb
  calc
    rieszEnergy μ u ≤ ∫⁻ _ : Plane, B ∂μ := lintegral_mono hpot
    _ = B * μ univ := lintegral_const B
    _ < ∞ := ENNReal.mul_lt_top hB (measure_lt_top μ univ)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_BoundedDualDensity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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
-- module Solutions.OAIQ088_FD.Falconer_Measures_FiniteLpIntegral
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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
  exact tendsto_integral_of_L1' (hfi := by first | fun_prop | assumption | solve_by_elim | exact Lp.aestronglyMeasurable _ | (apply Measurable.aestronglyMeasurable; solve_by_elim) | (apply Continuous.aestronglyMeasurable; solve_by_elim) | (apply Measurable.aestronglyMeasurable; measurability) | measurability) f
    (Eventually.of_forall (fun g => (hmem g).integrable hq)) ht1

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialPreparation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_frostman_above_one (E : Set Plane) (hE : IsCompact E)
    (hd : 1 < dimH E) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∃ ζ : ProbabilityMeasure Plane,
      (ζ : Measure Plane) Eᶜ = 0 ∧ NullSingletonClass (ζ : Measure Plane) ∧
      ∃ C : ℝ, 0 < C ∧ BallBound ζ (1+δ) C ∧
        ∀ u : ℝ, 0 < u → u < 1+δ → rieszEnergy ζ u < ∞ := by
  obtain ⟨a,ha1,ha⟩ := exists_between (lt_min hd (by norm_num : (1 : ℝ≥0∞) < 2))
  have ha2 := ha.trans_le (min_le_right _ _)
  have hatop : a ≠ ∞ := ne_of_lt (ha2.trans_le (le_top))
  have har1 : 1 < a.toReal := by
    simpa using (ENNReal.toReal_lt_toReal (by simp) hatop).mpr ha1
  have har2 : a.toReal < 2 := by
    simpa using (ENNReal.toReal_lt_toReal hatop (by simp)).mpr ha2
  have has : 0 < a.toNNReal := ENNReal.toNNReal_pos (zero_lt_one.trans ha1).ne' hatop
  obtain ⟨ζ,hζ,C,hC,hb⟩ := frostman_probability E hE has
    (by rw [ENNReal.coe_toNNReal hatop]; exact ha.trans_le (min_le_left _ _))
  have hball : BallBound ζ (1+(a.toReal-1)) C := by
    simpa only [BallBound, add_sub_cancel, ENNReal.toReal] using hb
  refine ⟨a.toReal-1,by linarith,by linarith,ζ,hζ,
    noAtoms_of_ball_bound ζ (by linarith) hball,C,hC,hball,?_⟩
  intro u hu hus
  exact rieszEnergy_lt_top_of_ball_bound ζ hu hus hball

theorem normalized_restriction_ball_bound (μ : ProbabilityMeasure Plane)
    {s C : ℝ} (hb : BallBound μ s C) (hC : 0 < C)
    (A : Set Plane) (hA : MeasurableSet A) (hpos : 0 < (μ : Measure Plane) A) :
    ∃ ν : ProbabilityMeasure Plane, (ν : Measure Plane) Aᶜ = 0 ∧
      ∃ D : ℝ, 0 < D ∧ BallBound ν s D ∧
        (ν : Measure Plane) = (ENNReal.ofReal (((μ : Measure Plane) A).toReal))⁻¹ •
          (μ : Measure Plane).restrict A := by
  let m := ((μ : Measure Plane) A).toReal
  have hm : 0 < m := ENNReal.toReal_pos hpos.ne' (measure_ne_top _ _)
  have hmass : (μ : Measure Plane).restrict A univ = ENNReal.ofReal m := by
    rw [Measure.restrict_apply MeasurableSet.univ, univ_inter,
      ENNReal.ofReal_toReal (measure_ne_top _ _)]
  let ν₀ := ENNReal.ofReal m⁻¹ • (μ : Measure Plane).restrict A
  have hprob : IsProbabilityMeasure ν₀ := by
    constructor
    dsimp [ν₀]
    rw [hmass,
      ← ENNReal.ofReal_mul (by positivity),inv_mul_cancel₀ hm.ne',ENNReal.ofReal_one]
  let ν : ProbabilityMeasure Plane := ⟨ν₀,hprob⟩
  refine ⟨ν,?_,m⁻¹*C,mul_pos (inv_pos.mpr hm) hC,?_,?_⟩
  · simp [ν,ν₀,Measure.smul_apply,Measure.restrict_apply hA.compl]
  · intro x r hr
    change ν₀ (ball x r) ≤ _
    dsimp [ν₀]
    rw [Measure.restrict_apply measurableSet_ball]
    calc
      _ ≤ ENNReal.ofReal m⁻¹ * ENNReal.ofReal (C*r^s) :=
        mul_le_mul_right ((measure_mono inter_subset_left).trans (hb x r hr)) _
      _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]; congr 1; ring
  · change ENNReal.ofReal m⁻¹ • _ = (ENNReal.ofReal m)⁻¹ • _
    rw [ENNReal.ofReal_inv_of_pos hm]

theorem support_subset_carrier (μ : Measure Plane) {E : Set Plane}
    (hE : IsClosed E) (hμ : μ Eᶜ = 0) : μ.support ⊆ E :=
  μ.support_subset_of_isClosed hE hμ

theorem exists_distinct_support_points (μ : ProbabilityMeasure Plane)
    [NullSingletonClass (μ : Measure Plane)] :
    ∃ x ∈ (μ : Measure Plane).support, ∃ y ∈ (μ : Measure Plane).support, x ≠ y := by
  obtain ⟨x,hx⟩ := (μ : Measure Plane).nonempty_support (by
    intro h; have := congrArg (fun ν : Measure Plane => ν univ) h; simp at this)
  have hcomp : (μ : Measure Plane) {x}ᶜ = 1 := by
    rw [measure_compl (measurableSet_singleton x) (measure_ne_top _ _)]
    simp
  obtain ⟨y,hy,hyS⟩ := (μ : Measure Plane).nonempty_inter_support_of_pos
    (by rw [hcomp]; exact zero_lt_one)
  exact ⟨x,hx,y,hyS,fun he => hy (by simp [he])⟩

theorem radial_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    1 < 1+δ/2 ∧ 1+δ/2 < 2 ∧ 1 < 1+δ/8 ∧ 1+δ/8 < 2 ∧
      0 < 1-δ/4 ∧
      (1+δ/8)*(2-(1+δ/2)) < 1-δ/4 ∧
      1-δ/4 < 2-(1+δ/8) ∧ 1+δ/2 < 1+δ ∧ 1-δ/4 < 1+δ := by
  constructor <;> (try constructor) <;> (try constructor) <;>
    (try constructor) <;> (try constructor) <;> (try constructor) <;>
    (try constructor) <;> (try constructor) <;> nlinarith

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialTestNorm
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_lowerSemicontinuous {X : Type*} [TopologicalSpace X]
    (γ : X → Measure UnitCircle) (q : ℝ)
    (hγ : ∀ F : BoundedContinuousFunction UnitCircle ℝ,
      Continuous (fun x => ∫ ω, F ω ∂γ x)) :
    LowerSemicontinuous (fun x => sourceTestNorm q (γ x)) := by
  unfold sourceTestNorm
  apply lowerSemicontinuous_biSup
  intro F _
  exact (ENNReal.continuous_ofReal.comp (hγ F).norm).lowerSemicontinuous

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_TestNormRepresentation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Measures_TestNormMeasurable
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Measures_TestNormDensity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadonLpDensity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Measures_ExtendedDensityNorm
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Angular_CircleTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceTestNorm_mono (γ δ : Measure UnitCircle) [IsFiniteMeasure δ]
    (hγδ : γ ≤ δ) (q : ℝ) : sourceTestNorm q γ ≤ sourceTestNorm q δ := by
  apply iSup_le; intro F; apply iSup_le; intro hF
  let G : BoundedContinuousFunction UnitCircle ℝ :=
    BoundedContinuousFunction.mkOfCompact ⟨fun x => |F x|, F.continuous.abs⟩
  have hG : eLpNorm G (ENNReal.ofReal q) sourceArcLength ≤ 1 := by
    have he : eLpNorm G (ENNReal.ofReal q) sourceArcLength = eLpNorm F (ENNReal.ofReal q) sourceArcLength :=
      eLpNorm_congr_norm_ae
        (Eventually.of_forall (fun x => by simp [G, Real.norm_eq_abs]))
    rwa [he]
  have hi : Integrable G δ := (G.memLp_top (μ := δ)).integrable le_top
  have he : ENNReal.ofReal ‖∫ x, G x ∂δ‖ = ∫⁻ x, ‖F x‖ₑ ∂δ := by
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun x => abs_nonneg (F x))),
      ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => abs_nonneg (F x)))]
    apply lintegral_congr
    intro x
    exact ofReal_norm (F x)
  calc
    ENNReal.ofReal ‖∫ x, F x ∂γ‖ ≤ ∫⁻ x, ‖F x‖ₑ ∂γ := by
      simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm (μ := γ) (fun x => F x)
    _ ≤ ∫⁻ x, ‖F x‖ₑ ∂δ := lintegral_mono' hγδ le_rfl
    _ = ENNReal.ofReal ‖∫ x, G x ∂δ‖ := he.symm
    _ ≤ sourceTestNorm q δ := le_iSup_of_le G (le_iSup_of_le hG le_rfl)

theorem sourceTestNorm_smul_le (γ : Measure UnitCircle) (c : ℝ≥0∞) (hc : c ≠ ∞)
    (q : ℝ) : sourceTestNorm q (c • γ) ≤ c * sourceTestNorm q γ := by
  apply iSup_le; intro F; apply iSup_le; intro hF
  rw [integral_smul_measure, norm_smul, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hc]
  have hb : ENNReal.ofReal ‖∫ x, F x ∂γ‖ ≤ sourceTestNorm q γ :=
    le_iSup_of_le F (le_iSup_of_le hF le_rfl)
  exact mul_le_mul_right hb c

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_DyadicCube
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dyadic cubes in the ambient dimension of the manuscript

Half-open cubes partition without boundary overlaps. Their centers and
Euclidean diameter bounds use the same original ambient coordinates as the
distance measure.
-/

namespace Falconer
open Set MeasureTheory

theorem DyadicCube.measurable {d : ℕ} (Q : DyadicCube d) : MeasurableSet Q.carrier := by
  simp only [carrier, ofPred_forall]
  apply MeasurableSet.iInter
  intro i
  exact (measurableSet_le measurable_const (EuclideanSpace.proj i).continuous.measurable).inter
    (measurableSet_lt (EuclideanSpace.proj i).continuous.measurable measurable_const)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_CubeCapacity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic capacities in the original ambient dimension

These capacities construct the compactly supported Frostman law needed by the
application. At each occupied cube the available mass is the smaller of its
geometric capacity and the total available mass of its children.
-/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal
attribute [local instance] Classical.propDecidable

theorem cubeOccupied_nonneg {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) : 0 ≤ cubeOccupied E s Q := by
  unfold cubeOccupied
  split_ifs <;> positivity

theorem cubeCapacity_nonneg {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (K : ℕ) : 0 ≤ cubeCapacity E s Q K := by
  induction K generalizing Q with
  | zero => exact cubeOccupied_nonneg E s Q hQ
  | succ K ih =>
    exact le_min (cubeOccupied_nonneg E s Q hQ)
      (Finset.sum_nonneg fun b _ => ih (Q.child b) (by change 0 ≤ Q.side/2; positivity))

theorem cubeCapacity_le_occupied {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (K : ℕ) : cubeCapacity E s Q K ≤ cubeOccupied E s Q := by
  cases K with
  | zero => exact le_rfl
  | succ K => exact min_le_left _ _

theorem cubeOccupied_le {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) : cubeOccupied E s Q ≤ Q.side^s := by
  unfold cubeOccupied
  split_ifs
  · exact le_rfl
  · positivity

theorem content_le_cubeOccupied {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((Real.sqrt d)^s * cubeOccupied E s Q) := by
  classical
  by_cases h : (E ∩ Q.carrier).Nonempty
  · rw [cubeOccupied,ite_eq_left h,← Real.mul_rpow (Real.sqrt_nonneg _) hQ]
    calc
      _ ≤ (ediam (E ∩ Q.carrier))^s := PlanarFalconer.content_le_diameter hs _
      _ ≤ (ENNReal.ofReal (Real.sqrt d * Q.side))^s := by
        apply ENNReal.rpow_le_rpow _ hs.le
        exact ediam_le_of_forall_dist_le fun x hx y hy => Q.dist_le hQ hx.2 hy.2
      _ = _ := ENNReal.ofReal_rpow_of_nonneg (by positivity) hs.le
  · rw [not_nonempty_iff_eq_empty.mp h,PlanarFalconer.content_empty hs,
      cubeOccupied,ite_eq_right h,mul_zero,ENNReal.ofReal_zero]

theorem content_le_cube_children {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ∑ b : Fin d → Bool, PlanarFalconer.hausdorffContent s (E ∩ (Q.child b).carrier) := by
  simp_rw [← PlanarFalconer.contentOuter_apply hs]
  rw [Q.cover_children,inter_iUnion]
  exact (measure_iUnion_le _).trans_eq (tsum_fintype _)

theorem ofReal_finset_sum_nonneg {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, 0 ≤ f i) :
    ENNReal.ofReal (∑ i ∈ S, f i) = ∑ i ∈ S, ENNReal.ofReal (f i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    rw [Finset.sum_insert ha,Finset.sum_insert ha,
      ENNReal.ofReal_add (hf a (Finset.mem_insert_self _ _))
        (Finset.sum_nonneg fun i hi => hf i (Finset.mem_insert_of_mem hi)),
      ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem content_le_cubeCapacity {d : ℕ} (E : Set (Space d)) {s : ℝ} (hs : 0 < s)
    (Q : DyadicCube d) (hQ : 0 ≤ Q.side) (K : ℕ) :
    PlanarFalconer.hausdorffContent s (E ∩ Q.carrier) ≤
      ENNReal.ofReal ((Real.sqrt d)^s * cubeCapacity E s Q K) := by
  classical
  induction K generalizing Q with
  | zero => exact content_le_cubeOccupied E hs Q hQ
  | succ K ih =>
    change _ ≤ ENNReal.ofReal (_ * min _ _)
    by_cases h : cubeOccupied E s Q ≤ ∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K
    · rw [min_eq_left h]
      exact content_le_cubeOccupied E hs Q hQ
    · rw [min_eq_right (le_of_not_ge h),Finset.mul_sum,ofReal_finset_sum_nonneg]
      · exact (content_le_cube_children E hs Q).trans
          (Finset.sum_le_sum fun b _ => ih (Q.child b) (by change 0 ≤ Q.side/2; positivity))
      · intro b _
        exact mul_nonneg (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
          (cubeCapacity_nonneg E s (Q.child b) (by change 0 ≤ Q.side/2; positivity) K)

theorem exists_uniform_cube_capacity {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0} (hs : 0 < s)
    (hDim : (s : ℝ≥0∞) < dimH E) (Q : DyadicCube d)
    (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∀ K, c ≤ cubeCapacity E s Q K := by
  have hs' : 0 < (s:ℝ) := by exact_mod_cast hs
  have hp := PlanarFalconer.content_positive_of_lt_dimH E hs hDim
  have hf := PlanarFalconer.content_finite_of_bounded hs' hE.isBounded
  have hd' : (0:ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hF : 0 < (Real.sqrt d)^(s:ℝ) := Real.rpow_pos_of_pos (Real.sqrt_pos.mpr hd') _
  let c := (PlanarFalconer.hausdorffContent (s:ℝ) E).toReal / (Real.sqrt d)^(s:ℝ)
  have hc : 0 < c := div_pos (ENNReal.toReal_pos hp.ne' hf.ne) hF
  refine ⟨c,hc,fun K => ?_⟩
  have hb := content_le_cubeCapacity E hs' Q hQ.le K
  rw [inter_eq_left.mpr hEQ] at hb
  have hn := cubeCapacity_nonneg E (s:ℝ) Q hQ.le K
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  rw [ENNReal.toReal_ofReal (mul_nonneg hF.le hn)] at hr
  exact (div_le_iff₀ hF).mpr (by simpa only [mul_comm] using hr)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicChart
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# The north-hemisphere gnomonic chart

This is the explicit inverse gnomonic map, in Euclidean coordinates.
The measure identity used with this map is kept separate as a published
input; all the coordinate identities below are proved.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem northLift_continuous (n : ℕ) : Continuous (@northLift n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [Fin.cons_succ] using (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j)

theorem gnomonicChart_continuous (n : ℕ) : Continuous (@gnomonicChart n) := by
  apply Continuous.subtype_mk
  exact ((northLift_continuous n).norm.inv₀ (fun x =>
    norm_ne_zero_iff.mpr (northLift_ne_zero x))).smul (northLift_continuous n)

theorem gnomonicChart_mem_hemisphere {n : ℕ} (x : Space n) :
    gnomonicChart x ∈ northHemisphere n := by
  change 0 < (gnomonicChart x : Space (n+1)) 0
  rw [gnomonicChart_zero]
  exact inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x))

theorem gnomonicChart_coordinate_ratio {n : ℕ} (x : Space n) (i : Fin n) :
    (gnomonicChart x : Space (n+1)) i.succ / (gnomonicChart x : Space (n+1)) 0 = x i := by
  rw [gnomonicChart_succ,gnomonicChart_zero]
  have h := norm_ne_zero_iff.mpr (northLift_ne_zero x)
  field_simp

theorem gnomonicChart_injective (n : ℕ) : Function.Injective (@gnomonicChart n) := by
  intro x y h
  apply PiLp.ext
  intro i
  rw [← gnomonicChart_coordinate_ratio x i,← gnomonicChart_coordinate_ratio y i,h]

theorem gnomonicDensity_continuous (n : ℕ) : Continuous (@gnomonicDensity n) := by
  change Continuous (fun x : Space n => (1+‖x‖^2)^(-((n+1 : ℕ) : ℝ)/2))
  have h : Continuous (fun x : Space n => 1+‖x‖^2) :=
    continuous_const.add (continuous_norm.pow 2)
  exact h.rpow_const (fun x => Or.inl (ne_of_gt (by positivity)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicInverse
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original direction labels in affine gnomonic coordinates -/

/-! # Explicit inverse and cone coordinates for the gnomonic measure formula -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem northLift_gnomonicRatio {n : ℕ} (z : Space (n+1)) (hz : z 0 ≠ 0) :
    northLift (gnomonicRatio z) = (z 0)⁻¹ • z := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hz]
  · simp only [northLift_succ,gnomonicRatio_apply,PiLp.smul_apply,smul_eq_mul,div_eq_mul_inv]
    ring

@[simp] theorem gnomonicRatio_chart {n : ℕ} (x : Space n) :
    gnomonicRatio (gnomonicChart x) = x := by
  apply PiLp.ext
  intro i
  exact gnomonicChart_coordinate_ratio x i

theorem northLift_ratio_norm {n : ℕ} (w : Sphere (n+1))
    (hw : 0 < (w : Space (n+1)) 0) :
    ‖northLift (gnomonicRatio (w : Space (n+1)))‖ = ((w : Space (n+1)) 0)⁻¹ := by
  have he := northLift_gnomonicRatio (w : Space (n+1)) hw.ne'
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw)]
  rw [sphere_norm,mul_one]

theorem gnomonicChart_ratio {n : ℕ} (w : Sphere (n+1)) (hw : w ∈ northHemisphere n) :
    gnomonicChart (gnomonicRatio (w : Space (n+1))) = w := by
  have hw0 : 0 < (w : Space (n+1)) 0 := hw
  have he := northLift_gnomonicRatio (w : Space (n+1)) hw0.ne'
  have hn := northLift_ratio_norm w hw0
  apply Subtype.ext
  change ‖northLift (gnomonicRatio (w : Space (n+1)))‖⁻¹ •
    northLift (gnomonicRatio (w : Space (n+1))) = (w : Space (n+1))
  rw [hn,he,inv_inv,smul_smul,mul_inv_cancel₀ hw0.ne',one_smul]

theorem gnomonicChart_range (n : ℕ) : Set.range (@gnomonicChart n) = northHemisphere n := by
  apply Set.Subset.antisymm
  · rintro w ⟨x,rfl⟩
    exact gnomonicChart_mem_hemisphere x
  · intro w hw
    exact ⟨gnomonicRatio w,gnomonicChart_ratio w hw⟩

theorem gnomonicChart_measurableEmbedding (n : ℕ) : MeasurableEmbedding (@gnomonicChart n) :=
  (gnomonicChart_continuous n).measurableEmbedding (gnomonicChart_injective n)

theorem gnomonicRatio_conePoint {n : ℕ} (r : ℝ) (hr : r ≠ 0) (x : Space n) :
    gnomonicRatio (gnomonicConePoint r x) = x := by
  apply PiLp.ext
  intro i
  simp [hr]

theorem gnomonicConePoint_radius {n : ℕ} (r : ℝ) (x : Space n) :
    gnomonicConePoint r x = (r*‖northLift x‖) • (gnomonicChart x : Space (n+1)) := by
  change r • northLift x = (r*‖northLift x‖) • (‖northLift x‖⁻¹ • northLift x)
  rw [smul_smul,mul_inv_cancel_right₀ (norm_ne_zero_iff.mpr (northLift_ne_zero x))]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicCone
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Gnomonic sectors as ordinary Euclidean cones -/
namespace Falconer
open Set MeasureTheory
open scoped Pointwise

theorem gnomonicRatio_measurable (n : ℕ) : Measurable (@gnomonicRatio n) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℝ)).measurable.comp
  apply measurable_pi_iff.mpr
  intro i
  exact (EuclideanSpace.proj i.succ).continuous.measurable.div
    (EuclideanSpace.proj 0).continuous.measurable

theorem gnomonicRatio_smul {n : ℕ} (r : ℝ) (hr : r ≠ 0) (z : Space (n+1)) :
    gnomonicRatio (r • z) = gnomonicRatio z := by
  apply PiLp.ext
  intro i
  simp only [gnomonicRatio_apply,PiLp.smul_apply,smul_eq_mul]
  exact mul_div_mul_left _ _ hr

theorem gnomonicCone_eq {n : ℕ} (A : Set (Space n)) :
    gnomonicCone A = {z | 0 < z 0 ∧ gnomonicRatio z ∈ A ∧ ‖z‖ < 1} := by
  ext z
  constructor
  · rintro ⟨r,hr,_,⟨_,⟨x,hx,rfl⟩,rfl⟩,rfl⟩
    refine ⟨?_,?_,?_⟩
    · simp only [PiLp.smul_apply,smul_eq_mul,gnomonicChart_zero]
      exact mul_pos hr.1 (inv_pos.mpr (norm_pos_iff.mpr (northLift_ne_zero x)))
    · rw [gnomonicRatio_smul r hr.1.ne',gnomonicRatio_chart]
      exact hx
    · simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr.1,sphere_norm,mul_one] using hr.2
  · rintro ⟨hz,hA,hbound⟩
    have hpoint : gnomonicConePoint (z 0) (gnomonicRatio z) = z := by
      rw [gnomonicConePoint,northLift_gnomonicRatio z hz.ne',smul_smul,
        mul_inv_cancel₀ hz.ne',one_smul]
    have hn : z 0*‖northLift (gnomonicRatio z)‖ = ‖z‖ := by
      conv_rhs => rw [← hpoint]
      rw [gnomonicConePoint,norm_smul,Real.norm_eq_abs,abs_of_pos hz]
    refine ⟨z 0*‖northLift (gnomonicRatio z)‖,?_,
      (gnomonicChart (gnomonicRatio z) : Space (n+1)),?_,?_⟩
    · exact ⟨mul_pos hz (norm_pos_iff.mpr (northLift_ne_zero _)),hn.trans_lt hbound⟩
    · exact ⟨gnomonicChart (gnomonicRatio z),⟨gnomonicRatio z,hA,rfl⟩,rfl⟩
    · exact (gnomonicConePoint_radius (z 0) (gnomonicRatio z)).symm.trans hpoint

theorem gnomonicCone_measurable {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    MeasurableSet (gnomonicCone A) := by
  rw [gnomonicCone_eq]
  exact (measurableSet_lt measurable_const (EuclideanSpace.proj 0).continuous.measurable).inter
    ((hA.preimage (gnomonicRatio_measurable n)).inter (measurableSet_lt measurable_norm measurable_const))

theorem gnomonicConePoint_mem_iff {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r)
    (x : Space n) : gnomonicConePoint r x ∈ gnomonicCone A ↔
      x ∈ A ∧ r < ‖northLift x‖⁻¹ := by
  rw [gnomonicCone_eq]
  simp only [mem_ofPred_eq,gnomonicConePoint_zero,gnomonicRatio_conePoint r hr.ne',
    hr,true_and]
  rw [gnomonicConePoint,norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  have hn := norm_pos_iff.mpr (northLift_ne_zero x)
  rw [← one_div,lt_div_iff₀ hn]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ConeIntegration
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Coordinate and dilation integration for the gnomonic cone formula -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem euclidean_coordinate_split_preserving (n : ℕ) :
    MeasurePreserving (fun z : Space (n+1) => (z 0,euclideanTail z))
      volume ((volume : Measure ℝ).prod (volume : Measure (Space n))) := by
  have h₁ := PiLp.volume_preserving_ofLp (Fin (n+1))
  have h₂ := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have h₃ := (MeasurePreserving.id (volume : Measure ℝ)).prod
    (PiLp.volume_preserving_toLp (Fin n))
  exact h₃.comp (h₂.comp h₁)

theorem lintegral_euclidean_coordinate_split {n : ℕ}
    (f : ℝ × Space n → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ z : Space (n+1), f (z 0,euclideanTail z)) = ∫⁻ r : ℝ, ∫⁻ x : Space n, f (r,x) := by
  rw [(euclidean_coordinate_split_preserving n).lintegral_comp hf]
  exact lintegral_prod _ hf.aemeasurable

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ConeSections
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Fiber volumes of the Euclidean cone over a gnomonic chart -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal Pointwise

theorem euclideanCons_continuous (n : ℕ) : Continuous (fun z : ℝ × Space n => euclideanCons z.1 z.2) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin (n+1) => ℝ)).comp
  apply continuous_pi
  intro i
  refine Fin.cases continuous_fst (fun j => ?_) i
  exact (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_snd

theorem euclideanCons_smul {n : ℕ} (r : ℝ) (x : Space n) :
    euclideanCons r (r • x) = gnomonicConePoint r x := by
  apply PiLp.ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp

theorem gnomonicCone_section_positive {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r) :
    {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      r • {x : Space n | x ∈ A ∧ r < ‖northLift x‖⁻¹} := by
  ext y
  constructor
  · intro hy
    refine ⟨r⁻¹ • y,?_,smul_inv_smul₀ hr.ne' y⟩
    apply (gnomonicConePoint_mem_iff A r hr (r⁻¹ • y)).mp
    rw [← euclideanCons_smul,smul_inv_smul₀ hr.ne']
    exact hy
  · rintro ⟨x,hx,rfl⟩
    change euclideanCons r (r • x) ∈ gnomonicCone A
    rw [euclideanCons_smul]
    exact (gnomonicConePoint_mem_iff A r hr x).mpr hx

theorem gnomonicCone_section_volume {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : 0 < r) :
    volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      ENNReal.ofReal (r^n)*volume {x : Space n | x ∈ A ∧ r < ‖northLift x‖⁻¹} := by
  rw [gnomonicCone_section_positive A r hr,Measure.addHaar_smul_of_nonneg volume hr.le]
  simp [Space]

theorem gnomonicCone_section_nonpositive {n : ℕ} (A : Set (Space n)) (r : ℝ) (hr : r ≤ 0) :
    {y : Space n | euclideanCons r y ∈ gnomonicCone A} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro y hy
  rw [gnomonicCone_eq] at hy
  exact (not_lt.mpr hr) hy.1

theorem gnomonicCone_volume_slices {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    volume (gnomonicCone A) = ∫⁻ r : ℝ,
      volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} := by
  let F : ℝ × Space n → ℝ≥0∞ := fun z => (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons z.1 z.2)
  have hC := gnomonicCone_measurable hA
  have hF : Measurable F := (measurable_const.indicator hC).comp (euclideanCons_continuous n).measurable
  calc
    volume (gnomonicCone A) = ∫⁻ z : Space (n+1), F (z 0,euclideanTail z) := by
      simp only [F,euclideanCons_self]
      exact (lintegral_indicator_one hC).symm
    _ = ∫⁻ r : ℝ, ∫⁻ y : Space n, F (r,y) := lintegral_euclidean_coordinate_split F hF
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards with r
      have hm : MeasurableSet {y : Space n | euclideanCons r y ∈ gnomonicCone A} :=
        hC.preimage ((euclideanCons_continuous n).comp (continuous_const.prodMk continuous_id)).measurable
      change (∫⁻ y : Space n, (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons r y)) = _
      have he : (fun y : Space n => (gnomonicCone A).indicator (fun _ => (1 : ℝ≥0∞)) (euclideanCons r y)) =
          {y : Space n | euclideanCons r y ∈ gnomonicCone A}.indicator (fun _ => (1 : ℝ≥0∞)) := by
        funext y
        by_cases hy : euclideanCons r y ∈ gnomonicCone A <;> simp [hy]
      rw [he]
      exact lintegral_indicator_one hm

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_ConeRadialIntegral
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The one-dimensional radial integral in the gnomonic cone formula -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem lintegral_nonnegative_power_Ioo (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    (∫⁻ r : ℝ in Ioo 0 t, ENNReal.ofReal (r^n)) = ENNReal.ofReal (t^(n+1)/(n+1)) := by
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc,
    ← ofReal_integral_eq_lintegral_ofReal (intervalIntegral.intervalIntegrable_pow n).1,
    ← intervalIntegral.integral_of_le ht]
  · simp
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact pow_nonneg hr.1.le _

theorem gnomonic_radial_height_power {n : ℕ} (x : Space n) :
    (‖northLift x‖⁻¹)^(n+1) = gnomonicDensity x := by
  have hn : 0 < ‖northLift x‖ := norm_pos_iff.mpr (northLift_ne_zero x)
  rw [gnomonicDensity,← northLift_norm_sq]
  rw [← Real.rpow_natCast (‖northLift x‖⁻¹),Real.inv_rpow hn.le]
  rw [← Real.rpow_neg hn.le]
  rw [← Real.rpow_natCast ‖northLift x‖ 2,← Real.rpow_mul hn.le]
  congr 1
  push_cast
  ring

theorem gnomonic_radial_integral {n : ℕ} (x : Space n) :
    (∫⁻ r : ℝ in Ioo 0 ‖northLift x‖⁻¹, ENNReal.ofReal (r^n)) =
      ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ)) := by
  rw [lintegral_nonnegative_power_Ioo _ _ (inv_nonneg.mpr (norm_nonneg _)),gnomonic_radial_height_power]
  norm_cast

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicConeVolume
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The Euclidean volume of a gnomonic cone -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem gnomonicCone_volume {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    volume (gnomonicCone A) = ∫⁻ x : Space n in A,
      ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ)) := by
  classical
  let b : Space n → ℝ := fun x => ‖northLift x‖⁻¹
  have hb : Continuous b := (northLift_continuous n).norm.inv₀
    (fun x => norm_ne_zero_iff.mpr (northLift_ne_zero x))
  let F : ℝ × Space n → ℝ≥0∞ := fun z =>
    if z.2 ∈ A ∧ 0 < z.1 ∧ z.1 < b z.2 then ENNReal.ofReal (z.1^n) else 0
  have hreg : MeasurableSet {z : ℝ × Space n | z.2 ∈ A ∧ 0 < z.1 ∧ z.1 < b z.2} :=
    (hA.preimage measurable_snd).inter ((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_lt measurable_fst (hb.measurable.comp measurable_snd)))
  have hF : Measurable F := Measurable.ite hreg
    (measurable_fst.pow_const n).ennreal_ofReal measurable_const
  have hslice (r : ℝ) : volume {y : Space n | euclideanCons r y ∈ gnomonicCone A} =
      ∫⁻ x : Space n, F (r,x) := by
    by_cases hr : 0 < r
    · rw [gnomonicCone_section_volume A r hr]
      have hset : MeasurableSet {x : Space n | x ∈ A ∧ r < b x} :=
        hA.inter (measurableSet_lt measurable_const hb.measurable)
      have he : (fun x : Space n => F (r,x)) =
          fun x => ENNReal.ofReal (r^n)*{x : Space n | x ∈ A ∧ r < b x}.indicator (fun _ => (1 : ℝ≥0∞)) x := by
        funext x
        by_cases hx : x ∈ A ∧ r < b x <;> simp [F,hr,hx]
      rw [he,lintegral_const_mul _ (measurable_const.indicator hset),lintegral_indicator_fun_one hset]
    · rw [gnomonicCone_section_nonpositive A r (le_of_not_gt hr),measure_empty]
      simp [F,hr]
  have hinner (x : Space n) : (∫⁻ r : ℝ, F (r,x)) =
      A.indicator (fun x => ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ))) x := by
    by_cases hx : x ∈ A
    · have he : (fun r : ℝ => F (r,x)) =
          (Ioo 0 (b x)).indicator (fun r : ℝ => ENNReal.ofReal (r^n)) := by
        funext r
        by_cases hr : 0 < r ∧ r < b x <;> simp [F,hx,Set.mem_Ioo,hr]
      rw [he,lintegral_indicator measurableSet_Ioo]
      rw [Set.indicator_of_mem hx]
      exact gnomonic_radial_integral x
    · simp [F,hx]
  calc
    volume (gnomonicCone A) = ∫⁻ r : ℝ, ∫⁻ x : Space n, F (r,x) := by
      rw [gnomonicCone_volume_slices hA]
      exact lintegral_congr_ae (Filter.Eventually.of_forall hslice)
    _ = ∫⁻ x : Space n, ∫⁻ r : ℝ, F (r,x) := lintegral_lintegral_swap hF.aemeasurable
    _ = ∫⁻ x : Space n, A.indicator (fun x => ENNReal.ofReal (gnomonicDensity x/((n+1:ℕ):ℝ))) x :=
      lintegral_congr_ae (Filter.Eventually.of_forall hinner)
    _ = _ := lintegral_indicator hA _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_GnomonicDischarge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published gnomonic surface identity proved from Euclidean cone volume -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal Pointwise

theorem gnomonic_sphere_image {n : ℕ} {A : Set (Space n)} (hA : MeasurableSet A) :
    sphereMeasure (n+1) (gnomonicChart '' A) =
      ((volume : Measure (Space n)).withDensity (fun x => ENNReal.ofReal (gnomonicDensity x))) A := by
  have hchart : MeasurableSet (gnomonicChart '' A) :=
    (gnomonicChart_measurableEmbedding n).measurableSet_image.mpr hA
  have hd : (0:ℝ) < ((n+1:ℕ):ℝ) := by positivity
  rw [sphereMeasure,Measure.toSphere_apply' _ hchart]
  change (Module.finrank ℝ (Space (n+1)) : ℝ≥0∞)*volume (gnomonicCone A) = _
  rw [show Module.finrank ℝ (Space (n+1)) = n+1 by simp [Space],gnomonicCone_volume hA,
    withDensity_apply _ hA]
  rw [← ENNReal.ofReal_natCast,← lintegral_const_mul _
    (((gnomonicDensity_continuous n).measurable.div_const _).ennreal_ofReal)]
  apply lintegral_congr_ae
  filter_upwards with x
  rw [← ENNReal.ofReal_mul hd.le]
  congr 1
  field_simp

theorem published_gnomonic_surface : PublishedGnomonicSurface := by
  intro n _hn
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (gnomonicChart_continuous n).measurable hB]
  have hA : MeasurableSet (gnomonicChart ⁻¹' B) := hB.preimage (gnomonicChart_continuous n).measurable
  rw [← gnomonic_sphere_image hA,Set.image_preimage_eq_inter_range,gnomonicChart_range,
    Measure.restrict_apply hB]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ParentConeGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RootPatchGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric

theorem rootPatchEnvelope_center (x : Plane) (r : ℝ) : (rootPatchEnvelope x r).center = x := by
  ext i
  fin_cases i <;> simp [rootPatchEnvelope,DyadicSquare.center] <;> ring

theorem closedBall_subset_rootPatchEnvelope (x : Plane) {r : ℝ} (hr : 0 < r) :
    closedBall x r ⊆ (rootPatchEnvelope x r).carrier := by
  intro z hz
  have h₀ := abs_le.mp ((plane_coordinate_dist_le z x 0).trans hz)
  have h₁ := abs_le.mp ((plane_coordinate_dist_le z x 1).trans hz)
  change x 0-2*r ≤ z 0 ∧ z 0 < x 0-2*r+4*r ∧ x 1-2*r ≤ z 1 ∧ z 1 < x 1-2*r+4*r
  exact ⟨by linarith only [h₀.1, hr], by linarith only [h₀.2, hr],
    by linarith only [h₁.1, hr], by linarith only [h₁.2, hr]⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RootSimilarityGeometry
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory

theorem DyadicSquare.dilate_center (Q : DyadicSquare) (s : ℝ) :
    (Q.dilate s).center = s • Q.center := by
  ext i
  fin_cases i <;> simp [dilate,DyadicSquare.center] <;> ring

theorem DyadicSquare.mem_dilate (Q : DyadicSquare) {s : ℝ} (hs : 0 < s) (x : Plane) :
    s • x ∈ (Q.dilate s).carrier ↔ x ∈ Q.carrier := by
  change s*Q.x ≤ s*x 0 ∧ s*x 0 < s*Q.x+s*Q.side ∧
    s*Q.y ≤ s*x 1 ∧ s*x 1 < s*Q.y+s*Q.side ↔ _
  rw [← mul_add,← mul_add]
  simp only [mul_le_mul_iff_right₀ hs,mul_lt_mul_iff_right₀ hs,DyadicSquare.carrier,mem_ofPred_eq]

theorem normalized_root_patch_geometry (x y : Plane) (hxy : x ≠ y) :
    let r := dist x y/1000
    let s := 250/dist x y
    let Q := (rootPatchEnvelope x r).dilate s
    let P := (rootPatchEnvelope y r).dilate s
    0 < s ∧ Q.side = 1 ∧ P.side = 1 ∧ dist Q.center P.center = 250 ∧
    (fun z : Plane => s • z) '' closedBall x r ⊆ Q.carrier ∧
    (fun z : Plane => s • z) '' closedBall y r ⊆ P.carrier := by
  have hd : 0 < dist x y := dist_pos.mpr hxy
  have hs : 0 < 250/dist x y := by positivity
  dsimp only
  refine ⟨hs,?_,?_,?_,?_,?_⟩
  · dsimp [DyadicSquare.dilate,rootPatchEnvelope]
    field_simp
    ring
  · dsimp [DyadicSquare.dilate,rootPatchEnvelope]
    field_simp
    ring
  · rw [DyadicSquare.dilate_center,DyadicSquare.dilate_center,
      rootPatchEnvelope_center,rootPatchEnvelope_center,dist_smul₀,Real.norm_eq_abs,abs_of_pos hs]
    field_simp
  · rintro z ⟨w,hw,rfl⟩
    exact (DyadicSquare.mem_dilate _ hs w).mpr (closedBall_subset_rootPatchEnvelope x (by positivity) hw)
  · rintro z ⟨w,hw,rfl⟩
    exact (DyadicSquare.mem_dilate _ hs w).mpr (closedBall_subset_rootPatchEnvelope y (by positivity) hw)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_RadialLpEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem finite_radial_Lp_integral (α β : Measure Plane)
    [IsFiniteMeasure α] [IsFiniteMeasure β] {K L : Set Plane}
    (hK : IsCompact K) (hL : IsCompact L) (hKL : Disjoint K L)
    (hα : ∀ᵐ z ∂α, z ∈ K) (hβ : ∀ᵐ z ∂β, z ∈ L) {s t p q : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p < 2) (hs1 : 1 < s) (hs2 : s < 2)
    (hupt : (2-s)*p < t) (htp : t < 2-p)
    (hEα : rieszEnergy α s < ∞) (hEβ : rieszEnergy β t < ∞) :
    (∫⁻ x, (sourceDensityNorm p (α.map (sourceRadialUnit x)))^p ∂β) < ∞ := by
  let D := Metric.diam (K ∪ L) + 1
  have hD : 0 < D := add_pos_of_nonneg_of_pos Metric.diam_nonneg zero_lt_one
  have hdist {x y : Plane} (hx : x ∈ K ∪ L) (hy : y ∈ K ∪ L) : dist x y ≤ D :=
    (dist_le_diam_of_mem (hK.union hL).isBounded hx hy).trans
      (le_add_of_nonneg_right zero_le_one)
  have hdiam : ∀ᵐ z : Plane × Plane ∂β.prod β, dist z.1 z.2 ≤ D := by
    apply (Measure.ae_prod_iff_ae_ae (p := fun z : Plane × Plane => dist z.1 z.2 ≤ D) ((isClosed_le (continuous_fst.dist continuous_snd) continuous_const).measurableSet)).mpr
    filter_upwards [hβ] with x hx
    filter_upwards [hβ] with y hy
    exact hdist (Or.inr hx) (Or.inr hy)
  have hbound : ∀ᵐ x ∂β, ∀ y ∈ K, dist y x ≤ D :=
    hβ.mono (fun x hx y hy => hdist (Or.inl hy) (Or.inr hx))
  have hx : ∀ᵐ x ∂β, ∀ᵐ y ∂α, y ≠ x := by
    filter_upwards [hβ] with x hx
    filter_upwards [hα] with y hy
    intro he
    exact Set.disjoint_left.mp hKL (he ▸ hy) hx
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact finite_radial_testNorm_integral α β hK hα hpq hp2 hs1 hs2 hD hupt htp hdiam hbound hx hEα hEβ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Frostman_AtomlessRadialContinuity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem continuousAt_sourceRadialUnit_center (x y : Plane) (hy : y ≠ x) :
    ContinuousAt (fun z => sourceRadialUnit z y) x := by
  rw [ContinuousAt, tendsto_subtype_rng]
  change Tendsto (fun z => sourceRadialVector z y) (𝓝 x) (𝓝 (sourceRadialVector x y))
  rw [show sourceRadialVector x y = ‖y-x‖⁻¹ • (y-x) by simp [sourceRadialVector,hy]]
  have hd : ContinuousAt (fun z : Plane => y-z) x := (continuous_const.sub continuous_id).continuousAt
  have h := (hd.norm.inv₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hy))).smul hd
  apply h.congr'
  have hne : ∀ᶠ z in 𝓝 x, z ≠ y := isClosed_singleton.isOpen_compl.mem_nhds hy.symm
  filter_upwards [hne] with z hz
  simp [sourceRadialVector, hz.symm]

theorem continuous_atomless_radial_test (α : Measure Plane) [IsFiniteMeasure α]
    [NullSingletonClass α] (F : BoundedContinuousFunction UnitCircle ℝ) :
    Continuous (fun x => ∫ ω, F ω ∂α.map (sourceRadialUnit x)) := by
  simp_rw [integral_map (measurable_sourceRadialUnit _).aemeasurable F.continuous.aestronglyMeasurable]
  rw [continuous_iff_continuousAt]
  intro x
  apply continuousAt_of_dominated (bound := fun _ : Plane => ‖F‖)
  · exact Eventually.of_forall (fun z =>
      (F.continuous.measurable.comp (measurable_sourceRadialUnit z)).aestronglyMeasurable)
  · exact Eventually.of_forall (fun z => Eventually.of_forall (fun y => F.norm_coe_le_norm _))
  · exact integrable_const _
  · filter_upwards [(show ∀ᵐ y ∂α, y ≠ x from by rw [ae_iff]; simp)] with y hy
    exact F.continuous.continuousAt.comp (continuousAt_sourceRadialUnit_center x y hy)

theorem sourceDensityNorm_atomless_radial_lowerSemicontinuous (α : Measure Plane)
    [IsFiniteMeasure α] [NullSingletonClass α] {p q : ℝ} (hpq : p.HolderConjugate q) :
    LowerSemicontinuous (fun x => sourceDensityNorm p (α.map (sourceRadialUnit x))) := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  exact sourceTestNorm_lowerSemicontinuous _ _ (continuous_atomless_radial_test α)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CompactSublevel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem exists_positive_compact_sublevel {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [BorelSpace X] [T2Space X]
    (μ : Measure X) [IsProbabilityMeasure μ] {K : Set X} (hK : IsCompact K)
    (hμ : ∀ᵐ x ∂μ, x ∈ K) (f : X → ℝ≥0∞) (hf : LowerSemicontinuous f)
    {p : ℝ} (hp : 0 < p) (hI : (∫⁻ x, (f x)^p ∂μ) < ∞) :
    ∃ A : Set X, IsCompact A ∧ A ⊆ K ∧ 0 < μ A ∧
      ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ x ∈ A, f x ≤ C := by
  let A : ℕ → Set X := fun n => K ∩ f ⁻¹' Iic (n : ℝ≥0∞)
  have hfinite : ∀ᵐ x ∂μ, f x < ∞ := by
    filter_upwards [ae_lt_top (hf.measurable.pow_const p) hI.ne] with x hx
    by_contra h
    have ht : f x = ∞ := top_unique (not_lt.mp h)
    rw [ht, ENNReal.top_rpow_of_pos hp] at hx
    exact lt_irrefl _ hx
  have hfull : ∀ᵐ x ∂μ, x ∈ ⋃ n, A n := by
    filter_upwards [hμ, hfinite] with x hx hfx
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt hfx.ne
    exact mem_iUnion.mpr ⟨n, hx, hn.le⟩
  obtain ⟨n, hn⟩ : ∃ n, 0 < μ (A n) := by
    by_contra h
    have hz : ∀ n, μ (A n) = 0 := fun n => le_antisymm (not_lt.mp (fun hn => h ⟨n, hn⟩)) bot_le
    have hzero : μ (⋃ n, A n) = 0 := measure_iUnion_null hz
    have hc : μ (⋃ n, A n)ᶜ = 0 := by
      change μ {x | x ∉ ⋃ n, A n} = 0
      exact (ae_iff.mp hfull)
    have hu : μ univ = 0 := by
      rw [← union_compl_self (⋃ n, A n)]
      exact measure_union_null hzero hc
    simp at hu
  refine ⟨A n, hK.inter_right (hf.isClosed_preimage n), inter_subset_left, hn,
    n, ENNReal.natCast_ne_top n, fun x hx => hx.2⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_UniformRadialRestrictions
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
open scoped ENNReal NNReal

theorem radial_densityNorm_normalized_restrict_le (ν : ProbabilityMeasure Plane)
    (B : Set Plane) (hB : 0 < (ν : Measure Plane) B)
    (ν' : ProbabilityMeasure Plane)
    (hν' : (ν' : Measure Plane) = ((ν : Measure Plane) B)⁻¹ • (ν : Measure Plane).restrict B)
    {p q : ℝ} (hpq : p.HolderConjugate q) (x : Plane) :
    sourceDensityNorm p ((ν' : Measure Plane).map (sourceRadialUnit x)) ≤
      ((ν : Measure Plane) B)⁻¹ * sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) := by
  simp_rw [← sourceTestNorm_eq_densityNorm _ hpq]
  rw [hν', Measure.map_smul]
  exact (sourceTestNorm_smul_le _ _ (ENNReal.inv_ne_top.mpr hB.ne') q).trans
    (mul_le_mul_right (sourceTestNorm_mono _ _
      (Measure.map_mono Measure.restrict_le_self (measurable_sourceRadialUnit x)) q) _)

theorem uniform_restrictions_of_finite_radial_moments
    (μ₀ ν₀ : ProbabilityMeasure Plane)
    (hμK : IsCompact (μ₀ : Measure Plane).support)
    (hνK : IsCompact (ν₀ : Measure Plane).support)
    {s C p q : ℝ} (hs : 0 < s) (hC : 0 < C)
    (hμball : BallBound μ₀ s C) (hνball : BallBound ν₀ s C)
    (hpq : p.HolderConjugate q)
    (hIμ : (∫⁻ x, (sourceDensityNorm p ((ν₀ : Measure Plane).map (sourceRadialUnit x)))^p ∂μ₀) < ∞)
    (hIν : (∫⁻ x, (sourceDensityNorm p ((μ₀ : Measure Plane).map (sourceRadialUnit x)))^p ∂ν₀) < ∞) :
    ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ (μ₀ : Measure Plane).support ∧
      (ν : Measure Plane).support ⊆ (ν₀ : Measure Plane).support ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ s D ∧ BallBound ν s D ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm p ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm p ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  let := noAtoms_of_ball_bound μ₀ hs hμball
  let := noAtoms_of_ball_bound ν₀ hs hνball
  obtain ⟨A, hA, hAμ, hAp, KA, hKA, hAb⟩ := exists_positive_compact_sublevel
    (μ₀ : Measure Plane) hμK (μ₀ : Measure Plane).support_mem_ae
    (fun x => sourceDensityNorm p ((ν₀ : Measure Plane).map (sourceRadialUnit x)))
    (sourceDensityNorm_atomless_radial_lowerSemicontinuous ν₀ hpq) hpq.pos hIμ
  obtain ⟨B, hB, hBν, hBp, KB, hKB, hBb⟩ := exists_positive_compact_sublevel
    (ν₀ : Measure Plane) hνK (ν₀ : Measure Plane).support_mem_ae
    (fun x => sourceDensityNorm p ((μ₀ : Measure Plane).map (sourceRadialUnit x)))
    (sourceDensityNorm_atomless_radial_lowerSemicontinuous μ₀ hpq) hpq.pos hIν
  obtain ⟨μ, hμA, Dμ, hDμ, hbμ, heμ⟩ := normalized_restriction_ball_bound μ₀ hμball hC A hA.measurableSet hAp
  obtain ⟨ν, hνB, Dν, hDν, hbν, heν⟩ := normalized_restriction_ball_bound ν₀ hνball hC B hB.measurableSet hBp
  have hμsub := support_subset_carrier μ hA.isClosed hμA
  have hνsub := support_subset_carrier ν hB.isClosed hνB
  have heμ' : (μ : Measure Plane) = ((μ₀ : Measure Plane) A)⁻¹ • (μ₀ : Measure Plane).restrict A := by
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using heμ
  have heν' : (ν : Measure Plane) = ((ν₀ : Measure Plane) B)⁻¹ • (ν₀ : Measure Plane).restrict B := by
    simpa only [ENNReal.ofReal_toReal (measure_ne_top _ _)] using heν
  let K := max (((ν₀ : Measure Plane) B)⁻¹ * KA) (((μ₀ : Measure Plane) A)⁻¹ * KB)
  refine ⟨μ, ν, hA.of_isClosed_subset Measure.isClosed_support hμsub,
    hB.of_isClosed_subset Measure.isClosed_support hνsub, hμsub.trans hAμ, hνsub.trans hBν,
    max Dμ Dν, hDμ.trans_le (le_max_left _ _), ?_, ?_, K, ?_, ?_, ?_⟩
  · intro x r hr
    exact (hbμ x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  · intro x r hr
    exact (hbν x r hr).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  · exact ne_of_lt (max_lt (ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hBp.ne').lt_top hKA.lt_top)
      (ENNReal.mul_lt_top (ENNReal.inv_ne_top.mpr hAp.ne').lt_top hKB.lt_top))
  · intro x hx
    exact (radial_densityNorm_normalized_restrict_le ν₀ B hBp ν heν' hpq x).trans
      ((mul_le_mul_right (hAb x (hμsub hx)) _).trans (le_max_left _ _))
  · intro y hy
    exact (radial_densityNorm_normalized_restrict_le μ₀ A hAp μ heμ' hpq y).trans
      ((mul_le_mul_right (hBb y (hνsub hy)) _).trans (le_max_right _ _))

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_RootSimilarityMeasures
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem dilate_ball_preimage {s : ℝ} (hs : 0 < s) (x : Plane) (r : ℝ) :
    (fun y : Plane => s • y) ⁻¹' ball x r = ball (s⁻¹ • x) (r/s) := by
  ext y
  simp only [mem_preimage,mem_ball]
  have he : dist (s • y) x = s*dist y (s⁻¹ • x) := by
    calc
      _ = dist (s • y) (s • (s⁻¹ • x)) := by rw [smul_inv_smul₀ hs.ne']
      _ = _ := by rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos hs]
  rw [he,lt_div_iff₀ hs,mul_comm s]

theorem BallBound.dilate {ρ : Measure Plane} {u C s : ℝ}
    (hb : BallBound ρ u C) (hs : 0 < s) :
    BallBound (ρ.map (fun x : Plane => s • x)) u (C/s^u) := by
  intro x r hr
  rw [Measure.map_apply (by fun_prop) measurableSet_ball,dilate_ball_preimage hs]
  apply (hb (s⁻¹ • x) (r/s) (by positivity)).trans_eq
  congr 1
  rw [Real.div_rpow hr.le hs.le]
  ring

theorem dilate_carried_compact (ρ : Measure Plane) (A : Set Plane)
    (hA : IsCompact A) (hρ : ρ Aᶜ = 0) (s : ℝ) :
    (ρ.map (fun x : Plane => s • x)) ((fun x : Plane => s • x) '' A)ᶜ = 0 := by
  rw [Measure.map_apply (by fun_prop) (hA.image (by fun_prop)).measurableSet.compl]
  apply measure_mono_null _ hρ
  intro x hx hmem
  exact hx ⟨x,hmem,rfl⟩

theorem distanceSet_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s) :
    distanceSet ((fun x : Plane => s • x) '' E) = (fun r : ℝ => s*r) '' distanceSet E := by
  ext r
  constructor
  · rintro ⟨x,⟨a,ha,rfl⟩,y,⟨b,hb,rfl⟩,hr⟩
    refine ⟨dist a b,⟨a,ha,b,hb,rfl⟩,?_⟩
    simpa only [dist_smul₀,Real.norm_eq_abs,abs_of_pos hs] using hr
  · rintro ⟨t,⟨x,hx,y,hy,rfl⟩,rfl⟩
    exact ⟨s • x,⟨x,hx,rfl⟩,s • y,⟨y,hy,rfl⟩,by simp [dist_smul₀,abs_of_pos hs]⟩

theorem distanceSet_positive_of_dilate (E : Set Plane) {s : ℝ} (hs : 0 < s)
    (hpos : 0 < volume (distanceSet ((fun x : Plane => s • x) '' E))) :
    0 < volume (distanceSet E) := by
  rw [distanceSet_dilate E hs] at hpos
  have he : (fun r : ℝ => s*r) '' distanceSet E = (fun r : ℝ => s⁻¹*r) ⁻¹' distanceSet E := by
    ext r
    constructor
    · rintro ⟨t,ht,rfl⟩
      simpa only [mem_preimage,inv_mul_cancel_left₀ hs.ne'] using ht
    · intro hr
      exact ⟨s⁻¹*r,hr,mul_inv_cancel_left₀ hs.ne' r⟩
  rw [he,Real.volume_preimage_mul_left (inv_ne_zero hs.ne')] at hpos
  exact (ENNReal.mul_pos_iff.mp hpos).2

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_Published
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Published radial input for the planar Falconer application

The only input isolated here is the planar specialization of Orponen,
*On the dimension and smoothness of radial projections*, Analysis & PDE
12 (2019), 1273–1294, proof of Theorem 1.13, equations (3.5)–(3.6).
The parameters used by the application are
`s = 1 + δ / 2`, `t = 1 - δ / 4`, and `p = 1 + δ / 8`.
They satisfy the strict inequalities in (3.5).  Orponen uses a distance
weighted source measure; on disjoint compact supports that weight and its
inverse are bounded, so finiteness of the moment is unchanged.

Prepared root measures follow from this radial moment estimate.
-/

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem compact_neighborhood_probability_for_published_radial (E : Set Plane) (hE : IsCompact E)
    (ζ : ProbabilityMeasure Plane) (hζ : (ζ : Measure Plane) Eᶜ = 0)
    {u C : ℝ} (hC : 0 < C) (hball : BallBound ζ u C)
    (x : Plane) (hx : x ∈ (ζ : Measure Plane).support) {r : ℝ} (hr : 0 < r) :
    ∃ μ : ProbabilityMeasure Plane, (μ : Measure Plane) (E ∩ closedBall x r)ᶜ = 0 ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ u D := by
  have hpos : 0 < (ζ : Measure Plane) (E ∩ closedBall x r) := by
    have hp := ((ζ : Measure Plane).mem_support_iff_forall x).mp hx (ball x r) (ball_mem_nhds x hr)
    have hsub : ball x r ⊆ (E ∩ closedBall x r) ∪ Eᶜ := by
      intro z hz
      by_cases he : z ∈ E
      · exact Or.inl ⟨he,ball_subset_closedBall hz⟩
      · exact Or.inr he
    have hb := (measure_mono hsub).trans (measure_union_le _ _ (μ := (ζ : Measure Plane)))
    rw [hζ,add_zero] at hb
    exact hp.trans_le hb
  obtain ⟨μ,hμ,D,hD,hb,_⟩ := normalized_restriction_ball_bound ζ hball hC
    (E ∩ closedBall x r) (hE.measurableSet.inter measurableSet_closedBall) hpos
  exact ⟨μ,hμ,D,hD,hb⟩

/-- Compact simultaneous restrictions turn the integrated published radial
estimate into uniform control at every retained pin. -/
theorem source_uniform_radial_restrictions_of_published_radial
    (hOrponen : PublishedPlanarRadialMoment) (μ₀ ν₀ : ProbabilityMeasure Plane)
    (hμK : IsCompact (μ₀ : Measure Plane).support)
    (hνK : IsCompact (ν₀ : Measure Plane).support)
    (hsep : Disjoint (μ₀ : Measure Plane).support (ν₀ : Measure Plane).support)
    {δ C : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hC : 0 < C)
    (hμball : BallBound μ₀ (1+δ) C) (hνball : BallBound ν₀ (1+δ) C) :
    ∃ μ ν : ProbabilityMeasure Plane,
      IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
      (μ : Measure Plane).support ⊆ (μ₀ : Measure Plane).support ∧
      (ν : Measure Plane).support ⊆ (ν₀ : Measure Plane).support ∧
      ∃ D : ℝ, 0 < D ∧ BallBound μ (1+δ) D ∧ BallBound ν (1+δ) D ∧
      ∃ K : ℝ≥0∞, K ≠ ∞ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨hs1, _, hp1, _, ht0, _, _, hsδ, htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hIμ := hOrponen ν₀ μ₀ δ hδ hδ1 hνK hμK hsep.symm
    (rieszEnergy_lt_top_of_ball_bound ν₀ (zero_lt_one.trans hs1) hsδ hνball)
    (rieszEnergy_lt_top_of_ball_bound μ₀ ht0 htδ hμball)
  have hIν := hOrponen μ₀ ν₀ δ hδ hδ1 hμK hνK hsep
    (rieszEnergy_lt_top_of_ball_bound μ₀ (zero_lt_one.trans hs1) hsδ hμball)
    (rieszEnergy_lt_top_of_ball_bound ν₀ ht0 htδ hνball)
  exact uniform_restrictions_of_finite_radial_moments μ₀ ν₀ hμK hνK
    (add_pos zero_lt_one hδ) hC hμball hνball hpq hIμ hIν

theorem exists_normalized_root_setup_of_published_radial
    (hOrponen : PublishedPlanarRadialMoment) (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    ∃ δ s : ℝ, 0 < δ ∧ δ < 1 ∧ 0 < s ∧
      ∃ Q : Fin 2 → DyadicSquare, (∀ l, (Q l).side = 1) ∧
        dist (Q 0).center (Q 1).center = 250 ∧
      ∃ μ ν : ProbabilityMeasure Plane,
        IsCompact (μ : Measure Plane).support ∧ IsCompact (ν : Measure Plane).support ∧
        (μ : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (ν : Measure Plane).support ⊆ (fun x : Plane => s • x) '' E ∧
        (μ : Measure Plane).support ⊆ (Q 0).carrier ∧
        (ν : Measure Plane).support ⊆ (Q 1).carrier ∧
        (μ : Measure Plane) (Q 0).carrierᶜ = 0 ∧ (ν : Measure Plane) (Q 1).carrierᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ BallBound μ (1+δ) C ∧ BallBound ν (1+δ) C ∧
      ∃ K : ℝ≥0∞, K ≠ ⊤ ∧
        (∀ x ∈ (μ : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((ν : Measure Plane).map (sourceRadialUnit x)) ≤ K) ∧
        (∀ y ∈ (ν : Measure Plane).support,
          sourceDensityNorm (1+δ/8) ((μ : Measure Plane).map (sourceRadialUnit y)) ≤ K) := by
  obtain ⟨δ,hδ,hδ1,ζ,hζ,hna,C,hC,hball,_⟩ := exists_frostman_above_one E hE hd
  let := hna
  obtain ⟨x,hx,y,hy,hxy⟩ := exists_distinct_support_points ζ
  let r := dist x y/1000
  let s := 250/dist x y
  have hdist : 0 < dist x y := dist_pos.mpr hxy
  have hr : 0 < r := by dsimp only [r]; positivity
  have hs : 0 < s := by dsimp only [s]; positivity
  obtain ⟨μ₀,hμ₀,Cμ,hCμ,hbμ⟩ := compact_neighborhood_probability_for_published_radial E hE ζ hζ hC hball x hx hr
  obtain ⟨ν₀,hν₀,Cν,hCν,hbν⟩ := compact_neighborhood_probability_for_published_radial E hE ζ hζ hC hball y hy hr
  let f : Plane → Plane := fun z => s • z
  have hfc : Continuous f := by dsimp only [f]; fun_prop
  let μ₁ := μ₀.map hfc.aemeasurable
  let ν₁ := ν₀.map hfc.aemeasurable
  let Q : Fin 2 → DyadicSquare := ![(rootPatchEnvelope x r).dilate s,(rootPatchEnvelope y r).dilate s]
  have hgeo := normalized_root_patch_geometry x y hxy
  have hQ (l : Fin 2) : (Q l).side = 1 := by
    fin_cases l
    · exact hgeo.2.1
    · exact hgeo.2.2.1
  have hcent : dist (Q 0).center (Q 1).center = 250 := hgeo.2.2.2.1
  have hAK : IsCompact (f '' (E ∩ closedBall x r)) := (hE.inter_right isClosed_closedBall).image hfc
  have hBK : IsCompact (f '' (E ∩ closedBall y r)) := (hE.inter_right isClosed_closedBall).image hfc
  have hμA : (μ₁ : Measure Plane).support ⊆ f '' (E ∩ closedBall x r) :=
    support_subset_carrier μ₁ hAK.isClosed (dilate_carried_compact μ₀ _
      (hE.inter_right isClosed_closedBall) hμ₀ s)
  have hνB : (ν₁ : Measure Plane).support ⊆ f '' (E ∩ closedBall y r) :=
    support_subset_carrier ν₁ hBK.isClosed (dilate_carried_compact ν₀ _
      (hE.inter_right isClosed_closedBall) hν₀ s)
  have hμK := hAK.of_isClosed_subset Measure.isClosed_support hμA
  have hνK := hBK.of_isClosed_subset Measure.isClosed_support hνB
  have hμQ : (μ₁ : Measure Plane).support ⊆ (Q 0).carrier :=
    hμA.trans ((image_mono inter_subset_right).trans hgeo.2.2.2.2.1)
  have hνQ : (ν₁ : Measure Plane).support ⊆ (Q 1).carrier :=
    hνB.trans ((image_mono inter_subset_right).trans hgeo.2.2.2.2.2)
  have hsep : Disjoint (μ₁ : Measure Plane).support (ν₁ : Measure Plane).support := by
    apply disjoint_left.mpr
    intro z hz hz'
    have hx := (Q 0).dist_center_le_three_quarters (by rw [hQ 0]; norm_num) (hμQ hz)
    have hy := (Q 1).dist_center_le_three_quarters (by rw [hQ 1]; norm_num) (hνQ hz')
    have ht := dist_triangle (Q 0).center z (Q 1).center
    rw [hQ 0] at hx
    rw [hQ 1] at hy
    rw [hcent, dist_comm (Q 0).center z] at ht
    linarith
  let D := max (Cμ/s^(1+δ)) (Cν/s^(1+δ))
  have hD : 0 < D := (by positivity : 0 < Cμ/s^(1+δ)).trans_le (le_max_left _ _)
  have hbμ₁ : BallBound μ₁ (1+δ) D := by
    intro z a ha
    exact ((hbμ.dilate hs) z a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hbν₁ : BallBound ν₁ (1+δ) D := by
    intro z a ha
    exact ((hbν.dilate hs) z a ha).trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
  obtain ⟨μ,ν,hμK',hνK',hμsub,hνsub,D',hD',hbμ',hbν',K,hK,hU,hV⟩ :=
    source_uniform_radial_restrictions_of_published_radial hOrponen μ₁ ν₁ hμK hνK hsep hδ hδ1 hD hbμ₁ hbν₁
  have hμQ' := hμsub.trans hμQ
  have hνQ' := hνsub.trans hνQ
  refine ⟨δ,s,hδ,hδ1,hs,Q,hQ,hcent,μ,ν,hμK',hνK',
    hμsub.trans (hμA.trans (image_mono inter_subset_left)),
    hνsub.trans (hνB.trans (image_mono inter_subset_left)),hμQ',hνQ',?_,?_,
    D',hD',hbμ',hbν',K,hK,hU,hV⟩
  · exact measure_mono_null (compl_subset_compl.mpr hμQ') (μ : Measure Plane).support_mem_ae
  · exact measure_mono_null (compl_subset_compl.mpr hνQ') (ν : Measure Plane).support_mem_ae


end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_SmoothShellPartition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory Filter
open scoped ENNReal NNReal Topology

theorem sourceShellPartition_telescope (n : ℕ) (r : ℝ) :
    sourceShellLowpass 0 r + ∑ k ∈ Finset.range n, sourceShellBand k r = sourceShellLowpass n r := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ← add_assoc, ih, sourceShellBand]; ring

theorem sourceShellLowpass_tendsto (r : ℝ) :
    Tendsto (fun n => sourceShellLowpass n r) atTop (𝓝 1) := by
  have ht : Tendsto (fun n : ℕ => r/(2:ℝ)^n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  have h := sourceShellBump.continuous.continuousAt.tendsto.comp ht
  have hz : sourceShellBump (0:ℝ) = 1 := sourceShellBump.one_of_mem_closedBall (by
    change dist (0:ℝ) 0 ≤ 1
    norm_num)
  simpa only [sourceShellLowpass, hz, Function.comp_def] using h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SourceAssemblyParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric
open scoped ContDiff

theorem exists_source_assembly_parameters {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ β lam sig kap : ℝ, β = δ/10 ∧ 0 < lam ∧ lam < δ/1000 ∧ 0 < sig ∧
      0 < kap ∧ 1000000*kap < β ∧ sig < kap/1000 ∧
      10000000*(lam+sig)/kap < β/100 := by
  let kap := δ/1000000000
  let lam := δ^2/1000000000000000000000000
  have hd2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hd2δ : δ^2 < δ := by nlinarith
  have hkap : 0 < kap := by dsimp only [kap]; positivity
  refine ⟨δ/10,lam,lam,kap,rfl,?_,?_,?_,hkap,?_,?_,?_⟩
  · dsimp only [lam]; positivity
  · dsimp only [lam]; nlinarith
  · dsimp only [lam]; positivity
  · dsimp only [kap]; linarith
  · dsimp only [lam,kap]; nlinarith
  · apply (div_lt_iff₀ hkap).mpr
    dsimp only [lam,kap]
    nlinarith

theorem exists_assembly_shell_cutoff :
    ∃ Ψ : ℝ → ℝ, ContDiff ℝ ∞ Ψ ∧ (∀ x, 0 ≤ Ψ x) ∧
      (∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4) ∧
      (∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) := by
  refine ⟨assemblyShellBump,assemblyShellBump.contDiff,fun _ => assemblyShellBump.nonneg,?_,?_⟩
  · intro x hx
    have hh : dist x (5/4:ℝ) < 1 := by
      by_contra hn
      exact hx (assemblyShellBump.zero_of_le_dist (not_lt.mp hn))
    rw [Real.dist_eq,abs_lt] at hh
    constructor <;> linarith
  · intro x hx
    have hh : x ∈ closedBall (5/4:ℝ) assemblyShellBump.rIn := by
      change dist x (5/4:ℝ) ≤ 3/4
      rw [Real.dist_eq,abs_le]
      constructor <;> linarith [hx.1,hx.2]
    rw [assemblyShellBump.one_of_mem_closedBall hh]

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DistributionAbsoluteContinuity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal

 theorem locallyIntegrable_rnDeriv_smul (μ ν : Measure ℝ) [SigmaFinite μ] [SigmaFinite ν]
    (hac : μ ≪ ν) (f : ℝ → ℂ) (hf : LocallyIntegrable f μ) :
    LocallyIntegrable (fun x => (μ.rnDeriv ν x).toReal • f x) ν := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hi := (integrable_rnDeriv_smul_iff hac).mpr
    ((hf.integrableOn_isCompact hK).integrable_indicator hK.measurableSet)
  apply (integrable_indicator_iff hK.measurableSet).mp
  apply hi.congr
  filter_upwards with x
  by_cases hx : x ∈ K <;> simp [hx]

 theorem absolutelyContinuous_of_smooth_test_density (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : LocallyIntegrable f volume)
    (ht : ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      (∫ x, (g x : ℂ) ∂τ) = ∫ x, g x • f x) : τ ≪ volume := by
  let μ : Measure ℝ := τ+volume
  have hτ : τ ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_right le_rfl)
  have hv : volume ≪ μ := Measure.absolutelyContinuous_of_le (by
    apply Measure.le_iff.mpr
    intro s _
    exact le_add_left le_rfl)
  let a : ℝ → ℂ := fun x => ((τ.rnDeriv μ x).toReal : ℂ)
  let b : ℝ → ℂ := fun x => (volume.rnDeriv μ x).toReal • f x
  have ha : LocallyIntegrable a μ := by
    simpa only [smul_eq_mul, Complex.real_smul, mul_one] using
      locallyIntegrable_rnDeriv_smul τ μ hτ (fun _ => (1:ℂ))
        (continuous_const.locallyIntegrable)
  have hb : LocallyIntegrable b μ := locallyIntegrable_rnDeriv_smul volume μ hv f hf
  have hab : a =ᵐ[μ] b := by
    apply ae_eq_of_integral_contDiff_smul_eq ha hb
    intro g hg hc
    calc
      _ = ∫ x, (τ.rnDeriv μ x).toReal • (g x : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards with x
        simp [a, Complex.real_smul, mul_comm]
      _ = ∫ x, (g x : ℂ) ∂τ := integral_rnDeriv_smul hτ
      _ = ∫ x, g x • f x := ht g hg hc
      _ = ∫ x, (volume.rnDeriv μ x).toReal • (g x • f x) ∂μ :=
        (integral_rnDeriv_smul hv).symm
      _ = _ := by simp only [b, smul_comm (g _) ((volume.rnDeriv μ _).toReal)]
  intro S hS
  have hS' : ∀ᵐ x ∂volume, x ∉ S := by simpa only [ae_iff, not_not, Set.ofPred_mem_eq] using hS
  rw [← Measure.withDensity_rnDeriv_eq volume μ hv] at hS'
  have hz := (ae_withDensity_iff (Measure.measurable_rnDeriv volume μ)).mp hS'
  have hgoal : ∀ᵐ x ∂τ, x ∉ S := by
    rw [← Measure.withDensity_rnDeriv_eq τ μ hτ]
    apply (ae_withDensity_iff (Measure.measurable_rnDeriv τ μ)).mpr
    filter_upwards [hz,hab,Measure.rnDeriv_lt_top τ μ] with x hx he hfin
    intro hax hxS
    have hzero : volume.rnDeriv μ x = 0 := by
      by_contra hn
      exact hx hn hxS
    have hzreal : (τ.rnDeriv μ x).toReal = 0 := by
      have he' : ((τ.rnDeriv μ x).toReal : ℂ) = 0 := by
        simpa only [a,b,hzero,ENNReal.toReal_zero,zero_smul] using he
      exact Complex.ofReal_eq_zero.mp he'
    have heq := ENNReal.ofReal_toReal hfin.ne
    rw [hzreal, ENNReal.ofReal_zero] at heq
    exact hax heq.symm
  simpa only [ae_iff,not_not,Set.ofPred_mem_eq] using hgoal

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_MeasureKernelConvolution
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform

theorem shellKernelMeasureConvolution_L1 (τ : Measure ℝ) [IsFiniteMeasure τ] (n : ℕ) :
    Integrable (kernelMeasureConvolution (sourceShellKernel n) τ) ∧
      (∫ x, ‖kernelMeasureConvolution (sourceShellKernel n) τ x‖) ≤
        τ.real univ * ∫ x, ‖sourceShellKernel 0 x‖ := by
  simpa only [sourceShellKernel_uniform_L1] using kernelMeasureConvolution_L1
    (sourceShellKernel n) (sourceShellKernel_continuous n) (sourceShellKernel_integrable n) τ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellFrequencyTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped Topology

theorem sourceShellLowpass_abs_le (n : ℕ) (r : ℝ) : |sourceShellLowpass n r| ≤ 1 := by
  rw [abs_of_nonneg (show 0 ≤ sourceShellLowpass n r from sourceShellBump.nonneg)]
  exact sourceShellBump.le_one

theorem sourceShellLowpass_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, sourceShellLowpass n r • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun r => sourceShellLowpass n r • (charFun τ r * f r)) volume :=
    (sourceShellLowpass_smooth n).continuous.aestronglyMeasurable.smul
      (continuous_charFun.aestronglyMeasurable.mul hf.aestronglyMeasurable)
  have hb (n : ℕ) : ∀ᵐ r ∂volume,
      ‖sourceShellLowpass n r • (charFun τ r * f r)‖ ≤ τ.real univ * ‖f r‖ := by
    filter_upwards with r
    rw [norm_smul, Real.norm_eq_abs, norm_mul]
    calc
      |sourceShellLowpass n r| * (‖charFun τ r‖ * ‖f r‖) ≤
          1 * (‖charFun τ r‖ * ‖f r‖) :=
        mul_le_mul_of_nonneg_right (sourceShellLowpass_abs_le n r) (by positivity)
      _ ≤ τ.real univ * ‖f r‖ := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_right (norm_charFun_le r) (norm_nonneg _)
  have hp : ∀ᵐ r ∂volume,
      Tendsto (fun n => sourceShellLowpass n r • (charFun τ r * f r)) atTop
        (𝓝 (charFun τ r * f r)) := by
    filter_upwards with r
    simpa using (sourceShellLowpass_tendsto r).smul (tendsto_const_nhds (x := charFun τ r * f r))
  exact tendsto_integral_of_dominated_convergence (fun r => τ.real univ * ‖f r‖)
    hm (hf.norm.const_mul _) hb hp

theorem sourceShellPartition_fourier_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (f : ℝ → ℂ) (hf : Integrable f) :
    Tendsto (fun n => ∫ r, (sourceShellLowpass 0 r +
      ∑ k ∈ Finset.range n, sourceShellBand k r) • (charFun τ r * f r)) atTop
      (𝓝 (∫ r, charFun τ r * f r)) := by
  simpa only [sourceShellPartition_telescope] using sourceShellLowpass_fourier_test τ f hf

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SpatialFourierTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceInverseKernel_pairing (f : ℝ → ℂ) (hf : Integrable f)
    (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * sourceInverseKernel f x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * 𝓕 φ (r/(2*Real.pi)) := by
  let g : ℝ × ℝ → ℂ := fun z =>
    φ z.1 * (Complex.exp (↑(-z.1*z.2)*Complex.I) * f z.2)
  have hg : AEStronglyMeasurable g (volume.prod volume) :=
    φ.continuous.aestronglyMeasurable.comp_fst.mul
      ((by fun_prop : Continuous (fun z : ℝ × ℝ =>
        Complex.exp (↑(-z.1*z.2)*Complex.I))).aestronglyMeasurable.mul
        hf.aestronglyMeasurable.comp_snd)
  have hi : Integrable g (volume.prod volume) :=
    (φ.integrable.norm.mul_prod hf.norm).mono' hg (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [sourceInverseKernel_formula, mul_smul_comm, ← integral_const_mul]
  rw [integral_smul, integral_integral_swap hi]
  congr 1
  apply integral_congr_ae
  filter_upwards with r
  rw [SchwartzMap.fourier_coe, Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  have he : -2*Real.pi*x*(r/(2*Real.pi)) = -x*r := by field_simp
  rw [he, smul_eq_mul]
  ring

 theorem sourceSchwartz_inversion (φ : 𝓢(ℝ, ℂ)) (y : ℝ) :
    (2*Real.pi)⁻¹ • (∫ r, Complex.exp (↑(r*y)*Complex.I) * 𝓕 φ (r/(2*Real.pi))) = φ y := by
  have hs := Measure.integral_comp_div
    (fun u : ℝ => Complex.exp (↑(2*Real.pi*u*y)*Complex.I) * 𝓕 φ u) (2*Real.pi)
  have he (r : ℝ) : 2*Real.pi*(r/(2*Real.pi))*y = r*y := by field_simp
  simp_rw [he] at hs
  rw [hs, abs_of_pos (by positivity : (0:ℝ)<2*Real.pi), smul_smul,
    inv_mul_cancel₀ (by positivity), one_smul]
  have h := congrArg (fun ψ : 𝓢(ℝ, ℂ) => ψ y)
    (show (𝓕⁻ (𝓕 φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ)) = φ from
      FourierTransform.fourierInv_fourier_eq φ)
  simpa only [SchwartzMap.fourierInv_coe, Real.fourierInv_eq', real_inner_eq_re_inner,
    RCLike.inner_apply, conj_trivial, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using h

 theorem source_characteristic_schwartz_test (τ : Measure ℝ) [IsFiniteMeasure τ]
    (φ : 𝓢(ℝ, ℂ)) :
    (2*Real.pi)⁻¹ • (∫ r, charFun τ r * 𝓕 φ (r/(2*Real.pi))) = ∫ y, φ y ∂τ := by
  let f : ℝ → ℂ := fun r => 𝓕 φ (r/(2*Real.pi))
  have hf : Integrable f := (𝓕 φ).integrable.comp_div (by positivity)
  let g : ℝ × ℝ → ℂ := fun z => Complex.exp (↑(z.1*z.2)*Complex.I)*f z.1
  have hp : Integrable g (volume.prod τ) :=
    (hf.norm.comp_fst τ).mono' (by dsimp [g, f]; fun_prop) (by
      filter_upwards with z
      simp [g, Complex.norm_exp, Complex.mul_re])
  simp_rw [charFun_apply_real, ← integral_mul_const]
  have he (r y : ℝ) : Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r = g (r,y) := by
    simp [g, Complex.ofReal_mul]
  change (2*Real.pi)⁻¹ • (∫ r : ℝ, ∫ y : ℝ, Complex.exp ((r:ℂ)*(y:ℂ)*Complex.I) * f r ∂τ) = _
  simp_rw [he]
  rw [integral_integral_swap hp, ← integral_smul]
  apply integral_congr_ae
  filter_upwards with y
  exact sourceSchwartz_inversion φ y

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_LowFrequencyKernel
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem schwartz_charFun_integrable (f : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * charFun τ r) := by
  apply (f.integrable.norm.mul_const (τ.real univ)).mono' (by fun_prop)
  filter_upwards with r
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_charFun_le r) (norm_nonneg _)

 theorem schwartzKernelMeasureConvolution_test (f : 𝓢(ℝ, ℂ))
    (τ : Measure ℝ) [IsFiniteMeasure τ] (φ : 𝓢(ℝ, ℂ)) :
    (∫ x, φ x * kernelMeasureConvolution (sourceInverseKernel f) τ x) =
      (2*Real.pi)⁻¹ • ∫ r, f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi))) := by
  have he : kernelMeasureConvolution (sourceInverseKernel f) τ =
      sourceInverseKernel (fun r => f r * charFun τ r) :=
    funext (sourceInverseKernel_measure f f.continuous f.integrable τ)
  rw [he, sourceInverseKernel_pairing _ (schwartz_charFun_integrable f τ) φ]
  simp only [mul_assoc]

 theorem schwartz_cutoff_test_integrable (f φ : 𝓢(ℝ, ℂ)) (τ : Measure ℝ) [IsFiniteMeasure τ] :
    Integrable (fun r => f r * (charFun τ r * 𝓕 φ (r/(2*Real.pi)))) := by
  have h2 := (schwartz_charFun_integrable f τ)
  have hb : ∃ C : ℝ, ∀ r, ‖𝓕 φ (r/(2*Real.pi))‖ ≤ C := by
    obtain ⟨C,_,hC⟩ := (𝓕 φ).decay 0 0
    exact ⟨C, fun r => by simpa using hC (r/(2*Real.pi))⟩
  obtain ⟨C,hC⟩ := hb
  apply (h2.norm.mul_const C).mono' (by fun_prop)
  filter_upwards with r
  rw [← mul_assoc, norm_mul]
  exact mul_le_mul_of_nonneg_left (hC r) (norm_nonneg _)

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellSummability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem summable_dyadic_decay {a : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ => (2:ℝ)^(-a*(n:ℝ))) := by
  have hq : (2:ℝ)^(-a) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  convert summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num) (-a)) hq using 1
  all_goals try with_reducible_and_instances rfl
  funext n
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

 theorem shellL2Term_norm_sq_le (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL2Term τN n‖^2 ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := by
  rw [shellL2Term, ← integral_sq_norm_toLp]
  exact (shellKernelMeasureConvolution_L2 (τN (n+1)) n).2

 theorem shellL2Term_norm_summable (τN : ℕ → FiniteMeasure ℝ)
    {γ C : ℝ} (hγ : 0 < γ) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, shellEnergy (τN N) N ≤ C*(2:ℝ)^(-γ*(N:ℝ))) :
    Summable (fun n => ‖shellL2Term τN n‖) := by
  have hs := (summable_dyadic_decay (half_pos hγ)).mul_left (Real.sqrt ((2*Real.pi)⁻¹*C))
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  calc
    _ ≤ (2*Real.pi)⁻¹ * shellEnergy (τN (n+1)) (n+1) := shellL2Term_norm_sq_le τN n
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*((n+1:ℕ):ℝ))) :=
      mul_le_mul_of_nonneg_left (hb _ (by omega)) (by positivity)
    _ ≤ (2*Real.pi)⁻¹ * (C*(2:ℝ)^(-γ*(n:ℝ))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = (Real.sqrt ((2*Real.pi)⁻¹*C) * (2:ℝ)^(-(γ/2)*(n:ℝ)))^2 := by
      rw [mul_pow, Real.sq_sqrt (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul (by norm_num)]
      rw [← mul_assoc]
      congr 2
      push_cast
      ring

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellErrorSummability
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped ENNReal Topology

 theorem shellL1Error_norm_le (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ) (n : ℕ) :
    ‖shellL1Error τ τN n‖ ≤ (variationDistance τ (τN (n+1))).toReal *
      ∫ x, ‖sourceShellKernel 0 x‖ := by
  have hi := (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).1
  rw [shellL1Error, Lp.norm_toLp, eLpNorm_one_eq_lintegral_enorm,
    ← integral_norm_eq_lintegral_enorm hi.aestronglyMeasurable]
  exact (shellKernelMeasureConvolution_sub_L1 τ (τN (n+1)) n).2

 theorem shellL1Error_norm_summable (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    {η C : ℝ} (hη : 0 < η) (hC : 0 < C) (N₀ : ℕ)
    (hb : ∀ N ≥ N₀, variationDistance τ (τN N) ≤ ENNReal.ofReal (C*(2:ℝ)^(-η*(N:ℝ)))) :
    Summable (fun n => ‖shellL1Error τ τN n‖) := by
  let K := ∫ x, ‖sourceShellKernel 0 x‖
  have hK : 0 ≤ K := integral_nonneg (fun x => norm_nonneg _)
  have hs := (summable_dyadic_decay hη).mul_left (C*K)
  apply hs.of_norm_bounded_eventually_nat
  filter_upwards [eventually_ge_atTop N₀] with n hn
  rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  calc
    _ ≤ (variationDistance τ (τN (n+1))).toReal * K := shellL1Error_norm_le τ τN n
    _ ≤ (C*(2:ℝ)^(-η*((n+1:ℕ):ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hb (n+1) (by omega))
      rw [ENNReal.toReal_ofReal (show 0 ≤ C*(2:ℝ)^(-η*((n+1:ℕ):ℝ)) by positivity)] at h
      exact h
    _ ≤ (C*(2:ℝ)^(-η*(n:ℝ))) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      apply mul_le_mul_of_nonneg_left _ hC.le
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      push_cast
      nlinarith
    _ = _ := by ring

 theorem shell_approximations_summable (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ τN : ℕ → FiniteMeasure ℝ,
      Summable (fun n => ‖shellL2Term τN n‖) ∧
      Summable (fun n => ‖shellL1Error τ τN n‖) ∧
      Summable (shellL2Term τN) ∧ Summable (shellL1Error τ τN) := by
  obtain ⟨τN,η,γ,Ctv,Cshell,hη,hγ,hCtv,hCshell,N₀,hb⟩ := hτ
  have h2 := shellL2Term_norm_summable τN hγ hCshell N₀ (fun N hN => (hb N hN).2)
  have h1 := shellL1Error_norm_summable τ τN hη hCtv N₀ (fun N hN => (hb N hN).1)
  exact ⟨τN,h2,h1,h2.of_norm,h1.of_norm⟩

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_SchwartzLpTests
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology ENNReal

 theorem schwartzLpTest_apply (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : Lp (α := ℝ) ℂ p volume) : schwartzLpTest p φ f = ∫ x, φ x * f x := by
  exact Lp.toTemperedDistribution_apply f φ

 theorem schwartzLpTest_toLp (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℝ → ℂ) (hf : MemLp f p volume) :
    schwartzLpTest p φ (hf.toLp f) = ∫ x, φ x * f x := by
  rw [schwartzLpTest_apply]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

 theorem schwartzLpTest_sum_tendsto (p : ℝ≥0∞) [Fact (1 ≤ p)] (φ : 𝓢(ℝ, ℂ))
    (f : ℕ → Lp (α := ℝ) ℂ p volume) (hf : Summable f) :
    Tendsto (fun N => ∑ n ∈ Finset.range N, schwartzLpTest p φ (f n)) atTop
      (𝓝 (schwartzLpTest p φ (∑' n, f n))) := by
  simpa only [Function.comp_def, map_sum] using
    ((schwartzLpTest p φ).continuous.tendsto (∑' n, f n)).comp hf.tendsto_sum_tsum_nat

 theorem schwartzLpTest_shell_recombine (τ : FiniteMeasure ℝ) (τN : ℕ → FiniteMeasure ℝ)
    (φ : 𝓢(ℝ, ℂ)) (n : ℕ) :
    schwartzLpTest 1 φ (shellL1Error τ τN n) + schwartzLpTest 2 φ (shellL2Term τN n) =
      ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
  rw [shellL1Error, shellL2Term, schwartzLpTest_toLp, schwartzLpTest_toLp]
  have ht : Integrable (fun x => φ x * kernelMeasureConvolution (sourceShellKernel n) τ x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 τ n).1)
  have hn : Integrable (fun x => φ x *
      kernelMeasureConvolution (sourceShellKernel n) (τN (n+1)) x) :=
    (φ.memLp_top volume).integrable_mul
      (memLp_one_iff_integrable.mpr (shellKernelMeasureConvolution_L1 (τN (n+1)) n).1)
  simp_rw [mul_sub]
  rw [integral_sub ht hn, sub_add_cancel]

 theorem schwartzLpTest_low (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    schwartzLpTest 1 φ (sourceLowTerm τ) =
      (2*Real.pi)⁻¹ • ∫ r, sourceShellLowpass 0 r •
        (charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))) := by
  rw [sourceLowTerm, schwartzLpTest_toLp]
  simpa only [sourceLowKernel, sourceLowpassSchwartz_apply, Complex.real_smul] using
    schwartzKernelMeasureConvolution_test sourceLowpassSchwartz τ φ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellTestConvergence
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem sourceShell_spatial_test_tendsto (τ : FiniteMeasure ℝ) (φ : 𝓢(ℝ, ℂ)) :
    Tendsto (fun N => schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x)
      atTop (𝓝 (∫ x, φ x ∂(τ : Measure ℝ))) := by
  let t : ℝ → ℂ := fun r => charFun (τ : Measure ℝ) r * 𝓕 φ (r/(2*Real.pi))
  have hi0 : Integrable (fun r => sourceShellLowpass 0 r • t r) := by
    simpa only [sourceLowpassSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable sourceLowpassSchwartz φ τ
  have hin (n : ℕ) : Integrable (fun r => sourceShellBand n r • t r) := by
    simpa only [sourceShellSchwartz_apply,Complex.real_smul] using
      schwartz_cutoff_test_integrable (sourceShellSchwartz n) φ τ
  have he (N : ℕ) : schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x =
      (2*Real.pi)⁻¹ • ∫ r, (sourceShellLowpass 0 r +
        ∑ n ∈ Finset.range N, sourceShellBand n r) • t r := by
    rw [schwartzLpTest_low]
    simp_rw [sourceShellKernel, schwartzKernelMeasureConvolution_test,
      sourceShellSchwartz_apply, ← Complex.real_smul]
    rw [← Finset.smul_sum, ← smul_add]
    congr 1
    simp_rw [add_smul, Finset.sum_smul]
    rw [integral_add hi0 (integrable_finsetSum _ (fun n _ => hin n)),
      integral_finsetSum _ (fun n _ => hin n)]
  simp_rw [he]
  have h := (sourceShellPartition_fourier_test (τ : Measure ℝ)
    (fun r => 𝓕 φ (r/(2*Real.pi))) ((𝓕 φ).integrable.comp_div (by positivity))).const_smul
    ((2*Real.pi)⁻¹)
  rw [source_characteristic_schwartz_test] at h
  exact h

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_ShellReconstruction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set Filter
open scoped FourierTransform SchwartzMap Topology

 theorem shell_reconstruction_test_density (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    ∃ a : Lp (α := ℝ) ℂ 1 volume, ∃ b : Lp (α := ℝ) ℂ 2 volume,
      ∀ φ : 𝓢(ℝ, ℂ), (∫ x, φ x * (a x+b x)) = ∫ x, φ x ∂(τ : Measure ℝ) := by
  obtain ⟨τN,_,_,h2,h1⟩ := shell_approximations_summable τ hτ
  let a : Lp (α := ℝ) ℂ 1 volume := sourceLowTerm τ + ∑' n, shellL1Error τ τN n
  let b : Lp (α := ℝ) ℂ 2 volume := ∑' n, shellL2Term τN n
  refine ⟨a,b,?_⟩
  intro φ
  have hlim := ((schwartzLpTest_sum_tendsto 1 φ _ h1).const_add
    (schwartzLpTest 1 φ (sourceLowTerm τ))).add (schwartzLpTest_sum_tendsto 2 φ _ h2)
  have he (N : ℕ) : (schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, schwartzLpTest 1 φ (shellL1Error τ τN n)) +
      ∑ n ∈ Finset.range N, schwartzLpTest 2 φ (shellL2Term τN n) =
      schwartzLpTest 1 φ (sourceLowTerm τ) +
      ∑ n ∈ Finset.range N, ∫ x, φ x * kernelMeasureConvolution (sourceShellKernel n) τ x := by
    rw [add_assoc, ← Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    exact schwartzLpTest_shell_recombine τ τN φ n
  simp_rw [he] at hlim
  have hval : schwartzLpTest 1 φ a + schwartzLpTest 2 φ b =
      ∫ x, φ x ∂(τ : Measure ℝ) := by
    have hu := tendsto_nhds_unique hlim (sourceShell_spatial_test_tendsto τ φ)
    simpa only [a,b,map_add] using hu
  have ha := (φ.memLp_top volume).integrable_mul (Lp.memLp a)
  have hb := (φ.memLp 2 volume).integrable_mul (Lp.memLp b)
  change Integrable (fun x => φ x * a x) at ha
  change Integrable (fun x => φ x * b x) at hb
  rw [← hval, schwartzLpTest_apply, schwartzLpTest_apply]
  simp_rw [mul_add]
  exact integral_add ha hb

 theorem shell_reconstruction_locallyIntegrable (τ : FiniteMeasure ℝ)
    (hτ : HasShellApproximations τ) :
    ∃ f : ℝ → ℂ, LocallyIntegrable f volume ∧
      ∀ (g : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
        (∫ x, (g x : ℂ) ∂(τ : Measure ℝ)) = ∫ x, g x • f x := by
  obtain ⟨a,b,ht⟩ := shell_reconstruction_test_density τ hτ
  refine ⟨fun x => a x+b x,
    ((Lp.memLp a).locallyIntegrable (by norm_num)).add
      ((Lp.memLp b).locallyIntegrable (by norm_num)), ?_⟩
  intro g hg hc
  let φ : 𝓢(ℝ, ℂ) := (hc.comp_left (map_zero Complex.ofRealCLM)).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  exact (ht φ).symm

 theorem shell_criterion (τ : FiniteMeasure ℝ) (hτ : HasShellApproximations τ) :
    (τ : Measure ℝ) ≪ volume := by
  obtain ⟨f,hf,ht⟩ := shell_reconstruction_locallyIntegrable τ hτ
  exact absolutelyContinuous_of_smooth_test_density τ f hf ht

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_DistanceMeasure
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open MeasureTheory Set
open scoped ENNReal

theorem weightedDistance_mass (π : Measure (Plane × Plane)) :
    weightedDistance π univ = ∫⁻ z, distanceWeight z ∂π := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    MeasurableSet.univ, Set.preimage_univ, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

theorem weightedDistance_mass_bounds (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ≤ weightedDistance π univ ∧
      weightedDistance π univ ≤ ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by
  rw [weightedDistance_mass]
  constructor
  · calc
      ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) = ∫⁻ _ : Plane × Plane,
        ENNReal.ofReal (dmax ^ (-1/2 : ℝ)) ∂π := by simp
      _ ≤ ∫⁻ z, distanceWeight z ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos (hmin.trans_le hz.1) hz.2 (by norm_num)
  · calc
      (∫⁻ z, distanceWeight z ∂π) ≤ ∫⁻ _ : Plane × Plane,
          ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) ∂π := by
        apply lintegral_mono_ae
        filter_upwards [hsep] with z hz
        apply ENNReal.ofReal_le_ofReal
        exact Real.rpow_le_rpow_of_nonpos hmin hz.1 (by norm_num)
      _ = ENNReal.ofReal (dmin ^ (-1/2 : ℝ)) := by simp

theorem weightedDistance_positive_finite (π : Measure (Plane × Plane)) [IsProbabilityMeasure π]
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂π, dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax) :
    0 < weightedDistance π univ ∧ weightedDistance π univ < ∞ := by
  obtain ⟨hl,hu⟩ := weightedDistance_mass_bounds π hmin hsep
  exact ⟨(ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hmax _)).trans_le hl,
    hu.trans_lt ENNReal.ofReal_lt_top⟩

theorem weightedDistance_carried (π : Measure (Plane × Plane))
    {E : Set Plane} (hE : IsCompact E) (hcarrier : π (E ×ˢ E)ᶜ = 0) :
    weightedDistance π (distanceSet E)ᶜ = 0 := by
  rw [weightedDistance, Measure.map_apply (continuous_fst.dist continuous_snd).measurable
    (distanceSet_measurable hE).compl]
  apply withDensity_absolutelyContinuous π distanceWeight
  apply measure_mono_null _ hcarrier
  intro z hz hzin
  exact hz ⟨z.1,hzin.1,z.2,hzin.2,rfl⟩

theorem product_carried (μ ν : Measure Plane) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (E : Set Plane) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0) :
    (μ.prod ν) (E ×ˢ E)ᶜ = 0 := by
  have hleft : (μ.prod ν) (Eᶜ ×ˢ (univ : Set Plane)) = 0 := by simp [Measure.prod_prod,hμ]
  have hright : (μ.prod ν) ((univ : Set Plane) ×ˢ Eᶜ) = 0 := by simp [Measure.prod_prod,hν]
  apply measure_mono_null _ (measure_union_null hleft hright)
  intro z hz
  by_cases hx : z.1 ∈ E
  · right
    refine ⟨Set.mem_univ _, ?_⟩
    intro hy
    exact hz ⟨hx,hy⟩
  · left
    exact ⟨hx,Set.mem_univ _⟩

theorem positive_distance_volume_of_weighted_ac (μ ν : Measure Plane)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {E : Set Plane} (hE : IsCompact E) (hμ : μ Eᶜ = 0) (hν : ν Eᶜ = 0)
    {dmin dmax : ℝ} (hmin : 0 < dmin) (hmax : 0 < dmax)
    (hsep : ∀ᵐ z ∂(μ.prod ν), dmin ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ dmax)
    (hac : weightedDistance (μ.prod ν) ≪ volume) : 0 < volume (distanceSet E) := by
  exact distanceSet_positive_of_measure E (weightedDistance (μ.prod ν))
    (weightedDistance_positive_finite (μ.prod ν) hmin hmax hsep).1
    (weightedDistance_carried (μ.prod ν) hE (product_carried μ ν E hμ hν)) hac

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Shells_NormalizedOuterShell
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ConditionalPlanar
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem manuscript_main_of_published_radial (hOrponen : PublishedPlanarRadialMoment) (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
    0 < volume (distanceSet E) := by
  obtain ⟨δ,s,hδ,hδ1,hs,Q,hQ,hcent,μ,ν,_,_,hμE,hνE,_,_,hμQ,hνQ,
    C,hC,hball₀,hball₁,K,hK,hμrad,hνrad⟩ := exists_normalized_root_setup_of_published_radial hOrponen E hE hd
  obtain ⟨β,lam,sig,kap,hβ,hlam,hlamδ,hsig,hkap,hkapβ,hgap,hratio⟩ :=
    exists_source_assembly_parameters hδ hδ1
  obtain ⟨Ψ,hΨ,hpos,hsupp,hone⟩ := exists_assembly_shell_cutoff
  have hp1 : 1 < 1+δ/8 := by linarith
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hμrad' : ∀ᵐ x ∂(μ:Measure Plane),
      sourceDensityNorm (1+δ/8) ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K := by
    filter_upwards [(μ:Measure Plane).support_mem_ae] with x hx
    exact hμrad x hx
  have hνrad' : ∀ᵐ y ∂(ν:Measure Plane),
      sourceDensityNorm (1+δ/8) ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K := by
    filter_upwards [(ν:Measure Plane).support_mem_ae] with y hy
    exact hνrad y hy
  have hlo : 100 ≤ dist (Q 0).center (Q 1).center := by rw [hcent]; norm_num
  have hhi : dist (Q 0).center (Q 1).center ≤ 2000 := by rw [hcent]; norm_num
  obtain ⟨hτ,happrox⟩ := two_root_has_shell_approximations Q hQ hlo hhi μ ν hμQ hνQ
    hδ hδ1 hβ hlam hlamδ hsig hkap hkapβ hgap hratio hC.le hC.le hball₀ hball₁
    hpq hK hμrad' hνrad' hΨ hpos hsupp hone
  have hac := shell_criterion ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ happrox
  have hsep : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane),
      90 ≤ dist z.1 z.2 ∧ dist z.1 z.2 ≤ 2010 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμQ,
      Measure.quasiMeasurePreserving_snd.ae hνQ] with z hx hy
    exact separated_unit_roots_distance Q hQ hlo hhi z.1 z.2 hx hy
  have hcompact : IsCompact ((fun x : Plane => s • x) '' E) := hE.image (by fun_prop)
  have hcarry₀ : (μ:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hμE) (μ:Measure Plane).support_mem_ae
  have hcarry₁ : (ν:Measure Plane) ((fun x : Plane => s • x) '' E)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr hνE) (ν:Measure Plane).support_mem_ae
  apply distanceSet_positive_of_dilate E hs
  exact positive_distance_volume_of_weighted_ac (μ:Measure Plane) (ν:Measure Plane)
    hcompact hcarry₀ hcarry₁ (by norm_num : (0:ℝ) < 90) (by norm_num : (0:ℝ) < 2010) hsep hac

end PlanarFalconer

namespace Falconer
open MeasureTheory Set

/-- The two-dimensional instance of the main theorem. -/
theorem planar_case_of_published_radial
    (hOrponen : PlanarFalconer.PublishedPlanarRadialMoment)
    (E : Set (Space 2)) (hE : IsCompact E) (hd : 1 < dimH E) :
    0 < volume (distanceSet E) :=
  PlanarFalconer.manuscript_main_of_published_radial hOrponen E hE hd

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiniteHolder
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The equal-exponent finite Hölder inequality for coordinate deletion

This is the finite sum inequality needed in the induction proving the exact
lattice Loomis–Whitney input. It follows from weighted arithmetic–geometric
mean after normalizing each row by its actual sum.
-/
namespace Falconer
open scoped BigOperators

variable {ι α : Type*}

theorem finite_holder_equal (I : Finset ι) (B : Finset α) (hI : I.Nonempty)
    (f : ι → α → ℝ) (hf : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ f i x) :
    (∑ x ∈ B, ∏ i ∈ I, (f i x) ^ (1/(I.card:ℝ))) ≤
      ∏ i ∈ I, (∑ x ∈ B, f i x) ^ (1/(I.card:ℝ)) := by
  classical
  let p : ℝ := 1/(I.card:ℝ)
  let M : ι → ℝ := fun i => ∑ x ∈ B, f i x
  have hcard : 0 < (I.card:ℝ) := by exact_mod_cast hI.card_pos
  have hp : 0 < p := one_div_pos.mpr hcard
  have hweights : ∑ _i ∈ I, p = 1 := by
    simp only [Finset.sum_const,nsmul_eq_mul,p]
    exact mul_one_div_cancel hcard.ne'
  have hMnonneg : ∀ i ∈ I, 0 ≤ M i := fun i hi =>
    Finset.sum_nonneg (fun x hx => hf i hi x hx)
  by_cases hM : ∀ i ∈ I, 0 < M i
  · let g : ι → α → ℝ := fun i x => f i x / M i
    have hg : ∀ i ∈ I, ∀ x ∈ B, 0 ≤ g i x :=
      fun i hi x hx => div_nonneg (hf i hi x hx) (hMnonneg i hi)
    have hgsum : ∀ i ∈ I, ∑ x ∈ B, g i x = 1 := by
      intro i hi
      simp only [g,← Finset.sum_div,M]
      exact div_self (hM i hi).ne'
    have hmean : ∀ x ∈ B, (∏ i ∈ I, (g i x)^p) ≤ ∑ i ∈ I, p*g i x := by
      intro x hx
      exact Real.geom_mean_le_arith_mean_weighted I (fun _ => p) (fun i => g i x)
        (fun _ _ => hp.le) hweights (fun i hi => hg i hi x hx)
    have hsum : (∑ x ∈ B, ∏ i ∈ I, (g i x)^p) ≤ 1 := by
      calc
        _ ≤ ∑ x ∈ B, ∑ i ∈ I, p*g i x := Finset.sum_le_sum hmean
        _ = ∑ i ∈ I, p*(∑ x ∈ B, g i x) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum]
        _ = 1 := by
          calc
            _ = ∑ i ∈ I, p := Finset.sum_congr rfl (fun i hi => by rw [hgsum i hi,mul_one])
            _ = 1 := hweights
    have hprod : ∀ x ∈ B, (∏ i ∈ I, (f i x)^p) =
        (∏ i ∈ I, (M i)^p)*(∏ i ∈ I, (g i x)^p) := by
      intro x hx
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i hi
      change (f i x)^p = (M i)^p*(f i x/M i)^p
      rw [Real.div_rpow (hf i hi x hx) (hMnonneg i hi)]
      have hne : (M i)^p ≠ 0 := (Real.rpow_pos_of_pos (hM i hi) _).ne'
      field_simp
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    calc
      _ = (∏ i ∈ I, (M i)^p)*(∑ x ∈ B, ∏ i ∈ I, (g i x)^p) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl hprod
      _ ≤ (∏ i ∈ I, (M i)^p)*1 :=
        mul_le_mul_of_nonneg_left hsum (Finset.prod_nonneg (fun i hi => Real.rpow_nonneg (hMnonneg i hi) _))
      _ = _ := mul_one _
  · push Not at hM
    obtain ⟨i,hi,hMi⟩ := hM
    have hzero : M i = 0 := le_antisymm hMi (hMnonneg i hi)
    have hrow : ∀ x ∈ B, f i x = 0 := by
      intro x hx
      apply le_antisymm _ (hf i hi x hx)
      calc
        f i x ≤ ∑ y ∈ B, f i y := Finset.single_le_sum (fun y hy => hf i hi y hy) hx
        _ = 0 := hzero
    have hleft : (∑ x ∈ B, ∏ j ∈ I, (f j x)^p) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      apply Finset.prod_eq_zero hi
      rw [hrow x hx,Real.zero_rpow hp.ne']
    change (∑ x ∈ B, ∏ i ∈ I, (f i x)^p) ≤ ∏ i ∈ I, (M i)^p
    rw [hleft]
    exact Finset.prod_nonneg (fun j hj => Real.rpow_nonneg (hMnonneg j hj) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceMoment
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The natural-number incidence moment used to select transverse pins -/

namespace Falconer
open MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

private theorem rpow_pow_nat (x : ℝ≥0∞) (a : ℝ) (k : ℕ) :
    (x^a)^k = x^(a*k) := by
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]

theorem incidence_moment (μ : Measure X) (F : X → ℝ≥0∞) (hF : AEMeasurable F μ)
    {k : ℕ} (hk : 2 ≤ k) :
    (∫⁻ x, F x ∂μ)^k ≤ (∫⁻ x, (F x)^k ∂μ)*(μ Set.univ)^(k-1) := by
  have hk' : 1 < (k:ℝ) := by exact_mod_cast (show 1 < k by omega)
  have hk0 : (k:ℝ) ≠ 0 := by linarith
  have hkm0 : (k:ℝ)-1 ≠ 0 := by linarith
  have hc : (k:ℝ).HolderConjugate ((k:ℝ)/((k:ℝ)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hk').mpr rfl
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc hF
    (aemeasurable_const : AEMeasurable (fun _ : X => (1:ℝ≥0∞)) μ)
  simp only [Pi.mul_apply,mul_one,ENNReal.one_rpow,lintegral_one,
    ENNReal.rpow_natCast] at hH
  have hp := pow_le_pow_left' hH k
  apply hp.trans_eq
  rw [mul_pow,rpow_pow_nat,rpow_pow_nat]
  have hfirst : (1/(k:ℝ))*(k:ℝ) = 1 := by field_simp
  have hsecond : (1/((k:ℝ)/((k:ℝ)-1)))*(k:ℝ) = ((k-1:ℕ):ℝ) := by
    rw [Nat.cast_sub (by omega : 1 ≤ k),Nat.cast_one]
    field_simp
  rw [hfirst,hsecond,ENNReal.rpow_one,ENNReal.rpow_natCast]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PublishedHeavyPlates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The published heavy-hyperplane cover used by the coarse-filter construction

P. Shmerkin, *A non-linear version of Bourgain's projection theorem*,
J. Eur. Math. Soc. 25 (2023), 4155--4204, Appendix B, Lemma B.3,
printed pages 4201--4202, DOI 10.4171/JEMS/1283.
Publisher PDF: https://ems.press/content/serial-article-files/32954 .

This is only the hyperplane case k=d-1, at the single scale used in the
application, with heavy threshold delta^(a/8192). The lower-dimensional
concentration hypothesis is retained explicitly. The conclusion covers
each heavy plate in the unit ball by one of finitely many thicker plates.
The constant is allowed to depend on the dimension, a and C. No assertion
about dyadic filters, retained product mass or distance sets is assumed.
-/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem heavyPlateExponent_pos {a : ℝ} (ha : 0 < a) : 0 < heavyPlateExponent a := by
  unfold heavyPlateExponent
  positivity

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_AffineSlabCluster
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Affine slabs with a common point and nearby normal directions -/

namespace Falconer
open Set NormedSpace
variable {d : ℕ}

theorem affine_slab_cluster {u v x y : Space d} {a b M r τ : ℝ}
    (hx : ‖x‖ ≤ M) (hy : ‖y‖ ≤ M) (hτ : normalDistance u v ≤ τ)
    (hux : |inner ℝ u x-a| ≤ r) (hvx : |inner ℝ v x-b| ≤ r)
    (hvy : |inner ℝ v y-b| ≤ r) :
    |inner ℝ u y-a| ≤ 2*M*τ+3*r := by
  have hM : 0 ≤ M := (norm_nonneg x).trans hx
  have hxy : ‖y-x‖ ≤ 2*M := (norm_sub_le y x).trans (by linarith only [hx,hy])
  have hvxy : |inner ℝ v (y-x)| ≤ 2*r := by
    rw [inner_sub_right]
    have he : inner ℝ v y-inner ℝ v x = (inner ℝ v y-b)-(inner ℝ v x-b) := by ring
    rw [he]
    exact (abs_sub _ _).trans (by linarith only [hvx,hvy])
  have huxy : |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
    have helper (w : Space d) (hw : ‖u-w‖ ≤ τ)
        (hwi : |inner ℝ w (y-x)| ≤ 2*r) :
        |inner ℝ u (y-x)| ≤ 2*M*τ+2*r := by
      have he : inner ℝ u (y-x) = inner ℝ (u-w) (y-x)+inner ℝ w (y-x) := by
        rw [inner_sub_left]; ring
      rw [he]
      apply (abs_add_le _ _).trans
      have hb : |inner ℝ (u-w) (y-x)| ≤ τ*(2*M) :=
        (abs_real_inner_le_norm _ _).trans
          (mul_le_mul hw hxy (norm_nonneg _) ((norm_nonneg _).trans hw))
      linarith only [hb,hwi]
    rcases (min_le_iff.mp hτ) with h | h
    · exact helper v h hvxy
    · apply helper (-v) (by simpa only [sub_neg_eq_add] using h)
      simpa only [inner_neg_left,abs_neg] using hvxy
  have he : inner ℝ u y-a = inner ℝ u (y-x)+(inner ℝ u x-a) := by
    rw [inner_sub_right]; ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith only [huxy,hux])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalSeparation
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Separation of unoriented normals controls their transverse component -/

namespace Falconer
variable {d : ℕ}

theorem normalDistance_le_perpendicular {u v : Space d}
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    normalDistance u v ≤ 2*‖perpendicularPart u v‖ := by
  by_cases h : 0 ≤ inner ℝ u v
  · exact (min_le_left _ _).trans (unit_close_of_perpendicular hu hv h)
  · have hneg : 0 ≤ inner ℝ u (-v) := by
      rw [inner_neg_right]
      linarith only [h]
    have hn : ‖-v‖ = 1 := by simpa only [norm_neg] using hv
    have hh := unit_close_of_perpendicular hu hn hneg
    have he : perpendicularPart u (-v) = -(perpendicularPart u v) := by
      simp only [perpendicularPart,inner_neg_right,neg_smul]
      abel
    rw [he,norm_neg,sub_neg_eq_add] at hh
    exact (min_le_right _ _).trans hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoNormalProjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The codimension-two plane orthogonal to two orthonormal directions -/

namespace Falconer
open Set Submodule
open scoped BigOperators
variable {d : ℕ}

theorem orthonormal_pair_complement (v : Fin 2 → Space d) (hv : Orthonormal ℝ v) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∀ z : Space d, ‖Vᗮ.starProjection z‖ ≤ |inner ℝ (v 0) z|+|inner ℝ (v 1) z| := by
  classical
  let W := Submodule.span ℝ (Set.range v)
  refine ⟨Wᗮ,?_,?_⟩
  · have hdim : Module.finrank ℝ W = 2 := by
      simpa only [Fintype.card_fin] using finrank_span_eq_card hv.linearIndependent
    have hd := W.finrank_add_finrank_orthogonal
    rw [hdim] at hd
    simp only [finrank_euclideanSpace_fin] at hd
    omega
  · intro z
    let p := ∑ i : Fin 2, inner ℝ (v i) z • v i
    have hp : p ∈ W := Submodule.sum_mem _ (fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i)))
    have hpinner (i : Fin 2) : inner ℝ p (v i) = inner ℝ z (v i) := by
      calc
        _ = inner ℝ (v i) p := real_inner_comm _ _
        _ = inner ℝ (v i) z := hv.inner_right_fintype (fun j => inner ℝ (v j) z) i
        _ = _ := real_inner_comm _ _
    have he : W.starProjection z = p := by
      apply W.eq_starProjection_of_mem_of_inner_eq_zero hp
      intro w hw
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨i,rfl⟩ := hw
        rw [inner_sub_left,hpinner,sub_self]
      | zero => simp
      | add x y _ _ hx hy => simp only [inner_add_right,hx,hy,add_zero]
      | smul a x _ hx => simp only [inner_smul_right,hx,mul_zero]
    simp only [Submodule.orthogonal_orthogonal]
    rw [he]
    calc
      _ ≤ ∑ i : Fin 2, ‖inner ℝ (v i) z • v i‖ := norm_sum_le _ _
      _ = _ := by simp [norm_smul,hv.norm_eq_one,Fin.sum_univ_two]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TripleGridRounding
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Rounding bounded physical point sets in transverse coordinates -/

namespace Falconer
open Set Metric

theorem round_mesh_error {δ : ℝ} (hδ : 0 < δ) (t : ℝ) :
    |t-δ*(round (t/δ):ℝ)| ≤ δ/2 := by
  have he : t-δ*(round (t/δ):ℝ) = δ*(t/δ-(round (t/δ):ℝ)) := by field_simp
  rw [he,abs_mul,abs_of_pos hδ]
  have hh := mul_le_mul_of_nonneg_left (abs_sub_round (t/δ)) hδ.le
  nlinarith

theorem round_bound {δ R : ℝ} (hδ : 0 < δ) (L : ℕ) (hL : R/δ+1 ≤ (L:ℝ))
    (t : ℝ) (ht : |t| ≤ R) : -(L:ℤ) ≤ round (t/δ) ∧ round (t/δ) ≤ (L:ℤ) := by
  have hh : |(round (t/δ):ℝ)| ≤ (L:ℝ) := by
    have hs := abs_sub_round (t/δ)
    have htri := abs_sub_le (round (t/δ):ℝ) (t/δ) 0
    rw [sub_zero,sub_zero,abs_sub_comm (round (t/δ):ℝ)] at htri
    have hd : |t/δ| ≤ R/δ := by
      rw [abs_div,abs_of_pos hδ]
      exact div_le_div_of_nonneg_right ht hδ.le
    linarith
  have hi : |round (t/δ)| ≤ (L:ℤ) := by exact_mod_cast hh
  exact abs_le.mp hi

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_SimilarityMeasures
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Original measure and radial-cap transport under a common similarity -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

variable {d : ℕ}

@[simp] theorem pairHomeomorph_mem_image (f : Space d ≃ₜ Space d)
    (G : Set (Space d × Space d)) (x y : Space d) :
    (f x,f y) ∈ pairHomeomorph f '' G ↔ (x,y) ∈ G :=
  (pairHomeomorph f).injective.mem_set_image (s := G) (a := (x,y))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LoomisWhitneyCoordinates
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite coordinate splitting for the Loomis–Whitney induction -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem sum_tuple_cons {n : ℕ} (f : (Fin (n+1) → X) → ℝ) :
    (∑ z, f z) = ∑ x, ∑ y : Fin n → X, f (Fin.cons x y) := by
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => X)).sum_comp f]
  exact Fintype.sum_prod_type _

omit [Fintype X] in
theorem finite_holder_two_successor {n : ℕ} (B : Finset X) (f g : X → ℝ)
    (hf : ∀ x ∈ B, 0 ≤ f x) (hg : ∀ x ∈ B, 0 ≤ g x) :
    (∑ x ∈ B, (f x)^(1/((n+1:ℕ):ℝ))*(g x)^((n:ℝ)/(n+1:ℕ))) ≤
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
  classical
  let h : Fin (n+1) → X → ℝ := Fin.cases f (fun _ => g)
  have hh : ∀ i ∈ (Finset.univ : Finset (Fin (n+1))), ∀ x ∈ B, 0 ≤ h i x := by
    intro i _ x hx
    refine Fin.cases (hf x hx) (fun _ => hg x hx) i
  have hc := finite_holder_equal Finset.univ B (by simp) h hh
  have hp (u v : ℝ) (hv : 0 ≤ v) :
      (∏ i : Fin (n+1), (Fin.cases u (fun _ => v) i)^(1/((n+1:ℕ):ℝ))) =
        u^(1/((n+1:ℕ):ℝ))*v^((n:ℝ)/(n+1:ℕ)) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cases_zero,Fin.cases_succ,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [← Real.rpow_mul_natCast hv]
    congr 2
    push_cast
    ring
  have hleft : (∑ x ∈ B, ∏ i : Fin (n+1), h i x^(1/((n+1:ℕ):ℝ))) =
      ∑ x ∈ B, f x^(1/((n+1:ℕ):ℝ))*g x^((n:ℝ)/(n+1:ℕ)) := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hp (f x) (g x) (hg x hx)]
    apply Finset.prod_congr rfl
    intro i _
    refine Fin.cases rfl (fun _ => rfl) i
  have hright : (∏ i : Fin (n+1), (∑ x ∈ B, h i x)^(1/((n+1:ℕ):ℝ))) =
      (∑ x ∈ B, f x)^(1/((n+1:ℕ):ℝ))*(∑ x ∈ B, g x)^((n:ℝ)/(n+1:ℕ)) := by
    have he : (fun i : Fin (n+1) => ∑ x ∈ B, h i x) =
        Fin.cases (∑ x ∈ B, f x) (fun _ => ∑ x ∈ B, g x) := by
      funext i
      refine Fin.cases rfl (fun _ => rfl) i
    change (∏ i : Fin (n+1), ((fun i => ∑ x ∈ B, h i x) i)^(1/((n+1:ℕ):ℝ))) = _
    rw [he]
    exact hp _ _ (Finset.sum_nonneg hg)
  simpa only [Finset.card_univ,Fintype.card_fin,hleft,hright] using hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite weighted Loomis–Whitney induction step -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finite_root_product_raise {ι : Type*} (I : Finset ι) {n : ℕ} (hn : 0 < n)
    (b : ι → ℝ) (hb : ∀ i ∈ I, 0 ≤ b i) :
    (∏ i ∈ I, (b i)^(1/(n:ℝ)))^((n:ℝ)/((n+1:ℕ):ℝ)) =
      ∏ i ∈ I, (b i)^(1/((n+1:ℕ):ℝ)) := by
  rw [← Real.finsetProd_rpow I _ (fun i hi => Real.rpow_nonneg (hb i hi) _) _]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← Real.rpow_mul (hb i hi)]
  congr 1
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem finite_weighted_loomis_step {n : ℕ} (hn : 0 < n)
    (ih : FiniteWeightedLoomis n X) : FiniteWeightedLoomis (n+1) X := by
  classical
  intro f hf
  let g : Fin (n+1) → (Fin n → X) → ℝ := fun i y => ∑ x : X, f i.succ (Fin.cons x y)
  have hg : ∀ i y, 0 ≤ g i y := fun i y => Finset.sum_nonneg (fun x _ => hf _ _)
  let H : (Fin (n+1) → X) → ℝ := fun y => ∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^(1/(n:ℝ))
  have hH : ∀ y, 0 ≤ H y := fun y => Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hg _ _) _)
  let p : ℝ := 1/((n+1:ℕ):ℝ)
  let q : ℝ := (n:ℝ)/((n+1:ℕ):ℝ)
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hh : (∑ y, H y) ≤ ∏ i : Fin (n+1), (∑ z, g i z)^(1/(n:ℝ)) := ih g hg
  have hfirst :
      (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
        ∑ y : Fin (n+1) → X, (f 0 y)^p*(H y)^q := by
    rw [sum_tuple_cons,Finset.sum_comm]
    apply Finset.sum_le_sum
    intro y _
    have he : (∑ x : X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i (Fin.cons x y)))^p) =
        (f 0 y)^p*(∑ x : X, ∏ i : Fin (n+1), (f i.succ (Fin.cons x (eraseFinCoordinate i y)))^p) := by
      simp only [Fin.prod_univ_succ,remove_coordinate_cons_zero,remove_coordinate_cons_succ,
        Finset.mul_sum]
    rw [he]
    have hc := finite_holder_equal (Finset.univ : Finset (Fin (n+1)))
      (Finset.univ : Finset X) (by simp)
      (fun i x => f i.succ (Fin.cons x (eraseFinCoordinate i y))) (fun i _ x _ => hf _ _)
    have hr : (∏ i : Fin (n+1), (g i (eraseFinCoordinate i y))^p) = (H y)^q :=
      (finite_root_product_raise Finset.univ hn _ (fun i _ => hg _ _)).symm
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (hf _ _) _)
    rw [← hr]
    simpa only [Finset.card_univ,Fintype.card_fin,p,g] using hc
  have houter := finite_holder_two_successor (n := n) (Finset.univ : Finset (Fin (n+1) → X))
    (f 0) H (fun y _ => hf _ _) (fun y _ => hH y)
  have hraise := Real.rpow_le_rpow (Finset.sum_nonneg (fun y _ => hH y)) hh hq
  have hgSum (i : Fin (n+1)) : (∑ z : Fin n → X, g i z) = ∑ y : Fin (n+1) → X, f i.succ y := by
    rw [sum_tuple_cons]
    exact Finset.sum_comm
  have hraise' : (∑ y, H y)^q ≤ ∏ i : Fin (n+1), (∑ y, f i.succ y)^p := by
    apply hraise.trans_eq
    rw [finite_root_product_raise Finset.univ hn _ (fun i _ => Finset.sum_nonneg (fun y _ => hg _ _))]
    apply Finset.prod_congr rfl
    intro i _
    rw [hgSum]
  change (∑ z : Fin (n+2) → X, ∏ i : Fin (n+2), (f i (eraseFinCoordinate i z))^p) ≤
    ∏ i : Fin (n+2), (∑ y : Fin (n+1) → X, f i y)^p
  apply hfirst.trans
  apply houter.trans
  rw [Fin.prod_univ_succ]
  exact mul_le_mul_of_nonneg_left hraise' (Real.rpow_nonneg (Finset.sum_nonneg (fun y _ => hf _ _)) _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_WeightedLoomisBase
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Base and induction for the finite weighted projection inequality -/
namespace Falconer
open scoped BigOperators

variable {X : Type*} [Fintype X]

theorem finite_weighted_loomis_one : FiniteWeightedLoomis 1 X := by
  classical
  intro f _hf
  simp only [Nat.cast_one,div_one,Real.rpow_one]
  change (∑ z : Fin 2 → X, ∏ i : Fin 2, f i (eraseFinCoordinate i z)) ≤
    ∏ i : Fin 2, ∑ y : Fin 1 → X, f i y
  simp only [Fin.prod_univ_two]
  have he : (∑ z : Fin 2 → X, f 0 (eraseFinCoordinate 0 z)*f 1 (eraseFinCoordinate 1 z)) =
      ∑ w : (Fin 1 → X) × (Fin 1 → X), f 0 w.1*f 1 w.2 := by
    rw [← (twoCoordinateEquiv (X := X)).symm.sum_comp]
    apply Finset.sum_congr rfl
    intro w _
    have hh := (twoCoordinateEquiv (X := X)).apply_symm_apply w
    exact congrArg (fun z : (Fin 1 → X) × (Fin 1 → X) => f 0 z.1*f 1 z.2) hh
  rw [he,Fintype.sum_prod_type]
  exact le_of_eq (by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro y _; rw [Finset.mul_sum])

theorem finite_weighted_loomis_whitney (n : ℕ) (hn : 1 ≤ n) : FiniteWeightedLoomis n X := by
  induction n,hn using Nat.le_induction with
  | base => exact finite_weighted_loomis_one
  | succ n hn ih => exact finite_weighted_loomis_step (by omega) ih

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteLatticeLoomis
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The finite lattice Loomis–Whitney inequality used in the manuscript -/
namespace Falconer
open scoped BigOperators

theorem finite_loomis_whitney_card {X : Type*} [Fintype X] [DecidableEq X]
    (n : ℕ) (hn : 1 ≤ n) (S : Finset (Fin (n+1) → X)) :
    S.card^n ≤ ∏ i : Fin (n+1), (S.image (eraseFinCoordinate i)).card := by
  classical
  let f : Fin (n+1) → (Fin n → X) → ℝ := fun i y =>
    if y ∈ S.image (eraseFinCoordinate i) then 1 else 0
  have hf : ∀ i y, 0 ≤ f i y := by intro i y; dsimp [f]; positivity
  have hpoint : ∀ z : Fin (n+1) → X,
      (if z ∈ S then (1:ℝ) else 0) ≤ ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) := by
    intro z
    by_cases hz : z ∈ S
    · have hm : ∀ i : Fin (n+1), eraseFinCoordinate i z ∈ S.image (eraseFinCoordinate i) :=
        fun i => Finset.mem_image.mpr ⟨z,hz,rfl⟩
      simp only [hz,ite_true, if_true,f,hm,Real.one_rpow,Finset.prod_const_one,le_refl]
    · simp only [hz,ite_false, if_false]
      exact Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hf _ _) _)
  have hcount : (S.card:ℝ) ≤
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)) := by
    calc
      _ = ∑ z : Fin (n+1) → X, if z ∈ S then (1:ℝ) else 0 := by simp
      _ ≤ ∑ z : Fin (n+1) → X, ∏ i : Fin (n+1), (f i (eraseFinCoordinate i z))^(1/(n:ℝ)) :=
        Finset.sum_le_sum (fun z _ => hpoint z)
      _ ≤ ∏ i : Fin (n+1), (∑ y : Fin n → X, f i y)^(1/(n:ℝ)) :=
        finite_weighted_loomis_whitney n hn f hf
      _ = _ := by
        apply Finset.prod_congr rfl
        intro i _
        congr 1
        change (∑ y : Fin n → X, if y ∈ S.image (eraseFinCoordinate i) then (1:ℝ) else 0) = _
        simp only [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.univ_inter]
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg S.card) hcount n
  have hright : (∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ)^(1/(n:ℝ)))^n =
      ∏ i : Fin (n+1), ((S.image (eraseFinCoordinate i)).card:ℝ) := by
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro i _
    rw [one_div]
    exact Real.rpow_inv_natCast_pow (Nat.cast_nonneg _) (by omega)
  rw [hright] at hpower
  exact_mod_cast hpower

theorem published_finite_loomis_whitney : PublishedFiniteLoomisWhitney := by
  classical
  intro n hn S
  let A : Finset ℤ := S.biUnion (fun z => Finset.univ.image z)
  have hA : ∀ z ∈ S, ∀ i : Fin (n+1), z i ∈ A := by
    intro z hz i
    exact Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩⟩
  let lift : {z // z ∈ S} → (Fin (n+1) → A) := fun z i => ⟨z.val i,hA z.val z.property i⟩
  let T := S.attach.image lift
  have hlift : Function.Injective lift := by
    intro z w he
    apply Subtype.ext
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hcard : T.card = S.card := by
    dsimp only [T]
    rw [Finset.card_image_of_injective _ hlift,Finset.card_attach]
  have hproj : ∀ i : Fin (n+1), (T.image (eraseFinCoordinate i)).card =
      (S.image (dropGridCoordinate i)).card := by
    intro i
    let lower : (Fin n → A) → (Fin n → ℤ) := fun z j => (z j).val
    have hlower : Function.Injective lower := by
      intro z w he
      funext j
      exact Subtype.ext (congrFun he j)
    rw [← Finset.card_image_of_injective _ hlower]
    congr 1
    dsimp only [T]
    rw [Finset.image_image,Finset.image_image]
    change S.attach.image (fun z => dropGridCoordinate i z.val) = _
    calc
      _ = (S.attach.image Subtype.val).image (dropGridCoordinate i) :=
        (Finset.image_image (s := S.attach) (f := Subtype.val) (g := dropGridCoordinate i)).symm
      _ = _ := by rw [Finset.attach_image_val]
  have hh := finite_loomis_whitney_card n hn T
  rw [hcard] at hh
  simpa only [hproj] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SixInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Removing the classical-threshold input by strict dimension descent

The charged affine plane has smaller dimension than the original space.
Its distance conclusion therefore follows from the induction hypothesis.
The planar base case and the higher-dimensional analytic proof stay separate.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem mainTarget_of_six_published_inputs
    (hPlanar : PlanarFalconer.PublishedPlanarRadialMoment)
    (hFrostman : PublishedFrostmanAboveHalf)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro hd E hE hDim
    have hmain : ∀ k : ℕ, k < d → 2 ≤ k → ∀ K : Set (Space k), IsCompact K →
        (k : ℝ≥0∞)/2 < dimH K → 0 < volume (distanceSet K) := by
      intro k hk
      exact ih k hk
    by_cases htwo : d = 2
    · subst d
      have he : (2 : ℝ≥0∞)/2 = 1 := ENNReal.div_self (by norm_num) (by norm_num)
      have hh : (1 : ℝ≥0∞) < dimH E := by simpa only [Nat.cast_ofNat,he] using hDim
      exact planar_case_of_published_radial hPlanar E hE hh
    · obtain ⟨m,rfl⟩ : ∃ m : ℕ, d = m+3 := ⟨d-3,by omega⟩
      rcases prepared_pair_of_lower_dimensions hFrostman hRadial hHeavy hFurstenberg
        published_finite_loomis_whitney hmain hd E hE hDim
        (by norm_num : (0:ℝ) < 1/8) with hpos | hp
      · exact hpos
      · obtain ⟨p⟩ := hp
        exact prepared_pair_positive_distance published_gnomonic_surface hQuadratic m E hE p

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_PlanarRadialDischarge
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The planar radial moment for compact disjoint supports

The finite-energy radial projection estimate specializes to compact,
disjoint supports with the same circle measure.
-/
namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal

theorem published_planar_radial_moment : PublishedPlanarRadialMoment := by
  intro α β δ hδ hδ1 hα hβ hsep hEα hEβ
  obtain ⟨hs1,hs2,hp1,hp2,_ht0,hupt,htp,_hsδ,_htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  exact finite_radial_Lp_integral (α : Measure Plane) (β : Measure Plane)
    hα hβ hsep (α : Measure Plane).support_mem_ae (β : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa only [mul_comm] using hupt) htp hEα hEβ

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FiveInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main theorem after three proved inputs and dimension descent -/
namespace Falconer

theorem mainTarget_of_five_published_inputs
    (hFrostman : PublishedFrostmanAboveHalf)
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_six_published_inputs PlanarFalconer.published_planar_radial_moment
    hFrostman hRadial hHeavy hFurstenberg hQuadratic

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CubeBallPacking
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A ball meets a bounded number of dyadic cubes of comparable side -/
namespace Falconer
open Set Metric

theorem mem_cubeBallHits {d : ℕ} (Q : DyadicCube d) (n : ℕ)
    (x : Space d) (r : ℝ) (p : List (Fin d → Bool)) :
    p ∈ cubeBallHits Q n x r ↔ p.length = n ∧
      ((Q.descendant p).carrier ∩ ball x r).Nonempty := by
  classical
  simp [cubeBallHits]

theorem cubeBallHits_coordinate_bound {d n : ℕ} (Q : DyadicCube d)
    (hQ : 0 < Q.side) (x : Space d) {r : ℝ}
    (hr : r ≤ Q.side/(2:ℝ)^n) {p q : List (Fin d → Bool)}
    (hp : p ∈ cubeBallHits Q n x r) (hq : q ∈ cubeBallHits Q n x r) (i : Fin d) :
    |dyadicCode p i - dyadicCode q i| ≤ (3 : ℤ) := by
  obtain ⟨hp, u, hu, hux⟩ := (mem_cubeBallHits Q n x r p).mp hp
  obtain ⟨hq, v, hv, hvx⟩ := (mem_cubeBallHits Q n x r q).mp hq
  have hui := hu i
  have hvi := hv i
  rw [Q.descendant_origin,Q.descendant_side,hp] at hui
  rw [Q.descendant_origin,Q.descendant_side,hq] at hvi
  have huv : |u i-v i| ≤ 2*r := by
    have hb : dist u v < 2*r :=
      (dist_triangle u x v).trans_lt (by
        rw [dist_comm x v]
        linarith [mem_ball.mp hux,mem_ball.mp hvx])
    exact (PiLp.norm_apply_le (u-v) i).trans (by simpa only [dist_eq_norm] using hb.le)
  have ht : 0 < Q.side/(2:ℝ)^n := by positivity
  have hh : |(dyadicCode p i:ℝ)-(dyadicCode q i:ℝ)| ≤ 3 := by
    rw [abs_le] at huv ⊢
    constructor <;> nlinarith
  exact_mod_cast hh

theorem cubeBallHits_card {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (n : ℕ) (x : Space d) {r : ℝ} (hr : r ≤ Q.side/(2:ℝ)^n) :
    (cubeBallHits Q n x r).card ≤ 7^d := by
  classical
  let S := cubeBallHits Q n x r
  change S.card ≤ 7^d
  by_cases hS : S.Nonempty
  · obtain ⟨p₀,hp₀⟩ := hS
    have hinj : Set.InjOn dyadicCode (S : Set (List (Fin d → Bool))) := by
      intro p hp q hq hpq
      exact dyadicCode_injective_at_depth
        ((mem_cubeBallHits Q n x r p).mp hp).1
        ((mem_cubeBallHits Q n x r q).mp hq).1 hpq
    have hc : (S.image dyadicCode).card = S.card := Finset.card_image_iff.mpr hinj
    rw [← hc]
    exact grid_box_card (L := 3) (S.image dyadicCode) (dyadicCode p₀) (by
      intro z hz i
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
      exact cubeBallHits_coordinate_bound Q hQ x hr hp hp₀ i)
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.card_empty]
    exact Nat.zero_le _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_CubeMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite Frostman measures from dyadic cube capacities -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem split_cube_budget {d : ℕ} (c : (Fin d → Bool) → ℝ)
    (hc : ∀ b, 0 ≤ c b) {m : ℝ} (hm : 0 ≤ m) (hmc : m ≤ ∑ b, c b) :
    ∃ v : (Fin d → Bool) → ℝ, (∀ b, 0 ≤ v b ∧ v b ≤ c b) ∧ ∑ b, v b = m := by
  classical
  let S := ∑ b, c b
  have hS : 0 ≤ S := Finset.sum_nonneg fun b _ => hc b
  by_cases hzero : S = 0
  · have hm0 : m = 0 := le_antisymm (hmc.trans_eq hzero) hm
    exact ⟨fun _ => 0,fun b => ⟨le_rfl,hc b⟩,by simp [hm0]⟩
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    have hfrac : m/S ≤ 1 := (div_le_one hpos).mpr hmc
    refine ⟨fun b => (m/S)*c b,fun b => ⟨mul_nonneg (div_nonneg hm hS) (hc b),?_⟩,?_⟩
    · simpa using mul_le_mul_of_nonneg_right hfrac (hc b)
    · rw [← Finset.mul_sum]
      exact div_mul_cancel₀ m hzero

theorem finite_cube_measure {d : ℕ} (E : Set (Space d)) (s : ℝ)
    (Q : DyadicCube d) (hQ : 0 < Q.side) (K : ℕ)
    (m : ℝ) (hm : 0 ≤ m) (hcap : m ≤ cubeCapacity E s Q K) :
    ∃ μ : Measure (Space d), μ univ = ENNReal.ofReal m ∧
      μ (E ∩ Q.carrier)ᶜ = 0 ∧
      ∀ p : List (Fin d → Bool), p.length ≤ K →
        μ (Q.descendant p).carrier ≤ ENNReal.ofReal ((Q.descendant p).side^s) := by
  classical
  induction K generalizing Q m with
  | zero =>
    by_cases h : (E ∩ Q.carrier).Nonempty
    · obtain ⟨x,hx⟩ := h
      refine ⟨ENNReal.ofReal m • Measure.dirac x,by simp,?_,?_⟩
      · simp [Measure.smul_apply,hx]
      · intro p hp
        have hp0 : p = [] := by cases p <;> simp_all
        subst p
        have hb : m ≤ Q.side^s := hcap.trans (cubeOccupied_le E s Q hQ.le)
        simpa [Measure.smul_apply,Measure.dirac_apply' _ Q.measurable,hx.2] using
          ENNReal.ofReal_le_ofReal hb
    · have hm0 : m = 0 := by
        have hb : m ≤ 0 := by simpa [cubeCapacity,cubeOccupied,h] using hcap
        exact le_antisymm hb hm
      refine ⟨0,by simp [hm0],by simp,?_⟩
      intro p hp
      simp
  | succ K ih =>
    have hsum : m ≤ ∑ b : Fin d → Bool, cubeCapacity E s (Q.child b) K :=
      hcap.trans (min_le_right _ _)
    obtain ⟨v,hv,hvsum⟩ := split_cube_budget (fun b => cubeCapacity E s (Q.child b) K)
      (fun b => cubeCapacity_nonneg E s (Q.child b) (by change 0 ≤ Q.side/2; positivity) K) hm hsum
    have hex (b : Fin d → Bool) :=
      ih (Q.child b) (by change 0 < Q.side/2; positivity) (v b) (hv b).1 (hv b).2
    choose μ hmass hcarry hbounds using hex
    have hchild (b : Fin d → Bool) : μ b (Q.child b).carrierᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_right) (hcarry b)
    have hparent (b : Fin d → Bool) : μ b (E ∩ Q.carrier)ᶜ = 0 :=
      measure_mono_null
        (compl_subset_compl.mpr (inter_subset_inter_right E (Q.child_subset b))) (hcarry b)
    refine ⟨∑ b, μ b,?_,?_,?_⟩
    · simp only [Measure.finsetSum_apply,hmass]
      rw [← ofReal_finset_sum_nonneg _ _ (fun b _ => (hv b).1),hvsum]
    · simp only [Measure.finsetSum_apply,hparent,Finset.sum_const_zero]
    · intro p hp
      cases p with
      | nil =>
        apply (measure_mono (subset_univ _)).trans
        simp only [Measure.finsetSum_apply,hmass]
        rw [← ofReal_finset_sum_nonneg _ _ (fun b _ => (hv b).1),hvsum]
        exact ENNReal.ofReal_le_ofReal
          (hcap.trans ((cubeCapacity_le_occupied E s Q (K+1)).trans (cubeOccupied_le E s Q hQ.le)))
      | cons b p =>
        change (∑ c, μ c) ((Q.child b).descendant p).carrier ≤ _
        rw [Measure.finsetSum_apply,Finset.sum_eq_single b]
        · exact hbounds b p (by simpa using Nat.le_of_succ_le_succ hp)
        · intro c _ hcb
          apply measure_mono_null _ (hchild c)
          intro x hx hxc
          exact Set.disjoint_left.mp (Q.children_disjoint (Ne.symm hcb))
            ((Q.child b).descendant_subset p hx) hxc
        · simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_CubeProbability
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Probability approximants with uniform dyadic Frostman bounds -/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem exists_containing_cube {d : ℕ} (E : Set (Space d)) (hE : IsCompact E) :
    ∃ Q : DyadicCube d, 0 < Q.side ∧ E ⊆ Q.carrier := by
  obtain ⟨R,hR,hbound⟩ := hE.isBounded.exists_pos_norm_lt
  let Q : DyadicCube d := ⟨WithLp.toLp 2 (fun _ => -R),2*R⟩
  refine ⟨Q,by dsimp [Q]; positivity,?_⟩
  intro x hx i
  have hi : |x i| < R := (PiLp.norm_apply_le x i).trans_lt (hbound x hx)
  obtain ⟨hlo,hhi⟩ := abs_lt.mp hi
  change -R ≤ x i ∧ x i < -R+2*R
  exact ⟨hlo.le,by linarith⟩

theorem cube_probability_sequence {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0} (hs : 0 < s)
    (hDim : (s : ℝ≥0∞) < dimH E) (Q : DyadicCube d)
    (hQ : 0 < Q.side) (hEQ : E ⊆ Q.carrier) :
    ∃ c : ℝ, 0 < c ∧ ∃ μ : ℕ → ProbabilityMeasure (Space d),
      ∀ K, (μ K : Measure (Space d)) Eᶜ = 0 ∧
        ∀ p : List (Fin d → Bool), p.length ≤ K →
          (μ K : Measure (Space d)) (Q.descendant p).carrier ≤
            ENNReal.ofReal (c⁻¹*(Q.descendant p).side^(s:ℝ)) := by
  classical
  obtain ⟨c,hc,hcaps⟩ := exists_uniform_cube_capacity hd E hE hs hDim Q hQ hEQ
  choose ν hmass hcarry hbound using fun K =>
    finite_cube_measure E (s:ℝ) Q hQ K c hc.le (hcaps K)
  have hprob (K : ℕ) : IsProbabilityMeasure (ENNReal.ofReal c⁻¹ • ν K) := by
    constructor
    rw [Measure.smul_apply,smul_eq_mul,hmass K,← ENNReal.ofReal_mul (by positivity),
      inv_mul_cancel₀ hc.ne',ENNReal.ofReal_one]
  let μ : ℕ → ProbabilityMeasure (Space d) := fun K => ⟨ENNReal.ofReal c⁻¹ • ν K,hprob K⟩
  refine ⟨c,hc,μ,fun K => ⟨?_,?_⟩⟩
  · have hz : ν K Eᶜ = 0 :=
      measure_mono_null (compl_subset_compl.mpr inter_subset_left) (hcarry K)
    simp [μ,Measure.smul_apply,hz]
  · intro p hp
    change (ENNReal.ofReal c⁻¹ • ν K) _ ≤ _
    rw [Measure.smul_apply,smul_eq_mul,ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_right (hbound K p hp) _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_CubeBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Uniform Frostman ball bounds for the finite cube approximants -/
namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem cube_ball_measure_le {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    (μ : Measure (Space d)) (hcarry : μ Q.carrierᶜ = 0)
    (s C : ℝ) (_hC : 0 ≤ C) (n : ℕ)
    (hb : ∀ p : List (Fin d → Bool), p.length = n →
      μ (Q.descendant p).carrier ≤ ENNReal.ofReal (C*(Q.descendant p).side^s))
    (x : Space d) {r : ℝ} (hr : r ≤ Q.side/(2:ℝ)^n) :
    μ (ball x r) ≤ ENNReal.ofReal ((7:ℝ)^d*C*(Q.side/(2:ℝ)^n)^s) := by
  classical
  let S := cubeBallHits Q n x r
  have hcover : ball x r ⊆ (⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ := by
    intro z hz
    by_cases hQz : z ∈ Q.carrier
    · obtain ⟨p,hp,hzp⟩ := Q.mem_descendant_at_depth n hQz
      exact Or.inl (mem_iUnion₂.mpr ⟨p,(mem_cubeBallHits Q n x r p).mpr
        ⟨(mem_cubePaths d n p).mp hp,⟨z,hzp,hz⟩⟩,hzp⟩)
    · exact Or.inr hQz
  calc
    μ (ball x r) ≤ μ ((⋃ p ∈ S, (Q.descendant p).carrier) ∪ Q.carrierᶜ) := measure_mono hcover
    _ ≤ μ (⋃ p ∈ S, (Q.descendant p).carrier)+μ Q.carrierᶜ := measure_union_le _ _
    _ = μ (⋃ p ∈ S, (Q.descendant p).carrier) := by rw [hcarry,add_zero]
    _ ≤ ∑ p ∈ S, μ (Q.descendant p).carrier := measure_biUnion_finset_le _ _
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C*(Q.side/(2:ℝ)^n)^s) := by
      apply Finset.sum_le_sum
      intro p hp
      have hl := ((mem_cubeBallHits Q n x r p).mp hp).1
      simpa only [Q.descendant_side,hl] using hb p hl
    _ ≤ (7^d:ℕ)*ENNReal.ofReal (C*(Q.side/(2:ℝ)^n)^s) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      exact mul_le_mul_left (by exact_mod_cast cubeBallHits_card Q hQ n x hr) _
    _ = _ := by
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
      congr 1
      push_cast
      ring

theorem eventual_cube_ball_bounds {d : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hcarry : ∀ K, (μ K : Measure (Space d)) Q.carrierᶜ = 0)
    (hb : ∀ K, ∀ p : List (Fin d → Bool), p.length ≤ K →
      (μ K : Measure (Space d)) (Q.descendant p).carrier ≤
        ENNReal.ofReal (c⁻¹*(Q.descendant p).side^s)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Space d, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure (Space d)) (ball x r) ≤ ENNReal.ofReal (C*r^s) := by
  let C := max ((7:ℝ)^d*c⁻¹*(2:ℝ)^s) (Q.side^s)⁻¹
  have hside : 0 < Q.side^s := Real.rpow_pos_of_pos hQ s
  have hC : 0 < C := (inv_pos.mpr hside).trans_le (le_max_right _ _)
  refine ⟨C,hC,fun x r hr => ?_⟩
  by_cases hrQ : r ≤ Q.side
  · obtain ⟨n,hrn,hnr⟩ := PlanarFalconer.exists_dyadic_scale hQ hr hrQ
    filter_upwards [eventually_ge_atTop n] with K hK
    have hball := cube_ball_measure_le Q hQ (μ K) (hcarry K) s c⁻¹
      (by positivity) n (fun p hp => hb K p (hp ▸ hK)) x hrn
    apply hball.trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := Real.rpow_le_rpow (by positivity : 0 ≤ Q.side/(2:ℝ)^n) hnr.le hs.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hr.le] at hp
    calc
      (7:ℝ)^d*c⁻¹*(Q.side/(2:ℝ)^n)^s ≤ (7:ℝ)^d*c⁻¹*((2:ℝ)^s*r^s) :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ = ((7:ℝ)^d*c⁻¹*(2:ℝ)^s)*r^s := by ring
      _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  · apply Filter.Eventually.of_forall
    intro K
    have hpow := Real.rpow_le_rpow hQ.le (le_of_not_ge hrQ) hs.le
    have hlarge : 1 ≤ C*r^s := by
      calc
        1 = (Q.side^s)⁻¹*Q.side^s := (inv_mul_cancel₀ hside.ne').symm
        _ ≤ (Q.side^s)⁻¹*r^s := mul_le_mul_of_nonneg_left hpow (by positivity)
        _ ≤ C*r^s := mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
    calc
      (μ K : Measure (Space d)) (ball x r) ≤ (μ K : Measure (Space d)) univ :=
        measure_mono (subset_univ _)
      _ = 1 := measure_univ
      _ ≤ ENNReal.ofReal (C*r^s) := by
        simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hlarge

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrostmanWeakLimit
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Compact weak limits preserve the required Frostman ball bounds -/
namespace Falconer
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology

theorem compact_carried_probabilities {d : ℕ} (E : Set (Space d)) (hE : IsCompact E) :
    IsCompact {μ : ProbabilityMeasure (Space d) | (μ : Measure (Space d)) Eᶜ = 0} := by
  have h := isCompact_setOfPred_probabilityMeasure_mass_eq_compl_isCompact_le
    (u := fun _ => 0) (K := fun _ => E) tendsto_const_nhds (fun _ => hE)
    (Or.inr monotone_const)
  simpa only [le_zero_iff,forall_const,ProbabilityMeasure.null_iff_toMeasure_null] using h

theorem exists_carried_weak_subsequence {d : ℕ} (E : Set (Space d)) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hμ : ∀ K, (μ K : Measure (Space d)) Eᶜ = 0) :
    ∃ ν : ProbabilityMeasure (Space d), (ν : Measure (Space d)) Eᶜ = 0 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (μ ∘ φ) atTop (𝓝 ν) :=
  (compact_carried_probabilities E hE).tendsto_subseq hμ

theorem frostman_of_eventual_ball_bounds {d : ℕ} (E : Set (Space d)) (hE : IsCompact E)
    (μ : ℕ → ProbabilityMeasure (Space d))
    (hμ : ∀ K, (μ K : Measure (Space d)) Eᶜ = 0) (s C : ℝ)
    (hbound : ∀ x : Space d, ∀ r > 0, ∀ᶠ K in atTop,
      (μ K : Measure (Space d)) (ball x r) ≤ ENNReal.ofReal (C*r^s)) :
    ∃ ν : ProbabilityMeasure (Space d), (ν : Measure (Space d)) Eᶜ = 0 ∧
      FrostmanBallBound (ν : Measure (Space d)) s C := by
  obtain ⟨ν,hν,φ,hφ,hlim⟩ := exists_carried_weak_subsequence E hE μ hμ
  refine ⟨ν,hν,fun x r hr => ?_⟩
  apply (ProbabilityMeasure.le_liminf_measure_open_of_tendsto hlim
    (G := ball x r) isOpen_ball).trans
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hb := hφt.eventually (hbound x r hr)
  exact (liminf_le_liminf hb).trans_eq (liminf_const _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Measures_FrostmanDischarge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The application-level Frostman input proved in every ambient dimension

Finite dyadic capacities give probability approximants carried by the compact
set. The finite cube count gives uniform ball bounds; a compact weak limit
preserves them. Only exponents strictly above half the dimension are selected
in the published-input discharge.
-/
namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal NNReal

theorem frostman_probability {d : ℕ} (hd : 1 ≤ d)
    (E : Set (Space d)) (hE : IsCompact E) {s : ℝ≥0}
    (hs : 0 < s) (hDim : (s : ℝ≥0∞) < dimH E) :
    ∃ μ : ProbabilityMeasure (Space d), (μ : Measure (Space d)) Eᶜ = 0 ∧
      ∃ C : ℝ, 0 < C ∧ FrostmanBallBound (μ : Measure (Space d)) (s:ℝ) C := by
  obtain ⟨Q,hQ,hEQ⟩ := exists_containing_cube E hE
  obtain ⟨c,hc,μ,hμ⟩ := cube_probability_sequence hd E hE hs hDim Q hQ hEQ
  have hcarry : ∀ K, (μ K : Measure (Space d)) Q.carrierᶜ = 0 := fun K =>
    measure_mono_null (compl_subset_compl.mpr hEQ) (hμ K).1
  obtain ⟨C,hC,hball⟩ := eventual_cube_ball_bounds Q hQ
    (by exact_mod_cast hs) hc μ hcarry (fun K => (hμ K).2)
  obtain ⟨ν,hν,hfrost⟩ := frostman_of_eventual_ball_bounds E hE μ
    (fun K => (hμ K).1) (s:ℝ) C hball
  exact ⟨ν,hν,C,hC,hfrost⟩

theorem published_frostman_above_half : PublishedFrostmanAboveHalf := by
  intro d hd E hE hDim
  have hhalf : (d : ℝ≥0∞)/2 = ENNReal.ofReal ((d:ℝ)/2) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num),ENNReal.ofReal_natCast]
    norm_num
  have hu : (d : ℝ≥0∞)/2 < ENNReal.ofReal ((d:ℝ)/2+1) := by
    rw [hhalf]
    exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  obtain ⟨a,ha0,ha⟩ := exists_between (lt_min hDim hu)
  have hatop : a ≠ ∞ := (ha.trans_le (min_le_right _ _)).ne_top
  have halow : (d:ℝ)/2 < a.toReal := by
    rw [hhalf] at ha0
    have hh := (ENNReal.toReal_lt_toReal ENNReal.ofReal_ne_top hatop).mpr ha0
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (d:ℝ)/2)] using hh
  have hahigh : a.toReal < (d:ℝ)/2+1 := by
    have hh := (ENNReal.toReal_lt_toReal hatop ENNReal.ofReal_ne_top).mpr
      (ha.trans_le (min_le_right _ _))
    simpa only [ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ (d:ℝ)/2+1)] using hh
  have has : 0 < a.toNNReal := ENNReal.toNNReal_pos (bot_le.trans_lt ha0).ne' hatop
  obtain ⟨μ,hμ,C,hC,hball⟩ := frostman_probability (by omega : 1 ≤ d) E hE has
    (by rw [ENNReal.coe_toNNReal hatop]; exact ha.trans_le (min_le_left _ _))
  refine ⟨a.toReal,halow,hahigh,μ,hμ,C,hC,?_⟩
  simpa only [ENNReal.toReal] using hball

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_FourInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The main distance theorem from four analytic hypotheses -/
namespace Falconer

theorem mainTarget_of_four_published_inputs
    (hRadial : PublishedRadialMoment)
    (hHeavy : PublishedHeavyHyperplanes)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_five_published_inputs published_frostman_above_half
    hRadial hHeavy hFurstenberg hQuadratic

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavySelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Counting heavy sets with small pairwise intersections

This second-moment estimate is the finite selection step for the published
heavy-hyperplane input. The geometric intersection estimate is kept separate.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators

theorem finite_indicator_square_integral {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) (I : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) :
    (∫⁻ x, (∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x)^2 ∂μ) =
      ∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j) := by
  classical
  have hpoint (x : X) : (∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x)^2 =
      ∑ i ∈ I, ∑ j ∈ I, (A i ∩ A j).indicator (fun _ => (1:ℝ≥0∞)) x := by
    rw [pow_two,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hi' : x ∈ A i <;> by_cases hj' : x ∈ A j <;> simp [hi',hj']
  simp_rw [hpoint]
  rw [lintegral_finsetSum' I (fun i hi =>
    (Finset.measurable_sum I fun j hj => measurable_const.indicator
      ((hA i hi).inter (hA j hj))).aemeasurable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [lintegral_finsetSum' I (fun j hj =>
    (measurable_const.indicator ((hA i hi).inter (hA j hj))).aemeasurable)]
  exact Finset.sum_congr rfl fun j hj => lintegral_indicator_one ((hA i hi).inter (hA j hj))

theorem heavy_pairwise_card_bound {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (I : Finset ι) (A : ι → Set X)
    (hA : ∀ i ∈ I, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m)
    (hheavy : ∀ i ∈ I, ENNReal.ofReal m ≤ μ (A i))
    (hpair : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2)) :
    (I.card:ℝ) ≤ 2/m := by
  classical
  let M : ℝ≥0∞ := ∑ i ∈ I, μ (A i)
  have hMfinite : M ≠ ∞ := by
    exact (ENNReal.sum_lt_top.mpr fun i _ => measure_lt_top μ (A i)).ne
  have hlow : (I.card:ℝ≥0∞)*ENNReal.ofReal m ≤ M := by
    simpa [M] using Finset.sum_le_sum hheavy
  have hlowR : (I.card:ℝ)*m ≤ M.toReal := by
    have h := ENNReal.toReal_mono hMfinite hlow
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_natCast,ENNReal.toReal_ofReal hm.le] using h
  let F : X → ℝ≥0∞ := fun x => ∑ i ∈ I, (A i).indicator (fun _ => (1:ℝ≥0∞)) x
  have hF : Measurable F := Finset.measurable_sum I fun i hi =>
    measurable_const.indicator (hA i hi)
  have hFM : (∫⁻ x, F x ∂μ) = M := by
    rw [lintegral_finsetSum' I (fun i hi =>
      (measurable_const.indicator (hA i hi)).aemeasurable)]
    exact Finset.sum_congr rfl fun i hi => lintegral_indicator_one (hA i hi)
  have hsecond : M^2 ≤ ∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j) := by
    have h := incidence_moment μ F hF.aemeasurable (by norm_num : 2 ≤ (2:ℕ))
    rw [hFM,measure_univ,one_pow,mul_one] at h
    exact h.trans_eq (finite_indicator_square_integral μ I A hA)
  have hupper : (∑ i ∈ I, ∑ j ∈ I, μ (A i ∩ A j)) ≤
      M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) := by
    calc
      _ ≤ ∑ i ∈ I, ∑ j ∈ I,
          ((if i=j then μ (A i) else 0)+ENNReal.ofReal (m^2/2)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i=j
        · subst j
          simp
        · simpa only [hij,ite_false, if_false,zero_add] using hpair i hi j hj hij
      _ = M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) := by
        simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul]
        simp [M,pow_two,mul_assoc]
  have hR : M.toReal^2 ≤ M.toReal+(I.card:ℝ)^2*(m^2/2) := by
    have ht : M+(I.card:ℝ≥0∞)^2*ENNReal.ofReal (m^2/2) ≠ ∞ := by finiteness
    have hh := ENNReal.toReal_mono ht (hsecond.trans hupper)
    rw [ENNReal.toReal_add hMfinite (by finiteness)] at hh
    simpa only [ENNReal.toReal_pow,
      ENNReal.toReal_mul,ENNReal.toReal_natCast,
      ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ m^2/2)] using hh
  have hsq : ((I.card:ℝ)*m)^2 ≤ M.toReal^2 :=
    (sq_le_sq₀ (by positivity) ENNReal.toReal_nonneg).mpr hlowR
  have hMle : M.toReal ≤ 2 := by nlinarith [ENNReal.toReal_nonneg (a := M)]
  exact (le_div_iff₀ hm).mpr (hlowR.trans hMle)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyMaximal
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # A finite maximal family of heavy sets

Every heavy set has a substantial intersection with a chosen representative.
The next geometric step turns that intersection into containment in a thicker
hyperplane neighborhood.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem maximal_heavy_family {X ι : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsProbabilityMeasure μ] (U : Set ι) (A : ι → Set X)
    (hA : ∀ i ∈ U, MeasurableSet (A i)) {m : ℝ} (hm : 0 < m) (hm1 : m ≤ 1)
    (hheavy : ∀ i ∈ U, ENNReal.ofReal m ≤ μ (A i)) :
    ∃ S : Finset ι, (∀ i ∈ S, i ∈ U) ∧ (S.card:ℝ) ≤ 2/m ∧
      ∀ i ∈ U, ∃ j ∈ S, ENNReal.ofReal (m^2/2) < μ (A i ∩ A j) := by
  classical
  let P : ℕ → Prop := fun n => ∃ S : Finset ι, S.card = n ∧
    (∀ i ∈ S, i ∈ U) ∧ ∀ i ∈ S, ∀ j ∈ S, i ≠ j →
      μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2)
  let B := Nat.ceil (2/m)
  have hbound (n : ℕ) (hn : P n) : n ≤ B := by
    obtain ⟨S,rfl,hS,hpair⟩ := hn
    have hb := heavy_pairwise_card_bound μ S A (fun i hi => hA i (hS i hi)) hm
      (fun i hi => hheavy i (hS i hi)) hpair
    exact_mod_cast hb.trans (Nat.le_ceil (2/m))
  have hP0 : P 0 := ⟨∅,by simp,by simp,by simp⟩
  obtain ⟨S,hcard,hS,hpair⟩ := Nat.findGreatest_spec (Nat.zero_le B) hP0
  refine ⟨S,hS,heavy_pairwise_card_bound μ S A (fun i hi => hA i (hS i hi)) hm
    (fun i hi => hheavy i (hS i hi)) hpair,?_⟩
  intro i hi
  by_contra hnone
  have hsmall (j : ι) (hj : j ∈ S) : μ (A i ∩ A j) ≤ ENNReal.ofReal (m^2/2) := by
    exact le_of_not_gt (fun h => hnone ⟨j,hj,h⟩)
  have his : i ∉ S := by
    intro his
    have hstrict : ENNReal.ofReal (m^2/2) < ENNReal.ofReal m :=
      (ENNReal.ofReal_lt_ofReal_iff hm).mpr (by nlinarith)
    have hh := hsmall i his
    rw [inter_self] at hh
    exact (not_lt_of_ge hh) (hstrict.trans_le (hheavy i hi))
  have hins : P ((insert i S).card) := by
    refine ⟨insert i S,rfl,?_,?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact hi
      · exact hS j hj
    · intro j hj k hk hjk
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        rcases Finset.mem_insert.mp hk with hki | hkS
        · exact (hjk hki.symm).elim
        · exact hsmall k hkS
      · rcases Finset.mem_insert.mp hk with hki | hkS
        · subst k
          simpa only [inter_comm] using hsmall j hjS
        · exact hpair j hjS k hkS hjk
  have hmax := Nat.le_findGreatest (hbound _ hins) hins
  rw [Finset.card_insert_of_notMem his,hcard] at hmax
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_OrthonormalRectangle
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Covering a transverse rectangle by codimension-two neighborhoods -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem orthonormal_rectangle_cover {d : ℕ} (v : Fin 2 → Space d)
    (hv : Orthonormal ℝ v) (a b : ℝ) {r R : ℝ} (hr : 0 < r) (hR : r ≤ R) :
    ∃ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 ∧
      ∃ S : Finset (Space d), (S.card:ℝ) ≤ 63*(R/r) ∧
        {x | |inner ℝ (v 0) x-a| ≤ r ∧ |inner ℝ (v 1) x-b| ≤ R} ⊆
          ⋃ p ∈ S, affineSubspaceNeighborhood V p r := by
  classical
  obtain ⟨V,hV,hproj⟩ := orthonormal_pair_complement v hv
  let L := Nat.ceil (R/(r/2)+1)
  let I := Finset.Icc (-3:ℤ) 3
  let J := Finset.Icc (-(L:ℤ)) (L:ℤ)
  let p : ℤ × ℤ → Space d := fun z =>
    (a+(r/2)*(z.1:ℝ)) • v 0 + (b+(r/2)*(z.2:ℝ)) • v 1
  let S := (I.product J).image p
  have hR0 : 0 ≤ R := hr.le.trans hR
  have hcard : (S.card:ℝ) ≤ 63*(R/r) := by
    have hI : I.card = 7 := by first | (norm_num [I]; done) | simp [I]
    have hJ : J.card = 2*L+1 := by dsimp [J]; rw [Int.card_Icc]; omega
    have hS : (S.card:ℝ) ≤ 7*(2*(L:ℝ)+1) := by
      have hh : S.card ≤ I.card*J.card :=
        (Finset.card_image_le (s := I.product J) (f := p)).trans_eq (Finset.card_product I J)
      rw [hI,hJ] at hh
      exact_mod_cast hh
    have hL : (L:ℝ) ≤ 2*(R/r)+2 := by
      calc
        (L:ℝ) ≤ R/(r/2)+1+1 := (Nat.ceil_lt_add_one (by positivity)).le
        _ = 2*(R/r)+2 := by field_simp; ring
    have hratio : 1 ≤ R/r := (le_div_iff₀ hr).mpr (by simpa using hR)
    nlinarith
  refine ⟨V,hV,S,hcard,?_⟩
  intro x hx
  let i := round ((inner ℝ (v 0) x-a)/(r/2))
  let j := round ((inner ℝ (v 1) x-b)/(r/2))
  have hi : i ∈ I := Finset.mem_Icc.mpr
    (round_bound (by positivity : 0 < r/2) 3
      (by rw [show r/(r/2) = 2 by field_simp]; norm_num) _ hx.1)
  have hj : j ∈ J := Finset.mem_Icc.mpr
    (round_bound (by positivity : 0 < r/2) L (Nat.le_ceil _) _ hx.2)
  refine mem_iUnion₂.mpr ⟨p (i,j),Finset.mem_image.mpr
    ⟨(i,j),Finset.mem_product.mpr ⟨hi,hj⟩,rfl⟩,?_⟩
  have hvij := orthonormal_iff_ite.mp hv
  have h0 : |inner ℝ (v 0) (x-p (i,j))| ≤ r/4 := by
    have he : inner ℝ (v 0) (x-p (i,j)) = inner ℝ (v 0) x-a-(r/2)*(i:ℝ) := by
      simp [p,inner_sub_right,inner_add_right,inner_smul_right,hvij,hv.norm_eq_one]
      ring
    rw [he]
    convert round_mesh_error (by positivity : 0 < r/2) (inner ℝ (v 0) x-a) using 1 <;> first | rfl | ring
  have h1 : |inner ℝ (v 1) (x-p (i,j))| ≤ r/4 := by
    have he : inner ℝ (v 1) (x-p (i,j)) = inner ℝ (v 1) x-b-(r/2)*(j:ℝ) := by
      simp [p,inner_sub_right,inner_add_right,inner_smul_right,hvij,hv.norm_eq_one]
      ring
    rw [he]
    convert round_mesh_error (by positivity : 0 < r/2) (inner ℝ (v 1) x-b) using 1 <;> first | rfl | ring
  change ‖Vᗮ.starProjection (x-p (i,j))‖ ≤ r
  exact (hproj _).trans (by linarith)

theorem orthonormal_rectangle_mass {d : ℕ} (μ : Measure (Space d))
    (v : Fin 2 → Space d) (hv : Orthonormal ℝ v) (a b : ℝ) {r R C α : ℝ}
    (hr : 0 < r) (hR : r ≤ R) (hC : 0 ≤ C)
    (hplane : ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
      ∀ p, μ (affineSubspaceNeighborhood V p r) ≤ ENNReal.ofReal (C*r^α)) :
    μ {x | |inner ℝ (v 0) x-a| ≤ r ∧ |inner ℝ (v 1) x-b| ≤ R} ≤
      ENNReal.ofReal (63*(R/r)*(C*r^α)) := by
  obtain ⟨V,hV,S,hcard,hcover⟩ := orthonormal_rectangle_cover v hv a b hr hR
  apply (measure_mono hcover).trans ((measure_biUnion_finset_le _ _).trans ?_)
  calc
    _ ≤ ∑ _p ∈ S, ENNReal.ofReal (C*r^α) := Finset.sum_le_sum fun p _ => hplane V hV p
    _ = ENNReal.ofReal ((S.card:ℝ)*(C*r^α)) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (by positivity)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right hcard (mul_nonneg hC (Real.rpow_nonneg hr.le _)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_TwoSlabSingleScale
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Single-scale mass of two transverse thick hyperplanes

Only the stated concentration bound at radius r is used. The long transverse
side is covered by O(1/τ) radius-r codimension-two neighborhoods.
-/
namespace Falconer
open Set MeasureTheory NormedSpace
open scoped ENNReal

theorem two_slab_single_scale_bound {d : ℕ} (μ : Measure (Space d))
    (u v : Space d) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (a b : ℝ)
    {r τ C α : ℝ} (hr : 0 < r) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hC : 0 ≤ C)
    (hsep : τ ≤ normalDistance u v)
    (hplane : ∀ V : Submodule ℝ (Space d), Module.finrank ℝ V = d-2 →
      ∀ p, μ (affineSubspaceNeighborhood V p r) ≤ ENNReal.ofReal (C*r^α)) :
    μ {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ≤
      ENNReal.ofReal (252*C*r^α/τ) := by
  let w := perpendicularPart u v
  have ht : τ ≤ 2*‖w‖ := hsep.trans (normalDistance_le_perpendicular hu hv)
  have hw : 0 < ‖w‖ := by linarith
  let e := normalize w
  have he : ‖e‖ = 1 := by
    dsimp [e,NormedSpace.normalize]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hw),inv_mul_cancel₀ hw.ne']
  have huu : inner ℝ u u = 1 := by rw [real_inner_self_eq_norm_sq,hu]; norm_num
  have hwu : inner ℝ u w = 0 := by
    simp only [w,perpendicularPart,inner_sub_right,inner_smul_right,huu,mul_one,sub_self]
  have heu : inner ℝ u e = 0 := by
    simp only [e,NormedSpace.normalize,inner_smul_right,hwu,mul_zero]
  have horth : Orthonormal ℝ (![u,e] : Fin 2 → Space d) := by
    apply orthonormal_iff_ite.mpr
    intro i j
    fin_cases i <;> fin_cases j
    · simpa using huu
    · simpa using heu
    · have h : inner ℝ e u = 0 := (real_inner_comm u e).trans heu
      simpa using h
    · simp [he]
  have hc : |inner ℝ u v| ≤ 1 := by
    simpa only [hu,hv,mul_one] using abs_real_inner_le_norm u v
  let c := (b-inner ℝ u v*a)/‖w‖
  have hsub : {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ v x-b| ≤ r} ⊆
      {x | |inner ℝ u x-a| ≤ r ∧ |inner ℝ e x-c| ≤ 4*r/τ} := by
    intro x hx
    refine ⟨hx.1,?_⟩
    have hformula : inner ℝ e x-c =
        (inner ℝ v x-b-inner ℝ u v*(inner ℝ u x-a))/‖w‖ := by
      simp only [e,NormedSpace.normalize,w,perpendicularPart,real_inner_smul_left,
        inner_sub_left,c]
      ring
    rw [hformula,abs_div,abs_of_pos hw]
    have hb : |inner ℝ v x-b-inner ℝ u v*(inner ℝ u x-a)| ≤ 2*r := by
      apply (abs_sub _ _).trans
      rw [abs_mul]
      have hmul := mul_le_mul hc hx.1 (abs_nonneg _) zero_le_one
      linarith [hx.2]
    apply (div_le_div_of_nonneg_right hb hw.le).trans
    apply (div_le_div_iff₀ hw hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right ht hr.le]
  have hR : r ≤ 4*r/τ := by
    apply (le_div_iff₀ hτ).mpr
    nlinarith [mul_le_mul_of_nonneg_right hτ1 hr.le]
  have hmass := orthonormal_rectangle_mass μ (![u,e] : Fin 2 → Space d)
    horth a c hr hR hC hplane
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one] at hmass
  apply (measure_mono hsub).trans (hmass.trans_eq ?_)
  congr 1
  field_simp
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Radial_HeavyDischarge
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Discharging the application-level heavy-hyperplane input

The maximal heavy family has at most 2/m representatives. A substantial
intersection forces the normals to be close, because transverse slabs have
small mass by the stated single-scale codimension-two concentration bound.
-/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal

theorem published_heavy_hyperplanes : PublishedHeavyHyperplanes := by
  intro d _hd a C ha ha1 hC
  let b := heavyPlateExponent a
  let c := a-2*b
  let K := max 2 (2016*C+3)
  have hb : 0 < b := heavyPlateExponent_pos (by linarith)
  have hc1 : c < 1 := by dsimp [c]; linarith
  refine ⟨K,(by dsimp [K]; exact le_trans (by norm_num) (le_max_left _ _)),?_⟩
  intro μ δ hδ hδ1 hbounded hplane
  let m := δ^b
  let τ := 504*C*δ^c
  have hm : 0 < m := Real.rpow_pos_of_pos hδ _
  have hm1 : m ≤ 1 := Real.rpow_le_one hδ.le hδ1 hb.le
  have hτ : 0 < τ := by dsimp [τ]; positivity
  let A : Space d × ℝ → Set (Space d) := fun p =>
    {x | ‖x‖ < 1 ∧ |inner ℝ p.1 x-p.2| ≤ δ}
  let U : Set (Space d × ℝ) := {p | ‖p.1‖ = 1 ∧ ENNReal.ofReal m ≤ (μ : Measure (Space d)) (A p)}
  have hA (p : Space d × ℝ) : MeasurableSet (A p) := by
    change MeasurableSet ({x : Space d | ‖x‖ < 1} ∩
      {x : Space d | |inner ℝ p.1 x-p.2| ≤ δ})
    exact (measurableSet_lt measurable_norm measurable_const).inter
      (measurableSet_le (by fun_prop) measurable_const)
  have hmass (p : Space d × ℝ) : (μ : Measure (Space d)) (A p) =
      (μ : Measure (Space d)) {x | |inner ℝ p.1 x-p.2| ≤ δ} := by
    apply measure_congr
    filter_upwards [hbounded] with x hx
    exact propext (and_iff_right hx)
  obtain ⟨S,hS,hcard,hcover⟩ := maximal_heavy_family (μ : Measure (Space d)) U A
    (fun p _ => hA p) hm hm1 (fun p hp => hp.2)
  refine ⟨S,fun p hp => (hS p hp).1,?_,?_⟩
  · apply hcard.trans
    have hK2 : 2 ≤ K := le_max_left _ _
    dsimp [m]
    rw [div_eq_mul_inv,← Real.rpow_neg hδ.le]
    exact mul_le_mul_of_nonneg_right hK2 (Real.rpow_nonneg hδ.le _)
  · intro w hw t hheavy
    have hi : (w,t) ∈ U := by
      exact ⟨hw,by rw [hmass]; exact hheavy⟩
    obtain ⟨p,hp,hinter⟩ := hcover (w,t) hi
    have hpunit : ‖p.1‖ = 1 := (hS p hp).1
    have hnonempty : (A (w,t) ∩ A p).Nonempty := by
      by_contra hempty
      rw [Set.not_nonempty_iff_eq_empty.mp hempty,measure_empty] at hinter
      exact (not_lt_of_ge bot_le) hinter
    obtain ⟨z,hz⟩ := hnonempty
    have hclose : normalDistance p.1 w ≤ 2*τ := by
      by_cases hτ1 : τ ≤ 1
      · by_cases hnear : normalDistance p.1 w ≤ τ
        · exact hnear.trans (by linarith)
        · have htrans := two_slab_single_scale_bound (μ : Measure (Space d)) p.1 w
            hpunit hw p.2 t hδ hτ hτ1 hC.le (le_of_lt (lt_of_not_ge hnear)) hplane
          have hsub : A (w,t) ∩ A p ⊆
              {x | |inner ℝ p.1 x-p.2| ≤ δ ∧ |inner ℝ w x-t| ≤ δ} :=
            fun x hx => ⟨hx.2.2,hx.1.2⟩
          have hpower : δ^a = δ^c*m^2 := by
            dsimp [m]
            rw [pow_two,← Real.rpow_add hδ,← Real.rpow_add hδ]
            congr 1
            dsimp [c]
            ring
          have heq : 252*C*δ^a/τ = m^2/2 := by
            rw [hpower]
            dsimp [τ]
            field_simp
            ring
          rw [heq] at htrans
          exact False.elim ((not_lt_of_ge ((measure_mono hsub).trans htrans)) hinter)
      · have hnormal : normalDistance p.1 w ≤ 2 := by
          apply (min_le_left _ _).trans
          exact (norm_sub_le _ _).trans_eq (by rw [hpunit,hw]; norm_num)
        exact hnormal.trans (by linarith)
    refine ⟨p,hp,fun x hx hxw => ?_⟩
    have hcluster := affine_slab_cluster (M := 1) hz.1.1.le hx.le hclose hz.2.2 hz.1.2 hxw
    have hδc : δ ≤ δ^c := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge hδ hδ1 hc1.le
    apply hcluster.trans
    have hK : 2016*C+3 ≤ K := le_max_right _ _
    calc
      2*1*(2*τ)+3*δ ≤ (2016*C+3)*δ^c := by dsimp [τ]; nlinarith
      _ ≤ K*δ^c := mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hδ.le _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ThreeInputsMain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The exact main theorem after the heavy-hyperplane discharge -/
namespace Falconer

theorem mainTarget_of_three_published_inputs_oai
    (hRadial : PublishedRadialMoment)
    (hFurstenberg : PublishedPlanarFurstenberg)
    (hQuadratic : PublishedQuadraticStationary) : MainTarget :=
  mainTarget_of_four_published_inputs hRadial published_heavy_hyperplanes
    hFurstenberg hQuadratic

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.mainTarget_of_three_published_inputs_oai := @OAI.Falconer.mainTarget_of_three_published_inputs_oai
