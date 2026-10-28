-- Prove2me | solution 1 for OAI.PlanarFalconer.exists_normalized_root_setup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T09:22:29.544589+00:00
-- url     : https://prove2.me/submissions/e8ec4c7d-8c1c-4056-b3f9-ef737e58fee3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_PlanarFalconer
import Definitions.Def_OAIQ038F002
import Theorems.Thm_OAI_PlanarFalconer_finite_radial_testNorm_integral

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
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Frostman_Capacity
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_Content
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_ContentBound
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_GeometricCapacity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Measures_DyadicMeasure
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Measures_WeakLimit
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_Frostman
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Graphs_Energy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialPreparation
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.projectedMeasure_finite _root_.OAI.PlanarFalconer.sourceArcLength_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialTestNorm
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Angular_CircleTests
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_AtomlessRadialContinuity
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Recursion_ParentConeGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_RootPatchGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_RootSimilarityGeometry
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_RadialLpEnergy
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.unitCircle_compactSpace _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Geometry_CompactSublevel
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_UniformRadialRestrictions
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Radial_SourceRadialSetup
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ENNReal NNReal

theorem source_uniform_radial_restrictions (μ₀ ν₀ : ProbabilityMeasure Plane)
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
  obtain ⟨hs1, hs2, hp1, hp2, ht0, hupt, htp, hsδ, htδ⟩ := radial_parameters hδ hδ1
  have hpq : (1+δ/8).HolderConjugate ((1+δ/8)/((1+δ/8)-1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp1).mpr rfl
  have hIμ := finite_radial_Lp_integral (ν₀ : Measure Plane) μ₀ hνK hμK hsep.symm
    (ν₀ : Measure Plane).support_mem_ae (μ₀ : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa [mul_comm] using hupt) htp
    (rieszEnergy_lt_top_of_ball_bound ν₀ (zero_lt_one.trans hs1) hsδ hνball)
    (rieszEnergy_lt_top_of_ball_bound μ₀ ht0 htδ hμball)
  have hIν := finite_radial_Lp_integral (μ₀ : Measure Plane) ν₀ hμK hνK hsep
    (μ₀ : Measure Plane).support_mem_ae (ν₀ : Measure Plane).support_mem_ae
    hpq hp2 hs1 hs2 (by simpa [mul_comm] using hupt) htp
    (rieszEnergy_lt_top_of_ball_bound μ₀ (zero_lt_one.trans hs1) hsδ hμball)
    (rieszEnergy_lt_top_of_ball_bound ν₀ ht0 htδ hνball)
  exact uniform_restrictions_of_finite_radial_moments μ₀ ν₀ hμK hνK
    (add_pos zero_lt_one hδ) hC hμball hνball hpq hIμ hIν

end PlanarFalconer

end OAI
end

section
-- module Solutions.OAIQ038_FA.Falconer_Measures_RootSimilarityMeasures
attribute [-instance] _root_.OAI.PlanarFalconer.PositiveDistanceData.cellPair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.distance_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.fourCells_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.pair_finite _root_.OAI.PlanarFalconer.PositiveDistanceData.suffixFullDistance_finite _root_.OAI.PlanarFalconer.angularFourCellMeasure_finite _root_.OAI.PlanarFalconer.weightedDistance_finite
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
-- module Solutions.OAIQ038_FA.Falconer_Shells_NormalizedOuterShell
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
-- module Solutions.OAIQ038_FA.Falconer_Frostman_NormalizedRootSetup
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ENNReal

theorem compact_neighborhood_probability (E : Set Plane) (hE : IsCompact E)
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

theorem exists_normalized_root_setup_oai (E : Set Plane) (hE : IsCompact E) (hd : 1 < dimH E) :
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
  obtain ⟨μ₀,hμ₀,Cμ,hCμ,hbμ⟩ := compact_neighborhood_probability E hE ζ hζ hC hball x hx hr
  obtain ⟨ν₀,hν₀,Cν,hCν,hbν⟩ := compact_neighborhood_probability E hE ζ hζ hC hball y hy hr
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
    have hh := separated_unit_roots_distance Q hQ (by rw [hcent]; norm_num)
      (by rw [hcent]; norm_num) z z (hμQ hz) (hνQ hz')
    have hh' := hh.1
    norm_num at hh'
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
    source_uniform_radial_restrictions μ₁ ν₁ hμK hνK hsep hδ hδ1 hD hbμ₁ hbν₁
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

theorem solution : type_of% @OAI.PlanarFalconer.exists_normalized_root_setup_oai := @OAI.PlanarFalconer.exists_normalized_root_setup_oai
