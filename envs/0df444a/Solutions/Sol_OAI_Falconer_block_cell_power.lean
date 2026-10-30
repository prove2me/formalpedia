-- Prove2me | solution 1 for OAI.Falconer.block_cell_power
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:03:03.62203+00:00
-- url     : https://prove2.me/submissions/73dc99bc-e436-45ce-af2c-3cb554affd04

import Mathlib
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_bounded_chart_regular_fine_gain

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGainFinite
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite labelled incidence obstruction

The sampling argument in `ang:planar-measures` ends with finite point
and line families. Their counting contradiction follows
from the precise published Furstenberg input. All line families must use
a common separated grid before cardinalities replace covering numbers.
Direction labels remain distinct throughout the upper counting estimate.
-/

namespace Falconer
open Set
open scoped BigOperators

theorem lineGridRound_error {δ : ℝ} (hδ : 0 < δ) (a : ℝ) :
    |a - lineGridRound δ a| ≤ δ / 2 := by
  have h := abs_sub_round (a / δ)
  calc
    |a - lineGridRound δ a| = |δ * (a / δ - (round (a / δ) : ℝ))| := by
      congr 1
      simp only [lineGridRound]
      field_simp
    _ = δ * |a / δ - (round (a / δ) : ℝ)| := by rw [abs_mul, abs_of_pos hδ]
    _ ≤ δ * (1 / 2) := mul_le_mul_of_nonneg_left h hδ.le
    _ = δ / 2 := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Angular_AngularGrid
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# A common line grid for the planar incidence obstruction

Each original strip gives a bounded list of common-grid line parameters.
The list is attached to its original direction label. Rounding therefore
turns the manuscript's covering-number upper bound into the cardinality
upper bound needed by `published_furstenberg_labelled_obstruction`.
-/

namespace Falconer
open Set

private theorem integer_grid_separation {δ : ℝ} (hδ : 0 < δ) {i j : ℤ}
    (hij : i ≠ j) : δ ≤ |δ * (i : ℝ) - δ * (j : ℝ)| := by
  have hzpos : (0 : ℤ) < |i - j| := abs_pos.mpr (sub_ne_zero.mpr hij)
  have hz : (1 : ℤ) ≤ |i - j| := by omega
  have hr : (1 : ℝ) ≤ |(i : ℝ) - (j : ℝ)| := by exact_mod_cast hz
  calc
    δ = δ * 1 := (mul_one _).symm
    _ ≤ δ * |(i : ℝ) - (j : ℝ)| := mul_le_mul_of_nonneg_left hr hδ.le
    _ = |δ * (i : ℝ) - δ * (j : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_pos hδ]

theorem gridLine_dist_ge {δ : ℝ} (hδ : 0 < δ) {p q : ℤ × ℤ} (hpq : p ≠ q) :
    δ ≤ dist (gridLine δ p) (gridLine δ q) := by
  by_cases hfst : p.1 = q.1
  · have hsnd : p.2 ≠ q.2 := by
      intro h
      exact hpq (Prod.ext hfst h)
    calc
      δ ≤ |δ * (p.2 : ℝ) - δ * (q.2 : ℝ)| := integer_grid_separation hδ hsnd
      _ = dist (gridLine δ p 1) (gridLine δ q 1) := by
        rw [gridLine_snd, gridLine_snd, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 1
  · calc
      δ ≤ |δ * (p.1 : ℝ) - δ * (q.1 : ℝ)| := integer_grid_separation hδ hfst
      _ = dist (gridLine δ p 0) (gridLine δ q 0) := by
        rw [gridLine_fst, gridLine_fst, Real.dist_eq]
      _ ≤ dist (gridLine δ p) (gridLine δ q) := PiLp.dist_apply_le _ _ 0

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicTree
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Finite dyadic trees in the original ambient dimension

All descendants use half-open carriers. Equal-depth cells are disjoint and
partition the parent, so restriction to them is an exact measure splitting.
-/

namespace Falconer
open Set MeasureTheory
attribute [local instance] Classical.propDecidable

theorem card_cubePaths (d n : ℕ) : (cubePaths d n).card = 2^(d*n) := by
  induction n with
  | zero => simp [cubePaths]
  | succ n ih =>
    rw [cubePaths, Finset.card_biUnion]
    · have hc (b : Fin d → Bool) : Function.Injective (List.cons b) :=
        fun _ _ h => (List.cons.inj h).2
      simp only [Finset.card_image_of_injective _ (hc _), ih,
        Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
        Fintype.card_fin, smul_eq_mul]
      rw [Nat.mul_succ, pow_add]
      exact Nat.mul_comm _ _
    · intro b _ c _ hbc
      apply Finset.disjoint_left.mpr
      intro p hp hq
      obtain ⟨p', _, hp'⟩ := Finset.mem_image.mp hp
      obtain ⟨q', _, hq'⟩ := Finset.mem_image.mp hq
      exact hbc (List.cons.inj (hp'.trans hq'.symm)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationLabels
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Upward regularization labels in arbitrary dimension

The label-preservation argument applies to all-dimensional dyadic paths.
Each extension retains or removes a whole previous child group.
-/

namespace Falconer.Regularization

variable {d : ℕ}

theorem labeledChildren_eq {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) (hf : f p = f q) :
    labeledChildren L f a b p = labeledChildren L f a b q := by
  classical
  simp only [labeledChildren, ha, hf]

theorem labeledChildren_nonempty {L : Finset (CellPath d)} (f : CellPath d → List ℕ)
    (a b : ℕ) {p : CellPath d} (hp : p ∈ L) :
    (labeledChildren L f a b p).Nonempty := by
  classical
  exact Finset.image_nonempty.mpr ⟨p, by simp [hp]⟩

theorem extendLabel_old {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (h : extendLabel L a b f p = extendLabel L a b f q) :
    f p = f q := (List.cons.inj h).2

theorem extendLabel_local {L : Finset (CellPath d)} {f : CellPath d → List ℕ}
    {a b : ℕ} {p q : CellPath d} (ha : p.take a = q.take a) :
    extendLabel L a b f p = extendLabel L a b f q ↔ f p = f q := by
  constructor
  · exact extendLabel_old
  · intro hf
    simp only [extendLabel, labeledChildren_eq ha hf, hf]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_AllDimensionalRegularizationCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Dimension-dependent counts for regularization labels

A selected-depth gap of length b-a has at most 2^(d*(b-a))
children, so its logarithmic count bin has d*(b-a)+1 possibilities.
The number of final labels is polynomial in terminal depth when the
number of selected blocks is fixed.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem labeledChildren_subset_extensions {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) :
    labeledChildren L f a b p ⊆ (cubePaths d (b-a)).image (fun q => p.take a ++ q) := by
  classical
  intro c hc
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hc
  obtain ⟨hq,ha,_⟩ := Finset.mem_filter.mp hq
  have hlen : q.length = N := (mem_cubePaths d N q).mp (hL hq)
  refine Finset.mem_image.mpr ⟨(q.take b).drop a, ?_, ?_⟩
  · simp only [mem_cubePaths, List.length_drop, List.length_take, hlen,
      Nat.min_eq_left hbN]
  · have he := List.take_append_drop a (q.take b)
    simpa only [List.take_take, Nat.min_eq_left hab, ha] using he

theorem labeledChildren_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : (labeledChildren L f a b p).card ≤ 2 ^ (d*(b-a)) :=
  (Finset.card_le_card (labeledChildren_subset_extensions hab hbN hL f p)).trans
    (Finset.card_image_le.trans_eq (card_cubePaths d (b-a)))

theorem child_bin_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ)
    (p : CellPath d) : Nat.log 2 (labeledChildren L f a b p).card ≤ d*(b-a) := by
  have hc := labeledChildren_card_le hab hbN hL f p
  have := Nat.log_mono_right (b := 2) hc
  simpa only [Nat.log_pow (by decide : 1 < 2)] using this

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCounting
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional prefix counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem prefixFiber_leaf {N : ℕ} {C : Finset (CellPath d)} (hC : C ⊆ cubePaths d N)
    {p : CellPath d} (hp : p ∈ C) : prefixFiber C N p = {p} := by
  classical
  ext q
  have hlen {path : CellPath d} (hpath : path ∈ C) : path.length = N :=
    (mem_cubePaths d N path).mp (hC hpath)
  simp only [prefixFiber, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ⟨hq,he⟩
    simpa only [← hlen hq, List.take_length] using he
  · intro he; subst q
    exact ⟨hp,by rw [← hlen hp,List.take_length]⟩

theorem prefixFiber_nonempty {C : Finset (CellPath d)} {a : ℕ} {P : CellPath d}
    (hP : P ∈ C.image (List.take a)) : (prefixFiber C a P).Nonempty := by
  classical
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  exact ⟨q,by simp [prefixFiber,hq]⟩

theorem prefixFiber_card_sum {C : Finset (CellPath d)} {a b : ℕ} (hab : a ≤ b)
    (P : CellPath d) :
    (prefixFiber C a P).card =
      ∑ c ∈ prefixChildren C a b P, (prefixFiber C b c).card := by
  classical
  rw [Finset.card_eq_sum_card_image (List.take b) (prefixFiber C a P)]
  apply Finset.sum_congr rfl
  intro c hc
  rw [prefixFiber_parent_filter hab hc]

theorem prefixFiber_count_bounds {C : Finset (CellPath d)} {a b lo hi B : ℕ}
    (hab : a ≤ b) (P : CellPath d)
    (hbranch : B ≤ (prefixChildren C a b P).card ∧ (prefixChildren C a b P).card ≤ 2*B)
    (hchild : ∀ c ∈ prefixChildren C a b P,
      lo ≤ (prefixFiber C b c).card ∧ (prefixFiber C b c).card ≤ hi) :
    B*lo ≤ (prefixFiber C a P).card ∧ (prefixFiber C a P).card ≤ 2*B*hi := by
  classical
  rw [prefixFiber_card_sum hab]
  constructor
  · calc
      B*lo ≤ (prefixChildren C a b P).card*lo := Nat.mul_le_mul_right _ hbranch.1
      _ = ∑ _c ∈ prefixChildren C a b P, lo := by simp
      _ ≤ _ := Finset.sum_le_sum (fun c hc => (hchild c hc).1)
  · calc
      _ ≤ ∑ _c ∈ prefixChildren C a b P, hi := Finset.sum_le_sum (fun c hc => (hchild c hc).2)
      _ = (prefixChildren C a b P).card*hi := by simp
      _ ≤ 2*B*hi := Nat.mul_le_mul_right _ hbranch.2

theorem prefixChildren_class_eq (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (a b : ℕ) {T : List ℕ} {p : CellPath d} (hp : p ∈ classLeaves L F T) :
    prefixChildren (classLeaves L F T) a b (p.take a) = labeledChildren L F a b p := by
  classical
  have hFp := (Finset.mem_filter.mp hp).2
  apply congrArg (Finset.image (List.take b))
  ext q
  simp only [prefixFiber, classLeaves, Finset.mem_filter, hFp]
  tauto

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockRegularization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# All-dimensional block regularization

The upward labels preserve complete child groups at every selected depth.
Count bins cost d*N+1 possibilities and leaf mass bins cost (d+2)*N+1.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem blockDepth_antitone (N B : ℕ) : Antitone (blockDepth N B) := by
  intro i j hij
  exact Nat.sub_le_sub_left (Nat.mul_le_mul_right B hij) N

theorem blockDepth_gap (N B i : ℕ) : blockDepth N B i - blockDepth N B (i+1) ≤ B := by
  dsimp only [blockDepth]
  rw [Nat.add_mul, one_mul]
  omega

theorem blockLabel_old (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j : ℕ} (hij : i ≤ j) {p q : CellPath d}
    (he : blockLabel L N B f j p = blockLabel L N B f j q) :
    blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    exact he
  | succ j ih =>
    by_cases heq : i = j+1
    · simpa only [heq] using he
    · exact ih (by omega) (extendLabel_old he)

theorem blockLabel_local (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i j a : ℕ} (hij : i ≤ j) (ha : blockDepth N B i ≤ a)
    {p q : CellPath d} (hpq : p.take a = q.take a) :
    blockLabel L N B f j p = blockLabel L N B f j q ↔
      blockLabel L N B f i p = blockLabel L N B f i q := by
  induction j with
  | zero =>
    have : i = 0 := by omega
    subst i
    rfl
  | succ j ih =>
    by_cases heq : i = j+1
    · subst i; rfl
    · have hji : i ≤ j := by omega
      rw [blockLabel, extendLabel_local (take_eq_of_take_eq
        ((blockDepth_antitone N B (by omega : i ≤ j+1)).trans ha) hpq)]
      exact ih hji

theorem block_final_children (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) (p : CellPath d) :
    labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p =
    labeledChildren L (blockLabel L N B f i)
      (blockDepth N B (i+1)) (blockDepth N B i) p := by
  classical
  apply congrArg (Finset.image (List.take (blockDepth N B i)))
  apply Finset.filter_congr
  intro q _
  constructor
  · rintro ⟨ha,hf⟩
    exact ⟨ha,blockLabel_old L N B f (by omega) hf⟩
  · rintro ⟨ha,hf⟩
    refine ⟨ha,(blockLabel_local L N B f (by omega : i+1 ≤ K) le_rfl ha).mpr ?_⟩
    exact (extendLabel_local ha).mpr hf

theorem block_final_bin_eq (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {i K : ℕ} (hi : i < K) {p q : CellPath d}
    (hclass : blockLabel L N B f K p = blockLabel L N B f K q) :
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) p).card =
    Nat.log 2 (labeledChildren L (blockLabel L N B f K)
      (blockDepth N B (i+1)) (blockDepth N B i) q).card := by
  rw [block_final_children L N B f hi,block_final_children L N B f hi]
  exact (List.cons.inj (blockLabel_old L N B f (by omega : i+1 ≤ K) hclass)).1

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockLeafCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional block-leaf counts for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}


theorem blockBin_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockBin L F N B i p := by
  unfold blockBin; positivity

theorem blockProduct_pos (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) : 0 < blockProduct L F N B i p := by
  exact Finset.prod_pos (fun j _ => blockBin_pos L F N B j p)

theorem blockClass_child_bounds (L : Finset (CellPath d)) (N B : ℕ) (f : CellPath d → List ℕ)
    {K i : ℕ} (hi : i < K) (p : CellPath d)
    {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B (i+1)))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockBin L F N B i p ≤ (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ∧
      (prefixChildren C (blockDepth N B (i+1)) (blockDepth N B i) P).card ≤ 2*blockBin L F N B i p := by
  classical
  dsimp only
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
  rw [prefixChildren_class_eq L _ _ _ hq]
  have hqL := (Finset.mem_filter.mp hq).1
  have hclass := (Finset.mem_filter.mp hq).2
  unfold blockBin
  rw [block_final_bin_eq L N B f hi hclass.symm]
  have hpos := Finset.card_pos.mpr (labeledChildren_nonempty
    (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) hqL)
  refine ⟨Nat.pow_log_le_self 2 (Nat.ne_of_gt hpos), ?_⟩
  have hu := Nat.lt_pow_succ_log_self (by decide : 1 < 2)
    (labeledChildren L (blockLabel L N B f K) (blockDepth N B (i+1)) (blockDepth N B i) q).card
  simpa only [pow_succ, Nat.mul_comm] using hu.le

theorem blockClass_leaf_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ) (p : CellPath d)
    {i : ℕ} (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hC : C ⊆ cubePaths d N := fun q hq => hL (Finset.mem_filter.mp hq).1
  change blockProduct L F N B i p ≤ (prefixFiber C (blockDepth N B i) P).card ∧
    (prefixFiber C (blockDepth N B i) P).card ≤ 2^i * blockProduct L F N B i p
  change P ∈ C.image (List.take (blockDepth N B i)) at hP
  induction i generalizing P with
  | zero =>
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hP
    have hlen : q.length = N := (mem_cubePaths _ _ _).mp (hC hq)
    simp only [blockDepth, Nat.zero_mul, Nat.sub_zero, ← hlen, List.take_length]
    rw [show q.length = N from hlen, prefixFiber_leaf hC hq]
    simp [blockProduct]
  | succ i ih =>
    have hb := blockClass_child_bounds L N B f (by omega : i < K) p hP
    have hc := prefixFiber_count_bounds (blockDepth_antitone N B (Nat.le_succ i)) P hb
      (fun c hc => ih (by omega) (prefixChildren_mem_image hc))
    dsimp only [blockProduct] at hc ⊢
    rw [Finset.prod_range_succ]
    constructor
    · simpa only [Nat.mul_comm] using hc.1
    · have hh := hc.2
      convert hh using 1
      all_goals try with_reducible_and_instances rfl
      ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNodeValues
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Values at the actual block depths, and the complementary descendant-count
values used by the Frostman profile lower bound. -/
namespace Falconer.Regularization

theorem finiteRampProfile_prefix (d c : ℕ → ℝ) {K k : ℕ} (hd : Antitone d) (hk : k ≤ K) :
    finiteRampProfile d c K (d 0)-finiteRampProfile d c K (d k) =
      ∑ j ∈ Finset.range k, c j*(d j-d (j+1)) := by
  classical
  have hr (j : ℕ) : intervalRamp (d (j+1)) (d j) (d 0)-
      intervalRamp (d (j+1)) (d j) (d k) = if j < k then d j-d (j+1) else 0 := by
    unfold intervalRamp
    rw [min_eq_right (hd (Nat.zero_le j)),min_eq_right (hd (Nat.zero_le (j+1)))]
    by_cases hj : j < k
    · rw [ite_eq_left hj,min_eq_left (hd (Nat.le_of_lt hj)),
        min_eq_left (hd (Nat.succ_le_of_lt hj))]
      ring
    · rw [ite_eq_right hj,min_eq_right (hd (Nat.le_of_not_gt hj)),
        min_eq_right (hd (Nat.le_succ_of_le (Nat.le_of_not_gt hj)))]
      ring
  have he : finiteRampProfile d c K (d 0)-finiteRampProfile d c K (d k) =
      ∑ j ∈ Finset.range K, c j*(intervalRamp (d (j+1)) (d j) (d 0)-
        intervalRamp (d (j+1)) (d j) (d k)) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  rw [he]
  calc
    _ = ∑ j ∈ Finset.range K, if j < k then c j*(d j-d (j+1)) else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hr]
      split_ifs <;> simp
    _ = ∑ j ∈ Finset.range k, c j*(d j-d (j+1)) := by
      rw [← Finset.sum_filter]
      congr 1
      ext j
      simp only [Finset.mem_filter,Finset.mem_range]
      omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileBranchCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact logarithmic coordinates for the retained block branching counts. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockSlope_mul_gap {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    blockSlope L F N B i p*((blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ)) =
      (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1)) (blockDepth N B i) p).card : ℝ)/(N : ℝ) := by
  unfold blockSlope
  by_cases he : (blockDepth N B i : ℝ)-(blockDepth N B (i+1) : ℝ) = 0
  · have hdep : blockDepth N B i = blockDepth N B (i+1) := by
      exact_mod_cast sub_eq_zero.mp he
    have hb := child_bin_le (blockDepth_antitone N B (Nat.le_succ i)) (Nat.sub_le _ _) hL F p
    have hd0 : d*(blockDepth N B i-blockDepth N B (i+1)) = 0 := by rw [hdep,Nat.sub_self,mul_zero]
    rw [hd0] at hb
    have hz := Nat.eq_zero_of_le_zero hb
    rw [hz,Nat.cast_zero,zero_div,zero_div,zero_mul]
  · exact div_mul_cancel₀ _ he

theorem regularizedProfile_node_difference {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i : ℕ} (hi : i ≤ K) :
    (N : ℝ)*(regularizedProfile L F N B K p N-
      regularizedProfile L F N B K p (blockDepth N B i)) =
      ∑ j ∈ Finset.range i,
        (Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card : ℝ) := by
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hp := finiteRampProfile_prefix (fun j => (blockDepth N B j : ℝ))
    (fun j => blockSlope L F N B j p)
    (show Antitone (fun j => (blockDepth N B j : ℝ)) from fun _ _ h =>
      Nat.cast_le.mpr (blockDepth_antitone N B h)) hi
  have hzero : (blockDepth N B 0 : ℝ) = N := by simp [blockDepth]
  rw [hzero] at hp
  change (N : ℝ)*(finiteRampProfile _ _ K N-finiteRampProfile _ _ K (blockDepth N B i)) = _
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [blockSlope_mul_gap hL F B j p]
  exact mul_div_cancel₀ _ hn

theorem blockProduct_real_rpow (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B i : ℕ) (p : CellPath d) :
    (blockProduct L F N B i p : ℝ) =
      (2 : ℝ) ^ (∑ j ∈ Finset.range i,
        (Nat.log 2 (labeledChildren L F (blockDepth N B (j+1)) (blockDepth N B j) p).card : ℝ)) := by
  rw [blockProduct,Nat.cast_prod]
  simp only [blockBin,Nat.cast_pow,Nat.cast_ofNat]
  rw [← Nat.cast_sum,Real.rpow_natCast]
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem blockProduct_profile_difference {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i : ℕ} (hi : i ≤ K) :
    (blockProduct L F N B i p : ℝ) = (2 : ℝ)^((N : ℝ)*
      (regularizedProfile L F N B K p N-regularizedProfile L F N B K p (blockDepth N B i))) := by
  rw [regularizedProfile_node_difference hN hL F B K p hi]
  exact blockProduct_real_rpow L F N B i p

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockDescendantCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local descendant counts in a retained block class, with both binning
losses explicit. These are the finite covering counts used by regularity. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockClass_descendant_count {N : ℕ} {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
    ((blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ))/(2 : ℝ)^j ≤ T.card ∧
      (T.card : ℝ) ≤ (2 : ℝ)^i*((blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ)) := by
  classical
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
  have hab := blockDepth_antitone N B hji
  have hparent := blockClass_leaf_count hL B f K p hi hP
  have hparent' : (blockProduct L F N B i p : ℝ) ≤ (prefixFiber C (blockDepth N B i) P).card ∧
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤ (2 : ℝ)^i*(blockProduct L F N B i p : ℝ) := by
    exact_mod_cast hparent
  have hchild (q : CellPath d) (hq : q ∈ T) :
      (blockProduct L F N B j p : ℝ) ≤ (prefixFiber C (blockDepth N B j) q).card ∧
      ((prefixFiber C (blockDepth N B j) q).card : ℝ) ≤ (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) := by
    have hh := blockClass_leaf_count hL B f K p (hji.trans hi) (prefixChildren_mem_image hq)
    exact_mod_cast hh
  have hsum : ((prefixFiber C (blockDepth N B i) P).card : ℝ) =
      ∑ q ∈ T, ((prefixFiber C (blockDepth N B j) q).card : ℝ) := by
    exact_mod_cast prefixFiber_card_sum (C := C) hab P
  have hlow : (T.card : ℝ)*(blockProduct L F N B j p : ℝ) ≤
      ((prefixFiber C (blockDepth N B i) P).card : ℝ) := by
    rw [hsum]
    calc
      _ = ∑ _q ∈ T, (blockProduct L F N B j p : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun q hq => (hchild q hq).1
  have hupp : ((prefixFiber C (blockDepth N B i) P).card : ℝ) ≤
      (T.card : ℝ)*((2 : ℝ)^j*(blockProduct L F N B j p : ℝ)) := by
    rw [hsum]
    calc
      _ ≤ ∑ _q ∈ T, (2 : ℝ)^j*(blockProduct L F N B j p : ℝ) :=
        Finset.sum_le_sum fun q hq => (hchild q hq).2
      _ = _ := by simp
  have hpj : 0 < (blockProduct L F N B j p : ℝ) := by exact_mod_cast blockProduct_pos L F N B j p
  constructor
  · apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^j)).2
    apply (div_le_iff₀ hpj).2
    nlinarith [hparent'.1.trans hupp]
  · rw [← mul_div_assoc]
    apply (le_div_iff₀ hpj).2
    exact hlow.trans hparent'.2

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large uniform subset retains mass in every one of its occupied parent
cells. This makes the original profile estimates hereditary after thinning. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prefix_fiber_local_retention (C S : Finset (CellPath 2)) (a : ℕ)
    (hSC : S ⊆ C) {M A D b d : ℝ} (hM : 0 ≤ M) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hd : 0 ≤ d) (hmass : (C.card:ℝ) ≤ M*(S.card:ℝ))
    (hC : ∀ q ∈ C.image (List.take a), b ≤ ((prefixFiber C a q).card:ℝ) ∧
      ((prefixFiber C a q).card:ℝ) ≤ A*b)
    (hS : ∀ q ∈ S.image (List.take a), d ≤ ((prefixFiber S a q).card:ℝ) ∧
      ((prefixFiber S a q).card:ℝ) ≤ D*d)
    {p : CellPath 2} (hp : p ∈ S.image (List.take a)) :
    ((prefixFiber C a p).card:ℝ) ≤ (A*M*D)*((prefixFiber S a p).card:ℝ) := by
  let B := C.image (List.take a)
  have hBC : p ∈ B := Finset.image_subset_image hSC hp
  have hB : 0 < (B.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr ⟨p,hBC⟩)
  have hCsum : (C.card:ℝ) = ∑ q ∈ B, ((prefixFiber C a q).card:ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_image (List.take a) C
  have hSsum : (S.card:ℝ) = ∑ q ∈ B, ((prefixFiber S a q).card:ℝ) := by
    have hmap : ∀ q ∈ S, q.take a ∈ B := fun q hq => Finset.mem_image_of_mem _ (hSC hq)
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  have hCmass : b*(B.card:ℝ) ≤ (C.card:ℝ) := by
    rw [hCsum]
    calc
      _ = ∑ _q ∈ B, b := by simp; ring
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (hC q hq).1)
  have hSmass : (S.card:ℝ) ≤ (D*d)*(B.card:ℝ) := by
    rw [hSsum]
    calc
      _ ≤ ∑ _q ∈ B, D*d := by
        apply Finset.sum_le_sum
        intro q _
        by_cases hq : (prefixFiber S a q).Nonempty
        · obtain ⟨v,hv⟩ := hq
          obtain ⟨hv,hvq⟩ := Finset.mem_filter.mp hv
          exact (hS q (Finset.mem_image.mpr ⟨v,hv,hvq⟩)).2
        · rw [Finset.not_nonempty_iff_eq_empty.mp hq,Finset.card_empty,Nat.cast_zero]
          exact mul_nonneg hD hd
      _ = _ := by simp; ring
  have hbd : b ≤ M*D*d := by
    apply (mul_le_mul_iff_left₀ hB).1
    calc
      _ ≤ (C.card:ℝ) := hCmass
      _ ≤ M*(S.card:ℝ) := hmass
      _ ≤ M*((D*d)*(B.card:ℝ)) := mul_le_mul_of_nonneg_left hSmass hM
      _ = _ := by ring
  calc
    _ ≤ A*b := (hC p hBC).2
    _ ≤ A*(M*D*d) := mul_le_mul_of_nonneg_left hbd hA
    _ = (A*M*D)*d := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (hS p hp).1 (by positivity)

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ChildRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local retention also controls the number of endpoint cells, not just
the fine mass. This is needed when the next incidence argument uses centers. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem prefix_children_mass_bounds (C : Finset (CellPath 2)) {a b : ℕ}
    (hab : a ≤ b) (p : CellPath 2) {u v : ℝ}
    (hchild : ∀ q ∈ prefixChildren C a b p,
      u ≤ ((prefixFiber C b q).card:ℝ) ∧ ((prefixFiber C b q).card:ℝ) ≤ v) :
    ((prefixChildren C a b p).card:ℝ)*u ≤ (prefixFiber C a p).card ∧
      ((prefixFiber C a p).card:ℝ) ≤ (prefixChildren C a b p).card*v := by
  have he : ((prefixFiber C a p).card:ℝ) =
      ∑ q ∈ prefixChildren C a b p, ((prefixFiber C b q).card:ℝ) := by
    exact_mod_cast prefixFiber_card_sum (C := C) hab p
  rw [he]
  constructor
  · calc
      _ = ∑ _q ∈ prefixChildren C a b p, u := by simp
      _ ≤ _ := Finset.sum_le_sum (fun q hq => (hchild q hq).1)
  · calc
      _ ≤ ∑ _q ∈ prefixChildren C a b p, v := Finset.sum_le_sum (fun q hq => (hchild q hq).2)
      _ = _ := by simp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeSecondMoment
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact finite incidence identities before the geometric common-tube bound. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem sum_tube_membership (U S : Finset (Space 2)) (hS : S ⊆ U) :
    (∑ l ∈ U, if l ∈ S then (1 : ℝ) else 0) = S.card := by
  rw [← Finset.sum_filter]
  have he : U.filter (fun l => l ∈ S) = S := by
    ext l
    simp only [Finset.mem_filter]
    exact and_iff_right_of_imp (fun hl => hS hl)
  rw [he]
  simp

theorem sum_tubeDegree (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, tubeDegree P T l) = ∑ x ∈ P, ((T x).card : ℝ) := by
  unfold tubeDegree
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  exact sum_tube_membership _ _ (Finset.subset_biUnion_of_mem T hx)

theorem sum_tubeDegree_sq (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ l ∈ P.biUnion T, (tubeDegree P T l)^2) =
      ∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ) := by
  let U := P.biUnion T
  calc
    _ = ∑ l ∈ U, ∑ x ∈ P, ∑ y ∈ P,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      simp only [tubeDegree, pow_two, Finset.sum_mul_sum, U]
    _ = ∑ x ∈ P, ∑ y ∈ P, ∑ l ∈ U,
        (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y _
      have he (l : Space 2) :
          (if l ∈ T x then (1 : ℝ) else 0)*(if l ∈ T y then 1 else 0) =
          if l ∈ T x ∩ T y then 1 else 0 := by
        by_cases hx : l ∈ T x <;> by_cases hy : l ∈ T y <;> simp [hx,hy]
      simp_rw [he]
      exact sum_tube_membership U _ (fun l hl =>
        Finset.mem_biUnion.mpr ⟨x,hx,(Finset.mem_inter.mp hl).1⟩)

theorem tube_union_second_moment (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) :
    (∑ x ∈ P, ((T x).card : ℝ))^2 ≤
      ((P.biUnion T).card : ℝ) * (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card : ℝ)) := by
  have hh := Finset.sum_mul_sq_le_sq_mul_sq (P.biUnion T)
    (fun _ => (1 : ℝ)) (tubeDegree P T)
  simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one,
    sum_tubeDegree, sum_tubeDegree_sq] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_TwoPointTubeGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two-point localization of actual bounded-chart tube parameters.
This is the elementary incidence kernel used in the multiscale Furstenberg proof. -/
namespace Falconer
open Set

theorem planar_dist_le_coordinate_sum (x y : Space 2) :
    dist x y ≤ |x 0-y 0| + |x 1-y 1| := by
  have he := EuclideanSpace.dist_sq_eq x y
  simp only [Fin.sum_univ_two, Real.dist_eq, sq_abs] at he
  nlinarith [dist_nonneg (x := x) (y := y), abs_nonneg (x 0-y 0),
    abs_nonneg (x 1-y 1), sq_abs (x 0-y 0), sq_abs (x 1-y 1),
    mul_nonneg (abs_nonneg (x 0-y 0)) (abs_nonneg (x 1-y 1))]

theorem tube_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l : Space 2}
    (hl : |l 0| ≤ 1) (hi : TubeIncident δ x l) :
    |x 1-l 0*x 0-l 1| ≤ 2*δ := by
  have hs : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (1+(l 0)^2) ≤ 2 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    have hsq := (sq_le_sq₀ (abs_nonneg (l 0)) zero_le_one).mpr hl
    nlinarith [sq_abs (l 0)]
  exact ((div_le_iff₀ hs).mp hi).trans (by nlinarith)

theorem tube_pair_residual_le {δ : ℝ} (hδ : 0 ≤ δ) {x l m : Space 2}
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hil : TubeIncident δ x l) (him : TubeIncident δ x m) :
    |(l 0-m 0)*x 0+(l 1-m 1)| ≤ 4*δ := by
  calc
    _ = |(x 1-m 0*x 0-m 1)-(x 1-l 0*x 0-l 1)| := by congr 1; ring
    _ ≤ |x 1-m 0*x 0-m 1|+|x 1-l 0*x 0-l 1| := abs_sub _ _
    _ ≤ _ := by linarith [tube_residual_le hδ hm him, tube_residual_le hδ hl hil]

theorem tube_point_coordinate_lower {δ r : ℝ} (hδ : 0 ≤ δ) (_hr : 0 < r)
    (hsmall : 16*δ ≤ r) {x y l : Space 2} (hl : |l 0| ≤ 1)
    (hx : TubeIncident δ x l) (hy : TubeIncident δ y l) (hxy : r ≤ dist x y) :
    r/4 ≤ |x 0-y 0| := by
  have he : |x 1-y 1| ≤ |x 0-y 0|+4*δ := by
    calc
      _ = |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)-(y 1-l 0*y 0-l 1)| := by congr 1; ring
      _ ≤ |l 0*(x 0-y 0)+(x 1-l 0*x 0-l 1)|+|y 1-l 0*y 0-l 1| := abs_sub _ _
      _ ≤ |l 0| * |x 0-y 0|+|x 1-l 0*x 0-l 1|+|y 1-l 0*y 0-l 1| := by
        rw [← abs_mul]
        linarith [abs_add_le (l 0*(x 0-y 0)) (x 1-l 0*x 0-l 1)]
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hl (abs_nonneg (x 0-y 0))
        linarith [tube_residual_le hδ hl hx, tube_residual_le hδ hl hy]
  linarith [planar_dist_le_coordinate_sum x y]

theorem two_point_tube_parameters_close {δ r : ℝ} (hδ : 0 ≤ δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    {x y l m : Space 2} (hx0 : |x 0| ≤ 1)
    (hl : |l 0| ≤ 1) (hm : |m 0| ≤ 1)
    (hxl : TubeIncident δ x l) (hyl : TubeIncident δ y l)
    (hxm : TubeIncident δ x m) (hym : TubeIncident δ y m)
    (hxy : r ≤ dist x y) : dist l m ≤ 80*δ/r := by
  have hcoord := tube_point_coordinate_lower hδ hr hsmall hl hxl hyl hxy
  have hs : |l 0-m 0| * |x 0-y 0| ≤ 8*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-((l 0-m 0)*y 0+(l 1-m 1))| := by
        rw [← abs_mul]; congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*y 0+(l 1-m 1)| := abs_sub _ _
      _ ≤ _ := by linarith [tube_pair_residual_le hδ hl hm hxl hxm,
        tube_pair_residual_le hδ hl hm hyl hym]
  have hslope : |l 0-m 0| ≤ 32*δ/r := by
    apply (le_div_iff₀ hr).2
    have hh := mul_le_mul_of_nonneg_left hcoord (abs_nonneg (l 0-m 0))
    nlinarith
  have hinter : |l 1-m 1| ≤ |l 0-m 0|+4*δ := by
    calc
      _ = |((l 0-m 0)*x 0+(l 1-m 1))-(l 0-m 0)*x 0| := by congr 1; ring
      _ ≤ |(l 0-m 0)*x 0+(l 1-m 1)|+|(l 0-m 0)*x 0| := abs_sub _ _
      _ ≤ _ := by
        rw [abs_mul]
        have hh := mul_le_mul_of_nonneg_left hx0 (abs_nonneg (l 0-m 0))
        linarith [tube_pair_residual_le hδ hl hm hxl hxm]
  apply (le_div_iff₀ hr).2
  have hdist : dist l m ≤ 2*|l 0-m 0|+4*δ :=
    (planar_dist_le_coordinate_sum l m).trans (by linarith [hinter])
  have hsum := mul_le_mul_of_nonneg_right hdist hr.le
  have hsl := (le_div_iff₀ hr).mp hslope
  have hd := mul_le_mul_of_nonneg_left hr1 hδ
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_FiniteBallBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Restriction and nonemptiness consequences for the normalized finite sets
appearing in the published planar incidence statement. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem normalized_finite_ball_bound_subset {δ s K C : ℝ}
    {P S : Finset (Space 2)} (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hS : S ⊆ P) (hsize : (P.card : ℝ) ≤ C*(S.card : ℝ))
    (hball : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound δ s (K*C) S := by
  intro z r hdr hr1
  have hsub : S.filter (fun x => dist x z ≤ r) ⊆ P.filter (fun x => dist x z ≤ r) := by
    intro x hx
    exact Finset.mem_filter.mpr ⟨hS (Finset.mem_filter.mp hx).1,(Finset.mem_filter.mp hx).2⟩
  calc
    _ ≤ ((P.filter (fun x => dist x z ≤ r)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ K*r^s*(P.card : ℝ) := hball z r hdr hr1
    _ ≤ K*r^s*(C*(S.card : ℝ)) :=
      mul_le_mul_of_nonneg_left hsize (mul_nonneg hK (Real.rpow_nonneg (hδ.trans hdr) _))
    _ = _ := by ring

theorem finiteSeparatedAt_subset {δ : ℝ} {P S : Finset (Space 2)}
    (hS : S ⊆ P) (hP : FiniteSeparatedAt δ P) : FiniteSeparatedAt δ S :=
  fun x hx y hy hxy => hP x (hS hx) y (hS hy) hxy

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InversePowerSum
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite dyadic inverse-power sums at the critical ambient exponent -/

namespace Falconer

theorem inverse_power_dyadic {r s : ℝ} (hr : 0 < r) (hs : 0 ≤ s) (g k : ℕ)
    (hmin : 1/(2:ℝ)^(g+k) ≤ r) :
    (1/r)^s ≤ ((2:ℝ)^g)^s + ∑ j ∈ Finset.range k,
      if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
  induction k with
  | zero =>
    simp only [Finset.range_zero,Finset.sum_empty,add_zero] at *
    apply Real.rpow_le_rpow (by positivity) _ hs
    apply (div_le_iff₀ hr).mpr
    have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^g)).mp hmin
    nlinarith
  | succ k ih =>
    rw [Finset.sum_range_succ]
    by_cases hc : 1/(2:ℝ)^(g+k) ≤ r
    · have hh := ih hc
      have hn : 0 ≤ (if r < 1/(2:ℝ)^(g+k) then ((2:ℝ)^(g+k+1))^s else 0) := by
        split_ifs <;> positivity
      linarith
    · rw [ite_eq_left (lt_of_not_ge hc)]
      have hinv : 1/r ≤ (2:ℝ)^(g+k+1) := by
        apply (div_le_iff₀ hr).mpr
        have hh := (div_le_iff₀ (by positivity : 0 < (2:ℝ)^(g+(k+1)))).mp hmin
        simpa only [Nat.add_assoc,mul_comm] using hh
      have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1/r) hinv hs
      have hsum : 0 ≤ ∑ j ∈ Finset.range k,
          if r < 1/(2:ℝ)^(g+j) then ((2:ℝ)^(g+j+1))^s else 0 := by
        apply Finset.sum_nonneg
        intro j _
        split_ifs <;> positivity
      have hz : 0 ≤ ((2:ℝ)^g)^s := by positivity
      linarith

end Falconer

end OAI
end

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
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RegularizedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale inverse-distance potentials for the slicing kernels -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_dyadic (μ : Measure X)
    (x : X) {s : ℝ} (hs : 0 ≤ s) (g k : ℕ) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
    ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g))+
      ∑ j ∈ Finset.range k, ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*
        μ (ball x (1/(2:ℝ)^(g+j))) := by
  let B := ball x (1/(2:ℝ)^g)
  let f : X → ℝ≥0∞ := fun y =>
    ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s)
  let F : X → ℝ≥0∞ := fun y =>
    B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k,
        (ball x (1/(2:ℝ)^(g+j))).indicator
          (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
  have hpoint : B.indicator f ≤ F := by
    intro y
    change B.indicator f y ≤ B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,show B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y =
        ENNReal.ofReal (((2:ℝ)^g)^s) from indicator_of_mem hy _]
      have hi := inverse_power_dyadic (s := s)
        (by positivity : 0 < dist x y+1/(2:ℝ)^(g+k)) hs g k
        (by linarith [dist_nonneg (x := x) (y := y)])
      have hh := ENNReal.ofReal_le_ofReal hi
      rw [ENNReal.ofReal_add (by positivity) (Finset.sum_nonneg (fun j _ => by split_ifs <;> positivity)),
        ENNReal.ofReal_sum_of_nonneg (fun j _ => by split_ifs <;> positivity)] at hh
      apply hh.trans
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro j hj
      by_cases hdist : dist x y+1/(2:ℝ)^(g+k) < 1/(2:ℝ)^(g+j)
      · rw [ite_eq_left hdist]
        have hyj : y ∈ ball x (1/(2:ℝ)^(g+j)) := by
          rw [mem_ball,dist_comm]
          linarith [show (0:ℝ) < 1/(2:ℝ)^(g+k) by positivity]
        rw [indicator_of_mem hyj]
      · rw [ite_eq_right hdist,ENNReal.ofReal_zero]
        exact bot_le
    · rw [indicator_of_notMem hy]
      exact bot_le
  rw [← lintegral_indicator measurableSet_ball]
  apply (lintegral_mono hpoint).trans_eq
  change (∫⁻ y, B.indicator (fun _ => ENNReal.ofReal (((2:ℝ)^g)^s)) y+
      ∑ j ∈ Finset.range k, (ball x (1/(2:ℝ)^(g+j))).indicator
        (fun _ => ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)) y ∂μ) = _
  rw [lintegral_add_left (measurable_const.indicator measurableSet_ball),
    lintegral_indicator_const measurableSet_ball,
    lintegral_finsetSum _ (fun j _ => measurable_const.indicator measurableSet_ball)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact lintegral_indicator_const measurableSet_ball _

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialScale
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Geometric summation above the inverse-kernel exponent -/

namespace Falconer

theorem dyadic_potential_weight (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^(n+1))^s)*(1/(2:ℝ)^n)^q =
      (2:ℝ)^s*(((2:ℝ)^n)^(s-q)) := by
  rw [pow_succ,Real.mul_rpow (by positivity) (by norm_num : (0:ℝ) ≤ 2),
    one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_start (n : ℕ) (s q : ℝ) :
    (((2:ℝ)^n)^s)*(1/(2:ℝ)^n)^q = (((2:ℝ)^n)^(s-q)) := by
  rw [one_div,Real.inv_rpow (by positivity),Real.rpow_sub (by positivity)]
  ring

theorem dyadic_potential_series (g k : ℕ) {s q : ℝ} (hsq : s < q) :
    (∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q))) ≤
      (((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q)) := by
  let a := (2:ℝ)^(s-q)
  have ha : 0 ≤ a := by positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hsq)
  have hsum : ∑ j ∈ Finset.range k, a^j ≤ (1-a)⁻¹ := by
    rw [← tsum_geometric_of_lt_one ha ha1]
    exact (summable_geometric_of_lt_one ha ha1).sum_le_tsum _ (fun _ _ => pow_nonneg ha _)
  have he (j : ℕ) : (((2:ℝ)^(g+j))^(s-q)) = (((2:ℝ)^g)^(s-q))*a^j := by
    rw [pow_add,Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    dsimp [a]
    rw [← Real.rpow_natCast_mul (by norm_num),← Real.rpow_mul_natCast (by norm_num)]
    congr 1
    ring
  simp_rw [he]
  rw [← Finset.mul_sum]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by rw [div_eq_mul_inv])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PotentialFrostman
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Finite-scale ball bounds control the regularized slicing potential -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_frostman (μ : Measure X) (x : X)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  apply (regularized_potential_dyadic μ x hs g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^s)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^s)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^s)*(1/(2:ℝ)^g)^q) := by ring
          _ = _ := by rw [dyadic_potential_start]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^s)*ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^s)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = _ := by rw [dyadic_potential_weight]; ring
  calc
    _ ≤ ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q)))+
        ∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^s*(((2:ℝ)^(g+j))^(s-q))) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))+
        K*(2:ℝ)^s*(∑ j ∈ Finset.range k, (((2:ℝ)^(g+j))^(s-q)))) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity),
        ← ENNReal.ofReal_add (by positivity) (by positivity),Finset.mul_sum]
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      have hh := mul_le_mul_of_nonneg_left (dyadic_potential_series g k hsq)
        (show 0 ≤ K*(2:ℝ)^s by positivity)
      calc
        _ ≤ K*(((2:ℝ)^g)^(s-q))+K*(2:ℝ)^s*
            ((((2:ℝ)^g)^(s-q))/(1-(2:ℝ)^(s-q))) := add_le_add le_rfl hh
        _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Dyadic inverse potentials of a nonnegative measurable geometric statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_frostman (Measure.map a μ) (0:ℝ) hK hs hsq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^s) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_TruncatedScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The maximum-truncated kernel and its dyadic sublevel bound -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem inverse_max_le_two_inverse_add {x r : ℝ} (hx : 0 ≤ x) (hr : 0 < r) :
    1/max x r ≤ 2/(x+r) := by
  apply (div_le_div_iff₀ (hr.trans_le (le_max_right x r)) (by positivity)).mpr
  have h₁ := le_max_left x r
  have h₂ := le_max_right x r
  linarith

theorem truncated_scalar_potential (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K s q : ℝ} (hK : 0 ≤ K) (hs : 0 ≤ s) (hsq : s < q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^s) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^s*(K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q))))) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^s ≤
      (2:ℝ)^s*(1/(a x+1/(2:ℝ)^(g+k)))^s := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^s := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hs
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^s)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^s) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal ((2:ℝ)^s)*ENNReal.ofReal
        (K*(((2:ℝ)^g)^(s-q))*(1+(2:ℝ)^s/(1-(2:ℝ)^(s-q)))) :=
      mul_le_mul' le_rfl (regularized_scalar_potential μ a ha ha0 hK hs hsq g k hsmall)
    _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_FiniteCountingPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The finite point potential needed by the elementary planar incidence bound. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem planarCountingMeasure_apply (P : Finset (Space 2)) (A : Set (Space 2)) :
    planarCountingMeasure P A = (P.filter (fun x => x ∈ A)).card := by
  rw [planarCountingMeasure,Measure.finsetSum_apply]
  simp_rw [Measure.dirac_apply,Set.indicator_apply,Pi.one_apply]
  rw [← Finset.sum_filter]
  simp

theorem planarCountingMeasure_lintegral (P : Finset (Space 2)) (f : Space 2 → ℝ≥0∞) :
    (∫⁻ x, f x ∂planarCountingMeasure P) = ∑ x ∈ P, f x := by
  rw [planarCountingMeasure,lintegral_finsetSum_measure]
  simp only [lintegral_dirac]

theorem finite_dyadic_truncated_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f)))) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^f) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^f = K*(1/(2:ℝ)^j)^f*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) (mul_nonneg hK (Nat.cast_nonneg _)) hb hbf 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add,Real.one_rpow,mul_one] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^b)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv hb).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

theorem planarPotentialConstant_pos {b f : ℝ} (hbf : b < f) :
    0 < planarPotentialConstant b f := by
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  unfold planarPotentialConstant
  positivity

theorem finite_dyadic_truncated_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K b f : ℝ} (hK : 1 ≤ K) (hb : 0 ≤ b) (hbf : b < f)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) f K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^b) ≤
      K*planarPotentialConstant b f*(P.card : ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hd : 0 < 1-(2:ℝ)^(b-f) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr hbf))
  have hR : 0 ≤ (P.card : ℝ)+(2:ℝ)^b*(K*(P.card : ℝ))*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by
    positivity
  have hh := finite_dyadic_truncated_potential P x N hK0 hb hbf hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity),
    ← ENNReal.ofReal_natCast P.card, ← ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)] at hh
  have hh' := (ENNReal.ofReal_le_ofReal_iff hR).mp hh
  apply hh'.trans
  unfold planarPotentialConstant
  have hC : 0 ≤ (2:ℝ)^b*(1+(2:ℝ)^b/(1-(2:ℝ)^(b-f))) := by positivity
  nlinarith [Nat.cast_nonneg (α := ℝ) P.card]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The logarithmic potential bound at the critical ball exponent

Unlike the strictly subcritical energy estimate, the finite critical estimate
has one bounded contribution per dyadic scale. It is used on the outer
intervals of the radial profile argument.
-/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [PseudoMetricSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

theorem regularized_potential_critical (μ : Measure X) (x : X)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hball : ∀ n : ℕ, n ≤ g+k →
      μ (ball x (1/(2:ℝ)^n)) ≤ ENNReal.ofReal (K*(1/(2:ℝ)^n)^q)) :
    (∫⁻ y in ball x (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist x y+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  apply (regularized_potential_dyadic μ x hq g k).trans
  have hstart : ENNReal.ofReal (((2:ℝ)^g)^q)*μ (ball x (1/(2:ℝ)^g)) ≤
      ENNReal.ofReal K := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^g)^q)*ENNReal.ofReal (K*(1/(2:ℝ)^g)^q) :=
        mul_le_mul_right (hball g (by omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^g)^q)*(1/(2:ℝ)^g)^q) := by ring
          _ = K := by rw [dyadic_potential_start,sub_self,Real.rpow_zero,mul_one]
  have hterm (j : ℕ) (hj : j ∈ Finset.range k) :
      ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*μ (ball x (1/(2:ℝ)^(g+j))) ≤
      ENNReal.ofReal (K*(2:ℝ)^q) := by
    calc
      _ ≤ ENNReal.ofReal (((2:ℝ)^(g+j+1))^q)*
          ENNReal.ofReal (K*(1/(2:ℝ)^(g+j))^q) :=
        mul_le_mul_right (hball (g+j) (by have := Finset.mem_range.mp hj; omega)) _
      _ = _ := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        calc
          _ = K*((((2:ℝ)^(g+j+1))^q)*(1/(2:ℝ)^(g+j))^q) := by ring
          _ = K*(2:ℝ)^q := by
            rw [dyadic_potential_weight,sub_self,Real.rpow_zero,mul_one]
  calc
    _ ≤ ENNReal.ofReal K+∑ j ∈ Finset.range k, ENNReal.ofReal (K*(2:ℝ)^q) :=
      add_le_add hstart (Finset.sum_le_sum hterm)
    _ = _ := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalScalarPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical dyadic inverse potentials of a nonnegative statistic -/

namespace Falconer
open Set Metric MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem regularized_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q) := by
  have hpre (j : ℕ) : a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^j) = {x | a x < 1/(2:ℝ)^j} := by
    ext x
    simp only [mem_preimage,mem_ball,Real.dist_eq,sub_zero,abs_of_nonneg (ha0 x),mem_ofPred_eq]
  have hball (j : ℕ) (hj : j ≤ g+k) :
      (Measure.map a μ) (ball (0:ℝ) (1/(2:ℝ)^j)) ≤
        ENNReal.ofReal (K*(1/(2:ℝ)^j)^q) := by
    rw [Measure.map_apply ha measurableSet_ball,hpre]
    exact hsmall j hj
  have hh := regularized_potential_critical (Measure.map a μ) (0:ℝ) hq g k hball
  have hf : Measurable (fun z : ℝ =>
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q)) := by fun_prop
  have he : (∫⁻ z in ball (0:ℝ) (1/(2:ℝ)^g),
      ENNReal.ofReal ((1/(dist 0 z+1/(2:ℝ)^(g+k)))^q) ∂Measure.map a μ) =
      ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
    rw [← lintegral_indicator measurableSet_ball,lintegral_map
      (hf.indicator measurableSet_ball) ha,
      ← lintegral_indicator (measurableSet_lt ha measurable_const)]
    apply lintegral_congr
    intro x
    by_cases hx : a x < 1/(2:ℝ)^g
    · have hz : a x ∈ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∈ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_mem hz,indicator_of_mem (show x ∈ {x | a x < 1/(2:ℝ)^g} from hx)]
      simp only [Real.dist_eq,zero_sub,abs_neg,abs_of_nonneg (ha0 x)]
    · have hz : a x ∉ ball (0:ℝ) (1/(2:ℝ)^g) := by
        change x ∉ a ⁻¹' ball (0:ℝ) (1/(2:ℝ)^g)
        rw [hpre]
        exact hx
      rw [indicator_of_notMem hz,indicator_of_notMem (show x ∉ {x | a x < 1/(2:ℝ)^g} from hx)]
  rw [he] at hh
  exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_CriticalTruncatedPotential
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # Critical maximum-truncated potentials with logarithmic scale loss -/

namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {X : Type*} [MeasurableSpace X]

theorem truncated_scalar_potential_critical (μ : Measure X) (a : X → ℝ)
    (ha : Measurable a) (ha0 : ∀ x, 0 ≤ a x)
    {K q : ℝ} (hq : 0 ≤ q) (g k : ℕ)
    (hsmall : ∀ j : ℕ, j ≤ g+k →
      μ {x | a x < 1/(2:ℝ)^j} ≤ ENNReal.ofReal (K*(1/(2:ℝ)^j)^q)) :
    (∫⁻ x in {x | a x < 1/(2:ℝ)^g},
      ENNReal.ofReal ((1/max (a x) (1/(2:ℝ)^(g+k)))^q) ∂μ) ≤
      ENNReal.ofReal ((2:ℝ)^q)*
        (ENNReal.ofReal K+(k:ℝ≥0∞)*ENNReal.ofReal (K*(2:ℝ)^q)) := by
  have hp (x : X) : (1/max (a x) (1/(2:ℝ)^(g+k)))^q ≤
      (2:ℝ)^q*(1/(a x+1/(2:ℝ)^(g+k)))^q := by
    have hax := ha0 x
    calc
      _ ≤ (2/(a x+1/(2:ℝ)^(g+k)))^q := Real.rpow_le_rpow (by positivity)
        (inverse_max_le_two_inverse_add (ha0 x) (by positivity)) hq
      _ = _ := by
        rw [show 2/(a x+1/(2:ℝ)^(g+k)) = 2*(1/(a x+1/(2:ℝ)^(g+k))) by ring,
          Real.mul_rpow (by norm_num) (by positivity)]
  calc
    _ ≤ ∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((2:ℝ)^q)*ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ := by
      apply lintegral_mono
      intro x
      dsimp only
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hp x)
    _ = ENNReal.ofReal ((2:ℝ)^q)*(∫⁻ x in {x | a x < 1/(2:ℝ)^g},
        ENNReal.ofReal ((1/(a x+1/(2:ℝ)^(g+k)))^q) ∂μ) :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl
      (regularized_scalar_potential_critical μ a ha ha0 hq g k hsmall)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Graphs_GraphBallCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual graph edges in a narrow Cartesian strip are covered by planar
balls. The count retains every neighbor, rather than only one witness. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem normalized_ball_bound_all_radii {δ t K : ℝ} {G : Finset (Space 2)}
    (ht : 0 ≤ t) (hK : 1 ≤ K) (hG : NormalizedFiniteBallBound δ t K G)
    (z : Space 2) (r : ℝ) (hr : δ ≤ r) :
    ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ K*r^t*(G.card:ℝ) := by
  by_cases hr1 : r ≤ 1
  · exact hG z r hr hr1
  · have hrpos : 1 ≤ r := le_of_lt (lt_of_not_ge hr1)
    have hp : 1 ≤ r^t := Real.one_le_rpow hrpos ht
    have hc : ((G.filter fun p => dist p z ≤ r).card:ℝ) ≤ (G.card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_filter_le _ _)
    have hk : 1 ≤ K*r^t := by nlinarith
    exact hc.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) G.card])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CoarsePlanarRounding
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common coarse grid inside the original chart and the resulting
point-line incidence error. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem coarsePlanarRound_near {Δ : ℝ} (hΔ : 0 < Δ) (p : Space 2) :
    dist p (coarsePlanarRound Δ p) ≤ Δ := by
  have hh := planar_dist_le_coordinate_sum p (coarsePlanarRound Δ p)
  simp only [coarsePlanarRound_zero,coarsePlanarRound_one] at hh
  linarith only [hh,lineGridRound_error hΔ (p 0),lineGridRound_error hΔ (p 1)]

theorem coarsePlanarRound_separated {Δ : ℝ} (hΔ : 0 < Δ) (P : Finset (Space 2)) :
    FiniteSeparatedAt Δ (P.image (coarsePlanarRound Δ)) := by
  intro x hx y hy hxy
  obtain ⟨p,_,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,_,rfl⟩ := Finset.mem_image.mp hy
  apply gridLine_dist_ge hΔ
    (p := (round (p 0/Δ),round (p 1/Δ)))
    (q := (round (q 0/Δ),round (q 1/Δ)))
  intro he
  exact hxy (congrArg (gridLine Δ) he)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CommonTubeCount
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normalized two-point common-tube kernel in the actual line chart. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem common_tube_card_bound {δ r b K : ℝ} (hδ : 0 < δ)
    (hr : 0 < r) (hr1 : r ≤ 1) (hsmall : 16*δ ≤ r)
    (hR1 : 80*δ/r ≤ 1) (hK : 0 ≤ K)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hxy : r ≤ dist x y) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/r)^b*(T.card : ℝ) := by
  let S := T.filter (fun l => TubeIncident δ y l)
  by_cases hS : S.Nonempty
  · obtain ⟨m,hm⟩ := hS
    have hmT := (Finset.mem_filter.mp hm).1
    have hmy := (Finset.mem_filter.mp hm).2
    have hsub : S ⊆ T.filter (fun l => dist l m ≤ 80*δ/r) := by
      intro l hl
      obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
      exact Finset.mem_filter.mpr ⟨hlT,two_point_tube_parameters_close hδ.le hr hr1 hsmall
        hx0 (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy⟩
    have hR0 : δ ≤ 80*δ/r := by
      apply (le_div_iff₀ hr).2
      nlinarith [mul_le_mul_of_nonneg_left hr1 hδ.le]
    exact (show (S.card : ℝ) ≤ (T.filter (fun l => dist l m ≤ 80*δ/r)).card by
      exact_mod_cast Finset.card_le_card hsub).trans (hball m _ hR0 hR1)
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    change (S.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (by positivity) _)) (Nat.cast_nonneg _)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A common-tube kernel valid at all point separations, including the diagonal. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_bounds {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (x y : Space 2) :
    0 < truncatedPlanarDistance δ x y ∧ truncatedPlanarDistance δ x y ≤ 1 :=
  ⟨hδ.trans_le (le_max_left _ _),max_le hδ1 (min_le_left _ _)⟩

theorem common_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T.filter (fun l => TubeIncident δ y l)).card : ℝ) ≤
      K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  by_cases hsmall : 80*δ ≤ r
  · have hlow : 16*δ ≤ r := by linarith
    have hR : 80*δ/r ≤ 1 := (div_le_one hr).2 hsmall
    have hrδ : δ < r := by linarith
    have hdist : r ≤ dist x y := by
      have hm : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      change max δ (min 1 (dist x y)) ≤ dist x y
      rw [max_eq_right hm.le]
      exact min_le_right _ _
    exact common_tube_card_bound hδ hr hr1 hlow hR (zero_le_one.trans hK)
      T x y hx0 hdist hchart hinc hball
  · have hR : 1 ≤ 80*δ/r := (le_div_iff₀ hr).2 (by linarith)
    have hp : 1 ≤ (80*δ/r)^b := by
      simpa only [Real.one_rpow] using Real.rpow_le_rpow (by norm_num : (0:ℝ) ≤ 1) hR hb
    have hm : 1 ≤ K*(80*δ/r)^b := by nlinarith
    calc
      _ ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_filter_le T _
      _ ≤ _ := by nlinarith [Nat.cast_nonneg (α := ℝ) T.card]

theorem intersect_tube_kernel_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤ K*(80*δ/truncatedPlanarDistance δ x y)^b*(T.card : ℝ) := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    obtain ⟨hlT,hlU⟩ := Finset.mem_inter.mp hl
    exact Finset.mem_filter.mpr ⟨hlT,hy l hlU⟩
  exact (show ((T ∩ U).card : ℝ) ≤ (T.filter (fun l => TubeIncident δ y l)).card by
    exact_mod_cast Finset.card_le_card hsub).trans
      (common_tube_kernel_bound hδ hδ1 hb hK T x y hx0 hchart hx hball)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubePacking
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separation supplies a second common-tube bound, independent of the
pencil cardinality. Interpolating it with regularity detects large pencils. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem common_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hinc : ∀ l ∈ T, TubeIncident δ x l) :
    ((T.filter (fun l => TubeIncident δ y l)).card:ℝ) ≤
      (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  let r := truncatedPlanarDistance δ x y
  obtain ⟨hr,hr1⟩ := truncatedPlanarDistance_bounds hδ hδ1 x y
  change 0 < r at hr
  change r ≤ 1 at hr1
  let S := T.filter fun l => TubeIncident δ y l
  by_cases hsmall : 16*δ ≤ r
  · have hrδ : δ < r := by linarith only [hδ,hsmall]
    have hxy : r ≤ dist x y := by
      have hh : δ < min 1 (dist x y) := (lt_max_iff.mp hrδ).resolve_left (lt_irrefl _)
      exact (max_eq_right hh.le).trans_le (min_le_right _ _)
    by_cases hS : S.Nonempty
    · obtain ⟨m,hm⟩ := hS
      have hmT := (Finset.mem_filter.mp hm).1
      have hmy := (Finset.mem_filter.mp hm).2
      have hball : ∀ l ∈ S, dist l m ≤ 80*δ/r := by
        intro l hl
        obtain ⟨hlT,hly⟩ := Finset.mem_filter.mp hl
        exact two_point_tube_parameters_close hδ.le hr hr1 hsmall hx0
          (hchart l hlT).1 (hchart m hmT).1 (hinc l hlT) hly (hinc m hmT) hmy hxy
      have hb := separated_ball_card S m hδ (by positivity : 0 ≤ 80*δ/r)
        (finiteSeparatedAt_subset (Finset.filter_subset _ _) hsep) hball
      have he : 2*(80*δ/r)/δ+1 = (160+r)/r := by field_simp; ring
      rw [he] at hb
      calc
        _ ≤ ((160+r)/r)^2 := hb
        _ ≤ (161/r)^2 := by gcongr; linarith only [hr1]
        _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring
    · change (S.card:ℝ) ≤ _
      rw [show S = ∅ from Finset.not_nonempty_iff_eq_empty.mp hS]
      simp only [Finset.card_empty,Nat.cast_zero]
      positivity
  · have hball : ∀ l ∈ T, dist l 0 ≤ 2 := by
      intro l hl
      have hh := planar_dist_le_coordinate_sum l 0
      simp only [PiLp.zero_apply,sub_zero] at hh
      linarith only [hh,(hchart l hl).1,(hchart l hl).2]
    have hb := separated_ball_card T 0 hδ (by norm_num : (0:ℝ) ≤ 2) hsep hball
    have hratio : 4/δ+1 ≤ 80/r := by
      apply (le_div_iff₀ hr).2
      have hrδ : r ≤ 16*δ := (lt_of_not_ge hsmall).le
      have hrd : r/δ ≤ 16 := (div_le_iff₀ hδ).2 hrδ
      calc
        (4/δ+1)*r = 4*(r/δ)+r := by ring
        _ ≤ 4*16+1 := by gcongr
        _ ≤ 80 := by norm_num
    calc
      _ ≤ (T.card:ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ (4/δ+1)^2 := by norm_num only [show (2:ℝ)*2 = 4 by norm_num] at hb; exact hb
      _ ≤ (80/r)^2 := by gcongr
      _ ≤ (161/r)^2 := by gcongr; norm_num
      _ = _ := by change (161/r)^2 = 25921*(1/r)^2; ring

theorem intersect_tube_packing_bound {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤ (25921:ℝ)*(1/truncatedPlanarDistance δ x y)^2 := by
  have hsub : T ∩ U ⊆ T.filter (fun l => TubeIncident δ y l) := by
    intro l hl
    exact Finset.mem_filter.mpr ⟨(Finset.mem_inter.mp hl).1,hy l (Finset.mem_inter.mp hl).2⟩
  exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans
    (common_tube_packing_bound hδ hδ1 T x y hx0 hchart hsep hx)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_CommonTubePower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Separating the scale power from the truncated common-tube kernel. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem truncatedPlanarDistance_inverse_power_le {δ b : ℝ} (_hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (x y : Space 2) :
    (1/truncatedPlanarDistance δ x y)^b ≤
      1+(1/max (dist x y) δ)^b := by
  rcases le_total (dist x y) 1 with hd | hd
  · simp only [truncatedPlanarDistance,min_eq_right hd,max_comm δ (dist x y)]
    linarith
  · simp only [truncatedPlanarDistance,min_eq_left hd,max_eq_right hδ1,
      div_one,Real.one_rpow]
    have hp : 0 ≤ (1/max (dist x y) δ)^b := by positivity
    linarith

theorem intersect_tube_power_bound {δ b K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hb : 0 ≤ b) (hK : 1 ≤ K) (T U : Finset (Space 2)) (x y : Space 2)
    (hx0 : |x 0| ≤ 1) (hchart : InBoundedLineChart T)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l)
    (hball : NormalizedFiniteBallBound δ b K T) :
    ((T ∩ U).card : ℝ) ≤
      (K*(80*δ)^b*(T.card : ℝ))*(1+(1/max (dist x y) δ)^b) := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have he : (80*δ/truncatedPlanarDistance δ x y)^b =
      (80*δ)^b*(1/truncatedPlanarDistance δ x y)^b := by
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    ring
  have hh := intersect_tube_kernel_bound hδ hδ1 hb hK T U x y hx0 hchart hx hy hball
  rw [he] at hh
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y (b := b))
    (show 0 ≤ K*(80*δ)^b*(T.card : ℝ) by positivity)
  convert hp using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_InterpolatedTubeKernel
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolation of the regularity and separation bounds on a common
pencil. The intermediate potential exponent stays strictly below the point
dimension, so only the already proved finite geometric-series bound is used. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem interpolate_two_power_bounds {z A B r s u θ : ℝ}
    (hz : 0 ≤ z) (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 < r)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (hfirst : z ≤ A*r^s) (hsecond : z ≤ B*r^2) :
    z ≤ A^θ*B^(1-θ)*r^u := by
  by_cases hz0 : z = 0
  · rw [hz0]
    positivity
  have hzpos : 0 < z := lt_of_le_of_ne hz (Ne.symm hz0)
  calc
    z = z^θ*z^(1-θ) := by rw [← Real.rpow_add hzpos]; norm_num
    _ ≤ (A*r^s)^θ*(B*r^2)^(1-θ) := by
      exact mul_le_mul (Real.rpow_le_rpow hz hfirst hθ.le)
        (Real.rpow_le_rpow hz hsecond (by linarith only [hθ1]))
        (Real.rpow_nonneg hz _) (by positivity)
    _ = A^θ*B^(1-θ)*r^u := by
      rw [Real.mul_rpow hA (Real.rpow_nonneg hr.le _),
        Real.mul_rpow hB (sq_nonneg r),← Real.rpow_mul hr.le,
        ← Real.rpow_natCast_mul hr.le 2 (1-θ)]
      norm_num only [Nat.cast_ofNat]
      rw [show A^θ*r^(s*θ)*(B^(1-θ)*r^(2*(1-θ))) =
        (A^θ*B^(1-θ))*(r^(s*θ)*r^(2*(1-θ))) by ring,
        ← Real.rpow_add hr,he]

theorem intersect_tube_interpolated_bound {δ s u θ K M : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (T U : Finset (Space 2)) (x y : Space 2) (hx0 : |x 0| ≤ 1)
    (hchart : InBoundedLineChart T) (hsep : FiniteSeparatedAt δ T)
    (hball : NormalizedFiniteBallBound δ s K T) (hM : (T.card:ℝ) ≤ M)
    (hx : ∀ l ∈ T, TubeIncident δ x l) (hy : ∀ l ∈ U, TubeIncident δ y l) :
    ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)*(1/truncatedPlanarDistance δ x y)^u := by
  have hr := (truncatedPlanarDistance_bounds hδ hδ1 x y).1
  have hm0 : 0 ≤ M := (Nat.cast_nonneg _).trans hM
  have hfirst : ((T ∩ U).card:ℝ) ≤
      (K*(80*δ)^s*M)*(1/truncatedPlanarDistance δ x y)^s := by
    have hh := intersect_tube_kernel_bound hδ hδ1 hs hK T U x y hx0 hchart hx hy hball
    rw [show 80*δ/truncatedPlanarDistance δ x y =
      (80*δ)*(1/truncatedPlanarDistance δ x y) by ring,
      Real.mul_rpow (by positivity : 0 ≤ 80*δ) (by positivity)] at hh
    calc
      _ ≤ _ := hh
      _ = (K*(80*δ)^s*(T.card:ℝ))*(1/truncatedPlanarDistance δ x y)^s := by ring
      _ ≤ _ := by gcongr
  exact interpolate_two_power_bounds (Nat.cast_nonneg _) (by positivity)
    (by norm_num) (by positivity) hθ hθ1 he hfirst
    (intersect_tube_packing_bound hδ hδ1 T U x y hx0 hchart hsep hx hy)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PointSamples
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Separated point sets from samples with repeated coordinates

A maximal separated subfamily covers the sampled coordinates. The bound
on the multiplicity in a small ball then controls the loss in cardinality.
This is the point-selection step of `ang:planar-measures`.
-/

namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem exists_separated_cover (S : Finset (Space 2)) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ P : Finset (Space 2), P ⊆ S ∧ FiniteSeparatedAt δ P ∧
      ∀ x ∈ S, ∃ y ∈ P, dist x y ≤ δ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simp [FiniteSeparatedAt], by simp⟩
  | @insert x S _ ih =>
    obtain ⟨P, hPS, hsep, hcover⟩ := ih
    by_cases hx : ∃ y ∈ P, dist x y ≤ δ
    · refine ⟨P, hPS.trans (Finset.subset_insert _ _), hsep, ?_⟩
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hx
      · exact hcover z hz
    · refine ⟨insert x P, Finset.insert_subset_insert x hPS, ?_, ?_⟩
      · intro u hu v hv hne
        rcases Finset.mem_insert.mp hu with hue | huP
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · exact (hne (hue.trans hve.symm)).elim
          · rw [hue]
            exact (lt_of_not_ge (fun h => hx ⟨v, hvP, h⟩)).le
        · rcases Finset.mem_insert.mp hv with hve | hvP
          · rw [hve, dist_comm]
            exact (lt_of_not_ge (fun h => hx ⟨u, huP, h⟩)).le
          · exact hsep u huP v hvP hne
      · intro z hz
        rcases Finset.mem_insert.mp hz with hzx | hz
        · exact ⟨x, Finset.mem_insert_self _ _, by simpa only [hzx, dist_self] using hδ⟩
        · obtain ⟨y, hy, hdist⟩ := hcover z hz
          exact ⟨y, Finset.mem_insert_of_mem hy, hdist⟩

/-- Covering the original labels by the selected point balls gives the
lower cardinality bound, with all repeated labels counted. -/
theorem selected_points_card_lower {ι : Type*} [DecidableEq ι]
    (D : Finset ι) (p : ι → Space 2) (P : Finset (Space 2))
    {δ L : ℝ} (hcover : ∀ i ∈ D, ∃ x ∈ P, dist (p i) x ≤ δ)
    (hcount : ∀ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) ≤ L) :
    (D.card : ℝ) ≤ (P.card : ℝ) * L := by
  classical
  have hsub : D ⊆ P.biUnion (fun x => D.filter (fun i => dist (p i) x ≤ δ)) := by
    intro i hi
    obtain ⟨x, hx, hdist⟩ := hcover i hi
    exact Finset.mem_biUnion.mpr ⟨x, hx, Finset.mem_filter.mpr ⟨hi, hdist⟩⟩
  calc
    (D.card : ℝ) ≤ ((P.biUnion (fun x => D.filter
        (fun i => dist (p i) x ≤ δ))).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ x ∈ P, ((D.filter (fun i => dist (p i) x ≤ δ)).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _x ∈ P, L := Finset.sum_le_sum hcount
    _ = (P.card : ℝ) * L := by simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRows
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The robust projection theorem in the original coordinates of one
coarse cell. No projected point or fine-scale witness is replaced. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localPacketPoint Δ y a) := by
  intro p q he
  have h0 := congrArg (fun z : Space 2 => z 0) he
  have h1 := congrArg (fun z : Space 2 => z 1) he
  change (p 0-y)/Δ = (q 0-y)/Δ at h0
  change (p 1-a)/Δ = (q 1-a)/Δ at h1
  have he0 := (div_left_inj' hΔ.ne').1 h0
  have he1 := (div_left_inj' hΔ.ne').1 h1
  ext i
  fin_cases i
  · change p 0 = q 0
    linarith only [he0]
  · change p 1 = q 1
    linarith only [he1]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPacketRegularity
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact similarity and regularity of the original points in a local
packet chart. The only cost is the explicit cardinality restriction. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_eq_smul {Δ : ℝ} (y a : ℝ) (p : Space 2) :
    localPacketPoint Δ y a p = Δ⁻¹ • (p-rowPoint y a) := by
  ext i
  fin_cases i <;> simp [localPacketPoint,div_eq_mul_inv,mul_comm]

theorem localPacketPoint_dist {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (p q : Space 2) :
    dist (localPacketPoint Δ y a p) (localPacketPoint Δ y a q) = dist p q/Δ := by
  rw [localPacketPoint_eq_smul,localPacketPoint_eq_smul,dist_smul₀,
    dist_sub_right,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hΔ),div_eq_mul_inv,mul_comm]

theorem localPacketPoint_inverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) (z : Space 2) :
    localPacketPoint Δ y a (Δ • z+rowPoint y a) = z := by
  rw [localPacketPoint_eq_smul,add_sub_cancel_right,smul_smul,inv_mul_cancel₀ hΔ.ne',one_smul]

theorem localPacketPoint_regular {δ Δ t K : ℝ} (hδ : 0 < δ) (hΔ : 0 < Δ)
    (hΔ1 : Δ ≤ 1) (y a : ℝ) (P : Finset (Space 2))
    (hreg : NormalizedFiniteBallBound δ t K P) :
    NormalizedFiniteBallBound (δ/Δ) t (K*Δ^t) (P.image (localPacketPoint Δ y a)) := by
  intro z r hr hr1
  have hr0 : 0 < r := (div_pos hδ hΔ).trans_le hr
  have hδr : δ ≤ Δ*r := by nlinarith only [(div_le_iff₀ hΔ).1 hr]
  have hΔr : Δ*r ≤ 1 := (mul_le_mul hΔ1 hr1 hr0.le (by norm_num)).trans_eq (by norm_num)
  have hsub : (P.image (localPacketPoint Δ y a)).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).image (localPacketPoint Δ y a) := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have he := localPacketPoint_dist hΔ y a x (Δ • z+rowPoint y a)
    rw [localPacketPoint_inverse hΔ] at he
    rw [he] at hpr
    nlinarith only [(div_le_iff₀ hΔ).1 hpr]
  rw [Finset.card_image_of_injective _ (localPacketPoint_injective hΔ y a)]
  calc
    _ ≤ ((P.filter (fun p => dist p (Δ • z+rowPoint y a) ≤ Δ*r)).card:ℝ) := by
      exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
    _ ≤ K*(Δ*r)^t*(P.card:ℝ) := hreg _ _ hδr hΔr
    _ = _ := by rw [Real.mul_rpow hΔ.le hr0.le]; ring

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
-- module Solutions.OAIQ088_FD.Falconer_Measures_PrefixMass
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # All-dimensional PrefixMass for regularized original measures -/

namespace Falconer.Regularization
variable {d : ℕ}

open Set MeasureTheory
open scoped ENNReal

theorem descendant_subset_take (Q : DyadicCube d) (_hQ : 0 < Q.side)
    (p : CellPath d) (a : ℕ) : (Q.descendant p).carrier ⊆ (Q.descendant (p.take a)).carrier := by
  have he := Q.descendant_append (p.take a) (p.drop a)
  rw [List.take_append_drop] at he
  rw [he]
  exact (Q.descendant (p.take a)).descendant_subset _

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PlanarLeafInjection
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Inject the original separated point set into sufficiently small dyadic
leaves, preserving the exact finite prefix counts. -/
namespace Falconer
open Set
open Regularization
attribute [local instance] Classical.propDecidable

theorem leaf_image_prefixFiber (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (k : ℕ) (p : CellPath 2) :
    prefixFiber (P.image l) k p = (P.filter fun x => (l x).take k = p).image l := by
  classical
  ext q
  simp only [prefixFiber,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,hx,rfl⟩,hp⟩
    exact ⟨x,⟨hx,hp⟩,rfl⟩
  · rintro ⟨x,⟨hx,hp⟩,rfl⟩
    exact ⟨⟨x,hx,rfl⟩,hp⟩

theorem leaf_image_prefixFiber_card {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2))) (k : ℕ) (p : CellPath 2) :
    (prefixFiber (P.image l) k p).card = (P.filter fun x => (l x).take k = p).card := by
  classical
  rw [leaf_image_prefixFiber]
  exact Finset.card_image_iff.mpr (hl.mono (by intro x hx; exact (Finset.mem_filter.mp hx).1))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_PointBallCounts
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer finite prefix bounds to geometric closed-ball counts. The
factor 7^d is the existing bounded overlap of dyadic cubes. -/
namespace Falconer
open Set Metric Regularization

theorem pointPrefixFiber_card_eq {P : Finset (Space 2)} {l : Space 2 → CellPath 2}
    (hl : Set.InjOn l (P : Set (Space 2))) (n : ℕ) (q : CellPath 2) :
    (pointPrefixFiber P l n q).card = (prefixFiber (P.image l) n q).card :=
  (leaf_image_prefixFiber_card hl n q).symm

theorem finite_point_ball_count {d N n : ℕ} (Q : DyadicCube d) (hQ : 0 < Q.side)
    {P : Finset (Space d)} {l : Space d → CellPath d}
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths d N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) {r M : ℝ} (hr : 0 < r) (hM : 0 ≤ M)
    (hscale : 2*r ≤ Q.side/(2 : ℝ)^n)
    (hfiber : ∀ q ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n q).card : ℝ) ≤ M) (z : Space d) :
    ((P.filter fun x => dist x z ≤ r).card : ℝ) ≤ (7^d : ℕ)*M := by
  classical
  let S := P.filter fun x => dist x z ≤ r
  let H := cubeBallHits Q n z (2*r)
  have hmap (x : Space d) (hx : x ∈ S) : (l x).take n ∈ H := by
    obtain ⟨hxP,hxz⟩ := Finset.mem_filter.mp hx
    have hl := hleaf x hxP
    apply (mem_cubeBallHits Q n z (2*r) _).2
    refine ⟨?_,x,descendant_subset_take Q hQ _ _ hl.2,?_⟩
    · simp only [List.length_take,(mem_cubePaths _ _ _).mp hl.1,Nat.min_eq_left hn]
    · exact mem_ball.mpr (by linarith)
  have hsum : (S.card : ℝ) = ∑ q ∈ H,
      ((S.filter fun x => (l x).take n = q).card : ℝ) := by
    exact_mod_cast Finset.card_eq_sum_card_fiberwise hmap
  calc
    _ = ∑ q ∈ H, ((S.filter fun x => (l x).take n = q).card : ℝ) := hsum
    _ ≤ ∑ _q ∈ H, M := by
      apply Finset.sum_le_sum
      intro q hq
      by_cases hex : (S.filter fun x => (l x).take n = q).Nonempty
      · obtain ⟨x,hx⟩ := hex
        obtain ⟨hxS,hxq⟩ := Finset.mem_filter.mp hx
        have hxP := (Finset.mem_filter.mp hxS).1
        have hqi : q ∈ (P.image l).image (List.take n) := by
          exact Finset.mem_image.mpr ⟨l x,Finset.mem_image.mpr ⟨x,hxP,rfl⟩,hxq⟩
        have hsub : (S.filter fun x => (l x).take n = q) ⊆ pointPrefixFiber P l n q := by
          intro y hy
          obtain ⟨hyS,hyq⟩ := Finset.mem_filter.mp hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hyS).1,hyq⟩
        exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hfiber q hqi)
      · rw [Finset.not_nonempty_iff_eq_empty.mp hex,Finset.card_empty,Nat.cast_zero]
        exact hM
    _ = (H.card : ℝ)*M := by simp
    _ ≤ (7^d : ℕ)*M := by
      apply mul_le_mul_of_nonneg_right _ hM
      exact_mod_cast cubeBallHits_card Q hQ n z hscale

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PrefixCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Actual dyadic parent centers and the original finite fibers over them. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem DyadicCube.center_coordinate_bound (Q : DyadicCube 2) {x : Space 2}
    (hx : x ∈ Q.carrier) (i : Fin 2) : |x i-Q.center i| ≤ Q.side/2 := by
  have hi := hx i
  change |x i-(Q.origin i+Q.side/2)| ≤ Q.side/2
  rw [abs_le]
  constructor <;> linarith

theorem DyadicCube.center_injective_at_depth (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {n : ℕ} {p q : CellPath 2} (hp : p.length = n) (hq : q.length = n)
    (he : (Q.descendant p).center = (Q.descendant q).center) : p = q := by
  by_contra hne
  have hh := Q.centers_separated hQ hp hq hne
  rw [he,dist_self] at hh
  exact (not_le_of_gt (by positivity : 0 < Q.side/(2:ℝ)^n)) hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarPathCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Realize a finite planar path set by its actual dyadic centers, with an
exact inverse coding. Prefix masses and cardinalities are unchanged. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_path_center_realization {N : ℕ} (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (L : Finset (CellPath 2)) (hL : L ⊆ cubePaths 2 N) :
    ∃ l : Space 2 → CellPath 2,
      let P := L.image (fun p => (Q.descendant p).center)
      (∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier) ∧
      Set.InjOn l (P : Set (Space 2)) ∧ P.image l = L ∧
      FiniteSeparatedAt (Q.side/(2:ℝ)^N) P := by
  let C := fun p : CellPath 2 => (Q.descendant p).center
  have hC : Set.InjOn C (L : Set (CellPath 2)) := by
    intro p hp q hq he
    exact Q.center_injective_at_depth hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) he
  let l := Function.invFunOn C (L : Set (CellPath 2))
  have hl (p : CellPath 2) (hp : p ∈ L) : l (C p) = p := hC.leftInvOn_invFunOn hp
  refine ⟨l,?_,?_,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    rw [hl p hp]
    exact ⟨hL hp,(Q.descendant p).center_mem (Q.descendant_side_pos hQ p)⟩
  · intro x hx y hy he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    rw [hl p hp,hl q hq] at he
    exact congrArg C he
  · ext p
    constructor
    · intro hp
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hx
      rwa [hl q hq]
    · intro hp
      exact Finset.mem_image.mpr ⟨C p,Finset.mem_image_of_mem C hp,hl p hp⟩
  · intro x hx y hy hxy
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
    exact Q.centers_separated hQ ((mem_cubePaths _ _ _).mp (hL hp))
      ((mem_cubePaths _ _ _).mp (hL hq)) (fun he => hxy (congrArg C he))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarPrefixTruncation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact planar prefix identities at the endpoint of a profile interval. -/
namespace Falconer.Regularization

theorem planar_prefix_image_take_take (L : Finset (CellPath 2)) {a t : ℕ} (hat : a ≤ t) :
    (L.image (List.take t)).image (List.take a) = L.image (List.take a) := by
  classical
  simp only [Finset.image_image,Function.comp_def,List.take_take,min_eq_left hat]

theorem planar_prefix_image_take_cubePaths {N t : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (ht : t ≤ N) : L.image (List.take t) ⊆ cubePaths 2 t := by
  classical
  intro p hp
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
  have hlen := (mem_cubePaths 2 N q).mp (hL hq)
  simp only [mem_cubePaths,List.length_take,hlen,min_eq_left ht]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalPrefixCenters
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Geometric realization of the endpoint cells inside their actual parent.
The local similarity preserves the number of cells and gives the separation
at the relative depth, as well as a bounded point chart. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem localPacketPoint_separated {δ Δ : ℝ} (hΔ : 0 < Δ) (y c : ℝ)
    (P : Finset (Space 2)) (hP : FiniteSeparatedAt δ P) :
    FiniteSeparatedAt (δ/Δ) (P.image (localPacketPoint Δ y c)) := by
  intro x hx z hz hxz
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
  rw [localPacketPoint_dist hΔ]
  exact div_le_div_of_nonneg_right
    (hP p hp q hq (fun he => hxz (congrArg (localPacketPoint Δ y c) he))) hΔ.le

theorem local_prefix_centers_geometry {N a b : ℕ} (Q : DyadicCube 2)
    (hQ : Q.side = 1) (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    let D := prefixChildren C a b p₀
    let P := D.image (fun q => (Q.descendant q).center)
    let Z := P.image (localPacketPoint (1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1))
    Z.card = D.card ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) Z := by
  let D := prefixChildren C a b p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hD : D ⊆ cubePaths 2 b :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hC hbN)
  obtain ⟨_,_,_,_,hsep⟩ := planar_path_center_realization Q hQpos D hD
  have hcard : P.card = D.card := by
    apply Finset.card_image_iff.mpr
    intro q hq r hr he
    exact Q.center_injective_at_depth hQpos ((mem_cubePaths _ _ _).mp (hD hq))
      ((mem_cubePaths _ _ _).mp (hD hr)) he
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ (localPacketPoint_injective (by positivity) _ _)]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨hu,hup⟩ := Finset.mem_filter.mp hu
    have hulen := (mem_cubePaths _ _ _).mp (hC hu)
    have hplen : p₀.length = a := by
      rw [← hup,List.length_take,hulen,Nat.min_eq_left (hab.trans hbN)]
    have htake : (u.take b).take a = p₀ := by
      simpa only [List.take_take,Nat.min_eq_left hab] using hup
    have hm := Q.center_mem_ancestor hQpos (u.take b) a
    rw [htake] at hm
    have hside : (Q.descendant p₀).side = 1/(2:ℝ)^a := by
      rw [Q.descendant_side,hplen,hQ]
    have hc (i : Fin 2) :
        |localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0)
          ((Q.descendant p₀).center 1) (Q.descendant (u.take b)).center i| ≤ 1/2 := by
      have hh := (Q.descendant p₀).center_coordinate_bound hm i
      rw [hside] at hh
      fin_cases i
      · change |(Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 0-(Q.descendant p₀).center 0)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
      · change |(Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1| ≤
          (1/(2:ℝ)^a)/2 at hh
        change |((Q.descendant (u.take b)).center 1-(Q.descendant p₀).center 1)/
          (1/(2:ℝ)^a)| ≤ 1/2
        rw [abs_div,abs_of_pos (by positivity : 0 < 1/(2:ℝ)^a)]
        exact (div_le_iff₀ (by positivity : 0 < 1/(2:ℝ)^a)).2 (by linarith only [hh])
    exact ⟨(hc 0).trans (by norm_num),(hc 1).trans (by norm_num)⟩
  · have hh := localPacketPoint_separated (by positivity : 0 < 1/(2:ℝ)^a)
      ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1) P hsep
    have he : (Q.side/(2:ℝ)^b)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(b-a) := by
      rw [hQ,show b = (b-a)+a by omega,pow_add]
      field_simp
      congr 1
      omega
    rw [he] at hh
    exact hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParentPrefixRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A recursive restriction pays for its loss within the current parent,
not for the number of unrelated parents in the original configuration. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_prefix_retention {N a : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i : ℕ} (hi : i ≤ K) (ha : a ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  let C₀ := prefixFiber C a r
  have hC₀ : C₀ ⊆ C := Finset.filter_subset _ _
  have hprefix (u : CellPath 2) (hu : u ∈ C₀.image (List.take (blockDepth N B i))) :
      prefixFiber C₀ (blockDepth N B i) u = prefixFiber C (blockDepth N B i) u :=
    prefixFiber_parent_filter ha hu
  have hret := prefix_fiber_local_retention
    (b := (blockProduct L (blockLabel L N B f K) N B i p:ℝ))
    C₀ S (blockDepth N B i) hsub hM
    (by positivity : 0 ≤ (2:ℝ)^i) (by positivity : 0 ≤ (2:ℝ)^i)
    (Nat.cast_nonneg (blockProduct L' (blockLabel L' N B g K) N B i q)) hmass
    (fun u hu => by
      rw [hprefix u hu]
      exact_mod_cast blockClass_leaf_count hL B f K p hi (Finset.image_subset_image hC₀ hu))
    (fun u hu => by exact_mod_cast blockClass_leaf_count hL' B g K q hi hu) hp₀
  rw [hprefix p₀ (Finset.image_subset_image hsub hp₀)] at hret
  convert hret using 1
  all_goals try with_reducible_and_instances rfl
  rw [show 2*i = i+i by omega,pow_add]
  ring

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ParentChildRetention
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint retention after restricting inside one actual recursive parent. -/
namespace Falconer.Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_child_retention {N a : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a r₀).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha : a ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    ((prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) ≤
      (M*(2:ℝ)^(2*i+2*j))*
        ((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ) := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  have hsubC : S ⊆ C := hsub.trans (Finset.filter_subset _ _)
  let u : ℝ := blockProduct L (blockLabel L N B f K) N B j p
  let v : ℝ := blockProduct L' (blockLabel L' N B g K) N B j q
  have hu : 0 < u := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hc (r : CellPath 2) (hr : r ∈ C.image (List.take (blockDepth N B j))) :
      u ≤ ((prefixFiber C (blockDepth N B j) r).card:ℝ) ∧
      ((prefixFiber C (blockDepth N B j) r).card:ℝ) ≤ (2:ℝ)^j*u := by
    dsimp only [u,C]
    exact_mod_cast blockClass_leaf_count hL B f K p (hji.trans hi) hr
  have hs (r : CellPath 2) (hr : r ∈ S.image (List.take (blockDepth N B j))) :
      v ≤ ((prefixFiber S (blockDepth N B j) r).card:ℝ) ∧
      ((prefixFiber S (blockDepth N B j) r).card:ℝ) ≤ (2:ℝ)^j*v := by
    dsimp only [v,S]
    exact_mod_cast blockClass_leaf_count hL' B g K q (hji.trans hi) hr
  obtain ⟨z,hz⟩ := prefixFiber_nonempty hp₀
  let r := z.take (blockDepth N B j)
  have hrS : r ∈ S.image (List.take (blockDepth N B j)) :=
    Finset.mem_image_of_mem _ (Finset.mem_filter.mp hz).1
  have hrC : r ∈ C.image (List.take (blockDepth N B j)) := Finset.image_subset_image hsubC hrS
  have hvu : v ≤ (2:ℝ)^j*u := by
    apply (hs r hrS).1.trans
    apply le_trans _ (hc r hrC).2
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ hsubC)
  have hCmass := (prefix_children_mass_bounds C (blockDepth_antitone N B hji) p₀
    (fun r hr => hc r (prefixChildren_mem_image hr))).1
  have hSmass := (prefix_children_mass_bounds S (blockDepth_antitone N B hji) p₀
    (fun r hr => hs r (prefixChildren_mem_image hr))).2
  have hretain := blockClass_parent_prefix_retention hL hL' B f g K p q r₀ hsub hM hmass hi ha hp₀
  apply (mul_le_mul_iff_left₀ hu).1
  calc
    _ ≤ ((prefixFiber C (blockDepth N B i) p₀).card:ℝ) := hCmass
    _ ≤ (M*(2:ℝ)^(2*i))*((prefixFiber S (blockDepth N B i) p₀).card:ℝ) := hretain
    _ ≤ (M*(2:ℝ)^(2*i))*
        (((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*v)) :=
      mul_le_mul_of_nonneg_left hSmass (by positivity)
    _ ≤ (M*(2:ℝ)^(2*i))*
        (((prefixChildren S (blockDepth N B i) (blockDepth N B j) p₀).card:ℝ)*((2:ℝ)^j*((2:ℝ)^j*u))) := by
      gcongr
    _ = _ := by
      rw [pow_add,pow_mul]
      ring


end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarQuarter
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction puts the actual two projection coordinates inside
one bounded square without changing their finite combinatorics. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

 theorem planarQuarter_apply (p : Space 2) (i : Fin 2) : planarQuarter p i = p i / 4 := by
  change (1/4:ℝ) * p i = p i / 4
  ring

 theorem planarQuarter_dist (p q : Space 2) :
    dist (planarQuarter p) (planarQuarter q) = dist p q / 4 := by
  rw [planarQuarter,planarQuarter,dist_smul₀]
  norm_num
  ring

 theorem planarQuarter_injective : Function.Injective planarQuarter := by
  intro p q h
  have hh : dist p q / 4 = 0 := by rw [← planarQuarter_dist,h,dist_self]
  exact dist_eq_zero.mp (by linarith)

 theorem planarQuarter_right_inverse (z : Space 2) : planarQuarter ((4:ℝ) • z) = z := by
  ext i
  rw [planarQuarter_apply]
  change 4 * z i / 4 = z i
  ring

 theorem planarQuarter_separated {δ : ℝ} (G : Finset (Space 2))
    (hsep : FiniteSeparatedAt δ G) :
    FiniteSeparatedAt (δ/4) (G.image planarQuarter) := by
  intro p hp q hq hpq
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hq
  rw [planarQuarter_dist]
  exact div_le_div_of_nonneg_right (hsep x hx y hy (fun h => hpq (congrArg _ h))) (by norm_num)

 theorem planarQuarter_regular {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    (G : Finset (Space 2)) (hreg : NormalizedFiniteBallBound δ t K G) :
    NormalizedFiniteBallBound (δ/4) t (K*4^t) (G.image planarQuarter) := by
  classical
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (G.image planarQuarter).filter (fun p => dist p z ≤ r) ⊆
      (G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).image planarQuarter := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := planarQuarter_dist x ((4:ℝ) • z)
    rw [planarQuarter_right_inverse] at hh
    linarith
  have hc : (((G.image planarQuarter).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((G.filter (fun p => dist p ((4:ℝ) • z) ≤ 4*r)).card:ℝ) := by
    exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_image_le
  have hb := normalized_ball_bound_all_radii ht hK hreg ((4:ℝ) • z) (4*r) (by linarith)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le] at hb
  rw [Finset.card_image_of_injective _ planarQuarter_injective]
  exact hc.trans (by nlinarith)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarSquash
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed anisotropic change of coordinates narrows every bounded slope.
The same map acts on points and line parameters; incidence widths contract
by four and both maps have inverse Lipschitz constant sixteen. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planarSquash_leftInverse : Function.LeftInverse planarUnsquash planarSquash := by
  intro p
  ext i
  fin_cases i <;> simp [planarSquash,planarUnsquash,rowPoint] <;> ring

theorem planarSquash_rightInverse : Function.RightInverse planarUnsquash planarSquash := by
  intro p
  ext i
  fin_cases i <;> simp [planarSquash,planarUnsquash,rowPoint]

theorem planarSquash_injective : Function.Injective planarSquash :=
  planarSquash_leftInverse.injective

theorem planarSquash_dist_bounds (p q : Space 2) :
    dist (planarSquash p) (planarSquash q) ≤ dist p q/4 ∧
      dist p q ≤ 16*dist (planarSquash p) (planarSquash q) := by
  have h := EuclideanSpace.dist_sq_eq p q
  have h' := EuclideanSpace.dist_sq_eq (planarSquash p) (planarSquash q)
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h h'
  change dist (planarSquash p) (planarSquash q)^2 =
    (p 0/4-q 0/4)^2+(p 1/16-q 1/16)^2 at h'
  constructor <;> nlinarith [sq_nonneg (p 0-q 0),sq_nonneg (p 1-q 1),
    dist_nonneg (x := p) (y := q),dist_nonneg (x := planarSquash p) (y := planarSquash q)]

theorem planarSquash_separated {δ : ℝ} (P : Finset (Space 2))
    (hP : FiniteSeparatedAt (4*δ) P) :
    FiniteSeparatedAt (δ/4) (P.image planarSquash) := by
  intro x hx y hy hxy
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hy
  have hs := hP p hp q hq (fun he => hxy (congrArg planarSquash he))
  linarith only [hs,(planarSquash_dist_bounds p q).2]

theorem planarSquash_chart (P : Finset (Space 2)) (hP : InBoundedLineChart P) :
    InBoundedLineChart (P.image planarSquash) := by
  intro x hx
  obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hx
  change |p 0/4| ≤ 1 ∧ |p 1/16| ≤ 1
  rw [abs_div,abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4),abs_of_pos (by norm_num : (0:ℝ) < 16)]
  constructor <;> linarith only [(hP p hp).1,(hP p hp).2]

theorem planarSquash_slope {p : Space 2} (hp : |p 0| ≤ 1) :
    |planarSquash p 0| ≤ 1/2 := by
  change |p 0/4| ≤ 1/2
  rw [abs_div]
  norm_num only [abs_of_pos (by norm_num : (0:ℝ) < 4)]
  linarith only [hp]

theorem planarSquash_incident {δ : ℝ} (hδ : 0 ≤ δ) {p l : Space 2}
    (h : TubeIncident δ p l) : TubeIncident (δ/4) (planarSquash p) (planarSquash l) := by
  have hd : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.2 (by positivity)
  have hd' : 0 < Real.sqrt (1+(l 0/4)^2) := Real.sqrt_pos.2 (by positivity)
  have hb : Real.sqrt (1+(l 0)^2) ≤ 4*Real.sqrt (1+(l 0/4)^2) := by
    nlinarith [Real.sq_sqrt (show 0 ≤ 1+(l 0)^2 by positivity),
      Real.sq_sqrt (show 0 ≤ 1+(l 0/4)^2 by positivity)]
  have hh := (div_le_iff₀ hd).1 h
  change |p 1/16-(l 0/4)*(p 0/4)-l 1/16|/Real.sqrt (1+(l 0/4)^2) ≤ δ/4
  rw [show p 1/16-(l 0/4)*(p 0/4)-l 1/16 = (p 1-l 0*p 0-l 1)/16 by ring,
    abs_div,abs_of_pos (by norm_num : (0:ℝ) < 16)]
  apply (div_le_iff₀ hd').2
  nlinarith only [hh,mul_le_mul_of_nonneg_left hb hδ]

theorem planarSquash_regular {δ s K : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (hP : NormalizedFiniteBallBound δ s K P) :
    NormalizedFiniteBallBound (δ/4) s (K*16^s) (P.image planarSquash) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  have hsub : (P.image planarSquash).filter (fun p => dist p z ≤ r) ⊆
      (P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).image planarSquash := by
    intro p hp
    obtain ⟨hp,hpr⟩ := Finset.mem_filter.mp hp
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨hx,?_⟩,rfl⟩
    have hh := (planarSquash_dist_bounds x (planarUnsquash z)).2
    rw [planarSquash_rightInverse z] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hpr (by norm_num))
  have hc : (((P.image planarSquash).filter (fun p => dist p z ≤ r)).card:ℝ) ≤
      ((P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).card:ℝ) :=
    Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
  have hb := normalized_ball_bound_all_radii hs hK hP (planarUnsquash z) (16*r)
    (by linarith only [hr,hδ])
  rw [Finset.card_image_of_injective _ planarSquash_injective]
  calc
    _ ≤ ((P.filter (fun p => dist p (planarUnsquash z) ≤ 16*r)).card:ℝ) := hc
    _ ≤ K*(16*r)^s*(P.card:ℝ) := hb
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 16) hr0.le]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_HalfSlopeGrid
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic nearest-grid rounding preserves the slope interval used by the
recursive cell construction. The endpoints are actual points of the grid. -/
namespace Falconer

theorem dyadic_relative_mesh (a b : ℕ) (hab : a ≤ b) :
    (1/(2:ℝ)^b)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(b-a) := by
  have hp : (2:ℝ)^b = (2:ℝ)^a*(2:ℝ)^(b-a) := by
    rw [← pow_add,Nat.add_sub_of_le hab]
  rw [hp]
  field_simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_LocalPrefixCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prefix covers in the exact local chart used by scale combination. -/
namespace Falconer
open Set Regularization
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_local_prefix_coarse_cover {N n : ℕ} {ρ Δ : ℝ}
    (hρ : 0 < ρ) (hΔ : 0 < Δ) (y a : ℝ)
    (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hn : n ≤ N) (hscale : (Q.side/(2:ℝ)^n)/Δ ≤ ρ) :
    (((P.image (localPacketPoint Δ y a)).image (coarsePlanarRound ρ)).card:ℝ) ≤
      49*(((P.image l).image (List.take n)).card:ℝ) := by
  let F := localPacketPoint Δ y a
  let R := fun x => coarsePlanarRound ρ (F x)
  let C := (P.image l).image (List.take n)
  let S := fun p => (pointPrefixFiber P l n p).image R
  have hsqrt : Real.sqrt (2:ℝ) ≤ 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
  have hS (p : CellPath 2) (hp : p ∈ C) : ((S p).card:ℝ) ≤ 49 := by
    obtain ⟨b,hb,he⟩ := Finset.mem_image.mp hp
    obtain ⟨x,hx,hbx⟩ := Finset.mem_image.mp hb
    have hlen : p.length = n := by
      rw [← he,← hbx,List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hn]
    have hside : (Q.descendant p).side = Q.side/(2:ℝ)^n := by rw [Q.descendant_side,hlen]
    have hwithin : ∀ z ∈ S p, dist z (F (Q.descendant p).center) ≤ 3*ρ := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨hvP,hvp⟩ := Finset.mem_filter.mp hv
      have hvcell := descendant_subset_take Q hQ (l v) n (hleaf v hvP).2
      rw [hvp] at hvcell
      have hd := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hvcell
        ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
      rw [hside] at hd
      have hdf : dist (F v) (F (Q.descendant p).center) ≤ 2*ρ := by
        rw [localPacketPoint_dist hΔ]
        calc
          _ ≤ (Real.sqrt 2*(Q.side/(2:ℝ)^n))/Δ := (div_le_div_iff_of_pos_right hΔ).2 hd
          _ = Real.sqrt 2*((Q.side/(2:ℝ)^n)/Δ) := by ring
          _ ≤ 2*ρ := mul_le_mul hsqrt hscale (by positivity) (by norm_num)
      exact (dist_triangle (R v) (F v) (F (Q.descendant p).center)).trans
        ((add_le_add (by simpa only [dist_comm] using coarsePlanarRound_near hρ (F v)) hdf).trans_eq (by ring))
    have hsep : FiniteSeparatedAt ρ (S p) := by
      have hh := coarsePlanarRound_separated hρ (P.image F)
      apply finiteSeparatedAt_subset (P := (P.image F).image (coarsePlanarRound ρ)) _ hh
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem F (Finset.mem_filter.mp hv).1)
    have hh := separated_ball_card (S p) (F (Q.descendant p).center) hρ
      (r := 3*ρ) (by positivity) hsep hwithin
    have heq : (2*(3*ρ)/ρ+1)^2 = (49:ℝ) := by field_simp; ring
    rwa [heq] at hh
  have hcover : P.image R ⊆ C.biUnion S := by
    intro z hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_biUnion.mpr ⟨(l x).take n,
      Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ hx),
      Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)⟩
  change (((P.image F).image (coarsePlanarRound ρ)).card:ℝ) ≤ _
  rw [Finset.image_image]
  calc
    _ ≤ ((C.biUnion S).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ p ∈ C, ((S p).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ C, (49:ℝ) := Finset.sum_le_sum hS
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_LocalProfileCounts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Local covering numbers and fiber ratios expressed in the actual
branching profile, for the regular-scale incidence argument. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockProduct_relative_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    (B K : ℕ) (p : CellPath d) {i j : ℕ} (hi : i ≤ K) (hj : j ≤ K) :
    (blockProduct L F N B i p : ℝ)/(blockProduct L F N B j p : ℝ) =
      (2 : ℝ)^((N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
        regularizedProfile L F N B K p (blockDepth N B i))) := by
  rw [blockProduct_profile_difference hN hL F B K p hi,
    blockProduct_profile_difference hN hL F B K p hj,
    ← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem blockClass_local_covering_count {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let T := prefixChildren C (blockDepth N B i) (blockDepth N B j) P
    let X := (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
      regularizedProfile L F N B K p (blockDepth N B i))
    (2 : ℝ)^X/(2 : ℝ)^j ≤ T.card ∧ (T.card : ℝ) ≤ (2 : ℝ)^i*(2 : ℝ)^X := by
  have hb := blockClass_descendant_count hL B f K p hji hi hP
  dsimp only at hb ⊢
  rw [blockProduct_relative_profile hN hL _ B K p hi (hji.trans hi)] at hb
  exact hb

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_LocalProfileRegularity
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two directions of the profile/regularity dictionary: a lower chord
bound gives local nonconcentration, and an upper chord bound gives covering. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem blockClass_local_covering {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (B : ℕ) (f : CellPath d → List ℕ) (K : ℕ)
    (p : CellPath d) {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {P : CellPath d}
    (hP : P ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i))) {s A : ℝ}
    (hprofile : let F := blockLabel L N B f K
      (N : ℝ)*(regularizedProfile L F N B K p (blockDepth N B j)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))+A) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    ((prefixChildren C (blockDepth N B i) (blockDepth N B j) P).card : ℝ) ≤
      (2 : ℝ)^i*(2 : ℝ)^(s*((blockDepth N B j : ℝ)-(blockDepth N B i : ℝ))+A) := by
  have hb := (blockClass_local_covering_count hN hL B f K p hji hi hP).2
  dsimp only at hprofile hb ⊢
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by norm_num) hprofile) (by positivity))

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockDepthBracket
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Bracket any intermediate integer depth by an actual selected block.
The loss is at most the original block size, including truncated end blocks. -/
namespace Falconer.Regularization

theorem blockDepth_bracket {N B i j n : ℕ} (hji : j ≤ i)
    (hlo : blockDepth N B i ≤ n) (hhi : n ≤ blockDepth N B j) :
    ∃ k, j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n ∧ n ≤ blockDepth N B k+B := by
  have hex : ∃ k, j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n := ⟨i,hji,le_rfl,hlo⟩
  let k := Nat.find hex
  have hk : j ≤ k ∧ k ≤ i ∧ blockDepth N B k ≤ n := Nat.find_spec hex
  refine ⟨k,hk.1,hk.2.1,hk.2.2,?_⟩
  by_cases he : k = j
  · rw [he]
    omega
  · have hk0 : 0 < k := by omega
    have hp : n < blockDepth N B (k-1) := by
      by_contra hn
      have hm := Nat.find_min hex (show k-1 < k by omega)
      exact hm ⟨by omega,by omega,by omega⟩
    have hgap := blockDepth_gap N B (k-1)
    have horder := blockDepth_antitone N B (show k-1 ≤ k by omega)
    rw [Nat.sub_add_cancel hk0] at hgap
    omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_RescaledConditional
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! # The actual affine rescaling of a conditional class probability -/

namespace Falconer.Regularization
open Set MeasureTheory Metric
open scoped ENNReal
variable {d : ℕ}

theorem dyadic_radius_bracket {m : ℕ} {r : ℝ}
    (hmin : 1/(2:ℝ)^m ≤ r) (hmax : r ≤ 1) :
    ∃ j ≤ m, r ≤ 1/(2:ℝ)^j ∧ 1/(2:ℝ)^j ≤ 2*r := by
  induction m with
  | zero =>
    refine ⟨0,le_rfl,?_,?_⟩
    · simpa using hmax
    · norm_num at hmin ⊢
      linarith
  | succ m ih =>
    by_cases hcoarse : 1/(2:ℝ)^m ≤ r
    · obtain ⟨j,hj,hr,hjr⟩ := ih hcoarse
      exact ⟨j,hj.trans (Nat.le_succ m),hr,hjr⟩
    · refine ⟨m,Nat.le_succ m,(lt_of_not_ge hcoarse).le,?_⟩
      have he : 1/(2:ℝ)^m = 2*(1/(2:ℝ)^(m+1)) := by rw [pow_succ]; field_simp
      rw [he]
      linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FinitePrefixBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every closed-ball test follows from the finite dyadic prefix tests.
This applies directly to original finite points, with no center replacement. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem finite_prefix_ball_bound_at {N M : ℕ} (hMN : M ≤ N)
    {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n ≤ M, ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^n)^s*(P.card:ℝ)) :
    NormalizedFiniteBallBound (1/(2:ℝ)^M) s (49*K*4^s) P := by
  intro z r hr _
  have hr0 : 0 < r := (by positivity : 0 < 1/(2:ℝ)^M).trans_le hr
  by_cases hsmall : 2*r ≤ 1
  · have hmin : 1/(2:ℝ)^M ≤ 2*r := hr.trans (by linarith only [hr0])
    obtain ⟨n,hn,hlo,hup⟩ := dyadic_radius_bracket hmin hsmall
    have hbound := finite_point_ball_count Q (by rw [hQ]; norm_num) hleaf (hn.trans hMN) hr0
      (by positivity : 0 ≤ K*(1/(2:ℝ)^n)^s*(P.card:ℝ))
      (by simpa only [hQ] using hlo) (hprefix n hn) z
    have hpow : (1/(2:ℝ)^n)^s ≤ (4*r)^s := Real.rpow_le_rpow (by positivity)
      (by linarith only [hup]) hs
    calc
      _ ≤ (49:ℝ)*(K*(1/(2:ℝ)^n)^s*(P.card:ℝ)) := by
        simpa only [Nat.reducePow,Nat.cast_ofNat] using hbound
      _ ≤ (49:ℝ)*(K*(4*r)^s*(P.card:ℝ)) := by gcongr
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring
  · have hpow : 1 ≤ (4*r)^s := Real.one_le_rpow (by linarith only [hsmall]) hs
    have hlarge : 1 ≤ 49*K*(4*r)^s := by nlinarith only [mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)]
    calc
      _ ≤ (P.card:ℝ) := Nat.cast_le.mpr (Finset.card_filter_le _ _)
      _ ≤ (49*K*(4*r)^s)*(P.card:ℝ) := le_mul_of_one_le_left (Nat.cast_nonneg _) hlarge
      _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_RelativePrefixBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite relative prefix tests give the exact normalized ball bound in
an original cell chart, with its dyadic radius and fixed losses explicit. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem relative_dyadic_power {a n : ℕ} (ha : a ≤ n) (s : ℝ) :
    (1/(2:ℝ)^(n-a))^s = ((2:ℝ)^a)^s*(1/(2:ℝ)^n)^s := by
  have hp : (2:ℝ)^n = (2:ℝ)^a*(2:ℝ)^(n-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
  have hb : 1/(2:ℝ)^(n-a) = (2:ℝ)^a*(1/(2:ℝ)^n) := by rw [hp]; field_simp
  rw [hb,Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^n)]

theorem finite_relative_prefix_ball_bound_at {N M a : ℕ} (hMN : M ≤ N)
    (ha : a ≤ M) {s K : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hprefix : ∀ n, a ≤ n → n ≤ M → ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ K*(1/(2:ℝ)^(n-a))^s*(P.card:ℝ))
    (y b : ℝ) :
    NormalizedFiniteBallBound (1/(2:ℝ)^(M-a)) s (49*K*4^s)
      (P.image (localPacketPoint (1/(2:ℝ)^a) y b)) := by
  have hpow : 1 ≤ ((2:ℝ)^a)^s := Real.one_le_rpow (one_le_pow₀ (by norm_num)) hs
  have hK' : 1 ≤ K*((2:ℝ)^a)^s := by
    simpa using mul_le_mul hK hpow (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  have htests : ∀ n ≤ M, ∀ p ∈ (P.image l).image (List.take n),
      ((pointPrefixFiber P l n p).card:ℝ) ≤ (K*((2:ℝ)^a)^s)*(1/(2:ℝ)^n)^s*(P.card:ℝ) := by
    intro n hn p hp
    by_cases han : a ≤ n
    · have hh := hprefix n han hn p hp
      rw [relative_dyadic_power han] at hh
      convert hh using 1 <;> first | rfl | ring
    · have hn' : n ≤ a := Nat.le_of_not_ge han
      have hbase : 1 ≤ (2:ℝ)^a*(1/(2:ℝ)^n) := by
        rw [mul_one_div]
        exact (le_div_iff₀ (by positivity)).2 (by simpa using pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hn')
      have hunit : 1 ≤ ((2:ℝ)^a)^s*(1/(2:ℝ)^n)^s := by
        rw [← Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^n)]
        exact Real.one_le_rpow hbase hs
      have hk : 1 ≤ (K*((2:ℝ)^a)^s)*(1/(2:ℝ)^n)^s := by
        have hh := mul_le_mul hK hunit (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
        first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))
      exact (Nat.cast_le.mpr (Finset.card_filter_le _ _)).trans
        (le_mul_of_one_le_left (Nat.cast_nonneg _) hk)
  have hb := finite_prefix_ball_bound_at hMN hs hK' Q hQ P l hleaf htests
  have hl := localPacketPoint_regular (by positivity : 0 < 1/(2:ℝ)^M)
    (by positivity : 0 < 1/(2:ℝ)^a)
    ((div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))) y b P hb
  have heq : (1/(2:ℝ)^M)/(1/(2:ℝ)^a) = 1/(2:ℝ)^(M-a) := by
    have hp : (2:ℝ)^M = (2:ℝ)^a*(2:ℝ)^(M-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
    rw [hp]
    field_simp
  have hcancel : ((2:ℝ)^a)^s*(1/(2:ℝ)^a)^s = 1 := by
    rw [← Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^a) (by positivity : 0 ≤ 1/(2:ℝ)^a)]
    simp
  have hc : (49*(K*((2:ℝ)^a)^s)*4^s)*(1/(2:ℝ)^a)^s = 49*K*4^s := by
    calc
      _ = (49*K*4^s)*(((2:ℝ)^a)^s*(1/(2:ℝ)^a)^s) := by ring
      _ = _ := by rw [hcancel,mul_one]
  rwa [heq,hc] at hl

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockPrefixBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Interpolate finite prefix tests between selected block depths. Only the
actual maximum depth gap is charged, before passing to geometric balls. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem pointPrefixFiber_subset_take (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    {a n : ℕ} (ha : a ≤ n) (p : CellPath 2) :
    pointPrefixFiber P l n p ⊆ pointPrefixFiber P l a (p.take a) := by
  intro x hx
  obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
  refine Finset.mem_filter.mpr ⟨hx,?_⟩
  have hh := congrArg (List.take a) he
  simpa only [List.take_take,Nat.min_eq_left ha] using hh

theorem dyadic_prefix_gap_bound {a n B : ℕ} (ha : a ≤ n) (hgap : n ≤ a+B) {s : ℝ} (hs : 0 ≤ s) :
    (1/(2:ℝ)^a)^s ≤ ((2:ℝ)^B)^s*(1/(2:ℝ)^n)^s := by
  have hp : (2:ℝ)^n = (2:ℝ)^a*(2:ℝ)^(n-a) := by rw [← pow_add,Nat.add_sub_of_le ha]
  have hbase : 1/(2:ℝ)^a ≤ (2:ℝ)^B*(1/(2:ℝ)^n) := by
    rw [hp]
    rw [mul_one_div]
    have hh : (2:ℝ)^(n-a) ≤ (2:ℝ)^B := pow_le_pow_right₀ (by norm_num) (by omega)
    apply (le_div_iff₀ (by positivity : 0 < (2:ℝ)^a*(2:ℝ)^(n-a))).2
    calc
      _ = (2:ℝ)^(n-a) := by field_simp
      _ ≤ _ := hh
  have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/(2:ℝ)^a) hbase hs
  rwa [Real.mul_rpow (by positivity : 0 ≤ (2:ℝ)^B) (by positivity : 0 ≤ 1/(2:ℝ)^n)] at hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_RelativeBlockBallBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Relative selected-depth tests give normalized ball bounds in the
original parent chart, retaining the block interpolation loss. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem finite_relative_block_ball_bound {N M a B : ℕ}
    (hMN : M ≤ N) (ha : a ≤ M) {s K : ℝ} (hs : 0 ≤ s) (hK : 1 ≤ K)
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (htests : ∀ n, a ≤ n → n ≤ M → ∃ b, a ≤ b ∧ b ≤ n ∧ n ≤ b+B ∧
      ∀ p ∈ (P.image l).image (List.take b),
        ((pointPrefixFiber P l b p).card:ℝ) ≤ K*(1/(2:ℝ)^(b-a))^s*(P.card:ℝ))
    (y c : ℝ) :
    NormalizedFiniteBallBound (1/(2:ℝ)^(M-a)) s (49*(K*((2:ℝ)^B)^s)*4^s)
      (P.image (localPacketPoint (1/(2:ℝ)^a) y c)) := by
  have hKB : 1 ≤ K*((2:ℝ)^B)^s := by
    have hp : 1 ≤ ((2:ℝ)^B)^s :=
      Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2)) hs
    simpa using mul_le_mul hK hp (by norm_num : (0:ℝ) ≤ 1) (zero_le_one.trans hK)
  apply finite_relative_prefix_ball_bound_at hMN ha hs hKB Q hQ P l hleaf
  intro n han hn p hp
  obtain ⟨b,hab,hbn,hgap,hbound⟩ := htests n han hn
  have hpb : p.take b ∈ (P.image l).image (List.take b) := by
    obtain ⟨v,hv,hvp⟩ := Finset.mem_image.mp hp
    refine Finset.mem_image.mpr ⟨v,hv,?_⟩
    have hh := congrArg (List.take b) hvp
    simpa only [List.take_take,Nat.min_eq_left hbn] using hh
  calc
    _ ≤ ((pointPrefixFiber P l b (p.take b)).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (pointPrefixFiber_subset_take P l hbn p))
    _ ≤ K*(1/(2:ℝ)^(b-a))^s*(P.card:ℝ) := hbound _ hpb
    _ ≤ K*(((2:ℝ)^B)^s*(1/(2:ℝ)^(n-a))^s)*(P.card:ℝ) := by
      gcongr
      exact dyadic_prefix_gap_bound (by omega : b-a ≤ n-a) (by omega) hs
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockProfileBallBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual block-profile lower chords imply all-radius finite ball
bounds for each original parent fiber, after rescaling its chart. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem dyadic_inverse_power_eq (n : ℕ) (s : ℝ) :
    (1/(2:ℝ)^n)^s = (2:ℝ)^(-s*(n:ℝ)) := by
  rw [one_div,Real.inv_rpow (by positivity),← Real.rpow_natCast_mul (by norm_num),
    ← Real.rpow_neg (by norm_num)]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_TruncatedBlockRatio
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prefix ratios for the actual endpoint cells of a profile interval.
Both endpoint binning losses are retained explicitly. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem planar_prefixFiber_children_subset (C : Finset (CellPath 2)) {a b n : ℕ}
    (hnb : n ≤ b) (p q : CellPath 2) :
    prefixFiber (prefixChildren C a b p) n q ⊆ prefixChildren C n b q := by
  intro v hv
  obtain ⟨hv,hvq⟩ := Finset.mem_filter.mp hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have hn : w.take n = q := by
    simpa only [List.take_take,Nat.min_eq_left hnb] using hvq
  exact Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hw).1,hn⟩,rfl⟩

theorem blockClass_truncated_fiber_ratio {N : ℕ} {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {q : CellPath 2}
    (hq : q ∈ (prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).image (List.take (blockDepth N B k))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
      (2:ℝ)^(k+j)*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B i p:ℝ)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  have hDsub : D ⊆ C.image (List.take (blockDepth N B j)) :=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hq' : q ∈ C.image (List.take (blockDepth N B k)) := by
    rw [← planar_prefix_image_take_take C (blockDepth_antitone N B hjk)]
    exact Finset.image_subset_image hDsub hq
  have hparent := (blockClass_descendant_count hL B f K p (hjk.trans hki) hi hp₀).1
  have hchild := (blockClass_descendant_count hL B f K p hjk (hki.trans hi) hq').2
  have hsub := planar_prefixFiber_children_subset C (a := blockDepth N B i)
    (blockDepth_antitone N B hjk) p₀ q
  have hi0 : 0 < (blockProduct L F N B i p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hj0 : 0 < (blockProduct L F N B j p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hk0 : 0 < (blockProduct L F N B k p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
  have hlow : 0 < ((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j := by positivity
  have hbound : ((prefixFiber D (blockDepth N B k) q).card:ℝ) ≤
      (2:ℝ)^k*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B j p:ℝ)) :=
    (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans hchild
  change ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
    (2:ℝ)^(k+j)*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B i p:ℝ))
  calc
    _ ≤ ((2:ℝ)^k*((blockProduct L F N B k p:ℝ)/(blockProduct L F N B j p:ℝ)))/
        (((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j) :=
      div_le_div₀ (by positivity) hbound hlow hparent
    _ = _ := by rw [pow_add]; field_simp

theorem blockClass_truncated_frostman {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K)
    {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {q : CellPath 2}
    (hq : q ∈ (prefixChildren
      (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
      (blockDepth N B i) (blockDepth N B j) p₀).image (List.take (blockDepth N B k)))
    {s A : ℝ}
    (hprofile : let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    ((prefixFiber D (blockDepth N B k) q).card:ℝ)/(D.card:ℝ) ≤
      (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) := by
  have hb := blockClass_truncated_fiber_ratio hL B f K p hjk hki hi hp₀ hq
  dsimp only at hb ⊢
  rw [blockProduct_relative_profile hN hL _ B K p (hki.trans hi) hi] at hb
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  dsimp only at hprofile
  linarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_TruncatedBlockBall
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Endpoint cells of a profile interval form an actual separated planar
set with the full local Frostman bound, including intermediate radii. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_truncated_local_ball {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) (y c : ℝ) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    let P := D.image (fun q => (Q.descendant q).center)
    P.Nonempty ∧ FiniteSeparatedAt (1/(2:ℝ)^(blockDepth N B j)) P ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s
        (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)
        (P.image (localPacketPoint (1/(2:ℝ)^(blockDepth N B i)) y c)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hCsub : C ⊆ cubePaths 2 N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hDsub : D ⊆ cubePaths 2 (blockDepth N B j) :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hCsub (Nat.sub_le _ _))
  obtain ⟨l,hleaf,hl,himage,hsep⟩ := planar_path_center_realization Q (by rw [hQ]; norm_num) D hDsub
  have hDlow := (blockClass_descendant_count hL B f K p hji hi hp₀).1
  have hDn : D.Nonempty := by
    apply Finset.card_pos.mp
    have hp : 0 < (blockProduct L F N B i p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
    have hq : 0 < (blockProduct L F N B j p:ℝ) := Nat.cast_pos.mpr (blockProduct_pos _ _ _ _ _ _)
    have hpos : 0 < (D.card:ℝ) := (by positivity : 0 <
      ((blockProduct L F N B i p:ℝ)/(blockProduct L F N B j p:ℝ))/(2:ℝ)^j).trans_le hDlow
    exact Nat.cast_pos.mp hpos
  have hP : P.Nonempty := hDn.image _
  have hcard : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  refine ⟨hP,by simpa only [hQ] using hsep,?_⟩
  have hconst : 1 ≤ (2:ℝ)^(i+j)*(2:ℝ)^A :=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (Real.one_le_rpow (by norm_num) hA)
  apply finite_relative_block_ball_bound le_rfl (blockDepth_antitone N B hji) hs hconst Q hQ P l hleaf
  intro n han hnb
  obtain ⟨k,hjk,hki,hkn,hgap⟩ := blockDepth_bracket hji han hnb
  refine ⟨blockDepth N B k,blockDepth_antitone N B hki,hkn,hgap,?_⟩
  intro q hq
  have hq' := hq
  rw [himage] at hq'
  have hb := blockClass_truncated_frostman hN hL B f K p hjk hki hi hp₀ hq'
    (hprofile k hjk hki)
  dsimp only at hb
  change (prefixFiber D (blockDepth N B k) q).card / (D.card:ℝ) ≤
    (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) at hb
  rw [← himage,← pointPrefixFiber_card_eq hl,Finset.card_image_iff.mpr hl] at hb
  have hpow : (2:ℝ)^(k+j)*(2:ℝ)^(A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))) ≤
      ((2:ℝ)^(i+j)*(2:ℝ)^A)*(1/(2:ℝ)^(blockDepth N B k-blockDepth N B i))^s := by
    rw [dyadic_inverse_power_eq,Nat.cast_sub (blockDepth_antitone N B hki),mul_assoc,
      ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    have he : A+-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) =
        A-s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ)) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  exact ((div_le_iff₀ hcard).1 hb).trans (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_TruncatedBlockCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Upper profile chords bound the actual rounded cover of the endpoint
center configuration used in the multiscale induction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_truncated_local_cover {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ)
    (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).image
      (List.take (blockDepth N B i)))
    {s A ρ : ℝ} (hρ : 0 < ρ)
    (hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤ ρ)
    (hprofile : let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) (y c : ℝ) :
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
    let P := D.image (fun q => (Q.descendant q).center)
    (((P.image (localPacketPoint (1/(2:ℝ)^(blockDepth N B i)) y c)).image
      (coarsePlanarRound ρ)).card:ℝ) ≤
        49*((2:ℝ)^i*(2:ℝ)^(s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := by
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  let D := prefixChildren C (blockDepth N B i) (blockDepth N B j) p₀
  let P := D.image (fun q => (Q.descendant q).center)
  have hCsub : C ⊆ cubePaths 2 N := fun q hq => hL (Finset.mem_filter.mp hq).1
  have hDsub : D ⊆ cubePaths 2 (blockDepth N B j) :=
    (Finset.image_subset_image (Finset.filter_subset _ _)).trans
      (planar_prefix_image_take_cubePaths hCsub (Nat.sub_le _ _))
  obtain ⟨l,hleaf,_,himage,_⟩ := planar_path_center_realization Q (by rw [hQ]; norm_num) D hDsub
  have hb := finite_local_prefix_coarse_cover hρ (by positivity : 0 < 1/(2:ℝ)^(blockDepth N B i))
    y c Q (by rw [hQ]; norm_num) P l hleaf (blockDepth_antitone N B hjk)
    (by simpa only [hQ] using hscale)
  have he : D.image (List.take (blockDepth N B k)) =
      prefixChildren C (blockDepth N B i) (blockDepth N B k) p₀ := by
    simp only [D,prefixChildren,Finset.image_image,Function.comp_def,List.take_take,
      Nat.min_eq_left (blockDepth_antitone N B hjk)]
  rw [himage,he] at hb
  have hc := blockClass_local_covering hN hL B f K p hki hi hp₀ hprofile
  exact hb.trans (mul_le_mul_of_nonneg_left hc (by norm_num))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_RetainedProfileBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Profile estimates on the actual endpoint centers after a retained class
is regularized again. The original profile remains the reference profile. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem normalizedFiniteBallBound_mono_constant {δ s A B : ℝ} {P : Finset (Space 2)}
    (hδ : 0 ≤ δ) (hAB : A ≤ B) (h : NormalizedFiniteBallBound δ s A P) :
    NormalizedFiniteBallBound δ s B P := by
  intro z r hr hr1
  exact (h z r hr hr1).trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (hδ.trans hr) _)) (Nat.cast_nonneg _))

section Retained
variable {N : ℕ} {L L' : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))

include hL hsub hQ hi hp₀ in
theorem blockClass_retained_endpoint_cover (hN : 0 < N)
    {k : ℕ} (hjk : j ≤ k) (hki : k ≤ i) {t A ρ : ℝ} (hρ : 0 < ρ)
    (hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤ ρ)
    (hprofile : let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound ρ)).card:ℝ) ≤
      49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := by
  have hpC := Finset.image_subset_image hsub hp₀
  have hcover := blockClass_truncated_local_cover hN hL B f K p Q hQ hjk hki hi hpC
    hρ hscale hprofile ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  apply le_trans _ hcover
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  apply Finset.image_subset_image
  apply Finset.image_subset_image
  apply Finset.image_subset_image
  exact Finset.image_subset_image (Finset.filter_subset_filter _ hsub)

end Retained
end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuarterEndpointMap
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed quarter chart closes under the actual local cell map. Its
contraction does not accumulate with the number of selected intervals. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem quarterEndpointPoint_eq (Q : DyadicCube 2) (a : ℕ) (p₀ r : CellPath 2) :
    quarterEndpointPoint Q a p₀ r = planarQuarter
      (localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
        (Q.descendant r).center) := by
  ext i
  rw [planarQuarter_apply]
  fin_cases i <;> dsimp [quarterEndpointPoint,localPacketPoint] <;> ring

theorem quarterEndpointSet_eq (Q : DyadicCube 2) (C : Finset (CellPath 2))
    (a b : ℕ) (p₀ : CellPath 2) :
    quarterEndpointSet Q C a b p₀ = (blockEndpointSet Q C a b p₀).image planarQuarter := by
  simp only [quarterEndpointSet,blockEndpointSet,Finset.image_image,Function.comp_def]
  congr 1
  funext r
  exact quarterEndpointPoint_eq Q a p₀ r

theorem quarterEndpointSet_geometry {N a b : ℕ} (Q : DyadicCube 2) (hQ : Q.side = 1)
    (C : Finset (CellPath 2)) (hC : C ⊆ cubePaths 2 N)
    (hab : a ≤ b) (hbN : b ≤ N) (p₀ : CellPath 2) :
    (quarterEndpointSet Q C a b p₀).card = (prefixChildren C a b p₀).card ∧
    (∀ x ∈ quarterEndpointSet Q C a b p₀, |x 0| ≤ 1/4 ∧ |x 1| ≤ 1/4) ∧
    FiniteSeparatedAt (1/(2:ℝ)^(b-a+2)) (quarterEndpointSet Q C a b p₀) := by
  obtain ⟨hcard,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ C hC hab hbN p₀
  rw [quarterEndpointSet_eq]
  refine ⟨?_,?_,?_⟩
  · rw [Finset.card_image_of_injective _ planarQuarter_injective]
    exact hcard
  · intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    have hz' := hchart z hz
    constructor
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.1]
    · rw [planarQuarter_apply,abs_div]
      norm_num
      linarith only [hz'.2]
  · have he : (1/(2:ℝ)^(b-a))/4 = 1/(2:ℝ)^(b-a+2) := by
      rw [pow_add]
      norm_num
      ring
    rw [← he]
    exact planarQuarter_separated _ hsep

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SampledRowCardinality
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the sampler's exact cardinality bounds to the dyadic lower
and upper powers used by the regular product theorem. -/
namespace Falconer

theorem half_power_rpow_exp (N : ℕ) (s : ℝ) :
    ((1/2:ℝ)^N)^s = Real.exp (-s*(N:ℝ)*Real.log 2) := by
  rw [Real.rpow_def_of_pos (by positivity),Real.log_pow,
    Real.log_div (by norm_num) (by norm_num),Real.log_one]
  congr 1
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SeparatedThinning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed finite loss makes the actual points four times more separated.
This pays for the anisotropic change of slope chart. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem quadruple_separated_subset {δ : ℝ} (hδ : 0 < δ)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hsep : FiniteSeparatedAt δ S) :
    ∃ P ⊆ S, P.Nonempty ∧ FiniteSeparatedAt (4*δ) P ∧ (S.card:ℝ) ≤ 81*(P.card:ℝ) := by
  obtain ⟨P,hPS,hPsep,hcover⟩ := exists_separated_cover S (show 0 ≤ 4*δ by positivity)
  have hP : P.Nonempty := by
    obtain ⟨x,hx⟩ := hS
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  refine ⟨P,hPS,hP,hPsep,?_⟩
  have hc : ∀ y ∈ P, ((S.filter fun x => dist x y ≤ 4*δ).card:ℝ) ≤ 81 := by
    intro y _
    have hh := separated_ball_card (S.filter fun x => dist x y ≤ 4*δ) y hδ
      (show 0 ≤ 4*δ by positivity)
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
    have he : 2*(4*δ)/δ+1 = (9:ℝ) := by field_simp; ring
    rw [he] at hh
    norm_num only [Nat.cast_ofNat,show (9:ℝ)^2 = 81 by norm_num] at hh
    exact hh
  simpa only [mul_comm] using selected_points_card_lower S id P hcover hc

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionSampleBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform polynomial costs for the robust projection step. These bounds
keep every loss explicit before the dyadic exponential absorption. -/
namespace Falconer

theorem projectionGapConstant_pos {κ : ℝ} (hκ : 0 < κ) :
    0 < projectionGapConstant κ := by
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  unfold projectionGapConstant
  positivity

theorem planarPotentialConstant_gap {κ s t : ℝ} (hκ : 0 < κ)
    (hs : s ≤ 1) (hgap : κ ≤ t-s) :
    planarPotentialConstant s t ≤ projectionGapConstant κ := by
  have hp : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hq : (2:ℝ)^(s-t) ≤ (2:ℝ)^(-κ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hgap])
  have hd : 0 < 1-(2:ℝ)^(-κ) := sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hκ]))
  have hden : 1-(2:ℝ)^(-κ) ≤ 1-(2:ℝ)^(s-t) := by linarith only [hq]
  have hquot : (2:ℝ)^s/(1-(2:ℝ)^(s-t)) ≤ 2/(1-(2:ℝ)^(-κ)) :=
    (div_le_div_of_nonneg_right hp (hd.le.trans hden)).trans
      (div_le_div_of_nonneg_left (by norm_num) hd hden)
  have hden0 : 0 < 1-(2:ℝ)^(s-t) := hd.trans_le hden
  have hq0 : 0 ≤ (2:ℝ)^s/(1-(2:ℝ)^(s-t)) := by positivity
  unfold planarPotentialConstant projectionGapConstant
  gcongr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ProjectionPowerBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit quadratic depth loss in projection sampling fits into
any prescribed positive dyadic power, uniformly over a fixed exponent gap. -/
namespace Falconer

theorem dyadic_quadratic_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^2 ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1 (24*C/a^3))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : 24*C ≤ a^3*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    have he := (div_le_iff₀ (pow_pos ha 3)).1 hh
    nlinarith only [he]
  have hsize : ((N:ℝ)+1)^2 ≤ (2*(N:ℝ))^2 := by
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) 2
  have hcub := mul_le_mul_of_nonneg_right hscale (sq_nonneg (N:ℝ))
  calc
    _ ≤ C*(2*(N:ℝ))^2 := mul_le_mul_of_nonneg_left hsize hC
    _ ≤ (a*(N:ℝ))^3/6 := by nlinarith only [hcub]
    _ ≤ Real.exp (a*(N:ℝ)) := by
      simpa only [Nat.factorial_succ,Nat.factorial_zero,Nat.reduceAdd,Nat.reduceMul,
        Nat.cast_ofNat] using Real.pow_div_factorial_le_exp (a*(N:ℝ))
          (by positivity : 0 ≤ a*(N:ℝ)) 3
    _ = _ := by congr 1; dsimp [a]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedGainBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reserve a uniform positive exponent for the two pencil-size cases of
the regular-scale estimate. All fixed constants are absorbed at large depth. -/
namespace Falconer

theorem normalized_regular_gain_budget {κ θ A : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hθ : 0 < θ) (hA : 0 ≤ A) :
    ∃ ε γ η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < γ ∧ 0 < η ∧ 0 < N0 ∧
      γ*(κ/2) = 4*η ∧ ∀ n : ℕ, N0 ≤ n+2 →
        let δ := 1/(2:ℝ)^(2*n)
        let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
        let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
        K ≤ E ∧ δ^(-(γ+η)) ≤ E ∧ 2*A*K^3 ≤ δ^(-3*η) := by
  let γ := θ/8
  let η := γ*κ/8
  let ε := min (min θ 1) (η/20)
  have hγ : 0 < γ := by dsimp [γ]; positivity
  have hη : 0 < η := by dsimp [η]; positivity
  have hε : 0 < ε := lt_min (lt_min hθ zero_lt_one) (by positivity)
  have hεθ : ε ≤ θ := (min_le_left _ _).trans (min_le_left _ _)
  have hεsmall : 3*ε ≤ η := by
    have he : ε ≤ η/20 := min_le_right _ _
    linarith only [he,hη]
  have hηlow : γ+η ≤ θ/2 := by
    dsimp [γ,η]
    nlinarith only [hκ1,hθ]
  obtain ⟨N1,hN1,hconst⟩ := dyadic_quadratic_loss hη (show 0 ≤ 2*A by positivity)
  refine ⟨ε,γ,η,max 4 N1,hε,(min_le_left _ _).trans (min_le_right _ _),hγ,hη,
    lt_of_lt_of_le (by norm_num : 0 < 4) (le_max_left _ _),?_,?_⟩
  · dsimp [η]
    ring
  intro n hn
  dsimp only
  have hn1 : 1 ≤ n := by have := (le_max_left 4 N1).trans hn; omega
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hmR : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
      Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by gcongr
  have hE : (1/(2:ℝ)^(2*n))^(-(γ+η)) ≤
      Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by
    rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    have hg := mul_le_mul_of_nonneg_right hηlow (show 0 ≤ 2*(n:ℝ) by positivity)
    apply mul_le_mul_of_nonneg_right _ hlog
    nlinarith only [hg,hθ]
  refine ⟨hK,hE,?_⟩
  have hfixed : 2*A ≤ Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ (hconst (n+2) ((le_max_right _ _).trans hn))
    have hsq : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hmR])
    nlinarith only [hsq,hA]
  have hexp : (Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2))^3 =
      Real.exp ((3*ε)*((n+2:ℕ):ℝ)*Real.log 2) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  calc
    _ ≤ Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2)*
        Real.exp (η*((n+2:ℕ):ℝ)*Real.log 2) := by
      apply mul_le_mul hfixed _ (Real.exp_pos _).le (Real.exp_pos _).le
      gcongr
    _ = Real.exp ((2*η)*((n+2:ℕ):ℝ)*Real.log 2) := by
      rw [← Real.exp_add]; congr 1; ring
    _ ≤ (1/(2:ℝ)^(2*n))^(-3*η) := by
      rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
      apply Real.exp_le_exp.mpr
      push_cast
      apply mul_le_mul_of_nonneg_right _ hlog
      have hnR1 : (1:ℝ) ≤ n := by exact_mod_cast hn1
      nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hnR1)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_SquashGainBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed losses in the slope normalization fit inside the reserved gain. -/
namespace Falconer

theorem squash_gain_budget {θ η : ℝ} (hθ : 0 < θ) (hη : 0 < η) :
    ∃ ε : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < N0 ∧ ∀ n : ℕ, N0 ≤ n+2 →
      20736*Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2) ≤
        Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2) ∧
      81 ≤ (1/(2:ℝ)^(2*n))^(-η/2) := by
  let ε := min (θ/2) 1
  have hε : 0 < ε := lt_min (by positivity) zero_lt_one
  obtain ⟨N1,_,hconst⟩ := dyadic_quadratic_loss
    (lt_min (half_pos hθ) (half_pos hη)) (by norm_num : (0:ℝ) ≤ 20736)
  refine ⟨ε,max 4 N1,hε,min_le_right _ _,lt_of_lt_of_le (by norm_num : 0 < 4) (le_max_left _ _),?_⟩
  intro n hn
  have hn2 : 2 ≤ n := by have := (le_max_left 4 N1).trans hn; omega
  have hnR : 0 ≤ (n:ℝ) := Nat.cast_nonneg _
  have hmR : 0 ≤ ((n+2:ℕ):ℝ) := Nat.cast_nonneg _
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hfixed : 20736 ≤ Real.exp ((min (θ/2) (η/2))*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply le_trans _ (hconst (n+2) ((le_max_right _ _).trans hn))
    have hs : (1:ℝ) ≤ (((n+2:ℕ):ℝ)+1)^2 := one_le_pow₀ (by linarith only [hmR])
    nlinarith only [hs]
  have hfirst : 20736 ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply hfixed.trans
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_left _ _) hmR) hlog
  have hsecond : 81 ≤ Real.exp ((η/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
    apply (show (81:ℝ) ≤ 20736 by norm_num).trans (hfixed.trans _)
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (min_le_right _ _) hmR) hlog
  constructor
  · calc
      _ ≤ Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2)*
          Real.exp ((θ/2)*((n+2:ℕ):ℝ)*Real.log 2) := by
        apply mul_le_mul hfirst _ (Real.exp_pos _).le (Real.exp_pos _).le
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (min_le_left _ _) hmR) hlog
      _ = Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        gcongr
        norm_num
  · apply hsecond.trans
    rw [show (1/(2:ℝ)^(2*n)) = (1/(2:ℝ))^(2*n) by rw [div_pow,one_pow],half_power_rpow_exp]
    apply Real.exp_le_exp.mpr
    push_cast
    apply mul_le_mul_of_nonneg_right _ hlog
    have hnR2 : (2:ℝ) ≤ n := by exact_mod_cast hn2
    nlinarith only [mul_nonneg hη.le (sub_nonneg.mpr hnR2)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_UpperBlockBracket
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The selected block immediately above a prescribed integer depth. -/
namespace Falconer.Regularization

theorem blockDepth_upper_bracket {N B i j n : ℕ} (hji : j ≤ i)
    (hlo : blockDepth N B i ≤ n) (hhi : n ≤ blockDepth N B j) :
    ∃ k, j ≤ k ∧ k ≤ i ∧ n ≤ blockDepth N B k ∧ blockDepth N B k ≤ n+B := by
  have hex : ∃ r, r ≤ i-j ∧ n ≤ blockDepth N B (i-r) :=
    ⟨i-j,le_rfl,by simpa only [Nat.sub_sub_self hji] using hhi⟩
  let r := Nat.find hex
  have hr : r ≤ i-j ∧ n ≤ blockDepth N B (i-r) := Nat.find_spec hex
  refine ⟨i-r,by omega,by omega,hr.2,?_⟩
  by_cases hz : r = 0
  · simp only [hz,Nat.sub_zero]
    omega
  · have hr0 : 0 < r := Nat.pos_of_ne_zero hz
    have hprev : blockDepth N B (i-r+1) < n := by
      by_contra hn
      have hmin := Nat.find_min hex (show r-1 < r by omega)
      apply hmin
      refine ⟨by omega,?_⟩
      have he : i-(r-1) = i-r+1 := by omega
      simpa only [he] using (le_of_not_gt hn)
    have hgap := blockDepth_gap N B (i-r)
    have hord := blockDepth_antitone N B (Nat.le_succ (i-r))
    omega

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_EndpointMidscaleCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The square-root cover required by the regular gain follows from an
upper profile chord even when its midpoint lies between selected blocks. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_retained_midscale_cover {N : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    {n : ℕ} (hn : 3 ≤ n) (hlen : blockDepth N B j-blockDepth N B i = 2*n)
    {t A : ℝ} (ht : 0 ≤ t)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) ≤
      (49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t := by
  have hab := blockDepth_antitone N B hji
  have hmid : blockDepth N B i+n+3 ≤ blockDepth N B j := by omega
  obtain ⟨k,hjk,hki,hlo,hup⟩ := blockDepth_upper_bracket hji
    (show blockDepth N B i ≤ blockDepth N B i+n+3 by omega) hmid
  have hscale : (1/(2:ℝ)^(blockDepth N B k))/(1/(2:ℝ)^(blockDepth N B i)) ≤
      1/(2:ℝ)^(n+3) := by
    rw [dyadic_relative_mesh _ _ (blockDepth_antitone N B hki)]
    apply one_div_le_one_div_of_le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hc := blockClass_retained_endpoint_cover hL B f g K p q hsub Q hQ hi hp₀ hN
    hjk hki (by positivity : 0 < 1/(2:ℝ)^(n+3)) hscale (hprofile k hjk hki)
  have hdist : (blockDepth N B k:ℝ)-(blockDepth N B i:ℝ) ≤ (n:ℝ)+3+B := by
    have hc : blockDepth N B k ≤ blockDepth N B i+n+3+B := hup
    have hc' : (blockDepth N B k:ℝ) ≤ (blockDepth N B i:ℝ)+n+3+B := by exact_mod_cast hc
    linarith only [hc']
  calc
    _ ≤ 49*((2:ℝ)^i*(2:ℝ)^(t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A)) := hc
    _ ≤ 49*((2:ℝ)^i*(2:ℝ)^(t*((n:ℝ)+3+B)+A)) := by gcongr; norm_num
    _ = (49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t := by
      apply (eq_div_iff (ne_of_gt (Real.rpow_pos_of_pos (by positivity) t))).2
      rw [dyadic_inverse_power_eq]
      calc
        _ = 49*((2:ℝ)^i*((2:ℝ)^(t*((n:ℝ)+3+B)+A)*(2:ℝ)^(-t*(n:ℝ)))) := by ring
        _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 3; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_PlanarCriticalPotential
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Critical finite planar potential with the exact linear depth loss.
This is used to control the distribution of cells along a selected tube. -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem finite_dyadic_critical_potential (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (_hK : 0 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)) ≤
      P.card + ENNReal.ofReal ((2:ℝ)^t)*
        (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
  let μ := planarCountingMeasure P
  have hsmall (j : ℕ) (hj : j ≤ 0+N) :
      μ {y | dist x y < 1/(2:ℝ)^j} ≤
        ENNReal.ofReal ((K*(P.card : ℝ))*(1/(2:ℝ)^j)^t) := by
    rw [planarCountingMeasure_apply]
    have hr0 : 1/(2:ℝ)^N ≤ 1/(2:ℝ)^j := by
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by simpa using hj)
    have hr1 : 1/(2:ℝ)^j ≤ 1 := by
      apply (div_le_one (by positivity)).2
      exact one_le_pow₀ (by norm_num)
    have hs : P.filter (fun y => dist x y < 1/(2:ℝ)^j) ⊆
        P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j) := by
      intro y hy
      obtain ⟨hyP,hy⟩ := Finset.mem_filter.mp hy
      exact Finset.mem_filter.mpr ⟨hyP,by simpa only [dist_comm] using hy.le⟩
    have hc := (show ((P.filter (fun y => dist x y < 1/(2:ℝ)^j)).card : ℝ) ≤
      (P.filter (fun y => dist y x ≤ 1/(2:ℝ)^j)).card from by exact_mod_cast Finset.card_le_card hs)
    have hh := hc.trans (hball x _ hr0 hr1)
    rw [show (K*(P.card : ℝ))*(1/(2:ℝ)^j)^t = K*(1/(2:ℝ)^j)^t*(P.card : ℝ) by ring]
    exact_mod_cast ENNReal.ofReal_le_ofReal hh
  have hlocal := truncated_scalar_potential_critical μ (fun y => dist x y) (by fun_prop)
    (fun _ => dist_nonneg) ht 0 N hsmall
  simp only [pow_zero,one_div_one,zero_add] at hlocal
  let A := {y : Space 2 | dist x y < 1}
  let F := fun y : Space 2 => ENNReal.ofReal ((1/max (dist x y) (1/(2:ℝ)^N))^t)
  have hfar : (∫⁻ y in Aᶜ, F y ∂μ) ≤ P.card := by
    calc
      _ ≤ ∫⁻ _ in Aᶜ, (1 : ℝ≥0∞) ∂μ := by
        apply setLIntegral_mono' (by measurability)
        intro y hy
        change ¬ dist x y < 1 at hy
        have hd : 1 ≤ max (dist x y) (1/(2:ℝ)^N) :=
          (le_of_not_gt hy).trans (le_max_left _ _)
        have hinv : 1/max (dist x y) (1/(2:ℝ)^N) ≤ 1 :=
          (div_le_one (zero_lt_one.trans_le hd)).2 hd
        exact ENNReal.ofReal_le_one.mpr ((Real.rpow_le_rpow (by positivity) hinv ht).trans_eq (Real.one_rpow _))
      _ ≤ μ univ := by
        simp only [lintegral_one,Measure.restrict_apply_univ]
        exact measure_mono (subset_univ _)
      _ = P.card := by rw [planarCountingMeasure_apply]; simp
  rw [← planarCountingMeasure_lintegral]
  change (∫⁻ y, F y ∂μ) ≤ _
  rw [← lintegral_add_compl F (show MeasurableSet A from by dsimp [A]; measurability)]
  simpa only [mul_assoc,add_comm] using add_le_add hlocal hfar

theorem finite_dyadic_critical_potential_real (P : Finset (Space 2)) (x : Space 2)
    (N : ℕ) {K t : ℝ} (hK : 1 ≤ K) (ht : 0 ≤ t)
    (hball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P) :
    (∑ y ∈ P, (1/max (dist x y) (1/(2:ℝ)^N))^t) ≤
      K*planarCriticalConstant N t*(P.card:ℝ) := by
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hh := finite_dyadic_critical_potential P x N hK0 ht hball
  rw [← ENNReal.ofReal_sum_of_nonneg (fun y _ => by positivity)] at hh
  have he : (P.card:ℝ≥0∞)+ENNReal.ofReal ((2:ℝ)^t)*
      (ENNReal.ofReal (K*(P.card:ℝ))+(N:ℝ≥0∞)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) =
      ENNReal.ofReal ((P.card:ℝ)+(2:ℝ)^t*(K*(P.card:ℝ)+(N:ℝ)*((K*(P.card:ℝ))*(2:ℝ)^t))) := by
    symm
    calc
      _ = ENNReal.ofReal (P.card:ℝ) + ENNReal.ofReal ((2:ℝ)^t) *
          (ENNReal.ofReal (K*(P.card:ℝ)) +
            ENNReal.ofReal (N:ℝ)*ENNReal.ofReal ((K*(P.card:ℝ))*(2:ℝ)^t)) := by
        conv_lhs =>
          rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity),
            ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_add (by positivity) (by positivity),
            ENNReal.ofReal_mul (Nat.cast_nonneg N)]
      _ = _ := by simp only [ENNReal.ofReal_natCast]
  rw [he] at hh
  have hb := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hh
  have hc := mul_le_mul_of_nonneg_right hK (Nat.cast_nonneg (α := ℝ) P.card)
  unfold planarCriticalConstant
  nlinarith only [hb,hc]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_InterpolatedIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large pencil improves the elementary incidence estimate. The exponent
is obtained by interpolating the actual packing and regularity kernels. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_interpolated_second_moment (N : ℕ) {s t u θ K M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hM0 : 0 ≤ M)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
      ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let A := (K*(80*δ)^s*M)^θ*(25921:ℝ)^(1-θ)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤ A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := by
    have hpot := finite_dyadic_truncated_potential_real P x N hK hu hut hPball
    calc
      _ ≤ ∑ y ∈ P, A*(1+(1/max (dist x y) δ)^u) := by
        apply Finset.sum_le_sum
        intro y hy
        exact (intersect_tube_interpolated_bound hδ hδ1 hs hK hθ hθ1 he (T x) (T y)
          x y (hPchart x hx).1 (hT x hx).1 (hT x hx).2.1 (hT x hx).2.2.1
          (hT x hx).2.2.2.1 (hT x hx).2.2.2.2 (hT y hy).2.2.2.2).trans
          (mul_le_mul_of_nonneg_left (truncatedPlanarDistance_inverse_power_le hδ hδ1 x y) hA)
      _ = A*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^u) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ A*((P.card:ℝ)+K*planarPotentialConstant u t*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hA
      _ = _ := by ring
  calc
    _ ≤ ∑ _x ∈ P, A*(1+K*planarPotentialConstant u t)*(P.card:ℝ) := Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [A]; ring

theorem planar_interpolated_incidence (N : ℕ) {s t u θ K m M : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (hθ : 0 < θ) (hθ1 : θ < 1) (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      (((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)) := by
  let B := ((K*(80*(1/(2:ℝ)^N))^s*M)^θ*(25921:ℝ)^(1-θ))*
    (1+K*planarPotentialConstant u t)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ _ := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hM0 : 0 ≤ M := by
    obtain ⟨p,hp⟩ := hP
    exact (Nat.cast_nonneg _).trans (hT p hp).2.1
  have hE := pencil_interpolated_second_moment N hs hu hut hK hM0 hθ hθ1 he P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.2.2.2.1,
      (hT x hx).2.1,(hT x hx).2.2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(B*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_QuarterCoarseCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed contraction changes the actual rounded point cover by at most
25 per original grid cell. No covering hypothesis is added. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planarQuarter_coarse_cover {ρ : ℝ} (hρ : 0 < ρ) (P : Finset (Space 2)) :
    (((P.image planarQuarter).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤
      25*((P.image (coarsePlanarRound ρ)).card:ℝ) := by
  let C := P.image (coarsePlanarRound ρ)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let A := fun c => ((S c).image planarQuarter).image (coarsePlanarRound (ρ/2))
  have hρ' : 0 < ρ/2 := by positivity
  have hA (c : Space 2) (_hc : c ∈ C) : ((A c).card:ℝ) ≤ 25 := by
    have hwithin : ∀ z ∈ A c, dist z (planarQuarter c) ≤ 2*(ρ/2) := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      have hpc := (Finset.mem_filter.mp hp).2
      have hd := coarsePlanarRound_near hρ p
      rw [hpc] at hd
      have hquarter : dist (planarQuarter p) (planarQuarter c) ≤ ρ/4 := by
        rw [planarQuarter_dist]
        exact div_le_div_of_nonneg_right hd (by norm_num)
      have hnear := coarsePlanarRound_near hρ' (planarQuarter p)
      rw [dist_comm] at hnear
      have htri := dist_triangle (coarsePlanarRound (ρ/2) (planarQuarter p))
        (planarQuarter p) (planarQuarter c)
      linarith
    have hh := separated_ball_card (A c) (planarQuarter c) hρ'
      (r := 2*(ρ/2)) (by positivity)
      (coarsePlanarRound_separated hρ' ((S c).image planarQuarter)) hwithin
    have he : (2*(2*(ρ/2))/(ρ/2)+1)^2 = (25:ℝ) := by field_simp; ring
    rwa [he] at hh
  have hcover : (P.image planarQuarter).image (coarsePlanarRound (ρ/2)) ⊆ C.biUnion A := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_biUnion.mpr ⟨coarsePlanarRound ρ p,Finset.mem_image_of_mem _ hp,?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,rfl⟩))
  calc
    _ ≤ ((C.biUnion A).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ c ∈ C, ((A c).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (25:ℝ) := Finset.sum_le_sum hA
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_InterpolatedPencilGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A large pencil supplies the extra normalized gain at a regular scale.
This retains the actual minimum pencil size and the loss from unequal sizes. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem interpolated_pencil_normalized (N : ℕ) {s t u θ K m R : ℝ}
    (hs : 0 ≤ s) (hu : 0 ≤ u) (hut : u < t) (hK : 1 ≤ K)
    (hm : 0 < m) (hR : 0 ≤ R) (hθ : 0 < θ) (hθ1 : θ < 1)
    (he : s*θ+2*(1-θ) = u)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m*m^(1-θ) ≤ ((P.biUnion T).card:ℝ)*
      (((K*(80*(1/(2:ℝ)^N))^s*R)^θ*(25921:ℝ)^(1-θ))*
        (1+K*planarPotentialConstant u t)) := by
  have hb := planar_interpolated_incidence N hs hu hut hK hm.le hθ hθ1 he
    P T hP hPchart hPball hT
  have heq : (K*(80*(1/(2:ℝ)^N))^s*(R*m))^θ =
      (K*(80*(1/(2:ℝ)^N))^s*R)^θ*m^θ := by
    rw [← mul_assoc,Real.mul_rpow (by positivity) hm.le]
  rw [heq] at hb
  have hmexp : m^(1-θ)*m^θ = m := by
    rw [← Real.rpow_add hm]
    norm_num
  apply (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hm θ)).1
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  · rw [mul_assoc,hmexp,pow_two]
  · ring

theorem large_pencil_growth (N : ℕ) {κ s t K m : ℝ}
    (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hs : 0 ≤ s) (hs1 : s ≤ 1-8*κ)
    (hgap : 2*κ ≤ t-s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) t K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ K*m ∧
      InBoundedLineChart (T x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m*m^(κ/2) ≤ ((P.biUnion T).card:ℝ)*
      ((80*25921*(1+projectionGapConstant κ))*K^3*
        (1/(2:ℝ)^N)^(s*(1-κ/2))) := by
  let θ := 1-κ/2
  let u := s*θ+2*(1-θ)
  have hθ : 0 < θ := by dsimp [θ]; linarith only [hκ1]
  have hθ1 : θ < 1 := by dsimp [θ]; linarith only [hκ]
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hugap : κ ≤ t-u := by
    dsimp [u,θ]
    nlinarith only [hgap,mul_nonneg hs hκ.le]
  have hu1 : u ≤ 1 := by
    dsimp [u,θ]
    nlinarith only [hs1,hκ,mul_nonneg hs hκ.le]
  have hut : u < t := by linarith only [hugap,hκ]
  have hb := interpolated_pencil_normalized N hs hu hut hK hm
    (zero_le_one.trans hK) hθ hθ1 rfl P T hP hPchart hPball hT
  have hH := projectionGapConstant_pos hκ
  have hpot := planarPotentialConstant_gap hκ hu1 hugap
  have hK0 : 0 < K := zero_lt_one.trans_le hK
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  have h80 : (80:ℝ)^s ≤ 80 := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num) (show s ≤ 1 by linarith only [hs1,hκ])).trans
    norm_num
  have hKθ : (K*K)^θ ≤ K^2 := by
    simpa only [Real.rpow_one,pow_two] using
      Real.rpow_le_rpow_of_exponent_le (show 1 ≤ K*K by nlinarith only [hK]) hθ1.le
  have h80θ : ((80:ℝ)^s)^θ ≤ 80 := by
    calc
      _ ≤ (80:ℝ)^θ := Real.rpow_le_rpow (by positivity) h80 hθ.le
      _ ≤ 80 := by simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hθ1.le
  have hB : (25921:ℝ)^(1-θ) ≤ 25921 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1:ℝ) ≤ 25921) (show 1-θ ≤ 1 by linarith only [hθ])
  have hker : (K*(80*(1/(2:ℝ)^N))^s*K)^θ ≤
      80*K^2*(1/(2:ℝ)^N)^(s*θ) := by
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le]
    rw [show K*((80:ℝ)^s*(1/(2:ℝ)^N)^s)*K =
      ((K*K)*(80:ℝ)^s)*(1/(2:ℝ)^N)^s by ring,
      Real.mul_rpow (by positivity) (by positivity),
      Real.mul_rpow (by positivity) (by positivity),← Real.rpow_mul hδ.le]
    calc
      _ ≤ K^2*80*(1/(2:ℝ)^N)^(s*θ) := by gcongr
      _ = _ := by ring
  have hpotbound : 1+K*planarPotentialConstant u t ≤ K*(1+projectionGapConstant κ) := by
    nlinarith only [mul_le_mul_of_nonneg_left hpot hK0.le,hK]
  have hbound : ((K*(80*(1/(2:ℝ)^N))^s*K)^θ*(25921:ℝ)^(1-θ))*
      (1+K*planarPotentialConstant u t) ≤
        (80*25921*(1+projectionGapConstant κ))*K^3*(1/(2:ℝ)^N)^(s*θ) := by
    calc
      _ ≤ (80*K^2*(1/(2:ℝ)^N)^(s*θ))*25921*(K*(1+projectionGapConstant κ)) := by
        apply mul_le_mul
        · exact mul_le_mul hker hB (by positivity) (by positivity)
        · exact hpotbound
        · have hp := planarPotentialConstant_pos hut; positivity
        · positivity
      _ = _ := by ring
  have hexp : 1-θ = κ/2 := by dsimp [θ]; ring
  rw [hexp] at hb hbound
  exact hb.trans (mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg _))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_PencilGainAlgebra
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The explicit pencil-size dichotomy behind the normalized regular gain. -/
namespace Falconer

theorem small_pencil_gain_bound {δ Δ s γ η E m : ℝ} (hδ : 0 < δ)
    (hΔ : 0 < Δ) (he : δ = Δ^2)
    (hbudget : δ^(-(γ+η)) ≤ E) (hm : m ≤ 1/δ^(s+γ)) :
    m/δ^(s+η) ≤ E/(Δ^s)^4 := by
  have hden : (Δ^s)^4 = δ^(2*s) := by
    rw [he,← Real.rpow_mul_natCast hΔ.le s 4,← Real.rpow_natCast_mul hΔ.le 2 (2*s)]
    norm_num only [Nat.cast_ofNat]
    congr 1
    ring
  have hinv (a : ℝ) : 1/δ^a = δ^(-a) := by
    rw [Real.rpow_neg hδ.le,one_div]
  calc
    _ ≤ (1/δ^(s+γ))/δ^(s+η) := div_le_div_of_nonneg_right hm (by positivity)
    _ = δ^(-(γ+η))/δ^(2*s) := by
      rw [div_eq_mul_one_div,hinv,hinv,div_eq_mul_one_div,hinv,
        ← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring
    _ ≤ E/δ^(2*s) := div_le_div_of_nonneg_right hbudget (by positivity)
    _ = _ := by rw [hden]

theorem large_pencil_gain_contradiction {δ κ s γ η A K m U : ℝ}
    (hδ : 0 < δ) (hκ : 0 ≤ κ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hm : 0 < m)
    (hrel : γ*(κ/2) = 4*η) (hbudget : 2*A*K^3 ≤ δ^(-3*η))
    (hlarge : 1/δ^(s+γ) ≤ m)
    (hgrowth : m*m^(κ/2) ≤ U*(A*K^3*δ^(s*(1-κ/2)))) :
    ¬ U ≤ m/δ^(s+η) := by
  intro hsmall
  have hcost : A*K^3*δ^(s*(1-κ/2))/δ^(s+η) ≤
      (1/2)*δ^(-(s+γ)*(κ/2)) := by
    calc
      _ = (A*K^3)*δ^(s*(1-κ/2)-(s+η)) := by
        rw [Real.rpow_sub hδ]
        ring
      _ ≤ (δ^(-3*η)/2)*δ^(s*(1-κ/2)-(s+η)) :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hbudget]) (by positivity)
      _ = (1/2)*δ^(-3*η+(s*(1-κ/2)-(s+η))) := by
        rw [Real.rpow_add hδ]
        ring
      _ = _ := by congr 2; nlinarith only [hrel]
  have hgrowth' : m^(κ/2) ≤ A*K^3*δ^(s*(1-κ/2))/δ^(s+η) := by
    apply (mul_le_mul_iff_right₀ hm).1
    calc
      _ ≤ U*(A*K^3*δ^(s*(1-κ/2))) := hgrowth
      _ ≤ (m/δ^(s+η))*(A*K^3*δ^(s*(1-κ/2))) := by
        exact mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  have hlower : δ^(-(s+γ)*(κ/2)) ≤ m^(κ/2) := by
    have hh := Real.rpow_le_rpow (by positivity : 0 ≤ 1/δ^(s+γ)) hlarge
      (show 0 ≤ κ/2 by positivity)
    rw [one_div,← Real.rpow_neg hδ.le,← Real.rpow_mul hδ.le] at hh
    exact hh
  have hpos : 0 < δ^(-(s+γ)*(κ/2)) := by positivity
  linarith only [hlower,hgrowth'.trans hcost,hpos]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_NormalizedRegularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The good-scale estimate normalized by the actual pencil cardinality.
Small pencils use the regular-set theorem, and large pencils use the
interpolated second moment. No upper bound on the union is assumed. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem normalized_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
      ∀ n : ℕ, N0 ≤ n+2 →
        let Δ := 1/(2:ℝ)^n
        let δ := 1/(2:ℝ)^(2*n)
        let ρ := 1/(2:ℝ)^(n+3)
        let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
        ∀ s t m : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
        ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
          FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ t K P →
          ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
        ∀ V : Space 2 → Finset (Space 2),
          (∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K*m ∧
            InBoundedLineChart (V p) ∧ FiniteSeparatedAt δ (V p) ∧
            NormalizedFiniteBallBound δ s K (V p) ∧
            ∀ l ∈ V p, |l 0| ≤ 1/2 ∧ TubeIncident δ p l) →
          ¬ ((P.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨θ,N1,hθ,_,hN1,hgain⟩ := bounded_chart_regular_fine_gain hκ hκ1
  let A := 80*25921*(1+projectionGapConstant κ)
  have hA : 0 ≤ A := by
    have hh := projectionGapConstant_pos hκ
    dsimp [A]
    positivity
  obtain ⟨ε,γ,η,N2,hε,hε1,_,hη,hN2,hrel,hbudget⟩ :=
    normalized_regular_gain_budget hκ hκ1 hθ hA
  refine ⟨ε,η,max N1 N2,hε,hε1,hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m hs hs1 hgap ht hm P hP hPchart hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(2*n)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let E := Real.exp (θ*((n+2:ℕ):ℝ)*Real.log 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hδeq : δ = Δ^2 := by
    dsimp [δ,Δ]
    rw [show 2*n = n*2 by omega,pow_mul,div_pow,one_pow]
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  obtain ⟨hKE,hEpower,hcost⟩ := hbudget n ((le_max_right _ _).trans hn)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have mono {u : ℝ} {F : Finset (Space 2)} (hb : NormalizedFiniteBallBound δ u K F) :
      NormalizedFiniteBallBound δ u E F := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKE (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  by_cases hmSmall : m ≤ 1/δ^(s+γ)
  · have hsmall' : ((P.biUnion V).card:ℝ) ≤ E/(Δ^s)^4 :=
      hsmall.trans (small_pencil_gain_bound hδ hΔ hδeq hEpower hmSmall)
    refine hgain n ((le_max_left _ _).trans hn) s t hs hs1 hgap ht P hP hPchart
      ?_ ?_ ?_ V ?_ hsmall'
    · rw [← hδeq]
      exact hPsep
    · rw [← hδeq]
      exact mono hPball
    · exact hPcover.trans (div_le_div_of_nonneg_right hKE (by positivity))
    · intro p hp
      have hv := hV p hp
      refine ⟨Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le hv.1)),hv.2.2.1,?_,?_,?_⟩
      · rw [← hδeq]
        exact hv.2.2.2.1
      · rw [← hδeq]
        exact mono hv.2.2.2.2.1
      · rw [← hδeq]
        exact hv.2.2.2.2.2
  · have hlarge := large_pencil_growth (2*n) hκ hκ1 hs0 hs1 hgap hK hm
      P V hP hPchart hPball (fun p hp => by
        have hv := hV p hp
        exact ⟨hv.1,hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,
          fun l hl => (hv.2.2.2.2.2 l hl).2⟩)
    exact large_pencil_gain_contradiction hδ hκ.le hA (zero_le_one.trans hK) hm
      hrel hcost (le_of_lt (lt_of_not_ge hmSmall)) hlarge hsmall

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_SquashCover
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The slope-chart change also preserves the needed coarse point cover. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem planarSquash_coarse_cover {ρ : ℝ} (hρ : 0 < ρ) (P : Finset (Space 2)) :
    (((P.image planarSquash).image (coarsePlanarRound (ρ/2))).card:ℝ) ≤
      25*((P.image (coarsePlanarRound ρ)).card:ℝ) := by
  let C := P.image (coarsePlanarRound ρ)
  let S := fun c => P.filter fun p => coarsePlanarRound ρ p = c
  let A := fun c => ((S c).image planarSquash).image (coarsePlanarRound (ρ/2))
  have hρ' : 0 < ρ/2 := by positivity
  have hA (c : Space 2) (_hc : c ∈ C) : ((A c).card:ℝ) ≤ 25 := by
    have hwithin : ∀ z ∈ A c, dist z (planarSquash c) ≤ 2*(ρ/2) := by
      intro z hz
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
      have hpc := (Finset.mem_filter.mp hp).2
      have hd := coarsePlanarRound_near hρ p
      rw [hpc] at hd
      have hsq : dist (planarSquash p) (planarSquash c) ≤ ρ/4 :=
        (planarSquash_dist_bounds p c).1.trans (div_le_div_of_nonneg_right hd (by norm_num))
      have hnear := coarsePlanarRound_near hρ' (planarSquash p)
      rw [dist_comm] at hnear
      have htri := dist_triangle (coarsePlanarRound (ρ/2) (planarSquash p))
        (planarSquash p) (planarSquash c)
      linarith only [hnear,htri,hsq,hρ]
    have hh := separated_ball_card (A c) (planarSquash c) hρ'
      (r := 2*(ρ/2)) (by positivity)
      (coarsePlanarRound_separated hρ' ((S c).image planarSquash)) hwithin
    have he : (2*(2*(ρ/2))/(ρ/2)+1)^2 = (25:ℝ) := by field_simp; ring
    rwa [he] at hh
  have hcover : (P.image planarSquash).image (coarsePlanarRound (ρ/2)) ⊆ C.biUnion A := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hv
    refine Finset.mem_biUnion.mpr ⟨coarsePlanarRound ρ p,Finset.mem_image_of_mem _ hp,?_⟩
    exact Finset.mem_image_of_mem _ (Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hp,rfl⟩))
  calc
    _ ≤ ((C.biUnion A).card:ℝ) := Nat.cast_le.mpr (Finset.card_le_card hcover)
    _ ≤ ∑ c ∈ C, ((A c).card:ℝ) := by exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _c ∈ C, (25:ℝ) := Finset.sum_le_sum hA
    _ = _ := by simp; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_SquashedPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original bounded-chart pencils, thinned by a fixed factor and moved
to the slope chart required by the regular incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem squashedPencils_at (V : Space 2 → Finset (Space 2)) (p : Space 2) :
    squashedPencils V (planarSquash p) = (V p).image planarSquash := by
  rw [squashedPencils,planarSquash_leftInverse]

theorem squashedPencils_union (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    (P.image planarSquash).biUnion (squashedPencils V) = (P.biUnion V).image planarSquash := by
  ext l
  constructor
  · intro hl
    obtain ⟨z,hz,hl⟩ := Finset.mem_biUnion.mp hl
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hz
    rw [squashedPencils_at] at hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨p,hp,ha⟩)
  · intro hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨p,hp,ha⟩ := Finset.mem_biUnion.mp ha
    refine Finset.mem_biUnion.mpr ⟨planarSquash p,Finset.mem_image_of_mem _ hp,?_⟩
    rw [squashedPencils_at]
    exact Finset.mem_image_of_mem _ ha

theorem squashedPencils_union_card (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2)) :
    ((P.image planarSquash).biUnion (squashedPencils V)).card = (P.biUnion V).card := by
  rw [squashedPencils_union,Finset.card_image_of_injective _ planarSquash_injective]

theorem squashed_pencil_configuration {δ s t K m M : ℝ}
    (hδ : 0 < δ) (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ M ∧
      InBoundedLineChart (V p) ∧ FiniteSeparatedAt δ (V p) ∧
      NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l) :
    ∃ R ⊆ P, R.Nonempty ∧ (P.card:ℝ) ≤ 81*(R.card:ℝ) ∧
      let Q := R.image planarSquash
      InBoundedLineChart Q ∧ FiniteSeparatedAt (δ/4) Q ∧
      NormalizedFiniteBallBound (δ/4) t (20736*K) Q ∧
      ∃ W : Space 2 → Finset (Space 2),
        (∀ p ∈ R, W p ⊆ V p) ∧
        (∀ q ∈ Q, m/81 ≤ ((squashedPencils W q).card:ℝ) ∧
          ((squashedPencils W q).card:ℝ) ≤ M ∧
          InBoundedLineChart (squashedPencils W q) ∧
          FiniteSeparatedAt (δ/4) (squashedPencils W q) ∧
          NormalizedFiniteBallBound (δ/4) s (20736*K) (squashedPencils W q) ∧
          ∀ l ∈ squashedPencils W q, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) q l) ∧
        (((Q.biUnion (squashedPencils W)).card:ℝ) ≤ ((P.biUnion V).card:ℝ)) := by
  obtain ⟨R,hRP,hR,hRsep,hRcard⟩ := quadruple_separated_subset hδ P hP hPsep
  have hselect : ∀ p, ∃ S : Finset (Space 2), p ∈ R →
      S ⊆ V p ∧ S.Nonempty ∧ FiniteSeparatedAt (4*δ) S ∧ ((V p).card:ℝ) ≤ 81*(S.card:ℝ) := by
    intro p
    by_cases hp : p ∈ R
    · have hv := hV p (hRP hp)
      have hn : (V p).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (hm.trans_le hv.1))
      obtain ⟨S,hS⟩ := quadruple_separated_subset hδ (V p) hn hv.2.2.2.1
      exact ⟨S,fun _ => hS⟩
    · exact ⟨∅,fun h => False.elim (hp h)⟩
  choose W hW using hselect
  have h81 : 1 ≤ K*81 := by linarith only [hK]
  have hpow (u : ℝ) (hu : u ≤ 2) : (K*81)*(16:ℝ)^u ≤ 20736*K := by
    have hh : (16:ℝ)^u ≤ 256 := by
      calc
        _ ≤ (16:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hu
        _ = 256 := by norm_num
    nlinarith only [mul_le_mul_of_nonneg_left hh (by linarith only [hK] : 0 ≤ K*81)]
  have mono {u A B : ℝ} {S : Finset (Space 2)} (hAB : A ≤ B)
      (hball : NormalizedFiniteBallBound (δ/4) u A S) :
      NormalizedFiniteBallBound (δ/4) u B S := by
    intro z r hr hr1
    exact (hball z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (by linarith only [hr,hδ]) _))
        (Nat.cast_nonneg _))
  refine ⟨R,hRP,hR,hRcard,planarSquash_chart R (fun p hp => hPchart p (hRP hp)),
    planarSquash_separated R hRsep,?_,W,(fun p hp => (hW p hp).1),?_,?_⟩
  · exact mono (hpow t ht2) (planarSquash_regular hδ ht h81 R
      (normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hRP hRcard hPball))
  · intro q hq
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hq
    rw [squashedPencils_at,Finset.card_image_of_injective _ planarSquash_injective]
    obtain ⟨hWV,hWne,hWsep,hWcard⟩ := hW p hp
    have hv := hV p (hRP hp)
    refine ⟨?_,?_,planarSquash_chart (W p) (fun l hl => hv.2.2.1 l (hWV hl)),
      planarSquash_separated (W p) hWsep,?_,?_⟩
    · exact (div_le_iff₀ (by norm_num : (0:ℝ) < 81)).2 (by linarith only [hv.1,hWcard])
    · exact (Nat.cast_le.mpr (Finset.card_le_card hWV)).trans hv.2.1
    · exact mono (hpow s hs2) (planarSquash_regular hδ hs h81 (W p)
        (normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hWV hWcard hv.2.2.2.2.1))
    · intro l hl
      obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
      exact ⟨planarSquash_slope (hv.2.2.1 a (hWV ha)).1,
        planarSquash_incident hδ.le (hv.2.2.2.2.2 a (hWV ha))⟩
  · rw [squashedPencils_union_card]
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨p,hp,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨p,hRP hp,(hW p hp).1 hl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_FullChartRegularGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pencil-normalized gain for the full bounded point and line chart.
The fixed change of slope chart preserves original incidences and pays only
the explicitly proved finite thinning and covering losses. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem full_chart_regular_fine_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
      ∀ n : ℕ, N0 ≤ n+2 →
        let Δ := 1/(2:ℝ)^n
        let δ := 1/(2:ℝ)^(2*n)
        let ρ := 1/(2:ℝ)^(n+3)
        let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
        ∀ s t m : ℝ, κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
        ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P →
          FiniteSeparatedAt δ P → NormalizedFiniteBallBound δ t K P →
          ((P.image (coarsePlanarRound ρ)).card:ℝ) ≤ K/Δ^t →
        ∀ V : Space 2 → Finset (Space 2),
          (∀ p ∈ P, m ≤ ((V p).card:ℝ) ∧ ((V p).card:ℝ) ≤ K*m ∧
            InBoundedLineChart (V p) ∧ FiniteSeparatedAt δ (V p) ∧
            NormalizedFiniteBallBound δ s K (V p) ∧ ∀ l ∈ V p, TubeIncident δ p l) →
          ¬ ((P.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨θ,η,N1,hθ,_,hη,hN1,hgain⟩ := normalized_regular_fine_gain hκ hκ1
  obtain ⟨ε,N2,hε,hε1,_,hbudget⟩ := squash_gain_budget hθ hη
  refine ⟨ε,η/2,max N1 N2,hε,hε1,half_pos hη,lt_of_lt_of_le hN1 (le_max_left _ _),?_⟩
  intro n hn
  dsimp only
  intro s t m hs hs1 hgap ht hm P hP hPchart hPsep hPball hPcover V hV hsmall
  let Δ := 1/(2:ℝ)^n
  let δ := 1/(2:ℝ)^(2*n)
  let ρ := 1/(2:ℝ)^(n+3)
  let K := Real.exp (ε*((n+2:ℕ):ℝ)*Real.log 2)
  let Δ' := 1/(2:ℝ)^(n+1)
  let E := Real.exp (θ*((n+3:ℕ):ℝ)*Real.log 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hΔ' : 0 < Δ' := by dsimp [Δ']; positivity
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by positivity)
  have hK0 : 0 < K := Real.exp_pos _
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hs2 : s ≤ 2 := by linarith only [hs1,hκ]
  have ht0 : 0 ≤ t := by linarith only [hs0,hgap,hκ]
  obtain ⟨hKE,h81⟩ := hbudget n ((le_max_right _ _).trans hn)
  have hΔeq : Δ' = Δ/2 := by dsimp [Δ',Δ]; rw [pow_succ]; ring
  have hδeq : 1/(2:ℝ)^(2*(n+1)) = δ/4 := by
    dsimp [δ]
    rw [show 2*(n+1) = 2*n+2 by omega,pow_add]
    norm_num
    ring
  have hρeq : 1/(2:ℝ)^((n+1)+3) = ρ/2 := by
    dsimp [ρ]
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]
    ring
  obtain ⟨R,hRP,hR,_,hchart,hsep,hball,W,_,hdata,hunion⟩ :=
    squashed_pencil_configuration hδ hs0 hs2 ht0 ht hK hm P V hP hPchart hPsep hPball hV
  have h25 : 25*K ≤ E := (by linarith only [hK0] : 25*K ≤ 20736*K).trans hKE
  have h81K : 81*K ≤ E := (by linarith only [hK0] : 81*K ≤ 20736*K).trans hKE
  have mono {u : ℝ} {S : Finset (Space 2)}
      (hb : NormalizedFiniteBallBound (δ/4) u (20736*K) S) :
      NormalizedFiniteBallBound (δ/4) u E S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hKE (Real.rpow_nonneg (by linarith only [hr,hδ]) _))
        (Nat.cast_nonneg _))
  have hcover : ((((R.image planarSquash).image (coarsePlanarRound (ρ/2))).card:ℝ)) ≤ E/Δ'^t := by
    calc
      _ ≤ 25*((R.image (coarsePlanarRound ρ)).card:ℝ) := planarSquash_coarse_cover hρ R
      _ ≤ 25*((P.image (coarsePlanarRound ρ)).card:ℝ) := mul_le_mul_of_nonneg_left
        (Nat.cast_le.mpr (Finset.card_le_card (Finset.image_subset_image hRP))) (by norm_num)
      _ ≤ 25*(K/Δ^t) := mul_le_mul_of_nonneg_left hPcover (by norm_num)
      _ = (25*K)/Δ^t := by ring
      _ ≤ E/Δ'^t := by
        gcongr
        rw [hΔeq]
        linarith only [hΔ]
  have hden : 81*(δ/4)^(s+η) ≤ δ^(s+η/2) := by
    calc
      _ ≤ 81*δ^(s+η) := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (by positivity) (by linarith only [hδ]) (by linarith only [hs0,hη]))
        (by norm_num)
      _ ≤ δ^(-η/2)*δ^(s+η) := mul_le_mul_of_nonneg_right h81 (by positivity)
      _ = δ^(s+η/2) := by rw [← Real.rpow_add hδ]; congr 1; ring
  have hsize : m/δ^(s+η/2) ≤ (m/81)/(δ/4)^(s+η) := by
    calc
      _ ≤ m/(81*(δ/4)^(s+η)) := div_le_div_of_nonneg_left hm.le (by positivity) hden
      _ = _ := by ring
  refine hgain (n+1) (by have := (le_max_left N1 N2).trans hn; omega) s t (m/81) hs hs1 hgap ht
    (by positivity) (R.image planarSquash) (hR.image _) hchart ?_ ?_ ?_
      (squashedPencils W) ?_ ?_
  · rw [hδeq]
    exact hsep
  · rw [hδeq]
    convert mono hball using 1
  · rw [hρeq]
    convert hcover using 1
  · intro q hq
    obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hdata q hq
    rw [hδeq]
    refine ⟨hlo,?_,hch,hsp,?_,hinc⟩
    · calc
        _ ≤ K*m := hhi
        _ = (81*K)*(m/81) := by ring
        _ ≤ E*(m/81) := mul_le_mul_of_nonneg_right h81K (by positivity)
    · convert mono hb using 1
  · rw [hδeq]
    exact hunion.trans (hsmall.trans hsize)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Geometry_ParentEndpointGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Hereditary endpoint geometry with loss measured in the active parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_endpoint_geometry {N a₀ : ℕ}
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
      M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i))) :
    let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let a := blockDepth N B i
    let b := blockDepth N B j
    let F := localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
    let ZC := ((prefixChildren C a b p₀).image (fun r => (Q.descendant r).center)).image F
    let ZS := ((prefixChildren S a b p₀).image (fun r => (Q.descendant r).center)).image F
    ZS.Nonempty ∧ ZS ⊆ ZC ∧ InBoundedLineChart ZS ∧
      FiniteSeparatedAt (1/(2:ℝ)^(b-a)) ZS ∧
      (ZC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(ZS.card:ℝ) ∧
      ∀ s A : ℝ, 0 ≤ A → NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s A ZC →
        NormalizedFiniteBallBound (1/(2:ℝ)^(b-a)) s (A*(M*(2:ℝ)^(2*i+2*j))) ZS := by
  let C := classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)
  let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
  have hsubC : S ⊆ C := hsub.trans (Finset.filter_subset _ _)
  let a := blockDepth N B i
  let b := blockDepth N B j
  let F := localPacketPoint (1/(2:ℝ)^a) ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  let DC := prefixChildren C a b p₀
  let DS := prefixChildren S a b p₀
  let ZC := (DC.image (fun r => (Q.descendant r).center)).image F
  let ZS := (DS.image (fun r => (Q.descendant r).center)).image F
  have hCN : C ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL
  have hSN : S ⊆ cubePaths 2 N := (Finset.filter_subset _ _).trans hL'
  have hab : a ≤ b := blockDepth_antitone N B hji
  have hbn : b ≤ N := Nat.sub_le _ _
  obtain ⟨hcC,_,_⟩ := local_prefix_centers_geometry Q hQ C hCN hab hbn p₀
  obtain ⟨hcS,hchart,hsep⟩ := local_prefix_centers_geometry Q hQ S hSN hab hbn p₀
  have hDS : DS ⊆ DC := Finset.image_subset_image (Finset.filter_subset_filter _ hsubC)
  have hZS : ZS ⊆ ZC := Finset.image_subset_image (Finset.image_subset_image hDS)
  have hne : ZS.Nonempty := ((prefixFiber_nonempty hp₀).image _).image _ |>.image _
  have hret := blockClass_parent_child_retention hL hL' B f g K p q r₀ hsub hM hmass hji hi ha₀ hp₀
  change (DC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(DS.card:ℝ) at hret
  have hcount : (ZC.card:ℝ) ≤ (M*(2:ℝ)^(2*i+2*j))*(ZS.card:ℝ) := by
    change ZC.card = DC.card at hcC
    change ZS.card = DS.card at hcS
    simpa only [hcC,hcS] using hret
  refine ⟨hne,hZS,hchart,hsep,hcount,?_⟩
  intro s A hA hball
  exact normalized_finite_ball_bound_subset (by positivity) hA hZS hcount hball


end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CriticalPencilIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-scale incidence estimate, with matching point and pencil
exponents. The loss at the critical potential is linear in the dyadic depth. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem pencil_critical_second_moment (N : ℕ) {s K M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, InBoundedLineChart (T x) ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ((T x).card:ℝ) ≤ M ∧ ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
      (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)*(P.card:ℝ)^2 := by
  let δ := 1/(2:ℝ)^N
  let C := K*(80*δ)^s*M
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ1 : δ ≤ 1 := (div_le_one (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hrow (x : Space 2) (hx : x ∈ P) :
      (∑ y ∈ P, ((T x ∩ T y).card:ℝ)) ≤
        C*(1+K*planarCriticalConstant N s)*(P.card:ℝ) := by
    have hM : 0 ≤ M := (Nat.cast_nonneg _).trans (hT x hx).2.2.1
    have hC : 0 ≤ C := by dsimp [C]; positivity
    have hpot := finite_dyadic_critical_potential_real P x N hK hs hPball
    calc
      _ ≤ ∑ y ∈ P, C*(1+(1/max (dist x y) δ)^s) := by
        apply Finset.sum_le_sum
        intro y hy
        apply (intersect_tube_power_bound hδ hδ1 hs hK (T x) (T y) x y
          (hPchart x hx).1 (hT x hx).1 (hT x hx).2.2.2
          (hT y hy).2.2.2 (hT x hx).2.1).trans
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hT x hx).2.2.1
          (by positivity)) (by positivity)
      _ = C*((P.card:ℝ)+∑ y ∈ P, (1/max (dist x y) δ)^s) := by
        simp only [mul_add,Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,mul_one]
        rw [← Finset.mul_sum]
        ring
      _ ≤ C*((P.card:ℝ)+K*planarCriticalConstant N s*(P.card:ℝ)) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hpot) hC
      _ = _ := by ring
  calc
    _ ≤ ∑ _x ∈ P, C*(1+K*planarCriticalConstant N s)*(P.card:ℝ) :=
      Finset.sum_le_sum hrow
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul]; dsimp [C]; ring

theorem planar_critical_variable_incidence (N : ℕ) {s K m M : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 ≤ m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ M ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m^2 ≤ ((P.biUnion T).card:ℝ)*
      ((K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)) := by
  let C := (K*(80*(1/(2:ℝ)^N))^s*M)*(1+K*planarCriticalConstant N s)
  have hI : m*(P.card:ℝ) ≤ ∑ x ∈ P, ((T x).card:ℝ) := by
    calc
      _ = ∑ _x ∈ P, m := by simp; ring
      _ ≤ ∑ x ∈ P, ((T x).card:ℝ) := Finset.sum_le_sum fun x hx => (hT x hx).1
  have hE := pencil_critical_second_moment N hs hK P T hPchart hPball
    (fun x hx => ⟨(hT x hx).2.2.1,(hT x hx).2.2.2.1,(hT x hx).2.1,(hT x hx).2.2.2.2⟩)
  have hh : (m*(P.card:ℝ))^2 ≤ ((P.biUnion T).card:ℝ)*(C*(P.card:ℝ)^2) := by
    calc
      _ ≤ (∑ x ∈ P, ((T x).card:ℝ))^2 :=
        (sq_le_sq₀ (by positivity) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)).2 hI
      _ ≤ ((P.biUnion T).card:ℝ)*(∑ x ∈ P, ∑ y ∈ P, ((T x ∩ T y).card:ℝ)) :=
        tube_union_second_moment P T
      _ ≤ _ := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)
  have hPc : 0 < (P.card:ℝ) := Nat.cast_pos.mpr hP.card_pos
  apply (mul_le_mul_iff_left₀ (sq_pos_of_pos hPc)).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

theorem planar_critical_normalized_incidence (N : ℕ) {s K m R : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    m ≤ ((P.biUnion T).card:ℝ)*
      (R*K*(80*(1/(2:ℝ)^N))^s*(1+K*planarCriticalConstant N s)) := by
  have hh := planar_critical_variable_incidence N hs hK hm.le P T hP hPchart hPball hT
  apply (mul_le_mul_iff_left₀ hm).1
  first | (convert hh using 1 <;> ring) | exact (le_of_eq (by ring)).trans (hh.trans (le_of_eq (by ring)))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_NormalProfileIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal-interval factor in the multiscale product, evaluated on the
actual retained endpoint configuration. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem planar_critical_normalized_ratio (N : ℕ) {s K m R : ℝ}
    (hs : 0 ≤ s) (hK : 1 ≤ K) (hm : 0 < m)
    (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty)
    (hPchart : InBoundedLineChart P)
    (hPball : NormalizedFiniteBallBound (1/(2:ℝ)^N) s K P)
    (hT : ∀ x ∈ P, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
      InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^N) s K (T x) ∧
      ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^N) x l) :
    (1/(2:ℝ)^N)^(-s) ≤
      (R*K*80^s*(1+K*planarCriticalConstant N s))*(((P.biUnion T).card:ℝ)/m) := by
  have hh := planar_critical_normalized_incidence N hs hK hm P T hP hPchart hPball hT
  have hδ : 0 < 1/(2:ℝ)^N := by positivity
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 80) hδ.le] at hh
  rw [← mul_div_assoc,Real.rpow_neg hδ.le]
  apply (le_div_iff₀ hm).2
  rw [← div_eq_inv_mul]
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hδ s)).2
  convert hh using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ParentProfileBounds
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Reference-profile bounds persist below an active parent and in the
fixed quarter chart used by the actual scale-product construction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockClass_parent_endpoint_ball {N a₀ : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))
    {s A : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))
    let Z := blockEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    Z.Nonempty ∧ InBoundedLineChart Z ∧
      FiniteSeparatedAt (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i)) s C Z ∧
      NormalizedFiniteBallBound (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2)) s
        ((max 1 C)*4^s)
        (quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀) := by
  have hsubC := hsub.trans (Finset.filter_subset _ _)
  have hpC := Finset.image_subset_image hsubC hp₀
  obtain ⟨_,_,hball⟩ := blockClass_truncated_local_ball hN hL B f K p Q hQ hji hi hpC
    hs hA hprofile ((Q.descendant p₀).center 0) ((Q.descendant p₀).center 1)
  obtain ⟨hne,_,hchart,hsep,_,htransfer⟩ := blockClass_parent_endpoint_geometry
    hL hL' B f g K p q r₀ hsub hM hmass Q hQ hji hi ha₀ hp₀
  have hretained := htransfer s _ (by positivity) hball
  refine ⟨hne,hchart,hsep,hretained,?_⟩
  rw [quarterEndpointSet_eq]
  have he : (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i))/4 =
      1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2) := by
    rw [pow_add]
    norm_num
    ring
  rw [← he]
  apply planarQuarter_regular (by positivity) hs (le_max_left _ _)
  exact normalizedFiniteBallBound_mono_constant (by positivity) (le_max_right _ _) hretained

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_ParentQuarterIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal and good interval bounds in the fixed chart of the recursive
endpoint construction. Retention is measured inside the active parent. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

section Parent
variable {N a₀ : ℕ} (hN : 0 < N)
    {L L' : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hL' : L' ⊆ cubePaths 2 N)
    (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2)
    (hsub : classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
      prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀)
    {M : ℝ} (hM : 0 ≤ M)
    (hmass : ((prefixFiber (classLeaves L (blockLabel L N B f K)
      (blockLabel L N B f K p)) a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ))
    (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) (ha₀ : a₀ ≤ blockDepth N B i) {p₀ : CellPath 2}
    (hp₀ : p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)))

include hN hL hL' hsub hM hmass hQ hji hi ha₀ hp₀ in
theorem blockClass_parent_quarter_normal_ratio {s A KL : ℝ} (hs : 0 ≤ s) (hA : 0 ≤ A)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    let D := blockDepth N B j-blockDepth N B i+2
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(M*(2:ℝ)^(2*i+2*j))
    let H := max 1 (max KL ((max 1 C)*4^s))
    ∀ m R : ℝ, 0 < m → ∀ T : Space 2 → Finset (Space 2),
      (∀ x ∈ Z, m ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ R*m ∧
        InBoundedLineChart (T x) ∧ NormalizedFiniteBallBound (1/(2:ℝ)^D) s KL (T x) ∧
        ∀ l ∈ T x, TubeIncident (1/(2:ℝ)^D) x l) →
      (1/(2:ℝ)^D)^(-s) ≤
        (R*H*80^s*(1+H*planarCriticalConstant D s))*(((Z.biUnion T).card:ℝ)/m) := by
  obtain ⟨hne,_,_,_,hball⟩ := blockClass_parent_endpoint_ball hN hL hL' B f g K p q r₀
    hsub hM hmass Q hQ hji hi ha₀ hp₀ hs hA hprofile
  have hquarter := hne.image planarQuarter
  rw [← quarterEndpointSet_eq] at hquarter
  have hchart := (quarterEndpointSet_geometry Q hQ
    (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
    ((Finset.filter_subset _ _).trans hL') (blockDepth_antitone N B hji)
    (Nat.sub_le _ _) p₀).2.1
  dsimp only
  intro m R hm T hT
  apply planar_critical_normalized_ratio _ hs (le_max_left _ _) hm _ T hquarter
  · intro x hx
    exact ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩
  · exact normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_right _ _).trans (le_max_right _ _)) hball
  · intro x hx
    obtain ⟨hlo,hhi,hch,hb,hinc⟩ := hT x hx
    exact ⟨hlo,hhi,hch,normalizedFiniteBallBound_mono_constant (by positivity)
      ((le_max_left _ _).trans (le_max_right _ _)) hb,hinc⟩

include hN hL hsub hQ hji hi hp₀ in
theorem blockClass_parent_quarter_midscale_cover {n : ℕ} (hn : 3 ≤ n)
    (hlen : blockDepth N B j-blockDepth N B i = 2*n) {t A : ℝ} (ht : 0 ≤ t)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
        regularizedProfile L F N B K p (blockDepth N B i)) ≤
          t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) :
    let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
    let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
    ((Z.image (coarsePlanarRound (1/(2:ℝ)^((n+1)+3)))).card:ℝ) ≤
      (25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))))/(1/(2:ℝ)^(n+1))^t := by
  have hc := blockClass_retained_midscale_cover hN hL B f g K p q
    (hsub.trans (Finset.filter_subset _ _)) Q hQ hji hi hp₀ hn hlen ht hprofile
  dsimp only
  rw [quarterEndpointSet_eq]
  have he : 1/(2:ℝ)^((n+1)+3) = (1/(2:ℝ)^(n+3))/2 := by
    rw [show (n+1)+3 = (n+3)+1 by omega,pow_succ]; ring
  rw [he]
  calc
    _ ≤ 25*((blockEndpointSet Q _ _ _ p₀ |>.image
        (coarsePlanarRound (1/(2:ℝ)^(n+3)))).card:ℝ) :=
      planarQuarter_coarse_cover (by positivity) _
    _ ≤ 25*((49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A)))/(1/(2:ℝ)^n)^t) :=
      mul_le_mul_of_nonneg_left hc (by norm_num)
    _ ≤ _ := by
      simp only [← mul_div_assoc]
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      apply Real.rpow_le_rpow (by positivity) _ ht
      apply one_div_le_one_div_of_le (by positivity)
      exact pow_le_pow_right₀ (by norm_num) (by omega)

end Parent

theorem blockClass_parent_quarter_good_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t m : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 0 < m →
    ∀ N a₀ : ℕ, 0 < N → ∀ L L' : Finset (CellPath 2),
      L ⊆ cubePaths 2 N → L' ⊆ cubePaths 2 N →
    ∀ (B : ℕ) (f g : CellPath 2 → List ℕ) (K : ℕ) (p q r₀ : CellPath 2),
      classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q) ⊆
        prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p)) a₀ r₀ →
    ∀ M : ℝ, 0 ≤ M →
      ((prefixFiber (classLeaves L (blockLabel L N B f K) (blockLabel L N B f K p))
        a₀ r₀).card:ℝ) ≤
        M*((classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).card:ℝ) →
    ∀ Q : DyadicCube 2, Q.side = 1 → ∀ i j : ℕ, j ≤ i → i ≤ K → a₀ ≤ blockDepth N B i →
    ∀ p₀ ∈ (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)).image
      (List.take (blockDepth N B i)), blockDepth N B j-blockDepth N B i = 2*n →
    ∀ A : ℝ, 0 ≤ A →
      (∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
        let v := (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))
        t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤ v ∧
          v ≤ t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) →
      let E := Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2)
      (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
        (M*(2:ℝ)^(2*i+2*j))))*4^t ≤ E →
      25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤ E →
      let S := classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q)
      let Z := quarterEndpointSet Q S (blockDepth N B i) (blockDepth N B j) p₀
      let δ := 1/(2:ℝ)^(2*n+2)
      ∀ V : Space 2 → Finset (Space 2),
        (∀ z ∈ Z, m ≤ ((V z).card:ℝ) ∧ ((V z).card:ℝ) ≤ E*m ∧
          InBoundedLineChart (V z) ∧ FiniteSeparatedAt δ (V z) ∧
          NormalizedFiniteBallBound δ s E (V z) ∧ ∀ l ∈ V z, TubeIncident δ z l) →
        ¬ ((Z.biUnion V).card:ℝ) ≤ m/δ^(s+η) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgain⟩ := full_chart_regular_fine_gain hκ hκ1
  refine ⟨ε,η,max N0 6,hε,hε1,hη,lt_of_lt_of_le hN0 (le_max_left _ _),?_⟩
  intro n hn s t m hs hs1 hgap ht hm N a₀ hN L L' hL hL' B f g K p q r₀ hsub
    M hM hmass Q hQ i j hji hi ha₀ p₀ hp₀ hlen A hA hprofile
  dsimp only
  intro hpointBudget hcoverBudget V hV
  have hn3 : 3 ≤ n := by have := (le_max_right N0 6).trans hn; omega
  have ht0 : 0 ≤ t := by linarith only [hκ,hs,hgap]
  obtain ⟨hne,_,_,_,hball⟩ := blockClass_parent_endpoint_ball hN hL hL' B f g K p q r₀
    hsub hM hmass Q hQ hji hi ha₀ hp₀ ht0 hA (fun k hjk hki => (hprofile k hjk hki).1)
  have hquarter := hne.image planarQuarter
  rw [← quarterEndpointSet_eq] at hquarter
  obtain ⟨_,hchart,hsep⟩ := quarterEndpointSet_geometry Q hQ
    (classLeaves L' (blockLabel L' N B g K) (blockLabel L' N B g K q))
    ((Finset.filter_subset _ _).trans hL') (blockDepth_antitone N B hji) (Nat.sub_le _ _) p₀
  have hcover := blockClass_parent_quarter_midscale_cover hN hL B f g K p q r₀ hsub
    Q hQ hji hi hp₀ hn3 hlen ht0 (fun k hjk hki => (hprofile k hjk hki).2)
  rw [hlen] at hball hsep
  have he : 2*(n+1) = 2*n+2 := by omega
  have hh := hgain (n+1) (by simpa only [Nat.add_assoc] using (le_max_left N0 6).trans hn)
    s t m hs hs1 hgap ht hm _ hquarter
    (fun x hx => ⟨(hchart x hx).1.trans (by norm_num),(hchart x hx).2.trans (by norm_num)⟩)
  rw [he] at hh
  apply hh hsep
  · exact normalizedFiniteBallBound_mono_constant (by positivity) hpointBudget hball
  · exact hcover.trans (div_le_div_of_nonneg_right hcoverBudget (by positivity))
  · simpa only [Nat.add_assoc] using hV

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileEndpointBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The induction statement retains the original reference profile. Its
single budget bounds parent mass loss, pencil regularity and pencil size ratio. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem ProfileEndpointBound.mono_value {N B K i j : ℕ} {L : Finset (CellPath 2)}
    {f : CellPath 2 → List ℕ} {p : CellPath 2} {Q : DyadicCube 2} {s W A D : ℝ}
    (h : ProfileEndpointBound N B K L f p Q i j s W A) (hDA : D ≤ A) :
    ProfileEndpointBound N B K L f p Q i j s W D := by
  intro L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  exact hDA.trans (h L' g q a₀ r₀ hL' hsub hmass ha₀ p₀ hp₀ m hm V hV)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileChordBounds
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normalized chord errors give the exact unnormalized profile increments
used in finite nonconcentration and covering estimates. -/
namespace Falconer
open Set

theorem scaled_intervalSecantError (g : ℝ → ℝ) {N : ℝ} (hN : N ≠ 0)
    (a b x : ℝ) :
    N*intervalSecantError (fun t => g (N*t)) (a/N) ((b-a)/N) (x/N) =
      N*(g x-g a)-intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N)*(x-a) := by
  unfold intervalSecantError
  dsimp only
  rw [mul_div_cancel₀ _ hN,mul_div_cancel₀ _ hN]
  field_simp

theorem normalized_chord_lower (g : ℝ → ℝ) {N : ℝ} (hN : 0 < N)
    {a b x s ε : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hs : s ≤ intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N))
    (herr : ∀ t ∈ Icc (a/N) (b/N), -ε*((b-a)/N) ≤
      intervalSecantError (fun u => g (N*u)) (a/N) ((b-a)/N) t) :
    s*(x-a)-ε*(b-a) ≤ N*(g x-g a) := by
  have hx' : x/N ∈ Icc (a/N) (b/N) :=
    ⟨(div_le_div_iff_of_pos_right hN).2 hx.1,(div_le_div_iff_of_pos_right hN).2 hx.2⟩
  have he := mul_le_mul_of_nonneg_left (herr _ hx') hN.le
  rw [scaled_intervalSecantError g hN.ne'] at he
  have hcancel : N*(-ε*((b-a)/N)) = -ε*(b-a) := by field_simp
  rw [hcancel] at he
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx.1)
  linarith

theorem normalized_chord_upper (g : ℝ → ℝ) {N : ℝ} (hN : 0 < N)
    {a b x s ε : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hs : intervalSecantSlope (fun t => g (N*t)) (a/N) ((b-a)/N) ≤ s)
    (herr : ∀ t ∈ Icc (a/N) (b/N),
      intervalSecantError (fun u => g (N*u)) (a/N) ((b-a)/N) t ≤ ε*((b-a)/N)) :
    N*(g x-g a) ≤ s*(x-a)+ε*(b-a) := by
  have hx' : x/N ∈ Icc (a/N) (b/N) :=
    ⟨(div_le_div_iff_of_pos_right hN).2 hx.1,(div_le_div_iff_of_pos_right hN).2 hx.2⟩
  have he := mul_le_mul_of_nonneg_left (herr _ hx') hN.le
  rw [scaled_intervalSecantError g hN.ne'] at he
  have hcancel : N*(ε*((b-a)/N)) = ε*(b-a) := by field_simp
  rw [hcancel] at he
  have hm := mul_le_mul_of_nonneg_right hs (sub_nonneg.mpr hx.1)
  linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockProfileCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transfer the rounded real profile cells and their gains to the exact
block-index pairs used by the recursive incidence estimates. -/
namespace Falconer
open Set Regularization

theorem blockProfileCell_chord_lower (g : ℝ → ℝ) {N B i j : ℕ} (hN : 0 < N)
    {s ε : ℝ}
    (hs : s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
      (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
        ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
      -ε*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) :
    ∀ k, j ≤ k → k ≤ i →
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-
        ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) ≤
          (N:ℝ)*(g (blockDepth N B k)-g (blockDepth N B i)) := by
  intro k hjk hki
  apply normalized_chord_lower g (Nat.cast_pos.mpr hN)
    ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
      Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hs
  intro x hx
  apply herr x
  change (blockDepth N B i:ℝ)/N ≤ x ∧
    x ≤ (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N
  rw [show (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N =
    (blockDepth N B j:ℝ)/N by ring]
  exact hx

theorem blockProfileCell_chord_upper (g : ℝ → ℝ) {N B i j : ℕ} (hN : 0 < N)
    {s ε : ℝ}
    (hs : intervalSecantSlope (fun x => g ((N:ℝ)*x))
      (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ≤ s)
    (herr : ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
        ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
      intervalSecantError (fun u => g ((N:ℝ)*u))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x ≤
          ε*(blockProfileCell N B (i,j)).2) :
    ∀ k, j ≤ k → k ≤ i →
      (N:ℝ)*(g (blockDepth N B k)-g (blockDepth N B i)) ≤
        s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+
          ε*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) := by
  intro k hjk hki
  apply normalized_chord_upper g (Nat.cast_pos.mpr hN)
    ⟨Nat.cast_le.mpr (blockDepth_antitone N B hki),
      Nat.cast_le.mpr (blockDepth_antitone N B hjk)⟩ hs
  intro x hx
  apply herr x
  change (blockDepth N B i:ℝ)/N ≤ x ∧
    x ≤ (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N
  rw [show (blockDepth N B i:ℝ)/N+((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))/N =
    (blockDepth N B j:ℝ)/N by ring]
  exact hx

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNormalBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The critical second-moment estimate supplies the normal-interval base
case of the recursive profile endpoint bound. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_normal {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s A W : ℝ}
    (hs : 0 ≤ s) (hA : 0 ≤ A) (hW : 1 ≤ W)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))) :
    let D := blockDepth N B j-blockDepth N B i+2
    let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
    let H := max 1 (max W ((max 1 C)*4^s))
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^D)^(-s)/(W*H*80^s*(1+H*planarCriticalConstant D s))) := by
  let D := blockDepth N B j-blockDepth N B i+2
  let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
  let H := max 1 (max W ((max 1 C)*4^s))
  have hH : 0 < H := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hcrit : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hcost : 0 < W*H*80^s*(1+H*planarCriticalConstant D s) := by positivity
  dsimp only
  intro L' g q a₀ r₀ hL' C₀ S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hh := blockClass_parent_quarter_normal_ratio hN hL hL' B f g K p q r₀
    hsub (zero_le_one.trans hW) hmass Q hQ hji hi ha₀ hp₀ hs hA hprofile m W hm V
    (fun x hx => ⟨(hV x hx).1,(hV x hx).2.1,(hV x hx).2.2.1,
      (hV x hx).2.2.2.2.1,fun l hl => ((hV x hx).2.2.2.2.2 l hl).2⟩)
  apply (div_le_iff₀ hcost).2
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileNormalBudget
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial depth loss suffices for a normal interval once its point
and pencil constants fit the common weak budget. -/
namespace Falconer
open Regularization

theorem planarCriticalConstant_le_depth {s : ℝ} (hs : s ≤ 1) {D N : ℕ} (hD : D ≤ N+2) :
    planarCriticalConstant D s ≤ 7*((N:ℝ)+3) := by
  have h2 : (2:ℝ)^s ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 2) hs
  have hD' : (D:ℝ) ≤ N+2 := by exact_mod_cast hD
  calc
    _ ≤ 1+2*(1+(D:ℝ)*2) := by unfold planarCriticalConstant; gcongr
    _ ≤ _ := by linarith

theorem planar_normal_cost_bound {s H W E : ℝ} {D N : ℕ}
    (hs : s ≤ 1) (hD : D ≤ N+2) (hH : 1 ≤ H) (hW : 1 ≤ W) (hE : 1 ≤ E)
    (hHE : H ≤ E) (hWE : W ≤ E) :
    W*H*80^s*(1+H*planarCriticalConstant D s) ≤ 640*E^3*((N:ℝ)+3) := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hE0 : 0 ≤ E := zero_le_one.trans hE
  have h80 : (80:ℝ)^s ≤ 80 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 80) hs
  have hcrit := planarCriticalConstant_le_depth hs hD
  have hcrit0 : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hparent : 1+H*planarCriticalConstant D s ≤ 8*E*((N:ℝ)+3) := by
    have hprod : H*planarCriticalConstant D s ≤ E*(7*((N:ℝ)+3)) :=
      mul_le_mul hHE hcrit (by unfold planarCriticalConstant; positivity) hE0
    have hlarge : 1 ≤ E*((N:ℝ)+3) := one_le_mul_of_one_le_of_one_le hE
      (by have := Nat.cast_nonneg (α := ℝ) N; linarith)
    nlinarith only [hprod,hlarge]
  calc
    _ ≤ E*E*80*(8*E*((N:ℝ)+3)) := by gcongr
    _ = _ := by ring

theorem profileEndpointBound_normal_budget {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s A W E : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hA : 0 ≤ A) (hW : 1 ≤ W) (hE : 1 ≤ E) (hWE : W ≤ E)
    (hprofile : ∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
      s*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤
        (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i)))
    (hpoint : (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*
      (W*(2:ℝ)^(2*i+2*j))))*4^s ≤ E) :
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3))) := by
  have hh := profileEndpointBound_normal hN hL f p Q hQ hji hi hs hA hW hprofile
  let D := blockDepth N B j-blockDepth N B i+2
  let C := (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^s)*4^s)*(W*(2:ℝ)^(2*i+2*j))
  let H := max 1 (max W ((max 1 C)*4^s))
  have hH : 1 ≤ H := le_max_left _ _
  have hHE : H ≤ E := max_le hE (max_le hWE hpoint)
  have hD : D ≤ N+2 := by dsimp [D,blockDepth]; omega
  have hcost := planar_normal_cost_bound hs1 hD hH hW hE hHE hWE
  have hcrit : 0 ≤ planarCriticalConstant D s := by unfold planarCriticalConstant; positivity
  have hcost0 : 0 < W*H*80^s*(1+H*planarCriticalConstant D s) := by positivity
  exact hh.mono_value (div_le_div_of_nonneg_left (by positivity) hcost0 hcost)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGeometryBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Common explicit bounds for the geometric constants of all selected
normal and good intervals. The exponent range needed here is only [0,2]. -/
namespace Falconer

theorem profile_geometry_costs {K i j B : ℕ} (hi : i ≤ K) (hj : j ≤ K)
    {t A W : ℝ} (_ht : 0 ≤ t) (ht2 : t ≤ 2) (hA : 0 ≤ A) (hW : 1 ≤ W) :
    (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j))))*4^t ≤
        100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) ∧
    25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤
        100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) := by
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have h4 : (4:ℝ)^t ≤ 16 := by
    have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ) ≤ 4) ht2
    norm_num only [Real.rpow_two] at hh
    exact hh
  have hB : ((2:ℝ)^B)^t ≤ (2:ℝ)^(2*B) := by
    have hh := Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ) ≤ (2:ℝ)^B from one_le_pow₀ (by norm_num)) ht2
    simpa only [Real.rpow_two,← pow_mul,Nat.mul_comm] using hh
  let D := W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B)
  have hD : 1 ≤ D := by
    apply one_le_mul_of_one_le_of_one_le
    · apply one_le_mul_of_one_le_of_one_le
      · exact one_le_mul_of_one_le_of_one_le hW (one_le_pow₀ (by norm_num))
      · exact Real.one_le_rpow (by norm_num) hA
    · exact one_le_pow₀ (by norm_num)
  have hC : (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j)) ≤ 784*D := by
    have hp : (2:ℝ)^((i+j)+(2*i+2*j)) ≤ (2:ℝ)^(6*K) :=
      pow_le_pow_right₀ (by norm_num) (by omega)
    calc
      _ ≤ (49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*(2:ℝ)^(2*B))*16)*
          (W*(2:ℝ)^(2*i+2*j)) := by gcongr
      _ = 784*W*(2:ℝ)^((i+j)+(2*i+2*j))*(2:ℝ)^A*(2:ℝ)^(2*B) := by rw [pow_add]; ring
      _ ≤ 784*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)) (by positivity)
      _ = _ := by dsimp [D]; ring
  have hmax : max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
      (W*(2:ℝ)^(2*i+2*j))) ≤ 784*D := max_le (by linarith only [hD]) hC
  constructor
  · calc
      _ ≤ (784*D)*16 := mul_le_mul hmax h4 (Real.rpow_nonneg (by norm_num) _) (by linarith only [hD])
      _ ≤ 100000*D := by nlinarith only [hD]
      _ = _ := by dsimp [D]; ring
  · have hexp : t*((B:ℝ)+3)+A ≤ (2*B:ℕ)+6+A := by
      push_cast
      nlinarith only [mul_le_mul_of_nonneg_right ht2 (show 0 ≤ (B:ℝ)+3 by positivity)]
    calc
      _ ≤ 25*(49*((2:ℝ)^i*(2:ℝ)^(((2*B:ℕ):ℝ)+6+A))) := by gcongr; norm_num
      _ = 78400*(2:ℝ)^i*(2:ℝ)^A*(2:ℝ)^(2*B) := by
        rw [Real.rpow_add (by norm_num : (0:ℝ) < 2),
          Real.rpow_add (by norm_num : (0:ℝ) < 2),Real.rpow_natCast]
        norm_num
        ring
      _ ≤ 100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A*(2:ℝ)^(2*B) := by
        have hp : (2:ℝ)^i ≤ (2:ℝ)^(6*K) := pow_le_pow_right₀ (by norm_num) (by omega)
        have hh : (78400:ℝ) ≤ 100000*W := by linarith only [hW]
        gcongr

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGeometryPower
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the common geometric constants to powers with explicit exponents.
The chord error remains proportional to its own interval length. -/
namespace Falconer

theorem profile_normal_power_cost {N : ℕ} {q r A : ℝ}
    (hpoly : 640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ))) :
    640*((2:ℝ)^(q*(N:ℝ)+A))^3*((N:ℝ)+3) ≤
      (2:ℝ)^((3*q+r)*(N:ℝ)+3*A) := by
  calc
    _ = (640*((N:ℝ)+3))*((2:ℝ)^(q*(N:ℝ)+A))^3 := by ring
    _ ≤ (2:ℝ)^(r*(N:ℝ))*((2:ℝ)^(q*(N:ℝ)+A))^3 :=
      mul_le_mul_of_nonneg_right hpoly (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      norm_num
      ring

theorem dyadic_power_below_normal_factor (D : ℕ) {s loss C : ℝ} (hC : 0 < C)
    (hcost : C ≤ (2:ℝ)^loss) :
    (2:ℝ)^(s*(D:ℝ)-loss) ≤ (1/(2:ℝ)^D)^(-s)/C := by
  rw [dyadic_inverse_power_eq,neg_neg,Real.rpow_sub (by norm_num : (0:ℝ) < 2)]
  exact div_le_div_of_nonneg_left (by positivity) hC hcost

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockCellNormalGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal estimate evaluated directly on a selected real profile cell. -/
namespace Falconer
open Set Regularization

theorem profileGeometryConstant_ge {W A : ℝ} (hW : 1 ≤ W) (hA : 0 ≤ A) (K B : ℕ) :
    W ≤ profileGeometryConstant K B W A := by
  have h1 : W ≤ 100000*W := by nlinarith only [hW]
  have h2 : 100000*W ≤ 100000*W*(2:ℝ)^(6*K) :=
    le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have h3 : 100000*W*(2:ℝ)^(6*K) ≤ 100000*W*(2:ℝ)^(6*K)*(2:ℝ)^A :=
    le_mul_of_one_le_right (by positivity) (Real.one_le_rpow (by norm_num) hA)
  exact h1.trans (h2.trans (h3.trans (le_mul_of_one_le_right (by positivity)
    (one_le_pow₀ (by norm_num)))))

theorem block_cell_normal_gain {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s θ W : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hW : 1 ≤ W)
    (hslope : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
          ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
        -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) :
    let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
    let E := profileGeometryConstant K B W A
    ProfileEndpointBound N B K L f p Q i j s W
      ((1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3))) := by
  let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
  have hA : 0 ≤ A := mul_nonneg hθ (sub_nonneg.mpr (Nat.cast_le.mpr (blockDepth_antitone N B hji)))
  have hWE := profileGeometryConstant_ge hW hA K B
  have hpoint := (profile_geometry_costs (B := B) hi (hji.trans hi) hs
    (hs1.trans (by norm_num)) hA hW).1
  have hprofile := blockProfileCell_chord_lower (B := B) (i := i) (j := j)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope herr
  exact profileEndpointBound_normal_budget hN hL f p Q hQ hji hi hs hs1 hA hW
    (hW.trans hWE) hWE hprofile hpoint

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGoodBound
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The independently proved regular incidence gain supplies the good-interval
base case, on every retained reference class allowed by the induction. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem profileEndpointBound_good {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t W : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 1 ≤ W →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
    ∀ A : ℝ, 0 ≤ A →
      (∀ k, j ≤ k → k ≤ i → let F := blockLabel L N B f K
        let v := (N:ℝ)*(regularizedProfile L F N B K p (blockDepth N B k)-
          regularizedProfile L F N B K p (blockDepth N B i))
        t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))-A ≤ v ∧
          v ≤ t*((blockDepth N B k:ℝ)-(blockDepth N B i:ℝ))+A) →
      let E := Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2)
      (max 1 ((49*(((2:ℝ)^(i+j)*(2:ℝ)^A)*((2:ℝ)^B)^t)*4^t)*
        (W*(2:ℝ)^(2*i+2*j))))*4^t ≤ E →
      25*(49*((2:ℝ)^i*(2:ℝ)^(t*((B:ℝ)+3)+A))) ≤ E → W ≤ E →
      ProfileEndpointBound N B K L f p Q i j s W ((1/(2:ℝ)^(2*n+2))^(-(s+η))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgain⟩ := blockClass_parent_quarter_good_gain hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s t W hs hs1 hgap ht hW N B K hN L hL f p Q hQ i j hji hi hlen A hA hprofile
  dsimp only
  intro hpoint hcover hWE L' g q a₀ r₀ hL' C S hsub hmass ha₀ p₀ hp₀ m hm V Z hV
  have hbad := hgain n hn s t m hs hs1 hgap ht hm N a₀ hN L L' hL hL'
    B f g K p q r₀ hsub W (zero_le_one.trans hW) hmass Q hQ i j hji hi ha₀ p₀ hp₀ hlen
    A hA hprofile hpoint hcover V (by
      intro x hx
      obtain ⟨hlo,hhi,hch,hsp,hb,hinc⟩ := hV x hx
      rw [hlen] at hsp hb hinc
      exact ⟨hlo,hhi.trans (mul_le_mul_of_nonneg_right hWE hm.le),hch,hsp,
        normalizedFiniteBallBound_mono_constant (by positivity) hWE hb,
        fun l hl => (hinc l hl).2⟩)
  have hh := (lt_of_not_ge hbad).le
  apply (le_div_iff₀ hm).2
  rw [Real.rpow_neg (by positivity : 0 ≤ 1/(2:ℝ)^(2*n+2))]
  simpa only [div_eq_mul_inv,mul_comm] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockCellGoodGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Apply the regular incidence gain directly to a linear profile cell.
One explicit geometric constant controls all the required point and cover data. -/
namespace Falconer
open Set Regularization

theorem block_cell_good_gain {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s t W θ : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 2*κ ≤ t-s → t ≤ 2 → 1 ≤ W → 0 ≤ θ →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
      (let g := regularizedProfile L (blockLabel L N B f K) N B K p;
        t = intervalSecantSlope (fun x => g ((N:ℝ)*x))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2) →
      (let g := regularizedProfile L (blockLabel L N B f K) N B K p;
        ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
            ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
          |intervalSecantError (fun u => g ((N:ℝ)*u))
            (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x| ≤
              θ*(blockProfileCell N B (i,j)).2) →
      profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2) →
      ProfileEndpointBound N B K L f p Q i j s W ((1/(2:ℝ)^(2*n+2))^(-(s+η))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgood⟩ := profileEndpointBound_good hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s t W θ hs hs1 hgap ht hW hθ N B K hN L hL f p Q hQ i j hji hi hlen
    hslope herr hbudget
  let A := θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))
  have hA : 0 ≤ A := mul_nonneg hθ (sub_nonneg.mpr (Nat.cast_le.mpr (blockDepth_antitone N B hji)))
  have ht0 : 0 ≤ t := by linarith only [hκ,hs,hgap]
  obtain ⟨hpoint,hcover⟩ := profile_geometry_costs (B := B) hi (hji.trans hi) ht0 ht hA hW
  have hlo := blockProfileCell_chord_lower (B := B) (i := i) (j := j) (ε := θ)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope.le
    (fun x hx => by simpa only [neg_mul] using (abs_le.mp (herr x hx)).1)
  have hhi := blockProfileCell_chord_upper (B := B) (i := i) (j := j) (ε := θ)
    (regularizedProfile L (blockLabel L N B f K) N B K p) hN hslope.symm.le
    (fun x hx => (abs_le.mp (herr x hx)).2)
  have hprofile := fun k hjk hki => And.intro (hlo k hjk hki) (hhi k hjk hki)
  exact hgood n hn s t W hs hs1 hgap ht hW N B K hN L hL f p Q hQ i j hji hi hlen A hA
    hprofile (hpoint.trans hbudget) (hcover.trans hbudget)
    ((profileGeometryConstant_ge hW hA K B).trans hbudget)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockCellNormalPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The normal cell contributes its baseline exponent, minus three times
its own chord error and the common weak loss. -/
namespace Falconer
open Set Regularization

theorem block_cell_normal_power {N B K : ℕ} (hN : 0 < N)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2) (hQ : Q.side = 1)
    {i j : ℕ} (hji : j ≤ i) (hi : i ≤ K) {s θ W q r : ℝ}
    (hs : 0 ≤ s) (hs1 : s ≤ 1) (hθ : 0 ≤ θ) (hW : 1 ≤ W)
    (hslope : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      s ≤ intervalSecantSlope (fun x => g ((N:ℝ)*x))
        (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2)
    (herr : let g := regularizedProfile L (blockLabel L N B f K) N B K p
      ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
          ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
        -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError (fun u => g ((N:ℝ)*u))
          (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x)
    (hgeometry : profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
      (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))))
    (hpoly : 640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ))) :
    ProfileEndpointBound N B K L f p Q i j s W
      ((2:ℝ)^((s-3*θ)*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))-(3*q+r)*(N:ℝ))) := by
  let d := (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)
  let A := θ*d
  let E := profileGeometryConstant K B W A
  let loss := (3*q+r)*(N:ℝ)+3*A
  have hE0 : 0 < E := by dsimp [E,profileGeometryConstant]; positivity
  have hcost : 640*E^3*((N:ℝ)+3) ≤ (2:ℝ)^loss := by
    calc
      _ ≤ 640*((2:ℝ)^(q*(N:ℝ)+A))^3*((N:ℝ)+3) := by gcongr
      _ ≤ _ := profile_normal_power_cost hpoly
  have hcost0 : 0 < 640*E^3*((N:ℝ)+3) := by positivity
  have hbound := block_cell_normal_gain hN hL f p Q hQ hji hi hs hs1 hθ hW hslope herr
  apply hbound.mono_value
  have hdepth : ((blockDepth N B j-blockDepth N B i+2:ℕ):ℝ) = d+2 := by
    rw [Nat.cast_add,Nat.cast_sub (blockDepth_antitone N B hji)]
    norm_num
    rfl
  calc
    _ ≤ (2:ℝ)^(s*((blockDepth N B j-blockDepth N B i+2:ℕ):ℝ)-loss) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      rw [hdepth]
      dsimp [loss,A,d]
      nlinarith only [hs]
    _ ≤ (1/(2:ℝ)^(blockDepth N B j-blockDepth N B i+2))^(-s)/(640*E^3*((N:ℝ)+3)) :=
      dyadic_power_below_normal_factor _ hcost0 hcost

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_BlockCellPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Normal and good cells have a common additive exponent. The gain is
charged only on cells whose actual secant slope crosses the fixed threshold. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem blockProfileCell_gain_exponent {N B i j : ℕ} (hN : 0 < N)
    (g : ℝ → ℝ) (u s η θ loss : ℝ) :
    profileGainExponent g u s η (3*θ) loss N (blockProfileCell N B (i,j)) =
      (s-3*θ)*( (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))+
        (if u ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1
          (blockProfileCell N B (i,j)).2
          then η*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) else 0)-loss*N := by
  have hn : (N:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold profileGainExponent
  split_ifs
  all_goals dsimp [blockProfileCell]
  all_goals field_simp
  all_goals ring

theorem dyadic_good_power_weaken {N D n : ℕ} {s η θ loss : ℝ}
    (hs : 0 ≤ s) (hη : 0 ≤ η) (hθ : 0 ≤ θ) (hloss : 0 ≤ loss)
    (hD : D = 2*n) :
    (2:ℝ)^((s+η-3*θ)*(D:ℝ)-loss*N) ≤ (1/(2:ℝ)^(2*n+2))^(-(s+η)) := by
  rw [dyadic_inverse_power_eq,neg_neg]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have ht : 0 ≤ 3*θ*(D:ℝ) := by positivity
  have hl : 0 ≤ loss*(N:ℝ) := by positivity
  rw [hD] at ht ⊢
  push_cast
  push_cast at ht
  nlinarith only [ht,hl,hs,hη]

theorem block_cell_power_oai {κ : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100) :
    ∃ ε η : ℝ, ∃ N0 : ℕ, 0 < ε ∧ ε ≤ 1 ∧ 0 < η ∧ 0 < N0 ∧
    ∀ n : ℕ, N0 ≤ n+3 → ∀ s W θ q r : ℝ,
      κ ≤ s → s ≤ 1-8*κ → 1 ≤ W → 0 ≤ θ → 0 ≤ 3*q+r →
    ∀ N B K : ℕ, 0 < N → ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 N →
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
    ∀ i j : ℕ, j ≤ i → i ≤ K → blockDepth N B j-blockDepth N B i = 2*n →
      (let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x);
        s ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ∧
        intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 ≤ 2 ∧
        (∀ x ∈ Icc (blockProfileCell N B (i,j)).1
            ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
          -θ*(blockProfileCell N B (i,j)).2 ≤ intervalSecantError g
            (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 x) ∧
        (s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2 →
          ∀ x ∈ Icc (blockProfileCell N B (i,j)).1
              ((blockProfileCell N B (i,j)).1+(blockProfileCell N B (i,j)).2),
            |intervalSecantError g (blockProfileCell N B (i,j)).1
              (blockProfileCell N B (i,j)).2 x| ≤ θ*(blockProfileCell N B (i,j)).2)) →
      profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) →
      q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ)) ≤ ε*((n+3:ℕ):ℝ) →
      640*((N:ℝ)+3) ≤ (2:ℝ)^(r*(N:ℝ)) →
      ProfileEndpointBound N B K L f p Q i j s W
        ((2:ℝ)^(profileGainExponent
          (fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x))
          (s+2*κ) s η (3*θ) (3*q+r) N (blockProfileCell N B (i,j)))) := by
  obtain ⟨ε,η,N0,hε,hε1,hη,hN0,hgood⟩ := block_cell_good_gain hκ hκ1
  refine ⟨ε,η,N0,hε,hε1,hη,hN0,?_⟩
  intro n hn s W θ q r hs hs1 hW hθ hloss N B K hN L hL f p Q hQ i j hji hi hlen
    hprofile hgeometry hscale hpoly
  obtain ⟨hslope,ht,hlo,hlinear⟩ := hprofile
  let g := fun x => regularizedProfile L (blockLabel L N B f K) N B K p ((N:ℝ)*x)
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hs1' : s ≤ 1 := by linarith
  have hcast : ((blockDepth N B j-blockDepth N B i:ℕ):ℝ) =
      (blockDepth N B j:ℝ)-(blockDepth N B i:ℝ) :=
    Nat.cast_sub (blockDepth_antitone N B hji)
  rw [blockProfileCell_gain_exponent hN]
  by_cases hh : s+2*κ ≤ intervalSecantSlope g (blockProfileCell N B (i,j)).1 (blockProfileCell N B (i,j)).2
  · rw [ite_eq_left hh]
    have hbudget : profileGeometryConstant K B W (θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) ≤
        Real.exp (ε*((n+3:ℕ):ℝ)*Real.log 2) := by
      calc
        _ ≤ (2:ℝ)^(q*(N:ℝ)+θ*((blockDepth N B j:ℝ)-(blockDepth N B i:ℝ))) := hgeometry
        _ ≤ (2:ℝ)^(ε*((n+3:ℕ):ℝ)) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hscale
        _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
    have hb := hgood n hn s (intervalSecantSlope g (blockProfileCell N B (i,j)).1
      (blockProfileCell N B (i,j)).2) W θ hs hs1 (by linarith only [hh]) ht hW hθ
      N B K hN L hL f p Q hQ i j hji hi hlen rfl (hlinear hh) hbudget
    apply hb.mono_value
    convert dyadic_good_power_weaken (N := N) hs0 hη.le hθ hloss hlen using 1
    all_goals try with_reducible_and_instances rfl
    rw [hcast]
    congr 1
    ring
  · rw [ite_eq_right hh,add_zero]
    exact block_cell_normal_power hN hL f p Q hQ hji hi hs0 hs1' hθ hW hslope hlo hgeometry hpoly

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.block_cell_power_oai := @OAI.Falconer.block_cell_power_oai
