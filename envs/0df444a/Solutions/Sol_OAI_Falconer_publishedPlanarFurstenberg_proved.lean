-- Prove2me | solution 1 for OAI.Falconer.publishedPlanarFurstenberg_proved
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-29T22:31:52.662466+00:00
-- url     : https://prove2.me/submissions/16599830-57bf-4d16-83bc-1519bb6ac5e2

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ088F002
import Theorems.Thm_OAI_Falconer_rounded_profile_endpoint_gain

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

theorem extendLabel_card_le {N a b : ℕ} (hab : a ≤ b) (hbN : b ≤ N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (f : CellPath d → List ℕ) :
    (L.image (extendLabel L a b f)).card ≤ (d*(b-a)+1) * (L.image f).card := by
  classical
  let S := (Finset.range (d*(b-a)+1)).product (L.image f)
  have hs : L.image (extendLabel L a b f) ⊆ S.image (fun z => z.1 :: z.2) := by
    intro T hT
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hT
    exact Finset.mem_image.mpr ⟨(Nat.log 2 (labeledChildren L f a b p).card, f p),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr
        (Nat.lt_succ_of_le (child_bin_le hab hbN hL f p)),
        Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,rfl⟩
  calc
    _ ≤ (S.image (fun z => z.1 :: z.2)).card := Finset.card_le_card hs
    _ ≤ S.card := Finset.card_image_le
    _ = _ := by simp [S]

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

theorem blockDepth_terminal (N : ℕ) {B : ℕ} (hB : 0 < B) :
    blockDepth N B (N/B+1) = 0 := by
  have h := Nat.lt_mul_div_succ N hB
  simp only [blockDepth]
  rw [Nat.mul_comm] at h
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


theorem prefixFiber_zero (C : Finset (CellPath d)) : prefixFiber C 0 [] = C := by
  classical
  simp [prefixFiber]

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

theorem blockClass_root_count {N : ℕ} {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N)
    {B : ℕ} (hB : 0 < B) (f : CellPath d → List ℕ) {p : CellPath d} (hp : p ∈ L) :
    let K := N/B+1
    let F := blockLabel L N B f K
    let C := classLeaves L F (F p)
    blockProduct L F N B K p ≤ C.card ∧ C.card ≤ 2^K * blockProduct L F N B K p := by
  classical
  have hpC : p ∈ classLeaves L (blockLabel L N B f (N/B+1)) (blockLabel L N B f (N/B+1) p) := by
    simp [classLeaves,hp]
  have hc := blockClass_leaf_count hL B f (N/B+1) p (le_refl (N/B+1))
    (P := []) (by rw [blockDepth_terminal N hB]; exact Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  simpa only [blockDepth_terminal N hB, prefixFiber_zero] using hc

end Falconer.Regularization

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
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileInterpolation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Profiles with the correct all-dimensional slope

The logarithmic child counts are linearly interpolated. Their exact slope
bound is d/N; after rescaling the depth interval to [0,1] it is d.
-/

namespace Falconer.Regularization
variable {d : ℕ}

theorem intervalRamp_increment {a b u v : ℝ} (hab : a ≤ b) (huv : u ≤ v) :
    0 ≤ intervalRamp a b v - intervalRamp a b u ∧
      intervalRamp a b v - intervalRamp a b u ≤ v-u := by
  unfold intervalRamp
  simp only [min_def]
  split_ifs <;> constructor <;> linarith

theorem intervalRamp_sum (d : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    (∑ i ∈ Finset.range K, intervalRamp (d (i+1)) (d i) u) = min u (d 0)-min u (d K) := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ,ih]; unfold intervalRamp; ring

theorem finiteRampProfile_zero (d c : ℕ → ℝ) (K : ℕ) (hd : ∀ i, 0 ≤ d i) :
    finiteRampProfile d c K 0 = 0 := by
  simp [finiteRampProfile,intervalRamp, min_eq_left (hd _)]

theorem blockSlope_bounds {N : ℕ} (hN : 0 < N) {L : Finset (CellPath d)}
    (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ) (B i : ℕ) (p : CellPath d) :
    0 ≤ blockSlope L F N B i p ∧ blockSlope L F N B i p ≤ (d:ℝ)/(N:ℝ) := by
  have hN' : 0 < (N:ℝ) := by exact_mod_cast hN
  have hd := blockDepth_antitone N B (Nat.le_succ i)
  have hd' : (blockDepth N B (i+1):ℝ) ≤ (blockDepth N B i:ℝ) := by exact_mod_cast hd
  have hb := child_bin_le hd (Nat.sub_le _ _) hL F p
  have hb' : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
      (blockDepth N B i) p).card:ℝ) ≤ (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
    have hbR : (Nat.log 2 (labeledChildren L F (blockDepth N B (i+1))
        (blockDepth N B i) p).card:ℝ) ≤ ((d*(blockDepth N B i-blockDepth N B (i+1)):ℕ):ℝ) := by
      exact_mod_cast hb
    simpa only [Nat.cast_mul,Nat.cast_ofNat,Nat.cast_sub hd] using hbR
  unfold blockSlope
  constructor
  · positivity
  · by_cases he : (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) = 0
    · rw [he,div_zero]; positivity
    · have hp : 0 < (blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ) := lt_of_le_of_ne (sub_nonneg.mpr hd') (Ne.symm he)
      apply (div_le_iff₀ hp).mpr
      apply (div_le_iff₀ hN').mpr
      have heq : (d:ℝ)/(N:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ))*(N:ℝ) =
          (d:ℝ)*((blockDepth N B i:ℝ)-(blockDepth N B (i+1):ℝ)) := by
        field_simp [hN'.ne']
      rw [heq]
      exact hb'

theorem regularizedProfile_zero (L : Finset (CellPath d)) (F : CellPath d → List ℕ)
    (N B K : ℕ) (p : CellPath d) : regularizedProfile L F N B K p 0 = 0 :=
  finiteRampProfile_zero _ _ _ (fun _ => Nat.cast_nonneg _)

end Falconer.Regularization

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

theorem finite_ball_bound_card_lower {δ s K : ℝ} {P : Finset (Space 2)}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hP : P.Nonempty)
    (hball : NormalizedFiniteBallBound δ s K P) :
    1 ≤ K*δ^s*(P.card : ℝ) := by
  obtain ⟨x,hx⟩ := hP
  have hx' : x ∈ P.filter (fun y => dist y x ≤ δ) := by simp [hx,hδ.le]
  have hc : 1 ≤ (P.filter (fun y => dist y x ≤ δ)).card :=
    Finset.one_le_card.mpr ⟨x,hx'⟩
  have hcR : (1 : ℝ) ≤ (P.filter (fun y => dist y x ≤ δ)).card := by exact_mod_cast hc
  exact hcR.trans (hball x δ le_rfl hδ1)

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicPolynomialBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Every fixed polynomial loss in the dyadic depth fits the available
positive exponent. This is used for the finitely many scale-product steps. -/
namespace Falconer

theorem dyadic_polynomial_loss {η C : ℝ} (hη : 0 < η) (hC : 0 ≤ C) (p : ℕ) :
    ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
      C*((N:ℝ)+1)^p ≤ Real.exp (η*(N:ℝ)*Real.log 2) := by
  let a := η*Real.log 2
  have ha : 0 < a := mul_pos hη (Real.log_pos (by norm_num))
  have hfac : 0 < ((p+1).factorial:ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos _)
  obtain ⟨N0,hN0⟩ := exists_nat_gt (max 1
    (C*2^p*((p+1).factorial:ℝ)/a^(p+1)))
  have hN01 : (1:ℝ) ≤ N0 := (le_max_left _ _).trans hN0.le
  refine ⟨N0,by exact_mod_cast (lt_of_lt_of_le zero_lt_one hN01),?_⟩
  intro N hN
  have hNN : (N0:ℝ) ≤ N := Nat.cast_le.mpr hN
  have hN1 : (1:ℝ) ≤ N := hN01.trans hNN
  have hscale : C*2^p*((p+1).factorial:ℝ) ≤ a^(p+1)*(N:ℝ) := by
    have hh := (le_max_right _ _).trans (hN0.le.trans hNN)
    exact (div_le_iff₀ (pow_pos ha _)).mp hh |>.trans_eq (mul_comm _ _)
  have hmult := mul_le_mul_of_nonneg_right hscale (pow_nonneg (Nat.cast_nonneg N) p)
  have hpoly : C*(2*(N:ℝ))^p ≤ (a*(N:ℝ))^(p+1)/((p+1).factorial:ℝ) := by
    apply (le_div_iff₀ hfac).2
    convert hmult using 1 <;> first | (with_reducible_and_instances rfl) | (simp only [mul_pow,pow_succ] <;> ring)
  calc
    _ ≤ C*(2*(N:ℝ))^p := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (by linarith only [hN1]) p) hC
    _ ≤ (a*(N:ℝ))^(p+1)/((p+1).factorial:ℝ) := hpoly
    _ ≤ Real.exp (a*(N:ℝ)) := Real.pow_div_factorial_le_exp (a*(N:ℝ)) (by positivity) (p+1)
    _ = _ := by congr 1; dsimp [a]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSlopeEnergy
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Dyadic slope energies for the quantitative differentiation of the
planar branching profile. Only the Lipschitz constant two is needed. -/
namespace Falconer

theorem intervalSecantSlope_abs_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) : |intervalSecantSlope f a h| ≤ 2 := by
  have hd := hf.dist_le_mul (a+h) a
  rw [Real.dist_eq,Real.dist_eq,add_sub_cancel_left,abs_of_pos hh] at hd
  unfold intervalSecantSlope
  rw [abs_div,abs_of_pos hh]
  exact (div_le_iff₀ hh).2 hd

theorem intervalSecantSlope_children (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantSlope f a (h/2)+intervalSecantSlope f (a+h/2) (h/2) =
      2*intervalSecantSlope f a h := by
  unfold intervalSecantSlope
  rw [show a+h/2+h/2 = a+h by ring]
  field_simp [hh]
  ring

theorem dyadicSlopeEnergy_nonneg (f : ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    0 ≤ dyadicSlopeEnergy f a h n := by
  induction n generalizing a h with
  | zero => exact sq_nonneg _
  | succ n ih => exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicSlopeEnergy_le_four {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) : dyadicSlopeEnergy f a h n ≤ 4 := by
  induction n generalizing a h with
  | zero =>
    have hb := intervalSecantSlope_abs_le hf a hh
    have hsq := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hb
    simpa only [dyadicSlopeEnergy,sq_abs,show (2:ℝ)^2 = 4 by norm_num] using hsq
  | succ n ih =>
    have h₁ := ih a (half_pos hh)
    have h₂ := ih (a+h/2) (half_pos hh)
    change (_+_)/2 ≤ 4
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSlopeVariance
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact variance and selection of a small energy increment for dyadic slopes. -/
namespace Falconer
open scoped BigOperators

theorem dyadicSlopeVariance_nonneg (f : ℝ → ℝ) (a h c : ℝ) (n : ℕ) :
    0 ≤ dyadicSlopeVariance f a h c n := by
  induction n generalizing a h with
  | zero => exact sq_nonneg _
  | succ n ih => exact div_nonneg (add_nonneg (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicSlopeVariance_eq (f : ℝ → ℝ) (a c : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h c n =
      dyadicSlopeEnergy f a h n-2*c*intervalSecantSlope f a h+c^2 := by
  induction n generalizing a h with
  | zero => dsimp [dyadicSlopeVariance,dyadicSlopeEnergy]; ring
  | succ n ih =>
    rw [dyadicSlopeVariance,ih a (half_pos hh),ih (a+h/2) (half_pos hh)]
    have he := intervalSecantSlope_children f a hh.ne'
    change (_+_)/2 = (_+_)/2-2*c*intervalSecantSlope f a h+c^2
    calc
      _ = (dyadicSlopeEnergy f a (h/2) n+dyadicSlopeEnergy f (a+h/2) (h/2) n)/2 -
          c*(intervalSecantSlope f a (h/2)+intervalSecantSlope f (a+h/2) (h/2))+c^2 := by ring
      _ = _ := by rw [he]; ring

theorem dyadicSlopeVariance_centered (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h (intervalSecantSlope f a h) n =
      dyadicSlopeEnergy f a h n-dyadicSlopeEnergy f a h 0 := by
  rw [dyadicSlopeVariance_eq f a _ hh n]
  dsimp [dyadicSlopeEnergy]
  ring

theorem dyadicSlopeEnergy_block_telescoping (f : ℝ → ℝ) (a h : ℝ) (m L : ℕ) :
    (∑ j ∈ Finset.range L, (dyadicSlopeEnergy f a h ((j+1)*m)-dyadicSlopeEnergy f a h (j*m))) =
      dyadicSlopeEnergy f a h (L*m)-dyadicSlopeEnergy f a h 0 := by
  induction L with
  | zero => simp
  | succ L ih => rw [Finset.sum_range_succ,ih]; ring

theorem exists_small_dyadic_energy_increment {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (m L : ℕ) (hL : 0 < L) :
    ∃ j < L, dyadicSlopeEnergy f a h ((j+1)*m)-dyadicSlopeEnergy f a h (j*m) ≤ 4/(L : ℝ) := by
  by_contra he
  push Not at he
  have hs := Finset.sum_lt_sum_of_nonempty
    (show (Finset.range L).Nonempty from ⟨0,Finset.mem_range.mpr hL⟩)
    (fun j hj => he j (Finset.mem_range.mp hj))
  rw [dyadicSlopeEnergy_block_telescoping] at hs
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  have heq : (∑ _j ∈ Finset.range L, (4/(L : ℝ))) = 4 := by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    exact mul_div_cancel₀ 4 hLR.ne'
  rw [heq] at hs
  linarith [dyadicSlopeEnergy_le_four hf a hh (L*m),dyadicSlopeEnergy_nonneg f a h 0]

theorem dyadicSlopeVariance_recenter (f : ℝ → ℝ) (a c : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    dyadicSlopeVariance f a h c n =
      dyadicSlopeVariance f a h (intervalSecantSlope f a h) n+(intervalSecantSlope f a h-c)^2 := by
  rw [dyadicSlopeVariance_eq f a c hh n,dyadicSlopeVariance_eq f a _ hh n]
  ring

theorem dyadicSlopeVariance_child_le (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (dyadicSlopeVariance f a (h/2) (intervalSecantSlope f a (h/2)) n+
      (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h)^2)/2 ≤
        dyadicSlopeVariance f a h (intervalSecantSlope f a h) (n+1) ∧
    (dyadicSlopeVariance f (a+h/2) (h/2) (intervalSecantSlope f (a+h/2) (h/2)) n+
      (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)^2)/2 ≤
        dyadicSlopeVariance f a h (intervalSecantSlope f a h) (n+1) := by
  rw [dyadicSlopeVariance]
  have hl := dyadicSlopeVariance_recenter f a (intervalSecantSlope f a h) (half_pos hh) n
  have hr := dyadicSlopeVariance_recenter f (a+h/2) (intervalSecantSlope f a h) (half_pos hh) n
  rw [hl,hr]
  constructor <;> nlinarith [dyadicSlopeVariance_nonneg f a (h/2) (intervalSecantSlope f a (h/2)) n,
    dyadicSlopeVariance_nonneg f (a+h/2) (h/2) (intervalSecantSlope f (a+h/2) (h/2)) n,
    sq_nonneg (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h),
    sq_nonneg (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicSecantError
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Pointwise straight-line error on the dyadic vertices is controlled by
the centered slope energy, without any differentiability assumption. -/
namespace Falconer
open Set

theorem dyadicEndpoints_bounds (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {x : ℝ} (hx : x ∈ dyadicEndpoints a h n) : a ≤ x ∧ x ≤ a+h := by
  induction n generalizing a h with
  | zero =>
    simp only [dyadicEndpoints,mem_insert_iff,mem_singleton_iff] at hx
    rcases hx with rfl | rfl <;> constructor <;> linarith
  | succ n ih =>
    rcases hx with hx | hx
    · have hb := ih a (div_nonneg hh (by norm_num)) hx
      constructor <;> linarith
    · have hb := ih (a+h/2) (div_nonneg hh (by norm_num)) hx
      constructor <;> linarith

theorem intervalSecantError_left (f : ℝ → ℝ) (a h x : ℝ) :
    intervalSecantError f a h x = intervalSecantError f a (h/2) x+
      (intervalSecantSlope f a (h/2)-intervalSecantSlope f a h)*(x-a) := by
  unfold intervalSecantError
  ring

theorem intervalSecantError_right (f : ℝ → ℝ) (a x : ℝ) {h : ℝ} (hh : h ≠ 0) :
    intervalSecantError f a h x = intervalSecantError f (a+h/2) (h/2) x+
      (intervalSecantSlope f (a+h/2) (h/2)-intervalSecantSlope f a h)*(x-a-h) := by
  unfold intervalSecantError intervalSecantSlope
  rw [show a+h/2+h/2 = a+h by ring]
  field_simp [hh]
  ring

private theorem secant_error_algebra {e d t h v V : ℝ}
    (he : e^2 ≤ (h/2)^2*v) (ht : t^2 ≤ (h/2)^2)
    (hv : (v+d^2)/2 ≤ V) : (e+d*t)^2 ≤ h^2*V := by
  have hd := mul_le_mul_of_nonneg_left ht (sq_nonneg d)
  have hV := mul_le_mul_of_nonneg_left hv (sq_nonneg h)
  nlinarith [sq_nonneg (e-d*t)]

theorem dyadic_secant_error_sq_le (f : ℝ → ℝ) (a : ℝ) {h : ℝ} (hh : 0 < h)
    (n : ℕ) {x : ℝ} (hx : x ∈ dyadicEndpoints a h n) :
    (intervalSecantError f a h x)^2 ≤
      h^2*dyadicSlopeVariance f a h (intervalSecantSlope f a h) n := by
  induction n generalizing a h with
  | zero =>
    have he : intervalSecantError f a h x = 0 := by
      simp only [dyadicEndpoints,mem_insert_iff,mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · simp [intervalSecantError]
      · unfold intervalSecantError intervalSecantSlope
        field_simp [hh.ne']
        ring
    rw [he]
    simpa only [zero_pow (by decide : 2 ≠ 0)] using
      mul_nonneg (sq_nonneg h) (dyadicSlopeVariance_nonneg f a h (intervalSecantSlope f a h) 0)
  | succ n ih =>
    have hvar := dyadicSlopeVariance_child_le f a hh n
    rcases hx with hx | hx
    · have he := ih a (half_pos hh) hx
      have hb := dyadicEndpoints_bounds a (div_nonneg hh.le (by norm_num)) n hx
      rw [intervalSecantError_left]
      apply secant_error_algebra he ?_ hvar.1
      nlinarith [sq_nonneg (x-a)]
    · have he := ih (a+h/2) (half_pos hh) hx
      have hb := dyadicEndpoints_bounds (a+h/2) (div_nonneg hh.le (by norm_num)) n hx
      rw [intervalSecantError_right f a x hh.ne']
      apply secant_error_algebra he ?_ hvar.2
      nlinarith [sq_nonneg (x-a-h)]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicLinearApproximation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite energy bound gives uniform linear approximation on the whole interval. -/
namespace Falconer
open Set

theorem exists_dyadic_endpoint_near (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {x : ℝ} (hx : x ∈ Icc a (a+h)) :
    ∃ y ∈ dyadicEndpoints a h n, |x-y| ≤ h/(2 : ℝ)^n := by
  induction n generalizing a h with
  | zero =>
    refine ⟨a,by simp [dyadicEndpoints],?_⟩
    rw [pow_zero,div_one,abs_of_nonneg (sub_nonneg.mpr hx.1)]
    linarith [hx.2]
  | succ n ih =>
    by_cases hm : x ≤ a+h/2
    · obtain ⟨y,hy,hxy⟩ := ih a (h := h/2) (div_nonneg hh (by norm_num)) ⟨hx.1,hm⟩
      refine ⟨y,Or.inl hy,hxy.trans_eq ?_⟩
      simp only [div_div,pow_succ,mul_comm]
    · obtain ⟨y,hy,hxy⟩ := ih (a+h/2) (h := h/2) (div_nonneg hh (by norm_num))
        ⟨le_of_not_ge hm,by linarith [hx.2]⟩
      refine ⟨y,Or.inr hy,hxy.trans_eq ?_⟩
      simp only [div_div,pow_succ,mul_comm]

theorem intervalSecantError_abs_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h : ℝ} (hh : 0 < h) (x y : ℝ) :
    |intervalSecantError f a h x-intervalSecantError f a h y| ≤ 4*|x-y| := by
  have hfxy : |f x-f y| ≤ 2*|x-y| := by
    simpa only [Real.dist_eq,NNReal.coe_ofNat] using hf.dist_le_mul x y
  have hs := intervalSecantSlope_abs_le hf a hh
  have he : intervalSecantError f a h x-intervalSecantError f a h y =
      (f x-f y)-intervalSecantSlope f a h*(x-y) := by
    unfold intervalSecantError
    ring
  rw [he]
  calc
    _ ≤ |f x-f y|+|intervalSecantSlope f a h*(x-y)| := by
      simpa only [sub_eq_add_neg,abs_neg] using
        abs_add_le (f x-f y) (-(intervalSecantSlope f a h*(x-y)))
    _ ≤ 2*|x-y|+2*|x-y| := add_le_add hfxy (by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hs (abs_nonneg _))
    _ = _ := by ring

theorem dyadic_linear_approximation {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 ≤ η) (n : ℕ)
    (hv : dyadicSlopeVariance f a h (intervalSecantSlope f a h) n ≤ η^2)
    {x : ℝ} (hx : x ∈ Icc a (a+h)) :
    |intervalSecantError f a h x| ≤ h*η+4*h/(2 : ℝ)^n := by
  obtain ⟨y,hy,hxy⟩ := exists_dyadic_endpoint_near a hh.le n hx
  have hs := dyadic_secant_error_sq_le f a hh n hy
  have hb := mul_le_mul_of_nonneg_left hv (sq_nonneg h)
  have hyerr : |intervalSecantError f a h y| ≤ h*η := by
    have hn := mul_nonneg hh.le hη
    nlinarith [sq_abs (intervalSecantError f a h y)]
  calc
    _ = |intervalSecantError f a h y+
        (intervalSecantError f a h x-intervalSecantError f a h y)| := by congr 1; ring
    _ ≤ |intervalSecantError f a h y|+
        |intervalSecantError f a h x-intervalSecantError f a h y| := abs_add_le _ _
    _ ≤ h*η+4*|x-y| := add_le_add hyerr (intervalSecantError_abs_sub_le hf a hh x y)
    _ ≤ h*η+4*(h/(2 : ℝ)^n) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hxy (by norm_num : (0 : ℝ) ≤ 4))
    _ = _ := by ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_OrderedProfileIntervals
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Length and endpoint accounting for ordered profile intervals. -/
namespace Falconer
open Set

 theorem ordered_interval_length_le {S : List (ℝ × ℝ)} {a b : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    (S.map Prod.snd).sum ≤ b-a := by
  induction S generalizing a with
  | nil => simpa using sub_nonneg.mpr hab
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have hs := ih (a := c.1+c.2) hc.2.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,(hb d (by simp [hd])).2⟩)
    simp only [List.map_cons,List.sum_cons]
    linarith

 theorem ordered_interval_count_bound {S : List (ℝ × ℝ)} {a b τ : ℝ} (hab : a ≤ b)
    (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ b ∧ 0 ≤ c.2)
    (hτ : ∀ c ∈ S, τ ≤ c.2) :
    τ*(S.length : ℝ) ≤ b-a := by
  have hsum : τ*(S.length : ℝ) ≤ (S.map Prod.snd).sum := by
    induction S with
    | nil => simp
    | cons c S ih =>
      have ht : ∀ d ∈ S, τ ≤ d.2 := fun d hd => hτ d (by simp [hd])
      have hi := ih (by simpa using hord.of_cons) (fun d hd => hb d (by simp [hd])) ht
      simp only [List.length_cons,Nat.cast_add,Nat.cast_one,List.map_cons,List.sum_cons]
      linarith [hτ c (by simp)]
  exact hsum.trans (ordered_interval_length_le hab hord hb)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfilePrefix
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prefix clipping for the finite low-slope merge algorithm. At most one
original interval is shortened; an undersized residual costs one minimum length. -/
namespace Falconer

theorem clipProfilePrefix_spec {u r : ℝ} {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, r ≤ c.2) {d : ℝ × ℝ} (hd : d ∈ clipProfilePrefix u r S) :
    ∃ c ∈ S, d.1 = c.1 ∧ r ≤ d.2 ∧ d.2 ≤ c.2 ∧ d.1+d.2 ≤ u := by
  induction S with
  | nil => simp [clipProfilePrefix] at hd
  | cons c S ih =>
    simp only [clipProfilePrefix] at hd
    split_ifs at hd with hend hsize
    · rcases List.mem_cons.mp hd with he | hd
      · subst d
        exact ⟨c,by simp,rfl,hmin c (by simp),le_rfl,hend⟩
      · obtain ⟨v,hv,h1,h2,h3,h4⟩ := ih (fun v hv => hmin v (by simp [hv])) hd
        exact ⟨v,by simp [hv],h1,h2,h3,h4⟩
    · have he : d = (c.1,u-c.1) := by simpa only [List.mem_singleton] using hd
      subst d
      refine ⟨c,by simp,rfl,hsize,?_,?_⟩ <;> dsimp <;> linarith
    · simp at hd

theorem clipProfilePrefix_ordered {u r H : ℝ} {S : List (ℝ × ℝ)}
    (hord : S.Pairwise (fun c d => c.1+H ≤ d.1)) (hmin : ∀ c ∈ S, r ≤ c.2) :
    (clipProfilePrefix u r S).Pairwise (fun c d => c.1+H ≤ d.1) := by
  induction S with
  | nil => simp [clipProfilePrefix]
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    simp only [clipProfilePrefix]
    split_ifs
    · rw [List.pairwise_cons]
      refine ⟨?_,ih hord.2 (fun d hd => hmin d (by simp [hd]))⟩
      intro d hd
      obtain ⟨v,hv,he,_⟩ := clipProfilePrefix_spec (fun v hv => hmin v (by simp [hv])) hd
      simpa only [he] using hord.1 v hv
    · simp
    · simp

theorem clipProfilePrefix_loss {u r b : ℝ} (hr : 0 ≤ r) (hub : u ≤ b)
    {S : List (ℝ × ℝ)} (hord : S.Pairwise (fun c d => c.1+c.2 ≤ d.1))
    (hb : ∀ c ∈ S, c.1+c.2 ≤ b ∧ 0 ≤ c.2) :
    (S.map Prod.snd).sum ≤ (clipProfilePrefix u r S |>.map Prod.snd).sum+(b-u)+r := by
  induction S with
  | nil => simp only [clipProfilePrefix,List.map_nil,List.sum_nil]; linarith
  | cons c S ih =>
    rw [List.pairwise_cons] at hord
    have hc := hb c (by simp)
    have ht := ordered_interval_length_le hc.1 hord.2 (by
      intro d hd
      exact ⟨hord.1 d hd,hb d (by simp [hd])⟩)
    simp only [clipProfilePrefix]
    split_ifs with hend hsize
    · have hi := ih hord.2 (fun d hd => hb d (by simp [hd]))
      simp only [List.map_cons,List.sum_cons]
      linarith
    · simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero]
      linarith
    · simp only [List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,zero_add]
      linarith

theorem clipProfilePrefix_length_lt {u r : ℝ} (hr : 0 < r) {S : List (ℝ × ℝ)}
    (hmin : ∀ c ∈ S, r ≤ c.2) (hex : ∃ c ∈ S, u ≤ c.1) :
    (clipProfilePrefix u r S).length < S.length := by
  induction S with
  | nil => simp at hex
  | cons c S ih =>
    simp only [clipProfilePrefix]
    split_ifs with hend hsize
    · have hex' : ∃ d ∈ S, u ≤ d.1 := by
        obtain ⟨d,hd,hu⟩ := hex
        rcases List.mem_cons.mp hd with he | hd
        · subst d
          have hm := hmin c (by simp)
          linarith
        · exact ⟨d,hd,hu⟩
      simpa only [List.length_cons] using
        Nat.succ_lt_succ (ih (fun d hd => hmin d (by simp [hd])) hex')
    · cases S with
      | nil =>
        obtain ⟨d,hd,hu⟩ := hex
        have he : d = c := by simpa only [List.mem_singleton] using hd
        subst d
        linarith
      | cons d S => simp
    · simp

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileRestriction
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative stability when a linear profile interval is shortened on the right. -/
namespace Falconer
open Set

theorem intervalSecantError_restrict_left (f : ℝ → ℝ) (a h x : ℝ)
    {k : ℝ} (hk : k ≠ 0) :
    intervalSecantError f a k x = intervalSecantError f a h x-
      intervalSecantError f a h (a+k)*((x-a)/k) := by
  unfold intervalSecantError
  unfold intervalSecantSlope
  field_simp [hk]
  ring

theorem linear_interval_restrict_left {f : ℝ → ℝ} {a h k ε : ℝ}
    (hk : 0 < k) (hkh : k ≤ h) (hε : 0 ≤ ε)
    (herr : ∀ x ∈ Icc a (a+h), |intervalSecantError f a h x| ≤ ε*h)
    {x : ℝ} (hx : x ∈ Icc a (a+k)) :
    |intervalSecantError f a k x| ≤ 2*ε*h := by
  have hr0 : 0 ≤ (x-a)/k := div_nonneg (sub_nonneg.mpr hx.1) hk.le
  have hr1 : (x-a)/k ≤ 1 := (div_le_iff₀ hk).2 (by linarith [hx.2])
  have hv := herr (a+k) ⟨by linarith,by linarith⟩
  have hx' := herr x ⟨hx.1,by linarith [hx.2]⟩
  rw [intervalSecantError_restrict_left f a h x hk.ne']
  calc
    _ ≤ |intervalSecantError f a h x|+
        |intervalSecantError f a h (a+k)*((x-a)/k)| := by
      simpa only [sub_eq_add_neg,abs_neg] using abs_add_le
        (intervalSecantError f a h x) (-(intervalSecantError f a h (a+k)*((x-a)/k)))
    _ = |intervalSecantError f a h x|+
        |intervalSecantError f a h (a+k)| *((x-a)/k) := by
      rw [abs_mul,abs_of_nonneg hr0]
    _ ≤ ε*h+ε*h := add_le_add hx' ((mul_le_mul_of_nonneg_right hv hr0).trans
      (mul_le_of_le_one_right (mul_nonneg hε (hk.le.trans hkh)) hr1))
    _ = _ := by ring

theorem linear_interval_restrict_proportion {f : ℝ → ℝ} {a h k η : ℝ}
    (hk : 0 < k) (hkh : k ≤ h) (hη : 0 < η) (hsize : η*h ≤ k)
    (herr : ∀ x ∈ Icc a (a+h), |intervalSecantError f a h x| ≤ η^2*h)
    {x : ℝ} (hx : x ∈ Icc a (a+k)) :
    |intervalSecantError f a k x| ≤ 2*η*k := by
  have he := linear_interval_restrict_left hk hkh (sq_nonneg η) herr hx
  have hb := mul_le_mul_of_nonneg_left hsize (show 0 ≤ 2*η by positivity)
  nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileCellFamily
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Invariants for the finite profile-merging recursion. The original equal
width cells are retained as witnesses when their active prefixes are shortened. -/
namespace Falconer
open Set

theorem ProfileCellFamily.actual_ordered {f : ℝ → ℝ} {H r η m b : ℝ}
    {S : List (ℝ × ℝ)} (hF : ProfileCellFamily f H r η m b S) :
    S.Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  apply hF.ordered.imp_of_mem
  intro c d hc _ hcd
  exact (add_le_add le_rfl (hF.bounds c hc).2.2.2.1).trans hcd

theorem ProfileCellFamily.clip {f : ℝ → ℝ} {H r η m b u : ℝ}
    {S : List (ℝ × ℝ)} (hF : ProfileCellFamily f H r η m b S) :
    ProfileCellFamily f H r η m u (clipProfilePrefix u r S) := by
  refine ⟨clipProfilePrefix_ordered hF.ordered (fun c hc => (hF.bounds c hc).2.2.1),?_,?_⟩
  · intro d hd
    obtain ⟨c,hc,he,hmin,hsize,hend⟩ := clipProfilePrefix_spec
      (fun c hc => (hF.bounds c hc).2.2.1) hd
    have hb := hF.bounds c hc
    exact ⟨by simpa only [he] using hb.1,by simpa only [he] using hb.2.1,
      hmin,hsize.trans hb.2.2.2.1,hend⟩
  · intro d hd x hx
    obtain ⟨c,hc,he,_⟩ := clipProfilePrefix_spec (fun c hc => (hF.bounds c hc).2.2.1) hd
    simpa only [he] using hF.linear c hc x (by simpa only [he] using hx)

theorem ProfileCellFamily.active_linear {f : ℝ → ℝ} {H η m b : ℝ}
    {S : List (ℝ × ℝ)} (hη : 0 < η) (hH : 0 < H)
    (hF : ProfileCellFamily f H (η*H) η m b S) {c : ℝ × ℝ} (hc : c ∈ S) :
    ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ (2*η)*c.2 := by
  have hb := hF.bounds c hc
  have hcpos : 0 < c.2 := lt_of_lt_of_le (mul_pos hη hH) hb.2.2.1
  exact fun x hx => linear_interval_restrict_proportion hcpos hb.2.2.2.1 hη hb.2.2.1
    (hF.linear c hc) hx

theorem StructuredProfilePieces.nil (f : ℝ → ℝ) (r θ s b : ℝ) :
    StructuredProfilePieces f r θ s b [] := by
  constructor <;> simp

theorem StructuredProfilePieces.append_interval {f : ℝ → ℝ} {r θ s a b : ℝ}
    {S : List (ℝ × ℝ)} (hS : StructuredProfilePieces f r θ s a S) (c : ℝ × ℝ)
    (hc0 : a ≤ c.1) (hcb : c.1+c.2 ≤ b) (hcr : r ≤ c.2) (hca : 0 ≤ c.1)
    (halt : (s ≤ intervalSecantSlope f c.1 c.2 ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ θ*c.2) ∨
    (intervalSecantSlope f c.1 c.2 = s ∧
      ∀ x ∈ Icc c.1 (c.1+c.2), -θ*c.2 ≤ intervalSecantError f c.1 c.2 x))
    (hcpos : 0 ≤ c.2) : StructuredProfilePieces f r θ s b (S++[c]) := by
  constructor
  · rw [List.pairwise_append]
    refine ⟨hS.ordered,by simp,?_⟩
    intro d hd e he
    have hec : e = c := by simpa only [List.mem_singleton] using he
    subst e
    exact (hS.bounds d hd).2.1.trans hc0
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · have hb := hS.bounds d hd
      exact ⟨hb.1,hb.2.1.trans (by linarith),hb.2.2⟩
    · have he : d = c := by simpa only [List.mem_singleton] using hd
      subst d
      exact ⟨hca,hcb,hcr⟩
  · intro d hd
    rcases List.mem_append.mp hd with hd | hd
    · exact hS.alternatives d hd
    · have he : d = c := by simpa only [List.mem_singleton] using hd
      subst d
      exact halt

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicAveraging
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite dyadic averaging and the energy increment identity. -/
namespace Falconer

theorem dyadicAverage_mono {g k : ℝ → ℝ → ℝ} (hg : ∀ a h, g a h ≤ k a h)
    (a h : ℝ) (n : ℕ) : dyadicAverage g a h n ≤ dyadicAverage k a h n := by
  induction n generalizing a h with
  | zero => exact hg a h
  | succ n ih => exact div_le_div_of_nonneg_right (add_le_add (ih _ _) (ih _ _)) (by norm_num)

theorem dyadicAverage_add (g k : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicAverage (fun a h => g a h+k a h) a h n =
      dyadicAverage g a h n+dyadicAverage k a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_mul (c : ℝ) (g : ℝ → ℝ → ℝ) (a h : ℝ) (n : ℕ) :
    dyadicAverage (fun a h => c*g a h) a h n = c*dyadicAverage g a h n := by
  induction n generalizing a h with
  | zero => rfl
  | succ n ih => simp only [dyadicAverage,ih]; ring

theorem dyadicAverage_centered_variance (f : ℝ → ℝ) (a : ℝ) {h : ℝ}
    (hh : 0 < h) (n m : ℕ) :
    dyadicAverage (fun a h => dyadicSlopeVariance f a h (intervalSecantSlope f a h) m) a h n =
      dyadicSlopeEnergy f a h (n+m)-dyadicSlopeEnergy f a h n := by
  induction n generalizing a h with
  | zero => simpa only [dyadicAverage,Nat.zero_add] using dyadicSlopeVariance_centered f a hh m
  | succ n ih =>
    rw [dyadicAverage,ih a (half_pos hh),ih (a+h/2) (half_pos hh),Nat.succ_add]
    simp only [dyadicSlopeEnergy]
    ring

theorem dyadicAverage_markov {g : ℝ → ℝ → ℝ} (hg : ∀ a h, 0 ≤ g a h)
    (a h θ : ℝ) (n : ℕ) :
    θ*dyadicAverage (fun a h => if θ < g a h then 1 else 0) a h n ≤
      dyadicAverage g a h n := by
  classical
  rw [← dyadicAverage_mul]
  apply dyadicAverage_mono
  intro a h
  split_ifs with ht
  · simpa only [mul_one] using ht.le
  · simpa only [mul_zero] using hg a h

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_DyadicCells
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit ordered dyadic interval partition and its weighted averages. -/
namespace Falconer
open Set

theorem dyadicCells_bounds (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ)
    {u l : ℝ} (hu : (u,l) ∈ dyadicCells a h n) :
    a ≤ u ∧ u+l ≤ a+h ∧ l = h/(2 : ℝ)^n := by
  induction n generalizing a h with
  | zero =>
    simp only [dyadicCells,List.mem_singleton,Prod.mk.injEq] at hu
    rcases hu with ⟨rfl,rfl⟩
    simp
  | succ n ih =>
    rw [dyadicCells,List.mem_append] at hu
    rcases hu with hu | hu
    · obtain ⟨hlo,hhi,he⟩ := ih a (h := h/2) (by positivity) hu
      refine ⟨hlo,by linarith,he.trans ?_⟩
      simp only [div_div,pow_succ,mul_comm]
    · obtain ⟨hlo,hhi,he⟩ := ih (a+h/2) (h := h/2) (by positivity) hu
      refine ⟨by linarith,by linarith,he.trans ?_⟩
      simp only [div_div,pow_succ,mul_comm]

theorem dyadicCells_ordered (a : ℝ) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (dyadicCells a h n).Pairwise (fun c d => c.1+c.2 ≤ d.1) := by
  induction n generalizing a h with
  | zero => simp [dyadicCells]
  | succ n ih =>
    rw [dyadicCells,List.pairwise_append]
    refine ⟨ih a (by positivity),ih (a+h/2) (by positivity),?_⟩
    intro c hc d hd
    have hl := dyadicCells_bounds a (h := h/2) (by positivity) n hc
    have hr := dyadicCells_bounds (a+h/2) (h := h/2) (by positivity) n hd
    exact hl.2.1.trans hr.1

theorem dyadicCells_selected_length (P : ℝ → ℝ → Prop) [DecidableRel P]
    (a h : ℝ) (n : ℕ) :
    (((dyadicCells a h n).filter (fun c => P c.1 c.2)).map Prod.snd).sum =
      h*dyadicAverage (fun a h => if P a h then 1 else 0) a h n := by
  induction n generalizing a h with
  | zero => by_cases hp : P a h <;> simp [dyadicCells,dyadicAverage,hp]
  | succ n ih =>
    simp only [dyadicCells,List.filter_append,List.map_append,List.sum_append,ih,dyadicAverage]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LinearPieces
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Selection of a bounded-scale family of intervals with uniform linear error. -/
namespace Falconer
open Set

theorem exists_dyadic_linear_pieces {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    (a : ℝ) {h η : ℝ} (hh : 0 < h) (hη : 0 < η) (m L : ℕ) (hL : 0 < L) :
    ∃ n ≤ L*m,
      (dyadicLinearPieces f a h η n m).Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
      h*(1-4/((L : ℝ)*η^2)) ≤ ((dyadicLinearPieces f a h η n m).map Prod.snd).sum ∧
      ∀ c ∈ dyadicLinearPieces f a h η n m,
        a ≤ c.1 ∧ c.1+c.2 ≤ a+h ∧ c.2 = h/(2 : ℝ)^n ∧
        ∀ x ∈ Icc c.1 (c.1+c.2),
          |intervalSecantError f c.1 c.2 x| ≤ c.2*(η+4/(2 : ℝ)^m) := by
  classical
  obtain ⟨j,hj,hinc⟩ := exists_small_dyadic_energy_increment hf a hh m L hL
  let V : ℝ → ℝ → ℝ := fun u l =>
    dyadicSlopeVariance f u l (intervalSecantSlope f u l) m
  let G := dyadicAverage (fun u l => if V u l ≤ η^2 then 1 else 0) a h (j*m)
  let B := dyadicAverage (fun u l => if η^2 < V u l then 1 else 0) a h (j*m)
  have hM : η^2*B ≤ dyadicAverage V a h (j*m) :=
    dyadicAverage_markov (fun u l => dyadicSlopeVariance_nonneg f u l _ m) a h (η^2) (j*m)
  have hE : dyadicAverage V a h (j*m) ≤ 4/(L : ℝ) := by
    dsimp [V]
    rw [dyadicAverage_centered_variance f a hh]
    simpa only [Nat.add_mul,Nat.one_mul] using hinc
  have hB : B ≤ 4/((L : ℝ)*η^2) := by
    rw [← div_div]
    apply (le_div_iff₀ (sq_pos_of_pos hη)).2
    nlinarith [hM.trans hE]
  have hGB : G+B = 1 := by
    dsimp [G,B]
    rw [← dyadicAverage_add]
    have he : (fun u l => (if V u l ≤ η^2 then (1 : ℝ) else 0)+
        (if η^2 < V u l then 1 else 0)) = fun _ _ => (1 : ℝ) := by
      funext u l
      by_cases hv : V u l ≤ η^2
      · simp [hv,not_lt.mpr hv]
      · simp [hv,lt_of_not_ge hv]
    rw [he,dyadicAverage_const]
  have hG : 1-4/((L : ℝ)*η^2) ≤ G := by linarith
  refine ⟨j*m,Nat.mul_le_mul_right m hj.le,?_,?_,?_⟩
  · exact (dyadicCells_ordered a hh.le (j*m)).filter _
  · rw [dyadicLinearPieces,dyadicCells_selected_length (fun u l => V u l ≤ η^2)]
    exact mul_le_mul_of_nonneg_left hG hh.le
  · intro c hc
    obtain ⟨hc,hv⟩ := List.mem_filter.mp hc
    have hb := dyadicCells_bounds a hh.le (j*m) hc
    refine ⟨hb.1,hb.2.1,hb.2.2,?_⟩
    intro x hx
    have hcpos : 0 < c.2 := by rw [hb.2.2]; positivity
    have he := dyadic_linear_approximation hf c.1 hcpos hη.le m (of_decide_eq_true hv) hx
    convert he using 1 <;> first | rfl | ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_QuantitativeDifferentiation
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative differentiation for the 2-Lipschitz profiles used in planar
Furstenberg regularization: the lower scale depends only on the error. -/
namespace Falconer
open Set

theorem quantitative_uniform_linear_decomposition {ε : ℝ} (hε : 0 < ε) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (f : ℝ → ℝ), LipschitzWith 2 f →
      ∀ (a : ℝ) (h : ℝ), 0 < h → ∃ S : List (ℝ × ℝ),
        (∃ H : ℝ, 0 < H ∧ H ≤ h ∧ τ*h ≤ H ∧ ∀ c ∈ S, c.2 = H) ∧
        S.Pairwise (fun c d => c.1+c.2 ≤ d.1) ∧
        h*(1-ε) ≤ (S.map Prod.snd).sum ∧
        ∀ c ∈ S, a ≤ c.1 ∧ c.1+c.2 ≤ a+h ∧ τ*h ≤ c.2 ∧
          ∀ x ∈ Icc c.1 (c.1+c.2), |intervalSecantError f c.1 c.2 x| ≤ ε*c.2 := by
  obtain ⟨m,hm⟩ := exists_pow_lt_of_lt_one (show 0 < ε/8 by positivity)
    (show (1/2 : ℝ) < 1 by norm_num)
  simp only [div_pow,one_pow] at hm
  have hm' : 4/(2 : ℝ)^m ≤ ε/2 := by
    calc
      _ = 4*(1/(2 : ℝ)^m) := by ring
      _ ≤ 4*(ε/8) := mul_le_mul_of_nonneg_left hm.le (by norm_num)
      _ = _ := by ring
  obtain ⟨L,hL⟩ := exists_nat_gt (4/(ε*(ε/2)^2))
  have hLR : (0 : ℝ) < L := lt_trans (by positivity : 0 < 4/(ε*(ε/2)^2)) hL
  have hLN : 0 < L := by exact_mod_cast hLR
  have hloss : 4/((L : ℝ)*(ε/2)^2) ≤ ε := by
    apply (div_le_iff₀ (by positivity : 0 < (L : ℝ)*(ε/2)^2)).2
    have he := (div_lt_iff₀ (by positivity : 0 < ε*(ε/2)^2)).mp hL
    nlinarith
  refine ⟨1/(2 : ℝ)^(L*m),by positivity,?_⟩
  intro f hf a h hh
  obtain ⟨n,hn,hord,hlen,hcells⟩ := exists_dyadic_linear_pieces hf a hh
    (show 0 < ε/2 by positivity) m L hLN
  refine ⟨dyadicLinearPieces f a h (ε/2) n m,?_,hord,?_,?_⟩
  · refine ⟨h/(2 : ℝ)^n,by positivity,div_le_self hh.le (one_le_pow₀ (by norm_num)),?_,?_⟩
    · have hpow : (2 : ℝ)^n ≤ 2^(L*m) := pow_le_pow_right₀ (by norm_num) hn
      have hw := div_le_div_of_nonneg_left hh.le (by positivity : 0 < (2 : ℝ)^n) hpow
      simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hw
    · exact fun c hc => (hcells c hc).2.2.1
  · exact (mul_le_mul_of_nonneg_left (by linarith : 1-ε ≤ 1-4/((L : ℝ)*(ε/2)^2)) hh.le).trans hlen
  · intro c hc
    obtain ⟨hlo,hhi,he,herr⟩ := hcells c hc
    have hpow : (2 : ℝ)^n ≤ 2^(L*m) := pow_le_pow_right₀ (by norm_num) hn
    have hwidth : h/(2 : ℝ)^(L*m) ≤ c.2 := by
      rw [he]
      exact div_le_div_of_nonneg_left hh.le (by positivity) hpow
    refine ⟨hlo,hhi,?_,?_⟩
    · simpa only [one_div,mul_comm,mul_inv_rev,div_eq_mul_inv,one_mul] using hwidth
    · intro x hx
      have hcpos : 0 ≤ c.2 := by rw [he]; positivity
      have hcoef : ε/2+4/(2 : ℝ)^m ≤ ε := by linarith
      exact (herr x hx).trans (by nlinarith [mul_le_mul_of_nonneg_left hcoef hcpos])

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileLipschitz
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual regularized branching profile has the global Lipschitz bound
required by quantitative differentiation, including its constant tails. -/
namespace Falconer.Regularization

theorem finiteRampProfile_increment_all (d c : ℕ → ℝ) (K : ℕ) {C u v : ℝ}
    (hd : Antitone d) (hC : 0 ≤ C) (hc : ∀ i < K, 0 ≤ c i ∧ c i ≤ C)
    (huv : u ≤ v) :
    0 ≤ finiteRampProfile d c K v-finiteRampProfile d c K u ∧
      finiteRampProfile d c K v-finiteRampProfile d c K u ≤ C*(v-u) := by
  have he : finiteRampProfile d c K v-finiteRampProfile d c K u =
      ∑ i ∈ Finset.range K, c i*(intervalRamp (d (i+1)) (d i) v-
        intervalRamp (d (i+1)) (d i) u) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  have hr (i : ℕ) := intervalRamp_increment (hd (Nat.le_succ i)) huv
  rw [he]
  constructor
  · exact Finset.sum_nonneg fun i hi =>
      mul_nonneg (hc i (Finset.mem_range.mp hi)).1 (hr i).1
  · calc
      _ ≤ ∑ i ∈ Finset.range K, C*(intervalRamp (d (i+1)) (d i) v-
          intervalRamp (d (i+1)) (d i) u) :=
        Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_right
          (hc i (Finset.mem_range.mp hi)).2 (hr i).1
      _ = C*(intervalRamp (d K) (d 0) v-intervalRamp (d K) (d 0) u) := by
        rw [← Finset.mul_sum,Finset.sum_sub_distrib,intervalRamp_sum,intervalRamp_sum]
        unfold intervalRamp
        ring
      _ ≤ C*(v-u) := mul_le_mul_of_nonneg_left
        (intervalRamp_increment (hd (Nat.zero_le K)) huv).2 hC

theorem planarProfile_lipschitz {N : ℕ} (hN : 0 < N) {L : Finset (CellPath 2)}
    (hL : L ⊆ cubePaths 2 N) (F : CellPath 2 → List ℕ) (B K : ℕ) (p : CellPath 2) :
    LipschitzWith 2 (fun x : ℝ => regularizedProfile L F N B K p ((N : ℝ)*x)) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hi {u v : ℝ} (huv : u ≤ v) :
      0 ≤ regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ∧
      regularizedProfile L F N B K p ((N : ℝ)*v)-
        regularizedProfile L F N B K p ((N : ℝ)*u) ≤ 2*(v-u) := by
    have hstep := finiteRampProfile_increment_all
      (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) K
      (show Antitone (fun i => (blockDepth N B i : ℝ)) from fun _ _ h =>
        Nat.cast_le.mpr (blockDepth_antitone N B h))
      (show 0 ≤ (2 : ℝ)/(N : ℝ) by positivity)
      (fun i _ => blockSlope_bounds hN hL F B i p)
      (mul_le_mul_of_nonneg_left huv hNR.le)
    refine ⟨hstep.1,hstep.2.trans_eq ?_⟩
    field_simp
  rw [lipschitzWith_iff_dist_le_mul]
  intro x y
  simp only [Real.dist_eq,NNReal.coe_ofNat]
  by_cases hxy : x ≤ y
  · have hb := hi hxy
    rw [abs_of_nonpos (by linarith [hb.1]),abs_of_nonpos (sub_nonpos.mpr hxy)]
    linarith [hb.2]
  · have hb := hi (le_of_not_ge hxy)
    rw [abs_of_nonneg hb.1,abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge hxy))]
    exact hb.2

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

theorem blockProduct_ratio_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1) :
    (blockProduct L F N B (N/B+1) p : ℝ)/(blockProduct L F N B i p : ℝ) =
      (2 : ℝ)^((N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i)) := by
  rw [blockProduct_profile_difference hN hL F B (N/B+1) p (le_refl _),
    blockProduct_profile_difference hN hL F B (N/B+1) p hi,
    blockDepth_terminal N hB,Nat.cast_zero,regularizedProfile_zero,sub_zero,← Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
  congr 1
  ring

theorem blockProduct_inverse_ratio_profile {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1) :
    (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) =
      (2 : ℝ)^(-((N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i))) := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    ← blockProduct_ratio_profile hN hL F hB p hi,inv_div]

theorem regularizedProfile_lower_of_ratio_bound {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {i : ℕ} (hi : i ≤ N/B+1)
    {t A : ℝ}
    (hbound : (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
      (2 : ℝ)^(A-t*(blockDepth N B i : ℝ))) :
    t*(blockDepth N B i : ℝ)-A ≤
      (N : ℝ)*regularizedProfile L F N B (N/B+1) p (blockDepth N B i) := by
  rw [blockProduct_inverse_ratio_profile hN hL F hB p hi,
    Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)] at hbound
  linarith

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

theorem exists_planar_leaf_injection {δ : ℝ} {P : Finset (Space 2)}
    (hP : FiniteSeparatedAt δ P) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    (hcarry : ∀ x ∈ P, x ∈ Q.carrier) (N : ℕ)
    (hsmall : Real.sqrt 2*(Q.side/(2 : ℝ)^N) < δ) :
    ∃ l : Space 2 → CellPath 2,
      (∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier) ∧
      Set.InjOn l (P : Set (Space 2)) := by
  classical
  have hex (x : Space 2) : ∃ p : CellPath 2,
      x ∈ P → p ∈ cubePaths 2 N ∧ x ∈ (Q.descendant p).carrier := by
    by_cases hx : x ∈ P
    · obtain ⟨p,hp,hxp⟩ := Q.mem_descendant_at_depth N (hcarry x hx)
      exact ⟨p,fun _ => ⟨hp,hxp⟩⟩
    · exact ⟨[],fun h => False.elim (hx h)⟩
  choose l hl using hex
  refine ⟨l,hl,?_⟩
  intro x hx y hy he
  by_contra hxy
  have hxQ := (hl x hx).2
  have hyQ := (hl y hy).2
  rw [← he] at hyQ
  have hside : 0 ≤ (Q.descendant (l x)).side := by rw [Q.descendant_side]; positivity
  have hd := (Q.descendant (l x)).dist_le hside hxQ hyQ
  have hlen : (l x).length = N := (mem_cubePaths _ _ _).mp (hl x hx).1
  rw [Q.descendant_side,hlen] at hd
  have hs := hP x hx y hy hxy
  linarith

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

theorem leaf_prefix_card_ball_bound {δ s K r : ℝ} {P : Finset (Space 2)}
    (hball : NormalizedFiniteBallBound δ s K P) (Q : DyadicCube 2) (hQ : 0 < Q.side)
    {l : Space 2 → CellPath 2} (hl : Set.InjOn l (P : Set (Space 2)))
    (hcarry : ∀ x ∈ P, x ∈ (Q.descendant (l x)).carrier)
    (k : ℕ) (p : CellPath 2) (hdr : δ ≤ r) (hr1 : r ≤ 1)
    (hdiam : Real.sqrt 2*(Q.descendant p).side ≤ r) :
    ((prefixFiber (P.image l) k p).card : ℝ) ≤ K*r^s*(P.card : ℝ) := by
  classical
  rw [leaf_image_prefixFiber_card hl]
  have hside : 0 < (Q.descendant p).side := by rw [Q.descendant_side]; positivity
  have hsub : (P.filter fun x => (l x).take k = p) ⊆
      P.filter (fun x => dist x (Q.descendant p).center ≤ r) := by
    intro x hx
    obtain ⟨hxP,hxp⟩ := Finset.mem_filter.mp hx
    have hc := descendant_subset_take Q hQ (l x) k (hcarry x hxP)
    rw [hxp] at hc
    exact Finset.mem_filter.mpr ⟨hxP,
      ((Q.descendant p).dist_le hside.le hc ((Q.descendant p).center_mem hside)).trans hdiam⟩
  have hcard : ((P.filter fun x => (l x).take k = p).card : ℝ) ≤
      (P.filter (fun x => dist x (Q.descendant p).center ≤ r)).card := by
    exact_mod_cast Finset.card_le_card hsub
  exact hcard.trans (hball _ r hdr hr1)

theorem leaf_image_prefix_count_bound {δ s K r : ℝ} (hδ : 0 < δ) (hK : 0 ≤ K)
    {P : Finset (Space 2)} (hball : NormalizedFiniteBallBound δ s K P)
    (Q : DyadicCube 2) (hQ : 0 < Q.side) {N k : ℕ} (hk : k ≤ N)
    {l : Space 2 → CellPath 2} (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hdr : δ ≤ r) (hr1 : r ≤ 1) (hdiam : Real.sqrt 2*(Q.side/(2 : ℝ)^k) ≤ r)
    (p : CellPath 2) :
    ((prefixFiber (P.image l) k p).card : ℝ) ≤ K*r^s*((P.image l).card : ℝ) := by
  classical
  rw [Finset.card_image_iff.mpr hl]
  by_cases hp : (prefixFiber (P.image l) k p).Nonempty
  · obtain ⟨q,hq⟩ := hp
    obtain ⟨hq,hqp⟩ := Finset.mem_filter.mp hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    have hlen : p.length = k := by
      rw [← hqp,List.length_take,(mem_cubePaths _ _ _).mp (hleaf x hx).1,Nat.min_eq_left hk]
    apply leaf_prefix_card_ball_bound hball Q hQ hl (fun x hx => (hleaf x hx).2) k p hdr hr1
    simpa only [Q.descendant_side,hlen] using hdiam
  · rw [Finset.not_nonempty_iff_eq_empty.mp hp,Finset.card_empty,Nat.cast_zero]
    exact mul_nonneg (mul_nonneg hK (Real.rpow_nonneg (hδ.le.trans hdr) _)) (Nat.cast_nonneg _)

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
-- module Solutions.OAIQ088_FD.Falconer_Estimates_TubeUniformization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.sphereMeasure_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equalizing the sizes of tube pencils with only the dyadic logarithmic
loss used in Orponen--Shmerkin, Section 9. -/
namespace Falconer
open scoped BigOperators
attribute [local instance] Classical.propDecidable

theorem exists_dyadic_tube_bucket (P : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) {M : ℕ} (hT : ∀ x ∈ P, (T x).Nonempty)
    (hM : ∀ x ∈ P, (T x).card ≤ M) :
    ∃ k : ℕ, ∃ Q : Finset (Space 2), Q.Nonempty ∧ Q ⊆ P ∧
      (P.card : ℝ) ≤ (Nat.log 2 M+1 : ℕ)*(Q.card : ℝ) ∧
      ∀ x ∈ Q, 2^k ≤ (T x).card ∧ (T x).card < 2^(k+1) := by
  let L := Nat.log 2 M+1
  let f : Space 2 → ℕ := fun x => Nat.log 2 (T x).card
  have hL : (0 : ℝ) < L := by dsimp [L]; positivity
  have hmap : ∀ x ∈ P, f x ∈ Finset.range L := by
    intro x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.log_mono_right (hM x hx)))
  have hdiv : (Finset.range L).card • ((P.card : ℝ)/(L : ℝ)) ≤ (P.card : ℝ) := by
    simp only [Finset.card_range, nsmul_eq_mul]
    rw [mul_div_cancel₀ _ (ne_of_gt hL)]
  obtain ⟨k,hk,hsize⟩ := Finset.exists_le_card_fiber_of_nsmul_le_card_of_maps_to
    (M := ℝ) hmap (show (Finset.range L).Nonempty from ⟨0,Finset.mem_range.mpr (by dsimp [L]; omega)⟩) hdiv
  let Q := P.filter (fun x => f x = k)
  have hQ : Q.Nonempty := by
    apply Finset.card_pos.mp
    have hp : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
    have hq : (0 : ℝ) < Q.card := (div_pos hp hL).trans_le hsize
    exact_mod_cast hq
  refine ⟨k,Q,hQ,Finset.filter_subset _ _,?_,?_⟩
  · have h := (div_le_iff₀ hL).mp hsize
    simpa only [mul_comm] using h
  · intro x hx
    obtain ⟨hxP,hxk⟩ := Finset.mem_filter.mp hx
    have hn : (T x).card ≠ 0 := (hT x hxP).card_pos.ne'
    dsimp [f] at hxk
    constructor
    · rw [← hxk]
      exact Nat.pow_log_le_self 2 hn
    · rw [← hxk]
      exact Nat.lt_pow_succ_log_self (by norm_num) _

theorem exists_equal_size_tube_pencils (P : Finset (Space 2))
    (T : Space 2 → Finset (Space 2)) (hP : P.Nonempty) {M : ℕ}
    (hT : ∀ x ∈ P, (T x).Nonempty) (hM : ∀ x ∈ P, (T x).card ≤ M) :
    ∃ k : ℕ, ∃ Q : Finset (Space 2), ∃ U : Space 2 → Finset (Space 2),
      Q.Nonempty ∧ Q ⊆ P ∧ (P.card : ℝ) ≤ (Nat.log 2 M+1 : ℕ)*(Q.card : ℝ) ∧
      ∀ x ∈ Q, U x ⊆ T x ∧ (U x).card = 2^k ∧ (T x).card ≤ 2*(U x).card := by
  obtain ⟨k,Q,hQ,hQP,hsize,hbucket⟩ := exists_dyadic_tube_bucket P T hP hT hM
  have hc (x : Space 2) (hx : x ∈ Q) : ∃ U ⊆ T x, U.card = 2^k :=
    Finset.exists_subset_card_eq (hbucket x hx).1
  let U : Space 2 → Finset (Space 2) := fun x => if hx : x ∈ Q then Classical.choose (hc x hx) else ∅
  refine ⟨k,Q,U,hQ,hQP,hsize,?_⟩
  intro x hx
  have hu := Classical.choose_spec (hc x hx)
  have he : U x = Classical.choose (hc x hx) := dite_eq_left hx
  rw [he]
  refine ⟨hu.1,hu.2,?_⟩
  rw [hu.2]
  have hb := (hbucket x hx).2
  rw [pow_succ] at hb
  omega

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_LocalCellLines
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The exact line map for an isotropically rescaled point cell. It preserves
the original line witnesses and their cardinalities; no direction thinning
is needed for the elementary local incidence estimate. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem localCellLine_leftInverse {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.LeftInverse (unlocalCellLine Δ y a) (localCellLine Δ y a) := by
  intro l
  ext i
  fin_cases i
  · rfl
  · change Δ*((l 0*y+l 1-a)/Δ)-l 0*y+a = l 1
    field_simp
    ring

theorem localCellLine_injective {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ) :
    Function.Injective (localCellLine Δ y a) :=
  (localCellLine_leftInverse hΔ y a).injective

theorem localCellLine_residual {Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) :
    localPacketPoint Δ y a p 1-localCellLine Δ y a l 0*localPacketPoint Δ y a p 0-
      localCellLine Δ y a l 1 = (p 1-l 0*p 0-l 1)/Δ := by
  change (p 1-a)/Δ-l 0*((p 0-y)/Δ)-(l 0*y+l 1-a)/Δ = _
  field_simp
  ring

theorem localCellLine_incident {δ Δ : ℝ} (hΔ : 0 < Δ) (y a : ℝ)
    (p l : Space 2) (hi : TubeIncident δ p l) :
    TubeIncident (δ/Δ) (localPacketPoint Δ y a p) (localCellLine Δ y a l) := by
  unfold TubeIncident at hi ⊢
  rw [localCellLine_residual hΔ,abs_div,abs_of_pos hΔ]
  change (|p 1-l 0*p 0-l 1|/Δ)/Real.sqrt (1+(l 0)^2) ≤ δ/Δ
  calc
    _ = (|p 1-l 0*p 0-l 1|/Real.sqrt (1+(l 0)^2))/Δ := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hi hΔ.le

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_PlanarTreeUniformization
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A logarithmic-cost planar block regularization. The existing exact
prefix classes preserve the local child counts; only the sharper block-width
count and the cardinality selection are needed here. -/
namespace Falconer.Regularization
attribute [local instance] Classical.propDecidable

theorem planar_blockLabel_card_le {L : Finset (CellPath 2)} {N : ℕ}
    (hL : L ⊆ cubePaths 2 N) (B : ℕ) (f : CellPath 2 → List ℕ) (K : ℕ) :
    (L.image (blockLabel L N B f K)).card ≤ (2*B+1)^K*(L.image f).card := by
  induction K with
  | zero => simp [blockLabel]
  | succ K ih =>
    have hs := extendLabel_card_le (blockDepth_antitone N B (Nat.le_succ K))
      (Nat.sub_le N (K*B)) hL (blockLabel L N B f K)
    have hb : 2*(blockDepth N B K-blockDepth N B (K+1))+1 ≤ 2*B+1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left 2 (blockDepth_gap N B K)) 1
    calc
      _ ≤ (2*B+1)*(L.image (blockLabel L N B f K)).card :=
        hs.trans (Nat.mul_le_mul_right _ hb)
      _ ≤ (2*B+1)*((2*B+1)^K*(L.image f).card) := Nat.mul_le_mul_left _ ih
      _ = _ := by rw [pow_succ]; ac_rfl

theorem exists_large_planar_block_class {L : Finset (CellPath 2)} {N : ℕ}
    (hL : L ⊆ cubePaths 2 N) (hLne : L.Nonempty) (B K : ℕ) :
    let F := blockLabel L N B (fun _ => []) K
    ∃ p ∈ L, L.card ≤ (2*B+1)^K*(classLeaves L F (F p)).card := by
  dsimp only
  let F := blockLabel L N B (fun _ => []) K
  obtain ⟨T,hT,hmax⟩ := (L.image F).exists_max_image
    (fun T => (classLeaves L F T).card) (hLne.image F)
  obtain ⟨p,hp,hpT⟩ := Finset.mem_image.mp hT
  refine ⟨p,hp,?_⟩
  have hc : (L.image F).card ≤ (2*B+1)^K := by
    have h := planar_blockLabel_card_le hL B (fun _ => []) K
    have hi : (L.image (fun _ : CellPath 2 => ([] : List ℕ))).card ≤ 1 :=
      Finset.card_le_one.mpr (by intro a ha b hb; simp_all)
    exact h.trans ((Nat.mul_le_mul_left _ hi).trans_eq (Nat.mul_one _))
  calc
    L.card = ∑ t ∈ L.image F, (classLeaves L F t).card := by
      simpa only [classLeaves] using Finset.card_eq_sum_card_image F L
    _ ≤ ∑ _t ∈ L.image F, (classLeaves L F T).card := Finset.sum_le_sum hmax
    _ = (L.image F).card*(classLeaves L F T).card := by simp
    _ ≤ (2*B+1)^K*(classLeaves L F T).card := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← hpT]

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_QuarterPencilGeometry
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed point contraction and its exact line map. This preserves the
original incidence witnesses and the dyadic scale needed by regular gain. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem unlocalCellLine_four_dist (l m : Space 2) :
    dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m) ≤ 4*dist l m := by
  have h := EuclideanSpace.dist_sq_eq l m
  have h' := EuclideanSpace.dist_sq_eq (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)
  simp only [Fin.sum_univ_two,Real.dist_eq,sq_abs] at h h'
  change dist (unlocalCellLine 4 0 0 l) (unlocalCellLine 4 0 0 m)^2 =
    (l 0-m 0)^2+((4*l 1-l 0*0+0)-(4*m 1-m 0*0+0))^2 at h'
  nlinarith [sq_nonneg (l 0-m 0),dist_nonneg (x := l) (y := m),
    dist_nonneg (x := unlocalCellLine 4 0 0 l) (y := unlocalCellLine 4 0 0 m)]

theorem localCellLine_four_separated {δ : ℝ} (T : Finset (Space 2))
    (hT : FiniteSeparatedAt δ T) :
    FiniteSeparatedAt (δ/4) (T.image (localCellLine 4 0 0)) := by
  intro l hl m hm hlm
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hm
  have hsep := hT a ha b hb (fun he => hlm (congrArg (localCellLine 4 0 0) he))
  have hd := unlocalCellLine_four_dist (localCellLine 4 0 0 a) (localCellLine 4 0 0 b)
  rw [localCellLine_leftInverse (by norm_num) 0 0 a,
    localCellLine_leftInverse (by norm_num) 0 0 b] at hd
  linarith

theorem localCellLine_four_regular {δ s K : ℝ} (hδ : 0 < δ)
    (hs : 0 ≤ s) (hK : 1 ≤ K) (T : Finset (Space 2))
    (hT : NormalizedFiniteBallBound δ s K T) :
    NormalizedFiniteBallBound (δ/4) s (K*4^s) (T.image (localCellLine 4 0 0)) := by
  intro z r hr _
  have hr0 : 0 < r := (by linarith : 0 < δ/4).trans_le hr
  let w := unlocalCellLine 4 0 0 z
  have hsub : (T.image (localCellLine 4 0 0)).filter (fun l => dist l z ≤ r) ⊆
      (T.filter (fun l => dist l w ≤ 4*r)).image (localCellLine 4 0 0) := by
    intro l hl
    obtain ⟨hl,hlr⟩ := Finset.mem_filter.mp hl
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
    refine Finset.mem_image.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,?_⟩,rfl⟩
    have hh := unlocalCellLine_four_dist (localCellLine 4 0 0 a) z
    rw [localCellLine_leftInverse (by norm_num) 0 0 a] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hlr (by norm_num))
  rw [Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]
  calc
    _ ≤ ((T.filter (fun l => dist l w ≤ 4*r)).card:ℝ) :=
      Nat.cast_le.mpr ((Finset.card_le_card hsub).trans Finset.card_image_le)
    _ ≤ K*(4*r)^s*(T.card:ℝ) := normalized_ball_bound_all_radii hs hK hT w (4*r)
      (by linarith only [hr])
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) hr0.le]; ring

theorem localCellLine_four_chart (T : Finset (Space 2)) (hT : InBoundedLineChart T) :
    InBoundedLineChart (T.image (localCellLine 4 0 0)) := by
  intro l hl
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hl
  constructor
  · exact (hT a ha).1
  · change |(a 0*0+a 1-0)/(4:ℝ)| ≤ 1
    rw [abs_div]
    norm_num only [mul_zero,zero_add,sub_zero,abs_of_pos (by norm_num : (0:ℝ) < 4)]
    linarith only [(hT a ha).2]

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
-- module Solutions.OAIQ088_FD.Falconer_Incidence_ProfileBlockBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose one even block width so that all block-label and fixed per-block
losses fit the prescribed weak exponent, uniformly in the total depth. -/
namespace Falconer

theorem exists_even_profile_block_budget {ε : ℝ} (hε : 0 < ε) (c : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∀ m : ℕ, 0 < m →
      (((2*B+1:ℕ):ℝ)^(m+1))*(2:ℝ)^(c*(m+1)) ≤
        (2:ℝ)^(ε*((B*m:ℕ):ℝ)) := by
  obtain ⟨B0,hB0,hbudget⟩ := dyadic_quadratic_loss (half_pos hε)
    (show 0 ≤ 3*(2:ℝ)^c by positivity)
  let B := 2*B0
  have hB : 0 < B := by dsimp [B]; omega
  have hBge : B0 ≤ B := by dsimp [B]; omega
  have hbase : ((2*B+1:ℕ):ℝ)*(2:ℝ)^c ≤ (2:ℝ)^((ε/2)*(B:ℝ)) := by
    have hh := hbudget B hBge
    have hdom : ((2*B+1:ℕ):ℝ) ≤ 3*((B:ℝ)+1)^2 := by
      push_cast
      nlinarith only [sq_nonneg (B:ℝ),Nat.cast_nonneg (α := ℝ) B]
    calc
      _ ≤ (3*((B:ℝ)+1)^2)*(2:ℝ)^c := mul_le_mul_of_nonneg_right hdom (by positivity)
      _ = (3*(2:ℝ)^c)*((B:ℝ)+1)^2 := by ring
      _ ≤ Real.exp ((ε/2)*(B:ℝ)*Real.log 2) := hh
      _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  refine ⟨B,hB,⟨B0,by dsimp [B]; omega⟩,?_⟩
  intro m hm
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hlength : (ε/2)*(B:ℝ)*(m+1:ℕ) ≤ ε*((B*m:ℕ):ℝ) := by
    push_cast
    have hh := mul_le_mul_of_nonneg_left (show (m:ℝ)+1 ≤ 2*(m:ℝ) by linarith only [hmR])
      (show 0 ≤ (ε/2)*(B:ℝ) by positivity)
    nlinarith only [hh]
  calc
    _ = (((2*B+1:ℕ):ℝ)*(2:ℝ)^c)^(m+1) := by rw [mul_pow,pow_mul]
    _ ≤ ((2:ℝ)^((ε/2)*(B:ℝ)))^(m+1) := pow_le_pow_left₀ (by positivity) hbase _
    _ = (2:ℝ)^((ε/2)*(B:ℝ)*(m+1:ℕ)) :=
      (Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2) _ _).symm
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) hlength

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileStepBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One explicit budget for the two branches of the endpoint scale product. -/
namespace Falconer

theorem profile_step_budget_bounds {H G W : ℝ} (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    W ≤ profileStepBudget H G W ∧ 4*H ≤ profileStepBudget H G W ∧
      280*W*H^3 ≤ profileStepBudget H G W ∧
      672*W^2*H^3 ≤ profileStepBudget H G W ∧
      32*W*H^3 ≤ profileStepBudget H G W ∧
      W*(20*H^2)*G ≤ profileStepBudget H G W ∧
      W*(16*W*H^3)*G ≤ profileStepBudget H G W := by
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hG0 : 0 ≤ G := zero_le_one.trans hG
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hW2 : W ≤ W^2 := by nlinarith only [hW]
  have hH2 : H^2 ≤ H^3 := by nlinarith only [sq_nonneg H,mul_le_mul_of_nonneg_left hH (sq_nonneg H)]
  have hH3 : 1 ≤ H^3 := one_le_pow₀ hH
  have hW21 : 1 ≤ W^2 := one_le_pow₀ hW
  have hHH3 : H ≤ H^3 := (show H ≤ H^2 by nlinarith only [hH]).trans hH2
  have hcore : W^2*H^3 ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    calc
      _ ≤ 1024*(W^2*H^3) := by nlinarith only [mul_nonneg (sq_nonneg W) (pow_nonneg hH0 3)]
      _ ≤ _ := by
        convert le_mul_of_one_le_right (show 0 ≤ 1024*(W^2*H^3) by positivity) hG using 1 <;> first | rfl | ring
  have bound {c : ℝ} (_hc : 0 ≤ c) (hc' : c ≤ 1024) :
      c*W^2*H^3*G ≤ profileStepBudget H G W := by
    dsimp [profileStepBudget]
    gcongr
  refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
  · exact (hW2.trans (le_mul_of_one_le_right (sq_nonneg W) hH3)).trans hcore
  · calc
      4*H ≤ 4*W^2*H^3*G := by
        calc
          _ ≤ 4*W^2*H^3 := by
            calc
              _ ≤ 4*H^3 := mul_le_mul_of_nonneg_left hHH3 (by norm_num)
              _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_right hW21 (pow_nonneg hH0 3)]
          _ ≤ _ := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ ≤ 280*W^2*H^3 := by gcongr
      _ ≤ 280*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · exact (le_mul_of_one_le_right (by positivity) hG).trans
      (bound (c := 672) (by norm_num) (by norm_num))
  · calc
      _ ≤ 32*W^2*H^3 := by gcongr
      _ ≤ 32*W^2*H^3*G := le_mul_of_one_le_right (by positivity) hG
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 20*W*H^2*G := by ring
      _ ≤ 20*W^2*H^3*G := by gcongr
      _ ≤ _ := bound (by norm_num) (by norm_num)
  · calc
      _ = 16*W^2*H^3*G := by ring
      _ ≤ _ := bound (by norm_num) (by norm_num)

theorem profile_label_cost_one_le (B K : ℕ) :
    1 ≤ (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K := by
  apply one_le_mul_of_one_le_of_one_le
  · exact one_le_pow₀ (by norm_num)
  · apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 2*B+1 by omega)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIntervalChain
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite composition of actual profile interval estimates. Every splitting
step uses the proved endpoint construction and its explicit next budget. -/
namespace Falconer
open Set Regularization
open scoped BigOperators

theorem profileBudgetSequence_one_le {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) (n : ℕ) :
    1 ≤ profileBudgetSequence H G W n := by
  induction n with
  | zero => exact hW
  | succ n ih => exact ih.trans (profile_step_budget_bounds hH hG ih).1

theorem profileBudgetSequence_monotone {H G W : ℝ}
    (hH : 1 ≤ H) (hG : 1 ≤ G) (hW : 1 ≤ W) :
    Monotone (profileBudgetSequence H G W) := by
  apply monotone_nat_of_le_succ
  intro n
  exact (profile_step_budget_bounds hH hG (profileBudgetSequence_one_le hH hG hW n)).1

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileIterationBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact growth of the finite recursive budget. The number of intervals is
fixed before the dyadic depth is sent to infinity. -/
namespace Falconer

theorem profileBudgetSequence_eq (H G W : ℝ) (n : ℕ) :
    profileBudgetSequence H G W n =
      (1024*H^3*G)^(2^n-1)*W^(2^n) := by
  induction n with
  | zero => simp [profileBudgetSequence]
  | succ n ih =>
    rw [profileBudgetSequence,ih]
    let C := 1024*H^3*G
    have hp : 1 ≤ 2^n := Nat.one_le_pow n 2 (by omega)
    calc
      _ = C*((C^(2^n-1))^2*(W^(2^n))^2) := by dsimp [profileStepBudget,C]; ring
      _ = C^(1+(2^n-1)*2)*W^((2^n)*2) := by
        rw [← pow_mul,← pow_mul,pow_add,pow_one]
        ring
      _ = _ := by
        have he : 1+(2^n-1)*2 = 2^(n+1)-1 := by rw [pow_succ]; omega
        rw [he,pow_succ]

theorem profileBudgetSequence_power_bound {H G W lam ξ : ℝ} {N : ℕ}
    (hH : 0 ≤ H) (hG : 0 ≤ G) (hW : 0 ≤ W)
    (hC : 1024*H^3*G ≤ (2:ℝ)^(ξ*(N:ℝ)))
    (hWb : W ≤ (2:ℝ)^(lam*(N:ℝ))) (n : ℕ) :
    profileBudgetSequence H G W n ≤
      (2:ℝ)^((((2^n-1:ℕ):ℝ)*ξ+((2^n:ℕ):ℝ)*lam)*(N:ℝ)) := by
  rw [profileBudgetSequence_eq]
  calc
    _ ≤ ((2:ℝ)^(ξ*(N:ℝ)))^(2^n-1)*((2:ℝ)^(lam*(N:ℝ)))^(2^n) := by
      exact mul_le_mul (pow_le_pow_left₀ (by positivity) hC _)
        (pow_le_pow_left₀ hW hWb _) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2),
        ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
      congr 1
      ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileUniformIterationBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose the block width after fixing the maximal number of intervals.
All recursive losses then fit a prescribed weak exponent uniformly in depth. -/
namespace Falconer

theorem exists_uniform_profile_iteration_budget {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ N0 : ℕ, 0 < N0 ∧
      ∀ m : ℕ, 0 < m → N0 ≤ B*m → ∀ j : ℕ, j ≤ J →
        let N := B*m
        let H : ℝ := (4*(N+2)+11:ℕ)
        let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
        profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ))) j ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
        G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
  let p : ℝ := ((2^J:ℕ):ℝ)
  have hp : 0 < p := by dsimp [p]; positivity
  let lam := ε/(4*p)
  have hlam : 0 < lam := by dsimp [lam]; positivity
  obtain ⟨B,hB,hBeven,hblock⟩ := exists_even_profile_block_budget (show 0 < lam/4 by positivity) 3
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_polynomial_loss hlam
    (show 0 ≤ (1024:ℝ)*19^3 by positivity) 3
  refine ⟨B,hB,hBeven,lam,hlam,N0,hN0,?_⟩
  intro m hm hN j hj
  let N := B*m
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
  have hN0' : N0 ≤ N := hN
  have hH0 : 0 ≤ H := by dsimp [H]; positivity
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hG : 1 ≤ G := profile_label_cost_one_le B (m+1)
  have hGsmall : G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    simpa only [G,N,mul_comm] using hblock m hm
  have hGbound : G ≤ (2:ℝ)^(lam*(N:ℝ)) := hGsmall.trans
    (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/4 ≤ lam) (Nat.cast_nonneg N)))
  have hHbound : H ≤ 19*((N:ℝ)+1) := by
    dsimp [H]
    push_cast
    nlinarith only [Nat.cast_nonneg (α := ℝ) N]
  have hpolybound : 1024*H^3 ≤ (2:ℝ)^(lam*(N:ℝ)) := by
    calc
      _ ≤ (1024:ℝ)*(19*((N:ℝ)+1))^3 := by gcongr
      _ = (1024:ℝ)*19^3*((N:ℝ)+1)^3 := by ring
      _ ≤ Real.exp (lam*(N:ℝ)*Real.log 2) := hpoly N hN0'
      _ = _ := by rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  have hC : 1024*H^3*G ≤ (2:ℝ)^((2*lam)*(N:ℝ)) := by
    calc
      _ ≤ (2:ℝ)^(lam*(N:ℝ))*(2:ℝ)^(lam*(N:ℝ)) :=
        mul_le_mul hpolybound hGbound (zero_le_one.trans hG) (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
  have hW : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hlast := profileBudgetSequence_power_bound hH0 (zero_le_one.trans hG)
    (show 0 ≤ (2:ℝ)^(lam*(N:ℝ)) by positivity) hC le_rfl J
  have hpow : (((2^J-1:ℕ):ℝ)*(2*lam)+((2^J:ℕ):ℝ)*lam) ≤ ε := by
    have hsub : ((2^J-1:ℕ):ℝ) ≤ p := by dsimp [p]; exact_mod_cast Nat.sub_le (2^J) 1
    have he : p*lam = ε/4 := by dsimp [lam]; field_simp
    have hh := mul_le_mul_of_nonneg_right hsub (show 0 ≤ 2*lam by positivity)
    nlinarith only [hh,he,hε]
  refine ⟨?_,hGsmall⟩
  calc
    _ ≤ profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ))) J :=
      profileBudgetSequence_monotone hH hG hW hj
    _ ≤ (2:ℝ)^((((2^J-1:ℕ):ℝ)*(2*lam)+((2^J:ℕ):ℝ)*lam)*(N:ℝ)) := hlast
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right hpow (Nat.cast_nonneg N))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileApplicationBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One block width and one weak initial constant control all profile-cell
estimates and every step of a bounded-length interval composition. -/
namespace Falconer

theorem profile_label_le_first_iterate {H W : ℝ} (hH : 1 ≤ H) (hW : 1 ≤ W)
    (B K : ℕ) :
    (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K ≤
      profileBudgetSequence H ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K) W 1 := by
  rw [profileBudgetSequence]
  change _ ≤ 1024*W^2*H^3*((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K)
  apply le_mul_of_one_le_left (by positivity)
  have hw : (1:ℝ) ≤ W^2 := one_le_pow₀ hW
  have hh : (1:ℝ) ≤ H^3 := one_le_pow₀ hH
  nlinarith only [mul_le_mul hw hh (by norm_num) (sq_nonneg W)]

theorem profile_sixth_power_le_label_square (B K : ℕ) :
    (2:ℝ)^(6*K) ≤ ((2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K)^2 := by
  have hb : (1:ℝ) ≤ ((2*B+1:ℕ):ℝ)^K := by
    apply one_le_pow₀
    exact_mod_cast (show 1 ≤ 2*B+1 by omega)
  have hh := le_mul_of_one_le_right (show 0 ≤ (2:ℝ)^(3*K) by positivity) hb
  have hpow := pow_le_pow_left₀ (show 0 ≤ (2:ℝ)^(3*K) by positivity) hh 2
  convert hpow using 1
  all_goals try with_reducible_and_instances rfl
  rw [← pow_mul]
  congr 1
  omega

theorem exists_profile_application_budget {ε : ℝ} (hε : 0 < ε) (J : ℕ) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ N0 : ℕ, 0 < N0 ∧
    ∀ m : ℕ, 0 < m → N0 ≤ B*m →
      let N := B*m
      let H : ℝ := (4*(N+2)+11:ℕ)
      let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
      let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
      (∀ j ≤ 2*J+1, W j ≤ (2:ℝ)^(ε*(N:ℝ))) ∧
      (∀ j ≤ 2*J, ∀ A : ℝ,
        profileGeometryConstant (m+1) B (W j) A ≤ (2:ℝ)^((4*ε)*(N:ℝ)+A)) ∧
      640*((N:ℝ)+3) ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
      (43264*H^4)^(2*J) ≤ (2:ℝ)^(ε*(N:ℝ)) ∧
      G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
  obtain ⟨B,hB,hBeven,lam,hlam,N1,hN1,hiter⟩ := exists_uniform_profile_iteration_budget hε (2*J+1)
  obtain ⟨N2,hN2,hfixed⟩ := dyadic_polynomial_loss hε
    (show 0 ≤ 100000*(2:ℝ)^(2*B) by positivity) 0
  obtain ⟨N3,hN3,hpoly⟩ := dyadic_polynomial_loss hε (show 0 ≤ (1920:ℝ) by norm_num) 1
  obtain ⟨N4,hN4,hcomp⟩ := dyadic_polynomial_loss hε
    (show 0 ≤ ((43264:ℝ)*19^4)^(2*J) by positivity) (8*J)
  refine ⟨B,hB,hBeven,lam,hlam,max N1 (max N2 (max N3 N4)),by omega,?_⟩
  intro m hm hN
  dsimp only
  let N := B*m
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1)
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have h1 : N1 ≤ N := by dsimp [N]; omega
  have h2 : N2 ≤ N := by dsimp [N]; omega
  have h3 : N3 ≤ N := by dsimp [N]; omega
  have h4 : N4 ≤ N := by dsimp [N]; omega
  have exp_eq (a : ℝ) : Real.exp (a*(N:ℝ)*Real.log 2) = (2:ℝ)^(a*(N:ℝ)) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
    congr 1
    ring
  have hW (j : ℕ) (hj : j ≤ 2*J+1) : W j ≤ (2:ℝ)^(ε*(N:ℝ)) := (hiter m hm h1 j hj).1
  have hH : 1 ≤ H := by dsimp [H]; exact_mod_cast (show 1 ≤ 4*(N+2)+11 by omega)
  have hW0 : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hG : G ≤ (2:ℝ)^(ε*(N:ℝ)) :=
    (profile_label_le_first_iterate hH hW0 B (m+1)).trans (hW 1 (by omega))
  have hK : (2:ℝ)^(6*(m+1)) ≤ (2:ℝ)^((2*ε)*(N:ℝ)) := by
    calc
      _ ≤ G^2 := profile_sixth_power_le_label_square B (m+1)
      _ ≤ ((2:ℝ)^(ε*(N:ℝ)))^2 := pow_le_pow_left₀ (by positivity) hG 2
      _ = _ := by
        rw [← Real.rpow_mul_natCast (by norm_num : (0:ℝ) ≤ 2)]
        congr 1
        norm_num
        ring
  have hfixed' : 100000*(2:ℝ)^(2*B) ≤ (2:ℝ)^(ε*(N:ℝ)) := by
    simpa only [pow_zero,mul_one,exp_eq] using hfixed N h2
  refine ⟨hW,?_,?_,?_,(hiter m hm h1 0 (by omega)).2⟩
  · intro j hj A
    have hWj := hW j (show j ≤ 2*J+1 by omega)
    have hWj0 : 0 ≤ W j := zero_le_one.trans
      (profileBudgetSequence_one_le hH (profile_label_cost_one_le B (m+1)) hW0 j)
    calc
      _ = (100000*(2:ℝ)^(2*B))*(W j)*(2:ℝ)^(6*(m+1))*(2:ℝ)^A := by
        dsimp [profileGeometryConstant]
        ring
      _ ≤ (2:ℝ)^(ε*(N:ℝ))*(2:ℝ)^(ε*(N:ℝ))*(2:ℝ)^((2*ε)*(N:ℝ))*(2:ℝ)^A := by
        gcongr
      _ = _ := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2),
          ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
  · calc
      _ ≤ 1920*((N:ℝ)+1)^1 := by
        change 640*((N:ℝ)+3) ≤ 1920*((N:ℝ)+1)^1
        rw [pow_one]
        nlinarith only [Nat.cast_nonneg (α := ℝ) N]
      _ ≤ Real.exp (ε*(N:ℝ)*Real.log 2) := hpoly N h3
      _ = _ := exp_eq ε
  · have hHle : H ≤ 19*((N:ℝ)+1) := by
      dsimp [H]
      push_cast
      nlinarith only [Nat.cast_nonneg (α := ℝ) N]
    calc
      _ ≤ (43264*(19*((N:ℝ)+1))^4)^(2*J) := by gcongr
      _ = ((43264:ℝ)*19^4)^(2*J)*((N:ℝ)+1)^(8*J) := by
        simp only [mul_pow,← pow_mul]
        rw [show 4*(2*J) = 8*J by omega]
        ring
      _ ≤ Real.exp (ε*(N:ℝ)*Real.log 2) := hcomp N h4
      _ = _ := exp_eq ε

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileGainParameters
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative choices for the final profile application. These scalar
bounds keep the gain, rounding error and recursive losses independent. -/
namespace Falconer

theorem exists_profile_gain_accuracy {κ η eg : ℝ} (hκ : 0 < κ) (hη : 0 < η) (heg : 0 < eg) :
    ∃ α : ℝ, 0 < α ∧ α ≤ κ/100 ∧ α ≤ η*κ/100 ∧ 6*α ≤ eg/4 := by
  let α := min κ (min (η*κ) eg)/100
  have ha : 0 < α := div_pos (lt_min hκ (lt_min (mul_pos hη hκ) heg)) (by norm_num)
  refine ⟨α,ha,?_,?_,?_⟩
  · exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  · exact div_le_div_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  · have hh : α ≤ eg/100 := div_le_div_of_nonneg_right
      ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
    linarith

theorem exists_profile_gain_budget {α κ η eg τ : ℝ}
    (hα : 0 < α) (hκ : 0 < κ) (hη : 0 < η) (heg : 0 < eg) (hτ : 0 < τ) (J : ℕ) :
    ∃ β : ℝ, 0 < β ∧ β ≤ α*κ ∧ β*(13*(J:ℝ)+1) ≤ η*κ/4 ∧ 4*β ≤ eg*τ/8 := by
  let β := min (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))/2
  have hden : 0 < 4*(13*(J:ℝ)+1) := by positivity
  have hp : 0 < min (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32)) :=
    lt_min (mul_pos hα hκ) (lt_min (div_pos (mul_pos hη hκ) hden) (by positivity))
  have hb : 0 < β := half_pos hp
  have hb1 : β ≤ α*κ := by
    have hh := min_le_left (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))
    dsimp [β]
    linarith
  have hb2 : β ≤ η*κ/(4*(13*(J:ℝ)+1)) := by
    have hh := (min_le_right (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))).trans (min_le_left _ _)
    dsimp [β]
    linarith
  have hb3 : β ≤ eg*τ/32 := by
    have hh := (min_le_right (α*κ) (min (η*κ/(4*(13*(J:ℝ)+1))) (eg*τ/32))).trans (min_le_right _ _)
    dsimp [β]
    linarith
  refine ⟨β,hb,hb1,?_,by linarith⟩
  have hh := (le_div_iff₀ hden).mp hb2
  nlinarith only [hh]

theorem profile_gain_parameters_close {κ η α β lam s t : ℝ} {J : ℕ}
    (_hκ : 0 < κ) (hκ1 : κ ≤ 1/100) (hα : 0 < α) (hακ : α ≤ κ/100)
    (hαη : α ≤ η*κ/100)
    (hβα : β ≤ α*κ) (hβη : β*(13*(J:ℝ)+1) ≤ η*κ/4)
    (hlam : 0 ≤ lam) (hlamb : lam ≤ β) (hs1 : s ≤ 1)
    (ht : s+8*κ ≤ t) :
    let χ := α^2+α+lam/(t-(s+κ));
    lam+2*χ ≤ κ ∧
      s+(η*κ/2)+β ≤ s*(1-χ-α)+η*κ-18*α-13*β*(J:ℝ) := by
  dsimp only
  have ha1 : α ≤ 1 := by linarith
  have hak : α*κ ≤ α := mul_le_of_le_one_right hα.le (by linarith)
  have hd : 0 < t-(s+κ) := by linarith
  have hdiv : lam/(t-(s+κ)) ≤ α/7 := by
    apply (div_le_iff₀ hd).2
    have hh := mul_le_mul_of_nonneg_left (show 7*κ ≤ t-(s+κ) by linarith) (show 0 ≤ α/7 by positivity)
    nlinarith only [hh,hlamb,hβα]
  have hχ : α^2+α+lam/(t-(s+κ)) ≤ 3*α := by
    have hsquare : α^2 ≤ α := by nlinarith only [hα.le,ha1]
    linarith
  have hχ0 : 0 ≤ α^2+α+lam/(t-(s+κ)) := by positivity
  have hprod : s*(α^2+α+lam/(t-(s+κ))+α) ≤ 4*α := by
    exact (mul_le_mul_of_nonneg_right hs1 (by positivity)).trans (by linarith only [hχ])
  constructor
  · linarith only [hlamb,hβα,hak,hχ,hακ,hα.le]
  · nlinarith only [hprod,hβη,hαη,hα.le]

theorem exists_incidence_profile_grid_threshold {α τ κ : ℝ} (hα : 0 < α) (hτ : 0 < τ) (hκ : 0 < κ)
    (Ng N0 : ℕ) :
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m → ∀ B : ℕ, 0 < B →
      N0 ≤ B*m ∧ 2/(m:ℝ) ≤ τ/2 ∧ 4/(m:ℝ) ≤ α*τ ∧
      16/((m:ℝ)*τ) ≤ κ/2 ∧ 2/((m:ℝ)*τ) ≤ α ∧ 4*(Ng:ℝ) ≤ τ*(m*B:ℕ) := by
  obtain ⟨M,hM⟩ := exists_nat_gt ((N0:ℝ)+1+4/τ+4/(α*τ)+32/(κ*τ)+4*(Ng:ℝ)/τ)
  have hterms : 0 ≤ 4/τ ∧ 0 ≤ 4/(α*τ) ∧ 0 ≤ 32/(κ*τ) ∧ 0 ≤ 4*(Ng:ℝ)/τ := by
    exact ⟨by positivity,by positivity,by positivity,by positivity⟩
  have hMpos : 0 < M := by
    have : (0:ℝ) < M := by linarith only [hM,hterms.1,hterms.2.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
    exact_mod_cast this
  refine ⟨M,hMpos,?_⟩
  intro m hm B hB
  have hm0 : 0 < m := hMpos.trans_le hm
  have hmR : (0:ℝ) < m := Nat.cast_pos.mpr hm0
  have hbound := hM.trans_le (Nat.cast_le.mpr hm)
  have hNm : (N0:ℝ) ≤ m := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.1,hterms.2.2.2]
  have h1 : 4/τ ≤ (m:ℝ) := by linarith only [hbound,hterms.2.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h2 : 4/(α*τ) ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h3 : 32/(κ*τ) ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.2,Nat.cast_nonneg (α := ℝ) N0]
  have h4 : 4*(Ng:ℝ)/τ ≤ (m:ℝ) := by linarith only [hbound,hterms.1,hterms.2.1,hterms.2.2.1,Nat.cast_nonneg (α := ℝ) N0]
  have hmB : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hmBR : (m:ℝ) ≤ (m*B:ℕ) := Nat.cast_le.mpr hmB
  have h1' := (div_le_iff₀ hτ).mp h1
  have h2' := (div_le_iff₀ (mul_pos hα hτ)).mp h2
  have h3' := (div_le_iff₀ (mul_pos hκ hτ)).mp h3
  have h4' := (div_le_iff₀ hτ).mp h4
  refine ⟨(Nat.cast_le.mp hNm).trans (by simpa only [Nat.mul_comm] using hmB),?_,?_,?_,?_,?_⟩
  · apply (div_le_iff₀ hmR).2
    nlinarith only [h1']
  · apply (div_le_iff₀ hmR).2
    nlinarith only [h2']
  · apply (div_le_iff₀ (mul_pos hmR hτ)).2
    nlinarith only [h3']
  · apply (div_le_iff₀ (mul_pos hmR hτ)).2
    nlinarith only [h2']
  · nlinarith only [h4',mul_le_mul_of_nonneg_left hmBR hτ.le]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileMergeStep
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The low-slope absorption step in the profile decomposition. The new
interval has exactly the prescribed slope and retains the lower chord bound. -/
namespace Falconer
open Set

theorem exists_superlinear_merge_left {f : ℝ → ℝ} (hf : Continuous f)
    {a c b s ε : ℝ} (hac : a < c) (hcb : c < b) (hε : 0 ≤ ε)
    (hab : s*(b-a) < f b-f a)
    (hk : intervalSecantSlope f c (b-c) < s)
    (herr : ∀ x ∈ Icc c b, -ε*(b-c) ≤ intervalSecantError f c (b-c) x) :
    ∃ u ∈ Ioo a c, f b-f u = s*(b-u) ∧
      ∀ x ∈ Icc u b, f u+s*(x-u)-ε*(b-u) ≤ f x := by
  let k := intervalSecantSlope f c (b-c)
  have hbc : b-c ≠ 0 := sub_ne_zero.mpr hcb.ne'
  have hkb : f b-f c = k*(b-c) := by
    dsimp [k,intervalSecantSlope]
    rw [show c+(b-c) = b by ring,div_mul_cancel₀ _ hbc]
  let g : ℝ → ℝ := fun x => f x-s*x-(f b-s*b)
  have hg : Continuous g := (hf.sub (continuous_const.mul continuous_id)).sub continuous_const
  have hga : g a < 0 := by dsimp [g]; nlinarith
  have hgc : 0 < g c := by
    have hm := mul_lt_mul_of_pos_right hk (sub_pos.mpr hcb)
    dsimp [g]
    change k*(b-c) < s*(b-c) at hm
    nlinarith [hkb]
  let Z := Icc a c ∩ {x | g x = 0}
  have hZ : IsCompact Z := isCompact_Icc.inter_right (isClosed_eq hg continuous_const)
  have hZne : Z.Nonempty := by
    obtain ⟨u,hu,hgu⟩ := intermediate_value_Icc hac.le hg.continuousOn ⟨hga.le,hgc.le⟩
    exact ⟨u,hu,hgu⟩
  obtain ⟨u,hu,hmax⟩ := hZ.exists_isGreatest hZne
  have hgu : g u = 0 := hu.2
  have hua : a < u := lt_of_le_of_ne hu.1.1 (by
    intro he
    have hz := hgu
    rw [← he] at hz
    linarith)
  have huc : u < c := lt_of_le_of_ne hu.1.2 (by
    intro he
    have hz := hgu
    rw [he] at hz
    linarith)
  have hleft : ∀ x ∈ Icc u c, 0 ≤ g x := by
    intro x hx
    by_contra hn
    have hneg : g x < 0 := lt_of_not_ge hn
    have hux : u < x := lt_of_le_of_ne hx.1 (by
      intro he
      rw [← he,hgu] at hneg
      linarith)
    obtain ⟨v,hv,hgv⟩ := intermediate_value_Icc hx.2 hg.continuousOn ⟨hneg.le,hgc.le⟩
    have hvZ : v ∈ Z := ⟨⟨hu.1.1.trans (hx.1.trans hv.1),hv.2⟩,hgv⟩
    have hle := hmax hvZ
    linarith [hv.1]
  refine ⟨u,⟨hua,huc⟩,?_,?_⟩
  · have hz := hgu
    dsimp [g] at hz
    linarith
  · intro x hx
    have hz := hgu
    dsimp [g] at hz
    by_cases hxc : x ≤ c
    · have hgx := hleft x ⟨hx.1,hxc⟩
      dsimp [g] at hgx
      have heps := mul_nonneg hε (sub_nonneg.mpr (hx.1.trans hx.2))
      nlinarith
    · have hx' : x ∈ Icc c b := ⟨le_of_not_ge hxc,hx.2⟩
      have he := herr x hx'
      change -ε*(b-c) ≤ f x-f c-k*(x-c) at he
      have hslope := mul_le_mul_of_nonneg_right hk.le (sub_nonneg.mpr hx.2)
      change k*(b-x) ≤ s*(b-x) at hslope
      have herrscale := mul_le_mul_of_nonneg_left (sub_le_sub_left huc.le b) hε
      nlinarith [hkb]

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Fourier_ProfileMergeCutoff
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The global profile lower bound supplies every noninitial merge. -/
namespace Falconer
open Set

theorem exists_superlinear_merge_above_cutoff {f : ℝ → ℝ} (hf : Continuous f)
    {c b s t m ε η : ℝ} (hcb : c < b) (hc : 0 < c) (hbm : b ≤ m)
    (hst : s < t) (hη : 0 ≤ η) (hf0 : f 0 = 0)
    (hlower : ∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x)
    (hcut : ε*m/(t-s) < b)
    (hk : intervalSecantSlope f c (b-c) < s)
    (herr : ∀ x ∈ Icc c b, -η*(b-c) ≤ intervalSecantError f c (b-c) x) :
    ∃ u ∈ Ioo 0 c, f b-f u = s*(b-u) ∧ b-c ≤ b-u ∧
      ∀ x ∈ Icc u b, f u+s*(x-u)-η*(b-u) ≤ f x := by
  have hmul := (div_lt_iff₀ (sub_pos.mpr hst)).mp hcut
  have hb := hlower b ⟨(hc.trans hcb).le,hbm⟩
  have hwhole : s*(b-0) < f b-f 0 := by rw [hf0]; nlinarith
  obtain ⟨u,hu,hs,he⟩ := exists_superlinear_merge_left hf hc hcb hη hwhole hk herr
  exact ⟨u,hu,hs,sub_le_sub_left hu.2.le b,he⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileMerging
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite recursive absorption of low-slope profile cells. -/
namespace Falconer
open Set

theorem merge_profile_cells {f : ℝ → ℝ} (hf : LipschitzWith 2 f)
    {H η m ε s t : ℝ} (hH : 0 < H) (hη : 0 < η) (hm : 0 < m)
    (hε : 0 ≤ ε) (hst : s < t) (hf0 : f 0 = 0)
    (hlower : ∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x) :
    ∀ (S : List (ℝ × ℝ)) (b : ℝ), 0 ≤ b → b ≤ m →
      ProfileCellFamily f H (η*H) η m b S →
      ∃ R : List (ℝ × ℝ), StructuredProfilePieces f (η*H) (2*η) s b R ∧
        (S.map Prod.snd).sum-η*H*(S.length : ℝ)-ε*m/(t-s) ≤ (R.map Prod.snd).sum := by
  let r := η*H
  let q := ε*m/(t-s)
  have hr : 0 < r := mul_pos hη hH
  have hq : 0 ≤ q := div_nonneg (mul_nonneg hε hm.le) (sub_pos.mpr hst).le
  suffices hmain : ∀ n : ℕ, ∀ (S : List (ℝ × ℝ)), S.length = n →
      ∀ b : ℝ, 0 ≤ b → b ≤ m → ProfileCellFamily f H r η m b S →
      ∃ R, StructuredProfilePieces f r (2*η) s b R ∧
        (S.map Prod.snd).sum-r*(S.length : ℝ)-q ≤ (R.map Prod.snd).sum by
    intro S b hb hbm hF
    exact hmain S.length S rfl b hb hbm hF
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro S hn b hb hbm hF
    rcases List.eq_nil_or_concat S with he | ⟨P,c,he⟩
    · subst S
      refine ⟨[],StructuredProfilePieces.nil _ _ _ _ _,?_⟩
      simpa using neg_nonpos.mpr hq
    · rw [he] at hn hF ⊢
      simp only [List.concat_eq_append] at hn hF ⊢
      have hc : c ∈ P++[c] := by simp
      have hcB := hF.bounds c hc
      have hcpos : 0 < c.2 := hr.trans_le hcB.2.2.1
      have hPlt : P.length < n := by
        have hh : P.length+1 = n := by simpa only [List.length_append,List.length_singleton] using hn
        omega
      have hPO := (List.pairwise_append.mp hF.ordered).1
      have hcross : ∀ d ∈ P, d.1+H ≤ c.1 := by
        intro d hd
        exact (List.pairwise_append.mp hF.ordered).2.2 d hd c (by simp)
      have hPF : ProfileCellFamily f H r η m c.1 P := by
        refine ⟨hPO,?_,?_⟩
        · intro d hd
          have hdB := hF.bounds d (by simp [hd])
          exact ⟨hdB.1,hdB.2.1,hdB.2.2.1,hdB.2.2.2.1,
            (add_le_add le_rfl hdB.2.2.2.1).trans (hcross d hd)⟩
        · intro d hd
          exact hF.linear d (by simp [hd])
      have hclin := hF.active_linear hη hH hc
      by_cases hs : s ≤ intervalSecantSlope f c.1 c.2
      · obtain ⟨R,hR,hlen⟩ := ih P.length hPlt P rfl c.1 hcB.1 (by linarith [hcB.2.1]) hPF
        refine ⟨R++[c],hR.append_interval c le_rfl hcB.2.2.2.2 hcB.2.2.1 hcB.1
          (Or.inl ⟨hs,hclin⟩) hcpos.le,?_⟩
        simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton,
          List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
        nlinarith
      · have hslow : intervalSecantSlope f c.1 c.2 < s := lt_of_not_ge hs
        let D := c.1+c.2
        have hD : 0 < D := by dsimp [D]; linarith [hcB.1]
        have hSD : ∀ d ∈ P++[c], d.1+d.2 ≤ D ∧ 0 ≤ d.2 := by
          intro d hd
          have hdB := hF.bounds d hd
          refine ⟨?_,hr.le.trans hdB.2.2.1⟩
          rcases List.mem_append.mp hd with hd | hd
          · have hdc := hcross d hd
            dsimp [D]
            linarith [hdB.2.2.2.1]
          · have hed : d = c := by simpa only [List.mem_singleton] using hd
            subst d
            exact le_rfl
        by_cases hcut : D ≤ q
        · have hsum := ordered_interval_length_le hD.le hF.actual_ordered (by
            intro d hd
            exact ⟨(hF.bounds d hd).1,hSD d hd⟩)
          refine ⟨[],StructuredProfilePieces.nil _ _ _ _ _,?_⟩
          simp only [List.map_nil,List.sum_nil]
          have hrcount : 0 ≤ r*((P++[c]).length : ℝ) := mul_nonneg hr.le (by positivity)
          linarith
        · have hwhole : s*D < f D := by
            have hlow := hlower D ⟨hD.le,hcB.2.2.2.2.trans hbm⟩
            have hqD : ε*m < D*(t-s) := (div_lt_iff₀ (sub_pos.mpr hst)).mp (lt_of_not_ge hcut)
            nlinarith
          have hc0 : 0 < c.1 := by
            by_contra hh
            have he0 : c.1 = 0 := le_antisymm (le_of_not_gt hh) hcB.1
            have hs' := (div_lt_iff₀ hcpos).mp hslow
            change (f (c.1+c.2)-f c.1)/c.2 < s at hslow
            rw [he0,hf0,zero_add] at hs'
            dsimp [D] at hwhole
            rw [he0,zero_add] at hwhole
            linarith
          have hterm : ∀ x ∈ Icc c.1 D,
              -(2*η)*(D-c.1) ≤ intervalSecantError f c.1 (D-c.1) x := by
            intro x hx
            have hh := (abs_le.mp (hclin x hx)).1
            simpa only [D,add_sub_cancel_left,neg_mul] using hh
          have hslow' : intervalSecantSlope f c.1 (D-c.1) < s := by
            simpa only [D,add_sub_cancel_left] using hslow
          obtain ⟨u,hu,hend,hw,huerr⟩ := exists_superlinear_merge_above_cutoff hf.continuous
            (show c.1 < D by dsimp [D]; linarith) hc0
            (hcB.2.2.2.2.trans hbm) hst (by positivity : 0 ≤ 2*η) hf0 hlower
            (lt_of_not_ge hcut) hslow' hterm
          let Q := clipProfilePrefix u r (P++[c])
          have hQF : ProfileCellFamily f H r η m u Q := hF.clip
          have hQlt : Q.length < n := by
            rw [← hn]
            exact clipProfilePrefix_length_lt hr (fun d hd => (hF.bounds d hd).2.2.1)
              ⟨c,hc,hu.2.le⟩
          obtain ⟨R,hR,hlen⟩ := ih Q.length hQlt Q rfl u hu.1.le
            (hu.2.le.trans (by linarith [hcB.2.1])) hQF
          have hdu : 0 < D-u := by dsimp [D]; linarith [hu.2]
          have heSlope : intervalSecantSlope f u (D-u) = s := by
            unfold intervalSecantSlope
            rw [show u+(D-u) = D by ring]
            exact (div_eq_iff hdu.ne').2 hend
          have hpiece : ∀ x ∈ Icc u (u+(D-u)),
              -(2*η)*(D-u) ≤ intervalSecantError f u (D-u) x := by
            intro x hx
            rw [show u+(D-u) = D by ring] at hx
            have hh := huerr x hx
            unfold intervalSecantError
            rw [heSlope]
            linarith
          have hnew := hR.append_interval (b := b) (u,D-u) le_rfl
            (by dsimp; linarith [hcB.2.2.2.2])
            (by dsimp [D] at hw; dsimp; linarith [hcB.2.2.1]) hu.1.le
            (Or.inr ⟨heSlope,hpiece⟩) hdu.le
          refine ⟨R++[(u,D-u)],hnew,?_⟩
          have hloss := clipProfilePrefix_loss hr.le (hu.2.le.trans (by dsimp [D]; linarith))
            hF.actual_ordered hSD
          have hcount : ((Q.length : ℕ) : ℝ)+1 ≤ ((P++[c]).length : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt (show Q.length < (P++[c]).length by simpa [hn] using hQlt)
          have hcost := mul_le_mul_of_nonneg_left hcount hr.le
          simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton]
          change (P++[c] |>.map Prod.snd).sum ≤ (Q.map Prod.snd).sum+(D-u)+r at hloss
          simp only [List.map_append,List.map_singleton,List.sum_append,List.sum_singleton] at hloss
          nlinarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileDecomposition
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Quantitative slope decomposition of the profile, with a uniform minimum
interval length and explicit uncovered-length bound. -/
namespace Falconer
open Set

private theorem equal_width_sum (H : ℝ) (S : List (ℝ × ℝ))
    (hw : ∀ c ∈ S, c.2 = H) : (S.map Prod.snd).sum = H*(S.length : ℝ) := by
  induction S with
  | nil => simp
  | cons c S ih =>
    have ht := ih (fun d hd => hw d (by simp [hd]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    rw [hw c (by simp),ht]
    ring

theorem quantitative_profile_slope_decomposition {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (f : ℝ → ℝ), LipschitzWith 2 f →
      ∀ (m ε s t : ℝ), 0 < m → 0 ≤ ε → s < t → f 0 = 0 →
      (∀ x ∈ Icc 0 m, t*x-ε*m ≤ f x) →
      ∃ R : List (ℝ × ℝ), StructuredProfilePieces f (τ*m) (2*η) s m R ∧
        m*(1-η^2-η-ε/(t-s)) ≤ (R.map Prod.snd).sum := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_uniform_linear_decomposition (sq_pos_of_pos hη)
  refine ⟨η*τ,mul_pos hη hτ,?_⟩
  intro f hf m ε s t hm hε hst hf0 hlower
  obtain ⟨S,⟨H,hH,hHm,hHlow,hwidth⟩,hord,hcover,hcells⟩ := ht f hf 0 m hm
  have hF : ProfileCellFamily f H (η*H) η m m S := by
    constructor
    · apply hord.imp_of_mem
      intro c d hc _ hcd
      simpa only [hwidth c hc] using hcd
    · intro c hc
      have hb := hcells c hc
      have he := hwidth c hc
      refine ⟨hb.1,?_,?_,he.le,?_⟩
      · simpa only [zero_add,he] using hb.2.1
      · rw [he]
        nlinarith [mul_le_mul_of_nonneg_right hη1 hH.le]
      · simpa only [zero_add] using hb.2.1
    · intro c hc x hx
      have he := hwidth c hc
      simpa only [he] using (hcells c hc).2.2.2 x (by simpa only [he] using hx)
  obtain ⟨R,hR,hlen⟩ := merge_profile_cells hf hH hη hm hε hst hf0 hlower S m hm.le le_rfl hF
  have hsum := equal_width_sum H S hwidth
  have hsumBound : (S.map Prod.snd).sum ≤ m := by
    simpa only [sub_zero] using ordered_interval_length_le hm.le hord (by
      intro c hc
      have hb := hcells c hc
      exact ⟨hb.1,by simpa only [zero_add] using hb.2.1,by rw [hwidth c hc]; exact hH.le⟩)
  have hcost : η*H*(S.length : ℝ) ≤ η*m := by
    calc
      _ = η*(S.map Prod.snd).sum := by rw [hsum]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsumBound hη.le
  refine ⟨R,⟨hR.ordered,?_,hR.alternatives⟩,?_⟩
  · intro c hc
    have hb := hR.bounds c hc
    refine ⟨hb.1,hb.2.1,?_⟩
    have he := mul_le_mul_of_nonneg_left hHlow hη.le
    nlinarith [hb.2.2]
  · have he : m*(1-η^2-η-ε/(t-s)) = m*(1-η^2)-η*m-ε*m/(t-s) := by ring
    rw [he]
    linarith

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileBetweenNodes
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Propagating the discrete profile bounds across each actual interpolation block. -/
namespace Falconer.Regularization

theorem finiteRampProfile_affine_on_block (d c : ℕ → ℝ) {K i : ℕ}
    (hd : Antitone d) (hi : i < K) {u : ℝ} (hu : d (i+1) ≤ u ∧ u ≤ d i) :
    finiteRampProfile d c K u = finiteRampProfile d c K (d (i+1))+c i*(u-d (i+1)) := by
  classical
  have hr (j : ℕ) : intervalRamp (d (j+1)) (d j) u-
      intervalRamp (d (j+1)) (d j) (d (i+1)) =
      if j = i then u-d (i+1) else 0 := by
    unfold intervalRamp
    by_cases hj : j = i
    · subst j
      rw [ite_eq_left rfl,min_eq_left hu.2,min_eq_right hu.1,
        min_eq_left (hd (Nat.le_succ i)),min_self]
      ring
    · rw [ite_eq_right hj]
      rcases lt_or_gt_of_ne hj with hj | hj
      · have h1 := hu.2.trans (hd (Nat.succ_le_of_lt hj))
        have h2 := hu.2.trans (hd (Nat.le_of_lt hj))
        have h3 := hd (show j+1 ≤ i+1 by omega)
        have h4 := hd (show j ≤ i+1 by omega)
        rw [min_eq_left h2,min_eq_left h1,min_eq_left h4,min_eq_left h3]
        ring
      · have h1 := (hd (show i+1 ≤ j by omega)).trans hu.1
        have h2 := (hd (show i+1 ≤ j+1 by omega)).trans hu.1
        have h3 := hd (show i+1 ≤ j by omega)
        have h4 := hd (show i+1 ≤ j+1 by omega)
        rw [min_eq_right h1,min_eq_right h2,min_eq_right h3,min_eq_right h4]
        ring
  have he : finiteRampProfile d c K u-finiteRampProfile d c K (d (i+1)) =
      ∑ j ∈ Finset.range K, c j*(intervalRamp (d (j+1)) (d j) u-
        intervalRamp (d (j+1)) (d j) (d (i+1))) := by
    simp only [finiteRampProfile,← Finset.sum_sub_distrib,mul_sub]
  simp_rw [hr] at he
  rw [Finset.sum_eq_single i (fun j _ hji => by simp [hji])
    (fun hni => False.elim (hni (Finset.mem_range.mpr hi)))] at he
  simp only [ite_true, if_true] at he
  linarith

theorem exists_profile_block (d : ℕ → ℝ) (_hd : Antitone d) (K : ℕ) {u : ℝ}
    (hu : d K ≤ u ∧ u ≤ d 0) :
    u = d 0 ∨ ∃ i < K, d (i+1) ≤ u ∧ u ≤ d i := by
  induction K with
  | zero => exact Or.inl (le_antisymm hu.2 hu.1)
  | succ K ih =>
    by_cases hlast : u ≤ d K
    · exact Or.inr ⟨K,Nat.lt_succ_self K,hu.1,hlast⟩
    · rcases ih ⟨(le_of_not_ge hlast),hu.2⟩ with he | ⟨i,hi,hui⟩
      · exact Or.inl he
      · exact Or.inr ⟨i,Nat.lt_succ_of_lt hi,hui⟩

theorem finiteRampProfile_lower_between_nodes (d c : ℕ → ℝ) (K : ℕ)
    (hd : Antitone d) {t A u : ℝ}
    (hnodes : ∀ i ≤ K, t*d i-A ≤ finiteRampProfile d c K (d i))
    (hu : d K ≤ u ∧ u ≤ d 0) : t*u-A ≤ finiteRampProfile d c K u := by
  rcases exists_profile_block d hd K hu with rfl | ⟨i,hi,hui⟩
  · exact hnodes 0 (Nat.zero_le _)
  · have hlow := hnodes (i+1) hi
    have hhigh := hnodes i hi.le
    have hf := finiteRampProfile_affine_on_block d c hd hi hui
    by_cases hs : t ≤ c i
    · have hm := mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hui.1)
      nlinarith
    · have hf' := finiteRampProfile_affine_on_block d c hd hi
        (show d (i+1) ≤ d i ∧ d i ≤ d i from ⟨hd (Nat.le_succ i),le_rfl⟩)
      have hm := mul_nonneg (sub_nonneg.mpr (le_of_not_ge hs)) (sub_nonneg.mpr hui.2)
      nlinarith

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileLowerBound
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Convert the actual finite block-count bounds into a lower bound for the
whole normalized branching profile, including between the block depths. -/
namespace Falconer.Regularization
variable {d : ℕ}

theorem regularizedProfile_lower_from_ratios {N : ℕ} (hN : 0 < N)
    {L : Finset (CellPath d)} (hL : L ⊆ cubePaths d N) (F : CellPath d → List ℕ)
    {B : ℕ} (hB : 0 < B) (p : CellPath d) {t A : ℝ}
    (hbound : ∀ i ≤ N/B+1,
      (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
        (2 : ℝ)^(A-t*(blockDepth N B i : ℝ)))
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    t*x-A/(N : ℝ) ≤ regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hnodes : ∀ i ≤ N/B+1, (t/(N : ℝ))*(blockDepth N B i : ℝ)-A/(N : ℝ) ≤
      regularizedProfile L F N B (N/B+1) p (blockDepth N B i) := by
    intro i hi
    have hb := regularizedProfile_lower_of_ratio_bound hN hL F hB p hi (hbound i hi)
    rw [show (t/(N : ℝ))*(blockDepth N B i : ℝ)-A/(N : ℝ) =
        (t*(blockDepth N B i : ℝ)-A)/(N : ℝ) by ring]
    apply (div_le_iff₀ hNR).2
    nlinarith
  have hbetween : (blockDepth N B (N/B+1) : ℝ) ≤ (N : ℝ)*x ∧
      (N : ℝ)*x ≤ (blockDepth N B 0 : ℝ) := by
    simp only [blockDepth_terminal N hB,Nat.cast_zero,blockDepth,Nat.zero_mul,Nat.sub_zero]
    constructor
    · exact mul_nonneg hNR.le hx.1
    · nlinarith [mul_le_mul_of_nonneg_left hx.2 hNR.le]
  have hp := finiteRampProfile_lower_between_nodes
    (fun i => (blockDepth N B i : ℝ)) (fun i => blockSlope L F N B i p) (N/B+1)
    (fun _ _ h => Nat.cast_le.mpr (blockDepth_antitone N B h)) hnodes hbetween
  have he : (t/(N : ℝ))*((N : ℝ)*x)-A/(N : ℝ) = t*x-A/(N : ℝ) := by
    field_simp
  change t*x-A/(N : ℝ) ≤ finiteRampProfile _ _ _ _
  rw [← he]
  exact hp

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_ProfileScaleSelection
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Select structured scale intervals for the actual regularized planar
branching profile from its finite prefix-count bounds. -/
namespace Falconer.Regularization

theorem planar_profile_scale_selection {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1) :
    ∃ τ : ℝ, 0 < τ ∧ ∀ (N : ℕ), 0 < N → ∀ L : Finset (CellPath 2),
      L ⊆ cubePaths 2 N → ∀ (F : CellPath 2 → List ℕ) (B : ℕ), 0 < B →
      ∀ (p : CellPath 2) (ε s t : ℝ), 0 ≤ ε → s < t →
      (∀ i ≤ N/B+1,
        (blockProduct L F N B i p : ℝ)/(blockProduct L F N B (N/B+1) p : ℝ) ≤
          (2 : ℝ)^(ε*(N : ℝ)-t*(blockDepth N B i : ℝ))) →
      ∃ R : List (ℝ × ℝ),
        StructuredProfilePieces (fun x => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x))
          τ (2*η) s 1 R ∧
        1-η^2-η-ε/(t-s) ≤ (R.map Prod.snd).sum := by
  obtain ⟨τ,hτ,ht⟩ := quantitative_profile_slope_decomposition hη hη1
  refine ⟨τ,hτ,?_⟩
  intro N hN L hL F B hB p ε s t hε hst hcounts
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hlo : ∀ x ∈ Set.Icc (0 : ℝ) 1, t*x-ε*1 ≤
      regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x) := by
    intro x hx
    have hh := regularizedProfile_lower_from_ratios hN hL F hB p hcounts hx
    simpa only [mul_div_cancel_right₀ ε hNR,mul_one] using hh
  have hz : (fun x : ℝ => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x)) 0 = 0 := by
    simp [regularizedProfile_zero]
  have hd := ht (fun x => regularizedProfile L F N B (N/B+1) p ((N : ℝ)*x))
    (planarProfile_lipschitz hN hL F B (N/B+1) p) 1 ε s t (by norm_num) hε hst hz hlo
  simpa only [mul_one,one_mul] using hd

end Falconer.Regularization

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_UniformProfileGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform gain for the actual regularized planar profile, assuming only its
finite branching-count lower growth. All decomposition and recursion parameters
are chosen before the configuration and the depth. -/
namespace Falconer
open Set Regularization

theorem uniform_profile_endpoint_gain {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) →
    (2:ℝ)^(3*(m+1))*((2*B+1:ℕ):ℝ)^(m+1) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) ∧
    ∀ (f : CellPath 2 → List ℕ) (p : CellPath 2) (Q : DyadicCube 2), Q.side = 1 →
      (∀ i ≤ m+1,
        (blockProduct L (blockLabel L (m*B) B f (m+1)) (m*B) B i p:ℝ)/
          (blockProduct L (blockLabel L (m*B) B f (m+1)) (m*B) B (m+1) p:ℝ) ≤
        (2:ℝ)^(lam*(m*B:ℕ)-t*(blockDepth (m*B) B i:ℝ))) →
      ProfileEndpointBound (m*B) B (m+1) L f p Q m 0 s ((2:ℝ)^(lam*(m*B:ℕ)))
        ((2:ℝ)^((s+ζ)*(m*B:ℕ))) := by
  obtain ⟨eg,η,Ng,heg,heg1,hη,hNg,hendpoint⟩ := rounded_profile_endpoint_gain hκ hκ1
  obtain ⟨α,hα,hακ,hαη,hαe⟩ := exists_profile_gain_accuracy hκ hη heg
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨τ,hτ,hselect⟩ := planar_profile_scale_selection hα hα1
  let J := Nat.ceil (1/τ)
  obtain ⟨β,hβ,hβα,hβη,hβe⟩ := exists_profile_gain_budget hα hκ hη heg hτ J
  obtain ⟨B,hB,hBeven,lam,hlam,N0,hN0,hbudget⟩ := exists_profile_application_budget hβ J
  obtain ⟨M,hM,hgrid⟩ := exists_incidence_profile_grid_threshold hα hτ hκ Ng N0
  refine ⟨B,hB,hBeven,lam,η*κ/2,hlam,by positivity,M,hM,?_⟩
  intro m hm L hL
  have hm0 : 0 < m := hM.trans_le hm
  have hNmin := (hgrid m hm B hB).1
  have hentry := (hbudget m hm0 hNmin).2.2.2.2
  rw [Nat.mul_comm B m] at hentry
  refine ⟨hentry,?_⟩
  intro f p Q hQ hcounts
  let N := m*B
  let K := m+1
  let F := blockLabel L N B f K
  let g := fun x => regularizedProfile L F N B K p ((N:ℝ)*x)
  let H : ℝ := (4*(N+2)+11:ℕ)
  let G := (2:ℝ)^(3*K)*((2*B+1:ℕ):ℝ)^K
  let W := profileBudgetSequence H G ((2:ℝ)^(lam*(N:ℝ)))
  have hN : 0 < N := Nat.mul_pos hm0 hB
  have hNR : (0:ℝ) < N := Nat.cast_pos.mpr hN
  obtain ⟨hNmin,hmesh,herror,hslack,hround,hlarge⟩ := hgrid m hm B hB
  have hb := hbudget m hm0 hNmin
  dsimp only at hb
  rw [Nat.mul_comm B m] at hb
  change (∀ j ≤ 2*J+1, W j ≤ (2:ℝ)^(β*(N:ℝ))) ∧
    (∀ j ≤ 2*J, ∀ A : ℝ, profileGeometryConstant K B (W j) A ≤ (2:ℝ)^((4*β)*(N:ℝ)+A)) ∧
    640*((N:ℝ)+3) ≤ (2:ℝ)^(β*(N:ℝ)) ∧ (43264*H^4)^(2*J) ≤ (2:ℝ)^(β*(N:ℝ)) ∧
    G ≤ (2:ℝ)^((lam/4)*(N:ℝ)) at hb
  have hlamβ : lam ≤ β := by
    have hh := (Real.rpow_le_rpow_left_iff (by norm_num : (1:ℝ) < 2)).mp (hb.1 0 (by omega))
    change lam*(N:ℝ) ≤ β*(N:ℝ) at hh
    exact (mul_le_mul_iff_left₀ hNR).mp hh
  have hK : N/B+1 = K := by dsimp [N,K]; rw [Nat.mul_div_cancel m hB]
  have hcounts' : ∀ i ≤ N/B+1,
      (blockProduct L F N B i p:ℝ)/(blockProduct L F N B (N/B+1) p:ℝ) ≤
        (2:ℝ)^(lam*(N:ℝ)-t*(blockDepth N B i:ℝ)) := by
    rw [hK]
    exact hcounts
  obtain ⟨S,hS,hcover⟩ := hselect N hN L hL F B hB p lam (s+κ) t hlam.le (by linarith) hcounts'
  rw [hK] at hS
  change StructuredProfilePieces g τ (2*α) (s+κ) 1 S at hS
  let χ := α^2+α+lam/(t-(s+κ))
  have hcover' : 1-χ ≤ (S.map Prod.snd).sum := by
    dsimp [χ]
    linarith only [hcover]
  have hgrowth : t-lam ≤ g 1 := by
    have hh := regularizedProfile_lower_from_ratios hN hL F hB p hcounts'
      (x := 1) (show (1:ℝ) ∈ Icc 0 1 by simp)
    rw [hK] at hh
    simpa only [g,mul_one,mul_div_cancel_right₀ lam hNR.ne'] using hh
  have hcount : S.length ≤ J := by
    have hh := ordered_interval_count_bound (by norm_num : (0:ℝ) ≤ 1) hS.ordered
      (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1,hτ.le.trans (hS.bounds c hc).2.2⟩)
      (fun c hc => (hS.bounds c hc).2.2)
    have hh' : (S.length:ℝ) ≤ 1/τ := by
      apply (le_div_iff₀ hτ).2
      simpa only [sub_zero,mul_comm] using hh
    exact Nat.cast_le.mp (hh'.trans (Nat.le_ceil _))
  have hround' : (2/(m:ℝ))*(S.length:ℝ) ≤ α := by
    have hcountR : (S.length:ℝ) ≤ 1/τ := by
      have hh := ordered_interval_count_bound (by norm_num : (0:ℝ) ≤ 1) hS.ordered
        (fun c hc => ⟨(hS.bounds c hc).1,(hS.bounds c hc).2.1,hτ.le.trans (hS.bounds c hc).2.2⟩)
        (fun c hc => (hS.bounds c hc).2.2)
      apply (le_div_iff₀ hτ).2
      simpa only [sub_zero,mul_comm] using hh
    calc
      _ ≤ (2/(m:ℝ))*(1/τ) := mul_le_mul_of_nonneg_left hcountR (by positivity)
      _ = 2/((m:ℝ)*τ) := by ring
      _ ≤ α := hround
  obtain ⟨hweak,hgain⟩ := profile_gain_parameters_close hκ hκ1 hα hακ hαη
    hβα hβη hlam.le hlamβ (show s ≤ 1 by linarith) ht
  exact hendpoint m B hm0 hB hBeven L hL f p Q hQ s t (2*α) τ β lam χ α (η*κ/2)
    hs hs1 (by positivity) hτ hβ hlam J S hS hgrowth hcover' ht hweak hmesh
    (by convert herror using 1; ring) hslack hround' (by linarith) hcount hlarge hβe
    (by nlinarith only [hαe]) (by convert hgain using 1; ring)
    ⟨hb.2.1,hb.2.2.1,hb.2.2.2.1⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Recursion_InitialProfileClass
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial class inherits its lower profile from the actual leaf prefix
counts. The label-selection loss is explicit and paid only once. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem block_profile_ratios_from_prefix {N B : ℕ} (hB : 0 < B)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N)
    (f : CellPath 2 → List ℕ) {p : CellPath 2} (hp : p ∈ L)
    {A D t : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hmass : (L.card:ℝ) ≤ D*((classLeaves L (blockLabel L N B f (N/B+1))
      (blockLabel L N B f (N/B+1) p)).card:ℝ))
    (hprefix : ∀ k ≤ N, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ A*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ)) :
    ∀ i ≤ N/B+1,
      (blockProduct L (blockLabel L N B f (N/B+1)) N B i p:ℝ)/
        (blockProduct L (blockLabel L N B f (N/B+1)) N B (N/B+1) p:ℝ) ≤
      ((2:ℝ)^(N/B+1)*D*A)*(2:ℝ)^(-t*(blockDepth N B i:ℝ)) := by
  intro i hi
  let K := N/B+1
  let F := blockLabel L N B f K
  let C := classLeaves L F (F p)
  have hpC : p ∈ C := by simp [C,classLeaves,hp]
  have hCsub : C ⊆ L := Finset.filter_subset _ _
  have hc := blockClass_leaf_count hL B f K p hi (Finset.mem_image.mpr ⟨p,hpC,rfl⟩)
  have hr := blockClass_root_count hL hB f hp
  apply (div_le_iff₀ (Nat.cast_pos.mpr (blockProduct_pos L F N B K p))).2
  calc
    (blockProduct L F N B i p:ℝ) ≤ ((prefixFiber C (blockDepth N B i)
        (p.take (blockDepth N B i))).card:ℝ) := Nat.cast_le.mpr hc.1
    _ ≤ ((prefixFiber L (blockDepth N B i) (p.take (blockDepth N B i))).card:ℝ) :=
      Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset_filter _ hCsub))
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(L.card:ℝ) :=
      hprefix _ (Nat.sub_le N _) _
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(D*(C.card:ℝ)) := by gcongr
    _ ≤ A*(2:ℝ)^(-t*(blockDepth N B i:ℝ))*(D*((2:ℝ)^K*
        (blockProduct L F N B K p:ℝ))) := by
      gcongr
      exact_mod_cast hr.2
    _ = _ := by ring

theorem exists_initial_profile_class {N B : ℕ} (hB : 0 < B)
    {L : Finset (CellPath 2)} (hL : L ⊆ cubePaths 2 N) (hLne : L.Nonempty)
    {A t lam : ℝ} (hA : 0 ≤ A)
    (hprefix : ∀ k ≤ N, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ A*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ))
    (hcost : (2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*A ≤ (2:ℝ)^(lam*(N:ℝ))) :
    ∃ p ∈ L,
      (L.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^(N/B+1)*
        ((classLeaves L (blockLabel L N B (fun _ => []) (N/B+1))
          (blockLabel L N B (fun _ => []) (N/B+1) p)).card:ℝ) ∧
      ∀ i ≤ N/B+1,
        (blockProduct L (blockLabel L N B (fun _ => []) (N/B+1)) N B i p:ℝ)/
          (blockProduct L (blockLabel L N B (fun _ => []) (N/B+1)) N B (N/B+1) p:ℝ) ≤
        (2:ℝ)^(lam*(N:ℝ)-t*(blockDepth N B i:ℝ)) := by
  obtain ⟨p,hp,hmass⟩ := exists_large_planar_block_class hL hLne B (N/B+1)
  have hmassR : (L.card:ℝ) ≤ ((2*B+1:ℕ):ℝ)^(N/B+1)*
      ((classLeaves L (blockLabel L N B (fun _ => []) (N/B+1))
        (blockLabel L N B (fun _ => []) (N/B+1) p)).card:ℝ) := by exact_mod_cast hmass
  refine ⟨p,hp,hmassR,?_⟩
  have hh := block_profile_ratios_from_prefix hB hL (fun _ => []) hp hA (by positivity) hmassR hprefix
  intro i hi
  calc
    _ ≤ ((2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*A)*
        (2:ℝ)^(-t*(blockDepth N B i:ℝ)) := hh i hi
    _ ≤ (2:ℝ)^(lam*(N:ℝ))*(2:ℝ)^(-t*(blockDepth N B i:ℝ)) :=
      mul_le_mul_of_nonneg_right hcost (by positivity)
    _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafIncidenceGain
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Incidence gain on the actual terminal centers of a large regularized leaf
class, deduced from the original leaf-prefix counts. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem uniform_leaf_incidence_gain {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ L : Finset (CellPath 2), L ⊆ cubePaths 2 (m*B) → L.Nonempty →
      (∀ k ≤ m*B, ∀ q : CellPath 2,
        ((prefixFiber L k q).card:ℝ) ≤
          (2:ℝ)^((lam/4)*(m*B:ℕ))*(2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ)) →
    ∀ Q : DyadicCube 2, Q.side = 1 →
    ∃ p ∈ L,
      let C := classLeaves L (blockLabel L (m*B) B (fun _ => []) (m+1))
        (blockLabel L (m*B) B (fun _ => []) (m+1) p);
      C.Nonempty ∧ (L.card:ℝ) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ))*(C.card:ℝ) ∧
      ∀ a : ℝ, 0 < a → ∀ V : Space 2 → Finset (Space 2),
        QuarterPencilData (1/(2:ℝ)^(m*B+2)) s ((2:ℝ)^(lam*(m*B:ℕ))) a
          (quarterEndpointSet Q C 0 (m*B) []) V →
        (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤
          (((quarterEndpointSet Q C 0 (m*B) []).biUnion V).card:ℝ)/a := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hgain⟩ := uniform_profile_endpoint_gain hκ hκ1 hs hs1 ht
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro m hm L hL hLne hprefix Q hQ
  have hm0 : 0 < m := hM.trans_le hm
  let N := m*B
  let K := m+1
  have hK : N/B+1 = K := by dsimp [N,K]; rw [Nat.mul_div_cancel m hB]
  obtain ⟨hlabel,hprofile⟩ := hgain m hm L hL
  have hN0 : (0:ℝ) ≤ N := Nat.cast_nonneg N
  have hsmall : (2:ℝ)^(lam/4*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/4 ≤ lam) hN0)
  have hbase : (2:ℝ)^K*((2*B+1:ℕ):ℝ)^K ≤ (2:ℝ)^(lam/4*(N:ℝ)) := by
    apply le_trans _ hlabel
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply pow_le_pow_right₀ (by norm_num)
    dsimp [K]
    omega
  have hcost : (2:ℝ)^(N/B+1)*((2*B+1:ℕ):ℝ)^(N/B+1)*
      (2:ℝ)^((lam/4)*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) := by
    rw [hK]
    calc
      _ ≤ (2:ℝ)^((lam/4)*(N:ℝ))*(2:ℝ)^((lam/4)*(N:ℝ)) :=
        mul_le_mul_of_nonneg_right hbase (by positivity)
      _ = (2:ℝ)^((lam/2)*(N:ℝ)) := by
        rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hlam] : lam/2 ≤ lam) hN0)
  obtain ⟨p,hp,hmass,hcounts⟩ := exists_initial_profile_class hB hL hLne (by positivity) hprefix hcost
  rw [hK] at hmass hcounts
  let C := classLeaves L (blockLabel L N B (fun _ => []) K) (blockLabel L N B (fun _ => []) K p)
  have hpC : p ∈ C := by simp [C,classLeaves,hp]
  have hlabel' : ((2*B+1:ℕ):ℝ)^K ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    apply le_trans _ hbase
    exact le_mul_of_one_le_left (by positivity) (one_le_pow₀ (by norm_num))
  refine ⟨p,hp,⟨p,hpC⟩,hmass.trans (mul_le_mul_of_nonneg_right hlabel' (Nat.cast_nonneg _)),?_⟩
  intro a ha V hV
  have hb := hprofile (fun _ => []) p Q hQ hcounts
  have hzero : blockDepth N B m = 0 := by simp [blockDepth,N]
  have hroot : blockDepth N B 0 = N := by simp [blockDepth]
  have hW : 1 ≤ (2:ℝ)^(lam*(N:ℝ)) := Real.one_le_rpow (by norm_num) (by positivity)
  have hsub : C ⊆ prefixFiber C 0 [] := by simp [prefixFiber_zero]
  have hmassSelf : ((prefixFiber C 0 []).card:ℝ) ≤ (2:ℝ)^(lam*(N:ℝ))*(C.card:ℝ) := by
    rw [prefixFiber_zero]
    exact le_mul_of_one_le_left (Nat.cast_nonneg _) hW
  have hp0 : [] ∈ C.image (List.take (blockDepth N B m)) := by
    rw [hzero]
    exact Finset.mem_image.mpr ⟨p,hpC,by simp⟩
  have hv : QuarterPencilData (1/(2:ℝ)^(blockDepth N B 0-blockDepth N B m+2)) s
      ((2:ℝ)^(lam*(N:ℝ))) a (quarterEndpointSet Q C (blockDepth N B m) (blockDepth N B 0) []) V := by
    simpa only [hzero,hroot,Nat.sub_zero,N] using hV
  have hh := hb L (fun _ => []) p 0 [] hL hsub hmassSelf (Nat.zero_le _) [] hp0 a ha V hv
  simpa only [hzero,hroot,N] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafCenterIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original incidences survive moving points to their assigned leaf centers.
The half-slope chart leaves a fixed margin in the terminal tube width. -/
namespace Falconer
open Set Regularization

theorem cube_center_incident {δ : ℝ} (hδ : 0 ≤ δ) (Q : DyadicCube 2)
    {x l : Space 2} (hx : x ∈ Q.carrier) (hl : |l 0| ≤ 1/2)
    (hi : TubeIncident δ x l) (hsmall : 16*δ ≤ Q.side) :
    TubeIncident Q.side Q.center l := by
  have hside : 0 ≤ Q.side := (by positivity : 0 ≤ 16*δ).trans hsmall
  have h0 := Q.center_coordinate_bound hx 0
  have h1 := Q.center_coordinate_bound hx 1
  have hres := tube_residual_le hδ (hl.trans (by norm_num)) hi
  have hm : |l 0*(x 0-Q.center 0)| ≤ Q.side/4 := by
    rw [abs_mul]
    calc
      _ ≤ (1/2)*(Q.side/2) := mul_le_mul hl h0 (abs_nonneg _) (by norm_num)
      _ = _ := by ring
  have hres' : |Q.center 1-l 0*Q.center 0-l 1| ≤ Q.side := by
    calc
      _ = |(x 1-l 0*x 0-l 1)+(Q.center 1-x 1)+l 0*(x 0-Q.center 0)| := by congr 1; ring
      _ ≤ |(x 1-l 0*x 0-l 1)+(Q.center 1-x 1)|+|l 0*(x 0-Q.center 0)| := abs_add_le _ _
      _ ≤ (|x 1-l 0*x 0-l 1|+|Q.center 1-x 1|)+|l 0*(x 0-Q.center 0)| :=
        add_le_add (abs_add_le _ _) le_rfl
      _ ≤ 2*δ+Q.side/2+Q.side/4 := by rw [abs_sub_comm (Q.center 1)]; gcongr
      _ ≤ _ := by linarith
  have hden : 0 < Real.sqrt (1+(l 0)^2) := Real.sqrt_pos.mpr (by positivity)
  have hden1 : 1 ≤ Real.sqrt (1+(l 0)^2) := by
    exact (Real.one_le_sqrt).mpr (by nlinarith only [sq_nonneg (l 0)])
  apply (div_le_iff₀ hden).2
  exact hres'.trans (le_mul_of_one_le_right hside hden1)

theorem root_leaf_quarter_incident {N : ℕ} (Q : DyadicCube 2) (hQ : Q.side = 1)
    {r : CellPath 2} (hr : r ∈ cubePaths 2 N) {δ : ℝ} (hδ : 0 ≤ δ)
    {x l : Space 2} (hx : x ∈ (Q.descendant r).carrier) (hl : |l 0| ≤ 1/2)
    (hi : TubeIncident δ x l) (hsmall : 16*δ ≤ 1/(2:ℝ)^N) :
    TubeIncident (1/(2:ℝ)^(N+2)) (quarterEndpointPoint Q 0 [] r)
      (localCellLine 4 (Q.center 0) (Q.center 1) l) := by
  have hside : (Q.descendant r).side = 1/(2:ℝ)^N := by
    rw [Q.descendant_side,(mem_cubePaths _ _ _).mp hr,hQ]
  have hc := cube_center_incident hδ (Q.descendant r) hx hl hi (hside.symm ▸ hsmall)
  have hh := localCellLine_incident (by norm_num : (0:ℝ) < 4)
    (Q.center 0) (Q.center 1) (Q.descendant r).center l hc
  have hwidth : (Q.descendant r).side/4 = 1/(2:ℝ)^(N+2) := by
    rw [hside,pow_add]
    norm_num
    ring
  rw [hwidth] at hh
  simpa only [quarterEndpointPoint,pow_zero,div_one,DyadicCube.descendant] using hh

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafPencilTransport
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Transport the original pencils to the selected terminal centers by one
common line map. Their union cardinality cannot increase. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem quarterEndpointSet_root {N : ℕ} (Q : DyadicCube 2)
    {C : Finset (CellPath 2)} (hC : C ⊆ cubePaths 2 N) :
    quarterEndpointSet Q C 0 N [] = C.image (quarterEndpointPoint Q 0 []) := by
  have he : C.image (List.take N) = C := by
    ext p
    constructor
    · rintro hp
      obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
      have hlen := (mem_cubePaths _ _ _).mp (hC hq)
      simpa only [← hlen,List.take_length] using hq
    · intro hp
      exact Finset.mem_image.mpr ⟨p,hp,by rw [← (mem_cubePaths _ _ _).mp (hC hp),List.take_length]⟩
  rw [quarterEndpointSet,prefixChildren,prefixFiber_zero,he]

theorem transport_pencils_to_leaf_centers {N : ℕ} (Q : DyadicCube 2)
    (hQ : Q.side = 1) (hcenter : Q.center = 0)
    (P : Finset (Space 2)) (l : Space 2 → CellPath 2)
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    {C : Finset (CellPath 2)} (hCP : C ⊆ P.image l)
    {δ s K W a b : ℝ} (hδ : 0 < δ) (hs : 0 ≤ s) (hK : 1 ≤ K)
    (hsmall : 16*δ ≤ 1/(2:ℝ)^N) (hsize : b ≤ W*a) (hbudget : K*4^s ≤ W)
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^N) (V x) ∧
      NormalizedFiniteBallBound δ s K (V x) ∧
      ∀ u ∈ V x, |u 0| ≤ 1/2 ∧ TubeIncident δ x u) :
    ∃ T : Space 2 → Finset (Space 2),
      QuarterPencilData (1/(2:ℝ)^(N+2)) s W a (quarterEndpointSet Q C 0 N []) T ∧
      (((quarterEndpointSet Q C 0 N []).biUnion T).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  have hCN : C ⊆ cubePaths 2 N := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hCP hr)
    exact (hleaf x hx).1
  let F := fun x => quarterEndpointPoint Q 0 [] (l x)
  let Z := quarterEndpointSet Q C 0 N []
  have hZP : Z ⊆ P.image F := by
    dsimp [Z]
    rw [quarterEndpointSet_root Q hCN]
    intro z hz
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp (hCP hr)
    exact Finset.mem_image.mpr ⟨x,hx,rfl⟩
  let q := Function.invFunOn F (P : Set (Space 2))
  have hq (z : Space 2) (hz : z ∈ Z) : q z ∈ P ∧ F (q z) = z :=
    Function.invFunOn_pos (Finset.mem_image.mp (hZP hz))
  let A := localCellLine 4 0 0
  let T := fun z => (V (q z)).image A
  have hwidth : (1/(2:ℝ)^N)/4 = 1/(2:ℝ)^(N+2) := by rw [pow_add]; norm_num; ring
  have hδwidth : δ/4 ≤ 1/(2:ℝ)^(N+2) := by rw [← hwidth]; linarith
  refine ⟨T,?_,?_⟩
  · intro z hz
    obtain ⟨hqP,hqz⟩ := hq z hz
    obtain ⟨hlo,hhi,hchart,hsep,hball,hinc⟩ := hV (q z) hqP
    have hcard : ((T z).card:ℝ) = ((V (q z)).card:ℝ) := by
      dsimp [T,A]
      rw [Finset.card_image_of_injective _ (localCellLine_injective (by norm_num) 0 0)]
    refine ⟨hlo.trans_eq hcard.symm,hcard.trans_le (hhi.trans hsize),
      localCellLine_four_chart _ hchart,?_,?_,?_⟩
    · rw [← hwidth]
      exact localCellLine_four_separated _ hsep
    · have hb := localCellLine_four_regular hδ hs hK _ hball
      intro w r hr hr1
      have hh := hb w r (hδwidth.trans hr) hr1
      exact hh.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbudget (Real.rpow_nonneg ((by positivity : (0:ℝ) ≤ δ/4).trans (hδwidth.trans hr)) _)) (Nat.cast_nonneg _))
    · intro u hu
      obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
      have hv' := hinc v hv
      refine ⟨hv'.1,?_⟩
      have hh := root_leaf_quarter_incident Q hQ (hleaf (q z) hqP).1 hδ.le
        (hleaf (q z) hqP).2 hv'.1 hv'.2 hsmall
      simp only [hcenter,PiLp.zero_apply] at hh
      change TubeIncident _ (F (q z)) (A v) at hh
      simpa only [hqz] using hh
  · apply Nat.cast_le.mpr
    apply le_trans (Finset.card_le_card (show Z.biUnion T ⊆ (P.biUnion V).image A from ?_))
      Finset.card_image_le
    intro u hu
    obtain ⟨z,hz,hu⟩ := Finset.mem_biUnion.mp hu
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hu
    exact Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨q z,(hq z hz).1,hv⟩)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_LeafPrefixPower
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original finite ball bounds become the exact exponential prefix bounds
required by the terminal-center incidence theorem. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem leaf_image_prefix_power_bound {δ t K : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t) (hK : 1 ≤ K)
    {P : Finset (Space 2)} (hball : NormalizedFiniteBallBound δ t K P)
    (Q : DyadicCube 2) (hQ : Q.side = 1) {N : ℕ}
    (l : Space 2 → CellPath 2) (hl : Set.InjOn l (P : Set (Space 2)))
    (hleaf : ∀ x ∈ P, l x ∈ cubePaths 2 N ∧ x ∈ (Q.descendant (l x)).carrier)
    (hsmall : δ ≤ 1/(2:ℝ)^N) :
    ∀ k ≤ N, ∀ p : CellPath 2,
      ((prefixFiber (P.image l) k p).card:ℝ) ≤
        (K*2^t)*(2:ℝ)^(-t*(k:ℝ))*((P.image l).card:ℝ) := by
  intro k hk p
  let r := 2/(2:ℝ)^k
  have hr : 0 < r := by dsimp [r]; positivity
  have hdr : δ ≤ r := by
    calc
      _ ≤ 1/(2:ℝ)^N := hsmall
      _ ≤ 1/(2:ℝ)^k := one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) hk)
      _ ≤ _ := by
        dsimp [r]
        exact div_le_div_of_nonneg_right (by norm_num) (by positivity)
  have hc : ((prefixFiber (P.image l) k p).card:ℝ) ≤ K*r^t*((P.image l).card:ℝ) := by
    by_cases hr1 : r ≤ 1
    · apply leaf_image_prefix_count_bound hδ (zero_le_one.trans hK) hball Q (by rw [hQ]; norm_num)
        hk hl hleaf hdr hr1
      rw [hQ]
      have hsqrt : Real.sqrt 2 ≤ 2 := (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
      dsimp [r]
      calc
        _ ≤ 2*(1/(2:ℝ)^k) := mul_le_mul_of_nonneg_right hsqrt (by positivity)
        _ = _ := by ring
    · have htotal : ((prefixFiber (P.image l) k p).card:ℝ) ≤ ((P.image l).card:ℝ) :=
        Nat.cast_le.mpr (Finset.card_le_card (Finset.filter_subset _ _))
      have hp : 1 ≤ r^t := Real.one_le_rpow (le_of_lt (lt_of_not_ge hr1)) ht
      exact htotal.trans (le_mul_of_one_le_left (Nat.cast_nonneg _)
        (one_le_mul_of_one_le_of_one_le hK hp))
  have hpow : r^t = (2:ℝ)^t*(2:ℝ)^(-t*(k:ℝ)) := by
    dsimp [r]
    rw [show (2:ℝ)/(2:ℝ)^k = 2*(1/(2:ℝ)^k) by ring,
      Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity),dyadic_inverse_power_eq]
  rw [hpow] at hc
  convert hc using 1
  all_goals try with_reducible_and_instances rfl
  ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CenteredPlanarIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Original points and pencils enter the profile theorem through their
actual leaf assignment. The conclusion counts original line parameters. -/
namespace Falconer
open Set Regularization
attribute [local instance] Classical.propDecidable

theorem uniform_centered_planar_incidence {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ Q : DyadicCube 2, Q.side = 1 → Q.center = 0 →
    ∀ δ K a b : ℝ, 0 < δ → 1 ≤ K → 0 < a →
      16*δ ≤ 1/(2:ℝ)^(m*B) →
      K*2^t ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) →
      K*4^s ≤ (2:ℝ)^(lam*(m*B:ℕ)) → b ≤ (2:ℝ)^(lam*(m*B:ℕ))*a →
    ∀ P : Finset (Space 2), P.Nonempty → (∀ x ∈ P, x ∈ Q.carrier) →
      FiniteSeparatedAt (2/(2:ℝ)^(m*B)) P → NormalizedFiniteBallBound δ t K P →
    ∀ V : Space 2 → Finset (Space 2),
      (∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
        InBoundedLineChart (V x) ∧ FiniteSeparatedAt (1/(2:ℝ)^(m*B)) (V x) ∧
        NormalizedFiniteBallBound δ s K (V x) ∧
        ∀ u ∈ V x, |u 0| ≤ 1/2 ∧ TubeIncident δ x u) →
      (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤ ((P.biUnion V).card:ℝ)/a := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hgain⟩ := uniform_leaf_incidence_gain hκ hκ1 hs hs1 ht
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro m hm Q hQ hcenter δ K a b hδ hK ha hsmall hpointbudget hpencilbudget hsize P hP hcarry hsep hball V hV
  have ht0 : 0 ≤ t := by linarith
  have hs0 : 0 ≤ s := hκ.le.trans hs
  have hQpos : 0 < Q.side := by rw [hQ]; norm_num
  have hsmall' : Real.sqrt 2*(Q.side/(2:ℝ)^(m*B)) < 2/(2:ℝ)^(m*B) := by
    rw [hQ]
    have hh : Real.sqrt 2 < 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),Real.sqrt_nonneg (2:ℝ)]
    have hp := mul_lt_mul_of_pos_right hh (show 0 < 1/(2:ℝ)^(m*B) by positivity)
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    ring
  obtain ⟨l,hleaf,hinj⟩ := exists_planar_leaf_injection hsep Q hQpos hcarry (m*B) hsmall'
  let L := P.image l
  have hL : L ⊆ cubePaths 2 (m*B) := by
    intro r hr
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hr
    exact (hleaf x hx).1
  have hpref := leaf_image_prefix_power_bound hδ ht0 hK hball Q hQ l hinj hleaf
    (show δ ≤ 1/(2:ℝ)^(m*B) by linarith)
  have hpref' : ∀ k ≤ m*B, ∀ q : CellPath 2,
      ((prefixFiber L k q).card:ℝ) ≤ (2:ℝ)^((lam/4)*(m*B:ℕ))*
        (2:ℝ)^(-t*(k:ℝ))*(L.card:ℝ) := by
    intro k hk q
    exact (hpref k hk q).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hpointbudget (by positivity)) (Nat.cast_nonneg _))
  obtain ⟨p,_,_,_,hCG⟩ := hgain m hm L hL (hP.image l) hpref' Q hQ
  let C := classLeaves L (blockLabel L (m*B) B (fun _ => []) (m+1))
    (blockLabel L (m*B) B (fun _ => []) (m+1) p)
  have hCP : C ⊆ P.image l := Finset.filter_subset _ _
  obtain ⟨T,hT,hunion⟩ := transport_pencils_to_leaf_centers Q hQ hcenter P l hleaf hCP
    hδ hs0 hK hsmall hsize hpencilbudget V hV
  exact (hCG a ha T hT).trans (div_le_div_of_nonneg_right hunion ha.le)

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceScaleChoice
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Choose a whole number of blocks at an arbitrary sufficiently small
original scale. Its ratio to the terminal grid is bounded independently of depth. -/
namespace Falconer

theorem incidence_block_scale_choice {B M : ℕ} (hB : 0 < B) {δ : ℝ} (hδ : 0 < δ)
    (hsmall : δ ≤ 1/(4*(2:ℝ)^(B*M))) :
    ∃ m : ℕ, M ≤ m ∧ 4*δ ≤ 1/(2:ℝ)^(m*B) ∧
      1/(2:ℝ)^(m*B) ≤ 4*(2:ℝ)^B*δ := by
  have hp : 1 < (2:ℝ)^B := one_lt_pow₀ (by norm_num) hB.ne'
  have hxM : ((2:ℝ)^B)^M ≤ 1/(4*δ) := by
    rw [← pow_mul]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 4*δ)).2
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*(2:ℝ)^(B*M))).mp hsmall
    nlinarith only [hh]
  have hx1 : 1 ≤ 1/(4*δ) := (one_le_pow₀ hp.le).trans hxM
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near hx1 hp
  have hMm : M ≤ m := by
    by_contra h
    have hle : m+1 ≤ M := by omega
    have hh := pow_le_pow_right₀ hp.le hle
    exact (not_lt_of_ge (hh.trans hxM)) hmhi
  refine ⟨m,hMm,?_,?_⟩
  · rw [← pow_mul] at hmlo
    apply (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(m*B))).2
    have hh := (le_div_iff₀ (by positivity : (0:ℝ) < 4*δ)).mp hmlo
    simpa only [mul_comm,Nat.mul_comm] using hh
  · rw [pow_succ,← pow_mul] at hmhi
    apply (div_le_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^(m*B))).2
    have hh := (div_lt_iff₀ (by positivity : (0:ℝ) < 4*δ)).mp hmhi
    convert hh.le using 1
    all_goals try with_reducible_and_instances rfl
    simp only [Nat.mul_comm]
    ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_OriginalPencilEqualization
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Equalize the original pencils before the fixed geometric preparation.
Only a logarithmic fraction of the original point set is lost. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem original_pencil_equalization {δ s t K : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 1 ≤ K) (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧
      FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ s K (V x) ∧
      ∀ l ∈ V x, TubeIncident δ x l) :
    let M := Nat.ceil ((4/δ+1)^2)
    let J : ℝ := (Nat.log 2 M+1:ℕ)
    ∃ k : ℕ, ∃ R : Finset (Space 2), ∃ U : Space 2 → Finset (Space 2),
      R.Nonempty ∧ R ⊆ P ∧ InBoundedLineChart R ∧ FiniteSeparatedAt δ R ∧
      NormalizedFiniteBallBound δ t (K*J) R ∧
      1 ≤ 2*K*δ^s*(2:ℝ)^k ∧
      (∀ x ∈ R, (U x).card = 2^k ∧ InBoundedLineChart (U x) ∧
        FiniteSeparatedAt δ (U x) ∧ NormalizedFiniteBallBound δ s (2*K) (U x) ∧
        ∀ l ∈ U x, TubeIncident δ x l) ∧
      ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  dsimp only
  let M := Nat.ceil ((4/δ+1)^2)
  let J : ℝ := (Nat.log 2 M+1:ℕ)
  have hmax (x : Space 2) (hx : x ∈ P) : (V x).card ≤ M := by
    have hbound : ∀ l ∈ V x, dist l 0 ≤ 2 := by
      intro l hl
      have hb := (hV x hx).2.1 l hl
      have hd := planar_dist_le_coordinate_sum l 0
      simp only [PiLp.zero_apply,sub_zero] at hd
      linarith only [hd,hb.1,hb.2]
    have hh := separated_ball_card (V x) 0 hδ (by norm_num : (0:ℝ) ≤ 2)
      ((hV x hx).2.2.1) hbound
    norm_num only [show (2:ℝ)*2 = 4 by norm_num] at hh
    exact Nat.cast_le.mp (hh.trans (Nat.le_ceil _))
  obtain ⟨k,R,U,hR,hRP,hsize,hU⟩ := exists_equal_size_tube_pencils P V hP
    (fun x hx => (hV x hx).1) hmax
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hUsize (x : Space 2) (hx : x ∈ R) : ((V x).card:ℝ) ≤ 2*((U x).card:ℝ) := by
    exact_mod_cast (hU x hx).2.2
  have hnumber : 1 ≤ 2*K*δ^s*(2:ℝ)^k := by
    obtain ⟨x,hx⟩ := hR
    have hh := finite_ball_bound_card_lower hδ hδ1 (hV x (hRP hx)).1
      (hV x (hRP hx)).2.2.2.1
    have hcard : ((U x).card:ℝ) = (2:ℝ)^k := by exact_mod_cast (hU x hx).2.1
    have hc := mul_le_mul_of_nonneg_left (hUsize x hx) (mul_nonneg hK0 (Real.rpow_nonneg hδ.le s))
    rw [hcard] at hc
    nlinarith only [hh,hc]
  refine ⟨k,R,U,hR,hRP,(fun x hx => hPchart x (hRP hx)),finiteSeparatedAt_subset hRP hPsep,
    normalized_finite_ball_bound_subset hδ.le hK0 hRP hsize hPball,hnumber,?_,?_⟩
  · intro x hx
    have hu := hU x hx
    have hv := hV x (hRP hx)
    refine ⟨hu.2.1,(fun l hl => hv.2.1 l (hu.1 hl)),finiteSeparatedAt_subset hu.1 hv.2.2.1,?_,
      (fun l hl => hv.2.2.2.2 l (hu.1 hl))⟩
    have hb := normalized_finite_ball_bound_subset hδ.le hK0 hu.1 (hUsize x hx) hv.2.2.2.1
    simpa only [mul_comm K 2] using hb
  · apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRP hx,(hU x hx).1 hl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidenceBucketBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The pencil-cardinality pigeonhole has only a linear cost in the chosen
block depth, with a fixed additive cost depending on the block width. -/
namespace Falconer

theorem incidence_bucket_count_bound {δ : ℝ} (hδ : 0 < δ) (N B : ℕ)
    (hscale : 1 ≤ 4*(2:ℝ)^(N+B)*δ) :
    Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 ≤ 2*N+2*B+11 := by
  have hpow : 1 ≤ (2:ℝ)^(N+B) := one_le_pow₀ (by norm_num)
  have hdiv : 4/δ ≤ 16*(2:ℝ)^(N+B) := by
    apply (div_le_iff₀ hδ).2
    nlinarith only [hscale]
  have hbase : 4/δ+1 ≤ 32*(2:ℝ)^(N+B) := by linarith only [hdiv,hpow]
  have hsq : (4/δ+1)^2 ≤ (2:ℝ)^(2*N+2*B+10) := by
    calc
      _ ≤ (32*(2:ℝ)^(N+B))^2 := pow_le_pow_left₀ (by positivity) hbase 2
      _ = _ := by
        rw [mul_pow,← pow_mul]
        rw [show 2*N+2*B+10 = (N+B)*2+10 by omega,pow_add]
        norm_num
        ring
  have hceil : Nat.ceil ((4/δ+1)^2) ≤ 2^(2*N+2*B+10) := by
    apply Nat.ceil_le.mpr
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hsq
  have hh := Nat.log_mono_right (b := 2) hceil
  rw [Nat.log_pow (by norm_num)] at hh
  omega

theorem incidence_packing_factor_bound {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (B : ℕ) (hscale : ρ ≤ 4*(2:ℝ)^B*δ) :
    (16*ρ/δ+1)^2 ≤ (64*(2:ℝ)^B+1)^2 := by
  apply pow_le_pow_left₀ (by positivity)
  have hh := mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 16)
  have hh' := div_le_div_of_nonneg_right hh hδ.le
  have he : 16*(4*(2:ℝ)^B*δ)/δ = 64*(2:ℝ)^B := by field_simp; ring
  rw [he] at hh'
  linarith only [hh']

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_IncidencePowerBudget
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Power bounds relating the original radius to the chosen block scale. -/
namespace Falconer

theorem incidence_inverse_scale_power {δ C a : ℝ} (hδ : 0 < δ) (hC : 0 ≤ C)
    (ha : 0 ≤ a) (N : ℕ) (hscale : 1/(2:ℝ)^N ≤ C*δ) :
    δ^(-a) ≤ C^a*(2:ℝ)^(a*(N:ℝ)) := by
  have hi : δ⁻¹ ≤ C*(2:ℝ)^N := by
    rw [← one_div]
    apply (div_le_iff₀ hδ).2
    have hh := (div_le_iff₀ (show (0:ℝ) < (2:ℝ)^N by positivity)).mp hscale
    nlinarith only [hh]
  rw [Real.rpow_neg_eq_inv_rpow]
  calc
    _ ≤ (C*(2:ℝ)^N)^a := Real.rpow_le_rpow (by positivity) hi ha
    _ = _ := by
      rw [Real.mul_rpow hC (by positivity),← Real.rpow_natCast_mul (by norm_num : (0:ℝ) ≤ 2)]
      congr 2
      ring

theorem incidence_bucket_linear_bound {δ : ℝ} (hδ : 0 < δ) (N B : ℕ)
    (hscale : 1/(2:ℝ)^N ≤ (4*(2:ℝ)^B)*δ) :
    ((Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ):ℝ) ≤ (2*(B:ℝ)+13)*((N:ℝ)+1) := by
  have hh : 1 ≤ 4*(2:ℝ)^(N+B)*δ := by
    have ht := (div_le_iff₀ (show (0:ℝ) < (2:ℝ)^N by positivity)).mp hscale
    rw [pow_add]
    nlinarith only [ht]
  have hc : ((Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ):ℝ) ≤ (2*N+2*B+11:ℕ) :=
    Nat.cast_le.mpr (incidence_bucket_count_bound hδ N B hh)
  push_cast at hc
  have hBN : 0 ≤ (B:ℝ)*(N:ℝ) := mul_nonneg (Nat.cast_nonneg B) (Nat.cast_nonneg N)
  push_cast
  nlinarith only [hc,hBN,Nat.cast_nonneg (α := ℝ) N]

theorem exists_incidence_absorption_parameters {lam ζ : ℝ}
    (hlam : 0 < lam) (hζ : 0 < ζ) (C : ℝ) (hC : 0 ≤ C) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1/8 ∧ ε ≤ lam/16 ∧ ε ≤ ζ/8 ∧
      ∃ N0 : ℕ, 0 < N0 ∧ ∀ N : ℕ, N0 ≤ N →
        C*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) ≤ (2:ℝ)^((lam/4)*(N:ℝ)) ∧
        C*(2:ℝ)^((2*ε)*(N:ℝ)) ≤ (2:ℝ)^(ζ*(N:ℝ)) := by
  let ε := min (1/8:ℝ) (min (lam/16) (ζ/8))
  have hε : 0 < ε := lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  have hε1 : ε ≤ 1/8 := min_le_left _ _
  have he_lam : ε ≤ lam/16 := (min_le_right _ _).trans (min_le_left _ _)
  have hεζ : ε ≤ ζ/8 := (min_le_right _ _).trans (min_le_right _ _)
  let σ := min (lam/8) (ζ/2)
  have hσ : 0 < σ := lt_min (by positivity) (by positivity)
  obtain ⟨N0,hN0,hpoly⟩ := dyadic_polynomial_loss hσ hC 1
  refine ⟨ε,hε,hε1,he_lam,hεζ,N0,hN0,?_⟩
  intro N hN
  have hc : C*((N:ℝ)+1) ≤ (2:ℝ)^(σ*(N:ℝ)) := by
    have hh := hpoly N hN
    rw [pow_one] at hh
    simpa only [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),mul_comm (Real.log 2)] using hh
  have hsigma_lam : σ ≤ lam/8 := min_le_left _ _
  have hσζ : σ ≤ ζ/2 := min_le_right _ _
  constructor
  · calc
      _ ≤ (2:ℝ)^(σ*(N:ℝ))*(2:ℝ)^(ε*(N:ℝ)) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = (2:ℝ)^((σ+ε)*(N:ℝ)) := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hsigma_lam,he_lam,hlam]) (Nat.cast_nonneg N))
  · have hCsmall : C ≤ (2:ℝ)^(σ*(N:ℝ)) :=
      (le_mul_of_one_le_right hC (by linarith only [Nat.cast_nonneg (α := ℝ) N])).trans hc
    calc
      _ ≤ (2:ℝ)^(σ*(N:ℝ))*(2:ℝ)^((2*ε)*(N:ℝ)) := mul_le_mul_of_nonneg_right hCsmall (by positivity)
      _ = (2:ℝ)^((σ+2*ε)*(N:ℝ)) := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_right (by linarith only [hσζ,hεζ,hζ]) (Nat.cast_nonneg N))

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_OriginalWeakCosts
attribute [-instance] _root_.OAI.Falconer.cellLabelMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All preparation costs fit one fixed polynomial. This converts the
original block-incidence estimate to the published weak-power conclusion. -/
namespace Falconer

theorem original_weak_costs {N B : ℕ} {δ ε lam ζ s t : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hε : 0 ≤ ε) (hε1 : ε ≤ 1/8)
    (hlam : 0 ≤ lam) (hs : 0 ≤ s) (hs1 : s ≤ 1) (_ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hscale : 1/(2:ℝ)^N ≤ (4*(2:ℝ)^B)*δ)
    (hpoly : originalIncidenceCost B*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) ≤ (2:ℝ)^((lam/4)*(N:ℝ)))
    (hfinal : originalIncidenceCost B*(2:ℝ)^((2*ε)*(N:ℝ)) ≤ (2:ℝ)^(ζ*(N:ℝ))) :
    let K := δ^(-ε);
    let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ);
    let F := (16*(1/(2:ℝ)^N)/δ+1)^2;
    (41472*K*J*F*2^t ≤ (2:ℝ)^((lam/4)*(N:ℝ)) ∧
      41472*K*J*F*4^s ≤ (2:ℝ)^(lam*(N:ℝ)) ∧
      81*F ≤ (2:ℝ)^(lam*(N:ℝ))) ∧
    (162*K*δ^s*F)*δ^(-2*s-ε) ≤ (2:ℝ)^((s+ζ)*(N:ℝ)) := by
  dsimp only
  let K := δ^(-ε)
  let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ)
  let F := (16*(1/(2:ℝ)^N)/δ+1)^2
  let C := 4*(2:ℝ)^B
  let D := 2*(B:ℝ)+13
  let F0 := (64*(2:ℝ)^B+1)^2
  have hC1 : 1 ≤ C := by
    have hh : (1:ℝ) ≤ 2^B := one_le_pow₀ (by norm_num)
    dsimp [C]
    linarith
  have hD0 : 0 ≤ D := by dsimp [D]; positivity
  have hF0 : 0 ≤ F0 := sq_nonneg _
  have hK1 : 1 ≤ K := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hJ1 : 1 ≤ J := by dsimp [J]; exact_mod_cast (show 1 ≤ Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 by omega)
  have hF : 0 ≤ F := sq_nonneg _
  have hCb : C^ε ≤ C := by
    calc
      _ ≤ C^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 (by linarith)
      _ = _ := Real.rpow_one _
  have hKb : K ≤ C*(2:ℝ)^(ε*(N:ℝ)) :=
    (incidence_inverse_scale_power hδ (zero_le_one.trans hC1) hε N hscale).trans
      (mul_le_mul_of_nonneg_right hCb (by positivity))
  have hJb : J ≤ D*((N:ℝ)+1) := incidence_bucket_linear_bound hδ N B hscale
  have hFb : F ≤ F0 := incidence_packing_factor_bound hδ (by positivity) B hscale
  have hweak : 41472*K*J*F*4 ≤ (2:ℝ)^((lam/4)*(N:ℝ)) := by
    calc
      _ ≤ 41472*(C*(2:ℝ)^(ε*(N:ℝ)))*(D*((N:ℝ)+1))*F0*4 := by gcongr
      _ = (165888*C*D*F0)*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) := by ring
      _ ≤ originalIncidenceCost B*((N:ℝ)+1)*(2:ℝ)^(ε*(N:ℝ)) := by
        gcongr
        exact le_max_left _ _
      _ ≤ _ := hpoly
  have hweakbig : (2:ℝ)^((lam/4)*(N:ℝ)) ≤ (2:ℝ)^(lam*(N:ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (mul_le_mul_of_nonneg_right (by linarith : lam/4 ≤ lam) (Nat.cast_nonneg N))
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · apply le_trans _ hweak
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (2:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ht2
      _ = 4 := by norm_num
  · apply le_trans _ (hweak.trans hweakbig)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc
      _ ≤ (4:ℝ)^(1:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 4 := by norm_num
  · apply le_trans _ (hweak.trans hweakbig)
    have hKJ := one_le_mul_of_one_le_of_one_le hK1 hJ1
    have hh := mul_le_mul_of_nonneg_right hKJ (show 0 ≤ 165888*F by positivity)
    nlinarith only [hh,hF]
  · have ha : 0 ≤ s+2*ε := by positivity
    have ha2 : s+2*ε ≤ 2 := by linarith
    have hCa : C^(s+2*ε) ≤ C^2 := by
      calc
        _ ≤ C^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hC1 ha2
        _ = C^2 := by norm_num
    have he : K*δ^s*δ^(-2*s-ε) = δ^(-(s+2*ε)) := by
      dsimp [K]
      rw [← Real.rpow_add hδ,← Real.rpow_add hδ]
      congr 1
      ring
    calc
      _ = 162*F*(K*δ^s*δ^(-2*s-ε)) := by ring
      _ = 162*F*δ^(-(s+2*ε)) := by rw [he]
      _ ≤ 162*F0*(C^(s+2*ε)*(2:ℝ)^((s+2*ε)*(N:ℝ))) := by
        gcongr
        exact incidence_inverse_scale_power hδ (zero_le_one.trans hC1) ha N hscale
      _ ≤ 162*F0*(C^2*(2:ℝ)^((s+2*ε)*(N:ℝ))) := by gcongr
      _ ≤ originalIncidenceCost B*(2:ℝ)^((s+2*ε)*(N:ℝ)) := by
        have hh : 162*F0*C^2 ≤ originalIncidenceCost B := le_max_right _ _
        nlinarith only [mul_le_mul_of_nonneg_right hh (show 0 ≤ (2:ℝ)^((s+2*ε)*(N:ℝ)) by positivity)]
      _ = (2:ℝ)^(s*(N:ℝ))*(originalIncidenceCost B*(2:ℝ)^((2*ε)*(N:ℝ))) := by
        rw [show (s+2*ε)*(N:ℝ) = s*(N:ℝ)+(2*ε)*(N:ℝ) by ring,
          Real.rpow_add (by norm_num : (0:ℝ) < 2)]
        ring
      _ ≤ (2:ℝ)^(s*(N:ℝ))*(2:ℝ)^(ζ*(N:ℝ)) := mul_le_mul_of_nonneg_left hfinal (by positivity)
      _ = _ := by rw [← Real.rpow_add (by norm_num : (0:ℝ) < 2)]; congr 1; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Estimates_ScaleThinning
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianDirectionSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.gaussianRows_probability _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.originalRadialSphereLaw_finite _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A prescribed coarser separation scale costs only the planar packing
factor. This is the fixed loss used before assigning original points to leaves. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planar_separated_subset_at {δ ρ : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (S : Finset (Space 2)) (hS : S.Nonempty) (hsep : FiniteSeparatedAt δ S) :
    ∃ P ⊆ S, P.Nonempty ∧ FiniteSeparatedAt ρ P ∧
      (S.card:ℝ) ≤ (2*ρ/δ+1)^2*(P.card:ℝ) := by
  obtain ⟨P,hPS,hPsep,hcover⟩ := exists_separated_cover S hρ
  have hP : P.Nonempty := by
    obtain ⟨x,hx⟩ := hS
    obtain ⟨y,hy,_⟩ := hcover x hx
    exact ⟨y,hy⟩
  refine ⟨P,hPS,hP,hPsep,?_⟩
  have hc : ∀ y ∈ P, ((S.filter fun x => dist x y ≤ ρ).card:ℝ) ≤ (2*ρ/δ+1)^2 := by
    intro y _
    exact separated_ball_card (S.filter fun x => dist x y ≤ ρ) y hδ hρ
      (fun x hx z hz hne => hsep x (Finset.mem_filter.mp hx).1 z (Finset.mem_filter.mp hz).1 hne)
      (fun x hx => (Finset.mem_filter.mp hx).2)
  simpa only [mul_comm] using selected_points_card_lower S id P hcover hc

theorem thin_pencils_to_scale {δ ρ s K a b : ℝ} (hδ : 0 < δ) (hρ : 0 ≤ ρ)
    (hK : 1 ≤ K) (ha : 0 < a) (P : Finset (Space 2))
    (V : Space 2 → Finset (Space 2))
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt δ (V x) ∧ NormalizedFiniteBallBound δ s K (V x)) :
    ∃ U : Space 2 → Finset (Space 2), ∀ x ∈ P,
      U x ⊆ V x ∧ a/(2*ρ/δ+1)^2 ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt ρ (U x) ∧
      NormalizedFiniteBallBound δ s (K*(2*ρ/δ+1)^2) (U x) := by
  have hF : 0 < (2*ρ/δ+1)^2 := by positivity
  have hex : ∀ x, ∃ T : Finset (Space 2), x ∈ P →
      T ⊆ V x ∧ T.Nonempty ∧ FiniteSeparatedAt ρ T ∧
      ((V x).card:ℝ) ≤ (2*ρ/δ+1)^2*(T.card:ℝ) := by
    intro x
    by_cases hx : x ∈ P
    · have hv := hV x hx
      have hn : (V x).Nonempty := Finset.card_pos.mp (Nat.cast_pos.mp (ha.trans_le hv.1))
      obtain ⟨T,hT⟩ := planar_separated_subset_at hδ hρ (V x) hn hv.2.2.1
      exact ⟨T,fun _ => hT⟩
    · exact ⟨∅,fun h => False.elim (hx h)⟩
  choose U hU using hex
  refine ⟨U,?_⟩
  intro x hx
  obtain ⟨hUV,_,hsep,hsize⟩ := hU x hx
  have hv := hV x hx
  refine ⟨hUV,(div_le_iff₀ hF).2 (by simpa only [mul_comm] using hv.1.trans hsize),
    (Nat.cast_le.mpr (Finset.card_le_card hUV)).trans hv.2.1,hsep,?_⟩
  exact normalized_finite_ball_bound_subset hδ.le (zero_le_one.trans hK) hUV hsize hv.2.2.2

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_CoarseSquashedPencils
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Prepare original bounded-chart pencils at the chosen terminal grid scale.
All losses are fixed packing factors in the scale ratio. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem planarSquash_in_centeredUnitCube {p : Space 2} (hp : |p 0| ≤ 1 ∧ |p 1| ≤ 1) :
    planarSquash p ∈ (centeredUnitCube 2).carrier := by
  intro i
  change -(1/2:ℝ) ≤ planarSquash p i ∧ planarSquash p i < -(1/2:ℝ)+1
  fin_cases i
  · change -(1/2:ℝ) ≤ p 0/4 ∧ p 0/4 < -(1/2:ℝ)+1
    rcases abs_le.mp hp.1 with ⟨hl,hu⟩
    constructor <;> linarith
  · change -(1/2:ℝ) ≤ p 1/16 ∧ p 1/16 < -(1/2:ℝ)+1
    rcases abs_le.mp hp.2 with ⟨hl,hu⟩
    constructor <;> linarith

theorem coarse_squashed_pencil_configuration {δ ρ s t K a b : ℝ}
    (hδ : 0 < δ) (hρ : 0 ≤ ρ) (hs : 0 ≤ s) (hs2 : s ≤ 2) (ht : 0 ≤ t) (ht2 : t ≤ 2)
    (hK : 1 ≤ K) (ha : 0 < a)
    (P : Finset (Space 2)) (V : Space 2 → Finset (Space 2))
    (hP : P.Nonempty) (hPchart : InBoundedLineChart P) (hPsep : FiniteSeparatedAt δ P)
    (hPball : NormalizedFiniteBallBound δ t K P)
    (hV : ∀ x ∈ P, a ≤ ((V x).card:ℝ) ∧ ((V x).card:ℝ) ≤ b ∧
      InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
      NormalizedFiniteBallBound δ s K (V x) ∧ ∀ l ∈ V x, TubeIncident δ x l) :
    let F := (16*ρ/δ+1)^2;
    ∃ R : Finset (Space 2), R.Nonempty ∧ (∀ x ∈ R, x ∈ (centeredUnitCube 2).carrier) ∧
      FiniteSeparatedAt (2*ρ) R ∧ NormalizedFiniteBallBound (δ/4) t (20736*K*F) R ∧
    ∃ U : Space 2 → Finset (Space 2),
      (∀ x ∈ R, a/(81*F) ≤ ((U x).card:ℝ) ∧ ((U x).card:ℝ) ≤ b ∧
        InBoundedLineChart (U x) ∧ FiniteSeparatedAt ρ (U x) ∧
        NormalizedFiniteBallBound (δ/4) s (20736*K*F) (U x) ∧
        ∀ l ∈ U x, |l 0| ≤ 1/2 ∧ TubeIncident (δ/4) x l) ∧
      ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := by
  obtain ⟨P0,hP0P,hP0,_,hchart,hsep,hball,V0,_,hV0,hunion⟩ :=
    squashed_pencil_configuration hδ hs hs2 ht ht2 hK ha P V hP hPchart hPsep hPball hV
  let Q := P0.image planarSquash
  let T := squashedPencils V0
  let F := (16*ρ/δ+1)^2
  let E := (2*ρ/(δ/4)+1)^2
  have hδ4 : 0 < δ/4 := by positivity
  have hF : 0 < F := by dsimp [F]; positivity
  have hE : 0 < E := by dsimp [E]; positivity
  have hK0 : 1 ≤ 20736*K := by linarith
  obtain ⟨R,hRQ,hR,hRsep,hRcard⟩ := planar_separated_subset_at hδ4
    (show 0 ≤ 2*ρ by positivity) Q (hP0.image planarSquash) hsep
  have hFformula : (2*(2*ρ)/(δ/4)+1)^2 = F := by dsimp [F]; field_simp; ring
  rw [hFformula] at hRcard
  have hEF : E ≤ F := by
    change (2*ρ/(δ/4)+1)^2 ≤ (16*ρ/δ+1)^2
    apply pow_le_pow_left₀ (by positivity)
    have he : 2*ρ/(δ/4) = 8*ρ/δ := by field_simp; ring
    rw [he]
    have hh : 8*ρ/δ ≤ 16*ρ/δ := div_le_div_of_nonneg_right (by linarith) hδ.le
    linarith
  have hdata : ∀ x ∈ R, a/81 ≤ ((T x).card:ℝ) ∧ ((T x).card:ℝ) ≤ b ∧
      FiniteSeparatedAt (δ/4) (T x) ∧ NormalizedFiniteBallBound (δ/4) s (20736*K) (T x) := by
    intro x hx
    have hh := hV0 x (hRQ hx)
    exact ⟨hh.1,hh.2.1,hh.2.2.2.1,hh.2.2.2.2.1⟩
  obtain ⟨U,hU⟩ := thin_pencils_to_scale hδ4 hρ hK0 (show 0 < a/81 by positivity) R T hdata
  refine ⟨R,hR,?_,hRsep,?_,U,?_,?_⟩
  · intro x hx
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp (hRQ hx)
    exact planarSquash_in_centeredUnitCube (hPchart p (hP0P hp))
  · exact normalized_finite_ball_bound_subset hδ4.le (by linarith) hRQ hRcard hball
  · intro x hx
    obtain ⟨hUT,hlo,hhi,hsep',hball'⟩ := hU x hx
    have hh := hV0 x (hRQ hx)
    refine ⟨?_,hhi,(fun l hl => hh.2.2.1 l (hUT hl)),hsep',?_,
      (fun l hl => hh.2.2.2.2.2 l (hUT hl))⟩
    · calc
        a/(81*F) ≤ a/(81*E) := div_le_div_of_nonneg_left ha.le (by positivity) (by gcongr)
        _ = (a/81)/E := by rw [div_mul_eq_div_div]
        _ ≤ ((U x).card:ℝ) := hlo
    · intro z r hr hr1
      have hb := hball' z r hr hr1
      exact hb.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEF (by linarith))
          (Real.rpow_nonneg (hδ4.le.trans hr) _)) (Nat.cast_nonneg _))
  · apply le_trans _ hunion
    apply Nat.cast_le.mpr
    apply Finset.card_le_card
    intro l hl
    obtain ⟨x,hx,hl⟩ := Finset.mem_biUnion.mp hl
    exact Finset.mem_biUnion.mpr ⟨x,hRQ hx,(hU x hx).1 hl⟩

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Incidence_OriginalBlockIncidence
attribute [-instance] _root_.OAI.Falconer.cellDistance_finite _root_.OAI.Falconer.cellLabelMeasurableSpace _root_.OAI.Falconer.gaussianChartSliceMeasure_finite _root_.OAI.Falconer.gaussianPointSliceMeasure_finite _root_.OAI.Falconer.instIsMarkovKernelSpaceRadialKernel _root_.OAI.Falconer.radialFrequencyMeasure_finite _root_.OAI.Falconer.radialIntervalMeasure_finite _root_.OAI.Falconer.scalarProjectionLaw_finite _root_.OAI.Falconer.surfaceMeasure_finite _root_.OAI.Falconer.testedCellDistance_finite _root_.OAI.Falconer.testedCellPair_finite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete original finite configuration at a chosen block depth.
The remaining numerical conditions concern only the scale and weak constants. -/
namespace Falconer
open Set
attribute [local instance] Classical.propDecidable

theorem original_block_incidence {κ s t : ℝ} (hκ : 0 < κ) (hκ1 : κ ≤ 1/100)
    (hs : κ ≤ s) (hs1 : s ≤ 1-8*κ) (ht : s+8*κ ≤ t) (ht2 : t ≤ 2) :
    ∃ B : ℕ, 0 < B ∧ Even B ∧ ∃ lam ζ : ℝ, 0 < lam ∧ 0 < ζ ∧
    ∃ M : ℕ, 0 < M ∧ ∀ m : ℕ, M ≤ m →
    ∀ δ K : ℝ, 0 < δ → δ ≤ 1 → 1 ≤ K → 4*δ ≤ 1/(2:ℝ)^(m*B) →
      (let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ);
       let F := (16*(1/(2:ℝ)^(m*B))/δ+1)^2;
       41472*K*J*F*2^t ≤ (2:ℝ)^((lam/4)*(m*B:ℕ)) ∧
       41472*K*J*F*4^s ≤ (2:ℝ)^(lam*(m*B:ℕ)) ∧
       81*F ≤ (2:ℝ)^(lam*(m*B:ℕ))) →
    ∀ P : Finset (Space 2), P.Nonempty → InBoundedLineChart P → FiniteSeparatedAt δ P →
      NormalizedFiniteBallBound δ t K P →
    ∀ V : Space 2 → Finset (Space 2),
      (∀ x ∈ P, (V x).Nonempty ∧ InBoundedLineChart (V x) ∧ FiniteSeparatedAt δ (V x) ∧
        NormalizedFiniteBallBound δ s K (V x) ∧ ∀ l ∈ V x, TubeIncident δ x l) →
      (2:ℝ)^((s+ζ)*(m*B:ℕ)) ≤
        (162*K*δ^s*(16*(1/(2:ℝ)^(m*B))/δ+1)^2)*((P.biUnion V).card:ℝ) := by
  obtain ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,hcentered⟩ := uniform_centered_planar_incidence hκ hκ1 hs hs1 ht
  refine ⟨B,hB,hBeven,lam,ζ,hlam,hζ,M,hM,?_⟩
  intro m hm δ K hδ hδ1 hK hscale hcost P hP hPchart hPsep hPball V hV
  let N := m*B
  let J : ℝ := (Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1:ℕ)
  let F := (16*(1/(2:ℝ)^N)/δ+1)^2
  have hJ : 1 ≤ J := by dsimp [J]; exact_mod_cast (show 1 ≤ Nat.log 2 (Nat.ceil ((4/δ+1)^2))+1 by omega)
  have hF : 0 < F := by dsimp [F]; positivity
  obtain ⟨hcost1,hcost2,hcost3⟩ := hcost
  obtain ⟨k,P0,V0,hP0,_hP0P,hchart0,hsep0,hball0,hnumber,hV0,hunion0⟩ :=
    original_pencil_equalization hδ hδ1 hK P V hP hPchart hPsep hPball hV
  let K0 := 2*K*J
  have hK0 : 1 ≤ K0 := by
    have hh := one_le_mul_of_one_le_of_one_le hK hJ
    dsimp [K0]
    nlinarith only [hh]
  have hKJ : K*J ≤ K0 := by dsimp [K0]; nlinarith only [mul_nonneg (zero_le_one.trans hK) (zero_le_one.trans hJ)]
  have h2K : 2*K ≤ K0 := by
    dsimp [K0]
    exact le_mul_of_one_le_right (by linarith) hJ
  have mono {a b u : ℝ} {S : Finset (Space 2)} (hab : a ≤ b)
      (hb : NormalizedFiniteBallBound δ u a S) : NormalizedFiniteBallBound δ u b S := by
    intro z r hr hr1
    exact (hb z r hr hr1).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg (hδ.le.trans hr) _)) (Nat.cast_nonneg _))
  have hv0 : ∀ x ∈ P0, (2:ℝ)^k ≤ ((V0 x).card:ℝ) ∧ ((V0 x).card:ℝ) ≤ (2:ℝ)^k ∧
      InBoundedLineChart (V0 x) ∧ FiniteSeparatedAt δ (V0 x) ∧
      NormalizedFiniteBallBound δ s K0 (V0 x) ∧ ∀ l ∈ V0 x, TubeIncident δ x l := by
    intro x hx
    have hh := hV0 x hx
    have hc : ((V0 x).card:ℝ) = (2:ℝ)^k := by exact_mod_cast hh.1
    exact ⟨hc.ge,hc.le,hh.2.1,hh.2.2.1,mono h2K hh.2.2.2.1,hh.2.2.2.2⟩
  obtain ⟨R,hR,hcarry,hRsep,hRball,U,hU,hunion⟩ := coarse_squashed_pencil_configuration hδ
    (by positivity : (0:ℝ) ≤ 1/(2:ℝ)^N) (hκ.le.trans hs) (by linarith) (by linarith) ht2
    hK0 (by positivity : (0:ℝ) < (2:ℝ)^k) P0 V0 hP0 hchart0 hsep0 (mono hKJ hball0) hv0
  have hKfinal : 1 ≤ 20736*K0*F := by
    have hF1 : 1 ≤ F := by
      dsimp [F]
      have hh : 0 ≤ 16*(1/(2:ℝ)^N)/δ := by positivity
      nlinarith only [hh]
    have hh := one_le_mul_of_one_le_of_one_le hK0 hF1
    nlinarith only [hh]
  have hQside : (centeredUnitCube 2).side = 1 := rfl
  have hQcenter : (centeredUnitCube 2).center = 0 := by
    ext i
    change -(1/2:ℝ)+1/2 = 0
    ring
  have hsize : (2:ℝ)^k ≤ (2:ℝ)^(lam*(N:ℝ))*((2:ℝ)^k/(81*F)) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (by positivity : (0:ℝ) < 81*F)).2
    have hh := mul_le_mul_of_nonneg_left hcost3 (show 0 ≤ (2:ℝ)^k by positivity)
    nlinarith only [hh]
  have hgain := hcentered m hm (centeredUnitCube 2) hQside hQcenter (δ/4) (20736*K0*F)
    ((2:ℝ)^k/(81*F)) ((2:ℝ)^k) (by positivity) hKfinal (by positivity)
    (by nlinarith only [hscale])
    (by dsimp [K0]; convert hcost1 using 1; ring)
    (by dsimp [K0]; convert hcost2 using 1; ring) hsize R hR hcarry (by simpa only [mul_one_div,N] using hRsep) hRball U hU
  have hUorig : ((R.biUnion U).card:ℝ) ≤ ((P.biUnion V).card:ℝ) := hunion.trans hunion0
  have hga := (le_div_iff₀ (by positivity : (0:ℝ) < (2:ℝ)^k/(81*F))).mp hgain
  have hmul := mul_le_mul_of_nonneg_right (hga.trans hUorig) (show 0 ≤ 81*F by positivity)
  have hcancel : (2:ℝ)^((s+ζ)*(N:ℝ))*((2:ℝ)^k/(81*F))*(81*F) =
      (2:ℝ)^((s+ζ)*(N:ℝ))*(2:ℝ)^k := by field_simp
  rw [hcancel] at hmul
  calc
    _ ≤ (2:ℝ)^((s+ζ)*(N:ℝ))*(2*K*δ^s*(2:ℝ)^k) :=
      le_mul_of_one_le_right (by positivity) hnumber
    _ = (2*K*δ^s)*((2:ℝ)^((s+ζ)*(N:ℝ))*(2:ℝ)^k) := by ring
    _ ≤ (2*K*δ^s)*(((P.biUnion V).card:ℝ)*(81*F)) :=
      mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by dsimp [F]; ring

end Falconer

end OAI
end

section
-- module Solutions.OAIQ088_FD.Falconer_Campaign123PlanarFurstenbergProof
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge the precise planar Furstenberg specialization used by the
all-dimensional Falconer proof, by the finite multiscale incidence argument. -/
namespace Falconer
open MeasureTheory
open scoped ENNReal

theorem publishedPlanarFurstenberg_proved_oai : PublishedPlanarFurstenberg := by
  intro b f hb hbhalf hbf hf1
  let κ := min b (min (f-b) (1/100:ℝ))/16
  have hκ : 0 < κ := div_pos (lt_min hb (lt_min (sub_pos.mpr hbf) (by norm_num))) (by norm_num)
  have hκb : κ ≤ b/16 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hκg : κ ≤ (f-b)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_left _ _)) (by norm_num)
  have hκone : κ ≤ (1/100:ℝ)/16 := div_le_div_of_nonneg_right
    ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  obtain ⟨B,hB,_,lam,ζ,hlam,hζ,M,hM,hblock⟩ := original_block_incidence hκ
    (by linarith : κ ≤ 1/100) (by linarith : κ ≤ b) (by linarith : b ≤ 1-8*κ)
    (by linarith : b+8*κ ≤ f) (by linarith : f ≤ 2)
  have hC : 0 ≤ originalIncidenceCost B := by unfold originalIncidenceCost; positivity
  obtain ⟨ε,hε,hε1,_,_,N0,hN0,habsorb⟩ := exists_incidence_absorption_parameters hlam hζ
    (originalIncidenceCost B) hC
  let δ0 := min 1 (1/(4*(2:ℝ)^(B*(M+N0+1))))
  have hδ0 : 0 < δ0 := lt_min (by norm_num) (by positivity)
  refine ⟨ε,δ0,hε,hδ0,min_le_left _ _,?_⟩
  intro δ hδ hδsmall P hP hPchart hPsep hPball V hV
  have hδ1 : δ ≤ 1 := hδsmall.le.trans (min_le_left _ _)
  have hsmall : δ ≤ 1/(4*(2:ℝ)^(B*(M+N0+1))) := hδsmall.le.trans (min_le_right _ _)
  obtain ⟨m,hm,hscale,hscale'⟩ := incidence_block_scale_choice hB hδ hsmall
  have hmM : M ≤ m := by omega
  have hNm : m ≤ m*B := Nat.le_mul_of_pos_right m hB
  have hNN : N0 ≤ m*B := by omega
  obtain ⟨hpoly,hfinal⟩ := habsorb (m*B) hNN
  have hcost := original_weak_costs hδ hδ1 hε.le hε1 hlam.le hb.le
    (by linarith : b ≤ 1) (by linarith : 0 ≤ f) (by linarith : f ≤ 2) hscale' hpoly hfinal
  have hK : 1 ≤ δ^(-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hδ hδ1 (by linarith)
  have hcard := hblock m hmM δ (δ^(-ε)) hδ hδ1 hK hscale hcost.1
    P hP hPchart hPsep hPball V hV
  have hcoeff : 0 < 162*δ^(-ε)*δ^b*(16*(1/(2:ℝ)^(m*B))/δ+1)^2 := by positivity
  exact (mul_le_mul_iff_right₀ hcoeff).mp (hcost.2.trans hcard)

end Falconer

end OAI
end

theorem solution : type_of% @OAI.Falconer.publishedPlanarFurstenberg_proved_oai := @OAI.Falconer.publishedPlanarFurstenberg_proved_oai
