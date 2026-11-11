-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:49:27.297197+00:00
-- url     : https://prove2.me/submissions/6466c5a5-66db-4a4e-9b38-33e83ffe9171

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT001
import Definitions.Def_OAIQ241TT002

section
-- module Solutions.OAIQ241_TT.ThinTrees_Coarea
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uE uV2 uE2 uV3 uE3 uI uI2 uI3

section
open scoped Classical
open Matrix

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma integrable_interval_indicator (a b c : ℝ) :
    Integrable ((Set.Ioc a b).indicator (fun _ : ℝ => c)) :=
  (integrable_indicator_iff measurableSet_Ioc).mpr (integrableOn_const (by simp [Real.volume_Ioc]))

lemma integral_interval_indicator (a b c : ℝ) (hab : a ≤ b) :
    (∫ t : ℝ, (Set.Ioc a b).indicator (fun _ => c) t) = (b-a)*c := by
  rw [integral_indicator_const c measurableSet_Ioc, Real.volume_real_Ioc,
    max_eq_left (sub_nonneg.mpr hab), smul_eq_mul]

lemma threshold_interval {x y t : ℝ} :
    ((x < t ∧ ¬ y < t) ∨ (y < t ∧ ¬ x < t)) ↔ t ∈ Set.Ioc (min x y) (max x y) := by
  simp only [Set.mem_Ioc, min_lt_iff, le_max_iff, not_lt]
  constructor
  · rintro (h | h)
    · exact ⟨Or.inl h.1, Or.inr h.2⟩
    · exact ⟨Or.inr h.1, Or.inl h.2⟩
  · rintro ⟨h | h, h' | h'⟩ <;> first | (exfalso; linarith) | exact Or.inl ⟨h, h'⟩ | exact Or.inr ⟨h, h'⟩

lemma finite_coarea {V : Type uV} {E : Type uE} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    (∫ t : ℝ, (((univ.filter (fun e =>
      (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) =
      ∑e, |f (u e)-f (v e)| := by
  have heq (t : ℝ) :
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ)) =
      ∑e, (Set.Ioc (min (f (u e)) (f (v e)))
        (max (f (u e)) (f (v e)))).indicator (fun _ : ℝ => (1:ℝ)) t := by
    simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    apply sum_congr rfl
    intro e he
    rw [Set.indicator_apply]
    simp only [threshold_interval]
    split_ifs <;> norm_num
  simp_rw [heq]
  rw [integral_finsetSum _ (fun e _ => integrable_interval_indicator _ _ _)]
  apply sum_congr rfl
  intro e he
  rw [integral_interval_indicator _ _ _ min_le_max, mul_one]
  simpa only [abs_sub_comm] using (max_sub_min_eq_abs (f (u e)) (f (v e)))

lemma integrable_cut_card {V : Type uV2} {E : Type uE2} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) :
    Integrable (fun t : ℝ =>
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) := by
  have hi := integrable_finsetSum univ
    (fun e _ => integrable_interval_indicator (min (f (u e)) (f (v e)))
      (max (f (u e)) (f (v e))) 1)
  apply hi.congr
  filter_upwards with t
  simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter]
  apply sum_congr rfl
  intro e he
  rw [Set.indicator_apply]
  simp only [threshold_interval]
  split_ifs <;> norm_num

lemma cut_range_bound {V : Type uV3} {E : Type uE3} [Fintype E] [DecidableEq E]
    (u v : E → V) (f : V → ℝ) {a b k : ℝ} (hab : a ≤ b)
    (hcut : ∀t ∈ Set.Ioc a b, k ≤
      (((univ.filter (fun e => (f (u e)<t ∧ ¬f (v e)<t) ∨
        (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) :
    k*(b-a) ≤ ∑e, |f (u e)-f (v e)| := by
  have hh := integral_mono (integrable_interval_indicator a b k)
    (integrable_cut_card u v f) (show (Set.Ioc a b).indicator (fun _ : ℝ => k) ≤
      (fun t : ℝ => (((univ.filter (fun e =>
        (f (u e)<t ∧ ¬f (v e)<t) ∨ (f (v e)<t ∧ ¬f (u e)<t))).card : ℝ))) by
        intro t
        by_cases ht : t ∈ Set.Ioc a b
        · rw [Set.indicator_of_mem ht]
          exact hcut t ht
        · rw [Set.indicator_of_notMem ht]
          positivity)
  rw [integral_interval_indicator a b k hab, finite_coarea] at hh
  simpa only [mul_comm] using hh

lemma clamp_eq_left {a b x : ℝ} (hab : a ≤ b) (hx : x ≤ a) : clamp a b x = a := by
  simp [clamp, max_eq_left hx, min_eq_right hab]

lemma clamp_eq_right {a b x : ℝ} (hab : a ≤ b) (hx : b ≤ x) : clamp a b x = b := by
  simp [clamp, max_eq_right (hab.trans hx), min_eq_left hx]

lemma clamp_bounds {a b : ℝ} (hab : a ≤ b) (x : ℝ) :
    a ≤ clamp a b x ∧ clamp a b x ≤ b := by
  exact ⟨le_min hab (le_max_left _ _), min_le_left _ _⟩

lemma clamp_lt_iff {a b x t : ℝ} (ht : t ∈ Set.Ioc a b) :
    clamp a b x < t ↔ x < t := by
  simp only [clamp, min_lt_iff, max_lt_iff]
  constructor
  · rintro (h | h)
    · linarith [ht.2]
    · exact h.2
  · intro h
    exact Or.inr ⟨ht.1, h⟩

end
end StrongThinTree.Geometry

namespace StrongThinTree.Geometry
noncomputable section
open Finset MeasureTheory Set

lemma clamp_mono {a b x y : ℝ} (hxy : x ≤ y) : clamp a b x ≤ clamp a b y :=
  min_le_min_left _ (max_le_max_left _ hxy)

lemma clipped_affine_interval_increasing {a b x y : ℝ} (hab : a ≤ b) (hxy : x < y) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  by_cases heq : clamp a b x = clamp a b y
  · exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp [heq],by simp⟩
  have hAB := lt_of_le_of_ne (clamp_mono hxy.le) heq
  have hAx := clamp_bounds hab x
  have hBy := clamp_bounds hab y
  have hx : x < b := by
    by_contra h
    have hh := clamp_eq_right hab (not_lt.mp h)
    linarith
  have hy : a < y := by
    by_contra h
    have hh := clamp_eq_left hab (not_lt.mp h)
    linarith
  have hxA : x ≤ clamp a b x := by
    rw [clamp, min_eq_right (max_le hab hx.le)]
    exact le_max_right _ _
  have hBy' : clamp a b y ≤ y := by
    rw [clamp, max_eq_right hy.le]
    exact min_le_right _ _
  let s := y-x
  have hs : 0 < s := sub_pos.mpr hxy
  let l := (clamp a b x-x)/s
  let r := (clamp a b y-x)/s
  have hl : 0 ≤ l := div_nonneg (sub_nonneg.mpr hxA) hs.le
  have hr : r ≤ 1 := (div_le_one hs).mpr (by dsimp [s] <;> linarith)
  have hlr : l ≤ r := (div_le_div_iff_of_pos_right hs).mpr (by linarith)
  have hlmul : l*s = clamp a b x-x := div_mul_cancel₀ _ hs.ne'
  have hrmul : r*s = clamp a b y-x := div_mul_cancel₀ _ hs.ne'
  refine ⟨l,r,hl,hlr,hr,?_,?_⟩
  · rw [abs_of_nonpos (by linarith : clamp a b x-clamp a b y ≤ 0),
      abs_of_pos (sub_pos.mpr hxy)]
    dsimp [s] at hlmul hrmul
    nlinarith
  · intro t ht
    have hlt := mul_lt_mul_of_pos_right ht.1 hs
    have htr := mul_lt_mul_of_pos_right ht.2 hs
    dsimp [s] at hlt htr hlmul hrmul
    constructor <;> nlinarith

lemma clipped_affine_interval {a b x y : ℝ} (hab : a ≤ b) :
    ∃ l r : ℝ, 0 ≤ l ∧ l ≤ r ∧ r ≤ 1 ∧
      |clamp a b x-clamp a b y| = |y-x| *(r-l) ∧
      ∀t ∈ Set.Ioo l r, a < x+t*(y-x) ∧ x+t*(y-x) < b := by
  rcases lt_trichotomy x y with hxy | hxy | hxy
  · exact clipped_affine_interval_increasing hab hxy
  · subst y
    exact ⟨0,0,by norm_num,by norm_num,by norm_num,by simp,by simp⟩
  · obtain ⟨l,r,hl,hlr,hr,heq,h⟩ := clipped_affine_interval_increasing hab hxy
    refine ⟨1-r,1-l,by linarith,by linarith,by linarith,?_,?_⟩
    · rw [abs_sub_comm, heq, abs_sub_comm x y]
      congr 1
      ring
    · intro t ht
      have hh := h (1-t) ⟨by linarith [ht.2],by linarith [ht.1]⟩
      constructor <;> nlinarith [hh.1,hh.2]

lemma clamped_affine_disjoint_sum {I : Type uI} [Fintype I]
    (a b x y : I → ℝ) {L : ℝ} (hL : 0 ≤ L)
    (hab : ∀i, a i ≤ b i) (hslope : ∀i, |y i-x i| ≤ L)
    (hdis : ∀ i j, i ≠ j → ∀t ∈ Set.Ioo (0:ℝ) 1,
      ¬(a i < x i+t*(y i-x i) ∧ x i+t*(y i-x i)<b i ∧
        a j < x j+t*(y j-x j) ∧ x j+t*(y j-x j)<b j)) :
    ∑i, |clamp (a i) (b i) (x i)-clamp (a i) (b i) (y i)| ≤ L := by
  classical
  choose l r hl hlr hr heq hactive using fun i =>
    clipped_affine_interval (x:=x i) (y:=y i) (hab i)
  have hsub : (⋃i, Set.Ioo (l i) (r i)) ⊆ Set.Ioo (0:ℝ) 1 := by
    rintro t ⟨_,⟨i,rfl⟩,ht⟩
    exact ⟨lt_of_le_of_lt (hl i) ht.1,lt_of_lt_of_le ht.2 (hr i)⟩
  have hd : Pairwise (fun i j => Disjoint (Set.Ioo (l i) (r i)) (Set.Ioo (l j) (r j))) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro t hti htj
    exact hdis i j hij t ⟨lt_of_le_of_lt (hl i) hti.1,
      lt_of_lt_of_le hti.2 (hr i)⟩ ⟨(hactive i t hti).1,(hactive i t hti).2,
        (hactive j t htj).1,(hactive j t htj).2⟩
  have hv := measureReal_mono (μ:=volume) hsub (by simp [Real.volume_Ioo])
  rw [measureReal_iUnion_fintype hd (fun _ => measurableSet_Ioo)
      (fun _ => by simp [Real.volume_Ioo]), Real.volume_real_Ioo] at hv
  simp only [Real.volume_real_Ioo, max_eq_left (sub_nonneg.mpr (hlr _))] at hv
  have hsum : ∑i, (r i-l i) ≤ 1 := by simpa using hv
  calc
    _ = ∑i, |y i-x i| *(r i-l i) := sum_congr rfl (fun i _ => heq i)
    _ ≤ ∑i, L*(r i-l i) := sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_right (hslope i) (sub_nonneg.mpr (hlr i)))
    _ = L*∑i, (r i-l i) := (mul_sum _ _ _).symm
    _ ≤ L*1 := mul_le_mul_of_nonneg_left hsum hL
    _ = L := mul_one L

end
end StrongThinTree.Geometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Hierarchy
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma cut_internal_split {A S : Finset (Fin n)} (hS : S ⊆ A) :
    ((G.inducedEdges A).card : ℝ) = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
  have heq : G.inducedEdges A = G.inducedEdges S ∪ G.inducedEdges (A\S) ∪ G.cut (G.inducedEdges A) S := by
    ext e
    simp only [mem_union,mem_inducedEdges,cut,mem_filter]
    simp only [mem_sdiff]
    constructor
    · intro h
      by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> tauto
    · intro h
      rcases h with ((h | h) | h)
      · exact ⟨hS h.1,hS h.2⟩
      · exact ⟨h.1.1,h.2.1⟩
      · exact h.1
  have hd : Disjoint (G.inducedEdges S) (G.inducedEdges (A\S)) := by
    rw [Finset.disjoint_left]
    intro e he hf
    rw [mem_inducedEdges] at he hf
    exact (mem_sdiff.mp hf.1).2 he.1
  have hd' : Disjoint (G.inducedEdges S ∪ G.inducedEdges (A\S)) (G.cut (G.inducedEdges A) S) := by
    rw [Finset.disjoint_left]
    intro e he hf
    have hc := (mem_filter.mp hf).2
    rcases mem_union.mp he with he | he
    · rw [mem_inducedEdges] at he
      tauto
    · rw [mem_inducedEdges] at he
      have hl := (mem_sdiff.mp he.1).2
      have hr := (mem_sdiff.mp he.2).2
      tauto
  have hc : (G.inducedEdges A).card = (G.inducedEdges S).card+
      (G.inducedEdges (A\S)).card+(G.cut (G.inducedEdges A) S).card := by
    conv_lhs => rw [heq]
    rw [card_union_of_disjoint hd',card_union_of_disjoint hd]
  exact_mod_cast hc

lemma vertexPartition_singleton {A : Finset (Fin n)} (hA : A.Nonempty) :
    VertexPartition A {A} := by
  refine ⟨?_,?_,by simp⟩
  · intro B hB
    have heq := mem_singleton.mp hB
    subst B
    exact ⟨hA,Subset.rfl⟩
  · intro B hB C hC hne
    exact (hne ((mem_singleton.mp hB).trans (mem_singleton.mp hC).symm)).elim

lemma vertexPartition_union {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (hQ : VertexPartition B Q) (hAB : Disjoint A B) :
    VertexPartition (A∪B) (P∪Q) ∧ Disjoint P Q := by
  have hd : ∀S ∈ P, ∀T ∈ Q, Disjoint S T := by
    intro S hS T hT
    exact hAB.mono (hP.1 S hS).2 (hQ.1 T hT).2
  have hPQ : Disjoint P Q := by
    rw [Finset.disjoint_left]
    intro S hS hT
    obtain ⟨u,hu⟩ := (hP.1 S hS).1
    exact Finset.disjoint_left.mp (hd S hS S hT) hu hu
  refine ⟨⟨?_,?_,?_⟩,hPQ⟩
  · intro S hS
    rcases mem_union.mp hS with hS | hS
    · exact ⟨(hP.1 S hS).1,((hP.1 S hS).2).trans (subset_union_left)⟩
    · exact ⟨(hQ.1 S hS).1,((hQ.1 S hS).2).trans (subset_union_right)⟩
  · intro S hS T hT hne
    rcases mem_union.mp hS with hS | hS <;> rcases mem_union.mp hT with hT | hT
    · exact hP.2.1 hS hT hne
    · exact hd S hS T hT
    · exact (hd T hT S hS).symm
    · exact hQ.2.1 hS hT hne
  · rw [union_biUnion,hP.2.2,hQ.2.2]

lemma connected_partition (A : Finset (Fin n)) (hA : A.Nonempty) {q : ℝ} (_hq : 0 ≤ q) :
    ∃P : Finset (Finset (Fin n)), VertexPartition A P ∧
      (∀B ∈ P, G.EdgeConnectedReal B q) ∧
      ((G.inducedEdges A).card : ℝ)-(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) ≤ q*((P.card : ℝ)-1) := by
  induction A using Finset.strongInductionOn with
  | _ A ih =>
    by_cases hconn : G.EdgeConnectedReal A q
    · exact ⟨{A},vertexPartition_singleton hA,by simpa,by simp⟩
    · obtain ⟨S,hSne,hSA,hcut⟩ : ∃S, S.Nonempty ∧ S ⊂ A ∧
          ((G.cut (G.inducedEdges A) S).card : ℝ) < q := by
        simp only [EdgeConnectedReal,not_forall,not_le] at hconn
        obtain ⟨S,hSne,hSA,hcut⟩ := hconn
        exact ⟨S,hSne,hSA,hcut⟩
      have hRA : A\S ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro heq
        obtain ⟨u,hu⟩ := hSne
        have : u ∈ A\S := heq.symm ▸ hSA.subset hu
        exact (mem_sdiff.mp this).2 hu
      have hRne : (A\S).Nonempty := by
        apply sdiff_nonempty.mpr
        intro hh
        exact (Finset.ssubset_iff_subset_ne.mp hSA).2 (Subset.antisymm hSA.subset hh)
      obtain ⟨P,hP,hPc,hPb⟩ := ih S hSA hSne
      obtain ⟨Q,hQ,hQc,hQb⟩ := ih (A\S) hRA hRne
      obtain ⟨hPQ,hdis⟩ := vertexPartition_union hP hQ (disjoint_sdiff_self_right)
      have hcover : S ∪ (A\S) = A := union_sdiff_of_subset hSA.subset
      rw [hcover] at hPQ
      refine ⟨P∪Q,hPQ,?_,?_⟩
      · intro B hB
        rcases mem_union.mp hB with hB | hB
        · exact hPc B hB
        · exact hQc B hB
      · rw [sum_union hdis,card_union_of_disjoint hdis,Nat.cast_add]
        have he := G.cut_internal_split hSA.subset
        linarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma partition_point_mass {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) (v : Fin n) :
    (∑B ∈ P, if v ∈ B then (1:ℝ) else 0) = if v ∈ A then (1:ℝ) else 0 := by
  by_cases hv : v ∈ A
  · obtain ⟨B,hB,hvB⟩ := mem_biUnion.mp (hP.2.2.symm ▸ hv)
    rw [ite_eq_left hv,sum_eq_single B]
    · exact ite_eq_left hvB
    · intro C hC hCB
      have hvC : v ∉ C := fun hh => Finset.disjoint_left.mp (hP.2.1 hC hB hCB) hh hvB
      simp [hvC]
    · exact fun hh => (hh hB).elim
  · rw [ite_eq_right hv]
    apply sum_eq_zero
    intro B hB
    exact ite_eq_right (fun hh => hv ((hP.1 B hB).2 hh))

lemma volume_partition {A R : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hP : VertexPartition A P) : (∑B ∈ P, G.volume R B) = G.volume R A := by
  simp only [volume]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,sum_add_distrib]
  rw [partition_point_mass hP,partition_point_mass hP]

lemma volume_eq_boundary {A B : Finset (Fin n)} (hBA : B ⊆ A) :
    G.volume A B = ((G.cut (G.inducedEdges A) B).card : ℝ)+2*(G.inducedEdges B).card := by
  have hcard (E : Finset (Fin m)) : (E.card : ℝ) = ∑e : Fin m, if e ∈ E then (1:ℝ) else 0 := by simp
  rw [hcard,hcard,mul_sum,← sum_add_distrib]
  simp only [volume,inducedEdges,sum_filter]
  apply sum_congr rfl
  intro e he
  simp only [endpointMass,cut,mem_filter,mem_univ,true_and]
  have hl := hBA (x := G.left e)
  have hr := hBA (x := G.right e)
  by_cases hlA : G.left e ∈ A <;> by_cases hrA : G.right e ∈ A <;>
    by_cases hlB : G.left e ∈ B <;> by_cases hrB : G.right e ∈ B <;>
      norm_num [*] at *

lemma cut_complement_in {A B : Finset (Fin n)} (_hBA : B ⊆ A) :
    G.cut (G.inducedEdges A) (A\B) = G.cut (G.inducedEdges A) B := by
  ext e
  simp only [cut,mem_filter,mem_inducedEdges,mem_sdiff]
  tauto

lemma outside_connected_partition {A T : Finset (Fin n)} {k : ℝ}
    (hk : 0 < k) (hconn : G.EdgeConnectedReal A k) (hT : T.Nonempty) (hTA : T ⊂ A) :
    ∃P : Finset (Finset (Fin n)), VertexPartition (A\T) P ∧
      (∀B ∈ P, G.EdgeConnectedReal B (k/4)) ∧
      (P.card : ℝ)*k ≤ 2*(G.cut (G.inducedEdges A) T).card := by
  have hR : (A\T).Nonempty := by
    apply sdiff_nonempty.mpr
    intro hh
    exact (Finset.ssubset_iff_subset_ne.mp hTA).2 (Subset.antisymm hTA.subset hh)
  obtain ⟨P,hP,hPc,hcost⟩ := G.connected_partition (A\T) hR (by positivity : 0 ≤ k/4)
  have hBA : ∀B ∈ P, B ⊆ A := fun B hB => ((hP.1 B hB).2).trans sdiff_subset
  have hcuts : (P.card : ℝ)*k ≤ ∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ) := by
    calc
      _ = ∑B ∈ P, k := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro B hB
        apply hconn B (hP.1 B hB).1
        refine Finset.ssubset_iff_subset_ne.mpr ⟨hBA B hB,?_⟩
        intro heq
        obtain ⟨v,hv⟩ := hT
        have hh := (hP.1 B hB).2 (heq.symm ▸ hTA.subset hv)
        exact (mem_sdiff.mp hh).2 hv
  have hvol : (∑B ∈ P, ((G.cut (G.inducedEdges A) B).card : ℝ))+
      2*(∑B ∈ P, ((G.inducedEdges B).card : ℝ)) =
      ((G.cut (G.inducedEdges A) T).card : ℝ)+2*(G.inducedEdges (A\T)).card := by
    calc
      _ = ∑B ∈ P, G.volume A B := by
        rw [mul_sum,← sum_add_distrib]
        exact sum_congr rfl (fun B hB => (G.volume_eq_boundary (hBA B hB)).symm)
      _ = G.volume A (A\T) := G.volume_partition hP
      _ = _ := by rw [G.volume_eq_boundary sdiff_subset,G.cut_complement_in hTA.subset]
  refine ⟨P,hP,hPc,?_⟩
  nlinarith

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m h : ℕ} (G : MultiGraph n m)

lemma routed_variation_lower {R L : Finset (Fin n)} {q a b : ℝ}
    (f : Fin n → ℝ) (hab : a ≤ b) (hconn : G.EdgeConnectedReal R q)
    (hu : ∃u ∈ R, u ∈ L ∧ f u ≤ a) (hv : ∃v ∈ R, b ≤ f v)
    (hprotect : ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ L ∧ G.right e ∉ L) ∨ (G.right e ∈ L ∧ G.left e ∉ L)) →
      b ≤ f (G.left e) ∧ b ≤ f (G.right e)) :
    q*(b-a) ≤ ∑e ∈ G.inducedEdges L,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  have hh := cut_range_bound (k := q) (fun e : G.inducedEdges L => G.left e)
    (fun e : G.inducedEdges L => G.right e) (fun v => clamp a b (f v)) hab
  rw [← Finset.sum_coe_sort]
  apply hh
  intro t ht
  let S := R.filter (fun v => v ∈ L ∧ f v < t)
  have hSR : S ⊆ R := filter_subset _ _
  have hSn : S.Nonempty := by
    obtain ⟨u,huR,huL,hu⟩ := hu
    exact ⟨u,mem_filter.mpr ⟨huR,huL,lt_of_le_of_lt hu ht.1⟩⟩
  have hSproper : S ⊂ R := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSR,?_⟩
    intro heq
    obtain ⟨v,hvR,hv⟩ := hv
    have hh := (mem_filter.mp (heq.symm ▸ hvR)).2.2
    linarith [ht.2]
  have hc := hconn S hSn hSproper
  have hedge : ∀e ∈ G.cut (G.inducedEdges R) S, e ∈ G.inducedEdges L ∧
      ((f (G.left e)<t ∧ ¬ f (G.right e)<t) ∨
       (f (G.right e)<t ∧ ¬f (G.left e)<t)) := by
    intro e he
    obtain ⟨heR,hcut⟩ := mem_filter.mp he
    obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp heR
    rcases hcut with hcut | hcut
    · have hl := (mem_filter.mp hcut.1).2
      have hrL : G.right e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inl ⟨hl.1,hh⟩)).1
        linarith [ht.2,hl.2]
      have hr : ¬f (G.right e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hrR,hrL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hl.1,hrL⟩,Or.inl ⟨hl.2,hr⟩⟩
    · have hr := (mem_filter.mp hcut.1).2
      have hlL : G.left e ∈ L := by
        by_contra hh
        have hp := (hprotect e heR (Or.inr ⟨hr.1,hh⟩)).2
        linarith [ht.2,hr.2]
      have hl : ¬f (G.left e)<t := fun hh => hcut.2 (mem_filter.mpr ⟨hlR,hlL,hh⟩)
      exact ⟨(G.mem_inducedEdges _ _).mpr ⟨hlL,hr.1⟩,Or.inr ⟨hr.2,hl⟩⟩
  have hcard : (G.cut (G.inducedEdges R) S).card ≤
      (univ.filter (fun e : G.inducedEdges L =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))).card := by
    let F (e : G.cut (G.inducedEdges R) S) :
        (univ.filter (fun e : G.inducedEdges L =>
          (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
          (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) :=
      ⟨⟨e.val,(hedge e.val e.property).1⟩,by
        simp only [mem_filter,mem_univ,true_and,clamp_lt_iff ht]
        exact (hedge e.val e.property).2⟩
    apply Finset.card_le_card_of_injective (f := F)
    intro e f hh
    apply Subtype.ext
    exact congrArg (fun x => x.val.val) hh
  exact hc.trans (by exact_mod_cast hcard)

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Records
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open scoped Classical
open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy
noncomputable section
open Finset StrongThinTree.Geometry
variable {n h : ℕ} (H : Hierarchy n)

lemma mem_domain {A B : Finset (Fin n)} {P : Finset (Finset (Fin n))} :
    B ∈ H.domain A P ↔ B ∈ H.nodes ∧ B ⊆ A ∧ ∀S ∈ P, ¬B ⊆ S := by
  simp [domain]

lemma mem_leaves {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    v ∈ H.leaves A P ↔ v ∈ A ∧ ∀S ∈ P, v ∉ S := by
  simp [leaves]

lemma root_mem_domain {A : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hP : ∀S ∈ P, S ⊂ A) : A ∈ H.domain A P := by
  apply H.mem_domain.mpr
  refine ⟨hA,Subset.refl _,?_⟩
  intro S hS hh
  have hs := hP S hS
  exact (Finset.ssubset_iff_subset_ne.mp hs).2 (Subset.antisymm hs.subset hh)

lemma singleton_domain_iff {A : Finset (Fin n)} {P : Finset (Finset (Fin n))} {v : Fin n} :
    {v} ∈ H.domain A P ↔ v ∈ H.leaves A P := by
  simp only [mem_domain,H.singletons,true_and,singleton_subset_iff,mem_leaves]

lemma domain_root_test {A B : Finset (Fin n)} {P Q : Finset (Finset (Fin n))}
    (hA : A ∈ H.nodes) (hB : B ∈ H.nodes)
    (hP : ∀S ∈ P, S ⊂ A) (hQ : ∀S ∈ Q, S ⊂ B) :
    (H.domain A P ∩ H.domain B Q).Nonempty ↔
      A ∈ H.domain B Q ∨ B ∈ H.domain A P := by
  constructor
  · rintro ⟨C,hC⟩
    obtain ⟨hCA,hCB⟩ := mem_inter.mp hC
    obtain ⟨hCnode,hCA,hCP⟩ := H.mem_domain.mp hCA
    obtain ⟨_,hCB,hCQ⟩ := H.mem_domain.mp hCB
    rcases H.laminar A hA B hB with hAB | hBA | hdis
    · left
      apply H.mem_domain.mpr
      exact ⟨hA,hAB,fun S hS hh => hCQ S hS (hCA.trans hh)⟩
    · right
      apply H.mem_domain.mpr
      exact ⟨hB,hBA,fun S hS hh => hCP S hS (hCB.trans hh)⟩
    · obtain ⟨v,hv⟩ := H.nonempty C hCnode
      exact (Finset.disjoint_left.mp hdis (hCA hv) (hCB hv)).elim
  · rintro (hAB | hBA)
    · exact ⟨A,mem_inter.mpr ⟨H.root_mem_domain hA hP,hAB⟩⟩
    · exact ⟨B,mem_inter.mpr ⟨hBA,H.root_mem_domain hB hQ⟩⟩

end
end StrongThinTree.MultiGraph.Hierarchy

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Selection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV uU uI

section
open scoped Classical
open Matrix

namespace StrongThinTree.AssignedAccounting
noncomputable section

lemma base_le_width (a : Bool) {R δ : ℝ} (hR : 0 ≤ R) (hδ : 0 ≤ δ) :
    base a R δ ≤ R := by
  have hh : max (R-3*δ) 0 ≤ R := max_le (by linarith) hR
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;> linarith

lemma base_discard (a : Bool) {R δ : ℝ} (hR : R ≤ 0) (hδ : 0 ≤ δ) :
    base a R δ = 0 := by
  have : max (R-3*δ) 0 = 0 := max_eq_right (by linarith)
  simp [base,this]

lemma fresh_lower {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) :
    (5/6:ℝ)*δ ≤ fresh δ ε := by dsimp [fresh] <;> linarith

lemma avoiding_carve {δ ε R R₁ R₂ : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-2*δ) :
    base true R δ + theta*δ ≤ base true R₁ δ+base true R₂ δ+fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := fresh_lower hδ hε
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,↓reduceIte,hr,theta]
  linarith

lemma dense_carve {δ ε R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hM : 0 ≤ M)
    (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L-4*δ)
    (hdense : 3*L ≤ M*δ) (hcount : 765*δ ≤ M*δ) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+M*fresh δ ε := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have hf := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hM
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  nlinarith

lemma sparse_carve {δ R R₁ R₂ L M : ℝ}
    (hδ : 0 ≤ δ) (hR : 512*δ ≤ R) (hsum : R₁+R₂ = R-L)
    (hwidth : 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) :
    base false R δ+theta*M*δ ≤
      base false R₁ δ+base false R₂ δ+base false (L-2*δ) δ+base true L δ := by
  have h1 := le_max_left (R₁-3*δ) 0
  have h2 := le_max_left (R₂-3*δ) 0
  have h3 := le_max_left (L-2*δ-3*δ) 0
  have h4 := le_max_left (L-3*δ) 0
  have hr : max (R-3*δ) 0 = R-3*δ := max_eq_left (by linarith)
  simp only [base,Bool.false_eq_true,↓reduceIte,div_one,hr,theta]
  linarith

lemma shrink_cost (a : Bool) {R δ ε : ℝ} (hδ : 0 ≤ δ)
    (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) :
    0 ≤ base a R δ-base a (R-514*δ) ε ∧
    base a R δ-base a (R-514*δ) ε ≤
      256*(base a R ε-base a R δ) := by
  have hthreshold : R-514*δ-3*ε ≤ R-3*δ := by linarith
  have hmono := max_le_max_right (0:ℝ) hthreshold
  have hr : max (R-3*δ) 0-max (R-514*δ-3*ε) 0 ≤
      256*(max (R-3*ε) 0-max (R-3*δ) 0) := by
    by_cases hh : R ≤ 3*δ
    · rw [max_eq_right (by linarith : R-3*δ ≤ 0)]
      have h0 := le_max_right (R-514*δ-3*ε) 0
      have h1 := le_max_right (R-3*ε) 0
      linarith
    · have hd : 3*δ ≤ R := (not_le.mp hh).le
      rw [max_eq_left (by linarith : 0 ≤ R-3*δ),
        max_eq_left (by linarith : 0 ≤ R-3*ε)]
      have hlo := le_max_left (R-514*δ-3*ε) 0
      linarith
  cases a <;> simp only [base,Bool.false_eq_true,↓reduceIte,div_one] <;>
    constructor <;> linarith

lemma border_payment {δ ε B D : ℝ}
    (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536) (hB : 0 ≤ B)
    (hD : D ≤ B*δ/2) : theta*B*δ+D ≤ B*fresh δ ε := by
  have hh := mul_le_mul_of_nonneg_left (fresh_lower hδ hε) hB
  have hnon : 0 ≤ B*δ := mul_nonneg hB hδ
  dsimp [theta]
  nlinarith

end
end StrongThinTree.AssignedAccounting

namespace StrongThinTree.AssignedSelection
noncomputable section
open Finset

lemma large_neighbor_class {U : Type uU} {I : Type uI} [DecidableEq U] [DecidableEq I]
    (A : Finset U) (P : Finset I) (R : U → I → Prop) [DecidableRel R]
    (hP : P.Nonempty) (hcover : ∀u ∈ A, ∃i ∈ P, R u i)
    {q O : ℝ} (hq : 0 < q) (hO : 0 < O)
    (hparts : q*(P.card : ℝ) ≤ 2*O) (hmany : 1536*O ≤ q*(A.card : ℝ)) :
    ∃i ∈ P, 768 ≤ (A.filter (fun u => R u i)).card := by
  obtain ⟨i,hi,hmax⟩ := P.exists_max_image (fun i => (A.filter (fun u => R u i)).card) hP
  have hcover' : A = P.biUnion (fun i => A.filter (fun u => R u i)) := by
    ext u
    simp only [mem_biUnion,mem_filter]
    constructor
    · intro hu
      obtain ⟨j,hj,hr⟩ := hcover u hu
      exact ⟨j,hj,hu,hr⟩
    · rintro ⟨j,hj,hu,hr⟩
      exact hu
  have hc : A.card ≤ P.card*(A.filter (fun u => R u i)).card := by
    calc
      A.card = (P.biUnion (fun i => A.filter (fun u => R u i))).card := congrArg card hcover'
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u j)).card := card_biUnion_le
      _ ≤ ∑j ∈ P, (A.filter (fun u => R u i)).card := sum_le_sum (fun j hj => hmax j hj)
      _ = _ := by simp
  have hc' : (A.card : ℝ) ≤ (P.card : ℝ)*(A.filter (fun u => R u i)).card := by exact_mod_cast hc
  have hm := mul_le_mul_of_nonneg_left hc' hq.le
  have hp := mul_le_mul_of_nonneg_right hparts
    (Nat.cast_nonneg (A.filter (fun u => R u i)).card : (0:ℝ) ≤ _)
  have hn : (768:ℝ) ≤ (A.filter (fun u => R u i)).card := by nlinarith
  exact ⟨i,hi,by exact_mod_cast hn⟩

lemma radial_range {r₁ r₂ p q s₀ u₀ s u δ : ℝ}
    (hδ : 0 < δ) (hp0 : p ≤ s₀) (hq0 : s₀ ≤ q)
    (hu₀lo : r₁+256*δ < u₀) (hu₀hi : u₀ < r₂-256*δ)
    (hnear0 : |u₀-s₀| < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hnear : |u-s| < δ)
    (hout : ¬(max r₁ p-δ < u ∧ u < min r₂ q+δ)) :
    255*δ ≤ min r₂ q-max r₁ p := by
  obtain ⟨hn0a,hn0b⟩ := abs_lt.mp hnear0
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have hslo : r₁+255*δ < s₀ := by linarith
  have hshi : s₀ < r₂-255*δ := by linarith
  have ha : max r₁ p ≤ s₀ := max_le (by linarith) hp0
  have hb : s₀ ≤ min r₂ q := le_min (by linarith) hq0
  by_cases hul : max r₁ p-δ < u
  · have huh : min r₂ q+δ ≤ u := le_of_not_gt (fun hh => hout ⟨hul,hh⟩)
    have hclip : r₂ ≤ q := by
      by_contra hh
      rw [min_eq_right (not_le.mp hh).le] at huh
      linarith
    rw [min_eq_left hclip]
    linarith
  · have hul : u ≤ max r₁ p-δ := not_lt.mp hul
    have hclip : p ≤ r₁ := by
      by_contra hh
      rw [max_eq_right (not_le.mp hh).le] at hul
      linarith
    rw [max_eq_left hclip]
    linarith

lemma interior_neighbor_in_range {r₁ r₂ p q s u δ : ℝ}
    (hδ : 0 < δ) (hp : p ≤ s) (hq : s ≤ q)
    (hulo : r₁+256*δ < u) (huhi : u < r₂-256*δ)
    (hnear : |u-s| < δ) :
    max r₁ p ≤ min r₂ q ∧ max r₁ p-δ < u ∧ u < min r₂ q+δ := by
  obtain ⟨hna,hnb⟩ := abs_lt.mp hnear
  have ha : max r₁ p ≤ s := max_le (by linarith) hp
  have hb : s ≤ min r₂ q := le_min (by linarith) hq
  exact ⟨ha.trans hb,by linarith,by linarith⟩

lemma dense_count {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hdense : 3*L ≤ M*δ) : 765*δ ≤ M*δ := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · linarith

lemma sparse_width {δ L M N : ℝ} (hδ : 0 ≤ δ) (hN : 768 ≤ N)
    (hdich : N ≤ M ∨ 255*δ ≤ L) (hsparse : M*δ ≤ 3*L) : 255*δ ≤ L := by
  rcases hdich with hh | hh
  · have := mul_le_mul_of_nonneg_right hh hδ
    nlinarith
  · exact hh

end
end StrongThinTree.AssignedSelection

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Profiles
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric profiles. -/

section

noncomputable section

namespace AlgorithmicThinTrees.MetricProfiles

open Finset Set

section Profiles

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

omit [Fintype V] in
lemma profile_mem (x : V) : profile x ∈ polytope :=
  subset_convexHull ℝ _ (Set.mem_range_self x)

omit [Fintype V] in
lemma polytope_convex : Convex ℝ (polytope (V := V)) := convex_convexHull ℝ _

lemma profile_norm_sub (x y : V) : ‖profile x - profile y‖ = dist x y := by
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg dist_nonneg).2
    intro z
    simp only [Pi.sub_apply, profile, Real.norm_eq_abs]
    apply abs_sub_le_iff.2
    constructor
    · linarith [dist_triangle x y z]
    · have h := dist_triangle y x z
      rw [dist_comm y x] at h
      linarith
  · have h := norm_le_pi_norm (profile x - profile y) y
    simpa [profile, Real.norm_eq_abs, abs_of_nonneg dist_nonneg] using h

omit [PseudoMetricSpace V] in
lemma norm_coordinate_convex (c : V → ℝ) (i : V) :
    Convex ℝ {x : V → ℝ | ‖x - c‖ ≤ x i} := by
  intro x hx y hy a b ha hb hab
  change ‖a • x + b • y - c‖ ≤ (a • x + b • y) i
  have heq : a • x + b • y - c = a • (x - c) + b • (y - c) := by
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination c j * hab
  rw [heq]
  calc
    ‖a • (x - c) + b • (y - c)‖ ≤ ‖a • (x - c)‖ + ‖b • (y - c)‖ := norm_add_le _ _
    _ = a * ‖x - c‖ + b * ‖y - c‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * x i + b * y i := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = (a • x + b • y) i := rfl

theorem radius_eq_coordinate {q : V → ℝ} (hq : q ∈ polytope) (x : V) :
    ‖q - profile x‖ = q x := by
  have hupper : ‖q - profile x‖ ≤ q x := by
    apply convexHull_min (t := {y : V → ℝ | ‖y - profile x‖ ≤ y x}) ?_
      (norm_coordinate_convex (profile x) x) hq
    rintro _ ⟨y, rfl⟩
    exact (profile_norm_sub y x).le
  have hlower : q x ≤ ‖q - profile x‖ := by
    have h := norm_le_pi_norm (q - profile x) x
    simp only [Pi.sub_apply, profile, dist_self, sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  exact le_antisymm hupper hlower

end Profiles

section Double

variable (V : Type*) [Fintype V] [PseudoMetricSpace V]

variable {V}

lemma opposite_dist (x : V) : dist (plus x) (minus x) = commonRadius V := by
  change doubledDist _ _ = _
  simp [doubledDist, plus, minus]

lemma profile_opposite_sum (x : V) (a : Doubled V) :
    profile a (plus x) + profile a (minus x) = commonRadius V := by
  change doubledDist a _ + doubledDist a _ = _
  rcases a with ⟨s, y⟩
  cases s <;> simp [doubledDist, plus, minus]

lemma opposite_coordinate_sum {q : Doubled V → ℝ}
    (hq : q ∈ polytope) (x : V) : q (plus x) + q (minus x) = commonRadius V := by
  have hconv : Convex ℝ {q : Doubled V → ℝ |
      q (plus x) + q (minus x) = commonRadius V} := by
    intro q hq r hr a b _ _ hab
    change (a • q + b • r) (plus x) + (a • q + b • r) (minus x) = _
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    change q (plus x) + q (minus x) = commonRadius V at hq
    change r (plus x) + r (minus x) = commonRadius V at hr
    calc
      _ = a * (q (plus x) + q (minus x)) +
          b * (r (plus x) + r (minus x)) := by ring
      _ = a * commonRadius V + b * commonRadius V := by rw [hq, hr]
      _ = commonRadius V := by rw [← add_mul, hab, one_mul]
  exact convexHull_min (by rintro _ ⟨a, rfl⟩; exact profile_opposite_sum x a) hconv hq

theorem opposite_radii {q : Doubled V → ℝ} (hq : q ∈ polytope) (x : V) :
    ‖q - profile (plus x)‖ + ‖q - profile (minus x)‖ = commonRadius V := by
  rw [radius_eq_coordinate hq, radius_eq_coordinate hq]
  exact opposite_coordinate_sum hq x

end Double

section Segments

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma mix_sub_mix (q r : E) (t s : ℝ) :
    mix q r t - mix q r s = (t - s) • (r - q) := by
  unfold mix
  module

lemma segment_distance (q r : E) (t s : ℝ) :
    ‖mix q r t - mix q r s‖ = |t - s| * ‖r - q‖ := by
  rw [mix_sub_mix, norm_smul, Real.norm_eq_abs]

end Segments

section RadialMotion

variable {V : Type*} [Fintype V] [PseudoMetricSpace V]

lemma mix_mem {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : mix q r t ∈ polytope :=
  polytope_convex hq hr (sub_nonneg.mpr ht.2) ht.1 (by ring)

lemma radius_mix {q r : V → ℝ} (hq : q ∈ polytope) (hr : r ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q r t - profile x‖ = (1 - t) * ‖q - profile x‖ + t * ‖r - profile x‖ := by
  rw [radius_eq_coordinate (mix_mem hq hr ht), radius_eq_coordinate hq,
    radius_eq_coordinate hr]
  rfl

lemma inward_radius {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q (profile (plus x)) t - profile (plus x)‖ =
      (1 - t) * ‖q - profile (plus x)‖ := by
  rw [radius_mix hq (profile_mem _) _ ht]
  simp

lemma inward_distance (q : Doubled V → ℝ) (x : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖mix q (profile (plus x)) t - q‖ = t * ‖q - profile (plus x)‖ := by
  simpa only [mix_zero, sub_zero, abs_of_nonneg ht, norm_sub_rev (profile (plus x)) q]
    using segment_distance q (profile (plus x)) t 0

lemma outward_radius {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖mix q (profile (minus x)) t - profile (plus x)‖ =
      ‖q - profile (plus x)‖ + t * (commonRadius V - ‖q - profile (plus x)‖) := by
  rw [radius_mix hq (profile_mem _) _ ht, profile_norm_sub, dist_comm, opposite_dist]
  ring

lemma outward_distance {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {t : ℝ} (ht : 0 ≤ t) :
    ‖mix q (profile (minus x)) t - q‖ =
      t * (commonRadius V - ‖q - profile (plus x)‖) := by
  have h : ‖q - profile (minus x)‖ = commonRadius V - ‖q - profile (plus x)‖ := by
    linarith [opposite_radii hq x]
  have hm := segment_distance q (profile (minus x)) t 0
  simpa only [mix_zero, sub_zero, abs_of_nonneg ht, norm_sub_rev (profile (minus x)) q, h]
    using hm

theorem radial_motion {q : Doubled V → ℝ} (hq : q ∈ polytope)
    (x : V) {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) (commonRadius V)) :
    ∃ z ∈ polytope, ‖z - profile (plus x)‖ = u ∧
      ‖z - q‖ = |u - ‖q - profile (plus x)‖| := by
  let ρ := ‖q - profile (plus x)‖
  have hρ : 0 ≤ ρ := norm_nonneg _
  by_cases h : u ≤ ρ
  · by_cases hz : ρ = 0
    · have hu0 : u = 0 := le_antisymm (hz ▸ h) hu.1
      refine ⟨q, hq, ?_, ?_⟩
      · exact hz.trans hu0.symm
      · simp only [sub_self, norm_zero]
        change 0 = |u - ρ|
        simp [hz, hu0]
    · have hpos : 0 < ρ := lt_of_le_of_ne hρ (Ne.symm hz)
      let t := (ρ - u) / ρ
      have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr h) hρ
      have ht1 : t ≤ 1 := (div_le_one hpos).2 (by linarith [hu.1])
      have htr : t * ρ = ρ - u := div_mul_cancel₀ _ hz
      refine ⟨mix q (profile (plus x)) t, mix_mem hq (profile_mem _) ⟨ht0, ht1⟩, ?_, ?_⟩
      · rw [inward_radius hq x ⟨ht0, ht1⟩]
        change (1 - t) * ρ = u
        nlinarith
      · rw [inward_distance q x ht0]
        change t * ρ = |u - ρ|
        rw [htr, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
  · have hlt : ρ < u := lt_of_not_ge h
    have hpos : 0 < commonRadius V - ρ := by linarith [hu.2]
    let t := (u - ρ) / (commonRadius V - ρ)
    have ht0 : 0 ≤ t := div_nonneg (sub_pos.mpr hlt).le hpos.le
    have ht1 : t ≤ 1 := (div_le_one hpos).2 (by linarith [hu.2])
    have htr : t * (commonRadius V - ρ) = u - ρ :=
      div_mul_cancel₀ _ (ne_of_gt hpos)
    refine ⟨mix q (profile (minus x)) t, mix_mem hq (profile_mem _) ⟨ht0, ht1⟩, ?_, ?_⟩
    · rw [outward_radius hq x ⟨ht0, ht1⟩]
      change ρ + t * (commonRadius V - ρ) = u
      rw [htr]
      ring
    · rw [outward_distance hq x ht0]
      change t * (commonRadius V - ρ) = |u - ρ|
      rw [htr, abs_of_nonneg (sub_nonneg.mpr hlt.le)]

end RadialMotion

end AlgorithmicThinTrees.MetricProfiles

end 
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CompactCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric compact charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset

section RadialLaws
variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_self (q : J → ℝ) : normDistance q q = 0 := by
  simp [normDistance]

omit [PseudoMetricSpace J] in
lemma normDistance_triangle (q r s : J → ℝ) :
    normDistance q s ≤ normDistance q r + normDistance r s := by
  simpa only [normDistance, dist_eq_norm] using dist_triangle q r s

omit [Fintype J] in
lemma isProfile_inPolytope {q : J → ℝ} (hq : isProfile q) : inPolytope q := by
  obtain ⟨j,rfl⟩ := hq
  exact profile_mem j

omit [PseudoMetricSpace J] in
lemma segment_formula (q r : J → ℝ) (t : ℝ) :
    (fun j => q j+t*(r j-q j)) = mix q r t := by
  ext j
  simp only [mix, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

lemma inPolytope_segment {q r : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    inPolytope (fun j => q j+t*(r j-q j)) := by
  rw [segment_formula]
  exact mix_mem hq hr ht

lemma isProfile_radial_affine {q r c : J → ℝ} (hq : inPolytope q) (hr : inPolytope r)
    (hc : isProfile c) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    normDistance (fun j => q j+t*(r j-q j)) c =
      normDistance q c+t*(normDistance r c-normDistance q c) := by
  obtain ⟨j,rfl⟩ := hc
  rw [segment_formula]
  change ‖mix q r t-profile j‖ = _
  rw [radius_mix hq hr j ht]
  unfold normDistance
  ring
end RadialLaws

namespace RadialShell
variable {V : Type*} {J : Type*} [Fintype J] [PseudoMetricSpace J]

lemma support_ball (X : V → J → ℝ) (v : V) (r : ℝ) :
    (ball v r).support X = {w | inPolytope w ∧ normDistance w (X v) < r} := by
  ext w
  simp [support,ball]

lemma support_hollow (X : V → J → ℝ) (v : V) (a b : ℝ) :
    (hollow v a b).support X = {w | inPolytope w ∧ a<normDistance w (X v) ∧ normDistance w (X v)<b} := by
  ext w
  simp only [support,hollow,Set.mem_ofPred_eq,Bool.false_eq_true,false_or]
  tauto

lemma valid_support_nonempty {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    {H : RadialShell V} (hH : H.Valid X) : (H.support X).Nonempty := by
  obtain ⟨v,hv⟩ := hH.2.2.2.2
  let R := normDistance (X v) (X H.center)
  let q := (H.inner+H.outer)/2
  have hq : H.inner<q ∧ q<H.outer := by dsimp [q]; constructor <;> linarith [hH.2.1]
  have hR : 0 < R := lt_of_lt_of_le (lt_of_le_of_lt hH.1 hH.2.1) hv
  let t := q/R
  have ht : t ∈ Set.Icc (0:ℝ) 1 :=
    ⟨div_nonneg (le_trans hH.1 hq.1.le) hR.le,
      (div_le_one hR).mpr (le_trans hq.2.le hv)⟩
  let w := fun j => X H.center j+t*(X v j-X H.center j)
  have hw : normDistance w (X H.center) = q := by
    rw [isProfile_radial_affine (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) (hX _) ht,
      normDistance_self, sub_zero, zero_add]
    exact div_mul_cancel₀ _ hR.ne'
  exact ⟨w,inPolytope_segment (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _)) ht,
    hw ▸ hq.2,Or.inr (hw ▸ hq.1)⟩

lemma restriction_subset (X : V → J → ℝ) (H : RadialShell V)
    {a b : ℝ} (ha : H.inner ≤ a) (hb : b ≤ H.outer) :
    (hollow H.center a b).support X ⊆ H.support X := by
  intro w hw
  rw [support_hollow] at hw
  exact ⟨hw.1,lt_of_lt_of_le hw.2.2 hb,Or.inr (lt_of_le_of_lt ha hw.2.1)⟩

lemma ball_subset_of_radial_margin (X : V → J → ℝ) (H : RadialShell V)
    (z : V) {δ : ℝ} (hlo : H.inner+δ ≤ normDistance (X z) (X H.center))
    (hhi : normDistance (X z) (X H.center) ≤ H.outer-δ) :
    (ball z δ).support X ⊆ H.support X := by
  intro w hw
  rw [support_ball] at hw
  have htri := normDistance_triangle w (X z) (X H.center)
  have htri' := normDistance_triangle (X z) w (X H.center)
  rw [normDistance_comm (X z) w] at htri'
  exact ⟨hw.1,by linarith [hw.2],Or.inr (by linarith [hw.2])⟩

lemma ball_disjoint_hollow_lower (X : V → J → ℝ) (x z : V) {δ q a : ℝ}
    (hq : q+δ ≤ normDistance (X z) (X x)) :
    Disjoint ((ball z δ).support X) ((hollow x a q).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle (X z) w (X x)
  rw [normDistance_comm (X z) w] at ht
  linarith [hw.2,hz.2.2]

lemma ball_disjoint_hollow_upper (X : V → J → ℝ) (x z : V) {δ q b : ℝ}
    (hq : normDistance (X z) (X x)+δ ≤ q) :
    Disjoint ((ball z δ).support X) ((hollow x q b).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_ball] at hw
  rw [support_hollow] at hz
  have ht := normDistance_triangle w (X z) (X x)
  linarith [hw.2,hz.2.1]

lemma concentric_disjoint (X : V → J → ℝ) (x : V) {a b c d : ℝ} (hbc : b ≤ c) :
    Disjoint ((hollow x a b).support X) ((hollow x c d).support X) := by
  rw [Set.disjoint_left]
  intro w hw hz
  rw [support_hollow] at hw hz
  linarith [hw.2.2,hz.2.1]

lemma disjoint_balls_distance {X : V → J → ℝ} (hX : ∀v, isProfile (X v))
    (u v : V) {δ : ℝ} (hd : Disjoint ((ball u δ).support X) ((ball v δ).support X)) :
    2*δ ≤ normDistance (X u) (X v) := by
  by_contra hh
  have hh := not_le.mp hh
  let w := fun j => X u j+(1/2:ℝ)*(X v j-X u j)
  have hw := inPolytope_segment (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v))
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hu := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX u)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  have hv := isProfile_radial_affine (isProfile_inPolytope (hX u)) (isProfile_inPolytope (hX v)) (hX v)
    (show (1/2:ℝ) ∈ Set.Icc (0:ℝ) 1 by norm_num)
  simp only [normDistance_self,normDistance_comm (X v) (X u)] at hu hv
  have hwu : w ∈ (ball u δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w] <;> linarith⟩
  have hwv : w ∈ (ball v δ).support X := by
    rw [support_ball]; exact ⟨hw,by dsimp [w] <;> linarith⟩
  exact Set.disjoint_left.mp hd hwu hwv

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_AssignedGeometry
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric assigned geometry. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.CompactGeometry
noncomputable section
open Finset
open StrongThinTree.Geometry (clamp clamped_affine_disjoint_sum)

variable {J : Type*} [Fintype J] [PseudoMetricSpace J]

omit [PseudoMetricSpace J] in
lemma normDistance_nonneg (x y : J → ℝ) : 0 ≤ normDistance x y := norm_nonneg _

omit [PseudoMetricSpace J] in
lemma normDistance_reverse (x y z : J → ℝ) :
    |normDistance x z-normDistance y z| ≤ normDistance x y := by
  simpa only [normDistance,sub_sub_sub_cancel_right] using
    abs_norm_sub_norm_le (x-z) (y-z)

lemma profile_shell_edge_bound {I : Type*} [Fintype I]
    {x y : J → ℝ} (hx : inPolytope x) (hy : inPolytope y)
    (z : I → J → ℝ) (hz : ∀i, isProfile (z i)) (a b : I → ℝ)
    (hab : ∀i, a i ≤ b i)
    (hdis : ∀i j, i ≠ j → ∀w, inPolytope w →
      ¬(a i < normDistance w (z i) ∧ normDistance w (z i)<b i ∧
        a j < normDistance w (z j) ∧ normDistance w (z j)<b j)) :
    ∑i, |clamp (a i) (b i) (normDistance x (z i))-
      clamp (a i) (b i) (normDistance y (z i))| ≤ normDistance x y := by
  apply clamped_affine_disjoint_sum a b _ _ (normDistance_nonneg x y) hab
  · intro i
    simpa only [normDistance_comm y x] using normDistance_reverse y x (z i)
  · intro i j hij t ht hbad
    have htc : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1.le,ht.2.le⟩
    apply hdis i j hij (fun j => x j+t*(y j-x j)) (inPolytope_segment hx hy htc)
    simpa only [isProfile_radial_affine hx hy (hz i) htc,
      isProfile_radial_affine hx hy (hz j) htc] using hbad

lemma profile_radial_max {x z : Doubled J → ℝ} (hx : isProfile x) (hz : inPolytope z) :
    normDistance z x ≤ commonRadius J := by
  obtain ⟨⟨s,a⟩,rfl⟩ := hx
  have h := opposite_radii hz a
  cases s
  · change normDistance z (profile (minus a)) ≤ commonRadius J
    unfold normDistance
    linarith [norm_nonneg (z-profile (plus a))]
  · change normDistance z (profile (plus a)) ≤ commonRadius J
    unfold normDistance
    linarith [norm_nonneg (z-profile (minus a))]

lemma profile_radial_move {x z : Doubled J → ℝ} (hx : isProfile x) (hz : inPolytope z)
    {r : ℝ} (hr : 0 ≤ r) (hrmax : r ≤ commonRadius J) :
    ∃w : Doubled J → ℝ, inPolytope w ∧ normDistance w x = r ∧
      normDistance w z = |r-normDistance z x| := by
  obtain ⟨⟨s,a⟩,rfl⟩ := hx
  cases s
  · obtain ⟨w,hw,hwplus,hwz⟩ := radial_motion hz a
      (show commonRadius J-r ∈ Set.Icc (0:ℝ) (commonRadius J) from
        ⟨by linarith,by linarith⟩)
    have hwp := opposite_radii hw a
    have hzp := opposite_radii hz a
    refine ⟨w,hw,?_,?_⟩
    · change ‖w-profile (minus a)‖ = r
      linarith
    · change ‖w-z‖ = |r-‖z-profile (minus a)‖|
      rw [hwz]
      have heq : commonRadius J-r-‖z-profile (plus a)‖ =
          -(r-‖z-profile (minus a)‖) := by linarith
      rw [heq,abs_neg]
  · exact radial_motion hz a ⟨hr,hrmax⟩

namespace RadialShell
variable {V : Type*} {X : V → Doubled J → ℝ}

lemma ball_meets_radial {B : RadialShell V} (hX : ∀v, isProfile (X v))
    (hB : B.Valid X) (z : V) {δ : ℝ} (hδ : 0 < δ)
    (hlo : B.inner-δ < normDistance (X z) (X B.center))
    (hhi : normDistance (X z) (X B.center) < B.outer+δ) :
    ¬Disjoint ((ball z δ).support X) (B.support X) := by
  have hinterval : max B.inner (normDistance (X z) (X B.center)-δ) <
      min B.outer (normDistance (X z) (X B.center)+δ) := by
    rw [max_lt_iff,lt_min_iff,lt_min_iff]
    exact ⟨⟨hB.2.1,by linarith⟩,⟨by linarith,by linarith⟩⟩
  obtain ⟨r,hl,hr⟩ := exists_between hinterval
  have hlo' : B.inner < r := (le_max_left _ _).trans_lt hl
  have hhi' : r < B.outer := hr.trans_le (min_le_left _ _)
  have hradlo : normDistance (X z) (X B.center)-δ < r := (le_max_right _ _).trans_lt hl
  have hradhi : r < normDistance (X z) (X B.center)+δ := hr.trans_le (min_le_right _ _)
  obtain ⟨v,hv⟩ := hB.2.2.2.2
  have hmax : B.outer ≤ commonRadius J := hv.trans (profile_radial_max (hX _) (isProfile_inPolytope (hX v)))
  obtain ⟨w,hw,hwr,hwz⟩ := profile_radial_move (hX B.center) (isProfile_inPolytope (hX z))
    (hB.1.trans hlo'.le) (hhi'.le.trans hmax)
  have hwA : w ∈ (ball z δ).support X := by
    rw [support_ball]
    refine ⟨hw,?_⟩
    rw [hwz,abs_lt]
    constructor <;> linarith
  have hwB : w ∈ B.support X := ⟨hw,hwr ▸ hhi',Or.inr (hwr ▸ hlo')⟩
  exact fun hdis => Set.disjoint_left.mp hdis hwA hwB

end RadialShell
end
end AlgorithmicThinTrees.MetricProfiles.CompactGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_AssignedCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric assigned charging. -/

section

open scoped Classical

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)

namespace Record
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

lemma root_mem {B : Record n} (hB : B.Shape H) : B.owner ∈ B.conflict H :=
  H.root_mem_domain hB.1 (fun S hS => (hB.2 S hS).2)

lemma mem_leafSet {B : Record n} {v : Fin n} :
    v ∈ B.leafSet H ↔ v ∈ B.owner ∧ ∀S ∈ B.excluded, v ∉ S := H.mem_leaves

lemma mem_routing {B : Record n} {v : Fin n} :
    v ∈ B.routing ↔ v ∈ B.owner ∧ ∀S ∈ B.avoided.toFinset, v ∉ S := by
  cases heq : B.avoided <;> simp [routing,heq]

omit [PseudoMetricSpace Coord] in
lemma protected_routing_edges {B : Record n} (hB : B.Protected G X)
    {R : Finset (Fin n)} (hR : R ⊆ B.routing) :
    ∀e ∈ G.inducedEdges R,
      ((G.left e ∈ B.leafSet H ∧ G.right e ∉ B.leafSet H) ∨
       (G.right e ∈ B.leafSet H ∧ G.left e ∉ B.leafSet H)) →
      B.shell.outer ≤ normDistance (X (G.left e)) (X B.shell.center) ∧
      B.shell.outer ≤ normDistance (X (G.right e)) (X B.shell.center) := by
  have hex {u v : Fin n} (hu : u ∈ B.leafSet H) (hv : v ∈ B.routing)
      (hn : v ∉ B.leafSet H) : ∃S ∈ B.predecessors, u ∉ S ∧ v ∈ S := by
    obtain ⟨hu,hup⟩ := (mem_leafSet H).mp hu
    obtain ⟨hv,hva⟩ := mem_routing.mp hv
    have : ∃S ∈ B.excluded, v ∈ S := by
      by_contra hh
      push Not at hh
      exact hn ((mem_leafSet H).mpr ⟨hv,hh⟩)
    obtain ⟨S,hS,hvS⟩ := this
    have hSp : S ∈ B.predecessors := by
      rcases mem_union.mp hS with hh | hh
      · exact hh
      · exact (hva S hh hvS).elim
    exact ⟨S,hSp,hup S hS,hvS⟩
  intro e he hcross
  obtain ⟨hlR,hrR⟩ := (G.mem_inducedEdges _ _).mp he
  rcases hcross with hcross | hcross
  · obtain ⟨S,hS,hl,hr⟩ := hex hcross.1 (hR hrR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inr ⟨hr,hl⟩⟩)
  · obtain ⟨S,hS,hr,hl⟩ := hex hcross.1 (hR hlR) hcross.2
    exact hB S hS e (mem_filter.mpr ⟨mem_univ _,Or.inl ⟨hl,hr⟩⟩)

omit [PseudoMetricSpace Coord] in
lemma variation_lower {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    q*B.shell.width ≤ ∑e ∈ G.inducedEdges (B.leafSet H),
      |clamp B.shell.inner B.shell.outer (normDistance (X (G.left e)) (X B.shell.center))-
       clamp B.shell.inner B.shell.outer (normDistance (X (G.right e)) (X B.shell.center))| := by
  obtain ⟨R,hR,hconn,hu,hv⟩ := hB.2.2.2
  exact G.routed_variation_lower _ hB.2.2.1.2.1.le hconn hu hv
    (protected_routing_edges H G X hB.2.1 hR)

omit [PseudoMetricSpace Coord] in
lemma restrict_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a < b) :
    ({B with shell := RadialShell.hollow B.shell.center a b}).Valid H G X q := by
  refine ⟨hB.1,?_,?_,?_⟩
  · intro S hS e he
    exact ⟨hb.trans (hB.2.1 S hS e he).1,hb.trans (hB.2.1 S hS e he).2⟩
  · obtain ⟨u,hu⟩ := hB.2.2.1.2.2.2.1
    obtain ⟨v,hv⟩ := hB.2.2.1.2.2.2.2
    exact ⟨hB.2.2.1.1.trans ha,hab,by simp [RadialShell.hollow],⟨u,hu.trans ha⟩,⟨v,hb.trans hv⟩⟩
  · obtain ⟨R,hR,hconn,⟨u,huR,huL,hu⟩,⟨v,hvR,hv⟩⟩ := hB.2.2.2
    exact ⟨R,hR,hconn,⟨u,huR,huL,hu.trans ha⟩,⟨v,hvR,hb.trans hv⟩⟩

end Record
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

lemma labeled_energy {q : ℝ} (hX : ∀v, isProfile (X v)) {Z : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) :
    q*(∑B ∈ Z, B.shell.width) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let f (B : Record n) (e : Fin m) :=
    |clamp B.shell.inner B.shell.outer (normDistance (X (G.left e)) (X B.shell.center))-
     clamp B.shell.inner B.shell.outer (normDistance (X (G.right e)) (X B.shell.center))|
  calc
    _ = ∑B ∈ Z, q*B.shell.width := mul_sum _ _ _
    _ ≤ ∑B ∈ Z, ∑e ∈ G.inducedEdges (B.leafSet H), f B e :=
      sum_le_sum (fun B hB => B.variation_lower H G X (hZ.1 B hB))
    _ = ∑e : Fin m, ∑B ∈ Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H)), f B e := by
      simp only [inducedEdges,sum_filter,mem_filter,mem_univ,true_and]
      rw [sum_comm]
    _ ≤ _ := by
      apply sum_le_sum
      intro e he
      let W := Z.filter (fun B => e ∈ G.inducedEdges (B.leafSet H))
      rw [← Finset.sum_coe_sort]
      apply profile_shell_edge_bound (isProfile_inPolytope (hX _)) (isProfile_inPolytope (hX _))
        (fun B : W => X B.val.shell.center) (fun B => hX _) _ _
      · intro B
        exact (hZ.1 B.val (mem_filter.mp B.property).1).2.2.1.2.1.le
      · intro B D hBD w hw hbad
        have hB : B.val ∈ Z := (mem_filter.mp B.property).1
        have hD : D.val ∈ Z := (mem_filter.mp D.property).1
        have hinter : ¬Disjoint (B.val.shell.support X) (D.val.shell.support X) := by
          intro hh
          exact Set.disjoint_left.mp hh ⟨hw,hbad.2.1,Or.inr hbad.1⟩
            ⟨hw,hbad.2.2.2,Or.inr hbad.2.2.1⟩
        have hdis := hZ.2 hB hD (fun hh => hBD (Subtype.ext hh)) hinter
        have hlB := ((G.mem_inducedEdges _ _).mp (mem_filter.mp B.property).2).1
        have hlD := ((G.mem_inducedEdges _ _).mp (mem_filter.mp D.property).2).1
        have hmB : {G.left e} ∈ B.val.conflict H := H.singleton_domain_iff.mpr hlB
        have hmD : {G.left e} ∈ D.val.conflict H := H.singleton_domain_iff.mpr hlD
        exact Finset.disjoint_left.mp hdis hmB hmD

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

lemma parent_boundary_lower {q : ℝ} (hconn : LocallyConnectedReal H G q)
    {A : Finset (Fin n)} (hA : A ∈ H.nodes) (hne : A ≠ univ) :
    q ≤ (parentBoundary H G A).card :=
  hconn (H.parent A) (H.parent_mem A hA hne) A (H.nonempty A hA)
    (H.parent_strict A hA hne)

namespace AssignedBag
variable {H G X} {δ η : ℝ} (A : AssignedBag H G X δ η)

lemma input_leaf {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    u ∈ (A.input P u).leafSet H := by
  apply (Record.mem_leafSet H).mpr
  refine ⟨(A.endpoint u hu).1,?_⟩
  intro S hS huS
  have hSP : S ∈ P := by simpa [Record.excluded,input] using hS
  obtain ⟨e,he,heu,hlen⟩ := (A.endpoint u hu).2
  have he' := (mem_filter.mp he).2
  have hcut : e ∈ G.cut univ S := by
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases he' with hh | hh
    · have hright : G.right e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact Or.inl ⟨heu.symm ▸ huS,hright⟩
      · exact (hright (heu.symm ▸ huS)).elim
    · have hleft : G.left e ∉ S := fun hs => hh.2 ((hP S hSP).subset hs)
      rcases heu with heu | heu
      · exact (hleft (heu.symm ▸ huS)).elim
      · exact Or.inr ⟨heu.symm ▸ huS,hleft⟩
  have hp := hins S hSP e hcut
  rcases heu with heu | heu
  · have hp := hp.1
    change δ ≤ normDistance (X (G.left e)) (X u) at hp
    rw [heu,normDistance_self] at hp
    linarith [A.radius_pos]
  · have hp := hp.2
    change δ ≤ normDistance (X (G.right e)) (X u) at hp
    rw [heu,normDistance_self] at hp
    linarith [A.radius_pos]

lemma input_valid (hX : ∀v, isProfile (X v)) {q : ℝ} (_hq : 0 ≤ q)
    (hconn : LocallyConnectedReal H G q) (hsize : 1 < A.centers.card)
    {P : Finset (Finset (Fin n))} (hP : ∀S ∈ P, S ∈ H.nodes ∧ S ⊂ A.owner)
    {u : Fin n} (hu : u ∈ A.centers) (hins : (A.input P u).Protected G X) :
    (A.input P u).Valid H G X (q/4) := by
  obtain ⟨v,hv,hvu⟩ := Finset.exists_mem_ne hsize u
  have hdist := RadialShell.disjoint_balls_distance hX u v (A.disjoint hu hv hvu.symm)
  have houter : δ ≤ normDistance (X v) (X u) := by
    rw [normDistance_comm]
    linarith [A.radius_pos]
  refine ⟨?_,hins,?_,?_⟩
  · refine ⟨A.owner_mem,?_⟩
    intro S hS
    exact hP S (by simpa [input,Record.excluded] using hS)
  · exact ⟨le_refl 0,A.radius_pos,by simp [input,RadialShell.ball],
      ⟨u,by simp [input,RadialShell.ball,normDistance_self]⟩,⟨v,houter⟩⟩
  · refine ⟨A.owner,?_,?_,⟨u,(A.endpoint u hu).1,A.input_leaf (fun S hS => (hP S hS).2) hu hins,?_⟩,
      ⟨v,(A.endpoint v hv).1,houter⟩⟩
    · simp [input,Record.routing]
    · intro S hS hSA
      have hh := hconn A.owner A.owner_mem S hS hSA
      linarith
    · simp [input,RadialShell.ball,normDistance_self]

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n)

lemma predecessor_dichotomy {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes)
    {S : Finset (Fin n)} (hS : S ∈ P) : S ⊂ t ∨ Disjoint S t := by
  obtain ⟨htn,hta,htP⟩ := H.mem_domain.mp ht
  rcases H.laminar S (hP S hS) t htn with hSt | htS | hdis
  · left
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hSt,?_⟩
    intro heq
    exact htP S hS (heq ▸ Subset.refl _)
  · exact (htP S hS htS).elim
  · exact Or.inr hdis

lemma domain_descendant_partition {A t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    (ht : t ∈ H.domain A P) (hP : ∀S ∈ P, S ∈ H.nodes) :
    H.domain t (P.filter (fun S => S ⊂ t)) =
      (H.domain A P).filter (fun C => C ⊆ t) := by
  obtain ⟨htn,htA,htP⟩ := H.mem_domain.mp ht
  ext C
  simp only [mem_filter,mem_domain]
  constructor
  · rintro ⟨hCn,hCt,hCP⟩
    refine ⟨⟨hCn,hCt.trans htA,?_⟩,hCt⟩
    intro S hS hCS
    rcases predecessor_dichotomy H ht hP hS with hSt | hdis
    · exact hCP S ⟨hS,hSt⟩ hCS
    · obtain ⟨v,hv⟩ := H.nonempty C hCn
      exact Finset.disjoint_left.mp hdis (hCS hv) (hCt hv)
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCt,fun S hS => hCP S hS.1⟩

lemma domain_avoid_partition (A t : Finset (Fin n)) (P : Finset (Finset (Fin n))) :
    H.domain A (insert t P) = (H.domain A P).filter (fun C => ¬C ⊆ t) := by
  ext C
  simp only [mem_domain,mem_filter,mem_insert]
  constructor
  · rintro ⟨hCn,hCA,hCP⟩
    exact ⟨⟨hCn,hCA,fun S hS => hCP S (Or.inr hS)⟩,hCP t (Or.inl rfl)⟩
  · rintro ⟨⟨hCn,hCA,hCP⟩,hCt⟩
    exact ⟨hCn,hCA,fun S hS => by rcases hS with rfl | hS; exact hCt; exact hCP S hS⟩

namespace Record
variable (G : MultiGraph n m) (X : Fin n → Doubled Coord → ℝ)

lemma central_conflict {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    (B.innerRecord t a b).conflict H = (B.conflict H).filter (fun C => C ⊆ t) ∧
    (B.outsideRecord t c d).conflict H = (B.conflict H).filter (fun C => ¬C ⊆ t) := by
  have heq : B.excluded = B.predecessors := by simp [excluded,hno]
  have hP : ∀S ∈ B.predecessors, S ∈ H.nodes := fun S hS => (hshape.2 S (heq.symm ▸ hS)).1
  have ht' : t ∈ H.domain B.owner B.predecessors := by simpa only [conflict,heq] using ht
  constructor
  · simpa only [conflict,innerRecord,excluded,Option.toFinset_none,union_empty,hno] using
      domain_descendant_partition H ht' hP
  · simpa only [conflict,outsideRecord,excluded,Option.toFinset_some,union_singleton,hno,Option.toFinset_none,union_empty] using
      domain_avoid_partition H B.owner t B.predecessors

lemma central_domain_disjoint {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (a b c d : ℝ) :
    Disjoint ((B.innerRecord t a b).conflict H) ((B.outsideRecord t c d).conflict H) := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  rw [h1,h2,Finset.disjoint_left]
  intro C hC hD
  exact (mem_filter.mp hD).2 (mem_filter.mp hC).2

omit [PseudoMetricSpace Coord] in
lemma protected_same_side {B : Record n} (hB : B.Protected G X)
    {u v : Fin n} {e : Fin m}
    (he : (G.left e = u ∧ G.right e = v) ∨ (G.left e = v ∧ G.right e = u))
    (hu : normDistance (X u) (X B.shell.center) < B.shell.outer) :
    ∀S ∈ B.predecessors, u ∈ S ↔ v ∈ S := by
  intro S hS
  have hn : e ∉ G.cut univ S := by
    intro hc
    have hh := hB S hS e hc
    rcases he with he | he
    · rw [he.1] at hh
      linarith [hh.1]
    · rw [he.2] at hh
      linarith [hh.2]
  simp only [cut,mem_filter,mem_univ,true_and] at hn
  rcases he with he | he <;> simp only [he.1,he.2] at hn <;> tauto

omit [PseudoMetricSpace Coord] in
lemma central_valid {q a b δ : ℝ} {B : Record n}
    (hB : B.Valid H G X (q/4)) (hno : B.avoided = none)
    (hq : 0 ≤ q) (hconn : LocallyConnectedReal H G q)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) (htstrict : t ⊂ B.owner)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hδ : 0 < δ) (hab : a+δ < b-δ)
    {R : Finset (Fin n)} (hR : R ⊆ H.parent t \ t)
    (hRc : G.EdgeConnectedReal R (q/4))
    {u₁ u₂ v₁ v₂ : Fin n} (hu₁ : u₁ ∈ t) (hu₂ : u₂ ∈ t)
    (hv₁ : v₁ ∈ R) (hv₂ : v₂ ∈ R)
    (hu₁rad : normDistance (X u₁) (X B.shell.center) ≤ a+δ)
    (hu₂rad : b-δ ≤ normDistance (X u₂) (X B.shell.center))
    (hv₁rad : normDistance (X v₁) (X B.shell.center) ≤ a)
    (hv₂rad : b ≤ normDistance (X v₂) (X B.shell.center))
    {e : Fin m} (he : (G.left e = u₁ ∧ G.right e = v₁) ∨
      (G.left e = v₁ ∧ G.right e = u₁)) :
    (B.innerRecord t (a+δ) (b-δ)).Valid H G X (q/4) ∧
    (B.outsideRecord t a b).Valid H G X (q/4) := by
  have htn := (H.mem_domain.mp ht).1
  have htne : t ≠ univ := by
    intro hh
    have := htstrict.not_subset (by simp [hh])
    exact this
  have hparent : H.parent t ⊆ B.owner :=
    H.parent_minimal t htn htne B.owner hB.1.1 htstrict
  have hp : ∀S ∈ B.predecessors, S ∈ H.nodes ∧ S ⊂ B.owner :=
    fun S hS => hB.1.2 S (mem_union_left _ hS)
  have htex : t ∈ H.domain B.owner B.predecessors := by
    simpa only [conflict,excluded,hno,Option.toFinset_none,union_empty] using ht
  have hv₁out : v₁ ∉ t := (mem_sdiff.mp (hR hv₁)).2
  have hsame : ∀S ∈ B.predecessors, u₁ ∈ S ↔ v₁ ∈ S :=
    protected_same_side G X hB.2.1 he (by linarith)
  have huvavoid : ∀S ∈ B.predecessors, u₁ ∉ S ∧ v₁ ∉ S := by
    intro S hS
    rcases predecessor_dichotomy H htex (fun S hS => (hp S hS).1) hS with hSt | hdis
    · have hvS : v₁ ∉ S := fun hh => hv₁out (hSt.subset hh)
      exact ⟨fun hh => hvS ((hsame S hS).mp hh),hvS⟩
    · have huS : u₁ ∉ S := fun hh => Finset.disjoint_left.mp hdis hh hu₁
      exact ⟨huS,fun hh => huS ((hsame S hS).mpr hh)⟩
  constructor
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨htn,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
        simpa [excluded,innerRecord] using hS
      exact ⟨(hp S hS'.1).1,hS'.2⟩
    · intro S hS e he
      have hS' : S ∈ B.predecessors := (mem_filter.mp hS).1
      have hh := hB.2.1 S hS' e he
      exact ⟨(by dsimp [innerRecord,RadialShell.hollow] <;> linarith [hh.1]),
        (by dsimp [innerRecord,RadialShell.hollow] <;> linarith [hh.2])⟩
    · refine ⟨?_,hab,by simp [innerRecord,RadialShell.hollow],⟨u₁,hu₁rad⟩,⟨u₂,hu₂rad⟩⟩
      dsimp [innerRecord,RadialShell.hollow]
      linarith [hB.2.2.1.1]
    · refine ⟨t,?_,?_,⟨u₁,hu₁,?_,hu₁rad⟩,⟨u₂,hu₂,hu₂rad⟩⟩
      · simp [routing,innerRecord]
      · intro S hSn hSt
        exact (by linarith : q/4 ≤ q).trans (hconn t htn S hSn hSt)
      · apply (mem_leafSet H).mpr
        refine ⟨hu₁,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∧ S ⊂ t := by
          simpa [excluded,innerRecord] using hS
        exact (huvavoid S hS'.1).1
  · refine ⟨?_,?_,?_,?_⟩
    · refine ⟨hB.1.1,?_⟩
      intro S hS
      have hS' : S ∈ B.predecessors ∨ S = t := by
        simpa [excluded,outsideRecord,or_comm] using hS
      rcases hS' with hS | rfl
      · exact hp S hS
      · exact ⟨htn,htstrict⟩
    · intro S hS e he
      have hh := hB.2.1 S hS e he
      exact ⟨hb.trans hh.1,hb.trans hh.2⟩
    · refine ⟨?_,?_,by simp [outsideRecord,RadialShell.hollow],⟨v₁,hv₁rad⟩,⟨v₂,hv₂rad⟩⟩
      · exact hB.2.2.1.1.trans ha
      · dsimp [outsideRecord,RadialShell.hollow]
        linarith
    · refine ⟨R,?_,hRc,⟨v₁,hv₁,?_,hv₁rad⟩,⟨v₂,hv₂,hv₂rad⟩⟩
      · intro v hv
        obtain ⟨hvA,hvt⟩ := mem_sdiff.mp (hR hv)
        exact mem_sdiff.mpr ⟨hparent hvA,hvt⟩
      · apply (mem_leafSet H).mpr
        refine ⟨hparent (mem_sdiff.mp (hR hv₁)).1,?_⟩
        intro S hS
        have hS' : S ∈ B.predecessors ∨ S = t := by
          simpa [excluded,outsideRecord,or_comm] using hS
        rcases hS' with hS | rfl
        · exact (huvavoid S hS).2
        · exact hv₁out

end Record
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

lemma compatible_symm {B D : Record n} (h : B.Compatible H X D) : D.Compatible H X B :=
  h.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

lemma compatible_self_iff (B : Record n) (hX : ∀v, isProfile (X v))
    (hshape : B.Shape H) (hvalid : B.shell.Valid X) : ¬B.Compatible H X B := by
  intro hh
  rcases hh with hh | hh
  · obtain ⟨w,hw⟩ := RadialShell.valid_support_nonempty hX hvalid
    exact Set.disjoint_left.mp hh hw hw
  · exact Finset.disjoint_left.mp hh (B.root_mem H hshape) (B.root_mem H hshape)

lemma compatible_heredity {B D C : Record n} (hBD : B.Compatible H X D)
    (hCB : C.shell.support X ⊆ B.shell.support X) (hCC : C.conflict H ⊆ B.conflict H) :
    C.Compatible H X D := by
  rcases hBD with hBD | hBD
  · exact Or.inl (hBD.mono_left hCB)
  · exact Or.inr (hBD.mono_left hCC)

lemma candidate_ancestor {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hinter : (A.conflict H ∩ B.conflict H).Nonempty) : A.owner ∈ B.conflict H := by
  have hroots := (H.domain_root_test hA.1 hB.1
    (fun S hS => (hA.2 S hS).2) (fun S hS => (hB.2 S hS).2)).mp hinter
  rcases hroots with hh | hh
  · exact hh
  · have hba := (H.mem_domain.mp hh).2.1
    by_cases heq : B.owner = A.owner
    · exact heq ▸ B.root_mem H hB
    · have hs := horder (Finset.ssubset_iff_subset_ne.mpr ⟨hba,heq⟩)
      exact ((H.mem_domain.mp hh).2.2 B.owner hs (Subset.refl _)).elim

lemma insert_compatible {q : ℝ} {Z : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) {A B D : Record n}
    (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D)
    (hBA : A.owner ∈ B.conflict H)
    (horder : ∀F ∈ Z, F.owner ⊂ A.owner → F.owner ∈ A.excluded)
    (hAB : A.shell.support X ⊆ B.shell.support X) : A.Compatible H X D := by
  by_cases hgeo : Disjoint (A.shell.support X) (D.shell.support X)
  · exact Or.inl hgeo
  right
  by_contra hh
  have hinter : (A.conflict H ∩ D.conflict H).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro hempty
    exact hh (Finset.disjoint_iff_inter_eq_empty.mpr hempty)
  have hDA := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hinter
  have hBD : ¬Disjoint (B.shell.support X) (D.shell.support X) :=
    fun hd => hgeo (hd.mono_left hAB)
  exact Finset.disjoint_left.mp (hZ.2 hB hD hne hBD) hBA hDA

omit [PseudoMetricSpace Coord] in
lemma interior_restriction {C δ : ℝ} {A B D : Record n}
    (hcenter : D.shell.center = B.shell.center)
    (ha : B.shell.inner ≤ D.shell.inner) (hb : D.shell.outer ≤ B.shell.outer)
    (hdom : D.conflict H ⊆ B.conflict H) (hh : A.Interior H X C δ D) :
    A.Interior H X C δ B := by
  obtain ⟨⟨S,hS⟩,hl,hr⟩ := hh
  rw [hcenter] at hl hr
  exact ⟨⟨S,mem_inter.mpr ⟨(mem_inter.mp hS).1,hdom (mem_inter.mp hS).2⟩⟩,
    by linarith,by linarith⟩

omit [PseudoMetricSpace Coord] in
lemma not_interior_ball {C δ : ℝ} (hC : 1 ≤ C) (hδ : 0 ≤ δ)
    (A B : Record n) (hw : B.shell.width ≤ δ) : ¬A.Interior H X C δ B := by
  rintro ⟨_,hl,hr⟩
  unfold RadialShell.width at hw
  have := mul_le_mul_of_nonneg_right hC hδ
  nlinarith

end Record

lemma labeled_empty (q : ℝ) : LabeledArrangement H G X q ∅ := by simp [LabeledArrangement]

lemma labeled_subset {q : ℝ} {Z W : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) (hW : W ⊆ Z) :
    LabeledArrangement H G X q W :=
  ⟨fun B hB => hZ.1 B (hW hB),fun _ hB _ hD hne => hZ.2 (hW hB) (hW hD) hne⟩

lemma labeled_pair {q : ℝ} {Z : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) {B D : Record n}
    (hB : B ∈ Z) (hD : D ∈ Z) (hne : B ≠ D) : B.Compatible H X D := by
  by_cases hh : Disjoint (B.shell.support X) (D.shell.support X)
  · exact Or.inl hh
  · exact Or.inr (hZ.2 hB hD hne hh)

lemma labeled_union {q : ℝ} {Z W : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) (hW : LabeledArrangement H G X q W)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) :
    LabeledArrangement H G X q (Z∪W) := by
  constructor
  · intro B hB
    exact (mem_union.mp hB).elim (hZ.1 B) (hW.1 B)
  · intro B hB D hD hne hgeo
    rcases mem_union.mp hB with hB | hB <;> rcases mem_union.mp hD with hD | hD
    · exact hZ.2 hB hD hne hgeo
    · exact (hZW B hB D hD).resolve_left hgeo
    · exact (Record.compatible_symm H X (hZW D hD B hB)).resolve_left hgeo
    · exact hW.2 hB hD hne hgeo

lemma labeled_sets_disjoint (hX : ∀v, isProfile (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z)
    (hZW : ∀B ∈ Z, ∀D ∈ W, B.Compatible H X D) : Disjoint Z W := by
  rw [Finset.disjoint_left]
  intro B hB hBW
  exact B.compatible_self_iff H X hX (hZ.1 B hB).1 (hZ.1 B hB).2.2.1 (hZW B hB B hBW)

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

lemma restriction_refines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).Refines H X B :=
  ⟨RadialShell.restriction_subset X B.shell ha hb,Subset.refl _⟩

lemma compatible_refinements {A B C D : Record n}
    (hBD : B.Compatible H X D) (hAB : A.Refines H X B) (hCD : C.Refines H X D) :
    A.Compatible H X C := by
  have hh := compatible_heredity H X hBD hAB.1 hAB.2
  have hh' := compatible_heredity H X (compatible_symm H X hh) hCD.1 hCD.2
  exact compatible_symm H X hh'

end Record

lemma labeled_replace {q : ℝ} {Z W : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) (hW : LabeledArrangement H G X q W)
    (B : Record n) (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A) :
    LabeledArrangement H G X q (Z.erase B∪W) :=
  labeled_union H G X (labeled_subset H G X hZ (erase_subset _ _)) hW hcompat

lemma replacement_credit (hX : ∀v, isProfile (X v)) {q : ℝ} {Z W : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) {B : Record n} (hB : B ∈ Z)
    (hcompat : ∀D ∈ Z.erase B, ∀A ∈ W, D.Compatible H X A)
    (p : Record n → ℝ) {c : ℝ} (hcredit : p B+c ≤ ∑A ∈ W, p A) :
    (∑D ∈ Z, p D)+c ≤ ∑D ∈ Z.erase B∪W, p D := by
  have hdis := labeled_sets_disjoint H G X hX
    (labeled_subset H G X hZ (erase_subset B Z)) hcompat
  rw [sum_union hdis]
  have hh := sum_erase_add Z p hB
  linarith

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

lemma compatible_ne (hX : ∀v, isProfile (X v)) {B D : Record n}
    (hB : B.Shape H) (hval : B.shell.Valid X) (hBD : B.Compatible H X D) : B ≠ D := by
  rintro rfl
  exact B.compatible_self_iff H X hX hB hval hBD

lemma restriction_not_fresh {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ) :
    B.restriction a b ∉ F := by
  intro hh
  have hh' := hF _ hh
  simp [restriction,RadialShell.hollow] at hh'

lemma restriction_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b δ ε : ℝ) :
    phaseToken F δ ε (B.restriction a b) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  rw [phaseToken,ite_eq_right (restriction_not_fresh hF B a b)]
  rfl

omit [PseudoMetricSpace Coord] in
lemma interior_width {δ : ℝ} {A B : Record n} (hh : A.Interior H X 256 δ B) :
    512*δ < B.shell.width := by
  dsimp [RadialShell.width]
  linarith [hh.2.1,hh.2.2]

lemma interior_ball_subset {δ : ℝ} {A B : Record n} (hδ : 0 ≤ δ)
    (hA : A.shell = RadialShell.ball A.shell.center δ)
    (hh : A.Interior H X 256 δ B) : A.shell.support X ⊆ B.shell.support X := by
  rw [hA]
  apply RadialShell.ball_subset_of_radial_margin
  · linarith [hh.2.1]
  · linarith [hh.2.2]

end Record

lemma labeled_singleton {q : ℝ} {B : Record n} (hB : B.Valid H G X q) :
    LabeledArrangement H G X q {B} := by
  constructor
  · intro A hA
    simpa only [mem_singleton.mp hA] using hB
  · intro A hA D hD hne
    exact (hne ((mem_singleton.mp hA).trans (mem_singleton.mp hD).symm)).elim

lemma labeled_insert {q : ℝ} {Z : Finset (Record n)} {B : Record n}
    (hZ : LabeledArrangement H G X q Z) (hB : B.Valid H G X q)
    (hcompat : ∀D ∈ Z, B.Compatible H X D) :
    LabeledArrangement H G X q (insert B Z) := by
  rw [← singleton_union]
  apply labeled_union H G X (labeled_singleton H G X hB) hZ
  intro A hA D hD
  simpa only [mem_singleton.mp hA] using hcompat D hD

lemma avoiding_operation (hX : ∀v, isProfile (X v))
    {q δ ε : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.avoided = none)
    (hZ : LabeledArrangement H G X q Z) {A B : Record n}
    (hA : A.Valid H G X q) (hAF : A ∈ F)
    (hAball : A.shell = RadialShell.ball A.shell.center δ)
    (hB : B ∈ Z) (havoid : B.avoided.isSome = true)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hinter : A.Interior H X 256 δ B) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = A ∨ ∃a b, D = B.restriction a b ∧
        B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a < b := by
  let r := normDistance (X A.shell.center) (X B.shell.center)
  let B₁ := B.restriction B.shell.inner (r-δ)
  let B₂ := B.restriction (r+δ) B.shell.outer
  have hbvalid := hZ.1 B hB
  have h1a : B.shell.inner < r-δ := by dsimp [r] <;> linarith [hinter.2.1]
  have h1b : r-δ ≤ B.shell.outer := by dsimp [r] <;> linarith [hinter.2.2]
  have h2a : B.shell.inner ≤ r+δ := by dsimp [r] <;> linarith [hinter.2.1]
  have h2b : r+δ < B.shell.outer := by dsimp [r] <;> linarith [hinter.2.2]
  have hB₁ : B₁.Valid H G X q := Record.restrict_valid H G X hbvalid (le_refl _) h1b h1a
  have hB₂ : B₂.Valid H G X q := Record.restrict_valid H G X hbvalid h2a (le_refl _) h2b
  have h12 : B₁.Compatible H X B₂ := Or.inl
    (RadialShell.concentric_disjoint X B.shell.center (by linarith : r-δ ≤ r+δ))
  have hA1 : A.Compatible H X B₁ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center B.shell.inner (r-δ)).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_lower X _ _ (by dsimp [r] <;> linarith)
  have hA2 : A.Compatible H X B₂ := by
    left
    change Disjoint (A.shell.support X) ((RadialShell.hollow B.shell.center (r+δ) B.shell.outer).support X)
    rw [hAball]
    exact RadialShell.ball_disjoint_hollow_upper X _ _ (le_refl _)
  let W : Finset (Record n) := {A,B₁,B₂}
  have hW : LabeledArrangement H G X q W := by
    apply labeled_insert H G X
    · apply labeled_insert H G X (labeled_singleton H G X hB₂) hB₁
      intro D hD
      simpa only [mem_singleton.mp hD] using h12
    · exact hA
    · intro D hD
      rcases mem_insert.mp hD with rfl | hD
      · exact hA1
      · simpa only [mem_singleton.mp hD] using hA2
  have hancestor : A.owner ∈ B.conflict H :=
    Record.candidate_ancestor H hA.1 hbvalid.1 (horder B hB) hinter.1
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBC : B.Compatible H X D := labeled_pair H G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.insert_compatible H G X hZ hA.1 hB hDZ hDB.symm hancestor horder
        (Record.interior_ball_subset H X hδ.le hAball hinter)
    rcases mem_insert.mp hC with rfl | hC
    · exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X (le_refl _) h1b).1 (Subset.refl _)
    · have heq := mem_singleton.mp hC
      subst C
      exact Record.compatible_heredity H X hBC
        (B.restriction_refines H X h2a (le_refl _)).1 (Subset.refl _)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at havoid
    simp at havoid
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hne12 := Record.compatible_ne H X hX hB₁.1 hB₁.2.2.1 h12
    have hneA1 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA1
    have hneA2 := Record.compatible_ne H X hX hA.1 hA.2.2.1 hA2
    have hAnot : A ∉ ({B₁,B₂} : Finset (Record n)) := by simp [hneA1,hneA2]
    have h1not : B₁ ∉ ({B₂} : Finset (Record n)) := by simpa using hne12
    dsimp [W]
    rw [sum_insert hAnot,sum_insert h1not,sum_singleton]
    rw [Record.phaseToken,ite_eq_right hBF,havoid]
    rw [show Record.phaseToken F δ ε A = AssignedAccounting.fresh δ ε by simp [Record.phaseToken,hAF]]
    rw [Record.restriction_token (fun D hD => (hF D hD).1) B,
      Record.restriction_token (fun D hD => (hF D hD).1) B,havoid]
    have hh := AssignedAccounting.avoiding_carve hδ.le hε
      (Record.interior_width H X hinter).le
      (show (r-δ-B.shell.inner)+(B.shell.outer-(r+δ))=B.shell.width-2*δ by
        dsimp [RadialShell.width] <;> ring)
    linarith
  refine ⟨Z.erase B∪W,labeled_replace H G X hZ hW B hcompat,
    replacement_credit H G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact Or.inl rfl
  right
  rcases mem_insert.mp hD with rfl | hD
  · exact ⟨B.shell.inner,r-δ,rfl,le_refl _,h1b,h1a⟩
  · have heq := mem_singleton.mp hD
    exact ⟨r+δ,B.shell.outer,heq,h2a,le_refl _,h2b⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

lemma mem_restrictionSet {B D : Record n} {a b : ℝ} :
    D ∈ B.restrictionSet a b ↔ a < b ∧ D = B.restriction a b := by
  by_cases hh : a < b <;> simp [restrictionSet,hh]

lemma restrictionSet_valid {q a b : ℝ} {B : Record n} (hB : B.Valid H G X q)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    LabeledArrangement H G X q (B.restrictionSet a b) := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab]
    exact labeled_singleton H G X (restrict_valid H G X hB ha hb hab)
  · rw [restrictionSet,ite_eq_right hab]
    exact labeled_empty H G X q

lemma restrictionSet_refines {B D : Record n} {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hD : D ∈ B.restrictionSet a b) : D.Refines H X B := by
  obtain ⟨hab,rfl⟩ := mem_restrictionSet.mp hD
  exact B.restriction_refines H X ha hb

lemma restrictionSet_token {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true) (B : Record n) (a b : ℝ)
    {δ ε : ℝ} (hδ : 0 ≤ δ) :
    (∑D ∈ B.restrictionSet a b, phaseToken F δ ε D) =
      AssignedAccounting.base B.avoided.isSome (b-a) δ := by
  by_cases hab : a < b
  · rw [restrictionSet,ite_eq_left hab,sum_singleton,restriction_token hF]
  · rw [restrictionSet,ite_eq_right hab,sum_empty,AssignedAccounting.base_discard _ (by linarith) hδ]

lemma restrictions_compatible (B : Record n) {a b c d : ℝ} (hbc : b ≤ c)
    {D E : Record n} (hD : D ∈ B.restrictionSet a b) (hE : E ∈ B.restrictionSet c d) :
    D.Compatible H X E := by
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hD
  obtain ⟨_,rfl⟩ := mem_restrictionSet.mp hE
  exact Or.inl (RadialShell.concentric_disjoint X B.shell.center hbc)

end Record

lemma dense_operation (hX : ∀v, isProfile (X v))
    {q δ ε a b : ℝ} (hδ : 0 < δ) (hε : ε ≤ δ/1536)
    {F Z M : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hZ : LabeledArrangement H G X q Z) {B : Record n} (hB : B ∈ Z)
    (hMZ : LabeledArrangement H G X q M) (hMF : M ⊆ F)
    (hMball : ∀A ∈ M, A.shell = RadialShell.ball A.shell.center δ)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hrange : ∀A ∈ M, a-δ < normDistance (X A.shell.center) (X B.shell.center) ∧
      normDistance (X A.shell.center) (X B.shell.center) < b+δ)
    (hinter : ∀A ∈ M, A.Interior H X 256 δ B)
    (horder : ∀A ∈ M, ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ A.excluded)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D ∈ M ∨ ∃c d, D = B.restriction c d ∧
        B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let W₁ := B.restrictionSet B.shell.inner (a-2*δ)
  let W₂ := B.restrictionSet (b+2*δ) B.shell.outer
  let W := W₁∪W₂∪M
  have hbvalid := hZ.1 B hB
  have h1b : a-2*δ ≤ B.shell.outer := by linarith
  have h2a : B.shell.inner ≤ b+2*δ := by linarith
  have hW₁ : LabeledArrangement H G X q W₁ :=
    B.restrictionSet_valid H G X hbvalid (le_refl _) h1b
  have hW₂ : LabeledArrangement H G X q W₂ :=
    B.restrictionSet_valid H G X hbvalid h2a (le_refl _)
  have h12 : ∀D ∈ W₁, ∀E ∈ W₂, D.Compatible H X E := by
    intro D hD E hE
    exact B.restrictions_compatible H X (by linarith : a-2*δ ≤ b+2*δ) hD hE
  have hWM : ∀D ∈ W₁∪W₂, ∀A ∈ M, D.Compatible H X A := by
    intro D hD A hAM
    apply Record.compatible_symm H X
    left
    rw [hMball A hAM]
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [(hrange A hAM).1])
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hD
      exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [(hrange A hAM).2])
  have hW12 := labeled_union H G X hW₁ hW₂ h12
  have hW : LabeledArrangement H G X q W := labeled_union H G X hW12 hMZ hWM
  have hcompat : ∀D ∈ Z.erase B, ∀C ∈ W, D.Compatible H X C := by
    intro D hD C hC
    obtain ⟨hDB,hDZ⟩ := mem_erase.mp hD
    have hBD := labeled_pair H G X hZ hB hDZ hDB.symm
    apply Record.compatible_symm H X
    rcases mem_union.mp hC with hC | hC
    · rcases mem_union.mp hC with hC | hC
      · have hh := B.restrictionSet_refines H X (le_refl _) h1b hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
      · have hh := B.restrictionSet_refines H X h2a (le_refl _) hC
        exact Record.compatible_heredity H X hBD hh.1 hh.2
    · have hancestor := Record.candidate_ancestor H (hMZ.1 C hC).1 hbvalid.1
        (horder C hC B hB) (hinter C hC).1
      exact Record.insert_compatible H G X hZ (hMZ.1 C hC).1 hB hDZ hDB.symm hancestor
        (horder C hC) (Record.interior_ball_subset H X hδ.le (hMball C hC) (hinter C hC))
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2.1] at hwidth
    linarith
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*(M.card : ℝ)*δ ≤
      ∑D ∈ W, Record.phaseToken F δ ε D := by
    have hd12 := labeled_sets_disjoint H G X hX hW₁ h12
    have hdM := labeled_sets_disjoint H G X hX hW12 hWM
    dsimp only [W]
    rw [sum_union hdM,sum_union hd12,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le]
    have hsumM : (∑D ∈ M, Record.phaseToken F δ ε D) =
        (M.card : ℝ)*AssignedAccounting.fresh δ ε := by
      calc
        _ = ∑D ∈ M, AssignedAccounting.fresh δ ε := sum_congr rfl (fun D hD => by
          simp only [Record.phaseToken,ite_eq_left (hMF hD)])
        _ = _ := by simp
    rw [hsumM,Record.phaseToken,ite_eq_right hBF,hno,Option.isSome_none]
    exact AssignedAccounting.dense_carve hδ.le hε (Nat.cast_nonneg _) hwidth.le
      (by dsimp [RadialShell.width] <;> ring) hdense hcount
  refine ⟨Z.erase B∪W,labeled_replace H G X hZ hW B hcompat,
    replacement_credit H G X hX hZ hB hcompat _ hcredit,?_⟩
  intro D hD
  rcases mem_union.mp hD with hD | hD
  · exact Or.inl (mem_of_mem_erase hD)
  right
  rcases mem_union.mp hD with hD | hD
  · right
    rcases mem_union.mp hD with hD | hD
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨B.shell.inner,a-2*δ,heq,le_refl _,h1b,hpos⟩
    · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hD
      exact ⟨b+2*δ,B.shell.outer,heq,h2a,le_refl _,hpos⟩
  · exact Or.inl hD

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] (H : Hierarchy n) (G : MultiGraph n m)
  (X : Fin n → Doubled Coord → ℝ)

namespace Record

lemma central_refines {B : Record n} (hshape : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).Refines H X B ∧ (B.outsideRecord t c d).Refines H X B := by
  obtain ⟨h1,h2⟩ := central_conflict H hshape hno ht a b c d
  exact ⟨⟨RadialShell.restriction_subset X B.shell ha hb,h1 ▸ filter_subset _ _⟩,
    ⟨RadialShell.restriction_subset X B.shell hc hd,h2 ▸ filter_subset _ _⟩⟩

lemma hollow_token {F : Finset (Record n)} (hF : ∀D ∈ F, D.shell.ordinary = true)
    {B : Record n} (hB : B.shell.ordinary = false) (δ ε : ℝ) :
    phaseToken F δ ε B = AssignedAccounting.base B.avoided.isSome B.shell.width δ := by
  rw [phaseToken,ite_eq_right]
  intro hh
  have := hF B hh
  simp [hB] at this

end Record

lemma sparse_operation (hX : ∀v, isProfile (X v))
    {q δ ε a b M : ℝ} (hδ : 0 < δ)
    {F Z : Finset (Record n)} (hF : ∀D ∈ F,
      D.shell.ordinary = true ∧ D.shell.width = δ)
    (hZ : LabeledArrangement H G X q Z) {B : Record n} (hB : B ∈ Z)
    (hno : B.avoided = none) (hwidth : 512*δ < B.shell.width)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hwide : 255*δ ≤ b-a) (hsparse : M*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord t (a+δ) (b-δ)).Valid H G X q)
    (houter : (B.outsideRecord t a b).Valid H G X q) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X q Z' ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+AssignedAccounting.theta*M*δ ≤
        ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      ∀D ∈ Z', D ∈ Z ∨ D = B.innerRecord t (a+δ) (b-δ) ∨
        D = B.outsideRecord t a b ∨ ∃c d, D = B.restriction c d ∧
          B.shell.inner ≤ c ∧ d ≤ B.shell.outer ∧ c < d := by
  let C := B.innerRecord t (a+δ) (b-δ)
  let D := B.outsideRecord t a b
  let W₁ := B.restrictionSet B.shell.inner a
  let W₂ := B.restrictionSet b B.shell.outer
  let W₀ := W₁∪W₂
  let W₃ := insert C W₀
  let W := insert D W₃
  have hab : a ≤ b := by linarith
  have hv := hZ.1 B hB
  have hW₁ : LabeledArrangement H G X q W₁ :=
    Record.restrictionSet_valid H G X hv (le_refl _) (hab.trans hb)
  have hW₂ : LabeledArrangement H G X q W₂ :=
    Record.restrictionSet_valid H G X hv (ha.trans hab) (le_refl _)
  have h12 : ∀E ∈ W₁, ∀J ∈ W₂, E.Compatible H X J := by
    intro E hE J hJ
    exact Record.restrictions_compatible H X B hab hE hJ
  have hW₀ : LabeledArrangement H G X q W₀ := labeled_union H G X hW₁ hW₂ h12
  have hC0 : ∀E ∈ W₀, C.Compatible H X E := by
    intro E hE
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (by linarith : a ≤ a+δ)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (by linarith : b-δ ≤ b))
  have hW₃ : LabeledArrangement H G X q W₃ := labeled_insert H G X hW₀ hinner hC0
  have hD3 : ∀E ∈ W₃, D.Compatible H X E := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr (Record.central_domain_disjoint H hv.1 hno ht (a+δ) (b-δ) a b).symm
    rcases mem_union.mp hE with hE | hE
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl ((RadialShell.concentric_disjoint X B.shell.center (le_refl a)).symm)
    · obtain ⟨_,rfl⟩ := Record.mem_restrictionSet.mp hE
      exact Or.inl (RadialShell.concentric_disjoint X B.shell.center (le_refl b))
  have hW : LabeledArrangement H G X q W := labeled_insert H G X hW₃ houter hD3
  have hCD := Record.central_refines H X hv.1 hno ht
    (show B.shell.inner ≤ a+δ by linarith) (show b-δ ≤ B.shell.outer by linarith) ha hb
  have hWB : ∀E ∈ W, E.Refines H X B := by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.2
    rcases mem_insert.mp hE with rfl | hE
    · exact hCD.1
    rcases mem_union.mp hE with hE | hE
    · exact Record.restrictionSet_refines H X (le_refl _) (hab.trans hb) hE
    · exact Record.restrictionSet_refines H X (ha.trans hab) (le_refl _) hE
  have hcompat : ∀J ∈ Z.erase B, ∀E ∈ W, J.Compatible H X E := by
    intro J hJ E hE
    obtain ⟨hne,hJ⟩ := mem_erase.mp hJ
    exact Record.compatible_symm H X (Record.compatible_heredity H X
      (labeled_pair H G X hZ hB hJ hne.symm) (hWB E hE).1 (hWB E hE).2)
  have hBF : B ∉ F := by
    intro hh
    rw [(hF B hh).2] at hwidth
    linarith
  have hDC : D ∉ W₃ := by
    intro hh
    exact Record.compatible_self_iff H X D hX houter.1 houter.2.2.1 (hD3 D hh)
  have hCW : C ∉ W₀ := by
    intro hh
    exact Record.compatible_self_iff H X C hX hinner.1 hinner.2.2.1 (hC0 C hh)
  have hcredit : Record.phaseToken F δ ε B+AssignedAccounting.theta*M*δ ≤
      ∑E ∈ W, Record.phaseToken F δ ε E := by
    have hdis := labeled_sets_disjoint H G X hX hW₁ h12
    change _ ≤ ∑E ∈ insert D W₃, _
    rw [sum_insert hDC]
    change _ ≤ _+(∑E ∈ insert C W₀, _)
    rw [sum_insert hCW]
    change _ ≤ _+(_+(∑E ∈ W₁∪W₂, _))
    rw [sum_union hdis,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.restrictionSet_token (fun D hD => (hF D hD).1) B _ _ hδ.le,
      Record.hollow_token (fun D hD => (hF D hD).1) (show D.shell.ordinary = false from rfl),
      Record.hollow_token (fun D hD => (hF D hD).1) (show C.shell.ordinary = false from rfl),
      Record.phaseToken,ite_eq_right hBF]
    simp only [D,C,Record.innerRecord,Record.outsideRecord,RadialShell.hollow,
      hno,Option.isSome_none,Option.isSome_some,RadialShell.width]
    have hh := AssignedAccounting.sparse_carve hδ.le hwidth.le
      (R₁ := a-B.shell.inner) (R₂ := B.shell.outer-b) (L := b-a)
      (by dsimp [RadialShell.width] <;> ring) hwide hsparse
    rw [show b-δ-(a+δ) = b-a-2*δ by ring]
    dsimp only [RadialShell.width] at hh
    linarith
  refine ⟨Z.erase B∪W,labeled_replace H G X hZ hW B hcompat,
    replacement_credit H G X hX hZ hB hcompat _ hcredit,?_⟩
  intro E hE
  rcases mem_union.mp hE with hE | hE
  · exact Or.inl (mem_of_mem_erase hE)
  right
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inr (Or.inl heq)
  rcases mem_insert.mp hE with heq | hE
  · exact Or.inl heq
  right; right
  rcases mem_union.mp hE with hE | hE
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨B.shell.inner,a,heq,le_refl _,hab.trans hb,hpos⟩
  · obtain ⟨hpos,heq⟩ := Record.mem_restrictionSet.mp hE
    exact ⟨b,B.shell.outer,heq,ha.trans hab,le_refl _,hpos⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}

namespace AssignedBag

lemma neighbor_spec (A : AssignedBag H G X δ η) {u : Fin n} (hu : u ∈ A.centers) :
    A.neighbor u ∈ H.parent A.owner\A.owner ∧
      normDistance (X u) (X (A.neighbor u)) < δ ∧
      ∃e : Fin m, (G.left e = u ∧ G.right e = A.neighbor u) ∨
        (G.left e = A.neighbor u ∧ G.right e = u) := by
  simpa only [neighbor,dite_eq_left hu] using (A.neighbor_exists hu).choose_spec

lemma input_injective (A : AssignedBag H G X δ η) (P : Finset (Finset (Fin n))) :
    Function.Injective (A.input P) := by
  intro u v hh
  exact congrArg (fun B : Record n => B.shell.center) hh

lemma input_arrangement (A : AssignedBag H G X δ η) {q : ℝ}
    {P : Finset (Finset (Fin n))} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hvalid : ∀u ∈ U, (A.input P u).Valid H G X q) :
    LabeledArrangement H G X q (U.image (A.input P)) := by
  constructor
  · intro B hB
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    exact hvalid u hu
  · intro B hB D hD hne hgeo
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hB
    obtain ⟨v,hv,rfl⟩ := mem_image.mp hD
    exact (hgeo (A.disjoint (hU hu) (hU hv) (fun hh => hne (congrArg (A.input P) hh)))).elim

end AssignedBag

namespace Record

lemma unique_interior (_hX : ∀v, isProfile (X v)) {q : ℝ}
    {Z : Finset (Record n)} (hZ : LabeledArrangement H G X q Z)
    {A B D : Record n} (hA : A.Shape H) (hB : B ∈ Z) (hD : D ∈ Z)
    (horder : ∀E ∈ Z, E.owner ⊂ A.owner → E.owner ∈ A.excluded)
    (hAB : (A.conflict H ∩ B.conflict H).Nonempty)
    (hAD : (A.conflict H ∩ D.conflict H).Nonempty)
    (hsub : A.shell.support X ⊆ D.shell.support X)
    (hmeet : ¬Disjoint (A.shell.support X) (B.shell.support X)) : B = D := by
  by_contra hne
  have hba := candidate_ancestor H hA (hZ.1 B hB).1 (horder B hB) hAB
  have hda := candidate_ancestor H hA (hZ.1 D hD).1 (horder D hD) hAD
  rcases labeled_pair H G X hZ hB hD hne with hh | hh
  · exact hmeet ((hh.symm).mono_left hsub)
  · exact Finset.disjoint_left.mp hh hba hda

lemma strict_owner_of_interior (hX : ∀v, isProfile (X v))
    {A B : Record n} (hA : A.Shape H) (hB : B.Shape H)
    (hAv : A.shell.Valid X) (hδ : 0 ≤ δ)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (horder : B.owner ⊂ A.owner → B.owner ∈ A.excluded)
    (hsep : B.owner = A.owner → Disjoint (A.shell.support X) (B.shell.support X))
    (hinter : A.Interior H X 256 δ B) : A.owner ⊂ B.owner := by
  have hanc := candidate_ancestor H hA hB horder hinter.1
  have hsub := (H.mem_domain.mp hanc).2.1
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨hsub,?_⟩
  intro hh
  obtain ⟨z,hz⟩ := RadialShell.valid_support_nonempty hX hAv
  exact Set.disjoint_left.mp (hsep hh.symm) hz
    (interior_ball_subset H X hδ hball hinter hz)

end Record
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma large_component (A : AssignedBag H G X δ η) {q : ℝ}
    (hq : 0 < q) (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    {U : Finset (Fin n)} (hU : U ⊆ A.centers) (hhalf : A.centers.card ≤ 2*U.card) :
    ∃R : Finset (Fin n), R ⊆ H.parent A.owner\A.owner ∧
      G.EdgeConnectedReal R (q/4) ∧ 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card := by
  obtain ⟨J,hJ,hJc,hcount⟩ := G.outside_connected_partition hq
    (hconn (H.parent A.owner) (H.parent_mem A.owner A.owner_mem A.nonroot))
    (H.nonempty A.owner A.owner_mem) (H.parent_strict A.owner A.owner_mem A.nonroot)
  have hJn : J.Nonempty := by
    have hout : (H.parent A.owner\A.owner).Nonempty :=
      sdiff_nonempty.mpr (H.parent_strict A.owner A.owner_mem A.nonroot).not_subset
    rw [← hJ.2.2] at hout
    obtain ⟨R,hR,_⟩ := biUnion_nonempty.mp hout
    exact ⟨R,hR⟩
  have hcover : ∀u ∈ U, ∃R ∈ J, A.neighbor u ∈ R := by
    intro u hu
    have hh := (A.neighbor_spec (hU hu)).1
    rw [← hJ.2.2] at hh
    simpa only [mem_biUnion,id_eq] using hh
  have hb := parent_boundary_lower H G hconn A.owner_mem A.nonroot
  have hηq : 3072 ≤ η*q := (div_le_iff₀ hq).mp hη
  have hsum := mul_le_mul_of_nonneg_right A.assignment hq.le
  have hmass := mul_le_mul_of_nonneg_right hηq
    (Nat.cast_nonneg (parentBoundary H G A.owner).card : (0:ℝ) ≤ _)
  have hhalf' : (A.centers.card : ℝ) ≤ 2*(U.card : ℝ) := by exact_mod_cast hhalf
  have hmul := mul_le_mul_of_nonneg_left hhalf' hq.le
  obtain ⟨R,hR,hlarge⟩ := AssignedSelection.large_neighbor_class U J
    (fun u R => A.neighbor u ∈ R) hJn hcover hq (lt_of_lt_of_le hq hb)
    (by simpa [mul_comm,parentBoundary] using hcount)
    (by nlinarith)
  exact ⟨R,(hJ.1 R hR).2,hJc R hR,hlarge⟩

lemma selected_interior (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    {Z : Finset (Record n)} (hZ : LabeledArrangement H G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    {B : Record n} (hB : B ∈ Z) {u₀ : Fin n}
    (hint₀ : (A.input P u₀).Interior H X 256 δ B)
    {a b : ℝ} (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    {u : Fin n} (hu : u ∈ U)
    (hr : a-δ < normDistance (X u) (X B.shell.center) ∧
      normDistance (X u) (X B.shell.center) < b+δ) :
    (A.input P u).Interior H X 256 δ B := by
  obtain ⟨D,hD,hintD⟩ := hinter u hu
  have hconf : ((A.input P u).conflict H ∩ B.conflict H).Nonempty := hint₀.1
  have hmeet : ¬Disjoint ((A.input P u).shell.support X) (B.shell.support X) :=
    RadialShell.ball_meets_radial hX (hZ.1 B hB).2.2.1 u A.radius_pos
      (by linarith [hr.1]) (by linarith [hr.2])
  have heq : B = D := Record.unique_interior hX hZ (hshape u hu) hB hD
    (fun E hE hsub => by simpa [input,Record.excluded] using horder E hE hsub)
    hconf hintD.1 (Record.interior_ball_subset H X A.radius_pos.le rfl hintD) hmeet
  exact heq.symm ▸ hintD

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma radial_group (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q : ℝ} {P : Finset (Finset (Fin n))} {U : Finset (Fin n)}
    (hU : U ⊆ A.centers) {Z : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z)
    (hshape : ∀u ∈ U, (A.input P u).Shape H)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hinter : ∀u ∈ U, ∃D ∈ Z, (A.input P u).Interior H X 256 δ D)
    (hno : ∀u ∈ U, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none)
    {R : Finset (Fin n)} (hlarge : 768 ≤ (U.filter (fun u => A.neighbor u ∈ R)).card) :
    ∃(B : Record n) (a b : ℝ) (M : Finset (Fin n)) (u₁ u₂ : Fin n),
      B ∈ Z ∧ B.avoided = none ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer ∧ a ≤ b ∧
      M.Nonempty ∧ M = U.filter (fun u => a-δ < normDistance (X u) (X B.shell.center) ∧
        normDistance (X u) (X B.shell.center) < b+δ) ∧
      (∀u ∈ M, (A.input P u).Interior H X 256 δ B) ∧
      (768 ≤ M.card ∨ 255*δ ≤ b-a) ∧
      u₁ ∈ U ∧ u₂ ∈ U ∧ A.neighbor u₁ ∈ R ∧ A.neighbor u₂ ∈ R ∧
      normDistance (X (A.neighbor u₁)) (X B.shell.center) ≤ a ∧
      b ≤ normDistance (X (A.neighbor u₂)) (X B.shell.center) ∧
      normDistance (X u₁) (X B.shell.center) ≤ a+δ ∧
      b-δ ≤ normDistance (X u₂) (X B.shell.center) := by
  let K := U.filter (fun u => A.neighbor u ∈ R)
  have hKn : K.Nonempty := card_pos.mp (lt_of_lt_of_le (by norm_num : 0<768) hlarge)
  obtain ⟨u₀,hu₀⟩ := hKn
  obtain ⟨B,hB,hint₀⟩ := hinter u₀ (mem_filter.mp hu₀).1
  let ρ := fun u => normDistance (X u) (X B.shell.center)
  obtain ⟨u₁,hu₁,hmin⟩ := K.exists_min_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  obtain ⟨u₂,hu₂,hmax⟩ := K.exists_max_image (fun u => ρ (A.neighbor u)) ⟨u₀,hu₀⟩
  let a := max B.shell.inner (ρ (A.neighbor u₁))
  let b := min B.shell.outer (ρ (A.neighbor u₂))
  let M := U.filter (fun u => a-δ < ρ u ∧ ρ u < b+δ)
  have hnear (u : Fin n) (hu : u ∈ U) : |ρ u - ρ (A.neighbor u)| < δ :=
    (normDistance_reverse _ _ _).trans_lt (A.neighbor_spec (hU hu)).2.1
  have hr₀ := AssignedSelection.interior_neighbor_in_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
    hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
  have hMn : M.Nonempty := ⟨u₀,mem_filter.mpr ⟨(mem_filter.mp hu₀).1,hr₀.2⟩⟩
  have hMinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B := by
    intro u hu
    obtain ⟨hu,hr⟩ := mem_filter.mp hu
    exact A.selected_interior hX hZ hshape horder hinter hB hint₀
      (le_max_left _ _) (min_le_left _ _) hu hr
  have hdich : 768 ≤ M.card ∨ 255*δ ≤ b-a := by
    by_cases hs : K ⊆ M
    · exact Or.inl (hlarge.trans (card_le_card hs))
    · obtain ⟨u,hu,huM⟩ := Finset.not_subset.mp hs
      have hr : ¬(a-δ < ρ u ∧ ρ u < b+δ) :=
        fun hh => huM (mem_filter.mpr ⟨(mem_filter.mp hu).1,hh⟩)
      exact Or.inr (AssignedSelection.radial_range A.radius_pos (hmin u₀ hu₀) (hmax u₀ hu₀)
        hint₀.2.1 hint₀.2.2 (hnear u₀ (mem_filter.mp hu₀).1)
        (hmin u hu) (hmax u hu) (hnear u (mem_filter.mp hu).1) hr)
  have hnear₁ := (abs_lt.mp (hnear u₁ (mem_filter.mp hu₁).1)).2
  have hnear₂ := (abs_lt.mp (hnear u₂ (mem_filter.mp hu₂).1)).1
  refine ⟨B,a,b,M,u₁,u₂,hB,hno u₀ (mem_filter.mp hu₀).1 B hB hint₀,
    le_max_left _ _,min_le_left _ _,hr₀.1,hMn,rfl,hMinter,hdich,
    (mem_filter.mp hu₁).1,(mem_filter.mp hu₂).1,(mem_filter.mp hu₁).2,(mem_filter.mp hu₂).2,
    le_max_right _ _,min_le_right _ _,?_,?_⟩
  · change ρ u₁ ≤ a+δ
    have hh : ρ (A.neighbor u₁) ≤ a := le_max_right _ _
    linarith
  · change b-δ ≤ ρ u₂
    have hh : b ≤ ρ (A.neighbor u₂) := min_le_right _ _
    linarith

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

namespace Record

lemma radialRefines_refl (B : Record n) : B.RadialRefines (H := H) B :=
  ⟨rfl,le_refl _,le_refl _,Subset.refl _⟩

lemma restriction_radialRefines (B : Record n) {a b : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) :
    (B.restriction a b).RadialRefines (H := H) B := ⟨rfl,ha,hb,Subset.refl _⟩

lemma central_radialRefines {B : Record n} (hB : B.Shape H) (hno : B.avoided = none)
    {t : Finset (Fin n)} (ht : t ∈ B.conflict H) {a b c d : ℝ}
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hc : B.shell.inner ≤ c) (hd : d ≤ B.shell.outer) :
    (B.innerRecord t a b).RadialRefines (H := H) B ∧
      (B.outsideRecord t c d).RadialRefines (H := H) B := by
  obtain ⟨h1,h2⟩ := central_conflict H hB hno ht a b c d
  refine ⟨⟨rfl,ha,hb,?_⟩,⟨rfl,hc,hd,?_⟩⟩
  · rw [h1]; exact filter_subset _ _
  · rw [h2]; exact filter_subset _ _

end Record

omit [PseudoMetricSpace Coord] in
lemma evolution_interior {δ : ℝ} (hδ : 0 ≤ δ)
    {F Z Z' : Finset (Record n)} (hF : ∀D ∈ F, D.shell.width = δ)
    (hevol : Evolution (H := H) F Z Z') {A : Record n}
    (hh : A.InteriorTo (H := H) (X := X) δ Z') : A.InteriorTo (H := H) (X := X) δ Z := by
  obtain ⟨D,hD,hint⟩ := hh
  rcases hevol D hD with hD | ⟨B,hB,href⟩
  · exact (Record.not_interior_ball H X (by norm_num : (1:ℝ) ≤ 256) hδ A D
      (hF D hD).le hint).elim
  · exact ⟨B,hB,Record.interior_restriction H X href.1 href.2.1 href.2.2.1 href.2.2.2 hint⟩

lemma ownerEvolution_order {t : Finset (Fin n)} {P : Finset (Finset (Fin n))}
    {Z Z' : Finset (Record n)} (hold : ∀B ∈ Z, B.owner ⊂ t → B.owner ∈ P)
    (hevol : OwnerEvolution t Z Z') : ∀B ∈ Z', B.owner ⊂ t → B.owner ∈ P := by
  intro B hB hs
  rcases hevol B hB with hh | ⟨D,hD,hh⟩
  · exact (hs.ne hh).elim
  · rw [hh] at hs ⊢
    exact hold D hD hs

namespace AssignedBag
variable {δ η : ℝ} (A : AssignedBag H G X δ η)

lemma metadata_evolution {F Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D ∈ F ∨ ∃B ∈ Z, D.RadialRefines (H := H) B)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    Evolution (H := H) F Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact Or.inr ⟨D,hD,D.radialRefines_refl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,B.restriction_radialRefines ha hb⟩

lemma metadata_owners {Z Z' Q : Finset (Record n)}
    (hQ : ∀D ∈ Q, D.owner = A.owner ∨ ∃B ∈ Z, D.owner = B.owner)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    OwnerEvolution A.owner Z Z' := by
  intro D hD
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inr ⟨D,hD,rfl⟩
  · exact hQ D hD
  · exact Or.inr ⟨B,hB,rfl⟩

lemma metadata_separation {P : Finset (Finset (Fin n))} {U V : Finset (Fin n)}
    (hVU : V ⊆ U) {Z Z' Q F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.width = δ) (hevol : Evolution (H := H) F Z Z')
    (hsep : A.SameOwnerSeparated P U Z)
    (hQ : ∀D ∈ Q, D.owner = A.owner → ∀u ∈ V,
      (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      Disjoint ((RadialShell.ball u δ).support X) (D.shell.support X))
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    A.SameOwnerSeparated P V Z' := by
  intro u hu hint D hD hown
  have hintold := evolution_interior A.radius_pos.le hF hevol hint
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,ha,hb⟩
  · exact hsep u (hVU hu) hintold D hD hown
  · exact hQ D hD hown u hu hintold
  · exact (hsep u (hVU hu) hintold B hB hown).mono_right
      (RadialShell.restriction_subset X B.shell ha hb)

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma metadata_fresh (A : AssignedBag H G X δ η) {P : Finset (Finset (Fin n))}
    {F Z Z' Q : Finset (Record n)} {M : Finset (Fin n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true)
    (hQ : ∀D ∈ Q, D ∈ F → ∃u ∈ M, D = A.input P u)
    (hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃B ∈ Z, ∃a b,
      D = B.restriction a b ∧ B.shell.inner ≤ a ∧ b ≤ B.shell.outer) :
    ∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ M, D = A.input P u := by
  intro D hD hDF
  rcases hmeta D hD with hD | hD | ⟨B,hB,a,b,rfl,_⟩
  · exact Or.inl hD
  · exact Or.inr (hQ D hD hDF)
  · exact (Record.restriction_not_fresh hF B a b hDF).elim

lemma avoiding_move (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {u : Fin n} (hu : u ∈ U) {B : Record n} (hB : B ∈ Z)
    (havoid : B.avoided.isSome = true) (hinter : (A.input P u).Interior H X 256 δ B) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := avoiding_operation H G X hX A.radius_pos hε
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.2⟩) hZ (hvalid u (hU hu))
    (hAF u (hU hu)) rfl hB havoid
    (fun D hD hs => by simpa [input,Record.excluded] using horder D hD hs) hinter
  let Q : Finset (Record n) := {A.input P u}
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | rfl | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl (mem_singleton_self _))
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution
    (fun D hD => Or.inl ((mem_singleton.mp hD).symm ▸ hAF u (hU hu))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners
    (fun D hD => Or.inl (by rw [mem_singleton.mp hD]; rfl)) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := {u}) (by
      intro D hD _
      exact ⟨u,mem_singleton_self _,mem_singleton.mp hD⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\{u}) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    rw [mem_singleton.mp hD]
    obtain ⟨hv,hvu⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU hu) (by simpa only [mem_singleton] using hvu)
  refine ⟨⟨{u},Z',singleton_nonempty _,?_,hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  · intro v hv
    rw [mem_singleton.mp hv]
    exact ⟨hu,⟨B,hB,hinter⟩⟩
  · simpa only [card_singleton,Nat.cast_one,mul_one] using hcredit

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma dense_move (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε a b : ℝ} (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer) (hab : a ≤ b)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hrange : ∀u ∈ M, a-δ < normDistance (X u) (X B.shell.center) ∧
      normDistance (X u) (X B.shell.center) < b+δ)
    (hcount : 765*δ ≤ (M.card : ℝ)*δ) (hdense : 3*(b-a) ≤ (M.card : ℝ)*δ) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  let Q := M.image (A.input P)
  have hQcard : Q.card = M.card := card_image_of_injective _ (A.input_injective P)
  obtain ⟨u₀,hu₀⟩ := hMn
  have hwidth := Record.interior_width H X (hinter u₀ hu₀)
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := dense_operation H G X hX A.radius_pos hε hF hZ hB
    (A.input_arrangement (hMU.trans hU) (fun u hu => hvalid u (hU (hMU hu))))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hAF u (hU (hMU hu)))
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; rfl) hno hwidth ha hb hab
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hrange u hu)
    (by intro D hD; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD; exact hinter u hu)
    (by intro D hD E hE hs; obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
        simpa [input,Record.excluded] using horder E hE hs)
    (by rwa [hQcard]) (by rwa [hQcard])
  have hmeta : ∀D ∈ Z', D ∈ Z ∨ D ∈ Q ∨ ∃E ∈ Z, ∃a b,
      D = E.restriction a b ∧ E.shell.inner ≤ a ∧ b ≤ E.shell.outer := by
    intro D hD
    rcases hmeta₀ D hD with hD | hD | ⟨a,b,heq,ha,hb,_⟩
    · exact Or.inl hD
    · exact Or.inr (Or.inl hD)
    · exact Or.inr (Or.inr ⟨B,hB,a,b,heq,ha,hb⟩)
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl (hAF u (hU (hMU hu)))) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact Or.inl rfl) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (M := M) (by
      intro D hD _
      obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
      exact ⟨u,hu,rfl⟩) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro D hD _ v hv _
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    obtain ⟨hv,hvM⟩ := mem_sdiff.mp hv
    exact A.disjoint (hU hv) (hU (hMU hu)) (fun hh => hvM (hh ▸ hu))
  refine ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',?_,hevol,howner,hfresh,hsep'⟩⟩
  rwa [hQcard] at hcredit

lemma sparse_move (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε a b : ℝ} {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U M : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    {B : Record n} (hB : B ∈ Z) (hno : B.avoided = none)
    (ha : B.shell.inner ≤ a) (hb : b ≤ B.shell.outer)
    (hMn : M.Nonempty) (hMU : M ⊆ U)
    (hinter : ∀u ∈ M, (A.input P u).Interior H X 256 δ B)
    (hexact : ∀u ∈ U, (A.input P u).InteriorTo (H := H) (X := X) δ Z →
      a-δ < normDistance (X u) (X B.shell.center) →
      normDistance (X u) (X B.shell.center) < b+δ → u ∈ M)
    (hwide : 255*δ ≤ b-a) (hsparse : (M.card : ℝ)*δ ≤ 3*(b-a))
    (hinner : (B.innerRecord A.owner (a+δ) (b-δ)).Valid H G X (q/4))
    (houter : (B.outsideRecord A.owner a b).Valid H G X (q/4)) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  obtain ⟨u₀,hu₀⟩ := hMn
  have hint := hinter u₀ hu₀
  have hov := hvalid u₀ (hU (hMU hu₀))
  have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
  have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
    hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
    (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
  obtain ⟨Z',hZ',hcredit,hmeta₀⟩ := sparse_operation H G X hX A.radius_pos
    (fun D hD => ⟨(hF D hD).1,(hF D hD).2.1⟩) hZ hB hno
    (Record.interior_width H X hint) ht ha hb hwide hsparse hinner houter
  let C := B.innerRecord A.owner (a+δ) (b-δ)
  let D := B.outsideRecord A.owner a b
  let Q : Finset (Record n) := {C,D}
  have hmeta : ∀E ∈ Z', E ∈ Z ∨ E ∈ Q ∨ ∃K ∈ Z, ∃c d,
      E = K.restriction c d ∧ K.shell.inner ≤ c ∧ d ≤ K.shell.outer := by
    intro E hE
    rcases hmeta₀ E hE with hE | rfl | rfl | ⟨c,d,heq,hc,hd,_⟩
    · exact Or.inl hE
    · exact Or.inr (Or.inl (mem_insert_self _ _))
    · exact Or.inr (Or.inl (mem_insert_of_mem (mem_singleton_self _)))
    · exact Or.inr (Or.inr ⟨B,hB,c,d,heq,hc,hd⟩)
  have href := Record.central_radialRefines (hZ.1 B hB).1 hno ht
    (by linarith [A.radius_pos] : B.shell.inner ≤ a+δ)
    (by linarith [A.radius_pos] : b-δ ≤ B.shell.outer) ha hb
  have hevol : Evolution (H := H) F Z Z' := metadata_evolution (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inr ⟨B,hB,href.1⟩
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,href.2⟩) hmeta
  have howner : OwnerEvolution A.owner Z Z' := A.metadata_owners (by
    intro E hE
    rcases mem_insert.mp hE with rfl | hE
    · exact Or.inl rfl
    · rw [mem_singleton.mp hE]
      exact Or.inr ⟨B,hB,rfl⟩) hmeta
  have hfresh := A.metadata_fresh (fun D hD => (hF D hD).1)
    (P := P) (M := M) (by
      intro E hE hEF
      have hh := (hF E hEF).1
      rcases mem_insert.mp hE with rfl | hE
      · simp [C,Record.innerRecord,RadialShell.hollow] at hh
      · rw [mem_singleton.mp hE] at hh
        simp [D,Record.outsideRecord,RadialShell.hollow] at hh) hmeta
  have hsep' : A.SameOwnerSeparated P (U\M) Z' := by
    apply A.metadata_separation sdiff_subset (fun D hD => (hF D hD).2.1) hevol hsep _ hmeta
    intro E hE hown u hu hintold
    rcases mem_insert.mp hE with rfl | hE
    · obtain ⟨hu,huM⟩ := mem_sdiff.mp hu
      by_cases hlo : a-δ < normDistance (X u) (X B.shell.center)
      · have hhi : b+δ ≤ normDistance (X u) (X B.shell.center) :=
          le_of_not_gt (fun hh => huM (hexact u hu hintold hlo hh))
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith [A.radius_pos])
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by
          have := not_lt.mp hlo
          linarith [A.radius_pos])
    · rw [mem_singleton.mp hE] at hown
      exact (hstrict.ne hown.symm).elim
  exact ⟨⟨M,Z',⟨u₀,hu₀⟩,fun u hu => ⟨hMU hu,⟨B,hB,hinter u hu⟩⟩,
    hZ',hcredit,hevol,howner,hfresh,hsep'⟩⟩

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma interior_move (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : LocallyConnectedReal H G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)} {U : Finset (Fin n)} (hU : U ⊆ A.centers)
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z)
    (hhalf : A.centers.card ≤ 2*(U.filter (fun u =>
      (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card) :
    Nonempty (InteriorMove A q ε P F Z U) := by
  by_cases hav : ∃u ∈ U, ∃B ∈ Z, B.avoided.isSome = true ∧
      (A.input P u).Interior H X 256 δ B
  · obtain ⟨u,hu,B,hB,hav,hint⟩ := hav
    exact A.avoiding_move hX hε hU hF hAF hvalid hZ horder hsep hu hB hav hint
  let I := U.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z)
  have hIU : I ⊆ U := by
    intro u hu
    exact (mem_filter.mp hu).1
  have hI : ∀u ∈ I, (A.input P u).InteriorTo (H := H) (X := X) δ Z :=
    fun u hu => (mem_filter.mp hu).2
  obtain ⟨R,hR,hRc,hlarge⟩ := A.large_component hq hconn hη (hIU.trans hU) hhalf
  have hno : ∀u ∈ I, ∀D ∈ Z, (A.input P u).Interior H X 256 δ D → D.avoided = none := by
    intro u hu D hD hint
    cases hh : D.avoided with
    | none => rfl
    | some t => exact (hav ⟨u,hIU hu,D,hD,by simp [hh],hint⟩).elim
  obtain ⟨B,a,b,M,u₁,u₂,hB,hBno,ha,hb,hab,hMn,hMeq,hinter,hdich,
    hu₁,hu₂,hv₁,hv₂,hv₁r,hv₂r,hu₁r,hu₂r⟩ := A.radial_group hX (hIU.trans hU) hZ
      (fun u hu => (hvalid u (hU (hIU hu))).1) horder hI hno hlarge
  have hMI : M ⊆ I := by rw [hMeq]; exact filter_subset _ _
  have hMU : M ⊆ U := hMI.trans hIU
  have hrange : ∀u ∈ M, a-δ < normDistance (X u) (X B.shell.center) ∧
      normDistance (X u) (X B.shell.center) < b+δ := by
    intro u hu
    rw [hMeq] at hu
    exact (mem_filter.mp hu).2
  have hdich' : (768:ℝ) ≤ M.card ∨ 255*δ ≤ b-a := by exact_mod_cast hdich
  by_cases hdense : 3*(b-a) ≤ (M.card : ℝ)*δ
  · have hcount := AssignedSelection.dense_count A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hdense
    exact A.dense_move hX hε hU hF hAF hvalid hZ horder hsep hB hBno ha hb hab
      hMn hMU hinter hrange hcount hdense
  · have hsparse : (M.card : ℝ)*δ ≤ 3*(b-a) := (not_le.mp hdense).le
    have hwide := AssignedSelection.sparse_width A.radius_pos.le (by norm_num : (768:ℝ) ≤ 768)
      hdich' hsparse
    obtain ⟨u₀,hu₀⟩ := hMn
    have hint := hinter u₀ hu₀
    have hov := hvalid u₀ (hU (hMU hu₀))
    have ht := Record.candidate_ancestor H hov.1 (hZ.1 B hB).1 (fun hs => by simpa [input,Record.excluded] using horder B hB hs) hint.1
    have hstrict : A.owner ⊂ B.owner := Record.strict_owner_of_interior hX
      hov.1 (hZ.1 B hB).1 hov.2.2.1 A.radius_pos.le rfl
      (fun hs => by simpa [input,Record.excluded] using horder B hB hs) (hsep u₀ (hMU hu₀) ⟨B,hB,hint⟩ B hB) hint
    obtain ⟨e,he⟩ := (A.neighbor_spec (hU (hIU hu₁))).2.2
    obtain ⟨hin,hout⟩ := Record.central_valid H G X (hZ.1 B hB) hBno hq.le hconn ht hstrict
      ha hb A.radius_pos (by linarith [A.radius_pos]) hR hRc
      (A.endpoint u₁ (hU (hIU hu₁))).1 (A.endpoint u₂ (hU (hIU hu₂))).1
      hv₁ hv₂ hu₁r hu₂r hv₁r hv₂r he
    apply A.sparse_move hX hU hF hvalid hZ horder hsep hB hBno ha hb ⟨u₀,hu₀⟩ hMU
      hinter _ hwide hsparse hin hout
    intro u hu hint hlo hhi
    rw [hMeq]
    exact mem_filter.mpr ⟨mem_filter.mpr ⟨hu,hint⟩,hlo,hhi⟩

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}

lemma ownerEvolution_refl (t : Finset (Fin n)) (Z : Finset (Record n)) : OwnerEvolution t Z Z := by
  intro D hD
  exact Or.inr ⟨D,hD,rfl⟩

lemma ownerEvolution_trans {t : Finset (Fin n)} {Z W V : Finset (Record n)}
    (h1 : OwnerEvolution t Z W) (h2 : OwnerEvolution t W V) : OwnerEvolution t Z V := by
  intro D hD
  rcases h2 D hD with hh | ⟨E,hE,hh⟩
  · exact Or.inl hh
  · rcases h1 E hE with he | ⟨B,hB,he⟩
    · exact Or.inl (hh.trans he)
    · exact Or.inr ⟨B,hB,hh.trans he⟩

namespace AssignedBag

lemma interior_loop (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : LocallyConnectedReal H G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (U : Finset (Fin n)) (hU : U ⊆ A.centers) (Z : Finset (Record n))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (hsep : A.SameOwnerSeparated P U Z) :
    ∃(V : Finset (Fin n)) (Z' : Finset (Record n)), V ⊆ U ∧
      LabeledArrangement H G X (q/4) Z' ∧
      2*(V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')).card <
        A.centers.card ∧
      (∑D ∈ Z, Record.phaseToken F δ ε D)+
        AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ ≤
          ∑D ∈ Z', Record.phaseToken F δ ε D ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ U\V, D = A.input P u) ∧
      A.SameOwnerSeparated P V Z' := by
  induction U using Finset.strongInduction generalizing Z with
  | H U ih =>
    by_cases hstop : 2*(U.filter (fun u =>
        (A.input P u).InteriorTo (H := H) (X := X) δ Z)).card < A.centers.card
    · refine ⟨U,Z,Subset.refl _,hZ,hstop,?_,fun _ h => h,ownerEvolution_refl _ _,
        fun _ h _ => Or.inl h,hsep⟩
      simp
    · obtain ⟨W⟩ := A.interior_move hX hq hconn hη hε hU hF hAF hvalid hZ horder hsep
        (not_lt.mp hstop)
      have hMU : W.treated ⊆ U := fun u hu => (W.treated_interior u hu).1
      have hss : U\W.treated ⊂ U := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨sdiff_subset,?_⟩
        intro hh
        obtain ⟨u,hu⟩ := W.nonempty
        have hm : u ∈ U\W.treated := hh.symm ▸ hMU hu
        exact (mem_sdiff.mp hm).2 hu
      obtain ⟨V,Z',hVU,hZ',hstop',hcredit',hinter',howners',hfresh',hsep'⟩ := ih (U\W.treated) hss
        (sdiff_subset.trans hU) W.next W.valid (ownerEvolution_order horder W.owners) W.separation
      have hcards : ((U\W.treated).card : ℝ)+(W.treated.card : ℝ) = (U.card : ℝ) := by
        exact_mod_cast card_sdiff_add_card_eq_card hMU
      refine ⟨V,Z',hVU.trans sdiff_subset,hZ',hstop',?_,?_,
        ownerEvolution_trans W.owners howners',?_,hsep'⟩
      · calc
          (∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*((U.card : ℝ)-(V.card : ℝ))*δ =
            ((∑D ∈ Z, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(W.treated.card : ℝ)*δ)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ := by
                rw [←hcards]
                ring
          _ ≤ (∑D ∈ W.next, Record.phaseToken F δ ε D)+
              AssignedAccounting.theta*(((U\W.treated).card : ℝ)-(V.card : ℝ))*δ :=
            add_le_add W.credit (le_refl _)
          _ ≤ _ := hcredit'
      · intro B hB
        exact evolution_interior A.radius_pos.le (fun D hD => (hF D hD).2.1)
          W.evolution (hinter' B hB)
      · intro D hD hDF
        rcases hfresh' D hD hDF with hD | ⟨u,hu,heq⟩
        · rcases W.fresh D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨u,mem_sdiff.mpr ⟨hMU hu,
              fun hv => (mem_sdiff.mp (hVU hv)).2 hu⟩,heq⟩
        · exact Or.inr ⟨u,mem_sdiff.mpr ⟨sdiff_subset (mem_sdiff.mp hu).1,
            (mem_sdiff.mp hu).2⟩,heq⟩

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}
namespace Record

lemma fresh_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {B : Record n} (hwidth : B.shell.width = δ) (hno : B.avoided = none) :
    B.baseToken ε = AssignedAccounting.fresh δ ε := by
  simp only [baseToken,hwidth,hno,Option.isSome_none,AssignedAccounting.base,
    Bool.false_eq_true,↓reduceIte,AssignedAccounting.fresh,div_one]
  exact max_eq_left (by linarith)

lemma shrink_refines {δ : ℝ} (hδ : 0 ≤ δ) (F : Finset (Record n)) (B : Record n) :
    (B.shrinkRecord F δ).Refines H X B := by
  by_cases hB : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hB]
    exact ⟨Set.Subset.refl _,Subset.refl _⟩
  · simp only [shrinkRecord,ite_eq_right hB]
    exact B.restriction_refines H X (by linarith) (by linarith)

omit [PseudoMetricSpace Coord] in
lemma shrink_valid {δ q : ℝ} (hδ : 0 ≤ δ) {F : Finset (Record n)} {B : Record n}
    (hB : B.Valid H G X q) (hw : 0 < (B.shrinkRecord F δ).shell.width) :
    (B.shrinkRecord F δ).Valid H G X q := by
  by_cases hf : B ∈ F
  · simpa only [shrinkRecord,ite_eq_left hf] using hB
  · simp only [shrinkRecord,ite_eq_right hf] at hw ⊢
    exact Record.restrict_valid H G X hB (by linarith) (by linarith)
      (by simpa only [restriction,RadialShell.hollow,RadialShell.width,sub_pos] using hw)

lemma shrink_base {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) : (B.shrinkRecord F δ).baseToken ε = B.shrinkValue F δ ε := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,shrinkValue,ite_eq_left hf]
    exact fresh_base hδ hε (hF B hf).1 (hF B hf).2
  · simp only [shrinkRecord,shrinkValue,ite_eq_right hf,baseToken,restriction,RadialShell.hollow,
      RadialShell.width]
    congr 1
    ring

lemma shrink_cost {δ ε : ℝ} (hδ : 0 ≤ δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (B : Record n) :
    0 ≤ B.phaseToken F δ ε-B.shrinkValue F δ ε ∧
      B.phaseToken F δ ε-B.shrinkValue F δ ε ≤
        256*(B.baseToken ε-B.phaseToken F δ ε) := by
  by_cases hf : B ∈ F
  · rw [phaseToken,shrinkValue,ite_eq_left hf,ite_eq_left hf,
      fresh_base hδ hscale (hF B hf).1 (hF B hf).2]
    simp
  · simp only [phaseToken,shrinkValue,ite_eq_right hf,baseToken]
    exact AssignedAccounting.shrink_cost _ hδ hε hscale

lemma shrink_discard {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 ≤ ε)
    {F : Finset (Record n)} (hF : ∀B ∈ F, B.shell.width = δ)
    (B : Record n) (hw : ¬0 < (B.shrinkRecord F δ).shell.width) :
    B.shrinkValue F δ ε = 0 := by
  by_cases hf : B ∈ F
  · rw [shrinkRecord,ite_eq_left hf,hF B hf] at hw
    exact (hw hδ).elim
  · rw [shrinkValue,ite_eq_right hf]
    apply AssignedAccounting.base_discard _ _ hε
    rw [shrinkRecord,ite_eq_right hf] at hw
    dsimp [restriction,RadialShell.hollow,RadialShell.width] at hw ⊢
    linarith [not_lt.mp hw]

lemma border_shrink_compatible {δ : ℝ} (_hδ : 0 ≤ δ) {F : Finset (Record n)}
    (hF : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    {A B : Record n} (hA : A ∈ F) (hne : A ≠ B)
    (hball : A.shell = RadialShell.ball A.shell.center δ)
    (hbor : ¬A.Interior H X 256 δ B) :
    A.Compatible H X (B.shrinkRecord F δ) := by
  by_cases hf : B ∈ F
  · simp only [shrinkRecord,ite_eq_left hf]
    exact Or.inl (hF A hA B hf hne)
  · simp only [shrinkRecord,ite_eq_right hf]
    by_cases hdis : Disjoint (A.conflict H) (B.conflict H)
    · exact Or.inr hdis
    · have hmeet : (A.conflict H ∩ B.conflict H).Nonempty := by
        apply nonempty_iff_ne_empty.mpr
        exact fun hh => hdis (Finset.disjoint_iff_inter_eq_empty.mpr hh)
      left
      rw [hball]
      by_cases hlo : B.shell.inner+256*δ < normDistance (X A.shell.center) (X B.shell.center)
      · have hhi : B.shell.outer-256*δ ≤ normDistance (X A.shell.center) (X B.shell.center) :=
          le_of_not_gt (fun hh => hbor ⟨hmeet,hlo,hh⟩)
        exact RadialShell.ball_disjoint_hollow_lower X _ _ (by linarith)
      · exact RadialShell.ball_disjoint_hollow_upper X _ _ (by linarith [not_lt.mp hlo])

end Record

lemma shrinkFamily_valid {q δ : ℝ} (hδ : 0 ≤ δ) {F Z : Finset (Record n)}
    (hZ : LabeledArrangement H G X q Z) : LabeledArrangement H G X q (shrinkFamily F Z δ) := by
  constructor
  · intro D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    exact Record.shrink_valid hδ (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
  · intro D hD E hE hne hgeo
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    obtain ⟨C,hC,rfl⟩ := mem_image.mp hE
    have hh := Record.compatible_refinements H X
      (labeled_pair H G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1
        (fun hh => hne (congrArg (Record.shrinkRecord F δ) hh)))
      (Record.shrink_refines hδ F B) (Record.shrink_refines hδ F C)
    exact hh.resolve_left hgeo

lemma shrinkFamily_sum (hX : ∀v, isProfile (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536) {F Z : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none)
    (hZ : LabeledArrangement H G X q Z) :
    ∑D ∈ shrinkFamily F Z δ, D.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε := by
  have hinj : ∀B ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      ∀C ∈ Z.filter (fun B => 0 < (B.shrinkRecord F δ).shell.width),
      B.shrinkRecord F δ = C.shrinkRecord F δ → B = C := by
    intro B hB C hC heq
    by_contra hh
    have hv := Record.shrink_valid hδ.le (hZ.1 B (mem_filter.mp hB).1) (mem_filter.mp hB).2
    have hc := Record.compatible_refinements H X
      (labeled_pair H G X hZ (mem_filter.mp hB).1 (mem_filter.mp hC).1 hh)
      (Record.shrink_refines hδ.le F B) (Record.shrink_refines hδ.le F C)
    rw [←heq] at hc
    exact (B.shrinkRecord F δ).compatible_self_iff H X hX hv.1 hv.2.2.1 hc
  rw [shrinkFamily,sum_image hinj,sum_filter]
  apply sum_congr rfl
  intro B hB
  by_cases hw : 0 < (B.shrinkRecord F δ).shell.width
  · rw [ite_eq_left hw,Record.shrink_base hδ.le hscale hF]
  · rw [ite_eq_right hw,Record.shrink_discard hδ hε (fun D hD => (hF D hD).1) B hw]

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

lemma border_transition (hX : ∀v, isProfile (X v)) {q δ ε : ℝ}
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    {F Z K : Finset (Record n)}
    (hF : ∀B ∈ F, B.shell.ordinary = true ∧ B.shell.width = δ ∧ B.avoided = none)
    (hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ)
    (hFgeo : ∀A ∈ F, ∀B ∈ F, A ≠ B → Disjoint (A.shell.support X) (B.shell.support X))
    (hFvalid : LabeledArrangement H G X q F)
    (hZ : LabeledArrangement H G X q Z) (hKF : K ⊆ F) (hKZ : Disjoint K Z)
    (hbor : ∀A ∈ K, ¬A.InteriorTo (H := H) (X := X) δ Z) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X q Z' ∧
      (∑B ∈ Z, B.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ≤
        ∑B ∈ Z', B.baseToken ε ∧
      (∀D ∈ Z', D ∈ K ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let p := ∑B ∈ Z, B.phaseToken F δ ε
  let q' := ∑B ∈ Z, B.baseToken ε
  have hw : ∀B ∈ F, B.shell.width = δ ∧ B.avoided = none :=
    fun B hB => (hF B hB).2
  by_cases hex : AssignedAccounting.theta*(K.card : ℝ)*δ ≤ q'-p
  · exact ⟨Z,hZ,by dsimp [p,q'] at * <;> linarith,fun D hD => Or.inr ⟨D,hD,rfl⟩⟩
  let W := shrinkFamily F Z δ
  have hW : LabeledArrangement H G X q W := shrinkFamily_valid hδ.le hZ
  have hK := labeled_subset H G X hFvalid hKF
  have hKW : ∀A ∈ K, ∀B ∈ W, A.Compatible H X B := by
    intro A hA D hD
    obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
    have hBZ : B ∈ Z := (mem_filter.mp hB).1
    exact Record.border_shrink_compatible hδ.le hFgeo (hKF hA)
      (fun heq => Finset.disjoint_left.mp hKZ hA (heq.symm ▸ hBZ))
      (hFball A (hKF hA)) (fun hh => hbor A hA ⟨B,hBZ,hh⟩)
  have hdis : Disjoint K W := labeled_sets_disjoint H G X hX hK hKW
  have hsum : ∑B ∈ W, B.baseToken ε = ∑B ∈ Z, B.shrinkValue F δ ε :=
    shrinkFamily_sum hX hδ hε hscale hw hZ
  have hkSum : ∑B ∈ K, B.baseToken ε = (K.card : ℝ)*AssignedAccounting.fresh δ ε := by
    calc
      ∑B ∈ K, B.baseToken ε = ∑B ∈ K, AssignedAccounting.fresh δ ε :=
        sum_congr rfl (fun B hB => Record.fresh_base hδ.le hscale (hw B (hKF hB)).1 (hw B (hKF hB)).2)
      _ = _ := by simp
  have hcost : p-(∑B ∈ W, B.baseToken ε) ≤ 256*(q'-p) := by
    rw [hsum]
    dsimp [p,q']
    rw [←sum_sub_distrib,←sum_sub_distrib,Finset.mul_sum]
    exact sum_le_sum (fun B hB => (Record.shrink_cost hδ.le hε hscale hw B).2)
  have hdef : p-(∑B ∈ W, B.baseToken ε) ≤ (K.card : ℝ)*δ/2 := by
    have hh := not_le.mp hex
    dsimp [AssignedAccounting.theta] at hh
    linarith
  have hpay := AssignedAccounting.border_payment hδ.le hscale
    (Nat.cast_nonneg K.card : (0:ℝ) ≤ _) hdef
  refine ⟨K∪W,labeled_union H G X hK hW hKW,?_,?_⟩
  · rw [sum_union hdis,hkSum]
    dsimp [p] at hpay
    linarith
  · intro D hD
    rcases mem_union.mp hD with hD | hD
    · exact Or.inl hD
    · obtain ⟨B,hB,rfl⟩ := mem_image.mp hD
      refine Or.inr ⟨B,(mem_filter.mp hB).1,?_⟩
      dsimp [Record.shrinkRecord]
      split_ifs <;> rfl

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}
namespace AssignedBag

lemma loop_with_border_debt (A : AssignedBag H G X δ η) (hX : ∀v, isProfile (X v))
    {q ε : ℝ} (hq : 0 < q) (hconn : LocallyConnectedReal H G q)
    (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536) {P : Finset (Finset (Fin n))}
    {F Z : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (hAF : ∀u ∈ A.centers, A.input P u ∈ F)
    (hvalid : ∀u ∈ A.centers, (A.input P u).Valid H G X (q/4))
    (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀D ∈ Z, D.owner ⊂ A.owner → D.owner ∈ P)
    (howner : ∀D ∈ Z, D.owner ≠ A.owner) :
    ∃(Z' K : Finset (Record n)), LabeledArrangement H G X (q/4) Z' ∧
      K ⊆ A.centers.image (A.input P) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(A.centers.card : ℝ)*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      OwnerEvolution A.owner Z Z' ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃u ∈ A.centers, D = A.input P u) := by
  obtain ⟨V,Z',hVA,hZ',hstop,hcredit,hinter,howners,hfresh,_⟩ :=
    A.interior_loop hX hq hconn hη hε hF hAF hvalid A.centers (Subset.refl _) Z hZ horder
      (fun u hu hint B hB hh => (howner B hB hh).elim)
  let I := V.filter (fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let B := V.filter (fun u => ¬(A.input P u).InteriorTo (H := H) (X := X) δ Z')
  let K := B.image (A.input P)
  have hKV : ∀D ∈ K, ∃u ∈ V, D = A.input P u ∧
      ¬D.InteriorTo (H := H) (X := X) δ Z' := by
    intro D hD
    obtain ⟨u,hu,rfl⟩ := mem_image.mp hD
    exact ⟨u,(mem_filter.mp hu).1,rfl,(mem_filter.mp hu).2⟩
  have hKcard : K.card = B.card := card_image_of_injective _ (A.input_injective P)
  have hcards : (I.card : ℝ)+(K.card : ℝ) = (V.card : ℝ) := by
    rw [hKcard]
    exact_mod_cast card_filter_add_card_filter_not (s := V)
      (p := fun u => (A.input P u).InteriorTo (H := H) (X := X) δ Z')
  have hI : 2*(I.card : ℝ) < A.centers.card := by exact_mod_cast hstop
  have hcount : (A.centers.card : ℝ)/2 ≤ (A.centers.card : ℝ)-(V.card : ℝ)+(K.card : ℝ) := by
    linarith
  have hnum := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcount (by norm_num [AssignedAccounting.theta] :
      (0:ℝ) ≤ AssignedAccounting.theta)) A.radius_pos.le
  refine ⟨Z',K,hZ',?_,?_,fun D hD => (hKV D hD).choose_spec.2.2,?_,hinter,howners,?_⟩
  · intro D hD
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    exact mem_image.mpr ⟨u,hVA hu,rfl⟩
  · rw [Finset.disjoint_left]
    intro D hD hDZ
    obtain ⟨u,hu,rfl,_⟩ := hKV D hD
    rcases hfresh _ hDZ (hAF u (hVA hu)) with hh | ⟨v,hv,heq⟩
    · exact howner _ hh rfl
    · have he : u = v := A.input_injective P heq
      exact (mem_sdiff.mp hv).2 (he ▸ hu)
  · dsimp [AssignedAccounting.theta] at hnum hcredit ⊢
    nlinarith
  · intro D hD hDF
    rcases hfresh D hD hDF with hh | ⟨u,hu,heq⟩
    · exact Or.inl hh
    · exact Or.inr ⟨u,(mem_sdiff.mp hu).1,heq⟩

end AssignedBag
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}

lemma phase_loops {ι : Type*} [DecidableEq ι]
    (A : ι → AssignedBag H G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, isProfile (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η) (hε : ε ≤ δ/1536)
    {F : Finset (Record n)}
    (hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (Z : Finset (Record n)) (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃(Z' K : Finset (Record n)), LabeledArrangement H G X (q/4) Z' ∧ K ⊆ F ∧
      (∀D ∈ K, ∃i ∈ J, D.owner = (A i).owner) ∧ Disjoint K Z' ∧
      (∀B ∈ K, ¬B.InteriorTo (H := H) (X := X) δ Z') ∧
      (∑D ∈ Z, D.phaseToken F δ ε)+
        (AssignedAccounting.theta/2)*(∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤
          (∑D ∈ Z', D.phaseToken F δ ε)+AssignedAccounting.theta*(K.card : ℝ)*δ ∧
      (∀B : Record n, B.InteriorTo (H := H) (X := X) δ Z' →
        B.InteriorTo (H := H) (X := X) δ Z) ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) ∧
      (∀D ∈ Z', D ∈ F → D ∈ Z ∨ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u) := by
  induction J using Finset.strongInduction generalizing Z with
  | H J ih =>
    by_cases hn : J.Nonempty
    · obtain ⟨j,hj,hmax⟩ := J.exists_max_image (fun i => (A i).owner.card) hn
      obtain ⟨Z₁,K₁,hZ₁,hKA,hKZ₁,hbor₁,hcredit₁,hint₁,hown₁,hfresh₁⟩ :=
        (A j).loop_with_border_debt hX hq hconn hη hε hF (hAF j hj) (hvalid j hj)
          hZ (horder j hj) (howner j hj)
      have hKi : ∀D ∈ K₁, ∃u ∈ (A j).centers, D = (A j).input (P j) u := by
        intro D hD
        obtain ⟨u,hu,heq⟩ := mem_image.mp (hKA hD)
        exact ⟨u,hu,heq.symm⟩
      have hKown : ∀D ∈ K₁, D.owner = (A j).owner := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        rfl
      have hKAf : K₁ ⊆ F := by
        intro D hD
        obtain ⟨u,hu,rfl⟩ := hKi D hD
        exact hAF j hj u hu
      have hInj : Set.InjOn (fun i => (A i).owner) (J.erase j) := hAi.mono (erase_subset _ _)
      have horder₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ⊂ (A i).owner → D.owner ∈ P i := by
        intro i hi D hD hs
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · rw [hh] at hs
          have hcard := card_lt_card hs
          have hmax := hmax i (mem_of_mem_erase hi)
          omega
        · rw [hh] at hs ⊢
          exact horder i (mem_of_mem_erase hi) B hB hs
      have howner₁ : ∀i ∈ J.erase j, ∀D ∈ Z₁, D.owner ≠ (A i).owner := by
        intro i hi D hD heq
        rcases hown₁ D hD with hh | ⟨B,hB,hh⟩
        · exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans hh))
        · exact howner i (mem_of_mem_erase hi) B hB (hh.symm.trans heq)
      obtain ⟨Z₂,K₂,hZ₂,hKF₂,hKown₂,hKZ₂,hbor₂,hcredit₂,hint₂,hown₂,hfresh₂⟩ :=
        ih (J.erase j) (erase_ssubset hj) hInj
          (fun i hi => hAF i (mem_of_mem_erase hi))
          (fun i hi => hvalid i (mem_of_mem_erase hi)) Z₁ hZ₁ horder₁ howner₁
      have hdis : Disjoint K₁ K₂ := by
        rw [Finset.disjoint_left]
        intro D hD hD₂
        obtain ⟨i,hi,heq⟩ := hKown₂ D hD₂
        exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (heq.symm.trans (hKown D hD)))
      have hKZ : Disjoint K₁ Z₂ := by
        rw [Finset.disjoint_left]
        intro D hD hDZ
        rcases hfresh₂ D hDZ (hKAf hD) with hD₁ | ⟨i,hi,u,hu,heq⟩
        · exact Finset.disjoint_left.mp hKZ₁ hD hD₁
        · have hoi : D.owner = (A i).owner := congrArg Record.owner heq
          exact (mem_erase.mp hi).1 (hAi (mem_of_mem_erase hi) hj (hoi.symm.trans (hKown D hD)))
      refine ⟨Z₂,K₁∪K₂,hZ₂,union_subset hKAf hKF₂,?_,disjoint_union_left.mpr ⟨hKZ,hKZ₂⟩,
        ?_,?_,fun B hh => hint₁ B (hint₂ B hh),?_,?_⟩
      · intro D hD
        rcases mem_union.mp hD with hD | hD
        · exact ⟨j,hj,hKown D hD⟩
        · obtain ⟨i,hi,hh⟩ := hKown₂ D hD
          exact ⟨i,mem_of_mem_erase hi,hh⟩
      · intro D hD hint
        rcases mem_union.mp hD with hD | hD
        · exact hbor₁ D hD (hint₂ D hint)
        · exact hbor₂ D hD hint
      · have hsum := sum_erase_add J (fun i => ((A i).centers.card : ℝ)) hj
        have hcard : ((K₁∪K₂).card : ℝ) = (K₁.card : ℝ)+(K₂.card : ℝ) := by
          exact_mod_cast card_union_of_disjoint hdis
        rw [hcard,←hsum]
        dsimp [AssignedAccounting.theta] at hcredit₁ hcredit₂ ⊢
        nlinarith
      · intro D hD
        rcases hown₂ D hD with ⟨i,hi,hh⟩ | ⟨B,hB,hh⟩
        · exact Or.inl ⟨i,mem_of_mem_erase hi,hh⟩
        · rcases hown₁ B hB with heq | ⟨C,hC,heq⟩
          · exact Or.inl ⟨j,hj,hh.trans heq⟩
          · exact Or.inr ⟨C,hC,hh.trans heq⟩
      · intro D hD hDF
        rcases hfresh₂ D hD hDF with hD | ⟨i,hi,u,hu,heq⟩
        · rcases hfresh₁ D hD hDF with hD | ⟨u,hu,heq⟩
          · exact Or.inl hD
          · exact Or.inr ⟨j,hj,u,hu,heq⟩
        · exact Or.inr ⟨i,mem_of_mem_erase hi,u,hu,heq⟩
    · have he : J = ∅ := not_nonempty_iff_eq_empty.mp hn
      subst J
      refine ⟨Z,∅,hZ,empty_subset _,?_,disjoint_empty_left _,?_,?_,fun _ hh => hh,?_,?_⟩
      · simp
      · simp
      · simp
      · intro D hD
        exact Or.inr ⟨D,hD,rfl⟩
      · intro D hD _
        exact Or.inl hD

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {δ η : ℝ}

lemma assigned_phase {ι : Type*} [DecidableEq ι]
    (A : ι → AssignedBag H G X δ η) (P : ι → Finset (Finset (Fin n)))
    (hX : ∀v, isProfile (X v)) {q ε : ℝ} (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    (hδ : 0 < δ) (hε : 0 ≤ ε) (hscale : ε ≤ δ/1536)
    (J : Finset ι) (hAi : Set.InjOn (fun i => (A i).owner) J)
    (hvalid : ∀i ∈ J, ∀u ∈ (A i).centers, ((A i).input (P i) u).Valid H G X (q/4))
    (hgeo : ∀i ∈ J, ∀u ∈ (A i).centers, ∀j ∈ J, ∀v ∈ (A j).centers,
      ((A i).input (P i) u) ≠ ((A j).input (P j) v) →
      Disjoint ((RadialShell.ball u δ).support X) ((RadialShell.ball v δ).support X))
    (Z : Finset (Record n)) (hZ : LabeledArrangement H G X (q/4) Z)
    (horder : ∀i ∈ J, ∀D ∈ Z, D.owner ⊂ (A i).owner → D.owner ∈ P i)
    (howner : ∀i ∈ J, ∀D ∈ Z, D.owner ≠ (A i).owner) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken δ)+(AssignedAccounting.theta/2)*
        (∑i ∈ J, ((A i).centers.card : ℝ))*δ ≤ ∑D ∈ Z', D.baseToken ε ∧
      (∀D ∈ Z', (∃i ∈ J, D.owner = (A i).owner) ∨ ∃B ∈ Z, D.owner = B.owner) := by
  let F := J.biUnion (fun i => ((A i).centers.image ((A i).input (P i))))
  have hFmem : ∀D : Record n, D ∈ F ↔ ∃i ∈ J, ∃u ∈ (A i).centers, D = (A i).input (P i) u := by
    intro D
    simp only [F,mem_biUnion,mem_image]
    constructor
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
    · rintro ⟨i,hi,u,hu,heq⟩
      exact ⟨i,hi,u,hu,heq.symm⟩
  have hF : ∀D ∈ F, D.shell.ordinary = true ∧ D.shell.width = δ ∧ D.avoided = none := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    simp [AssignedBag.input,RadialShell.ball,RadialShell.width]
  have hFball : ∀B ∈ F, B.shell = RadialShell.ball B.shell.center δ := by
    intro D hD
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
    rfl
  have hFg : ∀B ∈ F, ∀D ∈ F, B ≠ D → Disjoint (B.shell.support X) (D.shell.support X) := by
    intro B hB D hD hne
    obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem B).mp hB
    obtain ⟨j,hj,v,hv,rfl⟩ := (hFmem D).mp hD
    exact hgeo i hi u hu j hj v hv hne
  have hFv : LabeledArrangement H G X (q/4) F := by
    refine ⟨?_,?_⟩
    · intro D hD
      obtain ⟨i,hi,u,hu,rfl⟩ := (hFmem D).mp hD
      exact hvalid i hi u hu
    · intro B hB D hD hne hh
      exact (hh (hFg B hB D hD hne)).elim
  have hAF : ∀i ∈ J, ∀u ∈ (A i).centers, (A i).input (P i) u ∈ F :=
    fun i hi u hu => (hFmem _).mpr ⟨i,hi,u,hu,rfl⟩
  obtain ⟨Z₁,K,hZ₁,hKF,hKo,hKZ,hbor,hcredit,hint,hown,hfresh⟩ :=
    phase_loops A P hX hq hconn hη hscale hF J hAi hAF hvalid Z hZ horder howner
  obtain ⟨Z₂,hZ₂,hcredit₂,hown₂⟩ :=
    border_transition hX hδ hε hscale hF hFball hFg hFv hZ₁ hKF hKZ hbor
  have hsum : ∑D ∈ Z, D.phaseToken F δ ε = ∑D ∈ Z, D.baseToken δ := by
    apply sum_congr rfl
    intro D hD
    have hn : D ∉ F := by
      intro hf
      obtain ⟨i,hi,u,hu,heq⟩ := (hFmem D).mp hf
      exact howner i hi D hD (congrArg Record.owner heq)
    simp only [Record.phaseToken,ite_eq_right hn,Record.baseToken]
  refine ⟨Z₂,hZ₂,?_,?_⟩
  · rw [hsum] at hcredit
    linarith
  · intro D hD
    rcases hown₂ D hD with hDK | ⟨B,hB,heq⟩
    · exact Or.inl (hKo D hDK)
    · rcases hown B hB with ⟨i,hi,hoi⟩ | ⟨C,hC,hoi⟩
      · exact Or.inl ⟨i,hi,heq.trans hoi⟩
      · exact Or.inr ⟨C,hC,heq.trans hoi⟩

end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

lemma owner_mem (i : Fin F.count) : (F.bag i).owner ∈ F.owners := mem_image.mpr ⟨i,mem_univ _,rfl⟩
lemma owners_nodes : F.owners ⊆ H.nodes := by
  intro S hS
  obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
  exact (F.bag i).owner_mem

lemma input_valid {q : ℝ} (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (i : Fin F.count) {u : Fin n} (hu : u ∈ (F.bag i).centers) :
    ((F.bag i).input (F.predecessors E i) u).Valid H G X (q/4) := by
  have hbound := parent_boundary_lower H G hconn (F.bag i).owner_mem (F.bag i).nonroot
  have hassign := (F.bag i).assignment
  have hc : (3072:ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    have ha := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (parentBoundary H G (F.bag i).owner).card)
    have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (3072:ℝ)/q by positivity)
    have heq : (3072:ℝ)/q*q = 3072 := by field_simp
    rw [heq] at hb
    linarith
  apply (F.bag i).input_valid hX hq.le hconn
    (by exact_mod_cast (show (1:ℝ) < ((F.bag i).centers.card : ℝ) by linarith))
    (fun S hS => ⟨hE (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) hu (hprot i u hu)

lemma phase {q ε : ℝ} (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    (hε : 0 ≤ ε) (hscale : ε ≤ F.radius/1536)
    {E : Finset (Finset (Fin n))} (hE : E ⊆ H.nodes) (hprot : F.ProtectedFrom E)
    (hdis : Disjoint E F.owners)
    (Z : Finset (Record n)) (hZ : LabeledArrangement H G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X (q/4) Z' ∧
      (∑D ∈ Z, D.baseToken F.radius)+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z', D.baseToken ε ∧ (∀D ∈ Z', D.owner ∈ E∪F.owners) := by
  obtain ⟨Z',hZ',hc,ho⟩ := assigned_phase F.bag (F.predecessors E) hX hq hconn hη
    F.positive hε hscale univ F.owner_injective.injOn
    (fun i _ u hu => F.input_valid hX hq hconn hη hE hprot i hu)
    (by
      intro i hi u hu j hj v hv hne
      apply F.separated i u hu j v hv
      by_cases hh : i = j
      · right
        intro he
        subst j; subst v
        exact hne rfl
      · exact Or.inl hh)
    Z hZ
    (fun i _ D hD hs => mem_filter.mpr ⟨hown D hD,hs⟩)
    (fun i _ D hD heq => Finset.disjoint_left.mp hdis (hown D hD) (heq ▸ F.owner_mem i))
  refine ⟨Z',hZ',?_,?_⟩
  · simpa only [mass,mul_assoc] using hc
  · intro D hD
    rcases ho D hD with ⟨i,hi,heq⟩ | ⟨B,hB,heq⟩
    · exact mem_union_right _ (heq ▸ F.owner_mem i)
    · exact mem_union_left _ (heq ▸ hown B hB)

end AssignedFamily

namespace AssignedSequence

lemma radius_nonneg (L : List (Family (H := H) (G := G) (X := X) (η := η))) :
    0 ≤ initialRadius L := by
  cases L with
  | nil => exact le_refl _
  | cons F L => exact F.positive.le

lemma construct {q : ℝ} (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (E : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes)
    (hready : Ready E L) (Z : Finset (Record n)) (hZ : LabeledArrangement H G X (q/4) Z)
    (hown : ∀D ∈ Z, D.owner ∈ E) {credit : ℝ}
    (hcredit : credit ≤ ∑D ∈ Z, D.baseToken (initialRadius L)) :
    ∃Z' : Finset (Record n), LabeledArrangement H G X (q/4) Z' ∧
      credit+(AssignedAccounting.theta/2)*mass L ≤ ∑D ∈ Z', D.shell.width := by
  induction L generalizing E Z credit with
  | nil =>
    refine ⟨Z,hZ,?_⟩
    simp only [mass,mul_zero,add_zero] at *
    apply hcredit.trans
    exact sum_le_sum (fun D hD => AssignedAccounting.base_le_width D.avoided.isSome
      (by have hh := (hZ.1 D hD).2.2.1.2.1; dsimp [RadialShell.width] <;> linarith) (le_refl _))
  | cons F L ih =>
    obtain ⟨Z₁,hZ₁,hstep,hown₁⟩ := F.phase hX hq hconn hη (radius_nonneg L)
      hgeo.1 hE hready.2.1 hready.1 Z hZ hown
    have hc : credit+(AssignedAccounting.theta/2)*F.mass ≤
        ∑D ∈ Z₁, D.baseToken (initialRadius L) := by
      change credit ≤ ∑D ∈ Z, D.baseToken F.radius at hcredit
      linarith
    obtain ⟨Z₂,hZ₂,hc₂⟩ := ih hgeo.2 (E∪F.owners) (union_subset hE F.owners_nodes)
      hready.2.2 Z₁ hZ₁ hown₁ hc
    refine ⟨Z₂,hZ₂,?_⟩
    dsimp [mass]
    linarith

lemma insertable_bound {q : ℝ} (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hη : 3072/q ≤ η)
    (L : List (Family (H := H) (G := G) (X := X) (η := η)))
    (hgeo : Geometric L) (hready : Ready ∅ L) :
    (q/4096)*mass L ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  have hempty : LabeledArrangement H G X (q/4) ∅ := by constructor <;> simp
  obtain ⟨Z,hZ,hwidth⟩ := construct hX hq hconn hη L hgeo ∅ (empty_subset _) hready
    ∅ hempty (by simp) (credit := 0) (by simp)
  have he := labeled_energy H G X hX hZ
  have hh := mul_le_mul_of_nonneg_left hwidth (show 0 ≤ q/4 by positivity)
  dsimp [AssignedAccounting.theta] at hh
  nlinarith

end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ} {η : ℝ}

namespace AssignedFamily
variable (F : AssignedFamily H G X η)

lemma bad_witness {E : Finset (Finset (Fin n))} (i : Fin F.count) {u : Fin n}
    (hu : u ∈ F.badCenters E i) :
    ∃S ∈ E, ∃e ∈ G.cut univ S, ∃v : Fin n,
      (v = G.left e ∨ v = G.right e) ∧ normDistance (X v) (X u) < F.radius := by
  have hn : ¬((F.bag i).input (F.predecessors E i) u).Protected G X := by
    intro hh
    exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,hh⟩)
  simp only [Record.Protected,not_forall] at hn
  obtain ⟨S,hS,e,he,hn⟩ := hn
  have hSE : S ∈ E := (mem_filter.mp hS).1
  change ¬(F.radius ≤ normDistance (X (G.left e)) (X u) ∧
    F.radius ≤ normDistance (X (G.right e)) (X u)) at hn
  by_cases hl : normDistance (X (G.left e)) (X u) < F.radius
  · exact ⟨S,hSE,e,he,G.left e,Or.inl rfl,hl⟩
  · exact ⟨S,hSE,e,he,G.right e,Or.inr rfl,lt_of_not_ge (fun hr => hn ⟨le_of_not_gt hl,hr⟩)⟩

lemma badCount_le (hX : ∀v, isProfile (X v)) (E : Finset (Finset (Fin n))) :
    F.badCount E ≤ 2*boundaryCount G E := by
  let B := univ.sigma (F.badCenters E)
  let W := E.biUnion (fun S => (G.cut univ S).biUnion (fun e => {G.left e,G.right e}))
  have hBW : ∀p ∈ B, ∃v ∈ W, normDistance (X v) (X p.2) < F.radius := by
    intro p hp
    obtain ⟨S,hS,e,he,v,hv,hd⟩ := F.bad_witness p.1 (mem_sigma.mp hp).2
    refine ⟨v,mem_biUnion.mpr ⟨S,hS,mem_biUnion.mpr ⟨e,he,?_⟩⟩,hd⟩
    simp only [mem_insert,mem_singleton]
    exact hv
  choose f hfW hfd using hBW
  have hinj : ∀p hp q hq, f p hp = f q hq → p = q := by
    intro p hp r hr heq
    by_contra hh
    have hne : p.1 ≠ r.1 ∨ p.2 ≠ r.2 := by
      by_contra hn
      push Not at hn
      exact hh (Sigma.ext hn.1 (heq_of_eq hn.2))
    have hd := F.separated p.1 p.2 (mem_sdiff.mp (mem_sigma.mp hp).2).1
      r.1 r.2 (mem_sdiff.mp (mem_sigma.mp hr).2).1 hne
    have ha : X (f p hp) ∈ (RadialShell.ball p.2 F.radius).support X := by
      rw [RadialShell.support_ball]
      exact ⟨isProfile_inPolytope (hX _),hfd p hp⟩
    have hb : X (f p hp) ∈ (RadialShell.ball r.2 F.radius).support X := by
      rw [RadialShell.support_ball,heq]
      exact ⟨isProfile_inPolytope (hX _),hfd r hr⟩
    exact Set.disjoint_left.mp hd ha hb
  have hcard : B.card ≤ W.card := by
    apply Finset.card_le_card_of_injective (f := fun p : B => (⟨f p.val p.property,hfW p.val p.property⟩ : W))
    intro p r heq
    exact Subtype.ext (hinj p.val p.property r.val r.property (congrArg Subtype.val heq))
  have hW : W.card ≤ 2*boundaryCount G E := by
    calc
      W.card ≤ ∑S ∈ E, ((G.cut univ S).biUnion (fun e => {G.left e,G.right e})).card := card_biUnion_le
      _ ≤ ∑S ∈ E, ∑e ∈ G.cut univ S, ({G.left e,G.right e} : Finset (Fin n)).card :=
        sum_le_sum (fun S hS => card_biUnion_le)
      _ ≤ ∑S ∈ E, ∑_e ∈ G.cut univ S, 2 :=
        sum_le_sum (fun S hS => sum_le_sum (fun e he => card_le_two))
      _ = _ := by simp [boundaryCount,mul_sum,Nat.mul_comm]
  have heq : B.card = F.badCount E := by simp [B,badCount,Finset.card_sigma]
  rw [heq] at hcard
  exact hcard.trans hW

lemma prune (E : Finset (Finset (Fin n))) {η' : ℝ} (hη : 2*η' ≤ η) :
    ∃F' : AssignedFamily H G X η', F'.radius = F.radius ∧ F'.owners ⊆ F.owners ∧
      (∀E' ⊆ E, F'.ProtectedFrom E') ∧
      F.mass-2*(F.badCount E : ℝ)*F.radius ≤ F'.mass := by
  let J := univ.filter (fun i : Fin F.count => (F.bag i).centers.card ≤ 2*(F.goodCenters E i).card)
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have hnon : ∀i ∈ J, (F.goodCenters E i).Nonempty := by
    intro i hi
    apply card_pos.mp
    have hn := card_pos.mpr (F.bag i).nonempty
    have hc := (mem_filter.mp hi).2
    omega
  let a (i : J) : AssignedBag H G X F.radius η' := {
    owner := (F.bag i.val).owner
    owner_mem := (F.bag i.val).owner_mem
    nonroot := (F.bag i.val).nonroot
    centers := F.goodCenters E i.val
    nonempty := hnon i.val i.property
    radius_pos := F.positive
    disjoint := (F.bag i.val).disjoint.mono (filter_subset _ _)
    assignment := by
      have hc : ((F.bag i.val).centers.card : ℝ) ≤ 2*((F.goodCenters E i.val).card : ℝ) := by
        exact_mod_cast (mem_filter.mp i.property).2
      have hh := mul_le_mul_of_nonneg_right hη (Nat.cast_nonneg (parentBoundary H G (F.bag i.val).owner).card)
      have ha := (F.bag i.val).assignment
      nlinarith
    endpoint := fun u hu => (F.bag i.val).endpoint u (mem_filter.mp hu).1 }
  let F' : AssignedFamily H G X η' := {
    radius := F.radius
    positive := F.positive
    count := Fintype.card J
    bag := fun i => a (e i)
    owner_injective := by
      intro i j hij
      apply e.injective
      apply Subtype.ext
      exact F.owner_injective hij
    separated := by
      intro i u hu j v hv hne
      apply F.separated (e i).val u (mem_filter.mp hu).1 (e j).val v (mem_filter.mp hv).1
      rcases hne with hne | hne
      · left
        intro hh
        exact hne (e.injective (Subtype.ext hh))
      · exact Or.inr hne }
  have hsum : ∑i : Fin F'.count, ((F'.bag i).centers.card : ℝ) =
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    change (∑i : Fin (Fintype.card J), ((F.goodCenters E (e i).val).card : ℝ)) = _
    rw [e.sum_comp (fun i : J => ((F.goodCenters E i.val).card : ℝ))]
    exact Finset.sum_coe_sort J (fun i : Fin F.count => ((F.goodCenters E i).card : ℝ))
  have hgood : ∀i, ((F.bag i).centers.card : ℝ) ≤
      (if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0)+2*((F.badCenters E i).card : ℝ) := by
    intro i
    have hc : ((F.badCenters E i).card : ℝ)+((F.goodCenters E i).card : ℝ) =
        ((F.bag i).centers.card : ℝ) := by
      exact_mod_cast card_sdiff_add_card_eq_card (filter_subset (fun u =>
        ((F.bag i).input (F.predecessors E i) u).Protected G X) (F.bag i).centers)
    by_cases hi : i ∈ J
    · rw [ite_eq_left hi]
      nlinarith [show (0:ℝ) ≤ (F.badCenters E i).card from Nat.cast_nonneg _]
    · rw [ite_eq_right hi]
      have hh : 2*(F.goodCenters E i).card < (F.bag i).centers.card := by
        simpa only [J,mem_filter,mem_univ,true_and,not_le] using hi
      have hh' : 2*((F.goodCenters E i).card : ℝ) < ((F.bag i).centers.card : ℝ) := by exact_mod_cast hh
      linarith
  have hcount := Finset.sum_le_sum (s := univ) (fun i _ => hgood i)
  have hcounts : (∑i, ((F.bag i).centers.card : ℝ))-2*(F.badCount E : ℝ) ≤
      ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by
    rw [sum_add_distrib,←mul_sum] at hcount
    have heq : (∑i, if i ∈ J then ((F.goodCenters E i).card : ℝ) else 0) =
        ∑i ∈ J, ((F.goodCenters E i).card : ℝ) := by simp
    rw [heq] at hcount
    apply sub_le_iff_le_add.mpr
    simpa only [badCount,Nat.cast_sum] using hcount
  refine ⟨F',rfl,?_,?_,?_⟩
  · intro S hS
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hS
    exact F.owner_mem (e i).val
  · intro E' hE' i u hu S hS edge hedge
    have hp := (mem_filter.mp hu).2
    exact hp S (mem_filter.mpr ⟨hE' (mem_filter.mp hS).1,(mem_filter.mp hS).2⟩) edge hedge
  · dsimp [mass]
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_right hcounts F.positive.le]

end AssignedFamily
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open StrongThinTree.MultiGraph.Hierarchy (mem_domain mem_leaves)
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open StrongThinTree.Geometry (clamp)
variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Doubled Coord → ℝ}

namespace AssignedFamily
variable {q : ℝ} (F : AssignedFamily H G X (6144/q))

lemma boundary_mass {ρ : ℝ} (hq : 0 < q) (hR : F.BoundaryRatio ρ) :
    6144*ρ*(boundaryCount G F.owners : ℝ)*F.radius ≤ F.mass := by
  have he : (boundaryCount G F.owners : ℝ) =
      ∑i, ((G.cut univ (F.bag i).owner).card : ℝ) := by
    simp only [boundaryCount,owners,Nat.cast_sum]
    exact sum_image F.owner_injective.injOn
  have hi : ∀i, (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ) ≤ ((F.bag i).centers.card : ℝ) := by
    intro i
    have hh := mul_le_mul_of_nonneg_left (hR i) (show 0 ≤ (6144:ℝ)/q by positivity)
    have hx : (6144:ℝ)/q*((q*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)) =
        (6144*ρ)*((G.cut univ (F.bag i).owner).card : ℝ)  := by field_simp
    rw [hx] at hh
    exact hh.trans (F.bag i).assignment
  rw [he]
  dsimp [mass]
  apply mul_le_mul_of_nonneg_right _ F.positive.le
  rw [mul_sum]
  exact sum_le_sum (fun i _ => hi i)
end AssignedFamily

namespace AssignedSequence
open AssignedFamily
variable {q : ℝ}

lemma geometric_of {η ρ : ℝ} (hρ : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X η)) (hL : GeometricAt ρ L) : Geometric L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih hL.2⟩
    have hh := mul_le_mul_of_nonneg_right hρ F.positive.le
    linarith [hL.1]

lemma prune_sequence (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L)
    (E E' : Finset (Finset (Fin n))) (hE : E ⊆ H.nodes) (hE' : E' ⊆ E)
    (hfresh : Fresh E L) :
    ∃L' : List (AssignedFamily H G X (3072/q)), initialRadius L' = initialRadius L ∧
      GeometricAt ρ L' ∧ Ready E' L' ∧
      mass L/2-8*(initialRadius L)*(boundaryCount G E : ℝ) ≤ mass L' := by
  induction L generalizing E E' with
  | nil => exact ⟨[],rfl,True.intro,True.intro,by simp [mass,initialRadius]⟩
  | cons F L ih =>
    obtain ⟨F',hrad,howners,hprot,hgain⟩ := F.prune E (η' := 3072/q) (by field_simp; ring_nf; rfl)
    have hE₁ : E∪F.owners ⊆ H.nodes := union_subset hE F.owners_nodes
    obtain ⟨L',headEq,hgeo',hready',hgain'⟩ := ih hgeo.2 hR.2
      (E∪F.owners) (E'∪F'.owners) hE₁ (union_subset_union hE' howners) hfresh.2
    have hdis : Disjoint E' F'.owners := hfresh.1.mono hE' howners
    have hBC : (boundaryCount G (E∪F.owners) : ℝ) =
        (boundaryCount G E : ℝ)+(boundaryCount G F.owners : ℝ) := by
      simp only [boundaryCount,sum_union hfresh.1,Nat.cast_add]
    have hb := F.badCount_le hX E
    have hb' : (F.badCount E : ℝ) ≤ 2*(boundaryCount G E : ℝ) := by exact_mod_cast hb
    have hpf : F.mass-4*F.radius*(boundaryCount G E : ℝ) ≤ F'.mass := by
      have hh := mul_le_mul_of_nonneg_right hb' F.positive.le
      nlinarith
    have hr := F.boundary_mass hq hR.1
    have heps := radius_nonneg L
    have hsc := hgeo.1
    have hsmall := mul_le_mul_of_nonneg_right hρsmall F.positive.le
    have hcoal : 4*F.radius+8*initialRadius L ≤ 8*F.radius := by linarith
    have hB0 : (0:ℝ) ≤ boundaryCount G E := Nat.cast_nonneg _
    have hBF0 : (0:ℝ) ≤ boundaryCount G F.owners := Nat.cast_nonneg _
    have hc := mul_le_mul_of_nonneg_right hsc hBF0
    have hcost : 8*initialRadius L*(boundaryCount G F.owners : ℝ) ≤ F.mass/2 := by
      have hpos : 0 ≤ ρ*F.radius*(boundaryCount G F.owners : ℝ) :=
        mul_nonneg (mul_nonneg hρ.le F.positive.le) hBF0
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right hcoal hB0
    refine ⟨F'::L',hrad,⟨?_,hgeo'⟩,⟨hdis,hprot E' hE',hready'⟩,?_⟩
    · simpa only [headEq,hrad] using hsc
    · rw [hBC] at hgain'
      dsimp [mass,initialRadius]
      nlinarith

lemma assigned_bound (hX : ∀v, isProfile (X v)) {q : ℝ} (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q)
    {ρ : ℝ} (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (L : List (AssignedFamily H G X (6144/q)))
    (hgeo : GeometricAt ρ L) (hR : Ratios ρ L) (hfresh : Fresh ∅ L) :
    (q/8192)*mass L ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  obtain ⟨L',hrad,hgeo',hready',hmass⟩ := prune_sequence hX hq hρ hρsmall L hgeo hR ∅ ∅
    (empty_subset _) (Subset.refl _) hfresh
  have hcharge := insertable_bound hX hq hconn (le_refl (3072/q)) L' (geometric_of hρsmall L' hgeo') hready'
  have hmass' : mass L/2 ≤ mass L' := by simpa [boundaryCount] using hmass
  have hh := mul_le_mul_of_nonneg_left hmass' (show 0 ≤ q/4096 by positivity)
  nlinarith

end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ScaleCharging
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric scale charging. -/

section

namespace AlgorithmicThinTrees.MetricProfiles.AssignedGeometry
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry
open AlgorithmicThinTrees.MetricProfiles.CompactGeometry.RadialShell
open scoped Classical

variable {n m : ℕ} {Coord : Type*} [Fintype Coord] [PseudoMetricSpace Coord] {H : Hierarchy n} {G : MultiGraph n m} {X : Fin n → Doubled Coord → ℝ}

namespace AssignedSequence
variable {η q ρ : ℝ}

lemma mass_eq (L : List (AssignedFamily H G X η)) : mass L = (L.map AssignedFamily.mass).sum := by
  induction L with
  | nil => rfl
  | cons F L ih => simpa only [mass,List.map_cons,List.sum_cons] using congrArg (F.mass+·) ih

lemma geometric_of_pairwise (hρ : 0 ≤ ρ) (L : List (AssignedFamily H G X η))
    (hL : L.Pairwise (fun F F' => F'.radius ≤ ρ*F.radius)) : GeometricAt ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih =>
    refine ⟨?_,ih (List.pairwise_cons.mp hL).2⟩
    cases L with
    | nil => exact mul_nonneg hρ F.positive.le
    | cons F' L => exact (List.pairwise_cons.mp hL).1 F' (by simp)

lemma ratios_of_mem (L : List (AssignedFamily H G X (6144/q)))
    (hL : ∀F ∈ L, F.BoundaryRatio ρ) : Ratios ρ L := by
  induction L with
  | nil => trivial
  | cons F L ih => exact ⟨hL F (by simp),ih (fun F' hF' => hL F' (by simp [hF']))⟩

lemma fresh_of_pairwise (L : List (AssignedFamily H G X (6144/q)))
    (hL : L.Pairwise (fun F F' => Disjoint F.owners F'.owners))
    (E : Finset (Finset (Fin n))) (hE : ∀F ∈ L, Disjoint E F.owners) : Fresh E L := by
  induction L generalizing E with
  | nil => trivial
  | cons F L ih =>
    refine ⟨hE F (by simp),ih (List.pairwise_cons.mp hL).2 _ ?_⟩
    intro F' hF'
    exact disjoint_union_left.mpr ⟨hE F' (by simp [hF']), (List.pairwise_cons.mp hL).1 F' hF'⟩

lemma finite_bound (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    {r : ℕ} (F : Fin r → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j, i<j → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j, i<j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  have hh := assigned_bound hX hq hconn hρ hρsmall (List.ofFn F)
    (geometric_of_pairwise hρ.le _ (List.pairwise_ofFn.mpr hgeo))
    (ratios_of_mem _ (by
      intro A hA
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hA
      exact hR i))
    (fresh_of_pairwise _ (List.pairwise_ofFn.mpr hdis) ∅ (by simp))
  rw [mass_eq,List.map_ofFn,List.sum_ofFn] at hh
  exact hh

lemma ordered_bound_oai {J : Type*} [LinearOrder J] (hX : ∀v, isProfile (X v)) (hq : 0 < q)
    (hconn : LocallyConnectedReal H G q) (hρ : 0 < ρ) (hρsmall : ρ ≤ 1/1536)
    (S : Finset J) (F : S → AssignedFamily H G X (6144/q))
    (hgeo : ∀i j : S, j.val < i.val → (F j).radius ≤ ρ*(F i).radius)
    (hR : ∀i, (F i).BoundaryRatio ρ)
    (hdis : ∀i j : S, i≠j → Disjoint (F i).owners (F j).owners) :
    (q/8192)*(∑i, (F i).mass) ≤ ∑e : Fin m, normDistance (X (G.left e)) (X (G.right e)) := by
  let e := S.orderIsoOfFin rfl
  let f : Fin S.card ≃ S := Fin.revPerm.trans e.toEquiv
  have hh := finite_bound hX hq hconn hρ hρsmall (fun i => F (f i)) (by
    intro i j hij
    apply hgeo
    change (e j.rev).val < (e i.rev).val
    exact e.strictMono (Fin.rev_lt_rev.mpr hij))
    (fun i => hR (f i)) (fun i j hij => hdis _ _ (f.injective.ne hij.ne))
  rw [f.sum_comp (fun i => (F i).mass)] at hh
  exact hh
end AssignedSequence
end
end AlgorithmicThinTrees.MetricProfiles.AssignedGeometry

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound_oai.{u_1, u_2} := @OAI.AlgorithmicThinTrees.MetricProfiles.AssignedGeometry.AssignedSequence.ordered_bound_oai.{u_1, u_2}
