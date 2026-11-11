-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:59:14.587766+00:00
-- url     : https://prove2.me/submissions/e45bf3bf-ea55-4416-900c-93ce219b9344

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009

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

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset StrongThinTree.Geometry
variable {n m : ℕ} (G : MultiGraph n m)

lemma clamped_variation_lower {k : ℕ} (hk : G.EdgeConnected k)
    (f : Fin n → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hu : ∃u, f u ≤ a) (hv : ∃v, b ≤ f v) :
    (k : ℝ)*(b-a) ≤ ∑e : Fin m,
      |clamp a b (f (G.left e))-clamp a b (f (G.right e))| := by
  classical
  apply cut_range_bound G.left G.right (fun v => clamp a b (f v)) hab
  intro t ht
  let S := univ.filter (fun v => f v < t)
  have hne : S.Nonempty := by
    obtain ⟨u, hu⟩ := hu
    exact ⟨u, mem_filter.mpr ⟨mem_univ _, lt_of_le_of_lt hu ht.1⟩⟩
  have hproper : S ≠ univ := by
    obtain ⟨v, hv⟩ := hv
    intro heq
    have hh : v ∈ S := heq.symm ▸ mem_univ v
    have := (mem_filter.mp hh).2
    linarith [ht.2]
  have hc := hk S hne hproper
  have hset : (univ.filter (fun e =>
      (clamp a b (f (G.left e))<t ∧ ¬clamp a b (f (G.right e))<t) ∨
      (clamp a b (f (G.right e))<t ∧ ¬clamp a b (f (G.left e))<t))) = G.cut univ S := by
    ext e
    simp only [S, cut, mem_filter, mem_univ, true_and, clamp_lt_iff ht]
  rw [hset]
  exact_mod_cast hc

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Duality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uJ uV uI2 uI3 uV2 uW uJ2 uV3 uE2 uT uJ3 uH uI4

section

namespace StrongThinTree.ShortcutDual
noncomputable section
open Matrix Finset Filter Topology
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {V : Type uV3} {E : Type uE2} {T : Type uT} {J : Type uJ3} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] [Fintype T] [Fintype J]

omit [DecidableEq V] in
lemma trace_outer_mul (v : V → ℝ) (D : Matrix V V ℝ) :
    (vecMulVec v v * D).trace = v ⬝ᵥ (D *ᵥ v) := by
  rw [vecMulVec_mul,trace_vecMulVec,dotProduct_comm,dotProduct_mulVec]

end
end StrongThinTree.ShortcutDual

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ShortcutDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset StrongThinTree.Geometry
open scoped Classical MatrixOrder Matrix.Norms.L2Operator
variable {n m h : ℕ} (G : MultiGraph n m)

lemma eval_incidence (x : Fin n → ℝ) (e : Fin m) :
    (∑v, x v*G.incidence e v)=x (G.left e)-x (G.right e) := by
  simp [incidence,point,Pi.sub_apply,mul_sub,sum_sub_distrib,Pi.single_apply,mul_ite]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Matrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι

section
open Matrix
namespace StrongThinTree
section Resistance
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma rankOne_quadratic (b x : ι → ℝ) :
    x ⬝ᵥ (vecMulVec b b *ᵥ x) = (b ⬝ᵥ x) ^ 2 := by
  rw [vecMulVec_mulVec]
  simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

end Resistance
end StrongThinTree

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_GraphMatrix
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
lemma qform_add (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X+Y) v=qform X v+qform Y v := by
  simp [qform,add_mulVec,dotProduct_add]
omit [DecidableEq V] in
lemma qform_sub (X Y : Matrix V V ℝ) (v : V → ℝ) : qform (X-Y) v=qform X v-qform Y v := by
  simp [qform,sub_mulVec,dotProduct_sub]
omit [DecidableEq V] in
lemma qform_smul (a : ℝ) (X : Matrix V V ℝ) (v : V → ℝ) : qform (a • X) v=a*qform X v := by
  simp [qform,smul_mulVec,dotProduct_smul]
omit [DecidableEq V] in
lemma qform_mono {X Y : Matrix V V ℝ} (h : X ≤ Y) (v : V → ℝ) : qform X v ≤ qform Y v := by
  have hh := qform_nonneg (Matrix.le_iff.mp h) v
  rw [qform_sub] at hh
  linarith

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_BasePacking
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype _root_.OAI.CurrentKS.Hermitian.instFiniteDimensionalRealSubtypeMatMemSubmoduleH
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uI2

section

noncomputable section
open Finset Submodule
namespace StrongThinTree.Packing

variable {E : Type uE} {I : Type uI} {V : Type uV} [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_mono (v : E → V) {s t : Finset E} (h : s ⊆ t) : span v s ≤ span v t :=
  Submodule.span_mono (Set.image_mono h)

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma span_insert (v : E → V) (s : Finset E) (e : E) :
    span v (insert e s) = Submodule.span ℝ (insert (v e) (v '' (s : Set E))) := by
  simp only [span, coe_insert, Set.image_insert_eq]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma indep_rank (v : E → V) {s : Finset E} (hs : LinearIndepOn ℝ v s) :
    Module.finrank ℝ (span v s) = s.card := by
  have heq : Set.range (fun e : (s : Set E) => v e) = v '' (s : Set E) := by
    ext x; simp
  have h := finrank_span_eq_card hs.linearIndependent
  change Module.finrank ℝ (Submodule.span ℝ (Set.range (fun e : (s : Set E) => v e))) = _ at h
  rw [heq] at h
  simpa using h

omit [Fintype E] [FiniteDimensional ℝ V] in

lemma support_exchange (v : E → V) {s : Finset E}
    (hs : LinearIndepOn ℝ v s) {x : V} {l : E →₀ ℝ}
    (hl : l ∈ Finsupp.supported ℝ ℝ (s : Set E))
    (hx : Finsupp.linearCombination ℝ v l = x) {f : E} (hf : f ∈ l.support) :
    x ∉ span v (s.erase f) := by
  intro h
  obtain ⟨l', hl', hx'⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp h
  have hl's : l' ∈ Finsupp.supported ℝ ℝ (s : Set E) := by
    rw [Finsupp.mem_supported] at hl' ⊢
    exact hl'.trans (Finset.erase_subset _ _)
  have heq : l = l' := (linearIndepOn_iffₛ.mp hs) l hl l' hl's (hx.trans hx'.symm)
  have hz : l' f = 0 := by
    apply Finsupp.notMem_support_iff.mp
    intro hmem
    have := ((Finsupp.mem_supported ℝ l').mp hl') hmem
    simp at this
  exact (Finsupp.mem_support_iff.mp hf) (heq ▸ hz)

omit [Fintype E] [DecidableEq E] [Fintype I] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma valid_empty (v : E → V) : Valid v (fun _ : I => ∅) := by
  constructor
  · intro i; simp
  · intro i j h; simp

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma valid_update {v : E → V} (F : State v I) (i : I) (s : Finset E)
    (hs : LinearIndepOn ℝ v (s : Set E))
    (hd : ∀ j, j ≠ i → Disjoint s (F.1 j)) : Valid v (Function.update F.1 i s) := by
  constructor
  · intro j
    by_cases h : j = i
    · subst j; simpa using hs
    · simpa [Function.update_of_ne h] using F.2.1 j
  · intro j k hjk
    by_cases hj : j = i
    · subst j
      simpa [Function.update_of_ne (Ne.symm hjk)] using hd k (Ne.symm hjk)
    · by_cases hk : k = i
      · subst k
        simpa [Function.update_of_ne hj] using (hd j hj).symm
      · simpa [Function.update_of_ne hj, Function.update_of_ne hk] using F.2.2 hjk

omit [Fintype E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma disjoint_insert_unused {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (hs : s ⊆ F.1 i) {e : E} (he : unused F e) :
    ∀ j, j ≠ i → Disjoint (insert e s) (F.1 j) := by
  intro j hj
  rw [Finset.disjoint_insert_left]
  exact ⟨he j, (F.2.2 (Ne.symm hj)).mono_left hs⟩

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma cost_update {v : E → V} (F : State v I) {i : I} {s : Finset E}
    (h : Valid v (Function.update F.1 i s)) :
    cost (⟨Function.update F.1 i s, h⟩ : State v I) + (F.1 i).card = cost F + s.card := by
  unfold cost
  have hsum := Finset.sum_update_of_mem (Finset.mem_univ i) (fun j => (F.1 j).card) s.card
  have heq : (fun j => ((Function.update F.1 i s) j).card) =
      Function.update (fun j => (F.1 j).card) i s.card := by
    ext j; by_cases hj : j = i <;> simp [hj, Function.update_of_ne]
  rw [heq]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [← Finset.sum_erase_add (Finset.univ : Finset I) _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  have he : ∑ j ∈ Finset.univ.erase i,
      Function.update (fun j => (F.1 j).card) i s.card j =
      ∑ j ∈ Finset.univ.erase i, (F.1 j).card := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Function.update_of_ne (Finset.mem_erase.mp hj).1 _ _
  rw [he]
  omega

omit [DecidableEq E] [DecidableEq I] [FiniteDimensional ℝ V] in
lemma exists_maximal_state (v : E → V) :
    ∃ F : State v I, ∀ F' : State v I, cost F' ≤ cost F := by
  classical
  let : Fintype (State v I) := Fintype.ofFinite _
  have hne : (Finset.univ : Finset (State v I)).Nonempty :=
    ⟨⟨fun _ => ∅, valid_empty v⟩, Finset.mem_univ _⟩
  obtain ⟨F, _, hF⟩ := Finset.exists_max_image (Finset.univ : Finset (State v I)) cost hne
  exact ⟨F, fun F' => hF F' (Finset.mem_univ _)⟩

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma maximal_unused_mem_span {v : E → V} {F : State v I}
    (hF : ∀ F' : State v I, cost F' ≤ cost F) {e : E} (he : unused F e) (i : I) :
    v e ∈ span v (F.1 i) := by
  by_contra h
  have hs : LinearIndepOn ℝ v (insert e (F.1 i) : Finset E) := by
    simpa only [Finset.coe_insert] using (F.2.1 i).insert h
  have hv := valid_update F i _ hs (disjoint_insert_unused F (Subset.refl _) he)
  have hc := cost_update F hv
  have hu := hF ⟨_, hv⟩
  rw [Finset.card_insert_of_notMem (he i)] at hc
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma unused_after_exchange {v : E → V} {F F' : State v I} {i : I} {e f : E}
    (he : unused F e) (hf : f ∈ F.1 i)
    (h : F'.1 = Function.update F.1 i (insert e ((F.1 i).erase f))) : unused F' f := by
  intro j
  rw [h]
  by_cases hj : j = i
  · subst j
    have hfe : f ≠ e := by rintro rfl; exact he i hf
    simp [hfe]
  · rw [Function.update_of_ne hj]
    exact fun hfj => Finset.disjoint_left.mp (F.2.2 (Ne.symm hj)) hf hfj

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma Move.cost_eq {v : E → V} {F F' : State v I} (h : Move F F') : cost F' = cost F := by
  obtain ⟨i, e, f, he, hf, heq⟩ := h
  have hv : Valid v (Function.update F.1 i (insert e ((F.1 i).erase f))) := heq ▸ F'.2
  have hc := cost_update F hv
  have hsame : (⟨_, hv⟩ : State v I) = F' := Subtype.ext heq.symm
  rw [hsame, Finset.card_insert_of_notMem (fun hh => he i (Finset.mem_erase.mp hh).2),
    Finset.card_erase_of_mem hf] at hc
  have hfpos := Finset.card_pos.mpr ⟨f, hf⟩
  omega

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_cost_eq {v : E → V} {F F' : State v I}
    (h : Relation.ReflTransGen Move F F') : cost F' = cost F := by
  induction h with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact hm.cost_eq.trans ih

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma reachable_maximal {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (h : Relation.ReflTransGen Move F F') : ∀ G : State v I, cost G ≤ cost F' := by
  intro G
  rw [reachable_cost_eq h]
  exact hF G

omit [FiniteDimensional ℝ V] in
lemma mem_recycled {v : E → V} {F : State v I} {e : E} :
    e ∈ recycled F ↔ ∃ F', Relation.ReflTransGen Move F F' ∧ unused F' e := by
  classical
  simp [recycled]

omit [FiniteDimensional ℝ V] in
lemma unused_span_recycled {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') {e : E} (he : unused F' e) (i : I) :
    v e ∈ span v (F'.1 i ∩ recycled F) := by
  have hsp := maximal_unused_mem_span (reachable_maximal hF hr) he i
  obtain ⟨l, hl, hle⟩ := (Finsupp.mem_span_image_iff_linearCombination ℝ).mp hsp
  apply (Finsupp.mem_span_image_iff_linearCombination ℝ).mpr
  refine ⟨l, ?_, hle⟩
  rw [Finsupp.mem_supported]
  intro f hf
  have hfi : f ∈ F'.1 i := (Finsupp.mem_supported ℝ l).mp hl hf
  refine Finset.mem_inter.mpr ⟨hfi, mem_recycled.mpr ?_⟩
  have hex := support_exchange v (F'.2.1 i) hl hle hf
  have hs : LinearIndepOn ℝ v (insert e ((F'.1 i).erase f) : Finset E) := by
    simpa only [Finset.coe_insert] using
      ((F'.2.1 i).mono (Finset.erase_subset _ _)).insert hex
  have hv := valid_update F' i _ hs
    (disjoint_insert_unused F' (Finset.erase_subset _ _) he)
  let F'' : State v I := ⟨_, hv⟩
  have hm : Move F' F'' := ⟨i, e, f, he, hfi, rfl⟩
  exact ⟨F'', hr.tail hm, unused_after_exchange he hfi rfl⟩

omit [FiniteDimensional ℝ V] in
lemma move_span_recycled_eq {v : E → V} {F F' F'' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (hm : Move F' F'') (j : I) :
    span v (F''.1 j ∩ recycled F) = span v (F'.1 j ∩ recycled F) := by
  obtain ⟨i, e, f, he, hf, hup⟩ := hm
  by_cases hji : j = i
  · subst j
    have heU : v e ∈ span v (F'.1 i ∩ recycled F) := unused_span_recycled hF hr he i
    have hfU : v f ∈ span v (F''.1 i ∩ recycled F) :=
      unused_span_recycled hF (hr.tail ⟨i, e, f, he, hf, hup⟩)
        (unused_after_exchange he hf hup) i
    apply le_antisymm
    · apply (span_le_iff v).mpr
      intro g hg
      have hgU := (Finset.mem_inter.mp hg).2
      have hg' := (Finset.mem_inter.mp hg).1
      rw [hup, Function.update_self] at hg'
      rcases Finset.mem_insert.mp hg' with rfl | hg'
      · exact heU
      · exact mem_span_self v (Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hg').2, hgU⟩)
    · apply (span_le_iff v).mpr
      intro g hg
      by_cases hgf : g = f
      · subst g; exact hfU
      · apply mem_span_self v
        apply Finset.mem_inter.mpr
        refine ⟨?_, (Finset.mem_inter.mp hg).2⟩
        rw [hup, Function.update_self]
        exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hgf, (Finset.mem_inter.mp hg).1⟩)
  · rw [hup, Function.update_of_ne hji]

omit [FiniteDimensional ℝ V] in
lemma reachable_span_recycled_eq {v : E → V} {F F' : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F)
    (hr : Relation.ReflTransGen Move F F') (i : I) :
    span v (F'.1 i ∩ recycled F) = span v (F.1 i ∩ recycled F) := by
  induction hr with
  | refl => rfl
  | @tail F' F'' hr hm ih => exact (move_span_recycled_eq hF hr hm i).trans ih

omit [FiniteDimensional ℝ V] in

lemma span_recycled_eq {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) (i : I) :
    span v (recycled F) = span v (F.1 i ∩ recycled F) := by
  apply le_antisymm
  · apply (span_le_iff v).mpr
    intro e he
    obtain ⟨F', hr, he'⟩ := mem_recycled.mp he
    rw [← reachable_span_recycled_eq hF hr i]
    exact unused_span_recycled hF hr he' i
  · exact span_mono v Finset.inter_subset_right

omit [FiniteDimensional ℝ V] in
lemma cost_decomposition {v : E → V} {F : State v I}
    (hF : ∀ G : State v I, cost G ≤ cost F) :
    cost F = (Finset.univ \ recycled F).card +
      Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
  classical
  have hcover : Finset.univ \ recycled F =
      Finset.univ.biUnion (fun i => F.1 i \ recycled F) := by
    ext e
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_biUnion]
    constructor
    · intro he
      have hused : ∃ i, e ∈ F.1 i := by
        by_contra h
        have hu : unused F e := by simpa only [unused, not_exists] using h
        exact he (mem_recycled.mpr ⟨F, Relation.ReflTransGen.refl, hu⟩)
      obtain ⟨i, hi⟩ := hused
      exact ⟨i, hi, he⟩
    · rintro ⟨i, hi, he⟩; exact he
  have hdisj : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => F.1 i \ recycled F) := by
    intro i _ j _ hij
    exact (F.2.2 hij).mono Finset.sdiff_subset Finset.sdiff_subset
  have hrank (i : I) : (F.1 i ∩ recycled F).card =
      Module.finrank ℝ (span v (recycled F)) := by
    rw [span_recycled_eq hF i]
    exact (indep_rank v ((F.2.1 i).mono Finset.inter_subset_left)).symm
  rw [hcover, Finset.card_biUnion hdisj]
  calc
    cost F = ∑ i, ((F.1 i \ recycled F).card + (F.1 i ∩ recycled F).card) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (Finset.card_sdiff_add_card_inter _ _).symm
    _ = (∑ i, (F.1 i \ recycled F).card) +
        Fintype.card I * Module.finrank ℝ (span v (recycled F)) := by
      simp_rw [hrank, Finset.sum_add_distrib]
      simp

theorem vector_base_packing (v : E → V)
    (hcut : ∀ U : Finset E,
      Fintype.card I * Module.finrank ℝ (span v Finset.univ) ≤
        (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : State v I, ∀ i, span v (F.1 i) = span v Finset.univ := by
  obtain ⟨F, hF⟩ := exists_maximal_state (I := I) v
  have hle (i : I) : (F.1 i).card ≤ Module.finrank ℝ (span v Finset.univ) := by
    rw [← indep_rank v (F.2.1 i)]
    exact Submodule.finrank_mono (span_mono v (Finset.subset_univ _))
  have htotal : cost F = Fintype.card I * Module.finrank ℝ (span v Finset.univ) := by
    apply le_antisymm
    · calc
        cost F ≤ ∑ _i : I, Module.finrank ℝ (span v Finset.univ) :=
          Finset.sum_le_sum fun i _ => hle i
        _ = _ := by simp
    · rw [cost_decomposition hF]
      exact hcut (recycled F)
  have hcards (i : I) : (F.1 i).card = Module.finrank ℝ (span v Finset.univ) := by
    apply (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ (Finset.univ : Finset I)) => hle i)).mp ?_ i
      (Finset.mem_univ i)
    simpa [cost] using htotal
  refine ⟨F, fun i => ?_⟩
  apply Submodule.eq_of_le_of_finrank_eq (span_mono v (Finset.subset_univ _))
  rw [indep_rank v (F.2.1 i), hcards]

omit [Fintype E] [FiniteDimensional ℝ V] in
lemma masked_span (v : E → V) (T U : Finset E) :
    span (fun e => if e ∈ T then v e else 0) U = span v (U ∩ T) := by
  classical
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    by_cases heT : e ∈ T
    · simp only [ite_eq_left heT]
      exact mem_span_self v (Finset.mem_inter.mpr ⟨he, heT⟩)
    · simp [heT]
  · apply (span_le_iff _).mpr
    intro e he
    have hm := mem_span_self (fun e => if e ∈ T then v e else 0) (Finset.mem_inter.mp he).1
    simpa only [ite_eq_left (Finset.mem_inter.mp he).2] using hm

theorem vector_base_packing_on (v : E → V) (T : Finset E)
    (hcut : ∀ U : Finset E, U ⊆ T →
      Fintype.card I * Module.finrank ℝ (span v T) ≤
        (T \ U).card + Fintype.card I * Module.finrank ℝ (span v U)) :
    ∃ F : I → Finset E, Valid v F ∧ ∀ i, F i ⊆ T ∧ span v (F i) = span v T := by
  classical
  let w : E → V := fun e => if e ∈ T then v e else 0
  have hcrit : ∀ U : Finset E, Fintype.card I * Module.finrank ℝ (span w Finset.univ) ≤
      (Finset.univ \ U).card + Fintype.card I * Module.finrank ℝ (span w U) := by
    intro U
    have hw (A : Finset E) : span w A = span v (A ∩ T) := masked_span v T A
    rw [hw, hw, Finset.univ_inter]
    have h := hcut (U ∩ T) Finset.inter_subset_right
    apply h.trans
    apply Nat.add_le_add_right
    apply Finset.card_le_card
    intro e he
    simp only [Finset.mem_sdiff, Finset.mem_inter, Finset.mem_univ, true_and] at he ⊢
    tauto
  obtain ⟨F, hF⟩ := vector_base_packing (I := I) w hcrit
  have hsub (i : I) : F.1 i ⊆ T := by
    intro e he
    have hz := (F.2.1 i).ne_zero he
    by_contra h
    exact hz (by simp [w, h])
  refine ⟨F.1, ⟨?_, F.2.2⟩, fun i => ⟨hsub i, ?_⟩⟩
  · intro i
    apply (F.2.1 i).congr
    intro e he
    simp [w, hsub i he]
  · have heq := hF i
    simpa only [w, masked_span, Finset.inter_eq_left.mpr (hsub i), Finset.univ_inter] using heq

end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma rep_same (T : Finset (Fin m)) (u : Fin n) : G.Same T (G.rep T u) u :=
  Quotient.mk_out (s := G.components T) u

lemma rep_eq_iff (T : Finset (Fin m)) (u v : Fin n) : G.rep T u = G.rep T v ↔ G.Same T u v := by
  constructor
  · intro h
    exact G.same_trans (G.same_symm (G.rep_same T u)) (h ▸ G.rep_same T v)
  · intro h
    exact congrArg Quotient.out (Quotient.sound h)

lemma rep_idempotent (T : Finset (Fin m)) (u : Fin n) : G.rep T (G.rep T u) = G.rep T u :=
  (G.rep_eq_iff T _ _).mpr (G.rep_same T u)

lemma rep_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.rep T (G.left e) = G.rep T (G.right e) :=
  (G.rep_eq_iff T _ _).mpr (G.same_endpoints he)

lemma repDifference_mem (T : Finset (Fin m)) (u : Fin n) : G.repDifference T u ∈ G.edgeSpan T :=
  G.same_symm (G.rep_same T u)

lemma repDifference_independent (T : Finset (Fin m)) :
    LinearIndependent ℝ (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u) := by
  apply LinearIndependent.of_pairwise_dual_eq_zero_one _ (fun u => LinearMap.proj u.1)
  · intro u v huv
    have huv' : u.1 ≠ v.1 := fun h => huv (Subtype.ext h)
    have hru : u.1 ≠ G.rep T v.1 := by
      intro h
      have := G.rep_idempotent T v.1
      rw [← h] at this
      exact u.2 this
    simp [repDifference, point, huv', hru]
  · intro u
    simp [repDifference, point, (Ne.symm u.2)]

lemma edgeSpan_eq_repSpan (T : Finset (Fin m)) :
    G.edgeSpan T = Submodule.span ℝ
      (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
  classical
  apply le_antisymm
  · apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hdiff (u : Fin n) : G.repDifference T u ∈ Submodule.span ℝ
        (Set.range (fun u : {u : Fin n // G.rep T u ≠ u} => G.repDifference T u)) := by
      by_cases hu : G.rep T u = u
      · simp [repDifference, hu]
      · exact Submodule.subset_span ⟨⟨u, hu⟩, rfl⟩
    have h := (Submodule.span ℝ _).sub_mem (hdiff (G.left e)) (hdiff (G.right e))
    have heq : G.repDifference T (G.left e) - G.repDifference T (G.right e) = G.incidence e := by
      dsimp [repDifference, incidence]
      rw [G.rep_endpoints he]
      abel
    rwa [heq] at h
  · apply Submodule.span_le.mpr
    rintro x ⟨u, rfl⟩
    exact G.repDifference_mem T u

theorem incidence_rank (T : Finset (Fin m)) :
    Module.finrank ℝ (G.edgeSpan T) = n - G.componentCount T := by
  classical
  rw [G.edgeSpan_eq_repSpan, finrank_span_eq_card (G.repDifference_independent T),
    Fintype.card_subtype_compl]
  have heq : Finset.univ.image (G.rep T) = Finset.univ.filter (fun u => G.rep T u = u) := by
    ext u
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    constructor
    · rintro ⟨v, rfl⟩
      exact G.rep_idempotent T v
    · intro hu
      exact ⟨u, hu⟩
  simp only [componentCount, heq, Fintype.card_fin, Fintype.card_subtype]

lemma connected_of_span_eq {T U : Finset (Fin m)}
    (h : G.edgeSpan T = G.edgeSpan U) (hT : G.Connected T) : G.Connected U := by
  rw [G.connected_iff_same] at hT ⊢
  intro u v
  change point u - point v ∈ G.edgeSpan U
  rw [← h]
  exact hT u v

theorem spanningTree_iff_independent (T : Finset (Fin m)) :
    G.SpanningTree T ↔ G.Connected T ∧ LinearIndepOn ℝ G.incidence (T : Set (Fin m)) := by
  constructor
  · rintro ⟨hconn, hmin⟩
    refine ⟨hconn, linearIndepOn_iff_notMem_span.mpr ?_⟩
    intro e he hdep
    have hd : G.incidence e ∈ G.edgeSpan (T.erase e) := by
      simpa only [edgeSpan, Packing.span, Finset.coe_erase] using hdep
    have heq : G.edgeSpan T = G.edgeSpan (T.erase e) := by
      calc
        G.edgeSpan T = G.edgeSpan (insert e (T.erase e)) := by rw [Finset.insert_erase he]
        _ = G.edgeSpan (T.erase e) := by
          change Packing.span G.incidence (insert e (T.erase e)) = _
          rw [Packing.span_insert, Submodule.span_insert_eq_span hd]
    exact hmin e he (G.connected_of_span_eq heq hconn)
  · rintro ⟨hconn, hind⟩
    refine ⟨hconn, fun e he hdel => ?_⟩
    have hnot := linearIndepOn_iff_notMem_span.mp hind e he
    apply hnot
    have hsame := (G.connected_iff_same (T.erase e)).mp hdel (G.left e) (G.right e)
    simpa only [Same, incidence, edgeSpan, Packing.span, Finset.coe_erase] using hsame

lemma componentCount_pos (hn : 0 < n) (T : Finset (Fin m)) : 0 < G.componentCount T := by
  apply Finset.card_pos.mpr
  exact ⟨G.rep T ⟨0, hn⟩, Finset.mem_image.mpr ⟨⟨0, hn⟩, Finset.mem_univ _, rfl⟩⟩

lemma componentCount_le (T : Finset (Fin m)) : G.componentCount T ≤ n := by
  exact (Finset.card_image_le).trans_eq (Finset.card_univ.trans (Fintype.card_fin n))

lemma connected_componentCount {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    G.componentCount T = 1 := by
  apply Finset.card_eq_one.mpr
  let u : Fin n := ⟨0, hn⟩
  refine ⟨G.rep T u, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_singleton.mpr ((G.rep_eq_iff T w u).mpr ((G.connected_iff_same T).mp hc w u))
  · intro hv
    have hv' := Finset.mem_singleton.mp hv
    subst v
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩

lemma connected_rank {T : Finset (Fin m)} (hn : 0 < n) (hc : G.Connected T) :
    Module.finrank ℝ (G.edgeSpan T) = n - 1 := by
  rw [G.incidence_rank, G.connected_componentCount hn hc]

lemma spanningTree_card {T : Finset (Fin m)} (hn : 0 < n) (hT : G.SpanningTree T) : T.card = n - 1 := by
  rw [← Packing.indep_rank G.incidence ((G.spanningTree_iff_independent T).mp hT).2]
  exact G.connected_rank hn hT.1

lemma connected_of_componentCount_eq_one {T : Finset (Fin m)}
    (hc : G.componentCount T = 1) : G.Connected T := by
  rw [G.connected_iff_same]
  have ⟨v, hv⟩ := Finset.card_eq_one.mp hc
  intro a b
  have ha : G.rep T a ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
  have hb : G.rep T b ∈ Finset.univ.image (G.rep T) :=
    Finset.mem_image.mpr ⟨b, Finset.mem_univ _, rfl⟩
  rw [hv, Finset.mem_singleton] at ha hb
  exact (G.rep_eq_iff T a b).mp (ha.trans hb.symm)

lemma crossing_components_subset (T U : Finset (Fin m)) :
    G.crossing T (G.rep U) ⊆ T \ U := by
  intro e he
  obtain ⟨heT, hec⟩ := Finset.mem_filter.mp he
  exact Finset.mem_sdiff.mpr ⟨heT, fun heU => hec (G.rep_endpoints heU)⟩

lemma crossing_components_self (T : Finset (Fin m)) : G.crossing T (G.rep T) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro e he
  have := G.crossing_components_subset T T he
  simp at this

theorem partition_criterion_sufficient (T : Finset (Fin m)) {r : ℕ} (hr : 0 < r) (hn : 0 < n)
    (hp : ∀ p : Fin n → Fin n, r * (partitionSize p - 1) ≤ (G.crossing T p).card) :
    G.TreePackable T r := by
  have hc : G.Connected T := by
    have h := hp (G.rep T)
    rw [G.crossing_components_self, Finset.card_empty] at h
    change r * (G.componentCount T - 1) ≤ 0 at h
    have hpos := G.componentCount_pos hn T
    have hz : G.componentCount T - 1 = 0 := by nlinarith
    exact G.connected_of_componentCount_eq_one (by omega)
  have hcrit : ∀ U : Finset (Fin m), U ⊆ T →
      Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence T) ≤
        (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (Packing.span G.incidence U) := by
    intro U hUT
    change Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan T) ≤
      (T \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (G.edgeSpan U)
    rw [Fintype.card_fin, G.connected_rank hn hc, G.incidence_rank]
    have hpart := hp (G.rep U)
    have hcross := Finset.card_le_card (G.crossing_components_subset T U)
    have hcp := G.componentCount_pos hn U
    have hcle := G.componentCount_le U
    change r * (G.componentCount U - 1) ≤ (G.crossing T (G.rep U)).card at hpart
    have hnid : n - 1 = (G.componentCount U - 1) + (n - G.componentCount U) := by omega
    rw [hnid, Nat.mul_add]
    exact Nat.add_le_add_right (hpart.trans hcross) _
  obtain ⟨F, hv, hF⟩ := Packing.vector_base_packing_on G.incidence T hcrit
  refine ⟨F, fun i => ?_, hv.2⟩
  refine ⟨(hF i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, hv.1 i⟩⟩
  exact G.connected_of_span_eq (hF i).2.symm hc

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_MatrixBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric matrix bound. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m d : ℕ}

lemma sqrt_gram {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Z.PosSemidef) :
    (CFC.sqrt Z)ᵀ*CFC.sqrt Z=Z := by
  rw [isHermitian_iff_isSymm.mp (CFC.sqrt_nonneg Z).posSemidef.isHermitian]
  exact CFC.sqrt_mul_sqrt_self Z hZ.nonneg

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_CenteredMatrices
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered matrices. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma ones_dot (x : Fin n → ℝ) : ones n ⬝ᵥ x=∑i, x i := by
  simp [ones,dotProduct]

lemma constantProjection_mulVec (x : Fin n → ℝ) :
    constantProjection n *ᵥ x=((∑i, x i)/(n:ℝ)) • ones n := by
  ext j
  simp [constantProjection,mulVec,dotProduct,Matrix.smul_apply,vecMulVec,ones,div_eq_mul_inv,Finset.sum_mul,mul_comm]

lemma centering_mulVec (x : Fin n → ℝ) :
    centering n *ᵥ x=x-((∑i, x i)/(n:ℝ)) • ones n := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_mulVec]

lemma centering_mulVec_of_sum_zero {x : Fin n → ℝ} (hx : ∑i, x i=0) :
    centering n *ᵥ x=x := by
  simp only [centering_mulVec,hx,zero_div,zero_smul,sub_zero]

lemma centering_mulVec_sum (hn : 0 < n) (x : Fin n → ℝ) :
    ∑i, (centering n *ᵥ x) i=0 := by
  rw [centering_mulVec]
  simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,ones,sum_sub_distrib,mul_one,
    sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  field_simp
  ring

lemma constantProjection_ones (hn : 0 < n) : constantProjection n *ᵥ ones n=ones n := by
  rw [constantProjection_mulVec]
  simp only [ones,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
  rw [div_self (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)),one_smul]

lemma centering_ones (hn : 0 < n) : centering n *ᵥ ones n=0 := by
  rw [centering,sub_mulVec,one_mulVec,constantProjection_ones hn,sub_self]

lemma centered_dot (b y : Fin n → ℝ) (hb : ∑i, b i=0) :
    b ⬝ᵥ (centering n *ᵥ y)=b ⬝ᵥ y := by
  rw [dotProduct_mulVec,←mulVec_transpose,centering_symmetric,centering_mulVec_of_sum_zero hb]

lemma centered_psd {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) : (centered D).PosSemidef := by
  have hh := hD.mul_mul_conjTranspose_same (centering n)
  simpa only [centered,conjTranspose_eq_transpose_of_trivial,centering_symmetric] using hh

lemma centered_ones (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ) : centered D *ᵥ ones n=0 := by
  simp only [centered,←mulVec_mulVec,centering_ones hn,mulVec_zero]

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

lemma laplacian_ones (G : MultiGraph n m) : G.laplacian univ *ᵥ ones n=0 := by
  simp only [laplacian,sum_mulVec,vecMulVec_mulVec]
  apply Finset.sum_eq_zero
  intro e _
  rw [dotProduct_comm]
  change MulOpposite.op (∑v, ones n v*G.incidence e v) • G.incidence e=0
  rw [G.eval_incidence]
  simp [ones]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConicDuality
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric conic duality. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree
open scoped Classical MatrixOrder Topology
open Filter

section Pairing
variable {n : ℕ}

lemma trace_gram_pairing (B X : Matrix (Fin n) (Fin n) ℝ) :
    (B*(Xᵀ*X)).trace=∑i, qform B (X i) := by
  rw [←mul_assoc,trace_mul_cycle]
  apply sum_congr rfl
  intro i _
  simp only [diag_apply,mul_apply,transpose_apply,qform,mulVec,dotProduct]
  simp only [sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro j _
  apply sum_congr rfl
  intro k _
  ring

lemma trace_pairing_nonneg {B Z : Matrix (Fin n) (Fin n) ℝ}
    (hB : B.PosSemidef) (hZ : Z.PosSemidef) : 0 ≤ (B*Z).trace := by
  conv_rhs => rw [←sqrt_gram hZ]
  rw [trace_gram_pairing]
  exact sum_nonneg (fun i _ => qform_nonneg hB _)

lemma test_one : Test (1 : Matrix (Fin n) (Fin n) ℝ) := by
  refine ⟨Matrix.PosSemidef.one,?_⟩
  intro u v w
  have heq (a b : Fin n) : qform (1 : Matrix (Fin n) (Fin n) ℝ) (difference a b)=
      if a=b then 0 else 2 := by
    by_cases hab : a=b
    · simp [hab,difference,qform]
    · norm_num [qform,difference,MultiGraph.point,sub_dotProduct,dotProduct_sub,hab,Ne.symm hab]
  simp only [heq]
  split_ifs <;> try norm_num
  all_goals simp_all

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_CenteredDomain
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Centered domain. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma mul_constant_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*constantProjection n=0 := by
  simp only [constantProjection,mul_smul_comm,mul_vecMulVec,hD0,zero_vecMulVec,smul_zero]

lemma constant_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : constantProjection n*D=0 := by
  have hh := congrArg transpose (mul_constant_of_ones hD0)
  simpa only [transpose_mul,constantProjection_symmetric,
    (isHermitian_iff_isSymm.mp hD).eq,transpose_zero] using hh

lemma mul_centering_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD0 : D *ᵥ ones n=0) :
    D*centering n=D := by
  rw [centering,mul_sub,mul_one,mul_constant_of_ones hD0,sub_zero]

lemma centering_mul_of_ones {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centering n*D=D := by
  rw [centering,sub_mul,one_mul,constant_mul_of_ones hD hD0,sub_zero]

lemma centered_eq {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.IsHermitian)
    (hD0 : D *ᵥ ones n=0) : centered D=D := by
  rw [centered,centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma domain_psd (G : MultiGraph n m) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp ((Matrix.nonneg_iff_posSemidef.mpr (G.laplacian_psd univ)).trans hX.2.2.1)

lemma difference_sum (u v : Fin n) : (∑i, difference u v i)=0 := by
  simp [difference,point,sum_sub_distrib]

lemma test_centered (hn : 0 < n) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    CenteredTest (centered Z) := by
  refine ⟨⟨centered_psd hZ.1,?_⟩,centered_ones hn Z⟩
  intro u v w
  simpa only [qform_centered,centering_mulVec_of_sum_zero (difference_sum _ _)] using hZ.2 u v w

lemma centered_one (hn : 0 < n) : centered (1 : Matrix (Fin n) (Fin n) ℝ)=centering n := by
  rw [centered,mul_one,mul_centering_of_ones (centering_ones hn)]

lemma centering_test (hn : 0 < n) : CenteredTest (centering n) := by
  simpa only [centered_one hn] using test_centered hn (test_one (n:=n))

lemma domain_trace_bound (G : MultiGraph n m) (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) : X.trace ≤ 3*(G.laplacian univ).trace := by
  have hh := hX.2.2.2 _ (centering_test hn)
  simpa only [mul_centering_of_ones hX.2.1,mul_centering_of_ones (laplacian_ones G)] using hh

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionLattice
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition lattice. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

variable {V E : Type*} [Fintype V]

theorem partCount_strictAnti : StrictAnti (partCount (V := V)) := by
  intro p q hpq
  let f : Quotient p → Quotient q := Quotient.map id hpq.le
  have hsur : Function.Surjective f := Quotient.map_surjective hpq.le Function.surjective_id
  have hninj : ¬Function.Injective f := by
    intro hinj
    have hqp : q ≤ p := by
      intro a b hab
      apply Quotient.exact
      apply hinj
      change (Quotient.mk q a)=(Quotient.mk q b)
      exact Quotient.sound hab
    exact (not_le_of_gt hpq) hqp
  exact Fintype.card_lt_of_surjective_not_injective f hsur hninj

omit [Fintype V] in
lemma crossingIndicator_nonneg (p : Setoid V) (a b : V) : 0 ≤ crossingIndicator p a b := by
  unfold crossingIndicator
  split_ifs <;> norm_num

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_PartitionGeometry
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Partition geometry. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical

variable {V : Type*} [Fintype V]

lemma partCount_pos [Nonempty V] (p : Setoid V) : 0 < partCount p :=
  Fintype.card_pos_iff.mpr ⟨Quotient.mk p (Classical.arbitrary V)⟩

lemma partCount_top [Nonempty V] : partCount (⊤ : Setoid V)=1 := by
  apply Fintype.card_eq_one_iff.mpr
  refine ⟨Quotient.mk ⊤ (Classical.arbitrary V),?_⟩
  intro y
  induction y using Quotient.inductionOn with
  | h y => exact Quotient.sound trivial

lemma two_le_partCount [Nonempty V] {p : Setoid V} (hp : p ≠ ⊤) : 2 ≤ partCount p := by
  have hh := partCount_strictAnti (lt_top_iff_ne_top.mpr hp)
  rw [partCount_top] at hh
  exact hh

variable {n m : ℕ}

lemma capacity_eq_sum (G : MultiGraph n m) (w : Fin m → ℝ) (p : Setoid (Fin n)) :
    capacity G.left G.right w p=∑e ∈ crossing G p, w e := by
  simp only [capacity,crossing,sum_filter,crossingIndicator]
  apply sum_congr rfl
  intro e _
  split_ifs <;> simp_all

end
end AlgorithmicThinTrees.Partitions
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_ConeRepresentation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric cone representation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder Matrix.Norms.Elementwise Topology
open Filter

section Representation
variable {n : ℕ} {J : Type*} [Fintype J]

lemma psd_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ)
    {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosSemidef) : P ∈ coneImage W := by
  exact ⟨P,fun _ => 0,hP,fun _ => le_refl _,by simp⟩

lemma generator_mem_coneImage (W : J → Matrix (Fin n) (Fin n) ℝ) (j : J) :
    W j ∈ coneImage W := by
  refine ⟨0,Pi.single j 1,PosSemidef.zero,?_,?_⟩
  · intro i
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply]

end Representation
section TraceDual
variable {n : ℕ}

lemma linearTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) : (X*linearTraceMatrix f).trace=f X := by
  have hf : f X = ∑i, ∑j, X i j*f (Matrix.single i j 1) := by
    nth_rw 1 [matrix_eq_sum_single X]
    simp only [map_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    rw [show Matrix.single i j (X i j)=(X i j) • Matrix.single i j (1 : ℝ) by
      simp only [smul_single,smul_eq_mul,mul_one]]
    simp only [map_smul,smul_eq_mul]
  simpa only [Matrix.trace,diag_apply,mul_apply,linearTraceMatrix] using hf.symm

lemma trace_pairing_transpose_right {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X.IsHermitian) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (X*Zᵀ).trace=(X*Z).trace := by
  rw [←trace_transpose (X*Zᵀ),transpose_mul,transpose_transpose,
    (isHermitian_iff_isSymm.mp hX).eq,trace_mul_comm]

lemma symmetricTraceMatrix_hermitian (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) :
    (symmetricTraceMatrix f).IsHermitian := by
  apply isHermitian_iff_isSymm.mpr
  simp only [IsSymm,symmetricTraceMatrix,transpose_smul,transpose_add,transpose_transpose]
  rw [add_comm]

lemma symmetricTraceMatrix_pairing (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) :
    (X*symmetricTraceMatrix f).trace=f X := by
  rw [symmetricTraceMatrix,mul_smul_comm,mul_add,trace_smul,trace_add,
    trace_pairing_transpose_right hX,linearTraceMatrix_pairing]
  simp only [smul_eq_mul]
  ring

lemma symmetricTraceMatrix_psd (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hf : ∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P) :
    (symmetricTraceMatrix f).PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg (symmetricTraceMatrix_hermitian f)
  intro x
  simpa only [star_trivial,←ShortcutDual.trace_outer_mul,
    symmetricTraceMatrix_pairing f (ShortcutDual.outer_posSemidef x).isHermitian]
    using hf (vecMulVec x x) (ShortcutDual.outer_posSemidef x)

lemma difference_norm_sq {u v : Fin n} (huv : u ≠ v) :
    difference u v ⬝ᵥ difference u v=2 := by
  norm_num [difference,point,sub_dotProduct,dotProduct_sub,huv,huv.symm]

lemma triangleGenerator_trace (ijk : DistinctTriple n) : (triangleGenerator ijk).trace=2 := by
  simp only [triangleGenerator,triangleMatrix,trace_sub,trace_add,trace_vecMulVec,
    difference_norm_sq ijk.property.1,difference_norm_sq ijk.property.2.1,
    difference_norm_sq ijk.property.2.2]
  norm_num

lemma triangleMatrix_ones (u v w : Fin n) : triangleMatrix u v w *ᵥ ones n=0 := by
  have h (a b : Fin n) : vecMulVec (difference a b) (difference a b) *ᵥ ones n=0 := by
    rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,difference_sum,MulOpposite.op_zero,zero_smul]
  simp only [triangleMatrix,sub_mulVec,add_mulVec,h,zero_add,sub_zero]

lemma triangleMatrix_pairing (u v w : Fin n) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (triangleMatrix u v w*Z).trace=
      qform Z (difference u v)+qform Z (difference v w)-qform Z (difference u w) := by
  simp only [triangleMatrix,sub_mul,add_mul,trace_add,trace_sub,ShortcutDual.trace_outer_mul,qform]

lemma test_iff_generators (Z : Matrix (Fin n) (Fin n) ℝ) :
    Test Z ↔ Z.PosSemidef ∧ ∀ijk : DistinctTriple n, 0 ≤ (triangleGenerator ijk*Z).trace := by
  refine ⟨fun hZ => ⟨hZ.1,fun ijk => ?_⟩,fun hZ => ⟨hZ.1,fun u v w => ?_⟩⟩
  · simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hZ.2 _ _ _
  · by_cases huv : u=v
    · subst v
      simp [difference,qform]
    by_cases hvw : v=w
    · subst w
      simp [difference,qform]
    by_cases huw : u=w
    · subst w
      simpa only [difference,sub_self,mulVec_zero,dotProduct_zero,qform]
        using add_nonneg (qform_nonneg hZ.1 (difference u v)) (qform_nonneg hZ.1 (difference v u))
    have hh := hZ.2 ⟨(u,v,w),huv,hvw,huw⟩
    simpa only [triangleGenerator,triangleMatrix_pairing,sub_nonneg] using hh

theorem metric_dual_representation {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) :
    (∀Z, Test Z → 0 ≤ (A*Z).trace) ↔ A ∈ coneImage (triangleGenerator (n:=n)) := by
  constructor
  · intro hdual
    by_contra hn
    let : LocallyConvexSpace ℝ (Matrix (Fin n) (Fin n) ℝ) :=
      inferInstanceAs (LocallyConvexSpace ℝ (Fin n → Fin n → ℝ))
    obtain ⟨f,hf,hfA⟩ := (representedCone triangleGenerator triangleGenerator_trace).hyperplane_separation_point hn
    have hfP : ∀P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 0 ≤ f P :=
      fun P hP => hf P (psd_mem_coneImage triangleGenerator hP)
    let Z := symmetricTraceMatrix f.toLinearMap
    have hZ : Test Z := by
      apply (test_iff_generators Z).mpr
      refine ⟨symmetricTraceMatrix_psd f.toLinearMap hfP,fun ijk => ?_⟩
      change 0 ≤ (triangleGenerator ijk*symmetricTraceMatrix f.toLinearMap).trace
      have hi : (triangleGenerator ijk).IsHermitian := triangleMatrix_hermitian _ _ _
      rw [symmetricTraceMatrix_pairing f.toLinearMap hi]
      exact hf _ (generator_mem_coneImage triangleGenerator ijk)
    have hz := hdual Z hZ
    rw [symmetricTraceMatrix_pairing f.toLinearMap hA] at hz
    exact (not_lt_of_ge hz) hfA
  · rintro ⟨P,lam,hP,hlam,rfl⟩ Z hZ
    simp only [add_mul,sum_mul,smul_mul_assoc,trace_add,trace_sum,trace_smul,smul_eq_mul]
    exact add_nonneg (trace_pairing_nonneg hP hZ.1)
      (sum_nonneg fun ijk _ => mul_nonneg (hlam ijk) (((test_iff_generators Z).mp hZ).2 ijk))

lemma trace_centered_right {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) (Z : Matrix (Fin n) (Fin n) ℝ) :
    (A*centered Z).trace=(A*Z).trace := by
  calc
    (A*centered Z).trace=((A*centering n)*Z*centering n).trace := by
      simp only [centered,mul_assoc]
    _ = (A*Z*centering n).trace := by rw [mul_centering_of_ones hA0]
    _ = (centering n*(A*Z)).trace := trace_mul_comm _ _
    _ = (A*Z).trace := by rw [←mul_assoc,centering_mul_of_ones hA hA0]

theorem centered_metric_dual_representation (hn : 0 < n)
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) :
    (∀Z, CenteredTest Z → 0 ≤ (A*Z).trace) ↔
      ∃P : Matrix (Fin n) (Fin n) ℝ, ∃lam : DistinctTriple n → ℝ,
        P.PosSemidef ∧ P *ᵥ ones n=0 ∧ (∀ijk, 0 ≤ lam ijk) ∧
          A=P+∑ijk, lam ijk • triangleGenerator ijk := by
  constructor
  · intro hdual
    have hd : ∀Z, Test Z → 0 ≤ (A*Z).trace := fun Z hZ => by
      have h := hdual _ (test_centered hn hZ)
      rwa [trace_centered_right hA hA0] at h
    obtain ⟨P,lam,hP,hlam,he⟩ := (metric_dual_representation hA).mp hd
    refine ⟨P,lam,hP,?_,hlam,he⟩
    rw [he,add_mulVec] at hA0
    simpa only [sum_mulVec,smul_mulVec,triangleGenerator,triangleMatrix_ones,
      smul_zero,sum_const_zero,add_zero] using hA0
  · rintro ⟨P,lam,hP,_,hlam,he⟩ Z hZ
    exact (metric_dual_representation hA).mpr ⟨P,lam,hP,hlam,he⟩ Z hZ.1

theorem metricDomain_iff_lmi {m : ℕ} (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.IsHermitian) (hX0 : X *ᵥ ones n=0) :
    X ∈ metricDomain G ↔ G.laplacian univ ≤ X ∧
      ∃lam : DistinctTriple n → ℝ, (∀ijk, 0 ≤ lam ijk) ∧
        ((3:ℝ) • G.laplacian univ-X-∑ijk, lam ijk • triangleGenerator ijk).PosSemidef := by
  have hA : ((3:ℝ) • G.laplacian univ-X).IsHermitian :=
    ((G.laplacian_psd univ).smul (by norm_num : (0:ℝ) ≤ 3)).isHermitian.sub hX
  have hA0 : ((3:ℝ) • G.laplacian univ-X) *ᵥ ones n=0 := by
    simp only [sub_mulVec,smul_mulVec,laplacian_ones,hX0,smul_zero,sub_self]
  constructor
  · intro h
    refine ⟨h.2.2.1,?_⟩
    obtain ⟨P,lam,hP,_,hlam,he⟩ := (centered_metric_dual_representation hn hA hA0).mp
      (fun Z hZ => by
        simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg]
          using h.2.2.2 Z hZ)
    refine ⟨lam,hlam,?_⟩
    rwa [he,add_sub_cancel_right]
  · rintro ⟨hLX,lam,hlam,hP⟩
    refine ⟨hX,hX0,hLX,fun Z hZ => ?_⟩
    have h := (metric_dual_representation hA).mpr
      ⟨_,lam,hP,hlam,by abel⟩ Z hZ.1
    simpa only [sub_mul,smul_mul_assoc,trace_sub,trace_smul,smul_eq_mul,sub_nonneg] using h

lemma laplacian_trace {m : ℕ} (G : MultiGraph n m) : (G.laplacian univ).trace=2*m := by
  simp only [laplacian,trace_sum,trace_vecMulVec]
  have he (e : Fin m) : G.incidence e ⬝ᵥ G.incidence e=2 := difference_norm_sq (G.loopless e)
  simp only [he,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
  ring

lemma domain_trace_size {m : ℕ} (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) : X.trace ≤ 6*m := by
  have h := domain_trace_bound G hn hX
  rw [laplacian_trace G] at h
  linarith only [h]

lemma domain_multiplier_bound {m : ℕ} (G : MultiGraph n m)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X.PosSemidef)
    (lam : DistinctTriple n → ℝ)
    (hP : ((3:ℝ) • G.laplacian univ-X-∑ijk, lam ijk • triangleGenerator ijk).PosSemidef) :
    (∑ijk, lam ijk) ≤ 3*m := by
  have h := hP.trace_nonneg
  simp only [trace_sub,trace_smul,smul_eq_mul,trace_sum,triangleGenerator_trace,←sum_mul,
    laplacian_trace G] at h
  linarith only [h,hX.trace_nonneg]

end TraceDual

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Encoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation encoding. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma responseMatrix_ones (hn : 0 < n) (A : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix A *ᵥ ones n=0 := centered_ones hn _

lemma responseMatrix_fixed {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.IsHermitian) (hA0 : A *ᵥ ones n=0) : responseMatrix A=A := by
  rw [responseMatrix,(isHermitian_iff_isSymm.mp hA).eq,
    show (1/2 : ℝ) • (A+A)=A by module,centered_eq hA hA0]

lemma responseMatrix_add (A B : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (A+B)=responseMatrix A+responseMatrix B := by
  simp only [responseMatrix,transpose_add,centered,smul_add,mul_add,add_mul]
  abel

lemma responseMatrix_smul (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (c • A)=c • responseMatrix A := by
  simp only [responseMatrix,transpose_smul,←smul_add,smul_comm (1/2:ℝ) c,
    centered,mul_smul_comm,smul_mul_assoc]

lemma responseMatrix_sub (A B : Matrix (Fin n) (Fin n) ℝ) :
    responseMatrix (A-B)=responseMatrix A-responseMatrix B := by
  simp only [responseMatrix,transpose_sub,centered,smul_sub,mul_sub,sub_mul,smul_add,mul_add,add_mul]
  abel

namespace StepFree

lemma matrix_combo (a b : ℝ) (x w : StepFree n m) :
    (a • x+b • w).matrix=a • x.matrix+b • w.matrix := by
  change responseMatrix (a • x.1+b • w.1)=_
  rw [responseMatrix_add,responseMatrix_smul,responseMatrix_smul]
  rfl

lemma lowerPencil_combo (H : MultiGraph n m) (a b : ℝ) (hab : a+b=1) (x w : StepFree n m) :
    lowerPencil H (a • x+b • w)=a • lowerPencil H x+b • lowerPencil H w := by
  rw [lowerPencil,matrix_combo,lowerPencil,lowerPencil]
  have he : a • H.laplacian univ+b • H.laplacian univ=H.laplacian univ := by rw [←add_smul,hab,one_smul]
  simp only [smul_sub]
  conv_lhs => rw [←he]
  abel

lemma upperPencil_combo (H : MultiGraph n m) (a b : ℝ) (hab : a+b=1) (x w : StepFree n m) :
    upperPencil H (a • x+b • w)=a • upperPencil H x+b • upperPencil H w := by
  have he : a • H.laplacian univ+b • H.laplacian univ=H.laplacian univ := by rw [←add_smul,hab,one_smul]
  simp only [upperPencil,matrix_combo,multiplier,Prod.fst_add,Prod.smul_fst,
    Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_smul,mul_smul,sum_add_distrib,←smul_sum,smul_sub]
  have h3 : (3 : ℝ) • H.laplacian univ =
      a • (3 : ℝ) • H.laplacian univ+b • (3 : ℝ) • H.laplacian univ := by
    rw [←add_smul,hab,one_smul]
  conv_lhs => rw [h3]
  module

lemma edgePencil_combo (H : MultiGraph n m) (s a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    edgePencil H s (a • x+b • w) e=a • edgePencil H s x e+b • edgePencil H s w e := by
  simp only [edgePencil,matrix_combo,y,Prod.fst_add,Prod.smul_fst,Prod.snd_add,
    Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul,smul_sub,smul_smul]
  module

lemma capacities_combo (κ a b : ℝ) (hab : a+b=1) (u : Fin m → ℝ) (x w : StepFree n m) :
    capacities κ u (a • x+b • w)=a • capacities κ u x+b • capacities κ u w := by
  ext e
  simp only [capacities,z,Prod.snd_add,Prod.smul_snd,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs
  · rfl
  · rw [←add_mul,hab,one_mul]

end StepFree

lemma stepCore_domain (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) :
    x.matrix ∈ metricDomain H := by
  apply (metricDomain_iff_lmi H hn (responseMatrix_hermitian x.1) (responseMatrix_ones hn x.1)).mpr
  exact ⟨Matrix.le_iff.mpr hx.1,x.multiplier,hx.2.2.1,hx.2.1⟩

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Feasibility
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation feasibility. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

lemma slack_top {V E : Type*} [Fintype V] [Nonempty V] [Fintype E]
    (left right : E → V) (w : E → ℝ) (Q : ℝ) :
    slack left right w Q ⊤=0 := by
  simp [slack,capacity,crossingIndicator,partCount_top]

end
end AlgorithmicThinTrees.Partitions

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Finset Matrix StrongThinTree StrongThinTree.MultiGraph
open Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma continuation_parameters (m : ℕ) :
    0 < continuationBaseline m ∧ continuationBaseline m ≤ 1 ∧
    continuationBaseline m*m < 1 ∧
    0 ≤ continuationStep m ∧ continuationStep m ≤ 1/32 ∧
    4*continuationStep m ≤ continuationBaseline m ∧ 4*continuationStep m*m ≤ 1 := by
  have hmp : (0:ℝ) < m+1 := by positivity
  have hκ : 0 < continuationBaseline m := one_div_pos.mpr hmp
  have hκeq : continuationBaseline m*((m:ℝ)+1)=1 := div_mul_cancel₀ 1 (ne_of_gt hmp)
  have hκm : 0 ≤ continuationBaseline m*m := mul_nonneg hκ.le (Nat.cast_nonneg m)
  have hκ1 : continuationBaseline m ≤ 1 := by nlinarith only [hκeq,hκm]
  have hκm1 : continuationBaseline m*m < 1 := by nlinarith only [hκeq,hκ]
  refine ⟨hκ,hκ1,hκm1,?_,?_,?_,?_⟩ <;> unfold continuationStep <;>
    nlinarith only [hκ,hκ1,hκm1,hκm]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_SpectralSize
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Spectral size. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma laplacian_centered_energy (G : MultiGraph n m) (x : Fin n → ℝ) :
    qform (G.laplacian univ) (centering n *ᵥ x)=qform (G.laplacian univ) x := by
  rw [←qform_centered,centered_eq (G.laplacian_psd univ).isHermitian (laplacian_ones G)]

lemma range_le_edge_variation (G : MultiGraph n m) (hc : G.Connected univ)
    (x : Fin n → ℝ) (a b : Fin n)
    (ha : ∀i, x a ≤ x i) (hb : ∀i, x i ≤ x b) :
    x b-x a ≤ ∑e : Fin m, |x (G.left e)-x (G.right e)| := by
  have he : G.EdgeConnected 1 := fun S hS hp => card_pos.mpr (hc S hS hp)
  have h := G.clamped_variation_lower he x (ha b) ⟨a,le_rfl⟩ ⟨b,le_rfl⟩
  have hcl (i : Fin n) : Geometry.clamp (x a) (x b) (x i)=x i := by
    simp only [Geometry.clamp,max_eq_right (ha i),min_eq_right (hb i)]
  simpa only [Nat.cast_one,one_mul,hcl] using h

theorem laplacian_poincare (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : ∑i, x i=0) :
    (∑i, x i^2) ≤ (n : ℝ)*m*qform (G.laplacian univ) x := by
  have hne : (univ : Finset (Fin n)).Nonempty := ⟨⟨0,hn⟩,mem_univ _⟩
  obtain ⟨a,_,ha⟩ := exists_min_image univ x hne
  obtain ⟨b,_,hb⟩ := exists_max_image univ x hne
  have ha' : ∀i, x a ≤ x i := fun i => ha i (mem_univ _)
  have hb' : ∀i, x i ≤ x b := fun i => hb i (mem_univ _)
  have hna : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have ha0 : x a ≤ 0 := by
    have h := sum_le_sum (fun i (_ : i ∈ univ) => ha' i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hx] at h
    nlinarith only [h,hna]
  have hb0 : 0 ≤ x b := by
    have h := sum_le_sum (fun i (_ : i ∈ univ) => hb' i)
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,hx] at h
    nlinarith only [h,hna]
  have hnorm : (∑i, x i^2) ≤ (n : ℝ)*(x b-x a)^2 := by
    have h (i : Fin n) : x i^2 ≤ (x b-x a)^2 := by
      have hh : |x i| ≤ x b-x a := abs_le.mpr ⟨by linarith [ha' i],by linarith [hb' i]⟩
      simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x i)) hh 2
    simpa only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using
      sum_le_sum (fun i (_ : i ∈ univ) => h i)
  have hvar := range_le_edge_variation G hc x a b ha' hb'
  have hsqr : (x b-x a)^2 ≤ (∑e : Fin m, |x (G.left e)-x (G.right e)|)^2 :=
    pow_le_pow_left₀ (sub_nonneg.mpr (ha' b)) hvar 2
  have hCS := sq_sum_le_card_mul_sum_sq (s := univ)
    (f := fun e : Fin m => |x (G.left e)-x (G.right e)|)
  simp only [card_univ,Fintype.card_fin,sq_abs,←G.laplacian_qform] at hCS
  exact hnorm.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hsqr.trans hCS) hna.le)

lemma graphSize_pos : 0 < graphSize n m := by
  dsimp [graphSize]
  positivity

lemma vertex_edge_le_size_cube : (n : ℝ)*m ≤ (graphSize n m)^3 := by
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hnP : (n : ℝ) ≤ graphSize n m := by dsimp [graphSize] <;> linarith
  have hmP : (m : ℝ) ≤ graphSize n m := by dsimp [graphSize] <;> linarith
  have hP : 1 ≤ graphSize n m := by dsimp [graphSize] <;> linarith
  have hsq : (n : ℝ)*m ≤ (graphSize n m)^2 := by
    simpa only [pow_two] using mul_le_mul hnP hmP hm (le_trans hn hnP)
  exact hsq.trans (by
    have h := mul_le_mul_of_nonneg_left hP (sq_nonneg (graphSize n m))
    nlinarith only [h])

theorem laplacian_spectral_gap (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : ∑i, x i=0) :
    (graphSize n m)^(-3 : ℤ)*(∑i, x i^2) ≤ qform (G.laplacian univ) x := by
  have hbound : (∑i, x i^2) ≤ (graphSize n m)^3*qform (G.laplacian univ) x :=
    (laplacian_poincare G hn hc x hx).trans
      (mul_le_mul_of_nonneg_right vertex_edge_le_size_cube (qform_nonneg (G.laplacian_psd univ) x))
  simp only [_root_.zpow_neg,zpow_ofNat] 
  rw [inv_mul_le_iff₀ (pow_pos graphSize_pos 3)]
  exact hbound

lemma qform_one_sum_sq (x : Fin n → ℝ) :
    qform (1 : Matrix (Fin n) (Fin n) ℝ) x=∑i, x i^2 := by
  simp only [qform,one_mulVec,dotProduct,pow_two]

lemma centering_idempotent (hn : 0 < n) : centering n*centering n=centering n :=
  mul_centering_of_ones (centering_ones hn)

lemma qform_centering_sum_sq (hn : 0 < n) (x : Fin n → ℝ) :
    qform (centering n) x=∑i, (centering n *ᵥ x) i^2 := by
  rw [←qform_one_sum_sq,←qform_centered]
  simp only [centered,mul_one,centering_idempotent hn]

lemma centering_psd (hn : 0 < n) : (centering n).PosSemidef := by
  have h := centered_psd (PosSemidef.one : (1 : Matrix (Fin n) (Fin n) ℝ).PosSemidef)
  simpa only [centered,mul_one,centering_idempotent hn] using h

theorem laplacian_lower_order (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ) :
    (graphSize n m)^(-3 : ℤ) • centering n ≤ G.laplacian univ := by
  apply Matrix.le_iff.mpr
  apply PosSemidef.of_dotProduct_mulVec_nonneg
    ((G.laplacian_psd univ).isHermitian.sub
      ((centering_psd hn).smul (zpow_nonneg graphSize_pos.le _)).isHermitian)
  intro x
  change 0 ≤ qform (G.laplacian univ-(graphSize n m)^(-3 : ℤ) • centering n) x
  rw [qform_sub,qform_smul,qform_centering_sum_sq hn]
  have h := laplacian_spectral_gap G hn hc (centering n *ᵥ x) (centering_mulVec_sum hn x)
  rw [laplacian_centered_energy G x] at h
  linarith only [h]

lemma qform_outer (b x : Fin n → ℝ) : qform (vecMulVec b b) x=(b ⬝ᵥ x)^2 := by
  simp only [qform,vecMulVec_mulVec,dotProduct_smul,IsCentralScalar.op_smul_eq_smul,smul_eq_mul]
  rw [dotProduct_comm x b,pow_two]

lemma qform_outer_le (b x : Fin n → ℝ) :
    qform (vecMulVec b b) x ≤ (b ⬝ᵥ b)*(∑i, x i^2) := by
  simpa only [qform_outer,dotProduct,pow_two] using sum_mul_sq_le_sq_mul_sq univ b x

lemma difference_outer_le {a b : Fin n} (hab : a ≠ b) (x : Fin n → ℝ) :
    qform (vecMulVec (difference a b) (difference a b)) x ≤ 2*(∑i, x i^2) := by
  simpa only [difference_norm_sq hab] using qform_outer_le (difference a b) x

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Interior
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation interior. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

lemma qform_transpose (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform Aᵀ v=qform A v := by
  simp only [qform,dotProduct_mulVec,vecMul_transpose,dotProduct_comm]

lemma qform_responseMatrix (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform (responseMatrix A) v=qform A (centering n *ᵥ v) := by
  rw [responseMatrix,qform_centered,qform_smul,qform_add,qform_transpose]
  ring

lemma qform_sum {J : Type*} [Fintype J] (A : J → Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    qform (∑j, A j) v=∑j, qform (A j) v := by
  simp only [qform,sum_mulVec,dotProduct_sum]

lemma abs_qform_le_entries {A : Matrix (Fin n) (Fin n) ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hA : ∀i j, |A i j| ≤ η) (v : Fin n → ℝ) :
    |qform A v| ≤ (n : ℝ)*η*(∑i, v i^2) := by
  have hq : qform A v=∑i, ∑j, v i*A i j*v j := by
    simp only [qform,mulVec,dotProduct,mul_sum]
    congr 1
    ext i
    exact sum_congr rfl fun j _ => (mul_assoc _ _ _).symm
  have hh : ∑i, ∑j, |v i*A i j*v j| ≤ η*(∑i, |v i|)^2 := by
    calc
      _ ≤ ∑i, ∑j, |v i| *η*|v j| := sum_le_sum fun i _ => sum_le_sum fun j _ => by
        rw [abs_mul,abs_mul]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA i j) (abs_nonneg _)) (abs_nonneg _)
      _ = _ := by simp only [←mul_sum,←sum_mul] <;> ring
  have hcs : (∑i, |v i|)^2 ≤ (n : ℝ)*(∑i, v i^2) := by
    simpa only [sq_abs,card_univ,Fintype.card_fin] using sq_sum_le_card_mul_sum_sq (s:=univ) (f:=fun i => |v i|)
  calc
    _ ≤ ∑i, ∑j, |v i*A i j*v j| := by
      rw [hq]
      exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ η*(∑i, |v i|)^2 := hh
    _ ≤ _ := by nlinarith only [mul_le_mul_of_nonneg_left hcs hη]

lemma difference_outer_centered {a b : Fin n} (hab : a ≠ b) (v : Fin n → ℝ) :
    qform (vecMulVec (difference a b) (difference a b)) v ≤
      2*(∑i, (centering n *ᵥ v) i^2) := by
  have h := difference_outer_le hab (centering n *ᵥ v)
  rwa [qform_outer,centered_dot _ _ (difference_sum a b),←qform_outer] at h

lemma abs_triangle_energy (ijk : DistinctTriple n) (v : Fin n → ℝ) :
    |qform (triangleGenerator ijk) v| ≤ 6*(∑i, (centering n *ᵥ v) i^2) := by
  have h1 := difference_outer_centered ijk.property.1 v
  have h2 := difference_outer_centered ijk.property.2.1 v
  have h3 := difference_outer_centered ijk.property.2.2 v
  have h1n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.1 ijk.1.2.1)) v
  have h2n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.2.1 ijk.1.2.2)) v
  have h3n := qform_nonneg (ShortcutDual.outer_posSemidef (difference ijk.1.1 ijk.1.2.2)) v
  rw [triangleGenerator,triangleMatrix,qform_sub,qform_add]
  apply abs_le.mpr
  constructor <;> linarith only [h1,h2,h3,h1n,h2n,h3n]

lemma distinctTriple_card_le : Fintype.card (DistinctTriple n) ≤ n^3 := by
  have h := Fintype.card_subtype_le (fun p : Fin n × Fin n × Fin n =>
    p.1 ≠ p.2.1 ∧ p.2.1 ≠ p.2.2 ∧ p.1 ≠ p.2.2)
  simpa only [Fintype.card_prod,Fintype.card_fin,pow_succ,pow_zero,one_mul,mul_assoc] using h

lemma abs_triangle_sum {lam : DistinctTriple n → ℝ} {η : ℝ}
    (hη : 0 ≤ η) (hlam : ∀ijk, |lam ijk| ≤ η) (v : Fin n → ℝ) :
    |qform (∑ijk, lam ijk • triangleGenerator ijk) v| ≤
      6*(n : ℝ)^3*η*(∑i, (centering n *ᵥ v) i^2) := by
  simp only [qform_sum,qform_smul]
  calc
    _ ≤ ∑ijk, |lam ijk*qform (triangleGenerator ijk) v| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ijk : DistinctTriple n, η*(6*(∑i, (centering n *ᵥ v) i^2)) := by
      apply sum_le_sum
      intro ijk _
      rw [abs_mul]
      exact mul_le_mul (hlam ijk) (abs_triangle_energy ijk v) (abs_nonneg _) hη
    _ = (Fintype.card (DistinctTriple n) : ℝ)*η*6*(∑i, (centering n *ᵥ v) i^2) := by
      simp only [sum_const,card_univ,nsmul_eq_mul] <;> ring
    _ ≤ _ := by
      have hc : (Fintype.card (DistinctTriple n) : ℝ) ≤ (n : ℝ)^3 := by exact_mod_cast distinctTriple_card_le (n:=n)
      nlinarith only [mul_le_mul_of_nonneg_right hc
        (show 0 ≤ η*6*(∑i, (centering n *ᵥ v) i^2) by positivity)]

namespace StepFree

lemma Close.mono {x w : StepFree n m} {η δ : ℝ} (h : Close x w η) (hηδ : η ≤ δ) : Close x w δ :=
  ⟨fun i j => (h.1 i j).trans hηδ,fun ijk => (h.2.1 ijk).trans hηδ,
    fun e => (h.2.2.1 e).trans hηδ,fun e => (h.2.2.2 e).trans hηδ⟩

lemma Close.qform_bound {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (v : Fin n → ℝ) :
    |qform x.matrix v-qform w.matrix v| ≤ (n : ℝ)*η*(∑i, (centering n *ᵥ v) i^2) := by
  rw [←qform_sub,matrix,matrix,←responseMatrix_sub,qform_responseMatrix]
  exact abs_qform_le_entries hη h.1 _

end StepFree

lemma scaled_inverse_power {P c : ℝ} (hP : 0 < P) (a b : ℕ) (hc : c ≤ P^b) :
    c*P^(-((a+b : ℕ) : ℤ)) ≤ P^(-(a : ℤ)) := by
  have h := mul_le_mul_of_nonneg_right hc (zpow_nonneg hP.le (-((a+b : ℕ) : ℤ)))
  calc
    _ ≤ P^b*P^(-((a+b : ℕ) : ℤ)) := h
    _ = _ := by
      rw [←zpow_natCast,←zpow_add₀ (ne_of_gt hP)]
      congr 1
      push_cast
      ring

lemma inverse_power_mono {P : ℝ} (hP : 1 ≤ P) {a b : ℕ} (hab : a ≤ b) :
    P^(-(b : ℤ)) ≤ P^(-(a : ℤ)) := by
  simp only [_root_.zpow_neg,zpow_natCast]
  exact (inv_le_inv₀ (pow_pos (lt_of_lt_of_le zero_lt_one hP) _)
    (pow_pos (lt_of_lt_of_le zero_lt_one hP) _)).mpr (pow_le_pow_right₀ hP hab)

lemma auxiliary_numbers {P s κ : ℝ} (hP : 5 ≤ P) (hnP : (n : ℝ) ≤ P)
    (_hs : 0 ≤ s) (hsP : s ≤ P) (hκ : P⁻¹ ≤ κ) :
    let c := P^(-8 : ℤ)
    let η := P^(-20 : ℤ)
    let μ := P^(-3 : ℤ)
    0 < c ∧ 0 < η ∧ η ≤ c ∧ c+η ≤ 1 ∧ 4*η ≤ κ ∧
      (n : ℝ)*η ≤ μ ∧
      (n : ℝ)*η+6*(n : ℝ)^3*(c+η) ≤ μ ∧
      (n : ℝ)*η+12*s*(c+η) ≤ 2*μ := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hc0 := zpow_pos hP0 (-8)
  have hη0 := zpow_pos hP0 (-20)
  have hηc : P^(-20 : ℤ) ≤ P^(-8 : ℤ) := inverse_power_mono hP1 (by norm_num : 8 ≤ 20)
  have hP2 : 25 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-5)]
  have hP4 : 25 ≤ P^4 := by
    have hh : P^2 ≤ P^4 := pow_le_pow_right₀ hP1 (by norm_num)
    exact hP2.trans hh
  have hsmall := scaled_inverse_power hP0 0 8 (show (2 : ℝ) ≤ P^8 by
    exact (by linarith : (2 : ℝ) ≤ P).trans (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 8)))
  simp only [Nat.cast_zero,Nat.zero_add,neg_zero,zpow_zero,Nat.cast_ofNat] at hsmall
  have hfour : 4*P^(-20 : ℤ) ≤ P⁻¹ := by
    have hh := scaled_inverse_power hP0 1 19 (show (4 : ℝ) ≤ P^19 by
      exact (by linarith : (4 : ℝ) ≤ P).trans (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 19)))
    simpa using hh
  have hnη : (n : ℝ)*P^(-20 : ℤ) ≤ P^(-8 : ℤ) := by
    calc
      _ ≤ P*P^(-20 : ℤ) := mul_le_mul_of_nonneg_right hnP hη0.le
      _ = P^(-19 : ℤ) := by simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-20)).symm
      _ ≤ _ := inverse_power_mono hP1 (by norm_num : 8 ≤ 19)
  have hn3 : (n : ℝ)^3 ≤ P^3 := pow_le_pow_left₀ (Nat.cast_nonneg _) hnP 3
  have hP3 : 1 ≤ P^3 := one_le_pow₀ hP1
  have hu : 13*P^(-5 : ℤ) ≤ P^(-3 : ℤ) := by
    simpa using scaled_inverse_power hP0 3 2 (show (13 : ℝ) ≤ P^2 by linarith)
  have he : 25*P^(-7 : ℤ) ≤ P^(-3 : ℤ) := by
    simpa using scaled_inverse_power hP0 3 4 hP4
  have hupper : (n : ℝ)*P^(-20 : ℤ)+6*(n : ℝ)^3*(P^(-8 : ℤ)+P^(-20 : ℤ)) ≤ P^(-3 : ℤ) := by
    calc
      _ ≤ P^(-8 : ℤ)+12*P^3*P^(-8 : ℤ) := by
        have hh := mul_le_mul hn3 (show P^(-8 : ℤ)+P^(-20 : ℤ) ≤ 2*P^(-8 : ℤ) by linarith)
          (by positivity) (by positivity : 0 ≤ P^3)
        nlinarith only [hnη,hh]
      _ ≤ 13*P^3*P^(-8 : ℤ) := by nlinarith only [mul_le_mul_of_nonneg_right hP3 hc0.le]
      _ = 13*P^(-5 : ℤ) := by rw [mul_assoc,←zpow_natCast,←zpow_add₀ (ne_of_gt hP0)]; norm_num
      _ ≤ _ := hu
  have hedge : (n : ℝ)*P^(-20 : ℤ)+12*s*(P^(-8 : ℤ)+P^(-20 : ℤ)) ≤ P^(-3 : ℤ) := by
    calc
      _ ≤ P^(-8 : ℤ)+24*P*P^(-8 : ℤ) := by
        have hh := mul_le_mul hsP (show P^(-8 : ℤ)+P^(-20 : ℤ) ≤ 2*P^(-8 : ℤ) by linarith)
          (by positivity) hP0.le
        nlinarith only [hnη,hh]
      _ ≤ 25*P*P^(-8 : ℤ) := by nlinarith only [mul_le_mul_of_nonneg_right hP1 hc0.le]
      _ = 25*P^(-7 : ℤ) := by
        rw [mul_assoc]
        congr 1
        simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-8)).symm
      _ ≤ _ := he
  exact ⟨hc0,hη0,hηc,by linarith,hfour.trans hκ,
    hnη.trans (inverse_power_mono hP1 (by norm_num : 3 ≤ 8)),hupper,
    hedge.trans (le_mul_of_one_le_left (zpow_nonneg hP0.le _) (by norm_num))⟩

lemma auxiliaryPoint_matrix (H : MultiGraph n m) {κ : ℝ} :
    (auxiliaryPoint H κ).matrix=(2 : ℝ) • H.laplacian univ := by
  apply responseMatrix_fixed ((H.laplacian_psd univ).smul (by norm_num : (0 : ℝ) ≤ 2)).isHermitian
  rw [smul_mulVec,laplacian_ones,smul_zero]

lemma connected_size_five (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ) :
    5 ≤ graphSize n m := by
  have hm : 0 < m := by
    have hproper : ({⟨0,by omega⟩} : Finset (Fin n)) ≠ univ := by
      intro h
      have hh := congrArg Finset.card h
      simp only [card_singleton,card_univ,Fintype.card_fin] at hh
      omega
    obtain ⟨e,_⟩ := hc _ (singleton_nonempty _) hproper
    exact Nat.zero_lt_of_lt e.isLt
  dsimp [graphSize]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  linarith

lemma baseline_lower : (graphSize n m)⁻¹ ≤ continuationBaseline m := by
  rw [continuationBaseline,one_div]
  exact (inv_le_inv₀ graphSize_pos (by positivity : (0 : ℝ) < m+1)).mpr (by
    dsimp [graphSize]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    linarith)

theorem auxiliary_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hc : H.Connected univ)
    {s : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {x : StepFree n m}
    (hx : x.Close (auxiliaryPoint H (continuationBaseline m)) ((graphSize n m)^(-20 : ℤ))) :
    x ∈ stepCore H s (continuationBaseline m) (continuationStep m) u := by
  let P := graphSize n m
  let c := P^(-8 : ℤ)
  let η := P^(-20 : ℤ)
  let μ := P^(-3 : ℤ)
  let κ := continuationBaseline m
  have hP := connected_size_five H hn hc
  have hnP : (n : ℝ) ≤ P := by dsimp [P,graphSize] <;> linarith [Nat.cast_nonneg (α:=ℝ) m]
  obtain ⟨hc0,hη0,hηc,hcy,hηκ,hl,hu,he⟩ := auxiliary_numbers hP hnP hs hsP (baseline_lower (n:=n) (m:=m))
  have hκ0 : 0 < κ := (continuation_parameters m).1
  have hlam (ijk : DistinctTriple n) : 0 ≤ x.multiplier ijk ∧ |x.multiplier ijk| ≤ c+η := by
    have hh := abs_le.mp (hx.2.1 ijk)
    change -(η) ≤ x.multiplier ijk-c ∧ x.multiplier ijk-c ≤ η at hh
    have hl : 0 ≤ x.multiplier ijk := by linarith only [hh.1,hηc]
    refine ⟨hl,?_⟩
    rw [abs_of_nonneg hl]
    linarith only [hh.2]
  have hy (e : Fin m) : 0 ≤ x.y e ∧ x.y e ≤ c+η := by
    have hh := abs_le.mp (hx.2.2.1 e)
    change -η ≤ x.y e-c ∧ x.y e-c ≤ η at hh
    constructor <;> linarith only [hh.1,hh.2,hηc]
  have hz (e : Fin m) : κ/2-η ≤ x.z e ∧ x.z e ≤ κ/2+η := by
    have hh := abs_le.mp (hx.2.2.2 e)
    change -η ≤ x.z e-κ/2 ∧ x.z e-κ/2 ≤ η at hh
    constructor <;> linarith only [hh.1,hh.2]
  have henergy (v : Fin n → ℝ) : μ*(∑i, (centering n *ᵥ v) i^2) ≤ qform (H.laplacian univ) v := by
    simpa only [qform_smul,qform_centering_sum_sq (by omega : 0 < n)] using
      qform_mono (laplacian_lower_order H (by omega) hc) v
  have herror (v : Fin n → ℝ) :
      |qform x.matrix v-2*qform (H.laplacian univ) v| ≤
        (n : ℝ)*η*(∑i, (centering n *ᵥ v) i^2) := by
    simpa only [auxiliaryPoint_matrix,qform_smul] using hx.qform_bound hη0.le v
  refine ⟨?_,?_,fun ijk => (hlam ijk).1,fun e => ⟨(hy e).1,(hy e).2.trans hcy⟩,?_,?_⟩
  · apply PosSemidef.of_dotProduct_mulVec_nonneg (lowerPencil_hermitian H x)
    intro v
    change 0 ≤ qform (x.lowerPencil H) v
    rw [StepFree.lowerPencil,qform_sub]
    have hb := (abs_le.mp (herror v)).1
    have he := mul_le_mul_of_nonneg_right hl (show 0 ≤ ∑i, (centering n *ᵥ v) i^2 by positivity)
    linarith only [hb,he,henergy v]
  · apply PosSemidef.of_dotProduct_mulVec_nonneg (upperPencil_hermitian H x)
    intro v
    change 0 ≤ qform (x.upperPencil H) v
    rw [StepFree.upperPencil,qform_sub,qform_sub,qform_smul]
    have hb := (abs_le.mp (herror v)).2
    have hT := (abs_le.mp (abs_triangle_sum (show 0 ≤ c+η by positivity) (fun ijk => (hlam ijk).2) v)).2
    have he := mul_le_mul_of_nonneg_right hu (show 0 ≤ ∑i, (centering n *ᵥ v) i^2 by positivity)
    change ((n : ℝ)*η+6*(n : ℝ)^3*(c+η))*(∑i, (centering n *ᵥ v) i^2) ≤ _ at he
    linarith only [hb,hT,he,henergy v]
  · intro e
    exact ⟨by linarith only [(hz e).1,hηκ,hκ0],by linarith only [(hz e).2,hηκ,hκ0]⟩
  · intro e _
    refine ⟨?_,?_⟩
    · apply PosSemidef.of_dotProduct_mulVec_nonneg (edgePencil_hermitian H s x e)
      intro v
      change 0 ≤ qform (x.edgePencil H s e) v
      rw [StepFree.edgePencil,qform_sub,qform_smul]
      have hb := (abs_le.mp (herror v)).1
      have hE : 0 ≤ ∑i, (centering n *ᵥ v) i^2 := by positivity
      have hn0 := qform_nonneg (ShortcutDual.outer_posSemidef (H.incidence e)) v
      have hR := mul_le_mul (hy e).2 (difference_outer_centered (H.loopless e) v) hn0 (by positivity : 0 ≤ c+η)
      have hR' := mul_le_mul_of_nonneg_left hR (show 0 ≤ 6*s by positivity)
      change 6*s*(x.y e*qform (vecMulVec (H.incidence e) (H.incidence e)) v) ≤ _ at hR'
      have he' := mul_le_mul_of_nonneg_right he hE
      change ((n : ℝ)*η+12*s*(c+η))*(∑i, (centering n *ᵥ v) i^2) ≤ _ at he'
      linarith only [hb,hR',he',henergy v]
    · have hgain : 0 ≤ (κ/32)*x.y e := mul_nonneg (by positivity) (hy e).1
      change x.z e ≤ κ+u e+(κ/32)*(5*x.y e-4)
      nlinarith only [(hz e).2,hηκ,hκ0,hu0 e,hgain]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Margin
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation margin. -/

section

namespace AlgorithmicThinTrees.Partitions
noncomputable section
open Finset
open scoped Classical

lemma partCount_le_card {V : Type*} [Fintype V] (p : Setoid V) :
    partCount p ≤ Fintype.card V :=
  Fintype.card_le_of_surjective (Quotient.mk p) Quotient.mk_surjective

lemma crossingIndicator_le_one {V : Type*} (p : Setoid V) (a b : V) :
    crossingIndicator p a b ≤ 1 := by
  unfold crossingIndicator
  split_ifs <;> norm_num

lemma slack_combo {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (w z : E → ℝ) (q a b : ℝ) (hab : a+b=1)
    (p : Setoid V) :
    slack left right (a • w+b • z) q p=
      a*slack left right w q p+b*slack left right z q p := by
  simp only [slack,capacity,Pi.add_apply,Pi.smul_apply,smul_eq_mul,
    add_mul,sum_add_distrib,mul_assoc,←mul_sum]
  linear_combination (q*((partCount p:ℝ)-1))*hab

lemma slack_change_target {V E : Type*} [Fintype V] [Fintype E]
    (left right : E → V) (w : E → ℝ) (q β : ℝ) (p : Setoid V) :
    slack left right w (q-β) p=slack left right w q p+β*((partCount p:ℝ)-1) := by
  unfold slack
  ring

end
end AlgorithmicThinTrees.Partitions

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise

variable {n m : ℕ}

namespace StepFree

lemma multiplier_combo (a b : ℝ) (x w : StepFree n m) (ijk : DistinctTriple n) :
    (a • x+b • w).multiplier ijk=a*x.multiplier ijk+b*w.multiplier ijk := rfl

lemma y_combo (a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    (a • x+b • w).y e=a*x.y e+b*w.y e := rfl

lemma z_combo (a b : ℝ) (x w : StepFree n m) (e : Fin m) :
    (a • x+b • w).z e=a*x.z e+b*w.z e := rfl

lemma Close.refl (x : StepFree n m) {η : ℝ} (hη : 0 ≤ η) : Close x x η := by
  simp only [Close,sub_self,abs_zero]
  exact ⟨fun _ _ => hη,fun _ => hη,fun _ => hη,fun _ => hη⟩

lemma close_add_rescale {x c w : StepFree n m} {a η : ℝ} (ha : 0 < a)
    (h : Close x c (a*η)) : Close (w+a⁻¹ • (x-c)) w η := by
  have he (v z w : ℝ) (hh : |v-z| ≤ a*η) : |w+a⁻¹*(v-z)-w| ≤ η := by
    rw [add_sub_cancel_left,abs_mul,abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹*(a*η) := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr ha.le)
      _ = η := by rw [←mul_assoc,inv_mul_cancel₀ (ne_of_gt ha),one_mul]
  refine ⟨fun i j => ?_,fun ijk => ?_,fun e => ?_,fun e => ?_⟩
  · exact he _ _ _ (h.1 i j)
  · exact he _ _ _ (h.2.1 ijk)
  · exact he _ _ _ (h.2.2.1 e)
  · exact he _ _ _ (h.2.2.2 e)

lemma Close.capacities {x w : StepFree n m} {η : ℝ} (hη : 0 ≤ η)
    (h : Close x w η) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) :
    |x.capacities κ u e-w.capacities κ u e| ≤ η := by
  unfold StepFree.capacities
  split_ifs
  · exact h.2.2.2 e
  · simpa only [sub_self,abs_zero] using hη

lemma Close.slack (H : MultiGraph n m) {x w : StepFree n m} {η : ℝ}
    (hη : 0 ≤ η) (h : Close x w η) (κ q : ℝ) (u : Fin m → ℝ) (p : Setoid (Fin n)) :
    |slack H.left H.right (x.capacities κ u) q p-
      slack H.left H.right (w.capacities κ u) q p| ≤ (m : ℝ)*η := by
  simp only [Partitions.slack,sub_sub_sub_cancel_right,capacity,←sum_sub_distrib,←sub_mul]
  calc
    _ ≤ ∑e, |(x.capacities κ u e-w.capacities κ u e)*crossingIndicator p (H.left e) (H.right e)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑_e : Fin m, η := by
      apply sum_le_sum
      intro e _
      rw [abs_mul,abs_of_nonneg (crossingIndicator_nonneg _ _ _)]
      exact (mul_le_mul (h.capacities hη κ u e) (crossingIndicator_le_one _ _ _)
        (crossingIndicator_nonneg _ _ _) hη).trans_eq (mul_one η)
    _ = _ := by simp

end StepFree

lemma stepCore_convex (H : MultiGraph n m) (s κ t : ℝ) (u : Fin m → ℝ) :
    Convex ℝ (stepCore H s κ t u) := by
  intro x hx w hw a b ha hb hab
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · rw [StepFree.lowerPencil_combo H a b hab]
    exact (hx.1.smul ha).add (hw.1.smul hb)
  · rw [StepFree.upperPencil_combo H a b hab]
    exact (hx.2.1.smul ha).add (hw.2.1.smul hb)
  · intro ijk
    rw [StepFree.multiplier_combo]
    exact add_nonneg (mul_nonneg ha (hx.2.2.1 ijk)) (mul_nonneg hb (hw.2.2.1 ijk))
  · intro e
    rw [StepFree.y_combo]
    exact ⟨add_nonneg (mul_nonneg ha (hx.2.2.2.1 e).1) (mul_nonneg hb (hw.2.2.2.1 e).1),
      calc
        _ ≤ a*1+b*1 := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.1 e).2 ha)
          (mul_le_mul_of_nonneg_left (hw.2.2.2.1 e).2 hb)
        _ = 1 := by simpa using hab⟩
  · intro e
    rw [StepFree.z_combo]
    exact ⟨add_nonneg (mul_nonneg ha (hx.2.2.2.2.1 e).1) (mul_nonneg hb (hw.2.2.2.2.1 e).1),
      calc
        _ ≤ a*(κ+1)+b*(κ+1) := add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.2.1 e).2 ha)
          (mul_le_mul_of_nonneg_left (hw.2.2.2.2.1 e).2 hb)
        _ = κ+1 := by rw [←add_mul,hab,one_mul]⟩
  · intro e he
    refine ⟨?_,?_⟩
    · rw [StepFree.edgePencil_combo]
      exact ((hx.2.2.2.2.2 e he).1.smul ha).add ((hw.2.2.2.2.2 e he).1.smul hb)
    · rw [StepFree.y_combo,StepFree.z_combo]
      calc
        _ ≤ a*(κ+u e+t*(5*x.y e-4))+b*(κ+u e+t*(5*w.y e-4)) :=
          add_le_add (mul_le_mul_of_nonneg_left (hx.2.2.2.2.2 e he).2 ha)
            (mul_le_mul_of_nonneg_left (hw.2.2.2.2.2 e he).2 hb)
        _ = _ := by linear_combination (κ+u e-4*t)*hab

lemma convex_innerCube (K : Set (StepFree n m)) (hK : Convex ℝ K)
    (z c : StepFree n m) (hz : z ∈ K) {a η : ℝ} (ha : 0 < a) (ha1 : a ≤ 1)
    (hc : ∀x, x.Close c η → x ∈ K) {x : StepFree n m}
    (hx : x.Close ((1-a) • z+a • c) (a*η)) : x ∈ K := by
  have hu := hc _ (StepFree.close_add_rescale ha hx)
  have hh := hK hz hu (sub_nonneg.mpr ha1) ha.le (by ring : 1-a+a=1)
  have he : (1-a) • z+a • (c+a⁻¹ • (x-((1-a) • z+a • c)))=x := by
    rw [smul_add,smul_smul,mul_inv_cancel₀ (ne_of_gt ha),one_smul]
    abel
  rwa [he] at hh

lemma auxiliary_slack (H : MultiGraph n m) (hn : 0 < n)
    (u : Fin m → ℝ) {q : ℝ} (hq : q ≤ m) (p : Setoid (Fin n)) :
    -(graphSize n m)^2 ≤ slack H.left H.right
      ((auxiliaryPoint H (continuationBaseline m)).capacities (continuationBaseline m) u) q p := by
  have : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hd0 : 0 ≤ (partCount p:ℝ)-1 := by
    have hh : (1:ℝ) ≤ partCount p := by exact_mod_cast partCount_pos p
    linarith only [hh]
  have hd : (partCount p:ℝ)-1 ≤ n := by
    have hh : (partCount p:ℝ) ≤ n := by exact_mod_cast (show partCount p ≤ n by simpa using partCount_le_card p)
    linarith only [hh]
  have hκ : 0 < continuationBaseline m := (continuation_parameters m).1
  have hcap : 0 ≤ capacity H.left H.right
      ((auxiliaryPoint H (continuationBaseline m)).capacities (continuationBaseline m) u) p := by
    apply sum_nonneg
    intro e _
    apply mul_nonneg _ (crossingIndicator_nonneg _ _ _)
    unfold StepFree.capacities
    split_ifs
    · change 0 ≤ continuationBaseline m/2
      positivity
    · exact hκ.le
  have hm : (m:ℝ) ≤ graphSize n m := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hnP : (n:ℝ) ≤ graphSize n m := by unfold graphSize; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hh : q*((partCount p:ℝ)-1) ≤ (graphSize n m)^2 := by
    calc
      _ ≤ (m:ℝ)*n := mul_le_mul hq hd hd0 (Nat.cast_nonneg m)
      _ ≤ graphSize n m*graphSize n m := mul_le_mul hm hnP (Nat.cast_nonneg n) graphSize_pos.le
      _ = _ := (pow_two _).symm
  unfold slack
  linarith only [hcap,hh]

lemma mixing_numbers {P β : ℝ} (hP : 5 ≤ P) (hmP : (m:ℝ) ≤ P)
    (hβ : P⁻¹/32 ≤ β) :
    0 < P^(-8:ℤ) ∧ P^(-8:ℤ) ≤ 1 ∧
    β/2 ≤ (1-P^(-8:ℤ))*β-P^(-8:ℤ)*P^2 ∧
    P^(-30:ℤ) ≤ P^(-8:ℤ)*P^(-20:ℤ) ∧
    (m:ℝ)*P^(-30:ℤ) ≤ β/2 := by
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hβ0 : 0 ≤ β := (by positivity : 0 ≤ P⁻¹/32).trans hβ
  have hθ0 : 0 < P^(-8:ℤ) := zpow_pos hP0 _
  have h4 : (4:ℝ) ≤ P^8 := (by linarith : (4:ℝ) ≤ P).trans
    (by simpa using pow_le_pow_right₀ hP1 (by norm_num : 1 ≤ 8))
  have hθ4 : 4*P^(-8:ℤ) ≤ 1 := by
    simpa using scaled_inverse_power hP0 0 8 h4
  have h128 : (128:ℝ) ≤ P^5 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 5) hP 5
    norm_num at hh
    linarith only [hh]
  have he : 128*P^(-6:ℤ) ≤ P⁻¹ := by
    simpa using scaled_inverse_power hP0 1 5 h128
  have hθP : P^(-8:ℤ)*P^2=P^(-6:ℤ) := by
    rw [←zpow_natCast,←zpow_add₀ (ne_of_gt hP0)]
    norm_num
  have hθβ := mul_le_mul_of_nonneg_right hθ4 hβ0
  have hmδ : (m:ℝ)*P^(-30:ℤ) ≤ P^(-6:ℤ) := by
    calc
      _ ≤ P*P^(-30:ℤ) := mul_le_mul_of_nonneg_right hmP (zpow_pos hP0 _).le
      _ = P^(-29:ℤ) := by simpa using (zpow_add₀ (ne_of_gt hP0) 1 (-30)).symm
      _ ≤ _ := inverse_power_mono hP1 (by norm_num : 6 ≤ 29)
  refine ⟨hθ0,by linarith only [hθ4],?_,?_,?_⟩
  · rw [hθP]
    nlinarith only [hθβ,he,hβ]
  · rw [←zpow_add₀ (ne_of_gt hP0)]
    norm_num only [show (-8:ℤ)+(-20) = -28 by norm_num]
    exact inverse_power_mono hP1 (by norm_num : 28 ≤ 30)
  · linarith only [hmδ,he,hβ,hβ0]

theorem step_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    {s q β : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : q ≤ m) (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (q+β) u) :
    let θ := (graphSize n m)^(-8:ℤ)
    let c := (1-θ) • z+θ • auxiliaryPoint H (continuationBaseline m)
    ∀x, x.Close c ((graphSize n m)^(-30:ℤ)) →
      x ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) q u := by
  have : Nonempty (Fin n) := ⟨⟨0,by omega⟩⟩
  let P := graphSize n m
  let θ := P^(-8:ℤ)
  let aux := auxiliaryPoint H (continuationBaseline m)
  let c := (1-θ) • z+θ • aux
  have hP := connected_size_five H hn hconn
  have hmP : (m:ℝ) ≤ P := by dsimp [P,graphSize] <;> linarith [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨hθ,hθ1,hmix,hδ,hpert⟩ := mixing_numbers hP hmP hβ
  have hβ0 : 0 ≤ β := (div_nonneg (inv_nonneg.mpr (graphSize_pos (n:=n) (m:=m)).le) (by norm_num) : 0 ≤ (graphSize n m)⁻¹/32).trans hβ
  change ∀x : StepFree n m, x.Close c (P^(-30:ℤ)) → _
  intro x hx
  refine ⟨?_,fun p => ?_⟩
  · apply convex_innerCube (stepCore H s (continuationBaseline m) (continuationStep m) u)
      (stepCore_convex H _ _ _ u) z aux hz.1 hθ hθ1 _ (hx.mono hδ)
    intro w hw
    exact auxiliary_cube H hn hconn hs hsP u hu0 hw
  · by_cases hp : p=⊤
    · subst p
      rw [slack_top]
    have hd : 1 ≤ (partCount p:ℝ)-1 := by
      have hh : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount hp
      linarith only [hh]
    have hzβ : β ≤ slack H.left H.right (z.capacities (continuationBaseline m) u) q p := by
      have hz' := hz.2 p
      have he := slack_change_target H.left H.right (z.capacities (continuationBaseline m) u) (q+β) β p
      rw [add_sub_cancel_right] at he
      have hdβ := mul_le_mul_of_nonneg_left hd hβ0
      rw [he]
      nlinarith only [hz',hdβ]
    have haux := auxiliary_slack H (by omega) u hq p
    have hc : β/2 ≤ slack H.left H.right (c.capacities (continuationBaseline m) u) q p := by
      dsimp only [c]
      rw [StepFree.capacities_combo _ (1-θ) θ (by ring),slack_combo _ _ _ _ q _ _ (by ring)]
      have hh := add_le_add (mul_le_mul_of_nonneg_left hzβ (sub_nonneg.mpr hθ1))
        (mul_le_mul_of_nonneg_left haux hθ.le)
      change (1-θ)*β+θ*(-P^2) ≤ _ at hh
      exact hmix.trans (by nlinarith only [hh])
    have hp' := (abs_le.mp (hx.slack H (zpow_pos graphSize_pos _).le
      (continuationBaseline m) q u p)).1
    linarith only [hc,hp',hpert]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Grid
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation grid. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

namespace StepFree

lemma canonical_matrix (x : StepFree n m) (hn : 0 < n) :
    x.canonical.matrix=x.matrix :=
  responseMatrix_fixed (responseMatrix_hermitian x.1) (responseMatrix_ones hn x.1)

lemma canonical_core (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepCore H s κ t u) : x.canonical ∈ stepCore H s κ t u := by
  simpa only [stepCore,Set.mem_ofPred_eq,lowerPencil,upperPencil,edgePencil,
    canonical_matrix x hn,
    show x.canonical.multiplier=x.multiplier from rfl,
    show x.canonical.y=x.y from rfl,show x.canonical.z=x.z from rfl] using hx

lemma canonical_feasible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t q : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepFeasible H s κ t q u) : x.canonical ∈ stepFeasible H s κ t q u :=
  ⟨canonical_core H hn hx.1,hx.2⟩

lemma Bounded.combo {x z : StepFree n m} {R a b : ℝ}
    (hx : x.Bounded R) (hz : z.Bounded R) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    (a • x+b • z).Bounded R := by
  have he (v w : ℝ) (hv : |v| ≤ R) (hw : |w| ≤ R) : |a*v+b*w| ≤ R := by
    calc
      _ ≤ |a*v|+|b*w| := abs_add_le _ _
      _ = a*|v|+b*|w| := by rw [abs_mul,abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ a*R+b*R := add_le_add (mul_le_mul_of_nonneg_left hv ha) (mul_le_mul_of_nonneg_left hw hb)
      _ = R := by rw [←add_mul,hab,one_mul]
  exact ⟨fun i j => he _ _ (hx.1 i j) (hz.1 i j),
    fun ijk => he _ _ (hx.2.1 ijk) (hz.2.1 ijk),
    fun e => he _ _ (hx.2.2.1 e) (hz.2.2.1 e),
    fun e => he _ _ (hx.2.2.2 e) (hz.2.2.2 e)⟩

lemma canonical_bound (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hκ : κ ≤ 1)
    (hx : x ∈ stepCore H s κ t u) : x.canonical.Bounded (6*graphSize n m) := by
  have hd := stepCore_domain H hn hx
  have hp := domain_psd H hd
  have ht := domain_trace_size H hn hd
  have hmP : (m:ℝ) ≤ graphSize n m := by
    unfold graphSize
    linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hP : 2 ≤ graphSize n m := by
    unfold graphSize
    linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
  have h6 : 0 ≤ (6:ℝ)*m := by positivity
  have hdiag (i : Fin n) : x.matrix i i ≤ 6*m :=
    (single_le_sum (fun j _ => hp.diag_nonneg (i:=j)) (mem_univ i)).trans ht
  refine ⟨fun i j => (psd_entry_bound hp h6 hdiag i j).trans (by linarith only [hmP]),?_,?_,?_⟩
  · intro ijk
    change |x.multiplier ijk| ≤ _
    rw [abs_of_nonneg (hx.2.2.1 ijk)]
    have hsum := domain_multiplier_bound H hp x.multiplier hx.2.1
    have hle := single_le_sum (fun j _ => hx.2.2.1 j) (mem_univ ijk)
    linarith only [hle,hsum,hmP,graphSize_pos (n:=n) (m:=m)]
  · intro e
    change |x.y e| ≤ _
    rw [abs_of_nonneg (hx.2.2.2.1 e).1]
    linarith only [(hx.2.2.2.1 e).2,hP]
  · intro e
    change |x.z e| ≤ _
    rw [abs_of_nonneg (hx.2.2.2.2.1 e).1]
    linarith only [(hx.2.2.2.2.1 e).2,hκ,hP]

end StepFree

lemma auxiliaryPoint_canonical (H : MultiGraph n m) (_hn : 0 < n) (κ : ℝ) :
    (auxiliaryPoint H κ).canonical=auxiliaryPoint H κ := by
  change ((auxiliaryPoint H κ).matrix,(auxiliaryPoint H κ).2)=((auxiliaryPoint H κ).1,(auxiliaryPoint H κ).2)
  rw [auxiliaryPoint_matrix]
  rfl

lemma baseline_le_one : continuationBaseline m ≤ 1 := by
  unfold continuationBaseline
  exact (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) m])

theorem bounded_step_inner_cube (H : MultiGraph n m) (hn : 2 ≤ n) (hconn : H.Connected univ)
    {s q β : ℝ} (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : q ≤ m) (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu0 : ∀e, 0 ≤ u e)
    {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (q+β) u) :
    ∃c : StepFree n m, c.Bounded (6*graphSize n m) ∧
      ∀x, x.Close c ((graphSize n m)^(-30:ℤ)) →
        x ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) q u := by
  have hn0 : 0 < n := by omega
  let θ := (graphSize n m)^(-8:ℤ)
  let aux := auxiliaryPoint H (continuationBaseline m)
  have hθ : 0 ≤ θ := (zpow_pos graphSize_pos _).le
  have hθ1 : θ ≤ 1 := by
    have hP : 1 ≤ graphSize n m := by
      unfold graphSize
      linarith [Nat.cast_nonneg (α:=ℝ) n,Nat.cast_nonneg (α:=ℝ) m]
    exact (inverse_power_mono hP (by norm_num : 0 ≤ 8)).trans_eq (by simp)
  have ha : aux ∈ stepCore H s (continuationBaseline m) (continuationStep m) u :=
    auxiliary_cube H hn hconn hs hsP u hu0 (StepFree.Close.refl aux (zpow_pos graphSize_pos _).le)
  have hab := StepFree.canonical_bound H hn0 baseline_le_one ha
  rw [auxiliaryPoint_canonical H hn0] at hab
  refine ⟨(1-θ) • z.canonical+θ • aux,?_,?_⟩
  · exact (StepFree.canonical_bound H hn0 baseline_le_one hz.1).combo hab
      (sub_nonneg.mpr hθ1) hθ (by ring)
  · exact step_inner_cube H hn hconn hs hsP hq hβ u hu0 (z.canonical_feasible H hn0 hz)

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedOrientation
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

lemma reachable (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.Connected T)
    (v root : Fin n) : (adjacency G T).Reachable v root := by
  let S : Finset (Fin n) := univ.filter (fun w => (adjacency G T).Reachable w root)
  have hr : root ∈ S := by simp only [S,mem_filter,mem_univ,true_and]; exact .refl root
  by_contra hv
  have hv' : v ∉ S := by simpa only [S,mem_filter,mem_univ,true_and] using hv
  have hSne : S ≠ univ := by intro he; exact hv' (he ▸ mem_univ v)
  obtain ⟨e,he⟩ := hT S ⟨root,hr⟩ hSne
  obtain ⟨heT,hecut⟩ := mem_filter.mp he
  have hadj : (adjacency G T).Adj (G.left e) (G.right e) := ⟨e,heT,Or.inl ⟨rfl,rfl⟩⟩
  rcases hecut with ⟨hl,hr⟩ | ⟨hr,hl⟩
  · have h := hadj.reachable.symm.trans ((mem_filter.mp hl).2)
    exact hr (mem_filter.mpr ⟨mem_univ _,h⟩)
  · have h := hadj.reachable.trans ((mem_filter.mp hr).2)
    exact hl (mem_filter.mpr ⟨mem_univ _,h⟩)

lemma parent_exists (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.Connected T)
    (root : Fin n) (v : Fin n) (hv : v ≠ root) :
    ∃e ∈ T,
      (G.left e=v ∧ (adjacency G T).dist (G.right e) root < (adjacency G T).dist v root) ∨
      (G.right e=v ∧ (adjacency G T).dist (G.left e) root < (adjacency G T).dist v root) := by
  obtain ⟨p,hp⟩ := (reachable G hT v root).exists_walk_length_eq_dist
  cases p with
  | nil => exact (hv rfl).elim
  | @cons v w root h p =>
    obtain ⟨e,he,h|h⟩ := h
    · refine ⟨e,he,Or.inl ⟨h.1,?_⟩⟩
      rw [h.2]
      exact lt_of_le_of_lt (SimpleGraph.dist_le p) (by simpa using hp.symm ▸ Nat.lt_succ_self p.length)
    · refine ⟨e,he,Or.inr ⟨h.1,?_⟩⟩
      rw [h.2]
      exact lt_of_le_of_lt (SimpleGraph.dist_le p) (by simpa using hp.symm ▸ Nat.lt_succ_self p.length)

lemma rooted_exists (G : MultiGraph n m) {T : Finset (Fin m)} (hT : G.SpanningTree T)
    (root : Fin n) : Nonempty (Rooted G T root) := by
  choose f hf using fun v : {v : Fin n // v ≠ root} => parent_exists G hT.1 root v v.property
  let F : {v : Fin n // v ≠ root} → T := fun v => ⟨f v,(hf v).1⟩
  have hi : Function.Injective F := by
    intro v w he
    have he' : f v=f w := congrArg Subtype.val he
    obtain hvl|hvr := (hf v).2
    obtain hwl|hwr := (hf w).2
    · apply Subtype.ext
      exact hvl.1.symm.trans (he' ▸ hwl.1)
    · have h1 := hvl.2
      have h2 := hwr.2
      rw [he',hwr.1] at h1
      rw [←he',hvl.1] at h2
      omega
    obtain hwl|hwr := (hf w).2
    · have h1 := hvr.2
      have h2 := hwl.2
      rw [he',hwl.1] at h1
      rw [←he',hvr.1] at h2
      omega
    · apply Subtype.ext
      exact hvr.1.symm.trans (he' ▸ hwr.1)
  have hc : Fintype.card {v : Fin n // v ≠ root}=Fintype.card T := by
    rw [Fintype.card_subtype_compl,Fintype.card_fin,Fintype.card_subtype_eq root,
      Fintype.card_coe,G.spanningTree_card (Fin.pos root) hT]
  let E := Equiv.ofBijective F ⟨hi,(Fintype.bijective_iff_injective_and_card F).mpr ⟨hi,hc⟩ |>.2⟩
  refine ⟨⟨E.symm,fun e => ?_⟩⟩
  have he : f (E.symm e)=e := congrArg Subtype.val (E.apply_symm_apply e)
  obtain h|h := (hf (E.symm e)).2
  · exact Or.inl (h.1.symm.trans (congrArg G.left he))
  · exact Or.inr (h.1.symm.trans (congrArg G.right he))

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedFlow
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted flow. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical
variable {n m : ℕ}

lemma Rooted.leftFlow_nonneg {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : 0 ≤ R.leftFlow e := by
  unfold Rooted.leftFlow
  split_ifs <;> norm_num

lemma Rooted.rightFlow_nonneg {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) : 0 ≤ R.rightFlow e := by
  unfold Rooted.rightFlow
  split_ifs <;> norm_num

lemma Rooted.edgeFlow {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) :
    R.leftFlow e+R.rightFlow e=if e ∈ T then 1 else 0 := by
  by_cases he : e ∈ T
  · obtain hl|hr := R.endpoint ⟨e,he⟩
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.right e := by rw [hl]; exact G.loopless e
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hl,G.loopless e]
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.left e := by rw [hr]; exact (G.loopless e).symm
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hr,(G.loopless e).symm]
  · simp [Rooted.leftFlow,Rooted.rightFlow,he]

lemma Rooted.arc_at {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (e : Fin m) (v : Fin n) :
    (if G.left e=v then R.leftFlow e else 0)+(if G.right e=v then R.rightFlow e else 0)=
      if he : e ∈ T then if (R.tail ⟨e,he⟩).val=v then 1 else 0 else 0 := by
  by_cases he : e ∈ T
  · obtain hl|hr := R.endpoint ⟨e,he⟩
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.right e := by rw [hl]; exact G.loopless e
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hl,G.loopless e]
    · have hnot : (R.tail ⟨e,he⟩).val ≠ G.left e := by rw [hr]; exact (G.loopless e).symm
      simp [Rooted.leftFlow,Rooted.rightFlow,he,hr,(G.loopless e).symm]
  · simp [Rooted.leftFlow,Rooted.rightFlow,he]

lemma Rooted.out_eq {G : MultiGraph n m} {T : Finset (Fin m)} {root : Fin n}
    (R : Rooted G T root) (v : Fin n) :
    out G R.leftFlow R.rightFlow v=if v=root then 0 else 1 := by
  simp only [out,R.arc_at]
  by_cases hv : v=root
  · subst v
    simp only [ite_true, if_true]
    apply sum_eq_zero
    intro e he
    by_cases h : e ∈ T
    · simp only [dite_eq_left h,ite_eq_right (R.tail ⟨e,h⟩).property]
    · simp [h]
  · rw [ite_eq_right hv]
    let f : T := R.tail.symm ⟨v,hv⟩
    have hf : (R.tail f).val=v := congrArg Subtype.val (R.tail.apply_symm_apply ⟨v,hv⟩)
    rw [sum_eq_single f.val]
    · simp only [dite_eq_left f.property,hf,ite_true, if_true]
    · intro e he hef
      by_cases h : e ∈ T
      · rw [dite_eq_left h]
        apply ite_eq_right
        intro hv'
        apply hef
        exact congrArg Subtype.val (R.tail.injective (Subtype.ext (hv'.trans hf.symm)))
      · simp [h]
    · simp

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_FractionalOrientation
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_x
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional orientation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma out_sum {I : Type*} [Fintype I] (G : MultiGraph n m)
    (a b : I → Fin m → ℝ) (v : Fin n) :
    out G (fun e => ∑i, a i e) (fun e => ∑i, b i e) v = ∑i, out G (a i) (b i) v := by
  simp only [out]
  rw [sum_comm]
  apply sum_congr rfl
  intro e he
  rw [sum_add_distrib]
  have hi (p : Prop) [Decidable p] (f : I → ℝ) : (if p then ∑i, f i else 0)=∑i, if p then f i else 0 := by
    split_ifs <;> simp
  rw [hi,hi]

lemma out_scale (G : MultiGraph n m) (a b : Fin m → ℝ) (α : ℝ) (v : Fin n) :
    out G (fun e => α*a e) (fun e => α*b e) v=α*out G a b v := by
  simp only [out,mul_sum,mul_add]
  apply sum_congr rfl
  intro e he
  split_ifs <;> ring

lemma FlowPoint.Exact.scale {G : MultiGraph n m} {c : Fin m → ℝ} {q : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) {α : ℝ} (hα : 0 ≤ α) :
    (FlowPoint.mk (fun e => α*F.x e) (fun r e => α*F.a r e) (fun r e => α*F.b r e)).Exact
      G (fun e => α*c e) (α*q) := by
  refine ⟨fun e => ⟨mul_nonneg hα (hF.1 e).1,mul_le_mul_of_nonneg_left (hF.1 e).2 hα⟩,
    fun r e => ⟨mul_nonneg hα (hF.2.1 r e).1,mul_nonneg hα (hF.2.1 r e).2.1,?_⟩,?_,?_⟩
  · simp only [(hF.2.1 r e).2.2,mul_add]
  · intro r v
    rw [out_scale,hF.2.2.1]
    split_ifs <;> simp
  · change (∑e, α*F.x e)=_
    rw [←mul_sum,hF.2.2.2]
    ring

lemma FlowPoint.Exact.mono {G : MultiGraph n m} {c d : Fin m → ℝ} {q : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) (hcd : ∀e, c e ≤ d e) : F.Exact G d q :=
  ⟨fun e => ⟨(hF.1 e).1, (hF.1 e).2.trans (hcd e)⟩,hF.2⟩

lemma packed_exact_flow (G : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hpack : G.TreePackable univ r) :
    ∃F : FlowPoint n m, F.Exact G (fun _ => 1) r := by
  obtain ⟨T,hT,hdis⟩ := hpack
  let R (root : Fin n) (i : Fin r) : Rooted G (T i) root := Classical.choice (rooted_exists G (hT i).2 root)
  let F : FlowPoint n m := ⟨fun e => ∑i, if e ∈ T i then 1 else 0,
    fun root e => ∑i, (R root i).leftFlow e,
    fun root e => ∑i, (R root i).rightFlow e⟩
  refine ⟨F,?_,?_,?_,?_⟩
  · intro e
    constructor
    · change 0 ≤ ∑i : Fin r, if e ∈ T i then (1:ℝ) else 0
      exact sum_nonneg fun i _ => by split_ifs <;> norm_num
    · change (∑i, if e ∈ T i then (1:ℝ) else 0) ≤ 1
      rw [sum_boole]
      norm_cast
      apply card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have h := disjoint_left.mp (hdis hij)
      exact h (mem_filter.mp hi).2 (mem_filter.mp hj).2
  · intro root e
    change 0 ≤ (∑i, (R root i).leftFlow e) ∧
      0 ≤ (∑i, (R root i).rightFlow e) ∧ _
    refine ⟨sum_nonneg fun i _ => (R root i).leftFlow_nonneg e,
      sum_nonneg fun i _ => (R root i).rightFlow_nonneg e,?_⟩
    change (∑i, if e ∈ T i then (1:ℝ) else 0)=(∑i, (R root i).leftFlow e)+(∑i, (R root i).rightFlow e)
    rw [←sum_add_distrib]
    exact sum_congr rfl fun i _ => ((R root i).edgeFlow e).symm
  · intro root v
    change out G (fun e => ∑i, (R root i).leftFlow e) (fun e => ∑i, (R root i).rightFlow e) v=_
    rw [out_sum]
    simp only [Rooted.out_eq]
    split_ifs <;> simp
  · change (∑e, ∑i, if e ∈ T i then (1:ℝ) else 0)=(r:ℝ)*((n:ℝ)-1)
    rw [sum_comm]
    have hs (i : Fin r) : (∑e, if e ∈ T i then (1:ℝ) else 0)=(n:ℝ)-1 := by
      rw [sum_boole,filter_mem_eq_inter,univ_inter,G.spanningTree_card hn (hT i).2]
      rw [Nat.cast_sub (show 1 ≤ n by omega),Nat.cast_one]
    simp only [hs,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]

lemma out_push {M : ℕ} (G : MultiGraph n m) (H : MultiGraph n M) (π : Fin M → Fin m)
    (hl : ∀e, G.left (π e)=H.left e) (hr : ∀e, G.right (π e)=H.right e)
    (F : FlowPoint n M) (root v : Fin n) :
    out G ((F.push π).a root) ((F.push π).b root) v=out H (F.a root) (F.b root) v := by
  have hi (p : Prop) [Decidable p] (s : Finset (Fin M)) (a : Fin M → ℝ) :
      (if p then ∑f ∈ s, a f else 0)=∑f ∈ s, if p then a f else 0 := by
    split_ifs <;> simp
  simp only [out,FlowPoint.push,hi,←sum_add_distrib]
  trans ∑e : Fin m, ∑f ∈ univ.filter (fun f => π f=e),
    ((if H.left f=v then F.a root f else 0)+(if H.right f=v then F.b root f else 0))
  · apply sum_congr rfl
    intro e he
    apply sum_congr rfl
    intro f hf
    have hfe := (mem_filter.mp hf).2
    rw [←hfe,hl,hr]
  · exact sum_fiberwise_of_maps_to (fun e _ => mem_univ (π e)) _

lemma FlowPoint.Exact.push {M : ℕ} (G : MultiGraph n m) (H : MultiGraph n M) (π : Fin M → Fin m)
    (hl : ∀e, G.left (π e)=H.left e) (hr : ∀e, G.right (π e)=H.right e)
    {c : Fin M → ℝ} {q : ℝ} {F : FlowPoint n M} (hF : F.Exact H c q) :
    (F.push π).Exact G (fun e => ∑f ∈ univ.filter (fun f => π f=e), c f) q := by
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    change 0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.x f) ∧
      (∑f ∈ univ.filter (fun f => π f=e), F.x f) ≤ (∑f ∈ univ.filter (fun f => π f=e), c f)
    exact ⟨sum_nonneg fun f _ => (hF.1 f).1,sum_le_sum fun f _ => (hF.1 f).2⟩
  · intro r e
    change 0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.a r f) ∧
      0 ≤ (∑f ∈ univ.filter (fun f => π f=e), F.b r f) ∧ _
    refine ⟨sum_nonneg fun f _ => (hF.2.1 r f).1,
      sum_nonneg fun f _ => (hF.2.1 r f).2.1,?_⟩
    change (∑f ∈ univ.filter (fun f => π f=e), F.x f)=_
    simp only [FlowPoint.push,←sum_add_distrib]
    exact sum_congr rfl fun f _ => (hF.2.1 r f).2.2
  · intro r v
    rw [out_push G H π hl hr]
    exact hF.2.2.1 r v
  · change (∑e, ∑f ∈ univ.filter (fun f => π f=e), F.x f)=_
    rw [sum_fiberwise_of_maps_to (fun f _ => mem_univ (π f)),hF.2.2.2]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_ParallelCopies
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Parallel copies. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma sum_copies (a : Fin m → ℕ) (f : Fin m → ℝ) :
    (∑j : Fin (Fintype.card (Copy a)), f (copyProjection a j))=∑e, (a e:ℝ)*f e := by
  rw [←(copyEquiv a).sum_comp]
  simp [copyProjection,Fintype.sum_sigma,nsmul_eq_mul]

lemma fiber_copies (a : Fin m → ℕ) (e : Fin m) :
    (∑_copy ∈ univ.filter (fun f => copyProjection a f=e), (1:ℝ))=a e := by
  rw [sum_filter]
  simpa using sum_copies a (fun e' => if e'=e then (1:ℝ) else 0)

lemma capacity_unit (G : MultiGraph n m) (p : Setoid (Fin n)) :
    capacity G.left G.right (fun _ => 1) p=(Partitions.crossing G p).card := by
  rw [capacity_eq_sum]
  simp

lemma capacity_copies (G : MultiGraph n m) (a : Fin m → ℕ) (p : Setoid (Fin n)) :
    ((Partitions.crossing (copies G a) p).card:ℝ)=
      capacity G.left G.right (fun e => a e) p := by
  rw [←capacity_unit]
  simp only [capacity,one_mul,copies]
  exact sum_copies a (fun e => crossingIndicator p (G.left e) (G.right e))

lemma partCount_ker (p : Fin n → Fin n) : partCount (Setoid.ker p)=partitionSize p := by
  let f : Quotient (Setoid.ker p) → (univ.image p : Finset (Fin n)) :=
    Quotient.lift (fun v => ⟨p v,mem_image.mpr ⟨v,mem_univ _,rfl⟩⟩)
      (fun a b h => Subtype.ext h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a,b using Quotient.inductionOn₂ with
      | h a b =>
        intro he
        exact Quotient.sound (congrArg Subtype.val he)
    · intro A
      obtain ⟨v,_,hv⟩ := mem_image.mp A.property
      exact ⟨Quotient.mk (Setoid.ker p) v,Subtype.ext hv⟩
  exact (Fintype.card_congr (Equiv.ofBijective f hf)).trans (Fintype.card_coe _)

lemma crossing_ker (G : MultiGraph n m) (p : Fin n → Fin n) :
    Partitions.crossing G (Setoid.ker p)=G.crossing univ p := by
  ext e
  simp [Partitions.crossing,MultiGraph.crossing]

lemma packing_of_partitions (G : MultiGraph n m) (hn : 0 < n) {r : ℕ} (hr : 0 < r)
    (hp : ∀p : Setoid (Fin n), (r:ℝ)*((partCount p:ℝ)-1) ≤
      capacity G.left G.right (fun _ => 1) p) : G.TreePackable univ r := by
  apply G.partition_criterion_sufficient univ hr hn
  intro p
  have h := hp (Setoid.ker p)
  rw [capacity_unit,crossing_ker,partCount_ker] at h
  have hp0 : 1 ≤ partitionSize p := by
    apply card_pos.mpr
    exact ⟨p ⟨0,hn⟩,mem_image.mpr ⟨⟨0,hn⟩,mem_univ _,rfl⟩⟩
  have he : ((r*(partitionSize p-1):ℕ):ℝ)=(r:ℝ)*((partitionSize p:ℝ)-1) := by
    rw [Nat.cast_mul,Nat.cast_sub hp0,Nat.cast_one]
  exact_mod_cast (show ((r*(partitionSize p-1):ℕ):ℝ) ≤ (G.crossing univ p).card by rwa [he])

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_FractionalPackingMargin
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_x
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fractional packing margin. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma partCount_le_vertices (p : Setoid (Fin n)) : partCount p ≤ n := by
  simpa [partCount] using Fintype.card_le_of_surjective (Quotient.mk p) Quotient.mk_surjective

lemma floor_capacity_lower (G : MultiGraph n m) (c : Fin m → ℝ) (N : ℕ)
    (p : Setoid (Fin n)) :
    (N:ℝ)*capacity G.left G.right c p-m ≤
      capacity G.left G.right (fun e => (⌊(N:ℝ)*c e⌋₊:ℕ)) p := by
  rw [capacity_eq_sum,capacity_eq_sum]
  have h := sum_le_sum (s:=Partitions.crossing G p) (fun e _ =>
    show (N:ℝ)*c e-1 ≤ (⌊(N:ℝ)*c e⌋₊:ℕ) by linarith [Nat.lt_floor_add_one ((N:ℝ)*c e)])
  simp only [sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at h
  have hc : (Partitions.crossing G p).card ≤ m :=
    (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin m))
  have hc' : ((Partitions.crossing G p).card:ℝ) ≤ m := by exact_mod_cast hc
  linarith only [h,hc']

lemma FlowPoint.zero_exact (G : MultiGraph n m) {c : Fin m → ℝ} (hc : ∀e, 0 ≤ c e) :
    (FlowPoint.mk (fun _ => 0) (fun _ _ => 0) (fun _ _ => 0)).Exact G c 0 := by
  simp [FlowPoint.Exact,out,hc]

theorem exact_flow_of_margin (G : MultiGraph n m) (hn : 0 < n)
    (c : Fin m → ℝ) (hc : ∀e, 0 ≤ c e) {q δ : ℝ} (hq : 0 ≤ q) (hδ : 0 < δ)
    (hp : ∀p : Setoid (Fin n), (q+δ)*((partCount p:ℝ)-1) ≤ capacity G.left G.right c p) :
    ∃F : FlowPoint n m, F.Exact G c q := by
  rcases eq_or_lt_of_le hq with hq0|hq0
  · subst q
    exact ⟨_,FlowPoint.zero_exact G hc⟩
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  obtain ⟨N,hN⟩ := exists_nat_gt (((m:ℝ)+n+1)/δ)
  have hNδ : (m:ℝ)+n+1 < (N:ℝ)*δ := (div_lt_iff₀ hδ).mp hN
  have hN0 : 0 < (N:ℝ) := by
    by_contra h
    have hh : (N:ℝ)*δ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt h) hδ.le
    have hm0 : (0:ℝ) ≤ m := Nat.cast_nonneg m
    have hn0 : (0:ℝ) ≤ n := Nat.cast_nonneg n
    linarith only [hh,hNδ,hm0,hn0]
  let a : Fin m → ℕ := fun e => ⌊(N:ℝ)*c e⌋₊
  let r : ℕ := ⌈(N:ℝ)*q⌉₊
  have hrlo : (N:ℝ)*q ≤ r := Nat.le_ceil _
  have hrhi : (r:ℝ) ≤ (N:ℝ)*q+1 := (Nat.ceil_lt_add_one (mul_nonneg hN0.le hq)).le
  have hrpos : 0 < (r:ℝ) := (mul_pos hN0 hq0).trans_le hrlo
  have hr : 0 < r := by exact_mod_cast hrpos
  have hpack : (copies G a).TreePackable univ r := by
    apply packing_of_partitions _ hn hr
    intro p
    by_cases htop : p=⊤
    · subst p
      simp [capacity,crossingIndicator,partCount_top]
    · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
      have hdhi : (partCount p:ℝ) ≤ n := by exact_mod_cast partCount_le_vertices p
      rw [capacity_unit,capacity_copies]
      have hf := floor_capacity_lower G c N p
      have hpN := mul_le_mul_of_nonneg_left (hp p) hN0.le
      have hround := mul_le_mul_of_nonneg_right hrhi (show 0 ≤ (partCount p:ℝ)-1 by linarith)
      have hδgain := mul_le_mul_of_nonneg_left (show 1 ≤ (partCount p:ℝ)-1 by linarith)
        (mul_nonneg hN0.le hδ.le)
      change (r:ℝ)*((partCount p:ℝ)-1) ≤ capacity G.left G.right (fun e => (a e:ℝ)) p
      change (N:ℝ)*capacity G.left G.right c p-m ≤
        capacity G.left G.right (fun e => (a e:ℝ)) p at hf
      nlinarith only [hf,hpN,hround,hδgain,hNδ,hdhi]
  obtain ⟨F,hF⟩ := packed_exact_flow (copies G a) hn hpack
  have hpush := hF.push G (copies G a) (copyProjection a) (fun _ => rfl) (fun _ => rfl)
  simp only [fiber_copies] at hpush
  have hs := hpush.scale (div_nonneg hq hrpos.le)
  rw [div_mul_cancel₀ q (ne_of_gt hrpos)] at hs
  refine ⟨_,hs.mono fun e => ?_⟩
  have ha : (a e:ℝ) ≤ (N:ℝ)*c e := Nat.floor_le (mul_nonneg hN0.le (hc e))
  have hα : q/(r:ℝ)*N ≤ 1 := by
    rw [div_mul_eq_mul_div,div_le_one hrpos]
    simpa [mul_comm] using hrlo
  calc
    _ ≤ (q/(r:ℝ))*((N:ℝ)*c e) := mul_le_mul_of_nonneg_left ha (div_nonneg hq hrpos.le)
    _ = ((q/(r:ℝ))*N)*c e := by ring
    _ ≤ c e := by simpa using mul_le_mul_of_nonneg_right hα (hc e)

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_Interior
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_x
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Flow interior. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

namespace FlowPoint

lemma Exact.bump_bound {G : MultiGraph n m} {c : Fin m → ℝ} {q R γ : ℝ}
    {F : FlowPoint n m} (hF : F.Exact G c q) (hc : ∀e, c e ≤ R) (hγ : 0 ≤ γ) :
    (F.bump γ).Bounded (R+γ) := by
  refine ⟨?_,?_,?_⟩
  · intro e
    change |F.x e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.1 e).1 hγ)]
    linarith only [(hF.1 e).2, hc e]
  · intro r e
    change |F.a r e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.2.1 r e).1 hγ)]
    have h := (hF.2.1 r e).2.2
    linarith only [h,(hF.2.1 r e).2.1,(hF.1 e).2,hc e]
  · intro r e
    change |F.b r e+γ| ≤ _
    rw [abs_of_nonneg (add_nonneg (hF.2.1 r e).2.1 hγ)]
    have h := (hF.2.1 r e).2.2
    linarith only [h,(hF.2.1 r e).1,(hF.1 e).2,hc e]

end FlowPoint

lemma out_perturb_upper (G : MultiGraph n m) {a b a' b' : Fin m → ℝ} {σ : ℝ}
    (hσ : 0 ≤ σ) (ha : ∀e, a' e ≤ a e+σ) (hb : ∀e, b' e ≤ b e+σ) (v : Fin n) :
    out G a' b' v ≤ out G a b v+2*m*σ := by
  have hi (e : Fin m) :
      (if G.left e=v then a' e else 0)+(if G.right e=v then b' e else 0) ≤
        (if G.left e=v then a e else 0)+(if G.right e=v then b e else 0)+2*σ := by
    split_ifs <;> linarith only [ha e,hb e,hσ]
  have h := sum_le_sum (s:=univ) fun e _ => hi e
  simpa only [out,sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    mul_comm (m:ℝ),mul_assoc] using h

lemma exact_bump_cube (G : MultiGraph n m) {c : Fin m → ℝ} {qbar ε α γ : ℝ}
    (hγ : 0 < γ) (hα : 0 ≤ α) (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε)
    (hmγ : 4*m*γ ≤ α) {F : FlowPoint n m}
    (hF : F.Exact G (fun e => c e-2*γ) (qbar-α)) {H : FlowPoint n m}
    (hclose : H.Close (F.bump γ) (γ/4)) : H.Feasible G c qbar ε := by
  have hx (e : Fin m) := abs_le.mp (hclose.1 e)
  have ha (r : Fin n) (e : Fin m) := abs_le.mp (hclose.2.1 r e)
  have hb (r : Fin n) (e : Fin m) := abs_le.mp (hclose.2.2 r e)
  simp only [FlowPoint.bump] at hx ha hb
  have hg : 0 ≤ (m:ℝ)*γ := mul_nonneg (Nat.cast_nonneg _) hγ.le
  refine ⟨?_,?_,?_,?_⟩
  · intro e
    constructor
    · linarith only [(hx e).1,(hF.1 e).1,hγ]
    · linarith only [(hx e).2,(hF.1 e).2,hγ]
  · intro r e
    refine ⟨?_,?_,?_⟩
    · linarith only [(ha r e).1,(hF.2.1 r e).1,hγ]
    · linarith only [(hb r e).1,(hF.2.1 r e).2.1,hγ]
    · linarith only [(hx e).2,(ha r e).1,(hb r e).1,(hF.2.1 r e).2.2,hγ]
  · intro r v
    have ho := out_perturb_upper G (show 0 ≤ γ+γ/4 by linarith)
      (fun e => show H.a r e ≤ F.a r e+(γ+γ/4) by linarith only [(ha r e).2])
      (fun e => show H.b r e ≤ F.b r e+(γ+γ/4) by linarith only [(hb r e).2]) v
    rw [hF.2.2.1] at ho
    split_ifs at ho ⊢ <;> nlinarith only [ho,hmγ,hα,hαε,hg]
  · have hsum : (∑e, F.x e) ≤ ∑e, H.x e := sum_le_sum fun e _ => by
      linarith only [(hx e).1,hγ]
    rw [hF.2.2.2] at hsum
    nlinarith only [hsum,hαn]

lemma capacity_shift_lower (G : MultiGraph n m) (c : Fin m → ℝ) {γ : ℝ}
    (hγ : 0 ≤ γ) (p : Setoid (Fin n)) :
    capacity G.left G.right c p-γ*m ≤ capacity G.left G.right (fun e => c e-γ) p := by
  rw [capacity_eq_sum,capacity_eq_sum]
  simp only [sum_sub_distrib,sum_const,nsmul_eq_mul]
  have hc : (Partitions.crossing G p).card ≤ m :=
    (card_le_card (subset_univ _)).trans_eq (card_univ.trans (Fintype.card_fin m))
  have hc' : ((Partitions.crossing G p).card:ℝ) ≤ m := by exact_mod_cast hc
  nlinarith only [mul_le_mul_of_nonneg_left hc' hγ]

end
end AlgorithmicThinTrees.Orientations

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma exact_bump_cube_vary (G : MultiGraph n m) {c c' : Fin m → ℝ} {qbar ε α γ : ℝ}
    (hγ : 0 < γ) (hα : 0 ≤ α) (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε)
    (hmγ : 4*m*γ ≤ α) {F : FlowPoint n m}
    (hF : F.Exact G (fun e => c e-2*γ) (qbar-α))
    (hc' : ∀e, c e-γ/2 ≤ c' e) {H : FlowPoint n m}
    (hclose : H.Close (F.bump γ) (γ/4)) : H.Feasible G c' qbar ε := by
  have h := exact_bump_cube G hγ hα hαε hαn hmγ hF hclose
  refine ⟨?_,h.2⟩
  intro e
  refine ⟨(h.1 e).1,?_⟩
  have hx := (abs_le.mp (hclose.1 e)).2
  change H.x e-(F.x e+γ) ≤ γ/4 at hx
  linarith only [hx,(hF.1 e).2,hc' e,hγ]

theorem flow_inner_cube_vary (G : MultiGraph n m) (hn : 0 < n) (c : Fin m → ℝ)
    {qbar ε α β γ R : ℝ} (hγ : 0 < γ) (hα : 0 ≤ α) (hq : α ≤ qbar)
    (hαε : α ≤ ε) (hαn : α*((n:ℝ)-1) ≤ ε) (hβ : 0 < β)
    (hmγα : 4*m*γ ≤ α) (hmγβ : 4*m*γ ≤ β)
    (hc : ∀e, 2*γ ≤ c e) (hcR : ∀e, c e ≤ R)
    (hp : ∀p : Setoid (Fin n), (qbar+β)*((partCount p:ℝ)-1) ≤ capacity G.left G.right c p) :
    ∃F : FlowPoint n m, F.Bounded (R+γ) ∧
      ∀(c' : Fin m → ℝ) (H : FlowPoint n m),
        (∀e, c e-γ/2 ≤ c' e) → H.Close F (γ/4) → H.Feasible G c' qbar ε := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hmargin (p : Setoid (Fin n)) :
      (qbar-α+β/2)*((partCount p:ℝ)-1) ≤ capacity G.left G.right (fun e => c e-2*γ) p := by
    by_cases htop : p=⊤
    · subst p
      simp [capacity,crossingIndicator,partCount_top]
    · have hd : (2:ℝ) ≤ partCount p := by exact_mod_cast two_le_partCount htop
      have ha : 0 ≤ α*((partCount p:ℝ)-1) := mul_nonneg hα (by linarith)
      have hb : β ≤ β*((partCount p:ℝ)-1) := by nlinarith only [hd,hβ]
      have hs := capacity_shift_lower G c (show 0 ≤ 2*γ by linarith only [hγ]) p
      nlinarith only [hs,hp p,ha,hb,hmγβ]
  obtain ⟨F,hF⟩ := exact_flow_of_margin G hn (fun e => c e-2*γ)
    (fun e => sub_nonneg.mpr (hc e)) (sub_nonneg.mpr hq) (show 0 < β/2 by linarith) hmargin
  refine ⟨F.bump γ,hF.bump_bound (fun e => ?_) hγ.le,?_⟩
  · linarith only [hcR e,hγ]
  · intro c' H hc' hH
    exact exact_bump_cube_vary G hγ hα hαε hαn hmγα hF hc' hH

lemma FlowPoint.Close.mono {F H : FlowPoint n m} {ρ σ : ℝ}
    (h : F.Close H ρ) (hρσ : ρ ≤ σ) : F.Close H σ :=
  ⟨fun e => (h.1 e).trans hρσ,fun r e => (h.2.1 r e).trans hρσ,
    fun r e => (h.2.2 r e).trans hρσ⟩

lemma FlowPoint.Bounded.mono {F : FlowPoint n m} {R R' : ℝ}
    (h : F.Bounded R) (hRR' : R ≤ R') : F.Bounded R' :=
  ⟨fun e => (h.1 e).trans hRR',fun r e => (h.2.1 r e).trans hRR',
    fun r e => (h.2.2 r e).trans hRR'⟩
end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_FiniteContinuation
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_boundQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_errorQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_radiusQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_sizeQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mat _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.encode_z _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_a _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_b _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.flow_x _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_mul _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_y _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.step_z
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite continuation. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions Orientations
open scoped Classical MatrixOrder Matrix.Norms.Elementwise
variable {n m : ℕ}

lemma interior_capacities_lower (H : MultiGraph n m) {s κ t ρ : ℝ}
    (hρ : 0 ≤ ρ) (hρκ : ρ ≤ κ) (u : Fin m → ℝ) (c : StepFree n m)
    (h : ∀x : StepFree n m, x.Close c ρ → x ∈ stepCore H s κ t u) :
    ∀e, ρ ≤ c.capacities κ u e := by
  let w : StepFree n m := (c.1,c.multiplier,c.y,fun e => c.z e-ρ)
  have hw : w.Close c ρ := by
    refine ⟨?_,?_,?_,?_⟩
    · intro i j
      simpa only [w,sub_self,abs_zero] using hρ
    · intro ijk
      simpa only [w,StepFree.multiplier,sub_self,abs_zero] using hρ
    · intro e
      simpa only [w,StepFree.y,sub_self,abs_zero] using hρ
    · intro e
      change |c.z e-ρ-c.z e| ≤ ρ
      rw [show c.z e-ρ-c.z e = -ρ by ring,abs_neg,abs_of_nonneg hρ]
  have hwc := h w hw
  intro e
  unfold StepFree.capacities
  split_ifs
  · have he := (hwc.2.2.2.2.1 e).1
    change 0 ≤ c.z e-ρ at he
    linarith only [he]
  · exact hρκ

lemma finite_interior_numbers {P β : ℝ} (hP : 5 ≤ P)
    (hn : (n:ℝ) ≤ P) (hm : (m:ℝ) ≤ P) (hβ : P⁻¹/32 ≤ β) :
    let ε := P^(-10:ℤ)
    let α := P^(-12:ℤ)
    let γ := P^(-45:ℤ)
    let ρ := P^(-30:ℤ)
    let δ := P^(-50:ℤ)
    0 < β ∧ α ≤ ε ∧ α*((n:ℝ)-1) ≤ ε ∧
      4*m*γ ≤ α ∧ 4*m*γ ≤ β ∧ 2*γ ≤ ρ ∧
      δ ≤ ρ ∧ δ ≤ γ/4 ∧ γ ≤ 1 ∧ ρ ≤ P⁻¹ := by
  dsimp only
  have hP0 : 0 < P := by linarith
  have hP1 : 1 ≤ P := by linarith
  have hP2 : 25 ≤ P^2 := by nlinarith only [hP,sq_nonneg (P-5)]
  have hpw {a b : ℕ} (hab : a ≤ b) : P^a ≤ P^b := pow_le_pow_right₀ hP1 hab
  have h4 : (4:ℝ) ≤ P^5 := (by linarith : (4:ℝ) ≤ P).trans (by simpa using hpw (by norm_num : 1 ≤ 5))
  have h32 : (32:ℝ) ≤ P^11 := by
    have hh : 32 ≤ P^4 := by nlinarith only [hP2,sq_nonneg (P^2-25)]
    exact hh.trans (hpw (by norm_num))
  have hnm : (n:ℝ)-1 ≤ P^2 := calc
    _ ≤ P := by linarith only [hn]
    _ ≤ P^2 := by simpa using hpw (by norm_num : 1 ≤ 2)
  have hnα := scaled_inverse_power hP0 10 2 hnm
  have hm4 : 4*(m:ℝ) ≤ P^33 := calc
    _ ≤ 4*P := by linarith only [hm]
    _ ≤ P^2 := by nlinarith only [hP]
    _ ≤ P^33 := hpw (by norm_num)
  have hmγ := scaled_inverse_power hP0 12 33 hm4
  have hαβ : P^(-12:ℤ) ≤ β := by
    have hh := scaled_inverse_power hP0 1 11 h32
    norm_num only [Nat.cast_ofNat,Nat.reduceAdd,_root_.zpow_neg_one] at hh
    linarith only [hh,hβ]
  have hgρ := scaled_inverse_power hP0 30 15
    (show (2:ℝ) ≤ P^15 from (by linarith : (2:ℝ) ≤ P).trans (by simpa using hpw (by norm_num : 1 ≤ 15)))
  have hdg := scaled_inverse_power hP0 45 5 h4
  norm_num only [Nat.cast_ofNat,Nat.reduceAdd] at hnα hmγ hgρ hdg
  have hβ0 : 0 < β := (by positivity : (0:ℝ) < P⁻¹/32).trans_le hβ
  refine ⟨hβ0,inverse_power_mono hP1 (by norm_num : 10 ≤ 12),?_,?_,?_,?_,
    inverse_power_mono hP1 (by norm_num : 30 ≤ 50),?_,?_,?_⟩
  · simpa only [Nat.cast_ofNat,mul_comm] using hnα
  · simpa only [Nat.cast_ofNat,mul_assoc] using hmγ
  · exact hmγ.trans hαβ
  · simpa only [Nat.cast_ofNat] using hgρ
  · simpa only [Nat.cast_ofNat] using (show P^(-50:ℤ) ≤ P^(-45:ℤ)/4 by linarith only [hdg])
  · simpa using inverse_power_mono hP1 (by norm_num : 0 ≤ 45)
  · simpa using inverse_power_mono hP1 (by norm_num : 1 ≤ 30)

theorem finite_continuation_inner_cube_oai (H : MultiGraph n m) (hn : 2 ≤ n)
    (hconn : H.Connected univ) {s qbar β : ℝ}
    (hs : 0 ≤ s) (hsP : s ≤ graphSize n m)
    (hq : (graphSize n m)^(-12:ℤ) ≤ qbar) (hqm : qbar+β ≤ m)
    (hβ : (graphSize n m)⁻¹/32 ≤ β)
    (u : Fin m → ℝ) (hu : ∀e, 0 ≤ u e) {z : StepFree n m}
    (hz : z ∈ stepFeasible H s (continuationBaseline m) (continuationStep m) (qbar+β+β) u) :
    ∃(c : StepFree n m) (F : FlowPoint n m),
      c.Bounded (6*graphSize n m) ∧ F.Bounded (6*graphSize n m) ∧
      ∀(x : StepFree n m) (W : FlowPoint n m),
        x.Close c ((graphSize n m)^(-50:ℤ)) →
        W.Close F ((graphSize n m)^(-50:ℤ)) →
        finiteStep H s (continuationBaseline m) (continuationStep m) qbar
          ((graphSize n m)^(-10:ℤ)) u x W := by
  let P := graphSize n m
  have hP : 5 ≤ P := connected_size_five H hn hconn
  have hP0 : 0 < P := by linarith only [hP]
  have hnP : (n:ℝ) ≤ P := by unfold P graphSize; linarith [Nat.cast_nonneg (α:=ℝ) m]
  have hmP : (m:ℝ) ≤ P := by unfold P graphSize; linarith [Nat.cast_nonneg (α:=ℝ) n]
  obtain ⟨hβ0,hαε,hαn,hmγα,hmγβ,hgρ,hdρ,hdγ,hγ1,hρP⟩ :=
    finite_interior_numbers hP hnP hmP hβ
  have hγ0 : (0:ℝ) < P^(-45:ℤ) := zpow_pos hP0 _
  have hα0 : (0:ℝ) ≤ P^(-12:ℤ) := (zpow_pos hP0 _).le
  obtain ⟨c,hc,hball⟩ := bounded_step_inner_cube H hn hconn hs hsP hqm hβ u hu hz
  have hρ0 : (0:ℝ) ≤ P^(-30:ℤ) := (zpow_pos hP0 _).le
  have hcself := hball c (StepFree.Close.refl c hρ0)
  have hcap := interior_capacities_lower H hρ0 (hρP.trans baseline_lower) u c
    (fun x hx => (hball x hx).1)
  have hcR : ∀e, c.capacities (continuationBaseline m) u e ≤ 2 := by
    intro e
    unfold StepFree.capacities
    split_ifs
    · exact (hcself.1.2.2.2.2.1 e).2.trans (by linarith only [baseline_le_one (m:=m)])
    · exact baseline_le_one.trans (by norm_num)
  obtain ⟨F,hF,hFball⟩ := flow_inner_cube_vary H (by omega) (c.capacities (continuationBaseline m) u)
    hγ0 hα0 hq hαε hαn hβ0 hmγα hmγβ (fun e => hgρ.trans (hcap e)) hcR
    (fun p => by have hh := hcself.2 p; unfold slack at hh; linarith only [hh])
  refine ⟨c,F,hc,hF.mono ?_,?_⟩
  · linarith only [hγ1,hP]
  · intro x W hx hW
    refine ⟨(hball x (hx.mono hdρ)).1,hFball (x.capacities (continuationBaseline m) u) W ?_ (hW.mono hdγ)⟩
    intro e
    unfold StepFree.capacities
    split_ifs
    · have hh := (abs_le.mp (hx.2.2.2 e)).1
      change -(P^(-50:ℤ)) ≤ x.z e-c.z e at hh
      linarith only [hh,hdγ,hγ0]
    · linarith only [hγ0]

end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube_oai := @OAI.AlgorithmicThinTrees.MetricTests.finite_continuation_inner_cube_oai
