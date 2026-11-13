-- Prove2me | solution 1 for OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct_explicit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-12T12:08:47.311235+00:00
-- url     : https://prove2.me/submissions/a7158f66-457f-4d9a-89b1-2d3c8ff91c93

import Mathlib
import Definitions.Def_AlgorithmicThinTrees
import Definitions.Def_OAIQ241TT009
import Theorems.Thm_OAI_AlgorithmicThinTrees_MetricTests_RationalStep_uniform_search_response_explicit

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

lemma posDef_solve {X : Matrix ι ι ℝ} (hX : X.PosDef) (b : ι → ℝ) :
    X *ᵥ (X⁻¹ *ᵥ b) = b := by
  rw [mulVec_mulVec, mul_nonsing_inv X ((isUnit_iff_isUnit_det X).mp hX.isUnit),
    one_mulVec]

theorem resistance_order {X : Matrix ι ι ℝ} (hX : X.PosDef)
    (b : ι → ℝ) {t : ℝ} (ht : 0 < t) :
    b ⬝ᵥ (X⁻¹ *ᵥ b) ≤ t ↔ (t • X - vecMulVec b b).PosSemidef := by
  let y := X⁻¹ *ᵥ b
  have hsolve : X *ᵥ y = b := posDef_solve hX b
  have hq (x : ι → ℝ) : 0 ≤ x ⬝ᵥ (X *ᵥ x) := by
    simpa only [star_trivial] using hX.posSemidef.dotProduct_mulVec_nonneg x
  have hr : 0 ≤ b ⬝ᵥ y := by
    simpa only [hsolve, dotProduct_comm] using hq y
  constructor
  · intro h
    have hb : (vecMulVec b b).IsHermitian := by
      simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
    refine PosSemidef.of_dotProduct_mulVec_nonneg
      ((hX.isHermitian.smul (isSelfAdjoint_iff.mpr (star_trivial t))).sub hb) ?_
    intro x
    have hcs := quadratic_cauchy_schwarz hX.posSemidef x y
    rw [hsolve] at hcs
    have hm : (x ⬝ᵥ (X *ᵥ x)) * (b ⬝ᵥ y) ≤ (x ⬝ᵥ (X *ᵥ x)) * t :=
      mul_le_mul_of_nonneg_left h (hq x)
    rw [dotProduct_comm y b, dotProduct_comm x b] at hcs
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic]
    nlinarith
  · intro h
    have htest := h.dotProduct_mulVec_nonneg y
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul,
      smul_eq_mul, rankOne_quadratic, hsolve, dotProduct_comm y b] at htest
    change b ⬝ᵥ y ≤ t
    nlinarith

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
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionRank
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uI uV uE2 uV2

section

namespace StrongThinTree.MultiGraph
noncomputable section
open Finset Submodule
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_mono_span {A : Finset (Fin n)} {F T : Finset (Fin m)}
    (h : G.edgeSpan F ≤ G.edgeSpan T) (hc : G.ConnectedOn A F) : G.ConnectedOn A T := by
  intro u hu v hv
  exact h (hc u hu v hv)

lemma independent_spanning_subset (F : Finset (Fin m)) :
    ∃ T ⊆ F, LinearIndepOn ℝ G.incidence (T : Set (Fin m)) ∧ G.edgeSpan T = G.edgeSpan F := by
  classical
  let h : LinearIndepOn ℝ G.incidence (∅ : Set (Fin m)) := linearIndepOn_empty ℝ G.incidence
  let U := h.extend (Set.empty_subset (F : Set (Fin m)))
  refine ⟨U.toFinset, ?_, ?_, ?_⟩
  · intro e he
    exact h.extend_subset (Set.empty_subset (F : Set (Fin m))) (Set.mem_toFinset.mp he)
  · simpa only [Set.coe_toFinset] using h.linearIndepOn_extend (Set.empty_subset (F : Set (Fin m)))
  · simpa only [edgeSpan, Packing.span, Set.coe_toFinset] using
      h.span_image_extend_eq_span_image (Set.empty_subset (F : Set (Fin m)))

lemma packableOn_iff_trees (F : Finset (Fin m)) (q : ℕ) (A : Finset (Fin n)) :
    G.PackableOn F q A ↔ ∃ T : Fin q → Finset (Fin m),
      (∀ i, T i ⊆ F ∧ G.TreeOn A (T i)) ∧
      ∀ ⦃i j⦄, i ≠ j → Disjoint (T i) (T j) := by
  classical
  constructor
  · rintro ⟨T, hT, hd⟩
    choose U hU hi hs using fun i => G.independent_spanning_subset (T i)
    refine ⟨U, fun i => ⟨?_, ?_, ?_, hi i⟩, fun i j hij =>
      disjoint_of_subset_left (hU i) (disjoint_of_subset_right (hU j) (hd hij))⟩
    · exact (hU i).trans ((hT i).1.trans (filter_subset _ _))
    · intro e he
      exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp ((hT i).1 (hU i he))).2⟩
    · exact G.connectedOn_mono_span (le_of_eq (hs i).symm) (hT i).2
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨?_, (hT i).2.2.1⟩, hd⟩
    intro e he
    exact mem_filter.mpr ⟨(hT i).1 he, (mem_filter.mp ((hT i).2.1 he)).2⟩

lemma connectedOn_univ (T : Finset (Fin m)) : G.ConnectedOn univ T ↔ G.Connected T := by
  rw [G.connected_iff_same]
  simp only [ConnectedOn, mem_univ, forall_const]

lemma packableOn_univ (F : Finset (Fin m)) (q : ℕ) :
    G.PackableOn F q univ ↔ G.TreePackable F q := by
  rw [G.packableOn_iff_trees]
  constructor
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_⟩, hd⟩
    exact (G.spanningTree_iff_independent _).mpr
      ⟨(G.connectedOn_univ _).mp (hT i).2.2.1, (hT i).2.2.2⟩
  · rintro ⟨T, hT, hd⟩
    refine ⟨T, fun i => ⟨(hT i).1, ?_, ?_, ?_⟩, hd⟩
    · simp [internal]
    · exact (G.connectedOn_univ _).mpr (hT i).2.1
    · exact ((G.spanningTree_iff_independent _).mp (hT i).2).2

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_PartitionHierarchy
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
open Finset
variable {n m : ℕ} (G : MultiGraph n m)

lemma connectedOn_cut {A S : Finset (Fin n)} {T : Finset (Fin m)}
    (hc : G.ConnectedOn A T) (hS : S.Nonempty) (hSA : S ⊂ A) : (G.cut T S).Nonempty := by
  classical
  by_contra hcut
  have hempty : G.cut T S=∅ := not_nonempty_iff_eq_empty.mp hcut
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑u ∈ S, LinearMap.proj u
  have hker : G.edgeSpan T ≤ LinearMap.ker f := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e he
    have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
      have hh : ¬((G.left e ∈ S ∧ G.right e ∉ S) ∨ (G.right e ∈ S ∧ G.left e ∉ S)) := by
        intro h
        have hm : e ∈ G.cut T S := mem_filter.mpr ⟨he,h⟩
        simp [hempty] at hm
      tauto
    change f (G.incidence e)=0
    rw [incidence,map_sub]
    change (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
      (∑u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e))=0
    simp only [sumOn_point,hiff,sub_self]
  obtain ⟨u,hu⟩ := hS
  have hv : (A \ S).Nonempty := sdiff_nonempty.mpr (not_subset.mpr (by
    by_contra h
    push Not at h
    exact (not_ssubset_of_subset h) hSA))
  obtain ⟨v,hv⟩ := hv
  obtain ⟨hvA,hvS⟩ := mem_sdiff.mp hv
  have hz := hker (hc u (hSA.subset hu) v hvA)
  change f (point u-point v)=0 at hz
  rw [map_sub] at hz
  change (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
    (∑w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v)=0 at hz
  simp [sumOn_point,hu,hvS] at hz

lemma packableOn_edgeConnectedReal {F : Finset (Fin m)} {q : ℕ} {A : Finset (Fin n)}
    (hp : G.PackableOn F q A) : G.EdgeConnectedReal A q := by
  classical
  obtain ⟨T,hT,hd⟩ := hp
  intro S hS hSA
  have hne (i : Fin q) := G.connectedOn_cut (hT i).2 hS hSA
  have hdis : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint (fun i => G.cut (T i) S) := by
    intro i _ j _ hij
    exact disjoint_of_subset_left (filter_subset _ _) (disjoint_of_subset_right (filter_subset _ _) (hd hij))
  have hsub : univ.biUnion (fun i : Fin q => G.cut (T i) S) ⊆ G.cut (G.inducedEdges A) S := by
    apply biUnion_subset.mpr
    intro i _ e he
    obtain ⟨het,hes⟩ := mem_filter.mp he
    have hh := (mem_filter.mp ((hT i).1 het)).2
    exact mem_filter.mpr ⟨(G.mem_inducedEdges A e).mpr hh,hes⟩
  have hh := card_le_card hsub
  rw [card_biUnion hdis] at hh
  have hl : q ≤ ∑i : Fin q, (G.cut (T i) S).card := by
    simpa using sum_le_sum (s := (univ : Finset (Fin q))) (f := fun _ => 1)
      (g := fun i => (G.cut (T i) S).card) (fun i _ => card_pos.mpr (hne i))
  exact_mod_cast hl.trans hh

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_ExtractionCriterion
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Finset Matrix
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma treePackable_edgeConnected {r : ℕ} (hp : G.TreePackable univ r) : G.EdgeConnected r := by
  have hh := G.packableOn_edgeConnectedReal ((G.packableOn_univ univ r).mpr hp)
  intro S hS hS'
  have hs : S ⊂ (univ : Finset (Fin n)) := Finset.ssubset_iff_subset_ne.mpr ⟨subset_univ _,hS'⟩
  have hc := hh S hS hs
  have hi : G.inducedEdges univ = univ := by ext e; simp [mem_inducedEdges]
  rw [hi] at hc
  exact_mod_cast hc

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Representation
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix Finset
open scoped BigOperators
variable {n m : ℕ} (G : MultiGraph n m)

lemma edgeSpan_le_zeroSum (T : Finset (Fin m)) : G.edgeSpan T ≤ zeroSumSpace n :=
  (Packing.span_le_iff G.incidence).mpr (fun e _he => G.incidence_zeroSum e)

lemma connected_span_zeroSum {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    G.edgeSpan T = zeroSumSpace n := by
  apply le_antisymm (G.edgeSpan_le_zeroSum T)
  intro x hx
  have hx0 := (mem_zeroSumSpace x).mp hx
  let u₀ : Fin n := ⟨0, hn⟩
  have hs : ∑ u, x u • (point u - point u₀) ∈ G.edgeSpan T := by
    apply Submodule.sum_mem
    intro u hu
    exact Submodule.smul_mem _ _ ((G.connected_iff_same T).mp hT u u₀)
  have heq : ∑ u, x u • (point u - point u₀) = x := by
    simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hx0, zero_smul, sub_zero]
    ext u
    simp [point, Pi.single_apply, Finset.sum_apply, mul_ite]
  rwa [heq] at hs

end
end StrongThinTree.MultiGraph

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

lemma qform_constantProjection (x : Fin n → ℝ) :
    qform (constantProjection n) x=(∑i, x i)^2/(n:ℝ) := by
  rw [qform,constantProjection_mulVec,dotProduct_smul,dotProduct_comm x,ones_dot]
  simp only [smul_eq_mul]
  ring

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

lemma centered_psd {D : Matrix (Fin n) (Fin n) ℝ} (hD : D.PosSemidef) : (centered D).PosSemidef := by
  have hh := hD.mul_mul_conjTranspose_same (centering n)
  simpa only [centered,conjTranspose_eq_transpose_of_trivial,centering_symmetric] using hh

lemma centered_ones (hn : 0 < n) (D : Matrix (Fin n) (Fin n) ℝ) : centered D *ᵥ ones n=0 := by
  simp only [centered,←mulVec_mulVec,centering_ones hn,mulVec_zero]

lemma qform_centered (D : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    qform (centered D) x=qform D (centering n *ᵥ x) := by
  unfold centered qform
  rw [←mulVec_mulVec,←mulVec_mulVec,dotProduct_mulVec,←mulVec_transpose,centering_symmetric]

lemma laplacian_zeroSum_pos (G : MultiGraph n m) (hn : 0 < n) (hc : G.Connected univ)
    (x : Fin n → ℝ) (hx : (∑i, x i)=0) (hxne : x ≠ 0) :
    0 < qform (G.laplacian univ) x := by
  have hnonneg := qform_nonneg (G.laplacian_psd univ) x
  by_contra hpos
  have hzero : qform (G.laplacian univ) x=0 := le_antisymm (not_lt.mp hpos) hnonneg
  have hedge (e : Fin m) : x (G.left e)-x (G.right e)=0 := by
    rw [G.laplacian_qform] at hzero
    have he := (single_le_sum (fun i _ => sq_nonneg (x (G.left i)-x (G.right i))) (mem_univ e))
    rw [hzero] at he
    exact sq_eq_zero_iff.mp (le_antisymm he (sq_nonneg _))
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := fun v => x ⬝ᵥ v
      map_add' := fun v w => dotProduct_add x v w
      map_smul' := fun c v => dotProduct_smul c x v }
  have hf : G.edgeSpan univ ≤ f.ker := by
    apply (Packing.span_le_iff G.incidence).mpr
    intro e _
    change (∑v, x v*G.incidence e v)=0
    rw [G.eval_incidence]
    exact hedge e
  have hxx : x ⬝ᵥ x=0 := hf (by rw [G.connected_span_zeroSum hn hc]; exact (mem_zeroSumSpace x).mpr hx)
  exact hxne (dotProduct_self_eq_zero.mp hxx)

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

end Pairing
end
end AlgorithmicThinTrees.MetricTests
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Metric_Hierarchy
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Metric hierarchy. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma incidence_sum (G : MultiGraph n m) (e : Fin m) : ∑i, G.incidence e i=0 :=
  (mem_zeroSumSpace _).mp (G.incidence_zeroSum e)

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

lemma centeredPositive_psd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : D.PosSemidef := by
  apply PosSemidef.of_dotProduct_mulVec_nonneg hD.1
  intro x
  change 0 ≤ qform D x
  rw [←centered_eq hD.1 hD.2.1,qform_centered]
  by_cases hx : centering n *ᵥ x=0
  · simp [hx,qform]
  · exact (hD.2.2 _ (centering_mulVec_sum hn x) hx).le

lemma regularize_pd (hn : 0 < n) {D : Matrix (Fin n) (Fin n) ℝ}
    (hD : CenteredPositive D) : (regularize D).PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (hD.1.add constantProjection_psd.isHermitian)
  intro x hx
  change 0 < qform (regularize D) x
  rw [regularize,qform_add]
  by_cases hp : centering n *ᵥ x=0
  · have hs : (∑i, x i) ≠ 0 := by
      intro hs
      rw [centering_mulVec_of_sum_zero hs] at hp
      exact hx hp
    have hq : 0 < qform (constantProjection n) x := by
      rw [qform_constantProjection]
      exact div_pos (sq_pos_of_ne_zero hs) (Nat.cast_pos.mpr hn)
    exact add_pos_of_nonneg_of_pos (qform_nonneg (centeredPositive_psd hn hD) _) hq
  · have hq : 0 < qform D x := by
      rw [←centered_eq hD.1 hD.2.1,qform_centered]
      exact hD.2.2 _ (centering_mulVec_sum hn x) hp
    exact add_pos_of_pos_of_nonneg hq (qform_nonneg constantProjection_psd _)

lemma centered_rankOne {b : Fin n → ℝ} (hb : (∑i, b i)=0) :
    centered (vecMulVec b b)=vecMulVec b b := by
  apply centered_eq
  · simpa only [star_trivial] using (posSemidef_vecMulVec_self_star b).isHermitian
  · rw [vecMulVec_mulVec,dotProduct_comm,ones_dot,hb,IsCentralScalar.op_smul_eq_smul,zero_smul]

lemma centered_regularize {D : Matrix (Fin n) (Fin n) ℝ} (hn : 0 < n)
    (hD : D.IsHermitian) (hD0 : D *ᵥ ones n=0) : centered (regularize D)=D := by
  have hc0 : centering n*constantProjection n=0 := by
    exact mul_constant_of_ones (centering_ones hn)
  simp only [centered,regularize,mul_add,hc0,add_zero,
    centering_mul_of_ones hD hD0,mul_centering_of_ones hD0]

lemma centered_resistance_order (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : CenteredPositive X) {b : Fin n → ℝ} (hb : (∑i, b i)=0)
    {a : ℝ} (ha : 0 < a) :
    (X-a • vecMulVec b b).PosSemidef ↔ a*qform (inverseOnZeroSum X) b ≤ 1 := by
  have heq : a • (a⁻¹ • regularize X-vecMulVec b b)=regularize X-a • vecMulVec b b := by
    rw [smul_sub,smul_smul,mul_inv_cancel₀ ha.ne',one_smul]
  have hproblem := StrongThinTree.resistance_order (regularize_pd hn hX) b (inv_pos.mpr ha)
  constructor
  · intro h
    have h' : (regularize X-a • vecMulVec b b).PosSemidef := by
      convert h.add constantProjection_psd using 1
      all_goals try with_reducible_and_instances rfl
      unfold regularize
      abel
    have hinv := h'.smul (inv_nonneg.mpr ha.le)
    have hi : a⁻¹ • (regularize X-a • vecMulVec b b)=a⁻¹ • regularize X-vecMulVec b b := by
      rw [smul_sub,smul_smul,inv_mul_cancel₀ ha.ne',one_smul]
    rw [hi] at hinv
    have hh := hproblem.mpr hinv
    change qform (inverseOnZeroSum X) b ≤ a⁻¹ at hh
    have hm := mul_le_mul_of_nonneg_left hh ha.le
    rwa [mul_inv_cancel₀ ha.ne'] at hm
  · intro h
    have hh : qform (inverseOnZeroSum X) b ≤ a⁻¹ := by
      rw [←one_div,le_div_iff₀ ha]
      simpa only [mul_comm] using h
    have h' := (hproblem.mp hh).smul ha.le
    rw [heq] at h'
    have hc := centered_psd h'
    have he : centered (regularize X-a • vecMulVec b b)=X-a • vecMulVec b b := by
      simp only [centered,mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc]
      rw [show centering n*regularize X*centering n=X from centered_regularize hn hX.1 hX.2.1]
      rw [show centering n*vecMulVec b b*centering n=vecMulVec b b from centered_rankOne hb]
    rwa [he] at hc

lemma laplacian_mem_domain (G : MultiGraph n m) : G.laplacian univ ∈ metricDomain G := by
  refine ⟨(G.laplacian_psd univ).isHermitian,laplacian_ones G,le_rfl,?_⟩
  intro Z hZ
  have hh := trace_pairing_nonneg (G.laplacian_psd univ) hZ.1.1
  linarith only [hh]

lemma domain_positive (G : MultiGraph n m) (hn : 0 < n) (hG : G.Connected univ)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain G) : CenteredPositive X := by
  refine ⟨hX.1,hX.2.1,?_⟩
  intro x hx hx0
  exact (laplacian_zeroSum_pos G hn hG x hx hx0).trans_le (qform_mono hX.2.2.1 x)

lemma domain_convex (G : MultiGraph n m) : Convex ℝ (metricDomain G) := by
  intro X hX Y hY a b ha hb hab
  refine ⟨(hX.1.smul (isSelfAdjoint_iff.mpr (star_trivial a))).add (hY.1.smul (isSelfAdjoint_iff.mpr (star_trivial b))),?_,?_,?_⟩
  · simp only [add_mulVec,smul_mulVec,hX.2.1,hY.2.1,smul_zero,add_zero]
  · apply Matrix.le_iff.mpr
    have h := ((Matrix.le_iff.mp hX.2.2.1).smul ha).add ((Matrix.le_iff.mp hY.2.2.1).smul hb)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_sub,smul_sub]
    have hh : a • G.laplacian univ+b • G.laplacian univ=G.laplacian univ := by
      rw [←add_smul,hab,one_smul]
    nth_rw 1 [←hh]
    abel
  · intro Z hZ
    simp only [add_mul,smul_mul_assoc,trace_add,trace_smul,smul_eq_mul]
    calc
      a*(X*Z).trace+b*(Y*Z).trace ≤ a*(3*(G.laplacian univ*Z).trace)+b*(3*(G.laplacian univ*Z).trace) :=
        add_le_add (mul_le_mul_of_nonneg_left (hX.2.2.2 Z hZ) ha) (mul_le_mul_of_nonneg_left (hY.2.2.2 Z hZ) hb)
      _ = 3*(G.laplacian univ*Z).trace := by rw [←add_mul,hab,one_mul]

lemma difference_sum (u v : Fin n) : (∑i, difference u v i)=0 := by
  simp [difference,point,sum_sub_distrib]

lemma test_centered (hn : 0 < n) {Z : Matrix (Fin n) (Fin n) ℝ} (hZ : Test Z) :
    CenteredTest (centered Z) := by
  refine ⟨⟨centered_psd hZ.1,?_⟩,centered_ones hn Z⟩
  intro u v w
  simpa only [qform_centered,centering_mulVec_of_sum_zero (difference_sum _ _)] using hZ.2 u v w

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
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Ramp
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right _root_.OAI.AlgorithmicThinTrees.Partitions.mem_crossing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation ramp. -/

section

namespace AlgorithmicThinTrees.MetricTests
noncomputable section
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph
open scoped Classical MatrixOrder

variable {n m : ℕ}

lemma incidence_ne_zero (G : MultiGraph n m) (e : Fin m) : G.incidence e ≠ 0 := by
  intro hz
  have he := congrFun hz (G.left e)
  simp [MultiGraph.incidence,MultiGraph.point,G.loopless e] at he

lemma centered_resistance_pos (G : MultiGraph n m) (hn : 0 < n)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    0 < resistance G X e := by
  simpa only [resistance,inverseOnZeroSum,StrongThinTree.qform,star_trivial] using
    (regularize_pd hn hX).inv.dotProduct_mulVec_pos (incidence_ne_zero G e)

lemma cappedParameter_pos (G : MultiGraph n m) (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    0 < cappedParameter G s X e :=
  lt_min (by norm_num) (inv_pos.mpr (mul_pos hs (centered_resistance_pos G hn hX e)))

lemma cappedParameter_le_two (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) :
    cappedParameter G s X e ≤ 2 := min_le_left _ _

lemma ramp_nonneg (G : MultiGraph n m) (s : ℝ) (X : Matrix (Fin n) (Fin n) ℝ) (e : Fin m) :
    0 ≤ ramp G s X e := le_max_left _ _

lemma ramp_active (G : MultiGraph n m) {s : ℝ} {X : Matrix (Fin n) (Fin n) ℝ} {e : Fin m}
    (ha : 0 < ramp G s X e) :
    1 < cappedParameter G s X e ∧ ramp G s X e=cappedParameter G s X e-1 := by
  have hp : 0 < cappedParameter G s X e-1 := by
    simpa only [ramp,lt_max_iff,lt_self_iff_false,false_or] using ha
  exact ⟨by linarith,max_eq_right hp.le⟩

lemma capped_rankOne (G : MultiGraph n m) (hn : 0 < n) {s : ℝ} (hs : 0 < s)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X) (e : Fin m) :
    (s*cappedParameter G s X e) • vecMulVec (G.incidence e) (G.incidence e) ≤ X := by
  rw [Matrix.le_iff,centered_resistance_order hn hX (incidence_sum G e)
    (mul_pos hs (cappedParameter_pos G hn hs hX e))]
  change s*cappedParameter G s X e*resistance G X e ≤ 1
  have hr : 0 < s*resistance G X e := mul_pos hs (centered_resistance_pos G hn hX e)
  have hm := mul_le_mul_of_nonneg_right
    (min_le_right (2:ℝ) (s*resistance G X e)⁻¹) hr.le
  rw [inv_mul_cancel₀ hr.ne'] at hm
  dsimp only [cappedParameter]
  nlinarith only [hm]

lemma continuation_scalar {t p y : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hp : p ≤ 2) (hy : 0 ≤ y) :
    p+t*(5*y-4) ≤ ((1-t)*p+6*t*y)/(1+t) := by
  apply (le_div_iff₀ (by linarith : 0 < 1+t)).mpr
  have hy' : 0 ≤ (1-5*t)*y := mul_nonneg (by linarith) hy
  have hrem : 0 ≤ t*((1-5*t)*y+4+4*t-2*p) :=
    mul_nonneg ht (by linarith)
  nlinarith only [hrem]

lemma ramp_scalar_lower {p z t y : ℝ} (hp : 1 < p) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hp2 : p ≤ 2) (hy : 0 ≤ y)
    (hz : ((1-t)*p+6*t*y)/(1+t) ≤ z) :
    min 1 (max 0 (p-1)+t*(5*y-4)) ≤ max 0 (min 2 z-1) := by
  rw [max_eq_right (by linarith : 0 ≤ p-1)]
  have hz' := (continuation_scalar ht ht1 hp2 hy).trans hz
  have hcap := min_le_min_left (2:ℝ) hz'
  have he : min (1:ℝ) (p-1+t*(5*y-4))=min 2 (p+t*(5*y-4))-1 := by
    rw [←min_sub_sub_right]
    congr 1 <;> ring
  rw [he]
  exact (sub_le_sub_right hcap 1).trans (le_max_right _ _)

lemma continuation_reciprocal (G : MultiGraph n m) (hn : 0 < n)
    {X Y : Matrix (Fin n) (Fin n) ℝ} (hX : CenteredPositive X)
    {s t y : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (hy : 0 ≤ y) (e : Fin m)
    (hresp : (6*s*y) • vecMulVec (G.incidence e) (G.incidence e) ≤ Y)
    (hnew : CenteredPositive ((1-t) • X+t • Y)) :
    ((1-t)*cappedParameter G s X e+6*t*y)/(1+t) ≤
      ((1+t)*s*resistance G ((1-t) • X+t • Y) e)⁻¹ := by
  let b := vecMulVec (G.incidence e) (G.incidence e)
  let p := cappedParameter G s X e
  let c := ((1-t)*p+6*t*y)*s
  have ht' : 0 < 1-t := by linarith
  have hp : 0 < p := cappedParameter_pos G hn hs hX e
  have hc : 0 < c := mul_pos (add_pos_of_pos_of_nonneg (mul_pos ht' hp) (by positivity)) hs
  have horder : c • b ≤ (1-t) • X+t • Y := by
    have h1 := (Matrix.le_iff.mp (capped_rankOne G hn hs hX e)).smul ht'.le
    have h2 := (Matrix.le_iff.mp hresp).smul ht
    apply Matrix.le_iff.mpr
    convert h1.add h2 using 1
    all_goals try with_reducible_and_instances rfl
    dsimp [c,p,b]
    simp only [smul_sub,smul_smul]
    module
  have hrank := (centered_resistance_order hn hnew (incidence_sum G e) hc).mp (Matrix.le_iff.mp horder)
  have hR := centered_resistance_pos G hn hnew e
  have hnR : 0 < (1+t)*s*resistance G ((1-t) • X+t • Y) e := by positivity
  rw [←one_div]
  apply (le_div_iff₀ hnR).mpr
  have hden : (1-t)*p+6*t*y ≥ 0 := by positivity
  have hquot := (div_mul_cancel₀ ((1-t)*p+6*t*y) (by linarith : (1+t) ≠ 0))
  have he : (((1-t)*p+6*t*y)/(1+t))*((1+t)*s*resistance G ((1-t) • X+t • Y) e)=
      c*resistance G ((1-t) • X+t • Y) e := by
    dsimp [c]
    calc
      _ = ((((1-t)*p+6*t*y)/(1+t))*(1+t))*(s*resistance G ((1-t) • X+t • Y) e) := by ring
      _ = _ := by rw [hquot]; ring
  rw [he]
  exact hrank

end
end AlgorithmicThinTrees.MetricTests
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

lemma stepCore_domain (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) :
    x.matrix ∈ metricDomain H := by
  apply (metricDomain_iff_lmi H hn (responseMatrix_hermitian x.1) (responseMatrix_ones hn x.1)).mpr
  exact ⟨Matrix.le_iff.mpr hx.1,x.multiplier,hx.2.2.1,hx.2.1⟩

lemma stepCore_admissible (H : MultiGraph n m) (hn : 0 < n)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) :
    (x.matrix,x.y) ∈ admissible H s u :=
  ⟨stepCore_domain H hn hx,hx.2.2.2.1,fun e he => Matrix.le_iff.mpr ((hx.2.2.2.2.2 e he).1)⟩

lemma stepCore_capacity_le (H : MultiGraph n m)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m} (hx : x ∈ stepCore H s κ t u) (e : Fin m) :
    x.capacities κ u e ≤ lowerCapacity κ t (u e) (x.y e) := by
  unfold StepFree.capacities lowerCapacity
  split_ifs with he
  · rw [add_min]
    exact le_min (hx.2.2.2.2.1 e).2 (by simpa only [add_assoc] using (hx.2.2.2.2.2 e he).2)
  · exact le_rfl

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

lemma internal_le_out (G : MultiGraph n m) {x a b : Fin m → ℝ}
    (ha : ∀e, 0 ≤ a e) (hb : ∀e, 0 ≤ b e) (he : ∀e, x e ≤ a e+b e)
    (S : Finset (Fin n)) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e) ≤ ∑v ∈ S, out G a b v := by
  rw [sum_filter]
  simp only [out]
  rw [sum_comm]
  apply sum_le_sum
  intro e he'
  have hsum : (∑v ∈ S, ((if G.left e=v then a e else 0)+(if G.right e=v then b e else 0)))=
      (if G.left e ∈ S then a e else 0)+(if G.right e ∈ S then b e else 0) := by
    rw [sum_add_distrib]
    simp only [sum_ite_eq]
  rw [hsum]
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S
  · simpa only [hl,hr,and_self,ite_true, if_true] using he e
  · simpa only [hl,hr,and_false,ite_false, if_false,ite_true, if_true,add_zero] using ha e
  · simpa only [hl,hr,false_and,ite_false, if_false,ite_true, if_true,zero_add] using hb e
  · simp [hl,hr]

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Flow_RootedRelaxation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Rooted relaxation. -/

section

namespace AlgorithmicThinTrees.Orientations
noncomputable section
open Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped Classical
variable {n m : ℕ}

lemma parts_card {V : Type*} [Fintype V] (p : Setoid V) : (parts p).card=partCount p := by
  let f : Quotient p → parts p := Quotient.lift
    (fun v => ⟨block p v,block_mem_parts p v⟩)
    (fun a b h => Subtype.ext ((block_eq_iff p a b).mpr h))
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a,b using Quotient.inductionOn₂ with
      | h a b =>
        intro he
        exact Quotient.sound ((block_eq_iff p a b).mp (congrArg Subtype.val he))
    · intro A
      obtain ⟨v,hv⟩ := (mem_parts p A.val).mp A.property
      exact ⟨Quotient.mk p v,Subtype.ext hv⟩
  exact (Fintype.card_coe (parts p)).symm.trans (Fintype.card_congr (Equiv.ofBijective f hf)).symm

lemma parts_sum_card (p : Setoid (Fin n)) : ∑A ∈ parts p, A.card=n := by
  have h := card_biUnion (s:=parts p) (t:=id) 
    (fun A hA B hB hAB => parts_disjoint p hA hB hAB)
  have hcov : (parts p).biUnion id=(univ : Finset (Fin n)) := by
    ext v
    simp only [mem_biUnion,mem_univ,iff_true]
    exact ⟨block p v,block_mem_parts p v,self_mem_block p v⟩
  rw [hcov,card_univ,Fintype.card_fin] at h
  exact h.symm

lemma block_eq_of_part {p : Setoid (Fin n)} {S : Finset (Fin n)}
    (hS : S ∈ parts p) {v : Fin n} (hv : v ∈ S) : S=block p v := by
  obtain ⟨w,rfl⟩ := (mem_parts p S).mp hS
  exact (block_eq_iff p w v).mpr ((mem_block p w v).mp hv)

lemma internal_partition_accounting (G : MultiGraph n m) (x : Fin m → ℝ)
    (p : Setoid (Fin n)) :
    (∑S ∈ parts p, ∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), x e)+
      capacity G.left G.right x p = ∑e, x e := by
  simp only [sum_filter,capacity]
  rw [sum_comm,←sum_add_distrib]
  apply sum_congr rfl
  intro e he
  have hi : (∑S ∈ parts p, if G.left e ∈ S ∧ G.right e ∈ S then x e else 0)=
      if p (G.left e) (G.right e) then x e else 0 := by
    rw [sum_eq_single (block p (G.left e))]
    · simp only [self_mem_block,mem_block,true_and]
    · intro S hS hSne
      apply ite_eq_right
      rintro ⟨hl,hr⟩
      exact hSne (block_eq_of_part hS hl)
    · intro h
      exact (h (block_mem_parts p (G.left e))).elim
  rw [hi,crossingIndicator]
  split_ifs <;> ring

lemma sum_root_budget {S : Finset (Fin n)} {r : Fin n} (hr : r ∈ S) (qbar ε : ℝ) :
    (∑v ∈ S, if v=r then ε else qbar) = qbar*((S.card:ℝ)-1)+ε := by
  have he (v : Fin n) : (if v=r then ε else qbar) =
      (if v=r then ε-qbar else 0)+qbar := by split_ifs <;> ring
  simp only [he,sum_add_distrib,sum_ite_eq',hr,ite_true, if_true,sum_const,nsmul_eq_mul]
  ring

lemma internal_flow_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε)
    (S : Finset (Fin n)) (hS : S.Nonempty) :
    (∑e ∈ univ.filter (fun e => G.left e ∈ S ∧ G.right e ∈ S), F.x e) ≤
      qbar*((S.card:ℝ)-1)+ε := by
  obtain ⟨r,hr⟩ := hS
  calc
    _ ≤ ∑v ∈ S, out G (F.a r) (F.b r) v :=
      internal_le_out G (fun e => (hF.2.1 r e).1) (fun e => (hF.2.1 r e).2.1)
        (fun e => (hF.2.1 r e).2.2) S
    _ ≤ ∑v ∈ S, if v=r then ε else qbar := sum_le_sum fun v _ => hF.2.2.1 r v
    _ = _ := sum_root_budget hr qbar ε

lemma flow_partition_bound (G : MultiGraph n m) (c : Fin m → ℝ) {qbar ε : ℝ}
    {F : FlowPoint n m} (hF : F.Feasible G c qbar ε) (p : Setoid (Fin n)) :
    qbar*((partCount p:ℝ)-1)-ε*((partCount p:ℝ)+1) ≤ capacity G.left G.right c p := by
  have hi := sum_le_sum (s:=parts p) (fun S hS => internal_flow_bound G c hF S
    ((parts_partition p).1 S hS).1)
  have hs : (∑S ∈ parts p, (qbar*((S.card:ℝ)-1)+ε))=
      qbar*((n:ℝ)-partCount p)+ε*partCount p := by
    simp only [mul_sub,mul_one,sum_add_distrib,sum_sub_distrib,←mul_sum,sum_const,nsmul_eq_mul]
    rw [←Nat.cast_sum,parts_sum_card,parts_card]
    ring
  rw [hs] at hi
  have hcross : capacity G.left G.right F.x p ≤ capacity G.left G.right c p :=
    sum_le_sum fun e _ => mul_le_mul_of_nonneg_right (hF.1 e).2 (crossingIndicator_nonneg _ _ _)
  have htotal := hF.2.2.2
  have haccount := internal_partition_accounting G F.x p
  linarith

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

end
end AlgorithmicThinTrees.Orientations
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Iteration
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation iteration. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma continuation_ramp_lower_of_le (G : MultiGraph n m) (hn : 0 < n)
    (hconn : G.Connected univ)
    {X Y : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ metricDomain G) (hY : Y ∈ metricDomain G)
    {s t κ : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    (u y : Fin m → ℝ) (hur : ∀e, u e ≤ ramp G s X e) (hy : ∀e, 0 ≤ y e)
    (hresp : ∀e, 0 < u e →
      (6*s*y e) • vecMulVec (G.incidence e) (G.incidence e) ≤ Y) :
    (1-t) • X+t • Y ∈ metricDomain G ∧ ∀e,
      lowerCapacity κ t (u e) (y e) ≤
        ramp G ((1+t)*s) ((1-t) • X+t • Y) e+κ := by
  have hnext := domain_convex G hX hY (by linarith : 0 ≤ 1-t) ht (by ring : 1-t+t=1)
  refine ⟨hnext,?_⟩
  intro e
  by_cases ha : 0 < u e
  · rw [lowerCapacity,ite_eq_left ha]
    have har : 0 < ramp G s X e := ha.trans_le (hur e)
    have hr := continuation_reciprocal G hn (domain_positive G hn hconn hX)
      hs ht ht1 (hy e) e (hresp e ha) (domain_positive G hn hconn hnext)
    have hscalar := ramp_scalar_lower (ramp_active G har).1 ht ht1
      (cappedParameter_le_two G s X e) (hy e) hr
    change min 1 (ramp G s X e+t*(5*y e-4)) ≤
      ramp G ((1+t)*s) ((1-t) • X+t • Y) e at hscalar
    have hh := (min_le_min_left (1:ℝ) (show u e+t*(5*y e-4) ≤ ramp G s X e+t*(5*y e-4) by linarith only [hur e])).trans hscalar
    linarith only [hh]
  · rw [lowerCapacity,ite_eq_right ha]
    linarith only [ramp_nonneg G ((1+t)*s) ((1-t) • X+t • Y) e]

lemma StepFree.nextCapacity_nonneg (x : StepFree n m) (κ : ℝ) (u : Fin m → ℝ) (e : Fin m) :
    0 ≤ x.nextCapacity κ u e := le_max_left _ _

lemma StepFree.nextCapacity_bounds (H : MultiGraph n m)
    {s κ t : ℝ} {u : Fin m → ℝ} {x : StepFree n m}
    (hx : x ∈ stepCore H s κ t u) (e : Fin m) :
    x.nextCapacity κ u e ≤ 1 ∧ x.capacities κ u e ≤ x.nextCapacity κ u e+κ := by
  have he : x.capacities κ u e ≤ κ+1 := by
    unfold StepFree.capacities
    split_ifs
    · exact (hx.2.2.2.2.1 e).2
    · linarith
  refine ⟨max_le (by norm_num) (by linarith only [he]),?_⟩
  have hh := le_max_right (0:ℝ) (x.capacities κ u e-κ)
  change x.capacities κ u e ≤ max 0 (x.capacities κ u e-κ)+κ
  linarith only [hh]

theorem stepFeasible_update (H : MultiGraph n m) (hn : 0 < n) (hconn : H.Connected univ)
    {s κ t q : ℝ} (hs : 0 < s) (ht : 0 ≤ t) (ht1 : t ≤ 1/5)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ metricDomain H)
    (u : Fin m → ℝ) (hur : ∀e, u e ≤ ramp H s X e)
    {x : StepFree n m} (hx : x ∈ stepFeasible H s κ t q u) :
    (1-t) • X+t • x.matrix ∈ metricDomain H ∧
      (∀e, x.nextCapacity κ u e ≤ ramp H ((1+t)*s) ((1-t) • X+t • x.matrix) e) ∧
      (∀e, 0 ≤ x.nextCapacity κ u e ∧ x.nextCapacity κ u e ≤ 1) ∧
      ∀p, 0 ≤ slack H.left H.right (fun e => x.nextCapacity κ u e+κ) q p := by
  have had := stepCore_admissible H hn hx.1
  obtain ⟨hnew,hramp⟩ := continuation_ramp_lower_of_le H hn hconn hX had.1 hs ht ht1
    u x.y hur (fun e => (had.2.1 e).1) had.2.2
  refine ⟨hnew,?_,?_,?_⟩
  · intro e
    apply max_le (ramp_nonneg _ _ _ _)
    have hh := (stepCore_capacity_le H hx.1 e).trans (hramp e)
    linarith only [hh]
  · intro e
    exact ⟨x.nextCapacity_nonneg κ u e,(x.nextCapacity_bounds H hx.1 e).1⟩
  · intro p
    apply (hx.2 p).trans
    unfold slack capacity
    apply sub_le_sub_right
    apply sum_le_sum
    intro e _
    exact mul_le_mul_of_nonneg_right (x.nextCapacity_bounds H hx.1 e).2
      (crossingIndicator_nonneg _ _ _)

end AlgorithmicThinTrees.MetricTests

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma cast_qresponse (A : Matrix (Fin n) (Fin n) ℚ) :
    (qresponse A).map (fun a => (a:ℝ))=responseMatrix (A.map (fun a => (a:ℝ))) := by
  ext i j
  simp only [qresponse,Matrix.map_apply,Matrix.mul_apply,Rat.cast_sum,Rat.cast_mul,
    Matrix.smul_apply,Matrix.add_apply,Matrix.transpose_apply,smul_eq_mul,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,Rat.cast_add,cast_qproject,
    responseMatrix,centered]

lemma update_realMatrix (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) :
    (update H r g a).realMatrix=(1-continuationStep m) • a.realMatrix+
      continuationStep m • (rational (search H a.scale (target m r a.quality g) a.capacity)).real.matrix := by
  have hh := cast_qresponse (rawMatrix (search H a.scale (target m r a.quality g) a.capacity))
  ext i j
  change ((((1-stepQ m)*a.matrix i j+stepQ m*_) : ℚ) : ℝ)=_
  simp only [Rat.cast_add,Rat.cast_mul,Rat.cast_sub,Rat.cast_one,cast_stepQ]
  have hhi := congrFun (congrFun hh i) j
  exact congrArg (fun z : ℝ => (1-continuationStep m)*a.realMatrix i j+continuationStep m*z) hhi

lemma update_capacity (H : MultiGraph n m) (r : ℕ) (g : ℚ) (a : State n m) (e : Fin m) :
    ((update H r g a).capacity e:ℝ)=
      (rational (search H a.scale (target m r a.quality g) a.capacity)).real.nextCapacity
        (continuationBaseline m) (fun f => (a.capacity f:ℝ)) e := by
  simp only [update,StepFree.nextCapacity,StepFree.capacities]
  by_cases he : 0 < a.capacity e
  · have heR : 0 < (a.capacity e:ℝ) := by exact_mod_cast he
    simp only [ite_eq_left he,ite_eq_left heR,Rat.cast_max,Rat.cast_zero,Rat.cast_sub,cast_baselineQ]
    rfl
  · have heR : ¬0 < (a.capacity e:ℝ) := by exact_mod_cast he
    simp only [ite_eq_right he,ite_eq_right heR,Rat.cast_zero,sub_self,max_self]

lemma update_invariant (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (r : ℕ) (g : ℚ) (a : State n m) (ha : Invariant H a)
    (hv : (rational (search H a.scale (target m r a.quality g) a.capacity)).real ∈
      stepFeasible H (a.scale:ℝ) (continuationBaseline m) (continuationStep m)
        ((a.quality:ℝ)-2*(g:ℝ)*r*continuationStep m) (fun e => (a.capacity e:ℝ))) :
    Invariant H (update H r g a) := by
  have ht := (continuation_parameters m).2.2.2.1
  have ht1 := (continuation_parameters m).2.2.2.2.1
  have hh := stepFeasible_update H hn hc ha.1 ht (by linarith : continuationStep m ≤ 1/5)
    ha.2.1 (fun e => (a.capacity e:ℝ)) (fun e => (ha.2.2.1 e).2.2) hv
  have hs : ((update H r g a).scale:ℝ)=(1+continuationStep m)*(a.scale:ℝ) := by
    simp only [update,Rat.cast_mul,Rat.cast_add,Rat.cast_one,cast_stepQ]
  have hq : ((update H r g a).quality:ℝ)=(a.quality:ℝ)-2*(g:ℝ)*r*continuationStep m := by
    simp only [update,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,cast_stepQ]
  refine ⟨?_,?_,?_,?_⟩
  · rw [hs]
    exact mul_pos (by linarith only [ht]) ha.1
  · rw [update_realMatrix]
    exact hh.1
  · intro e
    rw [update_capacity,hs,update_realMatrix]
    exact ⟨(hh.2.2.1 e).1,(hh.2.2.1 e).2,hh.2.1 e⟩
  · simpa only [update_capacity,hq] using hh.2.2.2

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Schedule
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_baselineQ _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.cast_stepQ
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation schedule. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma nthRoot_le_real_root (d r : ℕ) (hd : 0 < d) :
    (Nat.nthRoot d r:ℝ) ≤ (r:ℝ)^(1/(d:ℝ)) := by
  rw [one_div,Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.pow_nthRoot_le (n:=d) (a:=r) (.inl hd.ne')

lemma real_root_lt_nthRoot_add (d r : ℕ) (hd : 0 < d) :
    (r:ℝ)^(1/(d:ℝ)) < (Nat.nthRoot d r:ℝ)+1 := by
  rw [one_div,Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg _) (by positivity)
    (Nat.cast_pos.mpr hd),Real.rpow_natCast]
  exact_mod_cast Nat.lt_pow_nthRoot_add_one hd.ne' r

lemma nthRoot_pos (d r : ℕ) (hd : 0 < d) (hr : 0 < r) :
    1 ≤ Nat.nthRoot d r := by
  rw [Nat.le_nthRoot_iff hd.ne',one_pow]
  exact hr

lemma gain_bounds (r : ℕ) (hr : 0 < r) :
    (r:ℝ)^(-1/8:ℝ) ≤ (gain r:ℝ) ∧ (gain r:ℝ) ≤ 2*(r:ℝ)^(-1/8:ℝ) := by
  have hroot := nthRoot_le_real_root 8 r (by norm_num)
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hu1 : (1:ℝ) ≤ Nat.nthRoot 8 r := by exact_mod_cast nthRoot_pos 8 r (by norm_num) hr
  have hup := real_root_lt_nthRoot_add 8 r (by norm_num)
  have hp : 0 < (r:ℝ)^(1/8:ℝ) := Real.rpow_pos_of_pos hr0 _
  have he : (r:ℝ)^(-1/8:ℝ)=1/((r:ℝ)^(1/8:ℝ)) := by
    simp only [show (-1/8:ℝ)= -(1/8:ℝ) by ring,Real.rpow_neg hr0.le,one_div]
  simp only [Nat.cast_ofNat] at hroot hup
  rw [he]
  have hg : (gain r:ℝ)=1/(Nat.nthRoot 8 r:ℝ) := by simp [gain]
  rw [hg]
  constructor
  · exact one_div_le_one_div_of_le (by linarith only [hu1]) hroot
  · have hu0 : 0 < (Nat.nthRoot 8 r:ℝ) := by linarith only [hu1]
    apply (div_le_iff₀ hu0).mpr
    rw [show 2*(1/((r:ℝ)^(1/8:ℝ)))*(Nat.nthRoot 8 r:ℝ)=
      (2*(Nat.nthRoot 8 r:ℝ))/((r:ℝ)^(1/8:ℝ)) by ring]
    apply (le_div_iff₀ hp).mpr
    linarith only [hu1,hup]

lemma blockLength_step (m : ℕ) : (blockLength m:ℝ)*continuationStep m=1 := by
  unfold blockLength continuationStep continuationBaseline
  push_cast
  field_simp

lemma blocks_le_root (r : ℕ) : (blocks r:ℝ) ≤ (r:ℝ)^(1/16:ℝ) :=
  nthRoot_le_real_root 16 r (by norm_num)

lemma schedule_loss_bound (r : ℕ) (hr : 0 < r) :
    2*(gain r:ℝ)*(blocks r:ℝ) ≤ 4*(r:ℝ)^(-1/16:ℝ) := by
  have hr0 : 0 < (r:ℝ) := Nat.cast_pos.mpr hr
  have hg := (gain_bounds r hr).2
  have hU := blocks_le_root r
  have hh := mul_le_mul hg hU (Nat.cast_nonneg _) (by positivity : 0 ≤ 2*(r:ℝ)^(-1/8:ℝ))
  have he : (r:ℝ)^(-1/8:ℝ)*(r:ℝ)^(1/16:ℝ)=(r:ℝ)^(-1/16:ℝ) := by
    rw [←Real.rpow_add hr0]
    congr 1
    norm_num
  rw [mul_assoc,he] at hh
  linarith only [hh]

lemma large_blocks (r : ℕ) (hr : 64^16 ≤ r) : 64 ≤ blocks r := by
  exact (Nat.le_nthRoot_iff (by norm_num : 16≠0)).mpr hr

lemma large_gain (r : ℕ) (hr : 64^16 ≤ r) : 3 ≤ (gain r:ℝ)*r := by
  have hu2 : 2 ≤ Nat.nthRoot 8 r := (Nat.le_nthRoot_iff (by norm_num : 8≠0)).mpr
    (le_trans (by norm_num : 2^8 ≤ 64^16) hr)
  have hpow : 3*Nat.nthRoot 8 r ≤ (Nat.nthRoot 8 r)^8 := by
    have hh : 3 ≤ (Nat.nthRoot 8 r)^7 := (by norm_num : 3 ≤ 2^7).trans (Nat.pow_le_pow_left hu2 7)
    calc
      _ ≤ (Nat.nthRoot 8 r)^7*Nat.nthRoot 8 r := Nat.mul_le_mul_right _ hh
      _ = _ := (pow_succ _ _).symm
  have hh := hpow.trans (Nat.pow_nthRoot_le (n:=8) (a:=r) (by left; norm_num))
  have hreal : (3:ℝ)*Nat.nthRoot 8 r ≤ r := by exact_mod_cast hh
  have hp : 0 < (Nat.nthRoot 8 r:ℝ) := by exact_mod_cast (show 0 < Nat.nthRoot 8 r by omega)
  simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
  rw [one_div,inv_mul_eq_div,le_div_iff₀ hp]
  exact hreal

lemma large_schedule_loss (r : ℕ) (hr : 64^16 ≤ r) :
    2*(gain r:ℝ)*(blocks r:ℝ) ≤ 1/4 := by
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num : 0 < 64^16) hr
  have hU : (64:ℝ) ≤ (blocks r:ℝ) := by exact_mod_cast large_blocks r hr
  have hp := hU.trans (blocks_le_root r)
  have hi : (r:ℝ)^(-1/16:ℝ) ≤ 1/64 := by
    rw [show (-1/16:ℝ)= -(1/16:ℝ) by ring,Real.rpow_neg (Nat.cast_nonneg _),←one_div]
    exact one_div_le_one_div_of_le (by norm_num) hp
  linarith only [schedule_loss_bound r hr0,hi]

lemma block_growth (m : ℕ) : 2 ≤ (1+continuationStep m)^(blockLength m) := by
  have ht := (continuation_parameters m).2.2.2.1
  have hh := one_add_mul_le_pow (by linarith : -2 ≤ continuationStep m) (blockLength m)
  rw [blockLength_step] at hh
  norm_num only [one_add_one_eq_two] at hh
  exact hh

lemma fourth_power_le_two_pow (U : ℕ) (hU : 64 ≤ U) : 2*(U+1)^4 ≤ 2^U := by
  induction U,hU using Nat.le_induction with
  | base => norm_num
  | succ U hU ih =>
    have hstep : (U+2)^4 ≤ 2*(U+1)^4 := by

      have hh : 16*(U+2) ≤ 17*(U+1) := by omega
      have hpow := Nat.pow_le_pow_left hh 4
      rw [mul_pow,mul_pow] at hpow
      norm_num only [Nat.reducePow] at hpow
      omega
    rw [pow_succ 2 U]
    have he : U+1+1=U+2 := by omega
    rw [he]
    omega

lemma schedule_growth (m r : ℕ) (hr : 64^16 ≤ r) :
    (r:ℝ)^(1/4:ℝ) ≤ (1+continuationStep m)^(scheduleLength m r)/2 := by
  have hU := large_blocks r hr
  have hpow := fourth_power_le_two_pow (blocks r) hU
  have hg := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (block_growth m) (blocks r)
  rw [←pow_mul,←scheduleLength] at hg
  have hroot : (r:ℝ)^(1/4:ℝ) ≤ ((blocks r:ℝ)+1)^4 := by
    have hh := Nat.lt_pow_nthRoot_add_one (by norm_num : 16≠0) r
    have hc : (r:ℝ) ≤ ((blocks r:ℝ)+1)^16 := by exact_mod_cast hh.le
    rw [one_div,Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) (by positivity) (by norm_num : (0:ℝ)<4)]
    simpa only [Real.rpow_ofNat,←pow_mul,Nat.reduceMul] using hc
  have hc : 2*((blocks r:ℝ)+1)^4 ≤ (2:ℝ)^(blocks r) := by exact_mod_cast hpow
  linarith only [hg,hroot,hc]

lemma scheduleLength_step (m r : ℕ) : (scheduleLength m r:ℝ)*continuationStep m=blocks r := by
  simp only [scheduleLength,Nat.cast_mul]
  calc
    _ = (blocks r:ℝ)*((blockLength m:ℝ)*continuationStep m) := by ring
    _ = _ := by rw [blockLength_step,mul_one]

lemma cost_le_schedule (m r i : ℕ) (hi : i ≤ scheduleLength m r) :
    (i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) ≤ 2*(gain r:ℝ)*(blocks r:ℝ)*r := by
  have hg : 0 ≤ (gain r:ℝ) := by simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] <;> positivity
  have hh := mul_le_mul_of_nonneg_right (show (i:ℝ) ≤ scheduleLength m r by exact_mod_cast hi)
    (continuation_parameters m).2.2.2.1
  rw [scheduleLength_step] at hh
  have hmul := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 2*(gain r:ℝ)*r)
  nlinarith only [hmul]

lemma running_quality_lower (m r i : ℕ) (hr : 64^16 ≤ r) (hi : i ≤ scheduleLength m r) :
    3*(r:ℝ)/4 ≤ (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) := by
  have hh := cost_le_schedule m r i hi
  have hl := mul_le_mul_of_nonneg_right (large_schedule_loss r hr) (Nat.cast_nonneg (α:=ℝ) r)
  linarith only [hh,hl]

lemma running_quality_loss (m r i : ℕ) (hr : 0 < r) (hi : i ≤ scheduleLength m r) :
    (1-4*(r:ℝ)^(-1/16:ℝ))*r ≤ (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) := by
  have hh := cost_le_schedule m r i hi
  have hl := mul_le_mul_of_nonneg_right (schedule_loss_bound r hr) (Nat.cast_nonneg (α:=ℝ) r)
  nlinarith only [hh,hl]

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Start
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation start. -/

section

namespace AlgorithmicThinTrees.MetricTests
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma rankOne_le_laplacian (H : MultiGraph n m) (e : Fin m) :
    vecMulVec (H.incidence e) (H.incidence e) ≤ H.laplacian univ := by
  apply Finset.single_le_sum _ (mem_univ e)
  intro f _
  apply Matrix.nonneg_iff_posSemidef.mpr
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (H.incidence f)

lemma initial_resistance_le_one (H : MultiGraph n m) (hn : 0 < n)
    (hc : H.Connected univ) (e : Fin m) : resistance H (H.laplacian univ) e ≤ 1 := by
  have hh := (centered_resistance_order hn (domain_positive H hn hc (laplacian_mem_domain H))
    (incidence_sum H e) (by norm_num : (0:ℝ)<1)).mp
    (by simpa only [one_smul] using Matrix.le_iff.mp (rankOne_le_laplacian H e))
  simpa only [one_mul,MetricTests.resistance] using hh

lemma initial_ramp (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (e : Fin m) : ramp H (1/2) (H.laplacian univ) e=1 := by
  have hR := initial_resistance_le_one H hn hc e
  have hRp := centered_resistance_pos H hn (domain_positive H hn hc (laplacian_mem_domain H)) e
  have hi : 2 ≤ ((1/2)*resistance H (H.laplacian univ) e)⁻¹ := by
    rw [←one_div]
    apply (le_div_iff₀ (by positivity : 0 < (1/2:ℝ)*resistance H (H.laplacian univ) e)).mpr
    linarith only [hR]
  unfold ramp cappedParameter
  rw [min_eq_left hi]
  norm_num

lemma packing_connected (H : MultiGraph n m) {r : ℕ} (hr : 0 < r)
    (hp : H.TreePackable univ r) : H.Connected univ := by
  intro S hS hS'
  apply card_pos.mp
  exact hr.trans_le (H.treePackable_edgeConnected hp S hS hS')

lemma packing_count_le_edges (H : MultiGraph n m) (hn : 2 ≤ n) {r : ℕ}
    (hp : H.TreePackable univ r) : r ≤ m := by
  let v : Fin n := ⟨0,by omega⟩
  have hS : ({v}:Finset (Fin n))≠univ := by
    intro he
    have hh := congrArg Finset.card he
    simp only [card_singleton,card_univ,Fintype.card_fin] at hh
    omega
  exact (H.treePackable_edgeConnected hp {v} (singleton_nonempty v) hS).trans
    (by simpa only [Fintype.card_fin] using Finset.card_le_univ (H.cut univ {v}))

lemma packing_partition_slack (H : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hp : H.TreePackable univ r) (κ : ℝ) (hκ : 0 ≤ κ) :
    ∀p, 0 ≤ slack H.left H.right (fun _ => 1+κ) r p := by
  obtain ⟨F,hF⟩ := Orientations.packed_exact_flow H hn hp
  have hf := hF.mono (fun e => show (1:ℝ) ≤ 1+κ by linarith only [hκ])
  have hfe : F.Feasible H (fun _ => 1+κ) r 0 := by
    refine ⟨hf.1,fun r e => ⟨(hf.2.1 r e).1,(hf.2.1 r e).2.1,(hf.2.1 r e).2.2.le⟩,
      fun r v => (hf.2.2.1 r v).le,?_⟩
    simpa only [sub_zero] using hf.2.2.2.ge
  intro p
  have hh := Orientations.flow_partition_bound H (fun _ => 1+κ) hfe p
  simpa only [zero_mul,sub_zero,sub_nonneg,slack] using hh

end AlgorithmicThinTrees.MetricTests

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma initial_invariant (H : MultiGraph n m) (hn : 0 < n) {r : ℕ}
    (hr : 0 < r) (hp : H.TreePackable univ r) : Invariant H (initial H r) := by
  have hc := packing_connected H hr hp
  have hm : (initial H r).realMatrix=H.laplacian univ := by
    ext i j
    exact cast_qlap H i j
  refine ⟨by norm_num [initial],hm.symm ▸ laplacian_mem_domain H,?_,?_⟩
  · intro e
    have hs : ((initial H r).scale:ℝ)=1/2 := by norm_num [initial]
    rw [hm,hs,initial_ramp H hn hc e]
    norm_num [initial]
  · simpa only [initial,Rat.cast_one,Rat.cast_natCast] using
      packing_partition_slack H hn hp (continuationBaseline m) (continuation_parameters m).1.le

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Continuation_Loop
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.MetricTests.RationalStep.Stack.poly_meshView
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Continuation loop. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma stateAt_zero (H : MultiGraph n m) (r : ℕ) : stateAt H r 0=initial H r := rfl

lemma stateAt_succ (H : MultiGraph n m) (r i : ℕ) :
    stateAt H r (i+1)=advance H r (stateAt H r i) := Function.iterate_succ_apply' _ _ _

lemma active_scale_bound {a : State n m} {r : ℕ} (ha : 0 < (a.scale:ℝ))
    (hactive : a.scale^4 < (r:ℚ)) : (a.scale:ℝ) ≤ (r:ℝ)^(1/4:ℝ) := by
  rw [one_div,Real.le_rpow_inv_iff_of_pos ha.le (Nat.cast_nonneg _) (by norm_num : (0:ℝ)<4),Real.rpow_ofNat]
  exact_mod_cast hactive.le

lemma advance_quality (H : MultiGraph n m) (r : ℕ) (a : State n m) :
    (a.quality:ℝ)-2*(gain r:ℝ)*r*continuationStep m ≤ ((advance H r a).quality:ℝ) ∧
    ((advance H r a).quality:ℝ) ≤ (a.quality:ℝ) := by
  have hg : 0 ≤ (gain r:ℝ) := by simp only [gain,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] <;> positivity
  have ht := (continuation_parameters m).2.2.2.1
  have hc : 0 ≤ 2*(gain r:ℝ)*r*continuationStep m := by positivity
  unfold advance
  split_ifs <;> (try simp only [update,Rat.cast_sub,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_natCast,cast_stepQ]) <;>
    constructor <;> linarith only [hc]

lemma stateAt_quality (H : MultiGraph n m) (r i : ℕ) :
    (r:ℝ)-(i:ℝ)*(2*(gain r:ℝ)*r*continuationStep m) ≤ ((stateAt H r i).quality:ℝ) ∧
    ((stateAt H r i).quality:ℝ) ≤ r := by
  induction i with
  | zero => simp [stateAt_zero,initial]
  | succ i ih =>
    rw [stateAt_succ]
    have hh := advance_quality H r (stateAt H r i)
    push_cast
    constructor <;> nlinarith only [ih.1,ih.2,hh.1,hh.2]

lemma scale_dichotomy (H : MultiGraph n m) (r i : ℕ) :
    (r:ℚ) ≤ (stateAt H r i).scale^4 ∨
    (stateAt H r i).scale=(1+stepQ m)^i/2 := by
  induction i with
  | zero => exact Or.inr (by simp [stateAt_zero,initial])
  | succ i ih =>
    rw [stateAt_succ]
    rcases ih with ih|ih
    · exact Or.inl (by simpa only [advance,ite_eq_right (not_lt.mpr ih)] using ih)
    · by_cases ha : (stateAt H r i).scale^4 < (r:ℚ)
      · right
        rw [advance,ite_eq_left ha]
        simp only [update,ih]
        rw [pow_succ]
        ring
      · left
        simpa only [advance,ite_eq_right ha] using not_lt.mp ha

lemma extract_scale_bound (H : MultiGraph n m) (r : ℕ) (hr : 64^16 ≤ r)
    (hp : 0 < ((extractState H r).scale:ℝ)) :
    (r:ℝ)^(1/4:ℝ) ≤ ((extractState H r).scale:ℝ) := by
  obtain h|h := scale_dichotomy H r (scheduleLength m r)
  · rw [one_div,Real.rpow_inv_le_iff_of_pos (Nat.cast_nonneg _) hp.le (by norm_num : (0:ℝ)<4),Real.rpow_ofNat]
    exact_mod_cast h
  · have he : ((extractState H r).scale:ℝ)=(1+continuationStep m)^(scheduleLength m r)/2 := by
      simpa only [Rat.cast_div,Rat.cast_pow,Rat.cast_add,Rat.cast_one,Rat.cast_ofNat,cast_stepQ,extractState] using congrArg (fun q : ℚ => (q:ℝ)) h
    rw [he]
    exact schedule_growth m r hr

theorem stateAt_invariant : ∀r : ℕ, 2^2048 ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      ∀i, i ≤ scheduleLength m r → Invariant H (stateAt H r i) := by
  have hresponse := uniform_search_response_explicit
  have hR : 64^16 ≤ 2^2048 := by
    rw [show (64:ℕ)=2^6 by rfl, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  intro r hr n m H hn hpack i hi
  have hr0 : 0 < r := (by norm_num : 0 < 64^16).trans_le (hR.trans hr)
  have hrlarge : 64^16 ≤ r := hR.trans hr
  have hconn := packing_connected H hr0 hpack
  have hrm := packing_count_le_edges H hn hpack
  induction i with
  | zero => exact initial_invariant H (by omega) hr0 hpack
  | succ i ih =>
    have hii : i ≤ scheduleLength m r := by omega
    have ha := ih hii
    rw [stateAt_succ]
    by_cases hactive : (stateAt H r i).scale^4 < (r:ℚ)
    · rw [advance,ite_eq_left hactive]
      apply update_invariant H (by omega) hconn r (gain r) (stateAt H r i) ha
      apply hresponse r (hr) n m H hn hconn hrm
        (stateAt H r i).capacity (fun e => (ha.2.2.1 e).1) (fun e => (ha.2.2.1 e).2.1)
        (stateAt H r i).scale (stateAt H r i).quality (gain r) ha.1
        (active_scale_bound ha.1 hactive)
        ((running_quality_lower m r i hrlarge hii).trans (stateAt_quality H r i).1)
        (stateAt_quality H r i).2 (gain_bounds r hr0).1 (gain_bounds r hr0).2
        (large_gain r hrlarge) ha.2.2.2
    · simpa only [advance,ite_eq_right hactive] using ha

theorem extractState_correct : ∀r : ℕ, 2^2048 ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      Invariant H (extractState H r) ∧
      (r:ℝ)^(1/4:ℝ) ≤ ((extractState H r).scale:ℝ) ∧
      (1-4*(r:ℝ)^(-1/16:ℝ))*r ≤ ((extractState H r).quality:ℝ) ∧
      ((extractState H r).quality:ℝ) ≤ r := by
  have hcorrect := stateAt_invariant
  have hR : 64^16 ≤ 2^2048 := by
    rw [show (64:ℕ)=2^6 by rfl, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  intro r hr n m H hn hp
  have hi := hcorrect r hr n m H hn hp (scheduleLength m r) le_rfl
  have hr0 : 0 < r := (by norm_num : 0 < 64^16).trans_le (hR.trans hr)
  refine ⟨hi,extract_scale_bound H r (hR.trans hr) hi.1,?_,(stateAt_quality H r _).2⟩
  exact (running_quality_loss m r _ hr0 le_rfl).trans (stateAt_quality H r _).1

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

section
-- module Solutions.OAIQ241_TT.ThinTrees_Sparsification_ShortcutExtraction
attribute [-simp] _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_left _root_.OAI.AlgorithmicThinTrees.BinaryInput.labelEquiv_right
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Shortcut extraction. -/

section

namespace AlgorithmicThinTrees.MetricTests.RationalStep
open Matrix Finset StrongThinTree StrongThinTree.MultiGraph Partitions
open scoped MatrixOrder
variable {n m : ℕ}

lemma active_mem (a : State n m) (e : Fin m) : e ∈ a.active ↔ 0 < (a.capacity e:ℝ) := by
  simp only [State.active,mem_filter,mem_univ,true_and]
  exact_mod_cast Iff.rfl

lemma baseline_total_lt_one (m : ℕ) : (m:ℝ)*continuationBaseline m < 1 := by
  unfold continuationBaseline
  rw [mul_one_div]
  exact (div_lt_one (by positivity)).mpr (by linarith)

lemma sum_capacity_le_active (H : MultiGraph n m) (a : State n m)
    (hu : ∀e, 0 ≤ (a.capacity e:ℝ) ∧ (a.capacity e:ℝ) ≤ 1)
    (p : Fin n → Fin n) :
    capacity H.left H.right (fun e => (a.capacity e:ℝ)+continuationBaseline m) (Setoid.ker p) <
      ((H.crossing a.active p).card:ℝ)+1 := by
  classical
  rw [capacity_eq_sum,Orientations.crossing_ker,sum_add_distrib]
  have hmain : (∑e ∈ H.crossing univ p, (a.capacity e:ℝ)) ≤ (H.crossing a.active p).card := by
    have he : H.crossing a.active p=(H.crossing univ p).filter (fun e => 0 < a.capacity e) := by
      ext e
      simp only [MultiGraph.crossing,State.active,mem_filter,mem_univ,true_and]
      tauto
    rw [he,←Finset.sum_boole]
    apply sum_le_sum
    intro e _
    by_cases h : 0 < a.capacity e
    · simpa only [h,ite_true, if_true] using (hu e).2
    · have hh : ¬0 < (a.capacity e:ℝ) := by exact_mod_cast h
      simpa only [h,ite_false, if_false] using not_lt.mp hh
  have hcount : (H.crossing univ p).card ≤ m := (card_le_card (filter_subset _ _)).trans_eq (card_fin _)
  have hbase : (∑_e ∈ H.crossing univ p, continuationBaseline m) < 1 := by
    simp only [sum_const,nsmul_eq_mul]
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (continuation_parameters m).1.le).trans_lt
      (baseline_total_lt_one m)
  linarith only [hmain,hbase]

lemma active_packable (H : MultiGraph n m) (hn : 0 < n) (a : State n m)
    (ha : Invariant H a) {q : ℕ} (hq : 0 < q) (hqQ : (q:ℝ) ≤ (a.quality:ℝ)-1) :
    H.TreePackable a.active q := by
  apply H.partition_criterion_sufficient a.active hq hn
  intro p
  by_cases hp : partitionSize p ≤ 1
  · have he : partitionSize p-1=0 := by omega
    simp only [he,mul_zero,Nat.zero_le]
  · have hp2 : 2 ≤ partitionSize p := by omega
    have hslack := ha.2.2.2 (Setoid.ker p)
    rw [slack,sub_nonneg,Orientations.partCount_ker] at hslack
    have hcap := sum_capacity_le_active H a (fun e => ⟨(ha.2.2.1 e).1,(ha.2.2.1 e).2.1⟩) p
    have hd : (1:ℝ) ≤ (partitionSize p:ℝ)-1 := by
      have hh : (2:ℝ) ≤ partitionSize p := by exact_mod_cast hp2
      linarith only [hh]
    have hm := mul_le_mul_of_nonneg_right hqQ (by linarith : (0:ℝ) ≤ (partitionSize p:ℝ)-1)
    have hnat : ((q*(partitionSize p-1):ℕ):ℝ)=(q:ℝ)*((partitionSize p:ℝ)-1) := by
      rw [Nat.cast_mul,Nat.cast_sub (by omega : 1 ≤ partitionSize p),Nat.cast_one]
    have hh : ((q*(partitionSize p-1):ℕ):ℝ) ≤ ((H.crossing a.active p).card:ℝ) := by
      rw [hnat]
      nlinarith only [hm,hcap,hslack,hd]
    exact_mod_cast hh

lemma packingTarget_lower (a : State n m) :
    (a.quality:ℝ)-2 ≤ (a.packingTarget:ℝ) := by
  have hh := Nat.lt_floor_add_one (a.quality-1)
  have hc : (a.quality:ℝ)-1 < (a.packingTarget:ℝ)+1 := by
    exact_mod_cast hh
  linarith only [hc]

lemma packingTarget_upper (a : State n m) (hq : 1 ≤ (a.quality:ℝ)) :
    (a.packingTarget:ℝ) ≤ (a.quality:ℝ)-1 := by
  have hi : (0:ℚ) ≤ a.quality-1 := by exact_mod_cast (sub_nonneg.mpr hq)
  exact_mod_cast Nat.floor_le hi

lemma packingTarget_pos (a : State n m) (hq : 2 ≤ (a.quality:ℝ)) : 0 < a.packingTarget := by
  apply Nat.floor_pos.mpr
  exact_mod_cast (show (1:ℝ) ≤ (a.quality:ℝ)-1 by linarith only [hq])

lemma active_resistance (H : MultiGraph n m) (hn : 0 < n) (hc : H.Connected univ)
    (a : State n m) (ha : Invariant H a) (e : Fin m) (he : e ∈ a.active) :
    resistance H a.realMatrix e < (a.scale:ℝ)⁻¹ := by
  have hX := domain_positive H hn hc ha.2.1
  have hR := centered_resistance_pos H hn hX e
  have hramp := (active_mem a e).mp he |>.trans_le (ha.2.2.1 e).2.2
  have hp := (ramp_active H hramp).1
  have hrec : 1 < ((a.scale:ℝ)*resistance H a.realMatrix e)⁻¹ :=
    hp.trans_le (min_le_right _ _)
  have hprod := (inv_lt_inv₀ (by norm_num : (0:ℝ)<1) (mul_pos ha.1 hR)).mp
    (by simpa using hrec)
  rw [←one_div]
  apply (lt_div_iff₀ ha.1).mpr
  nlinarith only [hprod]

lemma rounding_absorbed (r : ℕ) (hr : 1 ≤ r) : 1 ≤ (r:ℝ)^(-1/16:ℝ)*r := by
  have hp : (0:ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have he : (r:ℝ)^(-1/16:ℝ)*r=(r:ℝ)^(15/16:ℝ) := by
    conv_lhs => arg 2; rw [←Real.rpow_one (r:ℝ)]
    rw [←Real.rpow_add hp]
    norm_num
  rw [he]
  exact Real.one_le_rpow (by exact_mod_cast hr) (by norm_num)

theorem shortcut_correct_explicit_oai : ∀r : ℕ, 2^2048 ≤ r →
    ∀(n m : ℕ) (H : MultiGraph n m), 2 ≤ n → H.TreePackable univ r →
      let a := extractState H r
      a.realMatrix ∈ metricDomain H ∧ H.TreePackable a.active a.packingTarget ∧
      0 < a.packingTarget ∧ a.packingTarget ≤ r ∧
      (1-6*(r:ℝ)^(-1/16:ℝ))*r ≤ (a.packingTarget:ℝ) ∧
      ∀e ∈ a.active, resistance H a.realMatrix e ≤ (r:ℝ)^(-1/4:ℝ) := by
  have hcorrect := extractState_correct
  have hR : 64^16 ≤ 2^2048 := by
    rw [show (64:ℕ)=2^6 by rfl, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) (by norm_num)
  intro r hr n m H hn hpack
  dsimp only
  have hrlarge : 64^16 ≤ r := hR.trans hr
  have hr3 : 3 ≤ r := (by norm_num : 3 ≤ 64^16).trans hrlarge
  have hr0 : 0 < r := by omega
  have hconn := packing_connected H hr0 hpack
  obtain ⟨ha,hscale,hlower,hupper⟩ := hcorrect r hr n m H hn hpack
  have hQ : 2 ≤ ((extractState H r).quality:ℝ) := by
    have hl := (running_quality_lower m r (scheduleLength m r) hrlarge le_rfl).trans
      (stateAt_quality H r (scheduleLength m r)).1
    change 3*(r:ℝ)/4 ≤ ((extractState H r).quality:ℝ) at hl
    have hrR : (3:ℝ) ≤ r := by exact_mod_cast hr3
    linarith only [hl,hrR]
  have hqpos := packingTarget_pos (extractState H r) hQ
  have hqupper := packingTarget_upper (extractState H r) (by linarith only [hQ])
  refine ⟨ha.2.1,active_packable H (by omega) (extractState H r) ha hqpos hqupper,hqpos,?_,?_,?_⟩
  · exact_mod_cast (show ((extractState H r).packingTarget:ℝ) ≤ r by linarith only [hqupper,hupper])
  · have hfloor := packingTarget_lower (extractState H r)
    have hrnd := rounding_absorbed r (by omega)
    nlinarith only [hfloor,hlower,hrnd]
  · intro e he
    have hres := active_resistance H (by omega) hconn (extractState H r) ha e he
    have hpow : 0 < (r:ℝ)^(1/4:ℝ) := Real.rpow_pos_of_pos (by exact_mod_cast hr0) _
    have hrec := inv_anti₀ hpow hscale
    have heq : ((r:ℝ)^(1/4:ℝ))⁻¹=(r:ℝ)^(-1/4:ℝ) := by
      rw [←Real.rpow_neg (Nat.cast_nonneg r)]
      congr 1
      norm_num
    exact hres.le.trans (heq ▸ hrec)

end AlgorithmicThinTrees.MetricTests.RationalStep
end

end OAI
end

theorem solution : type_of% @OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct_explicit_oai := @OAI.AlgorithmicThinTrees.MetricTests.RationalStep.shortcut_correct_explicit_oai
