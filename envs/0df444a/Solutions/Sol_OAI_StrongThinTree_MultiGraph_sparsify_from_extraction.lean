-- Prove2me | solution 1 for OAI.StrongThinTree.MultiGraph.sparsify_from_extraction
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T17:08:12.196307+00:00
-- url     : https://prove2.me/submissions/d5bab36e-31e6-42cb-8e1f-d61a474f71c2

import Mathlib
import Definitions.Def_StrongThinTree
import Definitions.Def_OAIQWSTT000

section
-- module Solutions.OAIQW_StrongThinTree.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_StrongThinTree.ShortcutDuality
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
-- module Solutions.OAIQW_StrongThinTree.Matrix
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
-- module Solutions.OAIQW_StrongThinTree.GraphMatrix
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
lemma qform_nonneg {X : Matrix V V ℝ} (hX : X.PosSemidef) (v : V → ℝ) : 0 ≤ qform X v := by
  simpa only [qform,star_trivial] using hX.dotProduct_mulVec_nonneg v
omit [DecidableEq V] in
lemma qform_mono {X Y : Matrix V V ℝ} (h : X ≤ Y) (v : V → ℝ) : qform X v ≤ qform Y v := by
  have hh := qform_nonneg (Matrix.le_iff.mp h) v
  rw [qform_sub] at hh
  linarith
omit [Fintype V] [DecidableEq V] in
lemma posDef_of_le {X Y : Matrix V V ℝ} (hX : X.PosDef) (hXY : X ≤ Y) : Y.PosDef := by
  convert hX.add_posSemidef (Matrix.le_iff.mp hXY) using 1; abel

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_psd (F : Finset (Fin m)) : (G.laplacian F).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro e _
  simpa only [star_trivial] using posSemidef_vecMulVec_self_star (G.incidence e)
lemma laplacian_qform (F : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian F) v=∑e ∈ F, (v (G.left e)-v (G.right e))^2 := by
  simp only [laplacian,qform,sum_mulVec,dotProduct_sum,rankOne_quadratic]
  apply sum_congr rfl
  intro e _
  rw [dotProduct_comm]
  congr 1
  exact G.eval_incidence v e
lemma laplacian_cut (F : Finset (Fin m)) (S : Finset (Fin n)) :
    qform (G.laplacian F) (cutIndicator S)=(G.cut F S).card := by
  rw [G.laplacian_qform]
  simp only [cut,card_eq_sum_ones,Nat.cast_sum,sum_filter]
  apply sum_congr rfl
  intro e _
  by_cases hl : G.left e ∈ S <;> by_cases hr : G.right e ∈ S <;> simp [cutIndicator,hl,hr]
lemma baseMatrix_pd (hn : 0 < n) : G.baseMatrix.PosDef := by
  exact Matrix.PosDef.posSemidef_add (G.laplacian_psd univ) (Matrix.PosDef.one.smul (inv_pos.mpr (Nat.cast_pos.mpr hn)))

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MatrixDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uV

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
variable {V : Type uV} [Fintype V] [DecidableEq V]

namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)

lemma domain_pd (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain) : X.PosDef :=
  posDef_of_le (G.baseMatrix_pd hn) hX.1

end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.BasePacking
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

lemma same_endpoints {T : Finset (Fin m)} {e : Fin m} (he : e ∈ T) :
    G.Same T (G.left e) (G.right e) := Packing.mem_span_self G.incidence he

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

lemma sumOn_point (S : Finset (Fin n)) (v : Fin n) :
    (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) =
      if v ∈ S then 1 else 0 := by
  simp [LinearMap.sum_apply, point, Pi.single_apply, Finset.sum_ite_eq']

theorem connected_iff_same (T : Finset (Fin m)) :
    G.Connected T ↔ ∀ u v, G.Same T u v := by
  classical
  constructor
  · intro hconn u v
    by_contra huv
    let S := Finset.univ.filter (fun w => G.Same T w v)
    have hS : S.Nonempty := ⟨v, by simp [S, G.same_refl]⟩
    have hSne : S ≠ Finset.univ := by
      intro heq
      have hu : u ∈ S := heq ▸ Finset.mem_univ u
      exact huv (by simpa [S] using hu)
    obtain ⟨e, he⟩ := hconn S hS hSne
    obtain ⟨heT, hecut⟩ := Finset.mem_filter.mp he
    rcases hecut with ⟨hl, hr⟩ | ⟨hr, hl⟩
    · have hl' : G.Same T (G.left e) v := by simpa [S] using hl
      have hr' := G.same_trans (G.same_symm (G.same_endpoints heT)) hl'
      exact hr (by simpa [S] using hr')
    · have hr' : G.Same T (G.right e) v := by simpa [S] using hr
      have hl' := G.same_trans (G.same_endpoints heT) hr'
      exact hl (by simpa [S] using hl')
  · intro hsame S hS hSne
    by_contra hcut
    have hempty : G.cut T S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hcut
    let f : (Fin n → ℝ) →ₗ[ℝ] ℝ := ∑ u ∈ S, LinearMap.proj u
    have hker : G.edgeSpan T ≤ LinearMap.ker f := by
      apply (Packing.span_le_iff G.incidence).mpr
      intro e he
      have hiff : G.left e ∈ S ↔ G.right e ∈ S := by
        have h : ¬ ((G.left e ∈ S ∧ G.right e ∉ S) ∨
            (G.right e ∈ S ∧ G.left e ∉ S)) := by
          intro hc
          have : e ∈ G.cut T S := Finset.mem_filter.mpr ⟨he, hc⟩
          simp [hempty] at this
        tauto
      change f (G.incidence e) = 0
      rw [incidence, map_sub]
      change (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.left e)) -
        (∑ u ∈ S, LinearMap.proj u : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point (G.right e)) = 0
      simp only [sumOn_point]
      simp only [hiff, sub_self]
    obtain ⟨u, hu⟩ := hS
    have hv : ∃ v, v ∉ S := by
      by_contra h
      push Not at h
      exact hSne (Finset.eq_univ_of_forall h)
    obtain ⟨v, hv⟩ := hv
    have hz := hker (hsame u v)
    change f (point u - point v) = 0 at hz
    rw [map_sub] at hz
    change (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point u) -
      (∑ w ∈ S, LinearMap.proj w : (Fin n → ℝ) →ₗ[ℝ] ℝ) (point v) = 0 at hz
    simp [sumOn_point, hu, hv] at hz

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

end StrongThinTree.MultiGraph

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.ThresholdChain
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

lemma treePackable_mono_count {F : Finset (Fin m)} {q r : ℕ}
    (h : q ≤ r) (hp : G.TreePackable F r) : G.TreePackable F q := by
  obtain ⟨T,hT,hd⟩ := hp
  exact ⟨fun i => T (Fin.castLE h i),fun i => hT _,fun i j hij => hd (fun he => hij (Fin.castLE_injective h he))⟩

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Expectation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {D : Type uD} {R : Type uR} {S : Type uS} [Fintype D] [DecidableEq D] [CommRing R] [CommRing S]

lemma detLinear_apply (M A : Matrix D D R) :
    detLinear M A=∑i, (Matrix.updateRow M i (A i)).det := by
  exact MultilinearMap.linearDeriv_apply _ M A

lemma detLinear_map (f : R →+* S) (M A : Matrix D D R) :
    detLinear (M.map f) (A.map f)=f (detLinear M A) := by
  simp only [detLinear_apply,map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [f.map_det]
  congr 1
  ext a b
  by_cases h : a=i <;> simp [Matrix.updateRow,Matrix.map_apply,Function.update,h]

lemma det_piecewise_mul (s : Finset D) (c : D → R) (A M : Matrix D D R) :
    Matrix.det (s.piecewise (fun i j => c i*A i j) M)=
      (∏i ∈ s, c i)*Matrix.det (s.piecewise A M) := by
  have he : s.piecewise (fun i j => c i*A i j) M=
      Matrix.of (fun i j => (if i ∈ s then c i else 1)*(s.piecewise A M) i j) := by
    ext i j
    by_cases hi : i ∈ s <;> simp [Finset.piecewise,hi]
  rw [he]
  have hh := Matrix.det_mul_column (fun i => if i ∈ s then c i else 1)
    (Matrix.of (s.piecewise A M))
  convert hh using 1 <;> try rfl
  exact congrArg (fun z => z*Matrix.det (s.piecewise A M)) (Finset.prod_ite_mem_eq s c).symm

lemma det_add_rankOne (M : Matrix D D R) (u v : D → R) :
    (M+Matrix.vecMulVec u v).det=M.det+detLinear M (Matrix.vecMulVec u v) := by
  have he := Matrix.detRowAlternating.toMultilinearMap.map_add_eq_map_add_linearDeriv_add
    M (Matrix.vecMulVec u v)
  change (M+Matrix.vecMulVec u v).det=M.det+detLinear M (Matrix.vecMulVec u v)+
    ∑s : Finset D with 2 ≤ s.card, Matrix.det (s.piecewise (Matrix.vecMulVec u v) M) at he
  rw [he]
  suffices hh : ∑s : Finset D with 2 ≤ s.card, Matrix.det (s.piecewise (Matrix.vecMulVec u v) M)=0 by
    rw [hh,add_zero]
  apply Finset.sum_eq_zero
  intro s hs
  have hc : 1 < s.card := by have hh := (Finset.mem_filter.mp hs).2; omega
  obtain ⟨i,hi,j,hj,hij⟩ := Finset.one_lt_card.mp hc
  change Matrix.det (s.piecewise (fun i j => u i*v j) M)=0
  rw [det_piecewise_mul s u (fun _ => v) M]
  have hz : Matrix.det (s.piecewise (fun _ : D => v) M)=0 := by
    apply Matrix.det_zero_of_row_eq hij
    simp [Finset.piecewise,hi,hj]
  rw [hz,mul_zero]

lemma det_linear_pencil_coeff_one (M A : Matrix D D R) :
    ((M.map Polynomial.C + (X : R[X]) • A.map Polynomial.C).det).coeff 1=detLinear M A := by
  have he := Matrix.detRowAlternating.toMultilinearMap.map_add_eq_map_add_linearDeriv_add
    (M.map Polynomial.C) ((X : R[X]) • A.map Polynomial.C)
  change (M.map Polynomial.C + (X : R[X]) • A.map Polynomial.C).det=
    (M.map Polynomial.C).det+detLinear (M.map Polynomial.C) ((X : R[X]) • A.map Polynomial.C)+
    ∑s : Finset D with 2 ≤ s.card,
      Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C)) at he
  rw [he,coeff_add,coeff_add]
  have hc : (M.map Polynomial.C).det=C M.det := (Polynomial.C.map_det M).symm
  rw [hc,map_smul,detLinear_map,smul_eq_mul,coeff_X_mul,coeff_C_zero,coeff_C]
  simp only [one_ne_zero,ite_false,zero_add]
  suffices hz : (∑s : Finset D with 2 ≤ s.card,
      Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C))).coeff 1=0 by
    rw [hz,add_zero]
  rw [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro s hs
  have hc : 2 ≤ s.card := (Finset.mem_filter.mp hs).2
  have hp : Matrix.det (s.piecewise ((X : R[X]) • A.map Polynomial.C) (M.map Polynomial.C))=
      (X : R[X])^s.card*Matrix.det (s.piecewise (A.map Polynomial.C) (M.map Polynomial.C)) := by
    rw [show (X : R[X]) • A.map Polynomial.C=fun i j => X*(A.map Polynomial.C) i j from rfl,
      det_piecewise_mul]
    simp
  rw [hp,coeff_X_pow_mul']
  simp [show ¬s.card ≤ 1 by omega]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Stability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uI2 uA uD uI3 uD2

section

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder

variable {I : Type uI2} [DecidableEq I]

lemma slice_eval (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) (w : ℂ) :
    (slice p z i).eval w = MvPolynomial.eval (Function.update z i w) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq => simpa [slice,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [slice] at hp
    by_cases hji : j=i
    · subst j
      simp [slice,MvPolynomial.eval₂_mul,hp]
    · simp [slice,MvPolynomial.eval₂_mul,hji,hp]

lemma slice_derivative (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).derivative = slice (MvPolynomial.pderiv i p) z i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [slice]
  | add p q hp hq =>
    simp only [slice] at hp hq
    simp [slice,MvPolynomial.eval₂_add,hp,hq]
  | mul_X p j hp =>
    simp only [slice] at hp
    rw [MvPolynomial.pderiv_mul]
    by_cases hji : j=i
    · subst j
      simp [slice,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_add,Polynomial.derivative_mul,hp]
    · simp [slice,MvPolynomial.eval₂_mul,Polynomial.derivative_mul,
        MvPolynomial.pderiv_X,hji,hp]

lemma slice_eval_self (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).eval (z i) = MvPolynomial.eval z p := by
  simpa using slice_eval p z i (z i)

lemma slice_derivative_eval_self (p : MvPolynomial I ℂ) (z : I → ℂ) (i : I) :
    (slice p z i).derivative.eval (z i) = MvPolynomial.eval z (MvPolynomial.pderiv i p) := by
  rw [slice_derivative,slice_eval_self]

lemma inverse_difference_im_neg {z a : ℂ} (hz : 0 < z.im) (ha : a.im ≤ 0) :
    (1/(z-a)).im < 0 := by
  have hd : 0 < (z-a).im := by simp only [Complex.sub_im]; linarith
  have hd0 : z-a ≠ 0 := fun h => by simpa [h] using hd.ne'
  simp only [one_div,Complex.inv_im]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hd) (Complex.normSq_pos.mpr hd0)

lemma polynomial_log_derivative {p : Polynomial ℂ} {z : ℂ}
    (hz : 0 < z.im) (hp : ∀w : ℂ, 0 < w.im → p.eval w ≠ 0) :
    p.derivative.eval z / p.eval z = 0 ∨ (p.derivative.eval z / p.eval z).im < 0 := by
  have hp0 : p ≠ 0 := fun h => by simpa [h] using hp z hz
  have hr : ∀a ∈ p.roots, a.im ≤ 0 := by
    intro a ha
    by_contra h
    exact hp a (lt_of_not_ge h) ((Polynomial.mem_roots hp0).mp ha)
  rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero (hp z hz)]
  by_cases hempty : p.roots = 0
  · left
    simp [hempty]
  · right
    have hsum : ∀s : Multiset ℂ, (∀a ∈ s, a.im ≤ 0) → s ≠ 0 →
        ((s.map (fun a => 1/(z-a))).sum).im < 0 := by
      intro s
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons a s ih =>
        intro hs _
        have ha := inverse_difference_im_neg hz (hs a (by simp))
        have hsn : ∀b ∈ s, b.im ≤ 0 := fun b hb => hs b (by simp [hb])
        by_cases he : s=0
        · simp only [he,Multiset.map_cons,Multiset.map_zero,Multiset.sum_cons,Multiset.sum_zero,add_zero]
          exact ha
        · have hh := ih hsn he
          simp only [Multiset.map_cons,Multiset.sum_cons,Complex.add_im]
          linarith
    exact hsum _ hr hempty

lemma Stable.sub_pderiv {p : MvPolynomial I ℂ} (hp : Stable p) (i : I) :
    Stable (p-MvPolynomial.pderiv i p) := by
  intro z hz
  have hslice : ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j
      simpa using hw
    · simpa [Function.update_of_ne hji] using hz j
  have hh := polynomial_log_derivative (hz i) hslice
  rw [slice_derivative_eval_self,slice_eval_self] at hh
  intro heq
  have heq' : MvPolynomial.eval z (MvPolynomial.pderiv i p) = MvPolynomial.eval z p := by
    exact (sub_eq_zero.mp (by simpa only [MvPolynomial.eval_sub] using heq)).symm
  rw [heq',div_self (hp z hz)] at hh
  rcases hh with hh | hh
  · exact one_ne_zero hh
  · simp at hh

lemma factor_norm_bound {z a r : ℂ} (hz : 0 < z.im) (hr : r.im ≤ 0) :
    ‖a-r‖ ≤ (1+‖a-z‖/z.im)*‖z-r‖ := by
  have hzr : z.im ≤ ‖z-r‖ := by
    have hh := Complex.abs_im_le_norm (z-r)
    have hh' := le_abs_self (z-r).im
    simp only [Complex.sub_im] at hh hh'
    linarith
  have htriangle : ‖a-r‖ ≤ ‖a-z‖+‖z-r‖ := by
    simpa only [sub_add_sub_cancel] using norm_add_le (a-z) (z-r)
  have hh := mul_le_mul_of_nonneg_left hzr (div_nonneg (norm_nonneg (a-z)) hz.le)
  have he : (‖a-z‖/z.im)*z.im = ‖a-z‖ := div_mul_cancel₀ _ hz.ne'
  linarith only [hh,he,htriangle]

lemma stable_eval_norm_bound {p : Polynomial ℂ} {z : ℂ} (hz : 0 < z.im)
    (hp : ∀w : ℂ, 0 < w.im → p.eval w ≠ 0) (a : ℂ) {D : ℕ}
    (hD : p.natDegree ≤ D) :
    ‖p.eval a‖ ≤ ‖p.eval z‖*(1+‖a-z‖/z.im)^D := by
  have hp0 : p ≠ 0 := fun h => by simpa [h] using hp z hz
  have hr : ∀r ∈ p.roots, r.im ≤ 0 := by
    intro r hr
    by_contra hh
    exact hp r (lt_of_not_ge hh) ((Polynomial.mem_roots hp0).mp hr)
  let C := 1+‖a-z‖/z.im
  have hC : 1 ≤ C := le_add_of_nonneg_right (div_nonneg (norm_nonneg _) hz.le)
  have hg : ∀s : Multiset ℂ, (∀r ∈ s, r.im ≤ 0) →
      ‖(s.map (fun r => a-r)).prod‖ ≤ C^s.card*‖(s.map (fun r => z-r)).prod‖ := by
    intro s
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons r s ih =>
      intro hrs
      have h1 := factor_norm_bound (a := a) hz (hrs r (by simp))
      have h2 := ih (fun u hu => hrs u (by simp [hu]))
      have hm := mul_le_mul h1 h2 (norm_nonneg _) (mul_nonneg (zero_le_one.trans hC) (norm_nonneg _))
      simpa only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons,norm_mul,pow_succ,
        mul_assoc,mul_left_comm,mul_comm] using hm
  have hroot := hg p.roots hr
  have hdeg : C^p.roots.card ≤ C^D := by
    rw [←(IsAlgClosed.splits p).natDegree_eq_card_roots]
    exact pow_le_pow_right₀ hC hD
  rw [(IsAlgClosed.splits p).eval_eq_prod_roots a,(IsAlgClosed.splits p).eval_eq_prod_roots z]
  simp only [norm_mul]
  have h1 := mul_le_mul_of_nonneg_left hroot (norm_nonneg p.leadingCoeff)
  have h2 := mul_le_mul_of_nonneg_left hdeg
    (mul_nonneg (norm_nonneg p.leadingCoeff) (norm_nonneg ((p.roots.map (fun r => z-r)).prod)))
  linarith only [h1,h2]

lemma polynomial_stability_limit {A : Type uA} {L : Filter A} [L.NeBot]
    (f : A → Polynomial ℂ) (p : Polynomial ℂ) {D : ℕ}
    (hD : ∀ᶠa in L, (f a).natDegree ≤ D)
    (hf : ∀ᶠa in L, ∀z : ℂ, 0 < z.im → (f a).eval z ≠ 0)
    (hlim : ∀z : ℂ, Filter.Tendsto (fun a => (f a).eval z) L (nhds (p.eval z)))
    (hp : p ≠ 0) : ∀z : ℂ, 0 < z.im → p.eval z ≠ 0 := by
  intro z hz hzero
  have hvanish : ∀w : ℂ, 0 < w.im → p.eval w = 0 := by
    intro w hw
    have hb : ‖p.eval w‖ ≤ ‖p.eval z‖*(1+‖w-z‖/z.im)^D :=
      le_of_tendsto_of_tendsto (hlim w).norm ((hlim z).norm.mul_const _) (by
        filter_upwards [hD,hf] with a hDa hfa
        exact stable_eval_norm_bound hz hfa w hDa)
    rw [hzero,norm_zero,zero_mul] at hb
    exact norm_eq_zero.mp (le_antisymm hb (norm_nonneg _))
  have hinj : Function.Injective (fun k : ℕ => (k:ℂ)+Complex.I) := by
    intro k l h
    have hh := congrArg Complex.re h
    simpa only [Complex.add_re,Complex.natCast_re,Complex.I_re,add_zero,Nat.cast_inj] using hh
  have hinf := Set.infinite_range_of_injective hinj
  have hroots : Set.range (fun k : ℕ => (k:ℂ)+Complex.I) ⊆ {w | p.IsRoot w} := by
    rintro w ⟨k,rfl⟩
    exact hvanish _ (by simp)
  exact hp (p.eq_zero_of_infinite_isRoot (hinf.mono hroots))

lemma slice_degree_bound (p : MvPolynomial I ℂ) :
    ∃D : ℕ, ∀z i, (slice p z i).natDegree ≤ D := by
  induction p using MvPolynomial.induction_on with
  | C a => exact ⟨0,fun z i => by simp [slice]⟩
  | add p q hp hq =>
    obtain ⟨P,hP⟩ := hp
    obtain ⟨Q,hQ⟩ := hq
    refine ⟨max P Q,fun z i => ?_⟩
    have he : slice (p+q) z i = slice p z i+slice q z i := by simp [slice,MvPolynomial.eval₂_add]
    rw [he]
    exact (Polynomial.natDegree_add_le _ _).trans (max_le_max (hP z i) (hQ z i))
  | mul_X p j hp =>
    obtain ⟨P,hP⟩ := hp
    refine ⟨P+1,fun z i => ?_⟩
    have he : slice (p*MvPolynomial.X j) z i = slice p z i * (if j=i then Polynomial.X else Polynomial.C (z j)) := by
      simp [slice,MvPolynomial.eval₂_mul]
    rw [he]
    calc
      _ ≤ (slice p z i).natDegree+(if j=i then Polynomial.X else Polynomial.C (z j)).natDegree := Polynomial.natDegree_mul_le
      _ ≤ P+1 := by have hh := hP z i; split_ifs <;> simp only [Polynomial.natDegree_X,Polynomial.natDegree_C] <;> omega

lemma Stable.slice_boundary {p : MvPolynomial I ℂ} (hp : Stable p)
    (z : I → ℂ) (hz : ∀j, 0 ≤ (z j).im) (i : I)
    (h0 : slice p z i ≠ 0) :
    ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
  obtain ⟨D,hD⟩ := slice_degree_bound p
  let f : ℝ → Polynomial ℂ := fun t => slice p (fun j => z j+(t:ℂ)*Complex.I) i
  apply polynomial_stability_limit (L := nhdsWithin (0:ℝ) (Set.Ioi 0)) f (slice p z i)
    (D := D) (Filter.Eventually.of_forall (fun t => hD _ _)) _ _ h0
  · filter_upwards [self_mem_nhdsWithin] with t ht
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j
      simpa using hw
    · simp only [Function.update_of_ne hji,Complex.add_im,Complex.mul_im,
        Complex.ofReal_re,Complex.I_im,mul_one,Complex.ofReal_im,
        Complex.I_re,mul_zero,add_zero]
      exact add_pos_of_nonneg_of_pos (hz j) ht
  · intro w
    have hc : Continuous (fun t : ℝ =>
        MvPolynomial.eval (Function.update (fun j => z j+(t:ℂ)*Complex.I) i w) p) := by
      apply (MvPolynomial.continuous_eval p).comp
      apply continuous_pi
      intro j
      by_cases hji : j=i
      · subst j
        simpa using (continuous_const : Continuous (fun _ : ℝ => w))
      · simp only [Function.update_of_ne hji]
        fun_prop
    have hh := (hc.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
    simpa only [f,slice_eval,Complex.ofReal_zero,zero_mul,add_zero] using hh

lemma splits_of_upper_half_plane (p : Polynomial ℝ)
    (hp : ∀w : ℂ, 0 < w.im → (p.map (algebraMap ℝ ℂ)).eval w ≠ 0) : p.Splits := by
  apply Polynomial.Splits.of_splits_map (algebraMap ℝ ℂ) (IsAlgClosed.splits _)
  intro a ha
  have hroot := Polynomial.isRoot_of_mem_roots ha
  have haeval : Polynomial.aeval a p=0 := by
    simpa only [Polynomial.IsRoot,Polynomial.eval_map,Polynomial.aeval_def] using hroot
  have hle : a.im ≤ 0 := by
    by_contra hh
    exact hp a (lt_of_not_ge hh) hroot
  have hge : 0 ≤ a.im := by
    by_contra hh
    have hconj : (p.map (algebraMap ℝ ℂ)).eval (starRingEnd ℂ a)=0 := by
      simp only [Polynomial.eval_map,←Polynomial.aeval_def,Polynomial.aeval_conj,haeval,map_zero]
    exact hp _ (by simpa only [Complex.conj_im] using neg_pos.mpr (lt_of_not_ge hh)) hconj
  refine ⟨a.re,?_⟩
  apply Complex.ext
  · rfl
  · change 0 = a.im
    exact (le_antisymm hle hge).symm

section Determinant
open Matrix
variable {D : Type uD} [Fintype D] [DecidableEq D] [Fintype I]

omit [DecidableEq I] in
lemma stable_matrix_pencil (A : I → Matrix D D ℂ)
    (hA : ∀i, (A i).PosSemidef) (hSum : (∑i, A i).PosDef) (z : I → ℂ)
    (hz : ∀i, 0 < (z i).im) : (∑i, z i • A i).det ≠ 0 := by
  let M := ∑i, z i • A i
  have hker : ∀x : D → ℂ, M*ᵥx=0 → x=0 := by
    intro x hx
    by_contra hx0
    let a : I → ℂ := fun i => star x ⬝ᵥ (A i)*ᵥx
    have ha : ∀i, 0 ≤ a i := fun i => (hA i).dotProduct_mulVec_nonneg x
    have haR : ∀i, 0 ≤ (a i).re := fun i => (Complex.nonneg_iff.mp (ha i)).1
    have haI : ∀i, (a i).im=0 := fun i => (Complex.nonneg_iff.mp (ha i)).2.symm
    have hs : 0 < ∑i, (a i).re := by
      have hh := (Complex.pos_iff.mp (hSum.dotProduct_mulVec_pos hx0)).1
      simpa only [sum_mulVec,dotProduct_sum,Complex.re_sum] using hh
    obtain ⟨j,hj,hjpos⟩ := (sum_pos_iff_of_nonneg (fun i _ => haR i)).mp hs
    have hpos : 0 < ∑i, (z i).im*(a i).re :=
      (sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hz i).le (haR i))).mpr
        ⟨j,mem_univ _,mul_pos (hz j) hjpos⟩
    have hzero : ∑i, z i*a i=0 := by
      have hh := congrArg (fun y => star x ⬝ᵥ y) hx
      simpa only [M,sum_mulVec,smul_mulVec,dotProduct_sum,dotProduct_smul,
        smul_eq_mul,dotProduct_zero] using hh
    have him : (∑i, (z i).im*(a i).re)=0 := by
      have hh := congrArg Complex.im hzero
      simpa only [Complex.im_sum,Complex.mul_im,haI,mul_zero,zero_add,Complex.zero_im] using hh
    linarith only [hpos,him]
  have hinj : Function.Injective M.mulVec := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply hker
    rw [mulVec_sub,hxy,sub_self]
  exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det M).mp (mulVec_injective_iff_isUnit.mp hinj))

omit [DecidableEq I] in
lemma determinantPencil_eval (A : I → Matrix D D ℂ) (z : I → ℂ) :
    MvPolynomial.eval z (determinantPencil A) = (∑i, z i • A i).det := by
  let M : Matrix D D (MvPolynomial I ℂ) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.eval z) M.det = _
  rw [(MvPolynomial.eval z).map_det M]
  congr 1
  ext a b
  change (MvPolynomial.eval z) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma determinantPencil_stable (A : I → Matrix D D ℂ)
    (hA : ∀i, (A i).PosSemidef) (hSum : (∑i, A i).PosDef) : Stable (determinantPencil A) := by
  intro z hz
  rw [determinantPencil_eval]
  exact stable_matrix_pencil A hA hSum z hz
end Determinant

end
end StrongThinTree.MSS

namespace StrongThinTree.MSS
noncomputable section
open Finset Polynomial
open scoped Classical ComplexOrder
variable {I : Type uI3} [DecidableEq I]

lemma Stable.differentialProduct {p : MvPolynomial I ℂ} (hp : Stable p) (dirs : List I) :
    Stable (differentialProduct dirs p) := by
  induction dirs generalizing p with
  | nil => exact hp
  | cons i dirs ih => exact ih (hp.sub_pderiv i)

open Matrix

end
end StrongThinTree.MSS

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.PartialFractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Polynomial Filter Finset
open scoped Topology
namespace StrongThinTree.MSS.Rational

lemma upper_root_I {k : ℕ} (hk : 0 < k) :
    ∃w : ℂ, 0 < w.im ∧ w^k=Complex.I := by
  let θ : ℝ := Real.pi/(2*k)
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hkp : (0:ℝ)<k := Nat.cast_pos.mpr hk
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*k)).mpr
    have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  refine ⟨w,?_,?_⟩
  · simpa [w,Complex.exp_im] using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [show w^k=Complex.exp ((k:ℂ)*((θ:ℂ)*Complex.I)) from (Complex.exp_nat_mul _ _).symm]
    have heq : (k:ℂ)*((θ:ℂ)*Complex.I)=(Real.pi:ℂ)/2*Complex.I := by
      dsimp [θ]
      push_cast
      have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp [hkc]
    rw [heq,Complex.exp_pi_div_two_mul_I]

lemma upper_root_neg_I {k : ℕ} (hk : 2 ≤ k) :
    ∃w : ℂ, 0 < w.im ∧ w^k= -Complex.I := by
  let θ : ℝ := 3*Real.pi/(2*k)
  let w := Complex.exp ((θ:ℂ)*Complex.I)
  have hkp : (0:ℝ)<k := by exact_mod_cast (by omega : 0 < k)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hθπ : θ < Real.pi := by
    dsimp [θ]
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<2*k)).mpr
    have hk2 : (2:ℝ)≤k := by exact_mod_cast hk
    nlinarith [Real.pi_pos]
  refine ⟨w,?_,?_⟩
  · simpa [w,Complex.exp_im] using Real.sin_pos_of_pos_of_lt_pi hθ hθπ
  · rw [show w^k=Complex.exp ((k:ℂ)*((θ:ℂ)*Complex.I)) from (Complex.exp_nat_mul _ _).symm]
    have heq : (k:ℂ)*((θ:ℂ)*Complex.I)=(Real.pi:ℂ)*Complex.I+(Real.pi:ℂ)/2*Complex.I := by
      dsimp [θ]
      push_cast
      have hkc : (k:ℂ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
      field_simp [hkc]
      norm_num
    rw [heq,Complex.exp_add,Complex.exp_pi_mul_I,Complex.exp_pi_div_two_mul_I]
    simp

lemma principal_part_order {c : ℝ} (hc : c ≠ 0) {k : ℕ} (hk : 0 < k)
    (h : ∀w : ℂ, 0 < w.im → ((c:ℂ)/w^k).im ≤ 0) : k=1 ∧ 0<c := by
  obtain ⟨u,hu,huPow⟩ := upper_root_I hk
  have hc0 : 0 ≤ c := by
    have hh := h u hu
    rw [huPow] at hh
    simpa [Complex.div_im] using hh
  have hk1 : k=1 := by
    by_contra hn
    obtain ⟨v,hv,hvPow⟩ := upper_root_neg_I (by omega : 2 ≤ k)
    have hh := h v hv
    rw [hvPow] at hh
    have hc1 : c ≤ 0 := by simpa [Complex.div_im] using hh
    exact hc (le_antisymm hc1 hc0)
  exact ⟨hk1,lt_of_le_of_ne hc0 (Ne.symm hc)⟩

lemma polynomial_part_order {c : ℝ} (hc : c ≠ 0) {k : ℕ} (hk : 0 < k)
    (h : ∀w : ℂ, 0 < w.im → ((c:ℂ)*w^k).im ≤ 0) : k=1 ∧ c<0 := by
  obtain ⟨u,hu,huPow⟩ := upper_root_I hk
  have hc0 : c ≤ 0 := by simpa [huPow] using h u hu
  have hk1 : k=1 := by
    by_contra hn
    obtain ⟨v,hv,hvPow⟩ := upper_root_neg_I (by omega : 2 ≤ k)
    have hc1 : 0 ≤ c := by simpa [hvPow] using h v hv
    exact hc (le_antisymm hc0 hc1)
  exact ⟨hk1,lt_of_le_of_ne hc0 hc⟩

lemma continuous_cval (p : ℝ[X]) : Continuous (cval p) := (p.map (algebraMap ℝ ℂ)).continuous

lemma pole_test (a b : ℝ[X]) {x : ℝ} {k : ℕ} (hk : 0 < k)
    (ha : a.eval x ≠ 0) (hb : b.eval x ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/((z-(x:ℂ))^k*cval b z)).im ≤ 0) :
    k=1 ∧ 0<a.eval x/b.eval x := by
  apply principal_part_order (div_ne_zero ha hb) hk
  intro w hw
  have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
  have hb0 : cval b x ≠ 0 := by simpa using hb
  have hd : w^k*cval b x ≠ 0 := mul_ne_zero (pow_ne_zero _ hw0) hb0
  have ht : Tendsto (fun r : ℝ => cval a ((x:ℂ)+r*w)/(w^k*cval b ((x:ℂ)+r*w)))
      (𝓝[>] 0) (𝓝 (((a.eval x/b.eval x:ℝ):ℂ)/w^k)) := by
    have hc : ContinuousAt (fun r : ℝ => (x:ℂ)+(r:ℂ)*w) 0 := by fun_prop
    have hta := (continuous_cval a).continuousAt.comp hc
    have htb := (continuous_cval b).continuousAt.comp hc
    have htt := hta.tendsto.div (htb.tendsto.const_mul (w^k)) (by simpa using hd)
    dsimp only [Function.comp_apply,Pi.div_apply] at htt
    simp only [Complex.ofReal_zero] at htt
    have heq : cval a ((x:ℂ)+(0:ℂ)*w)/(w^k*cval b ((x:ℂ)+(0:ℂ)*w))=
        ((a.eval x/b.eval x:ℝ):ℂ)/w^k := by simp only [zero_mul,add_zero,cval_real,Complex.ofReal_div]; ring
    rw [heq] at htt
    exact htt.mono_left nhdsWithin_le_nhds
  have him := Complex.continuous_im.continuousAt.tendsto.comp ht
  apply le_of_tendsto him
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hrp : 0 < r := hr
  have hrc : (r:ℂ) ≠ 0 := by exact_mod_cast hrp.ne'
  have hzr : 0 < ((x:ℂ)+(r:ℂ)*w).im := by simpa using mul_pos hrp hw
  have hh := h _ hzr
  have heq : cval a ((x:ℂ)+r*w)/(w^k*cval b ((x:ℂ)+r*w))=
      (r:ℂ)^k * (cval a ((x:ℂ)+r*w)/(((x:ℂ)+r*w-x)^k*cval b ((x:ℂ)+r*w))) := by
    rw [add_sub_cancel_left,mul_pow]
    field_simp [hrc]
  dsimp only [Function.comp_apply]
  rw [heq,←Complex.ofReal_pow,Complex.mul_im]
  simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hrp.le _) hh

lemma simple_roots (a b : ℝ[X]) (hb : b ≠ 0) (hab : IsCoprime a b)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0) : b.roots.Nodup := by
  classical
  apply Multiset.nodup_iff_count_le_one.mpr
  intro x
  rw [count_roots]
  by_cases hx : b.IsRoot x
  · have ha : a.eval x ≠ 0 := by
      have ht := aeval_ne_zero_of_isCoprime hab x
      simpa [aeval_def,eval₂_at_apply,hx.eq_zero] using ht
    obtain ⟨q,hq,hq0⟩ := exists_eq_pow_rootMultiplicity_mul_and_not_dvd b hb x
    have hqx : q.eval x ≠ 0 := by simpa [dvd_iff_isRoot,IsRoot] using hq0
    have hh := pole_test a q ((rootMultiplicity_pos hb).mpr hx) ha hqx
      (fun z hz => by
        have he := congrArg (fun p => cval p z) hq
        simp only [cval_mul,cval_pow,cval_X_sub_C] at he
        rw [←he]
        exact h z hz)
    omega
  · have hh : rootMultiplicity x b = 0 := by
      exact Nat.eq_zero_of_not_pos (fun hp => hx ((rootMultiplicity_pos hb).mp hp))
    omega

lemma cval_ray (p : ℝ[X]) {w r : ℂ} (hw : w ≠ 0) (hr : r ≠ 0) :
    cval p (w/r) = cval p.reverse (r/w)*(w/r)^p.natDegree := by
  let : Invertible (w/r) := invertibleOfNonzero (div_ne_zero hw hr)
  have h := eval₂_reverse_mul_pow (algebraMap ℝ ℂ) (w/r) p
  simpa only [cval,eval_map,←eval₂_eq_eval_map,invOf_eq_inv,inv_div] using h.symm

lemma reverse_at_zero (p : ℝ[X]) : cval p.reverse 0=((p.leadingCoeff:ℝ):ℂ) := by
  simp [cval,eval_map,coeff_reverse]

lemma ray_limit (a b : ℝ[X]) (hb : b ≠ 0) (hdeg : b.natDegree ≤ a.natDegree)
    {w : ℂ} (hw : w ≠ 0) :
    Tendsto (fun r : ℝ => (r:ℂ)^(a.natDegree-b.natDegree)*
      (cval a (w/r)/cval b (w/r))) (𝓝[>] 0)
      (𝓝 (((a.leadingCoeff/b.leadingCoeff:ℝ):ℂ)*w^(a.natDegree-b.natDegree))) := by
  have hc : ContinuousAt (fun r : ℝ => (r:ℂ)/w) 0 := by fun_prop
  have ha := (continuous_cval a.reverse).continuousAt.comp hc
  have hb' := (continuous_cval b.reverse).continuousAt.comp hc
  have hlc : cval b.reverse ((0:ℂ)/w) ≠ 0 := by
    simp only [zero_div,reverse_at_zero,ne_eq,Complex.ofReal_eq_zero]
    exact leadingCoeff_ne_zero.mpr hb
  have ht := (ha.tendsto.div hb'.tendsto hlc).mul_const (w^(a.natDegree-b.natDegree))
  simp only [Function.comp_apply,zero_div,Complex.ofReal_zero,reverse_at_zero,←Complex.ofReal_div] at ht
  apply (ht.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with r hr
  have hr0 : (r:ℂ) ≠ 0 := by exact_mod_cast (show r ≠ 0 from ne_of_gt hr)
  rw [cval_ray a hw hr0,cval_ray b hw hr0]
  rw [show a.natDegree=b.natDegree+(a.natDegree-b.natDegree) from (Nat.add_sub_of_le hdeg).symm]
  simp only [Nat.add_sub_cancel_left,pow_add,div_pow]
  field_simp
  rfl

lemma degree_le (a b : ℝ[X]) (hb : b ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) : a.natDegree ≤ b.natDegree := by
  by_contra hdeg
  have hlt : b.natDegree < a.natDegree := Nat.lt_of_not_ge hdeg
  have ha : a ≠ 0 := by intro hh; simp [hh] at hlt
  have hc : a.leadingCoeff/b.leadingCoeff ≠ 0 :=
    div_ne_zero (leadingCoeff_ne_zero.mpr ha) (leadingCoeff_ne_zero.mpr hb)
  have ht := polynomial_part_order hc (Nat.sub_pos_of_lt hlt) (by
    intro w hw
    have hw0 : w ≠ 0 := by intro hh; simp [hh] at hw
    have hh := Complex.continuous_im.continuousAt.tendsto.comp (ray_limit a b hb hlt.le hw0)
    apply le_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : 0 < r := hr
    have hz : 0 < (w/(r:ℂ)).im := by
      simpa [Complex.div_ofReal_im] using div_pos hw hrp
    have hi := h _ hz
    dsimp only [Function.comp_apply]
    simp only [←Complex.ofReal_pow,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hrp.le _) hi)
  have hc0 : 0 ≤ a.leadingCoeff/b.leadingCoeff := by
    have hh := Complex.continuous_re.continuousAt.tendsto.comp (ray_limit a b hb hlt.le (one_ne_zero : (1:ℂ)≠0))
    simp only [one_pow,mul_one,Complex.ofReal_re] at hh
    apply ge_of_tendsto hh
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrp : 0 < r := hr
    dsimp only [Function.comp_apply]
    have he : (1:ℂ)/(r:ℂ)=((1/r:ℝ):ℂ) := by push_cast; rfl
    rw [he,cval_real,cval_real,←Complex.ofReal_div,←Complex.ofReal_pow,←Complex.ofReal_mul,Complex.ofReal_re]
    exact mul_nonneg (pow_nonneg hrp.le _) (hpos _ (by positivity))
  linarith [ht.2]

lemma monic_eq_prod_roots (b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : b.roots.Nodup) : b=∏x ∈ b.roots.toFinset, (X-C x) := by
  classical
  conv_lhs => rw [hs.eq_prod_roots,hm.leadingCoeff,C_1,one_mul,Finset.prod_multiset_map_count]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Multiset.count_eq_one_of_mem hn (Multiset.mem_toFinset.mp hx),pow_one]

lemma simple_decomposition (a b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : b.roots.Nodup) (hd : a.natDegree ≤ b.natDegree) :
    ∃c : ℝ, ∃d : ℝ → ℝ, a=C c*b+∑x ∈ b.roots.toFinset, C (d x)*∏y ∈ b.roots.toFinset.erase x, (X-C y) := by
  classical
  let s := b.roots.toFinset
  have hb : b=∏x ∈ s, (X-C x) := monic_eq_prod_roots b hm hs hn
  obtain ⟨q,r,hr,he⟩ := eq_quo_mul_prod_add_sum_rem_mul_prod (s:=s) a
    (g:=fun x : ℝ => X-C x) (fun _ _ => monic_X_sub_C _)
    (fun _ _ _ _ hxy => isCoprime_X_sub_C_of_isUnit_sub (isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr hxy)))
  have hrC : ∀x ∈ s, r x=C ((r x).coeff 0) := by
    intro x hx
    by_cases h0 : r x=0
    · simp [h0]
    apply eq_C_of_natDegree_eq_zero
    have hh := hr x hx
    rw [degree_X_sub_C,degree_eq_natDegree h0] at hh
    have hh' : (r x).natDegree < 1 := WithBot.coe_lt_coe.mp hh
    omega
  have hR : (∑x ∈ s, r x * ∏y ∈ s.erase x, (X-C y)).degree < b.degree := by
    apply (degree_sum_le _ _).trans_lt
    apply Finset.sup_lt_iff (by simpa only [bot_lt_iff_ne_bot,degree_ne_bot] using hm.ne_zero) |>.mpr
    intro x hx
    rw [hb,←Finset.mul_prod_erase s (fun x : ℝ => X-C x) hx]
    rw [degree_mul,degree_mul]
    apply WithBot.add_lt_add_right
    · rw [degree_ne_bot]
      exact (monic_prod_of_monic (s.erase x) _ (fun y _ => monic_X_sub_C y)).ne_zero
    · exact hr x hx
  have hq : q.natDegree=0 := by
    by_contra hq
    have hqp : 0 < q.degree := natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hq)
    have hqb : b.degree < (q*b).degree := by
      rw [degree_mul]
      simpa using WithBot.add_lt_add_right (by simpa [degree_ne_bot] using hm.ne_zero) hqp
    have hda : a.degree ≤ b.degree := by
      exact degree_le_of_natDegree_le hd |>.trans (le_of_eq (degree_eq_natDegree hm.ne_zero).symm)
    have he' : a=q*b+∑x ∈ s, r x*∏y ∈ s.erase x, (X-C y) := by simpa only [←hb] using he
    rw [he',degree_add_eq_left_of_degree_lt (hR.trans hqb)] at hda
    exact (not_le_of_gt hqb) hda
  refine ⟨q.coeff 0,fun x => (r x).coeff 0,?_⟩
  calc
    a=q*b+∑x ∈ s, r x*∏y ∈ s.erase x, (X-C y) := by simpa only [←hb] using he
    _=C (q.coeff 0)*b+∑x ∈ s, C ((r x).coeff 0)*∏y ∈ s.erase x, (X-C y) := by
      apply congrArg₂ (·+·)
      · exact congrArg (·*b) (eq_C_of_natDegree_eq_zero hq)
      · exact Finset.sum_congr rfl (fun x hx => congrArg (·*∏y ∈ s.erase x, (X-C y)) (hrC x hx))

lemma decomposition_value (a b : ℝ[X]) (s : Finset ℝ) (c : ℝ) (d : ℝ → ℝ)
    (hb : b=∏x ∈ s, (X-C x))
    (he : a=C c*b+∑x ∈ s, C (d x)*∏y ∈ s.erase x, (X-C y))
    {t : ℝ} (ht : ∀x ∈ s, t ≠ x) :
    a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
  classical
  have hb0 : b.eval t ≠ 0 := by
    rw [hb,eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    exact Finset.prod_ne_zero_iff.mpr (fun x hx => sub_ne_zero.mpr (ht x hx))
  have he' := congrArg (fun p : ℝ[X] => p.eval t) he
  simp only [eval_add,eval_mul,eval_C,eval_finsetSum,eval_prod,eval_sub,eval_X] at he'
  rw [he',add_div,mul_div_cancel_right₀ _ hb0,Finset.sum_div]
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  have hh := congrArg (fun p : ℝ[X] => p.eval t) (hb.trans (Finset.mul_prod_erase s (fun y : ℝ => X-C y) hx).symm)
  simp only [eval_mul,eval_sub,eval_X,eval_C,eval_prod] at hh
  have hpr : (∏y ∈ s.erase x, (t-y)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr (fun y hy => sub_ne_zero.mpr (ht y (mem_of_mem_erase hy)))
  rw [hh]
  field_simp

lemma residue_value (a b : ℝ[X]) (s : Finset ℝ) (c : ℝ) (d : ℝ → ℝ)
    (hb : b=∏x ∈ s, (X-C x))
    (he : a=C c*b+∑x ∈ s, C (d x)*∏y ∈ s.erase x, (X-C y))
    {x : ℝ} (hx : x ∈ s) :
    a.eval x/(∏y ∈ s.erase x, (X-C y)).eval x=d x := by
  classical
  have hb0 : b.eval x=0 := by
    rw [hb,eval_prod]
    exact Finset.prod_eq_zero hx (by simp)
  have he' := congrArg (fun p : ℝ[X] => p.eval x) he
  simp only [eval_add,eval_mul,eval_C,eval_finsetSum,hb0,mul_zero,zero_add] at he'
  rw [Finset.sum_eq_single x] at he'
  · rw [he',mul_div_cancel_right₀]
    rw [eval_prod]
    simp only [eval_sub,eval_X,eval_C]
    apply Finset.prod_ne_zero_iff.mpr
    intro y hy
    exact sub_ne_zero.mpr (mem_erase.mp hy).1.symm
  · intro y hy hxy
    suffices h0 : (∏z ∈ s.erase y, (X-C z)).eval x=0 by rw [h0,mul_zero]
    rw [eval_prod]
    exact Finset.prod_eq_zero (mem_erase.mpr ⟨hxy.symm,hx⟩) (by simp)
  · exact fun hn => (hn hx).elim

lemma positive_decomposition_monic (a b : ℝ[X]) (hm : b.Monic) (hs : b.Splits)
    (hn : ∀x ∈ b.roots, x < 0) (hab : IsCoprime a b)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) :
    ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧ (∀x ∈ b.roots.toFinset, 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ b.roots.toFinset, d x/(t-x) := by
  classical
  have hnodup := simple_roots a b hm.ne_zero hab h
  obtain ⟨c,d,he⟩ := simple_decomposition a b hm hs hnodup (degree_le a b hm.ne_zero h hpos)
  let s := b.roots.toFinset
  have hb : b=∏x ∈ s, (X-C x) := monic_eq_prod_roots b hm hs hnodup
  have hv : ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
    intro t ht
    exact decomposition_value a b s c d hb he (fun x hx => ne_of_gt ((hn x (Multiset.mem_toFinset.mp hx)).trans_le ht))
  have hd : ∀x ∈ s, 0 < d x := by
    intro x hx
    have hx0 : b.eval x=0 := (mem_roots hm.ne_zero).mp (Multiset.mem_toFinset.mp hx)
    have ha : a.eval x ≠ 0 := by
      simpa [aeval_def,eval₂_at_apply,hx0] using aeval_ne_zero_of_isCoprime hab x
    let q : ℝ[X] := ∏y ∈ s.erase x, (X-C y)
    have hqx : q.eval x ≠ 0 := by
      dsimp [q]
      rw [eval_prod]
      simp only [eval_sub,eval_X,eval_C]
      exact Finset.prod_ne_zero_iff.mpr (fun y hy => sub_ne_zero.mpr (mem_erase.mp hy).1.symm)
    have hbe : b=(X-C x)*q := hb.trans (Finset.mul_prod_erase s (fun y : ℝ => X-C y) hx).symm
    have hp := pole_test a q (k:=1) (by omega) ha hqx (by
      intro z hz
      simpa only [hbe,cval_mul,cval_X_sub_C,pow_one] using h z hz)
    have hr := residue_value a b s c d hb he hx
    exact hr ▸ hp.2
  have hc : 0 ≤ c := by
    have hlim : Tendsto (fun t : ℝ => c+∑x ∈ s, d x/(t-x)) atTop (𝓝 c) := by
      simpa using tendsto_const_nhds.add (tendsto_finsetSum s (fun x _ =>
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => d x) atTop (𝓝 (d x))).div_atTop (by simpa only [sub_eq_add_neg,id_eq] using tendsto_atTop_add_const_right atTop (-x) tendsto_id)))
    apply ge_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    rw [←hv t ht]
    exact hpos t ht
  exact ⟨c,d,hc,hd,hv⟩

lemma positive_decomposition (a b : ℝ[X]) (hb : b ≠ 0) (hs : b.Splits)
    (hreal : ∀t : ℝ, 0 ≤ t → b.eval t ≠ 0)
    (hupper : ∀z : ℂ, 0 < z.im → cval b z ≠ 0)
    (h : ∀z : ℂ, 0 < z.im → (cval a z/cval b z).im ≤ 0)
    (hpos : ∀t : ℝ, 0 ≤ t → 0 ≤ a.eval t/b.eval t) :
    ∃s : Finset ℝ, ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧
      (∀x ∈ s, x < 0 ∧ 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → a.eval t/b.eval t=c+∑x ∈ s, d x/(t-x) := by
  classical
  let f : RatFunc ℝ := algebraMap ℝ[X] (RatFunc ℝ) a/algebraMap ℝ[X] (RatFunc ℝ) b
  have hf : f.num*b=a*f.denom := (RatFunc.num_mul_eq_mul_denom_iff hb).mpr rfl
  obtain ⟨g,hg⟩ := RatFunc.denom_div_dvd a b
  change b=f.denom*g at hg
  have hcf (z : ℂ) (hz : cval b z ≠ 0) : cval f.num z/cval f.denom z=cval a z/cval b z := by
    have hd : cval f.denom z ≠ 0 := by
      rw [hg,cval_mul] at hz
      exact (mul_ne_zero_iff.mp hz).1
    apply (div_eq_div_iff hd hz).mpr
    simpa only [cval_mul] using congrArg (fun p => cval p z) hf
  have hrf (t : ℝ) (ht : b.eval t ≠ 0) : f.num.eval t/f.denom.eval t=a.eval t/b.eval t := by
    have hh := hcf (t:ℂ) (by simpa using ht)
    simpa only [cval_real,←Complex.ofReal_div,Complex.ofReal_inj] using hh
  have hds : f.denom.Splits := hs.of_dvd hb ⟨g,hg⟩
  have hdn : ∀x ∈ f.denom.roots, x < 0 := by
    intro x hx
    by_contra hx0
    have hd0 : f.denom.eval x=0 := (mem_roots (RatFunc.denom_ne_zero f)).mp hx
    have hb0 : b.eval x=0 := by rw [hg,eval_mul,hd0,zero_mul]
    exact hreal x (le_of_not_gt hx0) hb0
  have hdh : ∀z : ℂ, 0 < z.im → (cval f.num z/cval f.denom z).im ≤ 0 := by
    intro z hz
    rw [hcf z (hupper z hz)]
    exact h z hz
  have hdp : ∀t : ℝ, 0 ≤ t → 0 ≤ f.num.eval t/f.denom.eval t := by
    intro t ht
    rw [hrf t (hreal t ht)]
    exact hpos t ht
  obtain ⟨c,d,hc,hd,hrep⟩ := positive_decomposition_monic f.num f.denom (RatFunc.monic_denom f)
    hds hdn (RatFunc.isCoprime_num_denom f) hdh hdp
  refine ⟨f.denom.roots.toFinset,c,d,hc,fun x hx => ⟨hdn x (Multiset.mem_toFinset.mp hx),hd x hx⟩,?_⟩
  intro t ht
  rw [←hrf t (hreal t ht)]
  exact hrep t ht

end StrongThinTree.MSS.Rational

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Barrier
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uR uR2 uR3 uR4 uS uR5 uS2 uR6

section

noncomputable section
open Polynomial Finset Filter
open scoped Topology
namespace StrongThinTree.MSS

variable {I : Type uI} [DecidableEq I]

lemma ray_eval {R : Type uR2} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) (t : R) :
    (ray p z i).eval t=MvPolynomial.eval (Function.update z i (z i+t)) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simpa [ray,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [ray] at hp
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,hji,hp]

lemma ray_derivative {R : Type uR3} [CommRing R] (p : MvPolynomial I R) (z : I → R) (i : I) :
    (ray p z i).derivative=ray (MvPolynomial.pderiv i p) z i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq =>
    simp only [ray] at hp hq
    simp [ray,MvPolynomial.eval₂_add,hp,hq]
  | mul_X p j hp =>
    simp only [ray] at hp
    rw [MvPolynomial.pderiv_mul]
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_add,Polynomial.derivative_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_X,hji,hp]

lemma ray_map {R : Type uR4} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial I R) (z : I → R) (i : I) :
    (ray p z i).map f=ray (p.map f) (fun j => f (z j)) i := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [ray]
  | add p q hp hq => simpa [ray,MvPolynomial.eval₂_add] using congrArg₂ (·+·) hp hq
  | mul_X p j hp =>
    simp only [ray] at hp
    by_cases hji : j=i
    · subst j
      simp [ray,MvPolynomial.eval₂_mul,hp]
    · simp [ray,MvPolynomial.eval₂_mul,hp,hji]

omit [DecidableEq I] in
lemma eval_map_between {R : Type uR5} {S : Type uS2} [CommRing R] [CommRing S] (f : R →+* S)
    (p : MvPolynomial I R) (z : I → R) :
    MvPolynomial.eval (fun j => f (z j)) (p.map f)=f (MvPolynomial.eval z p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p j hp => simp [hp]

omit [DecidableEq I] in
lemma Above.pos {p : MvPolynomial I ℝ} {z : I → ℝ} (hz : Above p z) :
    0 < MvPolynomial.eval z p := by
  simpa using hz 0 (fun _ => le_rfl)

lemma ray_zero (p : MvPolynomial I ℝ) (z : I → ℝ) (i : I) :
    (ray p z i).eval 0=MvPolynomial.eval z p := by simp [ray_eval]

lemma real_ray_upper {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) :
    ∀w : ℂ, 0 < w.im → Rational.cval (ray p z i) w ≠ 0 := by
  have hs0 : slice (p.map (algebraMap ℝ ℂ)) (fun j => (z j:ℂ)) i ≠ 0 := by
    intro he
    have hh := slice_eval_self (p.map (algebraMap ℝ ℂ)) (fun j => (z j:ℂ)) i
    rw [he] at hh
    have hm := eval_map_between (algebraMap ℝ ℂ) p z
    change MvPolynomial.eval (fun j => (z j:ℂ)) (p.map (algebraMap ℝ ℂ))=(MvPolynomial.eval z p:ℂ) at hm
    rw [hm] at hh
    simp only [Polynomial.eval_zero] at hh
    exact hz.pos.ne' (by exact_mod_cast hh.symm)
  intro w hw
  have hh := hp.slice_boundary (fun j => (z j:ℂ)) (fun _ => by simp) i hs0 ((z i:ℂ)+w)
    (by simpa using hw)
  rw [slice_eval] at hh
  unfold Rational.cval
  rw [ray_map,ray_eval]
  exact hh

lemma real_ray_splits {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) : (ray p z i).Splits :=
  splits_of_upper_half_plane _ (real_ray_upper hp hz i)

lemma barrier_nonneg {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i : I) : 0 ≤ barrier p z i := by
  let g := ray p z i
  have hg0 : g.eval 0 ≠ 0 := by simpa [g,ray_zero] using hz.pos.ne'
  have hg : g.Splits := real_ray_splits hp hz i
  have hgroot : ∀x ∈ g.roots, x < 0 := by
    intro x hx
    by_contra hx0
    have he : g.eval x=0 := (mem_roots (by intro h0; simp [h0] at hg0)).mp hx
    have hp0 := (hz.update i (le_of_not_gt hx0)).pos
    rw [←ray_eval] at hp0
    exact hp0.ne' he
  have he : barrier p z i=g.derivative.eval 0/g.eval 0 := by
    simp [g,ray_derivative,ray_zero,barrier]
  rw [he,hg.eval_derivative_div_eval_of_ne_zero hg0]
  apply Multiset.sum_nonneg
  intro r hr
  obtain ⟨x,hx,rfl⟩ := Multiset.mem_map.mp hr
  exact div_nonneg zero_le_one (by linarith [hgroot x hx])

lemma Stable.log_derivative_im {p : MvPolynomial I ℂ} (hp : Stable p)
    (z : I → ℂ) (hz : ∀j, 0 < (z j).im) (i : I) :
    (MvPolynomial.eval z (MvPolynomial.pderiv i p)/MvPolynomial.eval z p).im ≤ 0 := by
  have hs : ∀w : ℂ, 0 < w.im → (slice p z i).eval w ≠ 0 := by
    intro w hw
    rw [slice_eval]
    apply hp
    intro j
    by_cases hji : j=i
    · subst j; simpa using hw
    · simpa [Function.update_of_ne hji] using hz j
  have hh := polynomial_log_derivative (hz i) hs
  rw [slice_derivative_eval_self,slice_eval_self] at hh
  rcases hh with hh | hh
  · simp [hh]
  · exact hh.le

lemma ray_log_derivative_im {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) (w : ℂ) (hw : 0 < w.im) :
    (Rational.cval (ray (MvPolynomial.pderiv i p) z j) w/Rational.cval (ray p z j) w).im ≤ 0 := by
  let P := p.map (algebraMap ℝ ℂ)
  let Z : ℝ → I → ℂ := fun t => Function.update (fun k => (z k:ℂ)+(t:ℂ)*Complex.I) j ((z j:ℂ)+w)
  have hZ : Continuous Z := by
    apply continuous_pi
    intro k
    by_cases hkj : k=j
    · subst k; simp only [Z,Function.update_self]; fun_prop
    · simp only [Z,Function.update_of_ne hkj]; fun_prop
  have he (q : MvPolynomial I ℝ) :
      Rational.cval (ray q z j) w=MvPolynomial.eval (Z 0) (q.map (algebraMap ℝ ℂ)) := by
    unfold Rational.cval
    rw [ray_map,ray_eval]
    simp only [Z,Complex.ofReal_zero,zero_mul,add_zero]
    rfl
  have hD : MvPolynomial.eval (Z 0) P ≠ 0 := by
    exact (he p).symm ▸ real_ray_upper hp hz j w hw
  have hA := ((MvPolynomial.continuous_eval (MvPolynomial.pderiv i P)).comp hZ).continuousAt (x:=0)
  have hB := ((MvPolynomial.continuous_eval P).comp hZ).continuousAt (x:=0)
  have hlim := Complex.continuous_im.continuousAt.tendsto.comp (hA.tendsto.div hB.tendsto hD)
  have heq : (MvPolynomial.eval (Z 0) (MvPolynomial.pderiv i P)/MvPolynomial.eval (Z 0) P).im=
      (Rational.cval (ray (MvPolynomial.pderiv i p) z j) w/Rational.cval (ray p z j) w).im := by
    dsimp [P]
    rw [MvPolynomial.pderiv_map,←he,←he]
  dsimp only [Function.comp_apply] at hlim
  rw [heq] at hlim
  apply le_of_tendsto (hlim.mono_left (nhdsWithin_le_nhds (s:=Set.Ioi 0)))
  filter_upwards [self_mem_nhdsWithin] with t ht
  apply hp.log_derivative_im
  intro k
  by_cases hkj : k=j
  · subst k; simpa only [Z,Function.update_self,Complex.add_im,Complex.ofReal_im,zero_add] using hw
  · simpa only [Z,Function.update_of_ne hkj,Complex.add_im,Complex.ofReal_im,Complex.mul_im,
      Complex.ofReal_re,Complex.I_im,mul_one,Complex.I_re,mul_zero,zero_add,add_zero,Set.mem_Ioi] using ht

lemma barrier_ray_representation {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) :
    ∃s : Finset ℝ, ∃c : ℝ, ∃d : ℝ → ℝ, 0 ≤ c ∧
      (∀x ∈ s, x < 0 ∧ 0 < d x) ∧
      ∀t : ℝ, 0 ≤ t → barrier p (Function.update z j (z j+t)) i=c+∑x ∈ s, d x/(t-x) := by
  have hb : ray p z j ≠ 0 := by
    intro h0
    have hh := hz.pos
    rw [←ray_zero p z j,h0,Polynomial.eval_zero] at hh
    exact lt_irrefl _ hh
  have hr : ∀t : ℝ, 0 ≤ t → (ray p z j).eval t ≠ 0 := by
    intro t ht
    rw [ray_eval]
    exact (hz.update j ht).pos.ne'
  obtain ⟨s,c,d,hc,hd,he⟩ := Rational.positive_decomposition (ray (MvPolynomial.pderiv i p) z j)
    (ray p z j) hb (real_ray_splits hp hz j) hr (real_ray_upper hp hz j)
    (ray_log_derivative_im hp hz i j) (fun t ht => by
      simpa only [ray_eval,barrier] using barrier_nonneg hp (hz.update j ht) i)
  refine ⟨s,c,d,hc,hd,?_⟩
  intro t ht
  simpa only [barrier,ray_eval] using he t ht

lemma barrier_update_le {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) {t : ℝ} (ht : 0 ≤ t) :
    barrier p (Function.update z j (z j+t)) i ≤ barrier p z i := by
  obtain ⟨s,c,d,_,hd,he⟩ := barrier_ray_representation hp hz i j
  have he0 := he 0 le_rfl
  simp only [add_zero,Function.update_eq_self] at he0
  rw [he t ht,he0]
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro x hx
  exact div_le_div_of_nonneg_left (hd x hx).2.le (by linarith [(hd x hx).1]) (by linarith)

lemma update_add_single (z : I → ℝ) (i : I) (t : ℝ) :
    Function.update z i (z i+t)=z+Pi.single i t := by
  ext j
  by_cases hj : j=i
  · subst j; simp
  · simp [Function.update_of_ne hj,Pi.single_eq_of_ne hj]

lemma barrier_add_le [Fintype I] {p : MvPolynomial I ℝ} (hp : RealStable p) {z s : I → ℝ}
    (hz : Above p z) (hs : ∀i, 0 ≤ s i) (i : I) : barrier p (z+s) i ≤ barrier p z i := by
  have hh : ∀T : Finset I, barrier p (z+∑j ∈ T, Pi.single j (s j)) i ≤ barrier p z i := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | @insert j T hj ih =>
      have hn : ∀k, 0 ≤ (∑j ∈ T, Pi.single j (s j)) k := by
        intro k
        rw [Finset.sum_apply]
        exact Finset.sum_nonneg (fun l _ => by by_cases hl : k=l; subst l; simp [hs]; simp [Pi.single_eq_of_ne hl])
      have hu := barrier_update_le hp (hz.add hn) i j (hs j)
      rw [update_add_single] at hu
      rw [Finset.sum_insert hj]
      simpa only [add_left_comm,add_assoc,add_comm] using hu.trans ih
  simpa only [Finset.univ_sum_single] using hh Finset.univ

lemma hasDerivAt_barrier_ray (p : MvPolynomial I ℝ) (z : I → ℝ) (i j : I) {t : ℝ}
    (ht : MvPolynomial.eval (Function.update z j (z j+t)) p ≠ 0) :
    HasDerivAt (fun u => barrier p (Function.update z j (z j+u)) i)
      (crossBarrier p (Function.update z j (z j+t)) i j) t := by
  have hh := ((ray (MvPolynomial.pderiv i p) z j).hasDerivAt t).div ((ray p z j).hasDerivAt t)
    (by simpa only [ray_eval] using ht)
  convert hh using 1 <;> first | rfl | (simp [ray_eval,ray_derivative,barrier,crossBarrier] <;> rfl)

lemma fractions_tangent {x d t : ℝ} (hx : x < 0) (hd : 0 ≤ d) (ht : 0 ≤ t) :
    d/(t-x)+t*(d/(t-x)^2) ≤ d/(0-x) := by
  have hb : 0 < t-x := by linarith
  calc
    d/(t-x)+t*(d/(t-x)^2) = d*(t-x+t)/(t-x)^2 := by field_simp
    _ ≤ d/(0-x) := by
      rw [div_le_div_iff₀ (sq_pos_of_pos hb) (by linarith)]
      linarith [mul_nonneg hd (sq_nonneg t)]

lemma barrier_ray_tangent {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (i j : I) {t : ℝ} (ht : 0 < t) :
    crossBarrier p (Function.update z j (z j+t)) i j ≤ 0 ∧
      barrier p (Function.update z j (z j+t)) i-t*crossBarrier p (Function.update z j (z j+t)) i j ≤ barrier p z i := by
  obtain ⟨s,c,d,_,hd,he⟩ := barrier_ray_representation hp hz i j
  have hder : HasDerivAt (fun u : ℝ => c+∑x ∈ s, d x/(u-x))
      (-(∑x ∈ s, d x/(t-x)^2)) t := by
    have hh : ∀x ∈ s, HasDerivAt (fun u : ℝ => d x/(u-x)) (-(d x/(t-x)^2)) t := by
      intro x hx
      have hu := (hasDerivAt_const t (d x)).div ((hasDerivAt_id t).sub_const x) (by linarith [(hd x hx).1] : t-x ≠ 0)
      convert hu using 1 <;> first | rfl | simp [neg_div]
    convert (hasDerivAt_const t c).add (HasDerivAt.fun_sum hh) using 1
    all_goals first | rfl | simp [Finset.sum_neg_distrib]
  have hder' : HasDerivAt (fun u => barrier p (Function.update z j (z j+u)) i)
      (-(∑x ∈ s, d x/(t-x)^2)) t := by
    apply hder.congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds ht] with u hu
    exact he u hu.le
  have hdval := (hasDerivAt_barrier_ray p z i j (hz.update j ht.le).pos.ne').unique hder'
  rw [hdval]
  constructor
  · exact neg_nonpos.mpr (Finset.sum_nonneg (fun x hx => div_nonneg (hd x hx).2.le (sq_nonneg _)))
  · have he0 := he 0 le_rfl
    simp only [add_zero,Function.update_eq_self] at he0
    rw [he t ht.le,he0,mul_neg,sub_neg_eq_add,add_assoc,Finset.mul_sum,←Finset.sum_add_distrib]
    exact add_le_add le_rfl (Finset.sum_le_sum (fun x hx => fractions_tangent (hd x hx).1 (hd x hx).2.le ht.le))

lemma pderiv_commute {R : Type uR6} [CommRing R] (p : MvPolynomial I R) (i j : I) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p)=MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  by_cases hij : i=j
  · subst j; rfl
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    by_cases hki : k=i
    · subst k
      simp [MvPolynomial.pderiv_X,hij,hp,add_comm]
    · by_cases hkj : k=j
      · subst k
        simp [MvPolynomial.pderiv_X,Ne.symm hij,hp,add_comm]
      · simp [MvPolynomial.pderiv_X,hki,hkj,hp]

omit [DecidableEq I] in
lemma RealStable.sub_pderiv {p : MvPolynomial I ℝ} (hp : RealStable p) (j : I) :
    RealStable (p-MvPolynomial.pderiv j p) := by
  classical
  simpa only [RealStable,map_sub,MvPolynomial.pderiv_map] using Stable.sub_pderiv hp j

omit [DecidableEq I] in
lemma eval_sub_pderiv {p : MvPolynomial I ℝ} {w : I → ℝ}
    (hw : MvPolynomial.eval w p ≠ 0) (j : I) :
    MvPolynomial.eval w (p-MvPolynomial.pderiv j p)=MvPolynomial.eval w p*(1-barrier p w j) := by
  simp only [map_sub,barrier]
  field_simp

lemma barrier_sub_pderiv {p : MvPolynomial I ℝ} {w : I → ℝ}
    (hw : MvPolynomial.eval w p ≠ 0) (i j : I) (hj : 1-barrier p w j ≠ 0) :
    barrier (p-MvPolynomial.pderiv j p) w i =
      barrier p w i-crossBarrier p w i j/(1-barrier p w j) := by
  have hne : MvPolynomial.eval w p-MvPolynomial.eval w (MvPolynomial.pderiv j p) ≠ 0 := by
    intro he
    have he' := sub_eq_zero.mp he
    apply hj
    simp [barrier,←he',hw]
  simp only [barrier,crossBarrier,map_sub,pderiv_commute p i j]
  field_simp
  ring

lemma barrier_shift [Fintype I] {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) (j : I) {δ : ℝ} (hδ : 0 < δ) (hh : barrier p z j+1/δ ≤ 1) :
    Above (p-MvPolynomial.pderiv j p) (Function.update z j (z j+δ)) ∧
      ∀i, barrier (p-MvPolynomial.pderiv j p) (Function.update z j (z j+δ)) i ≤ barrier p z i := by
  have hzq : Above (p-MvPolynomial.pderiv j p) z := by
    intro s hs
    rw [eval_sub_pderiv (hz.add hs).pos.ne']
    apply mul_pos (hz.add hs).pos
    have hm := barrier_add_le hp hz hs j
    have hpos := one_div_pos.mpr hδ
    linarith
  refine ⟨hzq.update j hδ.le,fun i => ?_⟩
  let w := Function.update z j (z j+δ)
  have hw := (hz.update j hδ.le).pos
  have hm : 1/δ ≤ 1-barrier p w j := by
    have hu := barrier_update_le hp hz j j hδ.le
    change barrier p w j ≤ _ at hu
    linarith
  have hpos : 0 < 1-barrier p w j := lt_of_lt_of_le (one_div_pos.mpr hδ) hm
  obtain ⟨hf,ht⟩ := barrier_ray_tangent hp hz i j hδ
  change crossBarrier p w i j ≤ 0 at hf
  change barrier p w i-δ*crossBarrier p w i j ≤ barrier p z i at ht
  rw [barrier_sub_pderiv hw.ne' i j hpos.ne']
  apply le_trans _ ht
  change barrier p w i-crossBarrier p w i j/(1-barrier p w j) ≤ barrier p w i-δ*crossBarrier p w i j
  apply sub_le_sub_left
  rw [le_div_iff₀ hpos]
  have he : 1 ≤ δ*(1-barrier p w j) := by
    simpa only [mul_comm] using (div_le_iff₀ hδ).mp hm
  have hm' := mul_le_mul_of_nonpos_left he hf
  linarith

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.DeterminantCalculus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma view_derivative (j : I) (p : MvPolynomial I R) :
    (view j p).derivative=view j (MvPolynomial.pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    rw [map_mul,Polynomial.derivative_mul,MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,hp]
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma view_zero (j : I) (p : MvPolynomial I R) :
    (view j p).eval 0=zeroSub j p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p i hp =>
    by_cases hi : i=j
    · subst i; simp
    · simp [hi,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma zeroDiff_coeff (j : I) (p : MvPolynomial I R) :
    zeroDiff j p=(view j p).coeff 0-(view j p).coeff 1 := by
  rw [zeroDiff,map_sub,←view_zero,←view_zero,←view_derivative]
  simp [←coeff_zero_eq_eval_zero,coeff_derivative]

omit [Fintype D] [DecidableEq D] in
lemma view_affine_entry (j : I) (c : R) (a : I → R) :
    view j (MvPolynomial.C c+∑i, MvPolynomial.X i*MvPolynomial.C (a i))=
    C (MvPolynomial.C c+∑i ∈ Finset.univ.erase j, MvPolynomial.X i*MvPolynomial.C (a i))+
      X*C (MvPolynomial.C (a j)) := by
  simp only [map_add,map_sum,map_mul,view_C,view_X]
  rw [←Finset.add_sum_erase Finset.univ
    (fun i => (if i=j then X else C (MvPolynomial.X i))*C (MvPolynomial.C (a i))) (Finset.mem_univ j)]
  simp only [ite_true]
  have hh : ∑i ∈ Finset.univ.erase j,
      (if i=j then X else C (MvPolynomial.X i))*C (MvPolynomial.C (a i))=
      ∑i ∈ Finset.univ.erase j, C (MvPolynomial.X i)*C (MvPolynomial.C (a i)) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [ite_eq_right (Finset.mem_erase.mp hi).1]
  rw [hh]
  abel

omit [Fintype D] [DecidableEq D] in
lemma view_baseMatrix (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    (M.map MvPolynomial.C + ∑i, (MvPolynomial.X i : MvPolynomial I R) •
      (A i).map MvPolynomial.C).map (view j)=
      (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).map Polynomial.C +
        (X : (MvPolynomial I R)[X]) • ((A j).map MvPolynomial.C).map Polynomial.C := by
  apply Matrix.ext
  intro a b
  simp only [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  exact view_affine_entry j (M a b) (fun i => A i a b)

lemma view_basePencil (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    view j (basePencil M A)=
      ((M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).map Polynomial.C +
        (X : (MvPolynomial I R)[X]) • ((A j).map MvPolynomial.C).map Polynomial.C).det := by
  unfold basePencil
  rw [(view j).map_det]
  exact congrArg Matrix.det (view_baseMatrix j M A)

lemma zeroDiff_basePencil (j : I) (M : Matrix D D R) (A : I → Matrix D D R) :
    zeroDiff j (basePencil M A)=
      (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C).det-
      detLinear (M.map MvPolynomial.C + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map MvPolynomial.C) ((A j).map MvPolynomial.C) := by
  rw [zeroDiff_coeff,view_basePencil,det_linear_pencil_coeff_one]
  congr 1
  rw [coeff_zero_eq_eval_zero,show Polynomial.eval (0 : MvPolynomial I R)=Polynomial.evalRingHom 0 from rfl,
    (Polynomial.evalRingHom (0 : MvPolynomial I R)).map_det]
  congr 1
  apply Matrix.ext
  intro a b
  simp

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.MixedPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma diffProduct_foldl (dirs : List I) (p : MvPolynomial I R) :
    diffProduct dirs p=dirs.foldl (fun q j => q-MvPolynomial.pderiv j q) p := by
  induction dirs generalizing p with
  | nil => rfl
  | cons j dirs ih => exact ih _

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma diffProduct_perm {s t : List I} (h : s.Perm t) (p : MvPolynomial I R) :
    diffProduct s p=diffProduct t p := by
  induction h generalizing p with
  | nil => rfl
  | cons j h ih => simpa only [diffProduct_cons] using ih _
  | swap i j s =>
    simp only [diffProduct_cons]
    apply congrArg (diffProduct s)
    simp only [map_sub]
    rw [pderiv_commute p i j]
    abel
  | trans h₁ h₂ ih₁ ih₂ => exact (ih₁ p).trans (ih₂ p)

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma eval_zero_zeroSub (j : I) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (zeroSub j p)=MvPolynomial.eval (fun _ => 0) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p i hp =>
    by_cases hi : i=j
    · subst i; simp
    · simp [hi]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma zeroSub_pderiv {j i : I} (h : i ≠ j) (p : MvPolynomial I R) :
    zeroSub j (MvPolynomial.pderiv i p)=MvPolynomial.pderiv i (zeroSub j p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    by_cases hk : k=j
    · subst k; simp [Ne.symm h]
    · by_cases hki : k=i
      · subst k; simp [h,hp]
      · simp [hk,hki,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma diffProduct_zeroSub (j : I) (dirs : List I) (h : j ∉ dirs) (p : MvPolynomial I R) :
    diffProduct dirs (zeroSub j p)=zeroSub j (diffProduct dirs p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    have hi : i ≠ j := fun he => h (by simp [he])
    have hj : j ∉ dirs := fun hj => h (List.mem_cons_of_mem _ hj)
    simp only [diffProduct_cons]
    rw [←zeroSub_pderiv hi,←map_sub,ih hj]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma eval_zero_diffProduct_cons (j : I) (dirs : List I) (h : j ∉ dirs) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (diffProduct (j::dirs) p)=
      MvPolynomial.eval (fun _ => 0) (diffProduct dirs (zeroDiff j p)) := by
  rw [diffProduct_cons,zeroDiff,diffProduct_zeroSub j dirs h,eval_zero_zeroSub]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Affine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uO uO2 uO3

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma zeroDiff_update (j : I) (M B : Matrix D D R) (A : I → Matrix D D R) :
    zeroDiff j (basePencil M (Function.update A j B))=
      (M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)).det-
      detLinear (M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
        (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)) (B.map (MvPolynomial.C : R →+* MvPolynomial I R)) := by
  rw [zeroDiff_basePencil,Function.update_self]
  have hh : ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) •
      ((Function.update A j B) i).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [hh]

omit [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] in
lemma matrix_map_mean {O : Type uO} [Fintype O] (w : O → R) (B : O → Matrix D D R) :
    (∑o, w o • B o).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      ∑o, (MvPolynomial.C (w o) : MvPolynomial I R) • (B o).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
  apply Matrix.ext
  intro a b
  simp [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]

lemma zeroDiff_affine {O : Type uO2} [Fintype O] (j : I) (M : Matrix D D R)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    zeroDiff j (basePencil M (Function.update A j (∑o, w o • B o)))=
      ∑o, w o • zeroDiff j (basePencil M (Function.update A j (B o))) := by
  simp only [zeroDiff_update]
  let N := M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i ∈ Finset.univ.erase j,
    (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)
  change N.det-detLinear N ((∑o, w o • B o).map (MvPolynomial.C : R →+* MvPolynomial I R))=
    ∑o, w o • (N.det-detLinear N ((B o).map (MvPolynomial.C : R →+* MvPolynomial I R)))
  rw [matrix_map_mean,map_sum]
  simp only [map_smul,smul_sub,Finset.sum_sub_distrib,←Finset.sum_smul,hw,one_smul]
  congr 1
  apply Finset.sum_congr rfl
  intro o _
  exact MvPolynomial.C_mul'

lemma mixedEval_affine_cons {O : Type uO3} [Fintype O] (j : I) (dirs : List I) (hj : j ∉ dirs)
    (M : Matrix D D R) (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R)
    (hw : ∑o, w o=1) :
    mixedEval (j::dirs) M (Function.update A j (∑o, w o • B o))=
      ∑o, w o * mixedEval (j::dirs) M (Function.update A j (B o)) := by
  simp only [mixedEval,eval_zero_diffProduct_cons j dirs hj]
  rw [zeroDiff_affine j M A w B hw,map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro o _
  rw [map_smul]
  simp only [←MvPolynomial.C_mul',map_mul,MvPolynomial.eval_C]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.RankOne
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma det_sub_rankOne (M : Matrix D D R) (u v : D → R) :
    (M-Matrix.vecMulVec u v).det=M.det-detLinear M (Matrix.vecMulVec u v) := by
  simpa only [Matrix.neg_vecMulVec,sub_eq_add_neg,map_neg] using det_add_rankOne M (-u) v

omit [Fintype D] [DecidableEq D] in
lemma sum_pencil_update_zero (A : I → Matrix D D R) (j : I) :
    ∑i, (MvPolynomial.X i : MvPolynomial I R) • ((Function.update A j 0) i).map (MvPolynomial.C : R →+* MvPolynomial I R)=
    ∑i ∈ Finset.univ.erase j, (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R) := by
  rw [←Finset.add_sum_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self,Matrix.map_zero,map_zero,smul_zero,zero_add]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]

lemma zeroDiff_rankOne (M : Matrix D D R) (A : I → Matrix D D R) (j : I)
    (u v : D → R) (h : A j=Matrix.vecMulVec u v) :
    zeroDiff j (basePencil M A)=basePencil (M-A j) (Function.update A j 0) := by
  rw [zeroDiff_basePencil,basePencil,sum_pencil_update_zero]
  have hm : (A j).map (MvPolynomial.C : R →+* MvPolynomial I R)=
      Matrix.vecMulVec (fun a => MvPolynomial.C (u a)) (fun a => MvPolynomial.C (v a)) := by
    rw [h]
    apply Matrix.ext
    intro a b
    simp [Matrix.vecMulVec,Matrix.map_apply]
  rw [hm,←det_sub_rankOne]
  apply congrArg Matrix.det
  rw [←hm]
  apply Matrix.ext
  intro a b
  simp only [Matrix.sub_apply,Matrix.map_apply,Matrix.add_apply,map_sub]
  abel

omit [DecidableEq I] in
lemma basePencil_eval (M : Matrix D D R) (A : I → Matrix D D R) (z : I → R) :
    MvPolynomial.eval z (basePencil M A)=(M+∑i, z i • A i).det := by
  unfold basePencil
  rw [(MvPolynomial.eval z).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change MvPolynomial.eval z ((M.map (MvPolynomial.C : R →+* MvPolynomial I R) + ∑i,
    (MvPolynomial.X i : MvPolynomial I R) • (A i).map (MvPolynomial.C : R →+* MvPolynomial I R)) a b)=_
  simp [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma mixedEval_nil (M : Matrix D D R) (A : I → Matrix D D R) : mixedEval [] M A=M.det := by
  rw [mixedEval,diffProduct_nil,basePencil_eval]
  simp

lemma mixedEval_rankOne (dirs : List I) (hd : dirs.Nodup) (M : Matrix D D R)
    (A : I → Matrix D D R) (hA : ∀i ∈ dirs, ∃u v, A i=Matrix.vecMulVec u v) :
    mixedEval dirs M A=(M-(dirs.map A).sum).det := by
  induction dirs generalizing M A with
  | nil => simp [mixedEval_nil]
  | cons j dirs ih =>
    have hj : j ∉ dirs := (List.nodup_cons.mp hd).1
    obtain ⟨u,v,hjv⟩ := hA j (List.mem_cons_self)
    have he : mixedEval (j::dirs) M A=mixedEval dirs (M-A j) (Function.update A j 0) := by
      rw [mixedEval,eval_zero_diffProduct_cons j dirs hj,zeroDiff_rankOne M A j u v hjv]
      rfl
    rw [he,ih (List.nodup_cons.mp hd).2]
    · have hu : dirs.map (Function.update A j 0)=dirs.map A := by
        apply List.map_congr_left
        intro i hi
        exact Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi)) _ _
      rw [hu,List.map_cons,List.sum_cons]
      apply congrArg Matrix.det
      abel
    · intro i hi
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (List.mem_cons_of_mem _ hi)

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.RootBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Polynomial Finset Matrix
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in
lemma pencil_eval [CommRing R] (A : I → Matrix D D R) (z : I → R) :
    MvPolynomial.eval z (pencil A)=(∑i, z i • A i).det := by
  let M : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.eval z) M.det = _
  rw [(MvPolynomial.eval z).map_det M]
  congr 1
  ext a b
  change (MvPolynomial.eval z) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] in
lemma pencil_map {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S) (A : I → Matrix D D R) :
    (pencil A).map f=pencil (fun i => (A i).map f) := by
  let M : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change (MvPolynomial.map f) M.det = _
  rw [(MvPolynomial.map f).map_det M]
  unfold pencil
  congr 1
  apply Matrix.ext
  intro a b
  change (MvPolynomial.map f) (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  simp [Matrix.map_apply]

lemma posSemidef_complex {A : Matrix D D ℝ} (hA : A.PosSemidef) :
    (A.map (algebraMap ℝ ℂ)).PosSemidef := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.isHermitian
  have he : Sᴴ*S=A := by rw [hS.eq]; exact CFC.sqrt_mul_sqrt_self A hA.nonneg
  rw [←he]
  have hm : (Sᴴ*S).map (algebraMap ℝ ℂ)=(S.map (algebraMap ℝ ℂ))ᴴ*S.map (algebraMap ℝ ℂ) := by
    rw [Matrix.map_mul]
    congr 1
    ext i j
    simp
  rw [hm]
  exact Matrix.posSemidef_conjTranspose_mul_self _

omit [DecidableEq I] in
lemma real_pencil_stable (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) : RealStable (pencil A) := by
  unfold RealStable
  rw [pencil_map]
  apply determinantPencil_stable _ (fun i => posSemidef_complex (hA i))
  have he : ∑i, (A i).map (algebraMap ℝ ℂ)=(1 : Matrix D D ℂ) := by
    ext a b
    simp only [Matrix.sum_apply,Matrix.map_apply]
    rw [←map_sum]
    rw [←Matrix.sum_apply,hsum]
    simp [Matrix.one_apply]
  rw [he]
  exact Matrix.PosDef.one

omit [DecidableEq I] in
lemma pencil_above (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {t : ℝ} (ht : 0 < t) : Above (pencil A) (fun _ => t) := by
  intro s hs
  rw [pencil_eval]
  have he : ∑i, ((fun _ : I => t)+s) i • A i=t • (1 : Matrix D D ℝ)+∑i,s i • A i := by
    simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib,←Finset.smul_sum,hsum]
  rw [he]
  exact ((Matrix.PosDef.one.smul ht).add_posSemidef
    (Matrix.posSemidef_sum _ (fun i _ => (hA i).smul (hs i)))).det_pos

omit [Fintype D] [DecidableEq D] in
lemma sum_update_smul [CommRing R] (A : I → Matrix D D R) (z : I → R) (j : I) (u : R) :
    ∑i, (Function.update z j (z j+u)) i • A i=(∑i, z i • A i)+u • A j := by
  classical
  have he : Function.update z j (z j+u)=z+Pi.single j u := by
    ext i
    by_cases hi : i=j
    · subst i; simp
    · simp [Function.update_of_ne hi,Pi.single_eq_of_ne hi]
  rw [he]
  simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · simp

lemma ray_pencil_constant (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) (t : ℝ) :
    ray (pencil A) (fun _ => t) j=((C t : ℝ[X]) • (1 : Matrix D D ℝ[X])+(X : ℝ[X]) • (A j).map C).det := by
  apply Polynomial.funext
  intro u
  rw [ray_eval,pencil_eval,sum_update_smul,←Finset.smul_sum,hsum]
  rw [show Polynomial.eval u = Polynomial.evalRingHom u from rfl, (Polynomial.evalRingHom u).map_det]
  congr 1
  ext a b
  simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,apply_ite]
  ring

lemma ray_pencil_factor (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) {t : ℝ} (ht : t ≠ 0) :
    ray (pencil A) (fun _ => t) j=C (t^(Fintype.card D)) * (1+(X : ℝ[X]) • ((t⁻¹) • A j).map C).det := by
  rw [ray_pencil_constant A hsum]
  have he : (C t : ℝ[X]) • (1 : Matrix D D ℝ[X])+(X : ℝ[X]) • (A j).map C=
      (C t : ℝ[X]) • (1+(X : ℝ[X]) • ((t⁻¹) • A j).map C) := by
    ext a b
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.map_apply,smul_eq_mul,map_mul]
    rw [mul_add]
    congr 1
    rw [←mul_assoc,←mul_assoc,mul_comm (C t) X,mul_assoc X,←map_mul,mul_inv_cancel₀ ht,map_one,mul_one]
  rw [he,Matrix.det_smul,map_pow]

lemma pencil_barrier (A : I → Matrix D D ℝ) (hsum : ∑i, A i=1) (j : I) {t : ℝ} (ht : t ≠ 0) :
    barrier (pencil A) (fun _ => t) j=(A j).trace/t := by
  have hnum : MvPolynomial.eval (fun _ => t) (MvPolynomial.pderiv j (pencil A))=
      t^(Fintype.card D)*((t⁻¹) • A j).trace := by
    rw [←ray_zero,←ray_derivative,ray_pencil_factor A hsum j ht,Polynomial.derivative_mul]
    simp only [Polynomial.derivative_C,zero_mul,zero_add,Polynomial.eval_mul,Polynomial.eval_C,
      Matrix.derivative_det_one_add_X_smul]
  have hden : MvPolynomial.eval (fun _ => t) (pencil A)=t^(Fintype.card D) := by
    rw [pencil_eval,←Finset.smul_sum,hsum,Matrix.det_smul,Matrix.det_one,mul_one]
  rw [barrier,hnum,hden,Matrix.trace_smul]
  simp only [smul_eq_mul]
  field_simp

omit [Fintype I] in
lemma shiftVector_cons (j : I) (dirs : List I) (δ : ℝ) :
    shiftVector (j::dirs) δ=Pi.single j δ+shiftVector dirs δ := by
  simp [shiftVector]

lemma many_barrier_shifts {p : MvPolynomial I ℝ} (hp : RealStable p) {z : I → ℝ}
    (hz : Above p z) {δ φ : ℝ} (hδ : 0 < δ) (hφ : φ+1/δ ≤ 1)
    (hb : ∀i, barrier p z i ≤ φ) (dirs : List I) :
    Above (realDifferentialProduct dirs p) (z+shiftVector dirs δ) ∧
      ∀i, barrier (realDifferentialProduct dirs p) (z+shiftVector dirs δ) i ≤ φ := by
  induction dirs generalizing p z with
  | nil => simpa [realDifferentialProduct,shiftVector] using And.intro hz hb
  | cons j dirs ih =>
    obtain ⟨hw,hb'⟩ := barrier_shift hp hz j hδ (by linarith [hb j])
    have hh := ih (hp.sub_pderiv j) hw (fun i => (hb' i).trans (hb i))
    simpa only [realDifferentialProduct,List.foldl_cons,shiftVector_cons,update_add_single,add_assoc] using hh

lemma shiftVector_univ (δ : ℝ) : shiftVector (Finset.univ.toList : List I) δ=fun _ => δ := by
  ext i
  simp [shiftVector,Finset.sum_apply,Pi.single_apply]

lemma skew_root_bound (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {ε : ℝ} (hε : 0 < ε) (htr : ∀i, (A i).trace ≤ ε) :
    Above (realDifferentialProduct Finset.univ.toList (pencil A)) (fun _ => (1+Real.sqrt ε)^2) := by
  let t := ε+Real.sqrt ε
  let δ := 1+Real.sqrt ε
  have ht : 0 < t := add_pos_of_pos_of_nonneg hε (Real.sqrt_nonneg _)
  have hδ : 0 < δ := add_pos_of_pos_of_nonneg zero_lt_one (Real.sqrt_nonneg _)
  have hid : ε/t+1/δ=1 := by
    have hsq := Real.sq_sqrt hε.le
    dsimp [t,δ] at *
    field_simp
    linarith
  have hb : ∀i, barrier (pencil A) (fun _ => t) i ≤ ε/t := by
    intro i
    rw [pencil_barrier A hsum i ht.ne']
    exact div_le_div_of_nonneg_right (htr i) ht.le
  have hh := (many_barrier_shifts (real_pencil_stable A hA hsum) (pencil_above A hA hsum ht)
    hδ hid.le hb (Finset.univ.toList : List I)).1
  rw [shiftVector_univ] at hh
  have he : (fun _ : I => t)+(fun _ => δ)=fun _ => (1+Real.sqrt ε)^2 := by
    ext i
    simp only [Pi.add_apply]
    dsimp [t,δ]
    linarith [Real.sq_sqrt hε.le]
  rwa [he] at hh

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.OptionalDirections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma coefficientX_pderiv (i : I) (p : MvPolynomial (Option I) R) :
    coefficientX (MvPolynomial.pderiv (some i) p)=MvPolynomial.pderiv i (coefficientX p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp =>
    rw [MvPolynomial.pderiv_mul,map_add,map_mul,map_mul,map_mul,MvPolynomial.pderiv_mul,hp]
    cases k with
    | none => simp
    | some k => by_cases hk : k=i <;> simp [hk]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma coefficientX_diffProduct (dirs : List I) (p : MvPolynomial (Option I) R) :
    coefficientX (diffProduct (dirs.map some) p)=diffProduct dirs (coefficientX p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    simp only [List.map_cons,diffProduct_cons,ih,map_sub,coefficientX_pderiv]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma eval_zero_coefficientX (p : MvPolynomial (Option I) R) :
    MvPolynomial.eval (fun _ => 0) (coefficientX p)=uniSlice p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp =>
    cases k <;> simp only [map_mul,coefficientX_X,uniSlice_X,Option.elim,
      MvPolynomial.eval_C,MvPolynomial.eval_X,mul_zero,hp]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma uniSlice_map (f : R →+* S) (p : MvPolynomial (Option I) R) :
    uniSlice (p.map f)=(uniSlice p).map f := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp,hq]
  | mul_X p k hp => cases k <;> simp [hp]

omit [Fintype I] [Fintype D] [DecidableEq D] [DecidableEq I] in
lemma diffProduct_map (f : R →+* S) (dirs : List I) (p : MvPolynomial I R) :
    diffProduct dirs (p.map f)=(diffProduct dirs p).map f := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih =>
    simp only [diffProduct_cons,MvPolynomial.pderiv_map,←map_sub,ih]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma uniSlice_eq_slice (p : MvPolynomial (Option I) ℂ) :
    uniSlice p=slice p (fun _ => 0) none := by
  change MvPolynomial.eval₂ Polynomial.C (fun o : Option I => o.elim X (fun _ => 0)) p = _
  unfold slice
  apply congrArg (fun z => MvPolynomial.eval₂ Polynomial.C z p)
  funext i
  cases i <;> simp

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Interlacing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uα uι uι2 uι3

section

noncomputable section
open Polynomial Finset Set
open scoped Topology
namespace StrongThinTree.MSS.Selection

lemma coeff_prod_negative (s : Multiset ℝ) (hs : ∀r ∈ s, r < 0) :
    (∀k, 0 ≤ ((s.map (fun r => (X-C r : ℝ[X]))).prod).coeff k) ∧
      ∀k ≤ s.card, 0 < ((s.map (fun r => (X-C r : ℝ[X]))).prod).coeff k := by
  induction s using Multiset.induction_on with
  | empty =>
    simp only [Multiset.map_zero,Multiset.prod_zero,Multiset.card_zero]
    constructor
    · intro k; simp only [coeff_one]; split_ifs <;> norm_num
    · intro k hk
      have : k=0 := by omega
      subst k
      simp
  | @cons r s ih =>
    have hr : r < 0 := hs r (Multiset.mem_cons_self _ _)
    obtain ⟨hn,hp⟩ := ih (fun a ha => hs a (Multiset.mem_cons_of_mem ha))
    simp only [Multiset.map_cons,Multiset.prod_cons,Multiset.card_cons]
    constructor
    · intro k
      cases k with
      | zero => simpa only [sub_mul,coeff_sub,coeff_X_mul_zero,coeff_C_mul,zero_sub,neg_mul] using mul_nonneg (neg_nonneg.mpr hr.le) (hn 0)
      | succ k =>
        simp only [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
        exact sub_nonneg.mpr (le_trans (mul_nonpos_of_nonpos_of_nonneg hr.le (hn _)) (hn _))
    · intro k hk
      cases k with
      | zero => simpa only [sub_mul,coeff_sub,coeff_X_mul_zero,coeff_C_mul,zero_sub,neg_mul] using mul_pos (neg_pos.mpr hr) (hp 0 (Nat.zero_le _))
      | succ k =>
        simp only [sub_mul,coeff_sub,coeff_X_mul,coeff_C_mul]
        exact sub_pos.mpr (lt_of_le_of_lt (mul_nonpos_of_nonpos_of_nonneg hr.le (hn _)) (hp k (by omega)))

lemma coeff_pos_of_negative_roots {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits)
    (hr : ∀r ∈ p.roots, r < 0) : ∀k ≤ p.natDegree, 0 < p.coeff k := by
  have hh := (coeff_prod_negative p.roots hr).2
  rw [←hs.eq_prod_roots_of_monic hm] at hh
  simpa only [←hs.natDegree_eq_card_roots] using hh

lemma eval_pos_of_nonneg_coeff {p : ℝ[X]} (hp : ∀k, 0 ≤ p.coeff k) (h0 : 0 < p.coeff 0)
    {x : ℝ} (hx : 0 ≤ x) : 0 < p.eval x := by
  rw [Polynomial.eval_eq_sum]
  apply lt_of_lt_of_le h0
  have hm : 0 ∈ p.support := Polynomial.mem_support_iff.mpr h0.ne'
  simpa only [Polynomial.sum,pow_zero,mul_one] using Finset.single_le_sum
    (fun k _ => mul_nonneg (hp k) (pow_nonneg hx k)) hm

lemma coeff_pos_of_nonneg {p : ℝ[X]} (hm : p.Monic) (hs : p.Splits)
    (hp : ∀k, 0 ≤ p.coeff k) (h0 : 0 < p.coeff 0) :
    ∀k ≤ p.natDegree, 0 < p.coeff k := by
  apply coeff_pos_of_negative_roots hm hs
  intro r hr
  by_contra hh
  exact (eval_pos_of_nonneg_coeff hp h0 (le_of_not_gt hh)).ne'
    ((Polynomial.mem_roots hm.ne_zero).mp hr)

lemma positive_coeff_path {α : Type uα} [TopologicalSpace α] [PreconnectedSpace α]
    (p : α → ℝ[X]) (d : ℕ) (hc : ∀k, Continuous (fun t => (p t).coeff k))
    (hm : ∀t, (p t).Monic) (hs : ∀t, (p t).Splits) (hd : ∀t, (p t).natDegree=d)
    (h0 : ∀t, 0 < (p t).coeff 0) {a : α} (ha : ∀k ≤ d, 0 < (p a).coeff k) :
    ∀t k, k ≤ d → 0 < (p t).coeff k := by
  let C : Set α := {t | ∀k ≤ d, 0 ≤ (p t).coeff k}
  let G : Set α := {t | ∀k ≤ d, 0 < (p t).coeff k}
  have he : C=G := by
    ext t
    constructor
    · intro ht k hk
      have hp : ∀k, 0 ≤ (p t).coeff k := by
        intro k
        by_cases hk' : k ≤ d
        · exact ht k hk'
        · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hd]; omega)]
      exact coeff_pos_of_nonneg (hm t) (hs t) hp (h0 t) k (by rwa [hd])
    · exact fun ht k hk => (ht k hk).le
  have hC : IsClosed C := by
    have hh : C=⋂k : Fin (d+1), {t | 0 ≤ (p t).coeff k} := by
      ext t
      simp only [C,Set.mem_ofPred_eq,Set.mem_iInter]
      exact ⟨fun h k => h k (by omega),fun h k hk => h ⟨k,by omega⟩⟩
    rw [hh]
    exact isClosed_iInter (fun k => isClosed_le continuous_const (hc k))
  have hG : IsOpen G := by
    have hh : G=⋂k : Fin (d+1), {t | 0 < (p t).coeff k} := by
      ext t
      simp only [G,Set.mem_ofPred_eq,Set.mem_iInter]
      exact ⟨fun h k => h k (by omega),fun h k hk => h ⟨k,by omega⟩⟩
    rw [hh]
    exact isOpen_iInter_of_finite (fun k => isOpen_lt continuous_const (hc k))
  have heq : G=Set.univ := (IsClopen.eq_univ ⟨he ▸ hC,hG⟩ ⟨a,ha⟩)
  intro t
  have ht : t ∈ G := heq.symm ▸ Set.mem_univ t
  exact ht

lemma monic_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d) (t : ℝ) :
    ((1-t) • p + t • q).IsMonicOfDegree d := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact natDegree_add_le_of_degree_le
      ((natDegree_smul_le _ _).trans hp.natDegree_eq.le)
      ((natDegree_smul_le _ _).trans hq.natDegree_eq.le)
  · rw [coeff_add, coeff_smul, coeff_smul]
    have hp' : p.coeff d=1 := hp.natDegree_eq ▸ hp.monic.coeff_natDegree
    have hq' : q.coeff d=1 := hq.natDegree_eq ▸ hq.monic.coeff_natDegree
    simp only [hp',hq',smul_eq_mul,mul_one]
    ring

lemma negative_roots_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d)
    (hs : ∀t ∈ Set.Icc (0 : ℝ) 1, ((1-t) • p + t • q).Splits)
    (hr : ∀r ∈ p.roots, r < 0) (h0p : 0 < p.coeff 0) (h0q : 0 < q.coeff 0) :
    ∀r ∈ q.roots, r < 0 := by
  let : PreconnectedSpace (Set.Icc (0 : ℝ) 1) := Subtype.preconnectedSpace isPreconnected_Icc
  let f : Set.Icc (0 : ℝ) 1 → ℝ[X] := fun t => (1-t.val) • p + t.val • q
  have hh := positive_coeff_path f d
    (fun k => by
      simp only [f,coeff_add,coeff_smul,smul_eq_mul]
      fun_prop)
    (fun t => (monic_segment hp hq t).monic)
    (fun t => hs t t.property)
    (fun t => (monic_segment hp hq t).natDegree_eq)
    (fun t => by
      simp only [f,coeff_add,coeff_smul,smul_eq_mul]
      have ht := t.property
      have hh : 0 < (1-t.val)*p.coeff 0+t.val*q.coeff 0 := by
        by_cases ht0 : t.val=0
        · simp [ht0,h0p]
        · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) h0p.le)
            (mul_pos (lt_of_le_of_ne ht.1 (Ne.symm ht0)) h0q)
      exact hh)
    (a := ⟨0,by simp⟩)
    (by
      simpa only [f,sub_zero,one_smul,zero_smul,add_zero,hp.natDegree_eq] using
        coeff_pos_of_negative_roots hp.monic (by simpa using hs 0 (by simp)) hr)
  have hqpos : ∀k ≤ d, 0 < q.coeff k := by
    simpa only [f,sub_self,zero_smul,one_smul,zero_add] using hh ⟨1,by simp⟩
  intro r hrq
  by_contra hnr
  have hn : ∀k, 0 ≤ q.coeff k := by
    intro k
    by_cases hk : k ≤ d
    · exact (hqpos k hk).le
    · rw [coeff_eq_zero_of_natDegree_lt (by rw [hq.natDegree_eq]; omega)]
  exact (eval_pos_of_nonneg_coeff hn h0q (le_of_not_gt hnr)).ne'
    ((mem_roots hq.ne_zero).mp hrq)

lemma roots_shift_iff {p : ℝ[X]} (hp : p ≠ 0) (x r : ℝ) :
    r ∈ (p.comp (X+C x)).roots ↔ r+x ∈ p.roots := by
  rw [mem_roots (comp_X_add_C_ne_zero_iff.mpr hp),mem_roots hp]
  simp [IsRoot,eval_comp]

lemma roots_lt_segment {p q : ℝ[X]} {d : ℕ}
    (hp : p.IsMonicOfDegree d) (hq : q.IsMonicOfDegree d)
    (hs : ∀t ∈ Set.Icc (0 : ℝ) 1, ((1-t) • p + t • q).Splits)
    {x : ℝ} (hr : ∀r ∈ p.roots, r < x) (hxq : 0 < q.eval x) :
    ∀r ∈ q.roots, r < x := by
  have hp' : (p.comp (X+C x)).IsMonicOfDegree d := by
    simpa using hp.comp one_ne_zero (isMonicOfDegree_X_add_one x)
  have hq' : (q.comp (X+C x)).IsMonicOfDegree d := by
    simpa using hq.comp one_ne_zero (isMonicOfDegree_X_add_one x)
  have hrp : ∀r ∈ (p.comp (X+C x)).roots, r < 0 := by
    intro r h
    have hh := hr (r+x) ((roots_shift_iff hp.ne_zero x r).mp h)
    linarith
  have hps : p.Splits := by simpa using hs 0 (by simp)
  have hp0 := coeff_pos_of_negative_roots hp'.monic (hps.comp_X_add_C x) hrp 0 (Nat.zero_le _)
  have hq0 : 0 < (q.comp (X+C x)).coeff 0 := by
    rw [coeff_zero_eq_eval_zero,eval_comp]
    simpa using hxq
  have hsr : ∀t ∈ Set.Icc (0 : ℝ) 1,
      ((1-t) • p.comp (X+C x) + t • q.comp (X+C x)).Splits := by
    intro t ht
    simpa only [add_comp,smul_comp] using (hs t ht).comp_X_add_C x
  have hh := negative_roots_segment hp' hq' hsr hrp hp0 hq0
  intro r h
  have hm : r-x ∈ (q.comp (X+C x)).roots := by
    rw [roots_shift_iff hq.ne_zero]
    simpa using h
  have hh' := hh _ hm
  linarith

lemma eval_pos_above_roots {p : ℝ[X]} (hp : p.Monic) (hs : p.Splits)
    {x : ℝ} (hr : ∀r ∈ p.roots, r < x) : 0 < p.eval x := by
  have hshift : ∀r ∈ (p.comp (X+C x)).roots, r < 0 := by
    intro r h
    have hh := hr (r+x) ((roots_shift_iff hp.ne_zero x r).mp h)
    linarith
  have hh := coeff_pos_of_negative_roots (hp.comp_X_add_C x) (hs.comp_X_add_C x)
    hshift 0 (Nat.zero_le _)
  simpa only [coeff_zero_eq_eval_zero,eval_comp,eval_add,eval_X,eval_C,zero_add] using hh

lemma monic_mean {ι : Type uι} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∑i, w i=1) :
    (∑i, w i • p i).IsMonicOfDegree d := by
  rw [isMonicOfDegree_iff]
  constructor
  · exact natDegree_sum_le_of_forall_le _ _ (fun i _ =>
      (natDegree_smul_le _ _).trans (hp i).natDegree_eq.le)
  · simp only [finsetSum_coeff,coeff_smul,smul_eq_mul]
    have hh : ∀i, (p i).coeff d=1 := fun i => (hp i).natDegree_eq ▸ (hp i).monic.coeff_natDegree
    simpa only [hh,mul_one] using hw

lemma selection_strict {ι : Type uι2} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∀i, 0 < w i)
    (hsum : ∑i, w i=1)
    (hs : ∀i t, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1-t) • (∑j, w j • p j) + t • p i).Splits)
    {x : ℝ} (hroot : ∀r ∈ (∑i, w i • p i).roots, r < x) :
    ∃i, ∀r ∈ (p i).roots, r < x := by
  have hne : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  let := hne
  have hm := monic_mean p hp w hsum
  have hsplit : (∑i, w i • p i).Splits := by
    simpa using hs (Classical.arbitrary ι) 0 (by simp)
  have he := eval_pos_above_roots hm.monic hsplit hroot
  have hei : ∃i, 0 < (p i).eval x := by
    by_contra! hh
    have hn : ∑i, w i*(p i).eval x ≤ 0 :=
      Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hw i).le (hh i))
    simp only [eval_finsetSum,eval_smul,smul_eq_mul] at he
    linarith
  obtain ⟨i,hi⟩ := hei
  exact ⟨i,roots_lt_segment hm (hp i) (hs i) hroot hi⟩

lemma selection {ι : Type uι3} [Fintype ι] (p : ι → ℝ[X]) {d : ℕ}
    (hp : ∀i, (p i).IsMonicOfDegree d) (w : ι → ℝ) (hw : ∀i, 0 < w i)
    (hsum : ∑i, w i=1)
    (hs : ∀i t, t ∈ Set.Icc (0 : ℝ) 1 →
      ((1-t) • (∑j, w j • p j) + t • p i).Splits)
    {b : ℝ} (hroot : ∀r ∈ (∑i, w i • p i).roots, r ≤ b) :
    ∃i, ∀r ∈ (p i).roots, r ≤ b := by
  classical
  by_contra! hn
  choose r hr hbr using hn
  have hne : Nonempty ι := by
    by_contra hn
    have : IsEmpty ι := not_nonempty_iff.mp hn
    simp at hsum
  let := hne
  have hmin : b < Finset.univ.inf' Finset.univ_nonempty r :=
    (Finset.lt_inf'_iff _).mpr (fun i _ => hbr i)
  obtain ⟨x,hbx,hxmin⟩ := exists_between hmin
  obtain ⟨i,hi⟩ := selection_strict p hp w hw hsum hs (fun a ha => (hroot a ha).trans_lt hbx)
  have hxi : x < r i := hxmin.trans_le (Finset.inf'_le _ (Finset.mem_univ i))
  exact (hi (r i) (hr i)).not_gt hxi

end StrongThinTree.MSS.Selection

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uO uO2

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

lemma univ_perm_cons (j : I) : (Finset.univ.toList : List I).Perm (j::(Finset.univ.erase j).toList) := by
  apply (List.perm_ext_iff_of_nodup (Finset.nodup_toList _) (List.nodup_cons.mpr
    ⟨by simp, Finset.nodup_toList _⟩)).mpr
  intro i
  simp
  tauto

lemma mixedEval_affine {O : Type uO} [Fintype O] (j : I) (M : Matrix D D R)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    mixedEval Finset.univ.toList M (Function.update A j (∑o, w o • B o))=
      ∑o, w o * mixedEval Finset.univ.toList M (Function.update A j (B o)) := by
  have hh : ∀A : I → Matrix D D R, mixedEval Finset.univ.toList M A=
      mixedEval (j::(Finset.univ.erase j).toList) M A := by
    intro A
    unfold mixedEval
    rw [diffProduct_perm (univ_perm_cons j)]
  simp only [hh]
  exact mixedEval_affine_cons j _ (by simp) M A w B hw

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma map_update (A : I → Matrix D D R) (j : I) (B : Matrix D D R) :
    (fun i => ((Function.update A j B) i).map Polynomial.C)=
      Function.update (fun i => (A i).map Polynomial.C) j (B.map Polynomial.C) := by
  funext i
  by_cases hi : i=j <;> simp [hi]

lemma mixedChar_affine {O : Type uO2} [Fintype O] (j : I)
    (A : I → Matrix D D R) (w : O → R) (B : O → Matrix D D R) (hw : ∑o, w o=1) :
    mixedChar (Function.update A j (∑o, w o • B o))=
      ∑o, Polynomial.C (w o) * mixedChar (Function.update A j (B o)) := by
  have hm : (∑o, w o • B o).map Polynomial.C=
      ∑o, Polynomial.C (w o) • (B o).map Polynomial.C := by
    apply Matrix.ext
    intro a b
    simp [Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply]
  simp only [mixedChar,map_update,hm]
  exact mixedEval_affine j _ _ (fun o => Polynomial.C (w o)) _ (by simpa using congrArg Polynomial.C hw)

lemma mixedChar_rankOne (A : I → Matrix D D R) (hA : ∀i, ∃u v, A i=Matrix.vecMulVec u v) :
    mixedChar A=(∑i, A i).charpoly := by
  unfold mixedChar
  rw [mixedEval_rankOne _ (Finset.nodup_toList _)]
  · rw [Finset.sum_map_toList]
    have he : (∑i, (A i).map Polynomial.C)=(∑i, A i).map Polynomial.C := by
      apply Matrix.ext
      intro a b
      simp [Matrix.sum_apply,Matrix.map_apply]
    rw [he]
    unfold Matrix.charpoly
    apply congrArg Matrix.det
    apply Matrix.ext
    intro a b
    by_cases hab : a=b <;> simp [Matrix.sub_apply,Matrix.smul_apply,Matrix.map_apply,hab]
  · intro i _
    obtain ⟨u,v,h⟩ := hA i
    refine ⟨fun a => Polynomial.C (u a),fun a => Polynomial.C (v a),?_⟩
    rw [h]
    apply Matrix.ext
    intro a b
    simp [Matrix.vecMulVec,Matrix.map_apply]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Monicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

lemma mixedChar_mean (j : I) (A : I → Matrix D D ℝ) (w : O → ℝ)
    (B : O → Matrix D D ℝ) (hw : ∑o, w o=1) :
    mixedChar (Function.update A j (∑o, w o • B o))=
      ∑o, w o • mixedChar (Function.update A j (B o)) := by
  simpa only [Polynomial.smul_eq_C_mul] using mixedChar_affine j A w B hw

lemma mixedChar_monic_partial (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (u v : I → O → D → ℝ) (hw : ∀i, ∑o, w i o=1)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (u i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃a b, A i=Matrix.vecMulVec a b) :
    (mixedChar A).IsMonicOfDegree (Fintype.card D) := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    rw [mixedChar_rankOne A (fun i => hfixed i (by simp))]
    exact ⟨Matrix.charpoly_natDegree_eq_dim _,Matrix.charpoly_monic _⟩
  | @insert j s hj ih =>
    let B : O → Matrix D D ℝ := fun o => Matrix.vecMulVec (u j o) (v j o)
    have hAj : A j=∑o, w j o • B o := hA j (by simp)
    have he : mixedChar A=∑o, w j o • mixedChar (Function.update A j (B o)) := by
      rw [←mixedChar_mean j A (w j) B (hw j)]
      congr 1
      rw [←hAj]
      simp
    rw [he]
    apply Selection.monic_mean _ _ (w j) (hw j)
    intro o
    apply ih
    · intro i hi
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (Finset.mem_insert_of_mem hi)
    · intro i hi
      by_cases hij : i=j
      · subst i
        exact ⟨u j o,v j o,by simp [B]⟩
      · rw [Function.update_of_ne hij]
        exact hfixed i (by simp [hij,hi])

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.RealRoots
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder ComplexOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [CommRing R]

omit [DecidableEq I] in
lemma coefficientX_fullPencil (A : I → Matrix D D R) :
    coefficientX (fullPencil A)=basePencil ((Polynomial.X : R[X]) • (1 : Matrix D D R[X]))
      (fun i => (A i).map Polynomial.C) := by
  let N : Matrix D D (MvPolynomial (Option I) R) := fun a b =>
    ∑i : Option I, MvPolynomial.X i * MvPolynomial.C ((i.elim (1 : Matrix D D R) A) a b)
  change coefficientX N.det = _
  unfold basePencil
  rw [(coefficientX (I := I) (R := R)).map_det N]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change coefficientX (∑i : Option I, MvPolynomial.X i * MvPolynomial.C ((i.elim 1 A) a b))=_
  simp only [Fintype.sum_option,Option.elim]
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
  by_cases h : a=b <;> simp [Matrix.one_apply,h]

lemma mixedChar_uniSlice (A : I → Matrix D D R) : mixedChar A=
    uniSlice (diffProduct ((Finset.univ.toList : List I).map some) (fullPencil A)) := by
  rw [←eval_zero_coefficientX,coefficientX_diffProduct,coefficientX_fullPencil]
  rfl

omit [DecidableEq I] in
lemma fullPencil_map {S : Type uS} [CommRing S] (f : R →+* S) (A : I → Matrix D D R) :
    (fullPencil A).map f=fullPencil (fun i => (A i).map f) := by
  unfold fullPencil
  rw [pencil_map]
  congr 1
  funext i
  cases i with
  | none => simp
  | some i => rfl

omit [DecidableEq I] in
lemma fullPencil_stable (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef) :
    RealStable (fullPencil A) := by
  unfold RealStable
  rw [fullPencil_map]
  apply determinantPencil_stable
  · intro i
    cases i with
    | none => exact Matrix.PosSemidef.one
    | some i => exact posSemidef_complex (hA i)
  · rw [Fintype.sum_option]
    simpa only [Option.elim] using (Matrix.PosDef.one.add_posSemidef
      (Matrix.posSemidef_sum Finset.univ (fun i _ => posSemidef_complex (hA i))))

lemma mixedChar_splits (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef) :
    (mixedChar A).Splits := by
  by_cases h0 : mixedChar A=0
  · rw [h0]; simp
  apply splits_of_upper_half_plane
  rw [mixedChar_uniSlice,←uniSlice_map,←diffProduct_map]
  have hs : Stable (diffProduct ((Finset.univ.toList : List I).map some)
      ((fullPencil A).map (algebraMap ℝ ℂ))) := by
    rw [diffProduct_foldl]
    exact (fullPencil_stable A hA).differentialProduct _
  rw [uniSlice_eq_slice]
  apply hs.slice_boundary _ (by simp) none
  rw [←uniSlice_eq_slice,diffProduct_map,uniSlice_map,←mixedChar_uniSlice]
  exact Polynomial.map_ne_zero h0

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.FiniteSelection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

omit [DecidableEq D] in
lemma rankOne_posSemidef (v : D → ℝ) : (Matrix.vecMulVec v v).PosSemidef := by
  simpa using Matrix.posSemidef_vecMulVec_self_star v

lemma mixedChar_segment (j : I) (A : I → Matrix D D ℝ) (B : Matrix D D ℝ) (t : ℝ) :
    (1-t) • mixedChar A+t • mixedChar (Function.update A j B)=
      mixedChar (Function.update A j ((1-t) • A j+t • B)) := by
  have hh := mixedChar_mean (O := Bool) j A (fun b => if b then t else 1-t)
    (fun b => if b then B else A j) (by simp)
  have hm : (∑b : Bool, (if b then t else 1-t) • (if b then B else A j))=
      (1-t) • A j+t • B := by
    rw [Fintype.sum_bool]
    simp only [Bool.false_eq_true,↓reduceIte]
    exact add_comm _ _
  rw [hm,Fintype.sum_bool] at hh
  simp only [Bool.false_eq_true,↓reduceIte] at hh
  rw [Function.update_eq_self] at hh
  rw [hh]
  exact add_comm _ _

omit [Fintype I] in
omit [DecidableEq D] in
lemma partial_posSemidef (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (v : I → O → D → ℝ) (hw : ∀i o, 0 ≤ w i o)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (v i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃o, A i=Matrix.vecMulVec (v i o) (v i o)) :
    ∀i, (A i).PosSemidef := by
  intro i
  by_cases hi : i ∈ s
  · rw [hA i hi]
    exact Matrix.posSemidef_sum _ (fun o _ => (rankOne_posSemidef _).smul (hw i o))
  · obtain ⟨o,ho⟩ := hfixed i hi
    rw [ho]
    exact rankOne_posSemidef _

lemma finite_selection_partial (s : Finset I) (A : I → Matrix D D ℝ)
    (w : I → O → ℝ) (v : I → O → D → ℝ) (hw : ∀i o, 0 < w i o)
    (hsum : ∀i, ∑o, w i o=1)
    (hA : ∀i ∈ s, A i=∑o, w i o • Matrix.vecMulVec (v i o) (v i o))
    (hfixed : ∀i, i ∉ s → ∃o, A i=Matrix.vecMulVec (v i o) (v i o))
    {b : ℝ} (hroot : ∀r ∈ (mixedChar A).roots, r ≤ b) :
    ∃f : I → O, ∀r ∈ (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))).charpoly.roots, r ≤ b := by
  induction s using Finset.induction_on generalizing A with
  | empty =>
    have hh : ∀i, ∃o, A i=Matrix.vecMulVec (v i o) (v i o) := fun i => hfixed i (by simp)
    choose f hf using hh
    refine ⟨f,?_⟩
    have hrank : ∀i, ∃a c, A i=Matrix.vecMulVec a c := fun i => ⟨_,_,hf i⟩
    rw [mixedChar_rankOne A hrank] at hroot
    simpa only [hf] using hroot
  | @insert j s hj ih =>
    let B : O → Matrix D D ℝ := fun o => Matrix.vecMulVec (v j o) (v j o)
    let child : O → I → Matrix D D ℝ := fun o => Function.update A j (B o)
    have hchildA : ∀o i, i ∈ s → child o i=∑a, w i a • Matrix.vecMulVec (v i a) (v i a) := by
      intro o i hi
      dsimp only [child]
      rw [Function.update_of_ne (show i ≠ j from fun he => hj (he ▸ hi))]
      exact hA i (Finset.mem_insert_of_mem hi)
    have hchildfixed : ∀o i, i ∉ s → ∃a, child o i=Matrix.vecMulVec (v i a) (v i a) := by
      intro o i hi
      by_cases hij : i=j
      · subst i; exact ⟨o,by simp [child,B]⟩
      · dsimp only [child]
        rw [Function.update_of_ne hij]
        exact hfixed i (by simp [hij,hi])
    have hmon : ∀o, (mixedChar (child o)).IsMonicOfDegree (Fintype.card D) := by
      intro o
      apply mixedChar_monic_partial s _ w v v hsum (hchildA o)
      intro i hi
      obtain ⟨a,ha⟩ := hchildfixed o i hi
      exact ⟨_,_,ha⟩
    have hmean : (∑o, w j o • mixedChar (child o))=mixedChar A := by
      rw [←mixedChar_mean j A (w j) B (hsum j),←hA j (by simp)]
      simp
    have hpsd := partial_posSemidef (insert j s) A w v (fun i o => (hw i o).le) hA hfixed
    have hsplit : ∀o t, t ∈ Set.Icc (0 : ℝ) 1 →
        ((1-t) • (∑a, w j a • mixedChar (child a))+t • mixedChar (child o)).Splits := by
      intro o t ht
      rw [hmean,mixedChar_segment]
      apply mixedChar_splits
      intro i
      by_cases hij : i=j
      · subst i
        simp only [Function.update_self]
        exact ((hpsd j).smul (sub_nonneg.mpr ht.2)).add ((rankOne_posSemidef _).smul ht.1)
      · rw [Function.update_of_ne hij]
        exact hpsd i
    obtain ⟨o,ho⟩ := Selection.selection (fun o => mixedChar (child o)) hmon (w j) (hw j) (hsum j)
      hsplit (by simpa only [hmean] using hroot)
    exact ih (child o) (hchildA o) (hchildfixed o) ho

lemma finite_selection (w : I → O → ℝ) (v : I → O → D → ℝ)
    (hw : ∀i o, 0 < w i o) (hsum : ∀i, ∑o, w i o=1)
    {b : ℝ} (hroot : ∀r ∈ (mixedChar (fun i => ∑o, w i o • Matrix.vecMulVec (v i o) (v i o))).roots, r ≤ b) :
    ∃f : I → O, ∀r ∈ (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))).charpoly.roots, r ≤ b :=
  finite_selection_partial Finset.univ _ w v hw hsum (by intros; rfl) (by simp) hroot

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Translation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uR uS

section

noncomputable section
open Matrix Polynomial Finset
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {R : Type uR} {S : Type uS} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D]
  [CommRing R] [CommRing S]

omit [DecidableEq I] in
lemma basePencil_map (f : R →+* S) (M : Matrix D D R) (A : I → Matrix D D R) :
    (basePencil M A).map f=basePencil (M.map f) (fun i => (A i).map f) := by
  unfold basePencil
  rw [(MvPolynomial.map f).map_det]
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  simp [Matrix.map_apply,Matrix.add_apply,Matrix.sum_apply,Matrix.smul_apply]

omit [DecidableEq I] [Fintype I] in
lemma eval_zero_map (f : R →+* S) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (p.map f)=f (MvPolynomial.eval (fun _ => 0) p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp []
  | mul_X p k hp => simp

omit [DecidableEq I] in
lemma mixedEval_map (f : R →+* S) (dirs : List I) (M : Matrix D D R) (A : I → Matrix D D R) :
    f (mixedEval dirs M A)=mixedEval dirs (M.map f) (fun i => (A i).map f) := by
  unfold mixedEval
  rw [←eval_zero_map,←diffProduct_map,basePencil_map]

omit [DecidableEq I] in
lemma mixedChar_eval (A : I → Matrix D D R) (x : R) :
    (mixedChar A).eval x=mixedEval Finset.univ.toList (x • (1 : Matrix D D R)) A := by
  unfold mixedChar
  change Polynomial.evalRingHom x (mixedEval _ _ _) = _
  rw [mixedEval_map]
  congr 1
  · apply Matrix.ext
    intro a b
    by_cases h : a=b <;> simp [Matrix.map_apply,Matrix.smul_apply,h]
  · funext i
    apply Matrix.ext
    intro a b
    simp [Matrix.map_apply]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma translate_pderiv (x : R) (i : I) (p : MvPolynomial I R) :
    translate x (MvPolynomial.pderiv i p)=MvPolynomial.pderiv i (translate x p) := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [translate]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp =>
    by_cases hk : k=i
    · subst k
      simp only [MvPolynomial.pderiv_mul,map_add,map_mul,MvPolynomial.pderiv_X_self,
        mul_one,hp]
      simp [translate]
    · simp only [MvPolynomial.pderiv_mul,map_mul,MvPolynomial.pderiv_X_of_ne hk,
        mul_zero,add_zero,hp]
      simp [translate,hk]

omit [Fintype I] [Fintype D] [DecidableEq D] in
lemma translate_diffProduct (x : R) (dirs : List I) (p : MvPolynomial I R) :
    translate x (diffProduct dirs p)=diffProduct dirs (translate x p) := by
  induction dirs generalizing p with
  | nil => rfl
  | cons i dirs ih => simp only [diffProduct_cons,ih,map_sub,translate_pderiv]

omit [Fintype I] [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma eval_zero_translate (x : R) (p : MvPolynomial I R) :
    MvPolynomial.eval (fun _ => 0) (translate x p)=MvPolynomial.eval (fun _ => x) p := by
  induction p using MvPolynomial.induction_on with
  | C r => simp [translate]
  | add p q hp hq => simpa only [map_add] using congrArg₂ (·+·) hp hq
  | mul_X p k hp => simpa only [map_mul,translate_X,
      MvPolynomial.eval_add,MvPolynomial.eval_X,MvPolynomial.eval_C,zero_add] using congrArg (·*x) hp

omit [Fintype D] [DecidableEq D] in
omit [DecidableEq I] in
lemma translate_linear_sum (a : I → R) (x : R) :
    translate x (∑i, MvPolynomial.X i * MvPolynomial.C (a i))=
      (∑i, MvPolynomial.X i * MvPolynomial.C (a i))+MvPolynomial.C x*MvPolynomial.C (∑i, a i) := by
  simp only [map_sum,map_mul,translate_X,translate_C,add_mul,Finset.sum_add_distrib]
  rw [←Finset.mul_sum,←map_sum]

omit [DecidableEq I] in
lemma translate_pencil (A : I → Matrix D D R) (hsum : ∑i, A i=1) (x : R) :
    translate x (pencil A)=basePencil (x • (1 : Matrix D D R)) A := by
  let N : Matrix D D (MvPolynomial I R) := fun a b => ∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)
  change translate x N.det = _
  rw [(translate x).map_det]
  unfold basePencil
  apply congrArg Matrix.det
  apply Matrix.ext
  intro a b
  change translate x (∑i, MvPolynomial.X i*MvPolynomial.C (A i a b)) = _
  rw [translate_linear_sum]

  have hab := congrArg (fun M : Matrix D D R => M a b) hsum
  simp only [Matrix.sum_apply] at hab
  rw [hab]
  simp only [Matrix.add_apply,Matrix.map_apply,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,map_mul]
  exact add_comm _ _

lemma mixedChar_eval_diagonal (A : I → Matrix D D R) (hsum : ∑i, A i=1) (x : R) :
    (mixedChar A).eval x=MvPolynomial.eval (fun _ => x) (diffProduct Finset.univ.toList (pencil A)) := by
  rw [mixedChar_eval,mixedEval,←translate_pencil A hsum x,←translate_diffProduct,eval_zero_translate]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.IndependentVectors
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uO

section

noncomputable section
open Matrix Polynomial Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} {O : Type uO} [DecidableEq I] [Fintype I] [Fintype D] [DecidableEq D] [Fintype O]

lemma mixedChar_roots_bound (A : I → Matrix D D ℝ) (hA : ∀i, (A i).PosSemidef)
    (hsum : ∑i, A i=1) {ε : ℝ} (hε : 0 < ε) (htr : ∀i, (A i).trace ≤ ε) :
    ∀r ∈ (mixedChar A).roots, r ≤ (1+Real.sqrt ε)^2 := by
  intro r hr
  by_contra! hlt
  have hp := skew_root_bound A hA hsum hε htr (fun _ => r-(1+Real.sqrt ε)^2)
    (fun _ => sub_nonneg.mpr hlt.le)
  have he : (fun _ : I => (1+Real.sqrt ε)^2)+(fun _ => r-(1+Real.sqrt ε)^2)=(fun _ => r) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [he] at hp
  have hev := (Polynomial.mem_roots (by intro h; simp [h] at hr)).mp hr
  have hd : realDifferentialProduct Finset.univ.toList (pencil A)=diffProduct Finset.univ.toList (pencil A) :=
    (diffProduct_foldl _ _).symm
  rw [hd,←mixedChar_eval_diagonal A hsum r,hev] at hp
  exact lt_irrefl _ hp

lemma matrix_le_of_roots {A : Matrix D D ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hr : ∀r ∈ A.charpoly.roots, r ≤ b) : A ≤ b • (1 : Matrix D D ℝ) := by
  have hh : A ≤ algebraMap ℝ (Matrix D D ℝ) b := by
    apply le_algebraMap_of_spectrum_le (ha := Matrix.isHermitian_iff_isSelfAdjoint.mp hA)
    intro r hr'
    exact hr r ((Polynomial.mem_roots (Matrix.charpoly_monic A).ne_zero).mpr
      (Matrix.mem_spectrum_iff_isRoot_charpoly.mp hr'))
  simpa only [Algebra.algebraMap_eq_smul_one] using hh

theorem small_vectors (w : I → O → ℝ) (v : I → O → D → ℝ)
    (hw : ∀i o, 0 < w i o) (hprob : ∀i, ∑o, w i o=1)
    (hiso : ∑i, ∑o, w i o • Matrix.vecMulVec (v i o) (v i o)=1)
    {ε : ℝ} (hε : 0 < ε)
    (hsize : ∀i, (∑o, w i o • Matrix.vecMulVec (v i o) (v i o)).trace ≤ ε) :
    ∃f : I → O, (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))) ≤
      (1+Real.sqrt ε)^2 • (1 : Matrix D D ℝ) := by
  have hA : ∀i, (∑o, w i o • Matrix.vecMulVec (v i o) (v i o)).PosSemidef :=
    fun i => Matrix.posSemidef_sum _ (fun o _ => (rankOne_posSemidef _).smul (hw i o).le)
  obtain ⟨f,hf⟩ := finite_selection w v hw hprob (mixedChar_roots_bound _ hA hiso hε hsize)
  exact ⟨f,matrix_le_of_roots (Matrix.posSemidef_sum _ (fun i _ => rankOne_posSemidef _)).isHermitian hf⟩

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Padding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {D : Type uD} [Fintype D] [DecidableEq D]

omit [Fintype D] [DecidableEq D] in
lemma rankOne_smul (c : ℝ) (v : D → ℝ) :
    Matrix.vecMulVec (c • v) (c • v)=c^2 • Matrix.vecMulVec v v := by
  apply Matrix.ext
  intro a b
  simp [Matrix.vecMulVec,Matrix.smul_apply,Pi.smul_apply]
  ring

omit [DecidableEq D] in
lemma sum_column_rankOne (M : Matrix D D ℝ) :
    ∑d, Matrix.vecMulVec (fun a => M a d) (fun a => M a d)=M*Mᵀ := by
  apply Matrix.ext
  intro a b
  simp [Matrix.sum_apply,Matrix.mul_apply,Matrix.vecMulVec,Matrix.transpose_apply]

omit [DecidableEq D] in
lemma rankOne_trace_nonneg (v : D → ℝ) : 0 ≤ (Matrix.vecMulVec v v).trace := by
  exact (rankOne_posSemidef v).trace_nonneg

lemma deterministic_padding (R : Matrix D D ℝ) (hR : R.PosSemidef) {ε : ℝ} (hε : 0 < ε) :
    ∃N : ℕ, ∃u : Fin N × D → D → ℝ,
      (∑p, Matrix.vecMulVec (u p) (u p))=R ∧
      ∀p, (Matrix.vecMulVec (u p) (u p)).trace ≤ ε := by
  let S := CFC.sqrt R
  have hS : S.IsHermitian := (CFC.sqrt_nonneg R).posSemidef.isHermitian
  have hsum : (∑d, Matrix.vecMulVec (fun a => S a d) (fun a => S a d))=R := by
    rw [sum_column_rankOne]
    have ht : Sᵀ=S := by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hS.eq
    rw [ht]
    exact CFC.sqrt_mul_sqrt_self R hR.nonneg
  have htr : ∀d, (Matrix.vecMulVec (fun a => S a d) (fun a => S a d)).trace ≤ R.trace := by
    intro d
    rw [←hsum,Matrix.trace_sum]
    exact Finset.single_le_sum (fun e _ => rankOne_trace_nonneg (fun a => S a e)) (Finset.mem_univ d)
  obtain ⟨N,hN⟩ := exists_nat_gt (max 0 (R.trace/ε))
  have hNpos : 0 < (N : ℝ) := (le_max_left _ _).trans_lt hN
  have hNε : R.trace/(N : ℝ) ≤ ε := by
    have hh : R.trace/ε ≤ N := (le_max_right _ _).trans hN.le
    apply (div_le_iff₀ hNpos).mpr
    simpa only [mul_comm] using (div_le_iff₀ hε).mp hh
  let c : ℝ := Real.sqrt (1/(N : ℝ))
  have hc : c^2=1/(N : ℝ) := Real.sq_sqrt (by positivity)
  let u : Fin N × D → D → ℝ := fun p => c • (fun a => S a p.2)
  refine ⟨N,u,?_,?_⟩
  · simp only [u,rankOne_smul,hc,Fintype.sum_prod_type,←Finset.smul_sum,hsum]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin]
    rw [←Nat.cast_smul_eq_nsmul ℝ, smul_smul]
    simp [hNpos.ne']
  · intro p
    simp only [u,rankOne_smul,hc,Matrix.trace_smul,smul_eq_mul]
    calc
      (1/(N : ℝ)) * (Matrix.vecMulVec (fun a => S a p.2) (fun a => S a p.2)).trace
          ≤ (1/(N : ℝ))*R.trace := mul_le_mul_of_nonneg_left (htr p.2) (by positivity)
      _ = R.trace/(N : ℝ) := by ring
      _ ≤ ε := hNε

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Subisotropic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} [Fintype I] [Fintype D] [DecidableEq D]

theorem subisotropic_binary (v : I → Bool → D → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hiso : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)) ≤ 1)
    (hsize : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)).trace ≤ ε) :
    ∃f : I → Bool, (∑i, Matrix.vecMulVec (v i (f i)) (v i (f i))) ≤
      (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)) +
      (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) := by
  classical
  let M := ∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (v i b) (v i b)
  have hR : (1-M).PosSemidef := (sub_nonneg.mpr hiso).posSemidef
  obtain ⟨N,u,hu,hutr⟩ := deterministic_padding (1-M) hR hε
  let V : I ⊕ (Fin N × D) → Bool → D → ℝ := Sum.elim v (fun p _ => u p)
  have hprob : ∀i : I ⊕ (Fin N × D), ∑_b : Bool, (1/2 : ℝ)=1 := by
    intro i
    norm_num [Fintype.sum_bool]
  have hdet (p : Fin N × D) :
      (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V (.inr p) b) (V (.inr p) b))=
        Matrix.vecMulVec (u p) (u p) := by
    simp only [V,Sum.elim_inr,Fintype.sum_bool,←add_smul]
    norm_num
  have hiso' : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V i b) (V i b))=1 := by
    rw [Fintype.sum_sum_type]
    simp only [hdet,V,Sum.elim_inl]
    change M+(∑p, Matrix.vecMulVec (u p) (u p))=1
    rw [hu]
    abel
  have hsize' : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (V i b) (V i b)).trace ≤ ε := by
    intro i
    cases i with
    | inl i => exact hsize i
    | inr p => rw [hdet]; exact hutr p
  obtain ⟨f,hf⟩ := small_vectors (fun _ _ => (1/2 : ℝ)) V (by intros; norm_num) hprob hiso' hε hsize'
  rw [Fintype.sum_sum_type] at hf
  simp only [V,Sum.elim_inl,Sum.elim_inr] at hf
  rw [hu] at hf
  refine ⟨fun i => f (.inl i),?_⟩
  change (∑i, Matrix.vecMulVec (v i (f (.inl i))) (v i (f (.inl i)))) ≤
    M+(2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ)
  have hβ : (1+Real.sqrt ε)^2=1+(2*Real.sqrt ε+ε) := by
    linarith [Real.sq_sqrt hε.le]
  have he : (1+Real.sqrt ε)^2 • (1 : Matrix D D ℝ) =
      (M+(2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ))+(1-M) := by
    rw [hβ,add_smul,one_smul]
    abel
  rw [he] at hf
  exact (add_le_add_iff_right (1-M)).mp hf

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD uO uI uI2

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {D : Type uD} {O : Type uO} [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O]

lemma blockDiagonal_nonneg (A : O → Matrix D D ℝ) (hA : ∀o, 0 ≤ A o) :
    0 ≤ Matrix.blockDiagonal A := by
  let S : O → Matrix D D ℝ := fun o => CFC.sqrt (A o)
  have hf : ∀o, (S o)ᴴ*S o=A o := by
    intro o
    rw [(CFC.sqrt_nonneg (A o)).posSemidef.isHermitian.eq]
    exact CFC.sqrt_mul_sqrt_self (A o) (hA o)
  have he : (Matrix.blockDiagonal S)ᴴ*Matrix.blockDiagonal S=Matrix.blockDiagonal A := by
    rw [Matrix.blockDiagonal_conjTranspose,←Matrix.blockDiagonal_mul]
    simp only [hf]
  rw [←he]
  exact (Matrix.posSemidef_conjTranspose_mul_self _).nonneg

lemma blockDiagonal_mono (A B : O → Matrix D D ℝ) (h : ∀o, A o ≤ B o) :
    Matrix.blockDiagonal A ≤ Matrix.blockDiagonal B := by
  apply sub_nonneg.mp
  rw [←Matrix.blockDiagonal_sub]
  exact blockDiagonal_nonneg _ (fun o => sub_nonneg.mpr (h o))

omit [Fintype D] [DecidableEq D] [Fintype O] [DecidableEq O] in
lemma blockDiag_mono {A B : Matrix (D × O) (D × O) ℝ} (h : A ≤ B) (o : O) :
    Matrix.blockDiag A o ≤ Matrix.blockDiag B o := by
  have hh := (sub_nonneg.mpr h).posSemidef.submatrix (fun d : D => (d,o))
  change (Matrix.blockDiag (B-A) o).PosSemidef at hh
  simpa only [Matrix.blockDiag_sub,Pi.sub_apply,sub_nonneg] using hh.nonneg

omit [Fintype O] [DecidableEq O] [Fintype D] [DecidableEq D] in
lemma blockDiag_sum {I : Type uI} (s : Finset I) (A : I → Matrix (D × O) (D × O) ℝ) (o : O) :
    Matrix.blockDiag (∑i ∈ s, A i) o=∑i ∈ s, Matrix.blockDiag (A i) o := by
  ext a b
  simp [Matrix.blockDiag_apply,Matrix.sum_apply]

omit [DecidableEq D] in
lemma blockEmbed_trace (v : D → ℝ) (b : Bool) :
    (Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b)).trace=(Matrix.vecMulVec v v).trace := by
  cases b <;> simp [Matrix.trace,Matrix.diag,Matrix.vecMulVec,blockEmbed,Fintype.sum_prod_type]

omit [Fintype D] [DecidableEq D] in
lemma blockEmbed_mean (v : D → ℝ) :
    (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b))=
      Matrix.blockDiagonal (fun _ : Bool => (1/2 : ℝ) • Matrix.vecMulVec v v) := by
  ext ⟨a,c⟩ ⟨d,b⟩
  cases c <;> cases b <;>
    simp [Matrix.vecMulVec,blockEmbed,Matrix.blockDiagonal_apply]

omit [Fintype D] [DecidableEq D] in
lemma blockEmbed_blockDiag (v : D → ℝ) (b c : Bool) :
    Matrix.blockDiag (Matrix.vecMulVec (blockEmbed v b) (blockEmbed v b)) c=
      if b=c then Matrix.vecMulVec v v else 0 := by
  cases b <;> cases c <;> ext a d <;>
    simp [Matrix.blockDiag_apply,Matrix.vecMulVec,blockEmbed]

omit [Fintype O] [DecidableEq O] [Fintype D] [DecidableEq D] in
lemma blockDiagonal_sum {I : Type uI2} (s : Finset I) (A : I → O → Matrix D D ℝ) [DecidableEq O] :
    Matrix.blockDiagonal (fun o => ∑i ∈ s, A i o)=∑i ∈ s, Matrix.blockDiagonal (A i) := by
  ext ⟨a,b⟩ ⟨c,d⟩
  by_cases h : b=d <;> simp [Matrix.blockDiagonal_apply,h,Matrix.sum_apply]

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.SpectralSplit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MSS
variable {I : Type uI} {D : Type uD} [Fintype I] [DecidableEq I] [Fintype D] [DecidableEq D]

omit [DecidableEq I] in

theorem two_sided_split (w : I → D → ℝ) {ε : ℝ} (hε : 0 < ε)
    (hiso : (∑i, Matrix.vecMulVec (w i) (w i)) ≤ (2 : ℝ) • (1 : Matrix D D ℝ))
    (hsize : ∀i, (Matrix.vecMulVec (w i) (w i)).trace ≤ ε) :
    ∃A : Finset I,
      (1/2 : ℝ) • (∑i, Matrix.vecMulVec (w i) (w i)) -
        (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) ≤ ∑i ∈ A, Matrix.vecMulVec (w i) (w i) ∧
      (∑i ∈ A, Matrix.vecMulVec (w i) (w i)) ≤
        (1/2 : ℝ) • (∑i, Matrix.vecMulVec (w i) (w i)) +
        (2*Real.sqrt ε+ε) • (1 : Matrix D D ℝ) := by
  let Smat := ∑i, Matrix.vecMulVec (w i) (w i)
  let τ := 2*Real.sqrt ε+ε
  have hhalf : (1/2 : ℝ) • Smat ≤ (1 : Matrix D D ℝ) := by
    have hh := smul_le_smul_of_nonneg_left hiso (by norm_num : (0:ℝ) ≤ 1/2)
    simpa only [smul_smul,show (1/2:ℝ)*2=1 by norm_num,one_smul] using hh
  have hmean : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b))=
      Matrix.blockDiagonal (fun _ : Bool => (1/2 : ℝ) • Smat) := by
    simp_rw [blockEmbed_mean]
    rw [←blockDiagonal_sum]
    simp only [Smat,Finset.smul_sum]
  have hmiso : (∑i, ∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b)) ≤ 1 := by
    rw [hmean]
    simpa only [Matrix.blockDiagonal_one] using blockDiagonal_mono
      (fun _ : Bool => (1/2 : ℝ) • Smat) (1 : Bool → Matrix D D ℝ) (fun _ => hhalf)
  have hmsize : ∀i, (∑b : Bool, (1/2 : ℝ) • Matrix.vecMulVec (blockEmbed (w i) b) (blockEmbed (w i) b)).trace ≤ ε := by
    intro i
    rw [Fintype.sum_bool, Matrix.trace_add]
    simp only [Matrix.trace_smul,smul_eq_mul,blockEmbed_trace]
    linarith [hsize i]
  obtain ⟨f,hf⟩ := subisotropic_binary (fun i b => blockEmbed (w i) b) hε hmiso hmsize
  rw [hmean] at hf
  have hb (b : Bool) : (∑i, if f i=b then Matrix.vecMulVec (w i) (w i) else 0) ≤
      (1/2 : ℝ) • Smat+τ • (1 : Matrix D D ℝ) := by
    have hh := blockDiag_mono hf b
    simpa only [blockDiag_sum,blockEmbed_blockDiag,Matrix.blockDiag_add,Pi.add_apply,
      Matrix.blockDiag_blockDiagonal,Matrix.blockDiag_smul,Pi.smul_apply,Matrix.blockDiag_one,Pi.one_apply] using hh
  let A : Finset I := Finset.univ.filter (fun i => f i=true)
  have hA : (∑i ∈ A, Matrix.vecMulVec (w i) (w i))=
      ∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0 := by
    simp only [A,Finset.sum_filter]
  have hcomp : (∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0)+
      (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0)=Smat := by
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    cases f i <;> simp
  refine ⟨A,?_,?_⟩
  · rw [hA]
    have hh := hb false
    rw [add_comm ((1/2 : ℝ) • Smat), ←sub_le_iff_le_add] at hh
    have he : (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0) -
        (1/2 : ℝ) • Smat = (1/2 : ℝ) • Smat - (∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0) := by
      have hc : (∑i, if f i=false then Matrix.vecMulVec (w i) (w i) else 0)=
          Smat-(∑i, if f i=true then Matrix.vecMulVec (w i) (w i) else 0) := by
        rw [←hcomp]; abel
      rw [hc]
      module
    rw [he] at hh
    exact (sub_le_comm.mp hh)
  · rw [hA]
    exact hb true

end StrongThinTree.MSS

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.TwoSystems
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uI uD uE

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {I : Type uI} {D : Type uD} {E : Type uE} [Fintype I] [Fintype D] [Fintype E]
  [DecidableEq I] [DecidableEq D] [DecidableEq E]

omit [Fintype I] [DecidableEq I] [DecidableEq D] [Fintype E] [DecidableEq E] in
lemma qform_covariance (v : I → D → ℝ) (A : Finset I) (x : D → ℝ) :
    qform (∑i ∈ A, vecMulVec (v i) (v i)) x=∑i ∈ A, (x ⬝ᵥ v i)^2 := by
  simp only [qform,sum_mulVec,dotProduct_sum]
  apply sum_congr rfl
  intro i _
  rw [vecMulVec_mulVec,dotProduct_smul,dotProduct_comm (v i) x]
  simp [pow_two]

omit [Fintype I] [DecidableEq I] [DecidableEq D] [DecidableEq E] in
lemma dotProduct_sum_elim (a x : D → ℝ) (b y : E → ℝ) :
    (Sum.elim a b) ⬝ᵥ (Sum.elim x y)=a ⬝ᵥ x+b ⬝ᵥ y := by
  simp [dotProduct,Fintype.sum_sum_type]

omit [DecidableEq I] in

theorem split_two_systems (a : I → D → ℝ) (z : I → E → ℝ) {ε : ℝ}
    (hε : 0 < ε)
    (ha : ∀x : D → ℝ, (∑i, (x ⬝ᵥ a i)^2) ≤ x ⬝ᵥ x)
    (hz : ∀y : E → ℝ, (∑i, (y ⬝ᵥ z i)^2) = y ⬝ᵥ y)
    (hsize : ∀i, a i ⬝ᵥ a i+z i ⬝ᵥ z i ≤ ε) :
    ∃A : Finset I,
      (∀x : D → ℝ, (∑i ∈ A, (x ⬝ᵥ a i)^2) ≤
        (1/2:ℝ)*(∑i, (x ⬝ᵥ a i)^2)+(2*Real.sqrt ε+ε)*(x ⬝ᵥ x)) ∧
      (∀y : E → ℝ, (1/2-(2*Real.sqrt ε+ε))*(y ⬝ᵥ y) ≤
        ∑i ∈ A, (y ⬝ᵥ z i)^2) := by
  let w : I → D ⊕ E → ℝ := fun i => Sum.elim (a i) (z i)
  let C : Matrix (D ⊕ E) (D ⊕ E) ℝ := ∑i, vecMulVec (w i) (w i)
  have hC : C.PosSemidef := Matrix.posSemidef_sum _ (fun i _ => by
    simpa only [star_trivial] using posSemidef_vecMulVec_self_star (w i))
  have hcov : C ≤ (2:ℝ) • (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) := by
    apply Matrix.le_iff.mpr
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 2)).isHermitian.sub hC.isHermitian)
    intro v
    have hv : v=Sum.elim (fun i => v (.inl i)) (fun j => v (.inr j)) := by ext i; cases i <;> rfl
    rw [show star v=v by rfl]
    change 0 ≤ qform ((2:ℝ) • (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ)-C) v
    rw [qform_sub,qform_smul]
    have hc : qform C v=∑i, (v ⬝ᵥ w i)^2 := qform_covariance w univ v
    rw [hc]
    have hterm := Finset.sum_le_sum (s:=univ) (fun i (_ : i ∈ (univ : Finset I)) =>
      show (v ⬝ᵥ w i)^2 ≤ 2*((fun j => v (.inl j)) ⬝ᵥ a i)^2+
          2*((fun j => v (.inr j)) ⬝ᵥ z i)^2 by
        rw [hv]
        simp only [w,dotProduct_sum_elim,Sum.elim_inl,Sum.elim_inr]
        linarith [sq_nonneg (((fun j => v (.inl j)) ⬝ᵥ a i)-((fun j => v (.inr j)) ⬝ᵥ z i))])
    rw [sum_add_distrib,←mul_sum,←mul_sum,hz] at hterm
    have hh := ha (fun j => v (.inl j))
    have hn : qform (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) v =
        ((fun j => v (.inl j)) ⬝ᵥ (fun j => v (.inl j)))+
        ((fun j => v (.inr j)) ⬝ᵥ (fun j => v (.inr j))) := by
      rw [qform,one_mulVec,hv,dotProduct_sum_elim]
      rfl
    rw [hn]
    linarith
  have hwsize : ∀i, (vecMulVec (w i) (w i)).trace ≤ ε := by
    intro i
    simpa only [trace_vecMulVec,w,dotProduct_sum_elim] using hsize i
  obtain ⟨A,hlo,hhi⟩ := MSS.two_sided_split w hε hcov hwsize
  have heq (x : D → ℝ) (y : E → ℝ) :
      qform (1 : Matrix (D ⊕ E) (D ⊕ E) ℝ) (Sum.elim x y)=x ⬝ᵥ x+y ⬝ᵥ y := by
    rw [qform,one_mulVec,dotProduct_sum_elim]
  refine ⟨A,?_,?_⟩
  · intro x
    have hh := qform_mono hhi (Sum.elim x (0:E → ℝ))
    simp only [qform_add,qform_smul,qform_covariance,heq,w,dotProduct_sum_elim,zero_dotProduct,add_zero] at hh
    exact hh
  · intro y
    have hh := qform_mono hlo (Sum.elim (0:D → ℝ) y)
    simp only [qform_sub,qform_smul,qform_covariance,heq,w,dotProduct_sum_elim,zero_dotProduct,zero_add,hz] at hh
    linarith

end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Representation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uι uE uT uI uE2 uE3 uV uE4 uV2 uW

section

open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise
namespace StrongThinTree
noncomputable section

section Determinant
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma hasDerivAt_det_one_add_smul (M : Matrix ι ι ℝ) :
    HasDerivAt (fun t : ℝ => (1 + t • M).det) M.trace 0 := by
  let p : Polynomial ℝ :=
    (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • M.map Polynomial.C)).divX.divX
  have hp := p.hasDerivAt (0 : ℝ)
  have hid := hasDerivAt_id (0 : ℝ)
  have h := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
    (hid.const_mul M.trace)).add (hp.mul (hid.pow 2))
  have heq : (fun t : ℝ => (1 + t • M).det) =
      (fun t : ℝ => 1 + M.trace * t + p.eval t * t ^ 2) := by
    funext t
    exact Matrix.det_one_add_smul t M
  rw [heq]
  simpa using! h

lemma hasDerivAt_det_add_smul (A B : Matrix ι ι ℝ) (hA : IsUnit A) :
    HasDerivAt (fun t : ℝ => (A + t • B).det)
      (A.det * (A⁻¹ * B).trace) 0 := by
  have hmul : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv A
    ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have heq (t : ℝ) : A + t • B = A * (1 + t • (A⁻¹ * B)) := by
    simp [mul_add, ← mul_assoc, hmul]
  have heq' : (fun t : ℝ => (A + t • B).det) =
      (fun t : ℝ => A.det * (1 + t • (A⁻¹ * B)).det) := by
    funext t
    rw [heq, Matrix.det_mul]
  rw [heq']
  exact (hasDerivAt_det_one_add_smul (A⁻¹ * B)).const_mul A.det

lemma differentiable_det : Differentiable ℝ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  classical
  change Differentiable ℝ (fun M : Matrix ι ι ℝ => M.det)
  simp_rw [Matrix.det_apply]
  fun_prop

lemma fderiv_det_apply (A B : Matrix ι ι ℝ) (hA : IsUnit A) :
    fderiv ℝ Matrix.det A B = A.det * (A⁻¹ * B).trace := by
  have hc : HasDerivAt (fun t : ℝ => A + t • B) B 0 := by
    simpa using! (hasDerivAt_const (0 : ℝ) A).add
      ((hasDerivAt_id (0 : ℝ)).smul_const B)
  have hd : HasFDerivAt Matrix.det (fderiv ℝ Matrix.det A) (A + (0 : ℝ) • B) := by
    simpa using! (differentiable_det A).hasFDerivAt
  have h := hd.comp_hasDerivAt (0 : ℝ) hc
  exact h.unique (hasDerivAt_det_add_smul A B hA)

lemma one_le_det_one_add {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    1 ≤ (1 + A).det := by
  let U := hA.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal hA.isHermitian.eigenvalues
  have hspec : A = (U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ) := by
    simpa [D, U, Unitary.conjStarAlgAut_apply] using hA.isHermitian.spectral_theorem
  have hconj : 1 + A = (U : Matrix ι ι ℝ) * (1 + D) * star (U : Matrix ι ι ℝ) := by
    rw [hspec]
    simp [mul_add, add_mul]
  rw [hconj, Matrix.det_mul_comm, ← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hdiag : 1 + D = Matrix.diagonal (fun i => 1 + hA.isHermitian.eigenvalues i) := by
    simp only [D, ← Matrix.diagonal_one, Matrix.diagonal_add]
  rw [hdiag, Matrix.det_diagonal]
  exact Finset.one_le_prod (fun i _ => by linarith [hA.eigenvalues_nonneg i])

lemma posDef_sqrt_factors {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    ∃ S : Matrix ι ι ℝ, S.IsHermitian ∧ IsUnit S ∧ S * S = A := by
  refine ⟨CFC.sqrt A, (CFC.sqrt_nonneg A).posSemidef.isHermitian, ?_,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg⟩
  apply (isUnit_pow_iff (by decide : 2 ≠ 0)).mp
  rw [CFC.sq_sqrt A hA.posSemidef.nonneg]
  exact hA.isUnit

lemma det_le_det_add_of_posSemidef {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosSemidef) : A.det ≤ (A + B).det := by
  obtain ⟨S, hSH, hSU, hS⟩ := posDef_sqrt_factors hA
  have hSi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hiS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  let Q := S⁻¹ * B * S⁻¹
  have hQ : Q.PosSemidef := by
    simpa only [hSH.inv.eq] using hB.mul_mul_conjTranspose_same S⁻¹
  have hdecomp : A + B = S * (1 + Q) * S := by
    dsimp [Q]
    simp only [mul_add, add_mul, mul_one, ← mul_assoc, hS]
    simp only [mul_assoc, hSi, hiS, one_mul, mul_one]
  have hdetS : S.det * S.det = A.det := by rw [← Matrix.det_mul, hS]
  have hdet : (A + B).det = A.det * (1 + Q).det := by
    rw [hdecomp, Matrix.det_mul, Matrix.det_mul]
    rw [← hdetS]
    ring
  rw [hdet]
  exact le_mul_of_one_le_right hA.det_pos.le (one_le_det_one_add hQ)

end Determinant
section Regularization
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
open Filter

lemma exists_fderiv_norm_lt_of_bddBelow (f : E → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (hb : ∀ x, L ≤ f x) {ε : ℝ} (hε : 0 < ε) :
    ∃ x, ‖fderiv ℝ f x‖ < ε := by
  let K : ℝ := f 0 - L
  have hK : 0 ≤ K := sub_nonneg.mpr (hb 0)
  let γ : ℝ := ε ^ 2 / (16 * (K + 1))
  have hγ : 0 < γ := div_pos (sq_pos_of_pos hε) (by positivity)
  let g : E → ℝ := fun x => f x + γ * ‖x‖ ^ 2
  have hg : Continuous g := hf.continuous.add
    (continuous_const.mul (continuous_norm.pow 2))
  have hcoerc : Tendsto (fun x : E => L + γ * ‖x‖ ^ 2) (cocompact E) atTop := by
    have hn : Tendsto (fun x : E => ‖x‖ ^ 2) (cocompact E) atTop := by
      simpa only [pow_two] using
        tendsto_norm_cocompact_atTop.atTop_mul_atTop₀
          (tendsto_norm_cocompact_atTop (E := E))
    exact tendsto_const_nhds.add_atTop (hn.const_mul_atTop hγ)
  have hcoercg : Tendsto g (cocompact E) atTop :=
    tendsto_atTop_mono (fun x => by dsimp [g]; linarith [hb x]) hcoerc
  obtain ⟨x, hx⟩ := hg.exists_forall_le hcoercg
  have hx0 := hx 0
  have hvalue : γ * ‖x‖ ^ 2 ≤ K := by
    dsimp [g] at hx0
    simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] at hx0
    dsimp [K]
    linarith [hb x]
  have hmin : IsLocalMin g x := by
    exact (show IsMinOn g Set.univ x from fun y _ => hx y).isLocalMin
      (by simp)
  have hder := hmin.hasFDerivAt_eq_zero
    ((hf x).hasFDerivAt.add
      ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul γ))
  have hnorm : ‖fderiv ℝ f x‖ = 2 * γ * ‖x‖ := by
    have hd : fderiv ℝ f x = -(γ • ((2 : ℝ) • innerSL ℝ x)) := by
      apply eq_neg_of_add_eq_zero_left
      simpa only [two_smul] using hder
    rw [hd, norm_neg, norm_smul, norm_smul, innerSL_apply_norm]
    simp only [Real.norm_eq_abs, abs_of_pos hγ, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    ring
  refine ⟨x, ?_⟩
  rw [hnorm]
  have hγeq : γ * (16 * (K + 1)) = ε ^ 2 := by
    dsimp [γ]
    exact div_mul_cancel₀ _ (ne_of_gt (by positivity))
  have hbnd := mul_le_mul_of_nonneg_left hvalue (le_of_lt hγ)
  have hγK : 4 * γ * K < ε ^ 2 := by
    nlinarith
  have hxnonneg : 0 ≤ 2 * γ * ‖x‖ := by positivity
  nlinarith [sq_nonneg (2 * γ * ‖x‖)]

end Regularization
section Covariance
variable {T : Type uT} {I : Type uI} [Fintype T] [DecidableEq T] [Nonempty T]
  [Fintype I] [DecidableEq I]

lemma basisCov_eq_sum (b : Matrix I I ℝ) (a : I → ℝ) :
    basisCov b a = ∑ j, Real.exp (a j) • vecMulVec (fun i => b i j) (fun i => b i j) := by
  apply Matrix.ext
  intro k l
  change (∑ j, (b * diagonal (fun j => Real.exp (a j))) k j * b l j) = _
  simp only [Matrix.mul_diagonal, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [DecidableEq T] [Nonempty T] in
lemma packingCov_eq_sum (b : T → Matrix I I ℝ) (a : EuclideanSpace ℝ (T × I)) :
    packingCov b a = ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) := by
  simp only [packingCov, basisCov_eq_sum, Fintype.sum_prod_type]

omit [DecidableEq T] [Nonempty T] in
lemma differentiable_packingCov (b : T → Matrix I I ℝ) :
    Differentiable ℝ (packingCov b) := by
  have heq : packingCov b = fun a => ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) :=
    funext (packingCov_eq_sum b)
  rw [heq]
  exact Differentiable.fun_sum fun e _ =>
    ((EuclideanSpace.proj (𝕜 := ℝ) e).differentiable.exp).smul_const _

omit [Nonempty T] in
lemma fderiv_packingCov_single (b : T → Matrix I I ℝ)
    (a : EuclideanSpace ℝ (T × I)) (e : T × I) :
    fderiv ℝ (packingCov b) a (EuclideanSpace.single e 1) =
      Real.exp (a e) • vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) := by
  have heq : packingCov b = fun a => ∑ e : T × I, Real.exp (a e) •
      vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2) :=
    funext (packingCov_eq_sum b)
  have hd : HasFDerivAt (packingCov b)
      (∑ e : T × I, (Real.exp (a e) • EuclideanSpace.proj (𝕜 := ℝ) e).smulRight
        (vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2))) a := by
    rw [heq]
    exact HasFDerivAt.fun_sum fun e _ =>
      ((EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt.exp).smul_const _
  rw [hd.fderiv]
  simp

lemma basisCov_posDef (b : Matrix I I ℝ) (hb : IsUnit b) (a : I → ℝ) :
    (basisCov b a).PosDef := by
  have hd : (diagonal (fun j => Real.exp (a j))).PosDef :=
    Matrix.PosDef.diagonal (fun j => Real.exp_pos _)
  simpa [basisCov] using hd.mul_mul_conjTranspose_same
    (Matrix.vecMul_injective_of_isUnit hb)

omit [DecidableEq T] in
lemma packingCov_posDef (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    (a : EuclideanSpace ℝ (T × I)) : (packingCov b a).PosDef := by
  exact Matrix.posDef_sum Finset.univ_nonempty
    (fun t _ => basisCov_posDef (b t) (hb t) _)

lemma det_basisCov (b : Matrix I I ℝ) (a : I → ℝ) :
    (basisCov b a).det = b.det ^ 2 * Real.exp (∑ j, a j) := by
  simp only [basisCov, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  rw [Real.exp_sum]
  ring

omit [Nonempty T] in
lemma det_basisCov_le_packingCov (b : T → Matrix I I ℝ)
    (hb : ∀ t, IsUnit (b t)) (a : EuclideanSpace ℝ (T × I)) (t : T) :
    (basisCov (b t) (fun j => a (t, j))).det ≤ (packingCov b a).det := by
  have hsum : packingCov b a = basisCov (b t) (fun j => a (t, j)) +
      ∑ u ∈ Finset.univ.erase t, basisCov (b u) (fun j => a (u, j)) := by
    exact (Finset.add_sum_erase _ _ (Finset.mem_univ t)).symm
  rw [hsum]
  apply det_le_det_add_of_posSemidef (basisCov_posDef _ (hb t) _)
  exact Matrix.posSemidef_sum _ (fun u _ => (basisCov_posDef _ (hb u) _).posSemidef)

lemma packingObjective_bddBelow (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t)) :
    ∀ a, (∑ t, Real.log ((b t).det ^ 2)) / Fintype.card T ≤ packingObjective b a := by
  intro a
  have ht (t : T) : Real.log ((b t).det ^ 2) + ∑ j, a (t, j) ≤
      Real.log (packingCov b a).det := by
    have hd := (basisCov_posDef (b t) (hb t) (fun j => a (t, j))).det_pos
    have hbd := det_basisCov_le_packingCov b hb a t
    have he := Real.log_le_log hd hbd
    rw [det_basisCov, Real.log_mul (by
      have := (Matrix.isUnit_iff_isUnit_det _).mp (hb t)
      exact pow_ne_zero 2 this.ne_zero) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at he
    exact he
  have hs := Finset.sum_le_sum (fun t (_ : t ∈ Finset.univ) => ht t)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
  have hq : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  dsimp [packingObjective]
  rw [le_sub_iff_add_le, ← add_div, div_le_iff₀ hq]
  rw [mul_comm] at hs
  simpa only [Fintype.sum_prod_type] using hs

omit [DecidableEq T] in
lemma differentiable_packingObjective (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t)) :
    Differentiable ℝ (packingObjective b) := by
  intro a
  apply DifferentiableAt.sub
  · exact ((differentiable_det _).comp a (differentiable_packingCov b a)).log
      (ne_of_gt (packingCov_posDef b hb a).det_pos)
  · have hs : DifferentiableAt ℝ (fun a : EuclideanSpace ℝ (T × I) => ∑ e, a e) a :=
      DifferentiableAt.fun_sum (fun e _ => (EuclideanSpace.proj (𝕜 := ℝ) e).differentiableAt)
    simpa only [div_eq_mul_inv] using hs.mul_const ((Fintype.card T : ℝ)⁻¹)

lemma fderiv_packingObjective_single (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    (a : EuclideanSpace ℝ (T × I)) (e : T × I) :
    fderiv ℝ (packingObjective b) a (EuclideanSpace.single e 1) =
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ (fun i => b e.1 i e.2))) - 1 / Fintype.card T := by
  have hn := (differentiable_packingCov b a).hasFDerivAt
  have hd := (differentiable_det (packingCov b a)).hasFDerivAt.comp a hn
  have hpos := (packingCov_posDef b hb a).det_pos
  have hl := hd.log (ne_of_gt hpos)
  have hs : HasFDerivAt (fun a : EuclideanSpace ℝ (T × I) => ∑ e, a e)
      (∑ e, EuclideanSpace.proj (𝕜 := ℝ) e) a :=
    HasFDerivAt.fun_sum (fun e _ => (EuclideanSpace.proj (𝕜 := ℝ) e).hasFDerivAt)
  have hsq : HasFDerivAt (fun a : EuclideanSpace ℝ (T × I) => (∑ e, a e) / Fintype.card T)
      ((Fintype.card T : ℝ)⁻¹ • ∑ e, EuclideanSpace.proj (𝕜 := ℝ) e) a := by
    simpa only [div_eq_mul_inv, mul_comm] using hs.const_mul ((Fintype.card T : ℝ)⁻¹)
  have ho := hl.sub hsq
  have ho' : HasFDerivAt (packingObjective b) _ a := ho
  rw [ho'.fderiv]
  change (packingCov b a).det⁻¹ *
      (fderiv ℝ Matrix.det (packingCov b a))
        ((fderiv ℝ (packingCov b) a) (EuclideanSpace.single e 1)) -
      (Fintype.card T : ℝ)⁻¹ * (∑ j, EuclideanSpace.proj (𝕜 := ℝ) j) (EuclideanSpace.single e 1) = _
  rw [fderiv_packingCov_single]
  rw [fderiv_det_apply _ _ (packingCov_posDef b hb a).isUnit]
  simp only [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, Matrix.mul_vecMulVec,
    Matrix.trace_vecMulVec, dotProduct_comm]
  simp
  field_simp

lemma exists_small_leverages (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a : EuclideanSpace ℝ (T × I), ∀ e : T × I,
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ (fun i => b e.1 i e.2))) ≤
      (1 + ρ) / Fintype.card T := by
  have hq : (0 : ℝ) < Fintype.card T := Nat.cast_pos.mpr Fintype.card_pos
  obtain ⟨a, ha⟩ := exists_fderiv_norm_lt_of_bddBelow (packingObjective b)
    (differentiable_packingObjective b hb)
    ((∑ t, Real.log ((b t).det ^ 2)) / Fintype.card T)
    (packingObjective_bddBelow b hb) (div_pos hρ hq)
  refine ⟨a, fun e => ?_⟩
  have hv := (fderiv ℝ (packingObjective b) a).le_opNorm (EuclideanSpace.single e 1)
  simp only [PiLp.norm_single, norm_one, mul_one, Real.norm_eq_abs] at hv
  have hu := (le_abs_self (fderiv ℝ (packingObjective b) a (EuclideanSpace.single e 1))).trans hv
  have hu' := lt_of_le_of_lt hu ha
  rw [fderiv_packingObjective_single b hb a e] at hu'
  rw [add_div]
  linarith

theorem isotropic_representation (b : T → Matrix I I ℝ) (hb : ∀ t, IsUnit (b t))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (M : Matrix I I ℝ) (s : T × I → ℝ), IsUnit M ∧ (∀ e, 0 < s e) ∧
      let z := fun e : T × I => s e • (M *ᵥ fun i => b e.1 i e.2)
      (∑ e, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e, z e ⬝ᵥ z e ≤ (1 + ρ) / Fintype.card T) := by
  obtain ⟨a, ha⟩ := exists_small_leverages b hb hρ
  obtain ⟨S, hSH, hSU, hS⟩ := posDef_sqrt_factors (packingCov_posDef b hb a)
  let M := S⁻¹
  let s : T × I → ℝ := fun e => Real.exp (a e / 2)
  have hMU : IsUnit M := Matrix.isUnit_nonsing_inv_iff.mpr hSU
  have hMT : Mᵀ = M := by simpa [M] using hSH.inv.eq
  have hMS : M * S = 1 := Matrix.nonsing_inv_mul S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hSM : S * M = 1 := Matrix.mul_nonsing_inv S
    ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hMNM : M * packingCov b a * M = 1 := by
    rw [← hS, ← mul_assoc, hMS, one_mul, hSM]
  have hMM : M * M = (packingCov b a)⁻¹ := by
    apply Eq.symm
    apply Matrix.inv_eq_left_inv
    rw [← hS, mul_assoc, ← mul_assoc M S S, hMS, one_mul, hMS]
  have hs (e : T × I) : s e * s e = Real.exp (a e) := by
    dsimp [s]
    rw [← Real.exp_add]
    congr 1
    ring
  have houter (e : T × I) :
      vecMulVec (s e • (M *ᵥ fun i => b e.1 i e.2))
        (s e • (M *ᵥ fun i => b e.1 i e.2)) =
      M * (Real.exp (a e) • vecMulVec (fun i => b e.1 i e.2) (fun i => b e.1 i e.2)) * M := by
    simp only [Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul, hs,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    rw [← Matrix.vecMul_transpose M, hMT]
  have hnorm (e : T × I) :
      (s e • (M *ᵥ fun i => b e.1 i e.2)) ⬝ᵥ (s e • (M *ᵥ fun i => b e.1 i e.2)) =
      Real.exp (a e) * ((fun i => b e.1 i e.2) ⬝ᵥ
        ((packingCov b a)⁻¹ *ᵥ fun i => b e.1 i e.2)) := by
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, ← mul_assoc, hs]
    congr 1
    rw [← hMM, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      ← Matrix.mulVec_transpose M, hMT]
    exact dotProduct_comm _ _
  refine ⟨M, s, hMU, fun e => Real.exp_pos _, ?_, ?_⟩
  · simp_rw [houter]
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← packingCov_eq_sum, hMNM]
  · intro e
    rw [hnorm]
    exact ha e

end Covariance

end
end StrongThinTree

namespace StrongThinTree.Packing
noncomputable section
open Matrix Finset
open scoped BigOperators MatrixOrder Matrix.Norms.Elementwise

variable {E : Type uE2} [Fintype E] [DecidableEq E] {q d : ℕ}

omit [Fintype E] in

 theorem represented_packing (v : E → (Fin d → ℝ)) (F : Fin q → Finset E)
    (hq : 0 < q) (hF : ∀ t, LinearIndepOn ℝ v (F t : Set E))
    (hcard : ∀ t, (F t).card = d) (hd : Pairwise (fun i j => Disjoint (F i) (F j)))
    {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (M : Matrix (Fin d) (Fin d) ℝ) (s : E → ℝ),
      IsUnit M ∧ (∀ e, 0 < s e) ∧
      let z := fun e => s e • (M *ᵥ v e)
      (∑ e ∈ Finset.univ.biUnion F, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e ∈ Finset.univ.biUnion F, z e ⬝ᵥ z e ≤ (1 + ρ) / q) := by
  classical
  let : Nonempty (Fin q) := Fin.pos_iff_nonempty.mp hq
  let B := Finset.univ.biUnion F
  let en (t : Fin q) : Fin d ≃ ↥(F t) :=
    Fintype.equivOfCardEq (by simp [hcard])
  let b (t : Fin q) : Matrix (Fin d) (Fin d) ℝ := fun i j => v (en t j) i
  have hb : ∀ t, IsUnit (b t) := by
    intro t
    apply Matrix.mulVec_injective_iff_isUnit.mp
    apply Matrix.mulVec_injective_iff.mpr
    exact (hF t).linearIndependent.comp (en t) (en t).injective
  let f : Fin q × Fin d → ↥B := fun tj => ⟨en tj.1 tj.2,
    Finset.mem_biUnion.mpr ⟨tj.1, Finset.mem_univ _, (en tj.1 tj.2).2⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨t, j⟩ ⟨t', j'⟩ heq
      have hev : (en t j : E) = (en t' j' : E) := congrArg Subtype.val heq
      have ht : t = t' := by
        by_contra h
        exact Finset.disjoint_left.mp (hd h) (en t j).2 (hev ▸ (en t' j').2)
      subst t'
      have hj : j = j' := (en t).injective (Subtype.ext hev)
      subst j'; rfl
    · intro e
      obtain ⟨t, ht, he⟩ := Finset.mem_biUnion.mp e.2
      refine ⟨(t, (en t).symm ⟨e, he⟩), ?_⟩
      apply Subtype.ext
      simp [f]
  let eb := Equiv.ofBijective f hf
  obtain ⟨M, s₀, hM, hs₀, hz, hnorm⟩ := isotropic_representation b hb hρ
  let s : E → ℝ := fun e => if he : e ∈ B then s₀ (eb.symm ⟨e, he⟩) else 1
  have hs : ∀ e, 0 < s e := by
    intro e
    dsimp [s]
    split_ifs
    · exact hs₀ _
    · exact zero_lt_one
  have hs_eq (tj : Fin q × Fin d) : s (eb tj) = s₀ tj := by
    simp [s, (eb tj).2]
  refine ⟨M, s, hM, hs, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort]
    rw [← eb.sum_comp]
    convert hz using 1
    apply Finset.sum_congr rfl
    intro tj htj
    change vecMulVec (s (eb tj) • (M *ᵥ v (eb tj)))
      (s (eb tj) • (M *ᵥ v (eb tj))) = _
    rw [hs_eq]
    rfl
  · intro e he
    have hh := hnorm (eb.symm ⟨e, he⟩)
    have hv : v e = fun i => b (eb.symm ⟨e, he⟩).1 i (eb.symm ⟨e, he⟩).2 := by
      have hh : (en (eb.symm ⟨e, he⟩).1 (eb.symm ⟨e, he⟩).2 : E) = e :=
        congrArg Subtype.val (eb.apply_symm_apply ⟨e, he⟩)
      simp [b, hh]
    have heB : e ∈ B := he
    have hsE : s e = s₀ (eb.symm ⟨e, he⟩) := by simp only [s, dite_eq_left heB]
    change (s e • (M *ᵥ v e)) ⬝ᵥ (s e • (M *ᵥ v e)) ≤ _
    rw [hsE, hv]
    simpa only [Fintype.card_fin] using hh

end
end StrongThinTree.Packing

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

lemma zeroSum_finrank {T : Finset (Fin m)} (hn : 0 < n) (hT : G.Connected T) :
    Module.finrank ℝ (zeroSumSpace n) = n - 1 := by
  rw [← G.connected_span_zeroSum hn hT]
  exact G.connected_rank hn hT

theorem graph_isotropic_representation {q : ℕ} (hq : 0 < q) (hn : 2 ≤ n)
    (F : Fin q → Finset (Fin m)) (hF : ∀ t, G.SpanningTree (F t))
    (hd : Pairwise (fun i j => Disjoint (F i) (F j))) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n - 1) → ℝ)) (s : Fin m → ℝ),
      (∀ e, 0 < s e) ∧
      let z := fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      (∑ e ∈ Finset.univ.biUnion F, vecMulVec (z e) (z e)) = 1 ∧
      (∀ e ∈ Finset.univ.biUnion F, z e ⬝ᵥ z e ≤ (1 + ρ) / q) := by
  classical
  have hn' : 0 < n := by omega
  let L₀ : zeroSumSpace n ≃ₗ[ℝ] (Fin (n - 1) → ℝ) :=
    LinearEquiv.ofFinrankEq _ _ (by
      rw [G.zeroSum_finrank hn' (hF ⟨0, hq⟩).1]
      simp)
  let v := fun e => L₀ ⟨G.incidence e, G.incidence_zeroSum e⟩
  have hvi (t : Fin q) : LinearIndepOn ℝ v (F t : Set (Fin m)) := by
    have hi := ((G.spanningTree_iff_independent (F t)).mp (hF t)).2.linearIndependent
    have hi' : LinearIndependent ℝ
        (fun e : ↥(F t) => (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n)) :=
      hi.of_comp (zeroSumSpace n).subtype
    exact hi'.map' L₀.toLinearMap L₀.ker
  obtain ⟨M, s, hM, hs, hi, hb⟩ := Packing.represented_packing v F hq hvi
    (fun t => G.spanningTree_card hn' (hF t)) hd hρ
  let L := L₀.trans (Matrix.toLinearEquiv' M hM.invertible)
  exact ⟨L, s, hs, hi, hb⟩

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.Packing
noncomputable section
open scoped BigOperators
open Finset
variable {E : Type uE3} {V : Type uV} [Fintype E] [DecidableEq E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

omit [Fintype E] in

lemma projected_trace_bound (v : E → V) (A U : Finset E) {c h : ℝ}
    (_hU : U ⊆ A) (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    c * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
      h * (A \ U).card := by
  classical
  let W := span v U
  let b := stdOrthonormalBasis ℝ Wᗮ
  let w := fun i : Fin (Module.finrank ℝ Wᗮ) => (b i : V)
  have hw : Orthonormal ℝ w := by
    rw [orthonormal_iff_ite]
    intro i j
    exact (orthonormal_iff_ite.mp b.orthonormal) i j
  have hzero (i : Fin (Module.finrank ℝ Wᗮ)) (e : E) (he : e ∈ U) :
      inner ℝ (w i) (v e) = 0 :=
    Submodule.inner_left_of_mem_orthogonal (mem_span_self v he) (b i).2
  have hlow' (i : Fin (Module.finrank ℝ Wᗮ)) :
      c ≤ ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 := by
    have hi := hlow (w i)
    rw [hw.norm_eq_one, one_pow, mul_one] at hi
    have heq : ∑ e ∈ A \ U, (inner ℝ (w i) (v e)) ^ 2 =
        ∑ e ∈ A, (inner ℝ (w i) (v e)) ^ 2 := by
      apply Finset.sum_subset Finset.sdiff_subset
      intro e he hne
      have heU : e ∈ U := by simpa [he] using hne
      simp [hzero i e heU]
    rwa [heq]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i hi => hlow' i)
  have hsb : (∑ i : Fin (Module.finrank ℝ Wᗮ), ∑ e ∈ A \ U,
      (inner ℝ (w i) (v e)) ^ 2) ≤ ∑ e ∈ A \ U, h := by
    rw [Finset.sum_comm]
    apply Finset.sum_le_sum
    intro e he
    have hb := hw.sum_inner_products_le (s := Finset.univ) (v e)
    simp only [Real.norm_eq_abs, sq_abs] at hb
    exact hb.trans (hn e (Finset.mem_sdiff.mp he).1)
  have ht := hs.trans hsb
  have hdim := W.finrank_add_finrank_orthogonal
  have heq : Module.finrank ℝ Wᗮ = Module.finrank ℝ V - Module.finrank ℝ W := by omega
  simpa [heq, mul_comm, W] using ht

omit [Fintype E] in
lemma lower_frame_span (v : E → V) (A : Finset E) {c h : ℝ} (hc : 0 < c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    span v A = ⊤ := by
  have hb := projected_trace_bound v A A (Subset.refl _) hn hlow
  simp only [Finset.sdiff_self, Finset.card_empty, Nat.cast_zero, mul_zero] at hb
  have hzero : (Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) = 0 := by
    have hh : ((Module.finrank ℝ V - Module.finrank ℝ (span v A) : ℕ) : ℝ) ≤ 0 :=
      by nlinarith
    exact_mod_cast (le_antisymm hh (Nat.cast_nonneg _))
  apply Submodule.eq_top_of_finrank_eq
  have hle := (span v A).finrank_le
  omega

theorem projected_trace_base_packing (v : E → V) (A : Finset E)
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hn : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h)
    (hlow : ∀ x : V, c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2) :
    ∃ F : Fin r → Finset E, Valid v F ∧
      ∀ i, F i ⊆ A ∧ span v (F i) = ⊤ := by
  have htop := lower_frame_span v A hc hn hlow
  have hp : ∀ U : Finset E, U ⊆ A →
      Fintype.card (Fin r) * Module.finrank ℝ (span v A) ≤
        (A \ U).card + Fintype.card (Fin r) * Module.finrank ℝ (span v U) := by
    intro U hU
    have ht := projected_trace_bound v A U hU hn hlow
    have hdim := (span v U).finrank_le
    have hdiff : (r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ) ≤
        (A \ U).card := by
      have h₁ := mul_le_mul_of_nonneg_right hr
        (Nat.cast_nonneg (Module.finrank ℝ V - Module.finrank ℝ (span v U)))
      have h₂ : h * ((r : ℝ) * (Module.finrank ℝ V - Module.finrank ℝ (span v U) : ℕ)) ≤
          h * (A \ U).card := by linarith [h₁.trans ht]
      exact (mul_le_mul_iff_right₀ hh).mp h₂
    have hdiffN : r * (Module.finrank ℝ V - Module.finrank ℝ (span v U)) ≤
        (A \ U).card := by exact_mod_cast hdiff
    rw [htop, finrank_top, Fintype.card_fin]
    have heq : Module.finrank ℝ V =
        (Module.finrank ℝ V - Module.finrank ℝ (span v U)) + Module.finrank ℝ (span v U) := by omega
    rw [heq, Nat.mul_add]
    exact Nat.add_le_add_right hdiffN _
  obtain ⟨F, hF, hs⟩ := vector_base_packing_on v A hp
  exact ⟨F, hF, fun i => ⟨(hs i).1, (hs i).2.trans htop⟩⟩

end
end StrongThinTree.Packing

namespace StrongThinTree.Packing
noncomputable section
variable {E : Type uE4} {V : Type uV2} {W : Type uW} [Fintype E] [DecidableEq E]
  [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
  [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] in
lemma span_smul (v : E → V) (s : E → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset E) :
    span (fun e => s e • v e) U = span v U := by
  apply le_antisymm
  · apply (span_le_iff _).mpr
    intro e he
    exact Submodule.smul_mem _ _ (mem_span_self v he)
  · apply (span_le_iff _).mpr
    intro e he
    have h := Submodule.smul_mem (span (fun e => s e • v e) U) (s e)⁻¹
      (mem_span_self (fun e => s e • v e) he)
    simpa only [smul_smul, inv_mul_cancel₀ (hs e), one_smul] using h

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma span_map (v : E → V) (L : V →ₗ[ℝ] W) (U : Finset E) :
    span (fun e => L (v e)) U = (span v U).map L := by
  rw [span, Submodule.map_span, ← Set.image_image]

omit [Fintype E] [DecidableEq E] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] in
lemma rank_injective_map (v : E → V) (L : V →ₗ[ℝ] W)
    (hL : Function.Injective L) (U : Finset E) :
    Module.finrank ℝ (span (fun e => L (v e)) U) = Module.finrank ℝ (span v U) := by
  rw [span_map]
  exact (Submodule.equivMapOfInjective L hL (span v U)).finrank_eq.symm

end
end StrongThinTree.Packing

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix StrongThinTree.Packing
variable {n m : ℕ} (G : StrongThinTree.MultiGraph n m)

lemma represented_rank (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, s e ≠ 0) (U : Finset (Fin m)) :
    Module.finrank ℝ (Packing.span
      (fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) U) =
      Module.finrank ℝ (G.edgeSpan U) := by
  rw [Packing.span_smul _ s hs]
  change Module.finrank ℝ (Packing.span
    (fun e => L.toLinearMap (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n)) U) = _
  rw [Packing.rank_injective_map _ L.toLinearMap L.injective]
  symm
  exact Packing.rank_injective_map
    (fun e => (⟨G.incidence e, G.incidence_zeroSum e⟩ : zeroSumSpace n))
    (zeroSumSpace n).subtype Subtype.val_injective U

theorem represented_frame_treePackable (hn : 2 ≤ n)
    (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ))
    (s : Fin m → ℝ) (hs : ∀ e, 0 < s e) (A : Finset (Fin m))
    {r : ℕ} {c h : ℝ} (hc : 0 < c) (hh : 0 < h) (hr : (r : ℝ) * h ≤ c)
    (hnorm : ∀ e ∈ A, let z := s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      z ⬝ᵥ z ≤ h)
    (hlow : ∀ x : Fin (n-1) → ℝ, c * (x ⬝ᵥ x) ≤
      ∑ e ∈ A, (x ⬝ᵥ (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)) ^ 2) :
    G.TreePackable A r := by
  classical
  let z := fun e => s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
  let J := (WithLp.linearEquiv 2 ℝ (Fin (n-1) → ℝ)).symm
  let v := fun e => J (z e)
  have hnorm' : ∀ e ∈ A, ‖v e‖ ^ 2 ≤ h := by
    intro e he
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [v, J, z, dotProduct, pow_two] using hnorm e he
  have hlow' : ∀ x : EuclideanSpace ℝ (Fin (n-1)),
      c * ‖x‖ ^ 2 ≤ ∑ e ∈ A, (inner ℝ x (v e)) ^ 2 := by
    intro x
    rw [EuclideanSpace.real_norm_sq_eq]
    simpa [EuclideanSpace.inner_eq_star_dotProduct,
      v, J, z, dotProduct, pow_two, mul_comm] using hlow x.ofLp
  have hrank (U : Finset (Fin m)) :
      Module.finrank ℝ (Packing.span v U) = Module.finrank ℝ (G.edgeSpan U) := by
    change Module.finrank ℝ (Packing.span (fun e => J.toLinearMap (z e)) U) = _
    rw [Packing.rank_injective_map z J.toLinearMap J.injective]
    exact G.represented_rank L s (fun e => ne_of_gt (hs e)) U
  have htop := Packing.lower_frame_span v A hc hnorm' hlow'
  have hfull : Module.finrank ℝ (G.edgeSpan A) = n-1 := by
    rw [← hrank, htop, finrank_top]
    simp
  obtain ⟨F, hF, hFA⟩ := Packing.projected_trace_base_packing v A hc hh hr hnorm' hlow'
  refine ⟨F, ?_, hF.2⟩
  intro i
  refine ⟨(hFA i).1, (G.spanningTree_iff_independent (F i)).mpr ⟨?_, ?_⟩⟩
  · have hdim : Module.finrank ℝ (G.edgeSpan (F i)) = n-1 := by
      rw [← hrank, (hFA i).2, finrank_top]
      simp
    apply G.connected_of_componentCount_eq_one
    have hcomp := G.incidence_rank (F i)
    have hpos := G.componentCount_pos (by omega) (F i)
    omega
  · apply linearIndependent_iff_card_eq_finrank_span.mpr
    have heq : Set.range (fun e : (F i : Set (Fin m)) => G.incidence e) =
        G.incidence '' (F i : Set (Fin m)) := by ext x; simp
    change Fintype.card ↥(F i : Set (Fin m)) = Module.finrank ℝ (Submodule.span ℝ _)
    rw [heq]
    simpa [← hrank] using (Packing.indep_rank v (hF.1 i)).symm

end
end StrongThinTree.MultiGraph

namespace StrongThinTree.MultiGraph
noncomputable section
open Matrix
variable {n m : ℕ} (G : StrongThinTree.MultiGraph n m)

theorem projected_trace_treePackable (hn : 2 ≤ n) {q : ℕ} (hq : 0 < q)
    {ρ c : ℝ} (hρ : 0 < ρ) (hc : 0 < c)
    (L : zeroSumSpace n ≃ₗ[ℝ] (Fin (n-1) → ℝ)) (s : Fin m → ℝ)
    (hs : ∀ e, 0 < s e) (A B : Finset (Fin m)) (hAB : A ⊆ B)
    (hnorm : ∀ e ∈ B, let z := s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩
      z ⬝ᵥ z ≤ (1 + ρ) / q)
    (hlow : (∑ e ∈ A,
       vecMulVec (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)
         (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) -
       c • (1 : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)).PosSemidef) :
    G.TreePackable A ⌊c * q / (1 + ρ)⌋₊ := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hp : 0 < 1 + ρ := by linarith
  apply G.represented_frame_treePackable hn L s hs A hc (div_pos hp hq')
  · have hf := Nat.floor_le (le_of_lt (div_pos (mul_pos hc hq') hp))
    apply (le_div_iff₀ (div_pos hp hq')).symm.mpr
    convert hf using 1 ; field_simp
  · intro e he
    exact hnorm e (hAB he)
  · intro x
    have ht := hlow.dotProduct_mulVec_nonneg x
    simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
      Matrix.one_mulVec, dotProduct_smul, Matrix.sum_mulVec, dotProduct_sum] at ht
    suffices heq : (∑ e ∈ A,
        x ⬝ᵥ (vecMulVec (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)
          (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩) *ᵥ x)) =
        ∑ e ∈ A, (x ⬝ᵥ (s e • L ⟨G.incidence e, G.incidence_zeroSum e⟩)) ^ 2 by
      rw [heq] at ht
      simp only [smul_eq_mul] at ht
      linarith
    apply Finset.sum_congr rfl
    intro e he
    rw [Matrix.vecMulVec_mulVec]
    simp [dotProduct, Finset.mul_sum, pow_two, mul_comm, mul_left_comm]

end
end StrongThinTree.MultiGraph

end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.Normalization
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uD

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree
variable {D : Type uD} [Fintype D] [DecidableEq D]
omit [DecidableEq D] in
lemma symmetric_transform_dot (M : Matrix D D ℝ) (hM : Mᵀ=M) (x y : D → ℝ) :
    x ⬝ᵥ (M *ᵥ y)=(M *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec,←mulVec_transpose,hM]
omit [DecidableEq D] in
lemma qform_square (S : Matrix D D ℝ) (hS : Sᵀ=S) (x : D → ℝ) :
    qform (S*S) x=(S*ᵥx) ⬝ᵥ (S*ᵥx) := by
  rw [qform,←mulVec_mulVec,symmetric_transform_dot S hS]
namespace MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_le_base : G.laplacian univ ≤ G.baseMatrix := by
  apply le_add_of_nonneg_right
  exact (Matrix.PosSemidef.one.smul (by positivity : (0:ℝ) ≤ (n:ℝ)⁻¹)).nonneg

lemma normalized_vectors (hn : 0 < n) {X : Matrix (Fin n) (Fin n) ℝ}
    (hX : X ∈ G.matrixDomain) (B : Finset (Fin m)) :
    ∃a : Fin m → Fin n → ℝ,
      (∀x : Fin n → ℝ, (∑e ∈ B, (x ⬝ᵥ a e)^2) ≤ x ⬝ᵥ x) ∧
      (∀e, a e ⬝ᵥ a e=G.resistance X e) ∧
      (∀v : Fin n → ℝ, ∃x : Fin n → ℝ, x ⬝ᵥ x=qform X v ∧
        ∀e, x ⬝ᵥ a e=v ⬝ᵥ G.incidence e) := by
  classical
  obtain ⟨S,hSH,hSU,hSS⟩ := posDef_sqrt_factors (G.domain_pd hn hX)
  let M := S⁻¹
  have hST : Sᵀ=S := by simpa only [conjTranspose_eq_transpose_of_trivial] using hSH.eq
  have hMT : Mᵀ=M := by simpa only [M,conjTranspose_eq_transpose_of_trivial] using hSH.inv.eq
  have hMS : M*S=1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hSM : S*M=1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hSU)
  have hMM : M*M=X⁻¹ := by
    apply Eq.symm
    apply Matrix.inv_eq_left_inv
    rw [←hSS,mul_assoc,←mul_assoc M S S,hMS,one_mul,hMS]
  let a : Fin m → Fin n → ℝ := fun e => M*ᵥG.incidence e
  refine ⟨a,?_,?_,?_⟩
  · intro x
    have he : ∀e, x ⬝ᵥ a e=(M*ᵥx) ⬝ᵥ G.incidence e := fun e => symmetric_transform_dot M hMT x _
    simp_rw [he]
    have hb : (∑e ∈ B, ((M*ᵥx) ⬝ᵥ G.incidence e)^2) ≤
        ∑e : Fin m, ((M*ᵥx) ⬝ᵥ G.incidence e)^2 := by
      exact sum_le_sum_of_subset_of_nonneg (subset_univ B) (fun _ _ _ => sq_nonneg _)
    have heL : (∑e : Fin m, ((M*ᵥx) ⬝ᵥ G.incidence e)^2)=qform (G.laplacian univ) (M*ᵥx) := by
      rw [G.laplacian_qform]
      apply sum_congr rfl
      intro e _
      congr 1
      exact G.eval_incidence (M*ᵥx) e
    rw [heL] at hb
    have hh := hb.trans (qform_mono (G.laplacian_le_base.trans hX.1) (M*ᵥx))
    rw [←hSS,qform_square S hST,mulVec_mulVec,hSM,one_mulVec] at hh
    exact hh
  · intro e
    change (M*ᵥG.incidence e) ⬝ᵥ (M*ᵥG.incidence e)=qform X⁻¹ (G.incidence e)
    rw [←hMM,qform_square M hMT]
  · intro v
    refine ⟨S*ᵥv,?_,?_⟩
    · rw [←hSS,qform_square S hST]
    · intro e
      change (S*ᵥv) ⬝ᵥ (M*ᵥG.incidence e)=_
      rw [symmetric_transform_dot M hMT,mulVec_mulVec,hMS,one_mulVec]
end MultiGraph
end StrongThinTree

end
end

end OAI
end

section
-- module Solutions.OAIQW_StrongThinTree.SparsifyGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Matrix Finset
open scoped MatrixOrder
namespace StrongThinTree.MultiGraph
variable {n m : ℕ} (G : MultiGraph n m)
lemma laplacian_dot (B : Finset (Fin m)) (v : Fin n → ℝ) :
    qform (G.laplacian B) v=∑e ∈ B, (v ⬝ᵥ G.incidence e)^2 :=
  qform_covariance G.incidence B v

lemma sparsify_from_extraction_oai (hn : 2 ≤ n) {r : ℕ} (hnum : StepNumeric r)
    {X : Matrix (Fin n) (Fin n) ℝ} (hX : X ∈ G.matrixDomain)
    (hp : G.TreePackable (G.thresholdEdges (G.resistance X) (4*resistanceT r)) (extractQ r)) :
    ∃A : Finset (Fin m), G.TreePackable A (stepCount r) ∧
      ∀S : Finset (Fin n), S.Nonempty → S ≠ univ →
        ((G.cut A S).card:ℝ) ≤ (1/2+3*splitTau r)*(G.cut univ S).card := by
  classical
  have hrp : 0 < r := by have := hnum.rlarge; omega
  have hrR : (0:ℝ) < r := Nat.cast_pos.mpr hrp
  have hu : 0 < errorU r := Real.rpow_pos_of_pos hrR _
  have ht : 0 < resistanceT r := Real.rpow_pos_of_pos hrR _
  have hε : 0 < splitEpsilon r := by unfold splitEpsilon; positivity
  have hτ0 : 0 ≤ splitTau r := by unfold splitTau; positivity
  have hc : 0 < 1/2-splitTau r := by have := hnum.usmall; have := hnum.tausmall; linarith
  obtain ⟨F,hF,hd⟩ := hp
  let B := univ.biUnion F
  have hB : B ⊆ G.thresholdEdges (G.resistance X) (4*resistanceT r) := by
    intro e he
    obtain ⟨i,_,hei⟩ := mem_biUnion.mp he
    exact (hF i).1 hei
  obtain ⟨L,s,hs,hiso,hnorm⟩ := G.graph_isotropic_representation hnum.qpos hn F (fun i => (hF i).2) hd hu
  let z : Fin m → Fin (n-1) → ℝ := fun e => s e • L ⟨G.incidence e,G.incidence_zeroSum e⟩
  change (∑e ∈ B, vecMulVec (z e) (z e))=1 at hiso
  change ∀e ∈ B, z e ⬝ᵥ z e ≤ (1+errorU r)/(extractQ r:ℝ) at hnorm
  obtain ⟨a,ha,haNorm,haTest⟩ := G.normalized_vectors (by omega) hX B
  have hsum {V : Type} [AddCommMonoid V] (f : Fin m → V) :
      (∑e : B, f e)=∑e ∈ B, f e := by
    simpa only [attach_eq_univ] using sum_attach B f
  have hnormB (e : B) : a e ⬝ᵥ a e+z e ⬝ᵥ z e ≤ splitEpsilon r := by
    have hh := (mem_filter.mp (hB e.property)).2
    have hz := (hnorm e e.property).trans hnum.size
    rw [haNorm]
    unfold splitEpsilon
    linarith
  have haB (x : Fin n → ℝ) : (∑e : B, (x ⬝ᵥ a e)^2) ≤ x ⬝ᵥ x := by
    rw [hsum (fun e => (x ⬝ᵥ a e)^2)]; exact ha x
  have hzB (y : Fin (n-1) → ℝ) : (∑e : B, (y ⬝ᵥ z e)^2)=y ⬝ᵥ y := by
    rw [hsum (fun e => (y ⬝ᵥ z e)^2),←qform_covariance,hiso,qform,one_mulVec]
  obtain ⟨A₀,hAhi,hAlo⟩ := split_two_systems (fun e : B => a e) (fun e : B => z e) hε haB hzB hnormB
  let A : Finset (Fin m) := A₀.image Subtype.val
  have hAB : A ⊆ B := by
    intro e he
    obtain ⟨i,_,rfl⟩ := mem_image.mp he
    exact i.property
  have hsumA {V : Type} [AddCommMonoid V] (f : Fin m → V) :
      (∑e ∈ A, f e)=∑e ∈ A₀, f e := by
    exact sum_image (fun _ _ _ _ h => Subtype.ext h)
  have hlow : ((∑e ∈ A, vecMulVec (z e) (z e))-
      (1/2-splitTau r) • (1 : Matrix (Fin (n-1)) (Fin (n-1)) ℝ)).PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      ((Matrix.posSemidef_sum A (fun e _ => by
        simpa only [star_trivial] using posSemidef_vecMulVec_self_star (z e))).isHermitian.sub
        (Matrix.PosSemidef.one.smul hc.le).isHermitian)
    intro y
    have hh := hAlo y
    change (1/2-splitTau r)*(y ⬝ᵥ y) ≤ ∑e ∈ A₀, (y ⬝ᵥ z e)^2 at hh
    rw [←hsumA (fun e => (y ⬝ᵥ z e)^2)] at hh
    change 0 ≤ qform _ y
    rw [qform_sub,qform_covariance,qform_smul,qform,one_mulVec]
    linarith
  have hpack := G.projected_trace_treePackable hn hnum.qpos hu hc L s hs A B hAB hnorm hlow
  refine ⟨A,G.treePackable_mono_count hnum.packing hpack,?_⟩
  intro S hS hS'
  obtain ⟨x,hx,he⟩ := haTest (cutIndicator S)
  have hh := hAhi x
  change (∑e ∈ A₀, (x ⬝ᵥ a e)^2) ≤
    (1/2:ℝ)*(∑e : B, (x ⬝ᵥ a e)^2)+splitTau r*(x ⬝ᵥ x) at hh
  rw [←hsumA (fun e => (x ⬝ᵥ a e)^2),hsum (fun e => (x ⬝ᵥ a e)^2),hx] at hh
  simp_rw [he] at hh
  rw [←G.laplacian_dot,←G.laplacian_dot,G.laplacian_cut,G.laplacian_cut] at hh
  have hcutSub : G.cut B S ⊆ G.cut univ S := by
    intro e he
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp he).2⟩
  have hcut : ((G.cut B S).card:ℝ) ≤ (G.cut univ S).card := by exact_mod_cast card_le_card hcutSub
  have hXcut := mul_le_mul_of_nonneg_left (hX.2 S hS hS') hτ0
  linarith

end StrongThinTree.MultiGraph

end
end

end OAI
end

theorem solution : type_of% @OAI.StrongThinTree.MultiGraph.sparsify_from_extraction_oai := @OAI.StrongThinTree.MultiGraph.sparsify_from_extraction_oai
