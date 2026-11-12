-- Prove2me | solution 1 for OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T11:33:18.584654+00:00
-- url     : https://prove2.me/submissions/662e989a-2f95-446c-a6a8-f76fc52b140f

import Mathlib
import Definitions.Def_Q238L018
import Definitions.Def_Q238L021

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_Blue
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion

variable {V : Type*} [DecidableEq V] {a : ℕ}

lemma designatedProxies_mem (R : Finset V) (dest : V → Destination V a) (v : V) :
    v ∈ designatedProxies R dest ↔ ∃ s ∈ R, dest s = .proxy v := by
  simp only [designatedProxies,Finset.mem_biUnion]
  constructor
  · rintro ⟨s,hs,hv⟩
    refine ⟨s,hs,?_⟩
    cases he : dest s with
    | proxy w =>
      simp only [he,Finset.mem_singleton] at hv
      subst w
      rfl
    | covered i => simp only [he,Finset.notMem_empty] at hv
    | uncovered o => simp only [he,Finset.notMem_empty] at hv
  · rintro ⟨s,hs,he⟩
    exact ⟨s,hs,by simp only [he,Finset.mem_singleton]⟩

lemma favorable_color_consequences (R : Finset V) (dest : V → Destination V a)
    (hdisj : Disjoint R (designatedProxies R dest)) (colors : V → Fin 3)
    (hcolors : ∀ s ∈ R ∪ designatedProxies R dest, colors s = requiredColors R dest s) :
    (∀ s ∈ designatedRed R dest, colors s = 1) ∧
    (∀ s ∈ designatedBlue R dest, colors s = 2) ∧
    (∀ s ∈ designatedProxies R dest, colors s = 0) := by
  refine ⟨?_,?_,?_⟩
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd,Bool.false_eq_true] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    obtain ⟨hsR,hsd⟩ := Finset.mem_filter.mp hs
    simpa only [requiredColors,hsR,↓reduceIte,hsd] using
      hcolors s (Finset.mem_union_left _ hsR)
  · intro s hs
    have hn : s ∉ R := fun hr => Finset.disjoint_left.mp hdisj hr hs
    simpa only [requiredColors,hn,↓reduceIte] using
      hcolors s (Finset.mem_union_right _ hs)

lemma proxy_requirements_consistent (R Proxies : Finset V)
    (dest : V → Destination V a) (hRP : Disjoint R Proxies)
    (hdest : ∀ s ∈ R, ∀ v, dest s = .proxy v → v ∈ Proxies) :
    Disjoint R (designatedProxies R dest) := by
  refine hRP.mono_right ?_
  intro v hv
  obtain ⟨s,hs,he⟩ := (designatedProxies_mem R dest v).mp hv
  exact hdest s hs v he

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_State2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling

variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

lemma chosen_mem (S : Finset V) (Δ : ℝ) (s : State V) (x : V) :
    chosen S Δ s x ∈ tags S s :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).1

lemma chosen_key_le (S : Finset V) (Δ : ℝ) (s : State V) (x : V) {t : Tag V}
    (ht : t ∈ tags S s) :
    toLex (tagDistance Δ s x (chosen S Δ s x),chosen S Δ s x) ≤
      toLex (tagDistance Δ s x t,t) :=
  (Classical.choose_spec (Finset.exists_min_image (tags S s)
    (fun t => toLex (tagDistance Δ s x t,t)) (tags_nonempty S s))).2 t ht

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_CoveredCenter
attribute [-simp] _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_ball _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_permanent _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real _root_.OAI.MetricKMedianRecovery.Completion.Virtual.cast_real_iff _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_proxy _root_.OAI.MetricKMedianRecovery.Sampling.Comparison.destinations_uncovered
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V]

omit [LinearOrder V] [PseudoMetricSpace V] in
lemma toVirtual_real_iff (s : State V) (t : Tag V) (v : V) :
    toVirtual s t = .real v ↔ t = realTag v := by
  cases ht : ofLex t with
  | inl u =>
    have he : t = realTag u := congrArg toLex ht
    subst t
    simp [toVirtual,realTag]
  | inr j =>
    have he : t = leafTag j := congrArg toLex ht
    subst t
    cases j with
    | zero => simp [toVirtual,leafTag,realTag]
    | succ j => simp [toVirtual,leafTag,realTag]; split <;> simp_all

lemma completionAssignment_real_iff (S : Finset V) (Δ : ℝ) (s : State V) (x v : V) :
    completionAssignment S Δ s x = .real v ↔ chosen S Δ s x = realTag v :=
  toVirtual_real_iff s (chosen S Δ s x) v

end MetricKMedianRecovery.Sampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Sampling_RationalSampling
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling
variable {n : ℕ}
lemma tagId_le_iff (t u : Tag (Fin n)) : tagId t≤tagId u ↔ t≤u := by
  cases t using Sum.rec with
  | inl a =>
    cases u using Sum.rec with
    | inl b =>
      change a.val≤b.val ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact (@Sum.Lex.inl_le_inl_iff (Fin n) ℕ _ _ a b).symm
    | inr b =>
      change a.val≤n+b ↔ toLex (Sum.inl a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      exact iff_of_true (by omega) (Sum.Lex.inl_le_inr a b)
  | inr a =>
    cases u using Sum.rec with
    | inl b =>
      change n+a≤b.val ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inl b)
      exact iff_of_false (by omega) Sum.Lex.not_inr_le_inl
    | inr b =>
      change n+a≤n+b ↔ toLex (Sum.inr a:Fin n⊕ℕ)≤toLex (Sum.inr b)
      rw [Sum.Lex.inr_le_inr_iff]
      omega
lemma tagId_injective : Function.Injective (tagId (n:=n)) := by
  intro t u h
  exact le_antisymm ((tagId_le_iff t u).mp h.le) ((tagId_le_iff u t).mp h.ge)
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ in
lemma tagDistance_cast (Δ : ℚ) (s : State n) (w : Fin n) (t : Tag (Fin n)) :
    (tagDistance δ Δ s w t:ℝ)=Sampling.tagDistance (Δ:ℝ) s.real w t := by
  cases ht : ofLex t with
  | inl v=>simp only [tagDistance,Sampling.tagDistance,ht,hδ]
  | inr j=>
    cases j with
    | zero=>simp only [tagDistance,Sampling.tagDistance,ht]
    | succ j=>
      simp only [tagDistance,Sampling.tagDistance,ht,State.real,List.getElem?_map]
      cases hz : s.leaves[j]? <;> simp only [Option.map_none,Option.map_some,Rat.cast_add,hδ]
include hδ in
lemma key_le_iff (Δ : ℚ) (s : State n) (w : Fin n) (t u : Tag (Fin n)) :
    key δ Δ s w t≤ key δ Δ s w u ↔
      toLex (Sampling.tagDistance (Δ:ℝ) s.real w t,t)≤toLex (Sampling.tagDistance (Δ:ℝ) s.real w u,u) := by
  rw [←tagDistance_cast δ hδ Δ s w t,←tagDistance_cast δ hδ Δ s w u]
  simp only [key,Prod.Lex.le_iff,ofLex_toLex,Rat.cast_lt,Rat.cast_inj,tagId_le_iff]
include hδ in
lemma minimum_key (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    (keys δ S Δ s w).min' (keys_nonempty δ S Δ s w)=key δ Δ s w (Sampling.chosen S (Δ:ℝ) s.real w) := by
  apply le_antisymm
  · exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨_,Sampling.chosen_mem S (Δ:ℝ) s.real w,rfl⟩)
  · apply Finset.le_min'
    intro x hx
    obtain ⟨t,ht,rfl⟩:=Finset.mem_image.mp hx
    exact (key_le_iff δ hδ Δ s w _ t).mpr (Sampling.chosen_key_le S (Δ:ℝ) s.real w ht)
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Encoding_RationalMenus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
open Sampling BitMachine
variable {n : ℕ}
section Metric
variable [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
include hδ
lemma chosenId_eq (S : Finset (Fin n)) (Δ : ℚ) (s : State n) (w : Fin n) :
    chosenId δ S Δ s w=tagId (Sampling.chosen S (Δ:ℝ) s.real w) := by
  simp only [chosenId,chosenKey,minimum_key δ hδ,key,ofLex_toLex]
end Metric
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.RationalSampling
variable {n : ℕ}
lemma assignmentWeight_cast [PseudoMetricSpace (Fin n)] (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : State n) (u : Fin n) :
    (assignmentWeight δ D S Δ s u:ℝ)=Completion.assignmentWeight D (Sampling.completionAssignment S (Δ:ℝ) s.real) u := by
  have he (p : Fin n) : chosenId δ S Δ s p=u.val ↔ Sampling.completionAssignment S (Δ:ℝ) s.real p=Completion.Virtual.real u := by
    rw [Sampling.completionAssignment_real_iff,chosenId_eq δ hδ]
    change tagId (Sampling.chosen S (Δ:ℝ) s.real p)=tagId (Sampling.realTag u) ↔ _
    exact tagId_injective.eq_iff
  simp only [assignmentWeight,Completion.assignmentWeight,he,Rat.cast_natCast]
end MetricKMedianRecovery.RationalSampling

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_Blocks
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BlueSubsetDP
open Finset
variable {L : Type*} [DecidableEq L]

lemma Partition.subset {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : ∀ V ∈ P, V ⊆ U := by
  induction h with
  | nil => simp
  | cons hne hsub tail ih =>
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact hsub
    · exact (ih _ hW).trans Finset.sdiff_subset

lemma Partition.nonempty {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : ∀ V ∈ P, V.Nonempty := by
  induction h with
  | nil => simp
  | cons hne hsub tail ih =>
    intro W hW
    rcases List.mem_cons.mp hW with rfl | hW
    · exact hne
    · exact ih _ hW

lemma Partition.union {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : P.foldr (· ∪ ·) ∅ = U := by
  induction h with
  | nil => rfl
  | @cons U V P hne hsub tail ih =>
    simp only [List.foldr_cons, ih]
    exact Finset.union_sdiff_of_subset hsub

lemma Partition.length_le {U : Finset L} {P : List (Finset L)}
    (h : Partition U P) : P.length ≤ U.card := by
  induction h with
  | nil => simp
  | @cons U V P hne hsub tail ih =>
    have hcard := Finset.card_sdiff_add_card_eq_card hsub
    have hv := hne.card_pos
    simp only [List.length_cons]
    omega

lemma value_le_partition (C : Finset L → WithTop ℝ) {U : Finset L}
    {P : List (Finset L)} (h : Partition U P) :
    value C P.length U ≤ (P.map C).sum := by
  induction h with
  | nil => simp [value]
  | @cons U V P hne hsub tail ih =>
    simp only [List.length_cons, value, List.map_cons, List.sum_cons]
    exact (Finset.inf_le (mem_blocks.mpr ⟨hne, hsub⟩)).trans (add_le_add (le_refl _) ih)

lemma best_le_partition (C : Finset L → WithTop ℝ) (c : ℕ) {U : Finset L}
    {P : List (Finset L)} (hP : Partition U P) (hlen : P.length ≤ c) :
    best C c U ≤ (P.map C).sum := by
  by_cases hu : U = ∅
  · have hp : P = [] := List.length_eq_zero_iff.mp (by
      have := hP.length_le
      simpa [hu] using this)
    simp [best, hu, hp]
  · have hp : 0 < P.length := by
      by_contra hn
      have he : P = [] := List.length_eq_zero_iff.mp (by omega)
      have := hP.union
      simp [he] at this
      exact hu this.symm
    simp only [best, hu, ↓reduceIte]
    exact (Finset.inf_le (Finset.mem_Icc.mpr ⟨hp, hlen⟩)).trans (value_le_partition C hP)

variable {R Y : Type*} [DecidableEq R] [DecidableEq Y]

omit [DecidableEq R] [DecidableEq Y] in
lemma blockCost_le (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (y : Y) (hy : y ∈ F) (sel : L → R)
    (hsel : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l) :
    blockCost B F label q U ≤ (∑ l ∈ U, q (sel l) y : ℝ) := by
  unfold blockCost
  refine (Finset.inf_le hy).trans ?_
  rw [WithTop.coe_sum]
  apply Finset.sum_le_sum
  intro l hl
  exact Finset.inf_le (Finset.mem_filter.mpr (hsel l hl))

lemma Partition.cost_sum {U : Finset L} {P : List (Finset L)} (h : Partition U P)
    {M : Type*} [AddCommMonoid M] (q : L → M) :
    (P.map (fun V => ∑ l ∈ V, q l)).sum = ∑ l ∈ U, q l := by
  induction h with
  | nil => simp
  | @cons U V P hne hsub tail ih =>
    simp only [List.map_cons, List.sum_cons, ih]
    simpa only [add_comm] using Finset.sum_sdiff hsub (f := q)

lemma partition_by_destination (U : Finset L) (dst : L → Y) :
    ∃ P, Partition U P ∧ P.length ≤ (U.image dst).card ∧
      ∀ V ∈ P, ∃ y, ∀ l ∈ V, dst l = y := by
  classical
  refine Finset.strongInductionOn U ?_
  intro U ih
  by_cases he : U = ∅
  · subst U
    exact ⟨[], Partition.nil, by simp, by simp⟩
  obtain ⟨l₀, hl₀⟩ := Finset.nonempty_iff_ne_empty.mpr he
  let V := U.filter (fun l => dst l = dst l₀)
  have hlV : l₀ ∈ V := by simp [V, hl₀]
  have hV : V.Nonempty := ⟨l₀, hlV⟩
  have hVU : V ⊆ U := Finset.filter_subset _ _
  have hss : U \ V ⊂ U := Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.sdiff_subset, fun hh => (Finset.mem_sdiff.mp (hh ▸ hl₀)).2 hlV⟩
  obtain ⟨P, hP, hlen, hconst⟩ := ih _ hss
  have himage : (U \ V).image dst ⊆ (U.image dst).erase (dst l₀) := by
    intro y hy
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hy
    rcases Finset.mem_sdiff.mp hl with ⟨hlU, hlV'⟩
    exact Finset.mem_erase.mpr ⟨fun hh => hlV' (Finset.mem_filter.mpr ⟨hlU, hh⟩),
      Finset.mem_image.mpr ⟨l, hlU, rfl⟩⟩
  have hc := Finset.card_le_card himage
  have hecard := Finset.card_erase_add_one (Finset.mem_image.mpr ⟨l₀, hl₀, rfl⟩ : dst l₀ ∈ U.image dst)
  refine ⟨V :: P, Partition.cons hV hVU hP, by simp only [List.length_cons]; omega, ?_⟩
  intro W hW
  rcases List.mem_cons.mp hW with rfl | hW
  · exact ⟨dst l₀, fun l hl => (Finset.mem_filter.mp hl).2⟩
  · exact hconst _ hW
omit [DecidableEq R] in

lemma best_le_routing (B : Finset R) (F : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (U : Finset L) (c : ℕ) (sel : L → R) (dst : L → Y)
    (hsel : ∀ l ∈ U, sel l ∈ B ∧ label (sel l) = l)
    (hdst : ∀ l ∈ U, dst l ∈ F) (hcount : (U.image dst).card ≤ c) :
    best (blockCost B F label q) c U ≤ (∑ l ∈ U, q (sel l) (dst l) : ℝ) := by
  obtain ⟨P, hP, hlen, hconst⟩ := partition_by_destination U dst
  refine (best_le_partition _ _ hP (hlen.trans hcount)).trans ?_
  rw [WithTop.coe_sum, ← hP.cost_sum (fun l => (q (sel l) (dst l) : WithTop ℝ))]
  apply List.sum_le_sum
  intro V hV
  obtain ⟨y, hy⟩ := hconst V hV
  obtain ⟨l₀, hl₀⟩ := hP.nonempty V hV
  have hyF : y ∈ F := hy l₀ hl₀ ▸ hdst l₀ (hP.subset V hV hl₀)
  calc
    blockCost B F label q V ≤ (∑ l ∈ V, q (sel l) y : ℝ) :=
      blockCost_le B F label q V y hyF sel (fun l hl => hsel l (hP.subset V hV hl))
    _ = ∑ l ∈ V, (q (sel l) (dst l) : WithTop ℝ) := by
      rw [WithTop.coe_sum]
      apply Finset.sum_congr rfl
      intro l hl
      rw [hy l hl]

end BlueSubsetDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_BestDesignation
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]

omit [DecidableEq R] in

lemma best_le_designation (B T : Finset R) (F C : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (dest : R → Y) (hT : T ⊆ B) (hC : C ⊆ F)
    (hcard : T.card = Fintype.card L) (hinj : Set.InjOn label (↑T))
    (hdest : ∀ r ∈ T, dest r ∈ C) :
    best (blockCost B F label q) C.card Finset.univ ≤
      (∑ r ∈ T, q r (dest r) : ℝ) := by
  classical
  let map : ↥T → L := fun r => label r
  have hmap : Function.Injective map := by
    intro r s he
    exact Subtype.ext (hinj r.property s.property he)
  have hsur : Function.Surjective map :=
    (Fintype.bijective_iff_injective_and_card map).mpr ⟨hmap, by simpa using hcard⟩ |>.2
  let e : ↥T ≃ L := Equiv.ofBijective map ⟨hmap,hsur⟩
  let sel : L → R := fun l => (e.symm l).val
  let dst : L → Y := fun l => dest (sel l)
  have hs : ∀ l ∈ (Finset.univ : Finset L), sel l ∈ B ∧ label (sel l) = l := by
    intro l _
    exact ⟨hT (e.symm l).property,e.apply_symm_apply l⟩
  have hd : ∀ l ∈ (Finset.univ : Finset L), dst l ∈ F := by
    intro l _
    exact hC (hdest _ (e.symm l).property)
  have hc : (Finset.univ.image dst).card ≤ C.card := by
    apply Finset.card_le_card
    intro y hy
    obtain ⟨l,_,rfl⟩ := Finset.mem_image.mp hy
    exact hdest _ (e.symm l).property
  have hh := best_le_routing B F label q Finset.univ C.card sel dst hs hd hc
  have he : (∑ l : L, q (sel l) (dst l)) = ∑ r ∈ T, q r (dest r) := by
    change (∑ l : L, q (e.symm l).val (dest (e.symm l).val)) = _
    exact (e.symm.sum_comp (fun r : ↥T => q r.val (dest r.val))).trans
      (Finset.sum_coe_sort T (fun r => q r (dest r)))
  rwa [he] at hh

end BlueSubsetDP
namespace BlueSubsetDP
variable {R Y L : Type*} [DecidableEq R] [DecidableEq Y] [DecidableEq L] [Fintype L]

lemma computedPlan_success [Nonempty R] [Nonempty Y]
    (B T : Finset R) (F C : Finset Y) (label : R → L)
    (q : R → Y → ℝ) (dest : R → Y) (hT : T ⊆ B) (hC : C ⊆ F)
    (hcard : T.card = Fintype.card L) (hinj : Set.InjOn label (↑T))
    (hdest : ∀ r ∈ T, dest r ∈ C) :
    ∃ P : Plan B F label q C.card,
      computedPlan B F label q C.card = some P ∧
      (∑ l, q (P.sel l) (P.dst l)) ≤ ∑ r ∈ T, q r (dest r) := by
  have hle := best_le_designation B T F C label q dest hT hC hcard hinj hdest
  have hfin : best (blockCost B F label q) C.card Finset.univ ≠ ⊤ :=
    ne_top_of_le_ne_top WithTop.coe_ne_top hle
  simp only [computedPlan,dite_eq_right hfin]
  refine ⟨_,rfl,?_⟩
  exact WithTop.coe_le_coe.mp ((Classical.choice (plan_exists B F label q C.card hfin)).value_eq.le.trans hle)

end BlueSubsetDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Strictness_ClientCharge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [PseudoMetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma selectedDestination_mem {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    selectedDestination theta center w radius Ω hΩ s ∈ Ω :=
  (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).1

omit [DecidableEq V] in
lemma selectedDestination_distance {a : ℕ} (theta : ℝ) (center w : Fin a → V)
    (radius : Fin a → ℝ) (Ω : Finset (Destination V a)) (hΩ : Ω.Nonempty) (s : V) :
    mixedDistance theta center w radius s (selectedDestination theta center w radius Ω hΩ s) =
      minimumMixed theta center w radius Ω hΩ s := by
  apply le_antisymm
  · exact Finset.le_inf' _ _ (fun d hd =>
      (Classical.choose_spec (Finset.exists_min_image Ω (mixedDistance theta center w radius s) hΩ)).2 d hd)
  · exact Finset.inf'_le _ (selectedDestination_mem theta center w radius Ω hΩ s)

end MetricKMedianRecovery.Completion

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_DestinationFacility
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Completion
variable {V : Type*} [DecidableEq V] {a : ℕ}

omit [DecidableEq V] in
lemma blue_destination_eq (d : Destination V a) (h : d.isBlue = true) (center : Fin a → V) :
    d = .uncovered (destinationFacility center d) := by
  cases d <;> simp_all [Destination.isBlue,destinationFacility]

end MetricKMedianRecovery.Completion

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma designatedDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (v : V) :
    C.designatedDestination hD s theta v ∈ C.destinations s :=
  selectedDestination_mem theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) v

lemma designation_disjoint (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) :
    Disjoint (C.nonproxy \ s.deleted)
      (designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) := by
  apply proxy_requirements_consistent (C.nonproxy \ s.deleted) (C.good.image C.proxy)
  · apply Finset.disjoint_left.mpr
    intro v hv hp
    exact (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hv).1).2 hp
  · intro u _ v he
    have hh := C.designatedDestination_mem hD s theta u
    rw [he] at hh
    exact (C.destinations_proxy s v).mp hh

lemma blueDestination_uncovered (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.designatedDestination hD s theta u = .uncovered (C.blueDestination hD s theta u) :=
  blue_destination_eq _ (Finset.mem_filter.mp hu).2 _

lemma blueDestination_mem (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    C.blueDestination hD s theta u ∈ C.bad \ C.covered s := by
  have hh := C.designatedDestination_mem hD s theta u
  rw [C.blueDestination_uncovered hD s theta u hu] at hh
  exact (C.destinations_uncovered s _).mp hh

lemma blueDestination_distance (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (u : V)
    (hu : u ∈ designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) :
    dist u (C.blueDestination hD s theta u) =
      minimumMixed theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
        (C.destinations s) (C.destinations_nonempty hD s) u := by
  have hh := selectedDestination_distance theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
    (C.destinations s) (C.destinations_nonempty hD s) u
  change mixedDistance theta (C.coveredCenter s) (leafCenter s) (leafRadius s) u
    (C.designatedDestination hD s theta u) = _ at hh
  rw [C.blueDestination_uncovered hD s theta u hu] at hh
  exact hh

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Recovery_SubsetSubtypeRepresentative
attribute [-instance] _root_.OAI.MetricKMedianRecovery.Categorical.binaryOracleIndexDecidableEq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.Sampling.Comparison
open Completion
variable {V : Type*} [LinearOrder V] [PseudoMetricSpace V] {D S O : Finset V}

lemma nonproxy_remaining_in (C : Comparison D S O) (s : State V) :
    C.nonproxy \ s.deleted ⊆ S \ s.deleted := by
  intro u hu
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hu).1).1,
    (Finset.mem_sdiff.mp hu).2⟩

lemma favorable_color_subsets (C : Comparison D S O) (hD : D.Nonempty)
    (s : State V) (theta : ℝ) (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u) :
    designatedRed (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 1 ∧
    designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) ⊆
        colorClass (S \ s.deleted) colors 2 := by
  have hh := favorable_color_consequences (C.nonproxy \ s.deleted)
    (C.designatedDestination hD s theta) (C.designation_disjoint hD s theta) colors hcolors
  exact ⟨fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.1 u hu⟩,
    fun u hu => Finset.mem_filter.mpr
    ⟨C.nonproxy_remaining_in s (Finset.mem_filter.mp hu).1,hh.2.1 u hu⟩⟩

lemma favorable_computedPlan {L : Type*} [Fintype L] [DecidableEq L] [Nonempty V]
    (C : Comparison D S O) (hD : D.Nonempty) (s : State V) (theta Δ : ℝ)
    (F : Finset V) (hOF : O ⊆ F) (colors : V → Fin 3)
    (hcolors : ∀ u ∈ (C.nonproxy \ s.deleted) ∪
        designatedProxies (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta),
      colors u = requiredColors (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta) u)
    (label : V → L)
    (hcard : (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).card =
      Fintype.card L)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy \ s.deleted)
      (C.designatedDestination hD s theta)))) :
    let B := designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)
    let Y := B.image (C.blueDestination hD s theta)
    let score := fun u v => assignmentWeight D (completionAssignment S Δ s) u * dist u v
    ∃ P : BlueSubsetDP.Plan (colorClass (S \ s.deleted) colors 2) F label score Y.card,
      BlueSubsetDP.computedPlan (colorClass (S \ s.deleted) colors 2) F label score Y.card = some P ∧
      (∑ l, score (P.sel l) (P.dst l)) ≤ ∑ u ∈ B,
        assignmentWeight D (completionAssignment S Δ s) u *
        minimumMixed theta (C.coveredCenter s) (leafCenter s) (leafRadius s)
          (C.destinations s) (C.destinations_nonempty hD s) u := by
  classical
  dsimp only
  have hBF := C.favorable_color_subsets hD s theta colors hcolors
  have hYF : (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).image
      (C.blueDestination hD s theta) ⊆ F := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    exact hOF (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp
      (C.blueDestination_mem hD s theta u hu)).1).1
  obtain ⟨P,hP,hval⟩ := BlueSubsetDP.computedPlan_success
    (colorClass (S \ s.deleted) colors 2)
    (designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)) F
    ((designatedBlue (C.nonproxy \ s.deleted) (C.designatedDestination hD s theta)).image
      (C.blueDestination hD s theta)) label
    (fun u v => assignmentWeight D (completionAssignment S Δ s) u * dist u v)
    (C.blueDestination hD s theta) hBF.2 hYF hcard hinj
    (fun u hu => Finset.mem_image.mpr ⟨u,hu,rfl⟩)
  refine ⟨P,hP,hval.trans_eq ?_⟩
  apply Finset.sum_congr rfl
  intro u hu
  rw [C.blueDestination_distance hD s theta u hu]

end MetricKMedianRecovery.Sampling.Comparison

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchChecksCorrect
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BlueDP
variable {L R Y : Type*} [LinearOrder L] [LinearOrder R] [LinearOrder Y] [Fintype L]
lemma best_some_of_plan (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (P : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c) :
    ∃ v xs,best (block B F label q) c Finset.univ=some (v,xs) := by
  have hh:=optimizer_value B F label q c Finset.univ
  cases he : best (block B F label q) c Finset.univ with
  | none=>
    rw [he,value,←P.value_eq] at hh
    exact False.elim (WithTop.coe_ne_top hh.symm)
  | some x=>exact ⟨x.1,x.2,rfl⟩
omit [LinearOrder R] in
lemma plan_value_unique (B : Finset R) (F : Finset Y) (label : R→L) (q : R→Y→ℚ) (c : ℕ)
    (P Q : BlueSubsetDP.Plan B F label (fun r y=>(q r y:ℝ)) c) :
    (∑ l,(q (P.sel l) (P.dst l):ℝ))=∑ l,(q (Q.sel l) (Q.dst l):ℝ) := by
  exact WithTop.coe_injective (P.value_eq.trans Q.value_eq.symm)
end MetricKMedianRecovery.BlueDP

end OAI
end

section
-- module Solutions.Q238_KM.KMedianRecovery_Branching_BranchObjective
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryBranchProgram
open Completion Categorical FiniteSampling BinaryBranchContext Sampling
variable {n m : ℕ} [PseudoMetricSpace (Fin n)]
lemma score_cast (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D S : Finset (Fin n)) (Δ : ℚ) (s : RationalSampling.State n) :
    (fun u v=>(rationalScore δ D S Δ s u v:ℝ))=branchScore D S (Δ:ℝ) s.real := by
  funext u v
  simp only [rationalScore,branchScore,Rat.cast_mul,hδ,RationalSampling.assignmentWeight_cast δ hδ]
lemma favorable_literal_plan_s238r_oai [Nonempty (Fin n)]
    (δ : Fin n→Fin n→ℚ) (hδ : ∀ i j,(δ i j:ℝ)=dist i j)
    (D F S O : Finset (Fin n)) (C : Comparison D S O) (hD : D.Nonempty) (hOF : O⊆F)
    (Δ : ℚ) (s : RationalSampling.State n) (colors : Fin n→Fin 3)
    (hcolors : ∀ u∈(C.nonproxy\s.real.deleted)∪designatedProxies (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)),colors u=requiredColors (C.nonproxy\s.real.deleted)
      (C.designatedDestination hD s.real (19/50)) u)
    (label : Fin n→Fin m)
    (hcard : (designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))).card=m)
    (hinj : Set.InjOn label (↑(designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50)))))
    (r0 y0 : Fin n) :
    let blue:=(S\s.deleted).filter (fun i=>colors i=2)
    let score:=rationalScore δ D S Δ s
    let bd:=designatedBlue (C.nonproxy\s.real.deleted) (C.designatedDestination hD s.real (19/50))
    let c:=(bd.image (C.blueDestination hD s.real (19/50))).card
    ∃ v xs,∃ h : BlueDP.best (BlueDP.block blue F label score) c Finset.univ=some (v,xs),
      let P:=BlueDP.makePlan blue F label score c r0 y0 v xs h
      (∑ l,branchScore D S (Δ:ℝ) s.real (P.sel l) (P.dst l))≤
        ∑ u∈bd,assignmentWeight D (completionAssignment S (Δ:ℝ) s.real) u*
          minimumMixed (19/50) (C.coveredCenter s.real) (leafCenter s.real) (leafRadius s.real)
            (C.destinations s.real) (C.destinations_nonempty hD s.real) u := by
  classical
  dsimp only
  obtain ⟨P0,hP0,hvalue⟩:=C.favorable_computedPlan hD s.real (19/50) (Δ:ℝ) F hOF colors hcolors label
    (by simpa only [Fintype.card_fin] using hcard) hinj
  clear hP0
  change BlueSubsetDP.Plan ((S\s.deleted).filter (fun i=>colors i=2)) F label
    (branchScore D S (Δ:ℝ) s.real) _ at P0
  let P0':=P0.reweight (fun u v=>(rationalScore δ D S Δ s u v:ℝ)) (score_cast δ hδ D S Δ s)
  obtain ⟨v,xs,h⟩:=BlueDP.best_some_of_plan _ _ label (rationalScore δ D S Δ s) _ P0'
  refine ⟨v,xs,h,?_⟩
  let P:=BlueDP.makePlan _ _ label (rationalScore δ D S Δ s) _ r0 y0 v xs h
  have hv:=BlueDP.plan_value_unique _ _ label (rationalScore δ D S Δ s) _ P P0'
  have he:=score_cast δ hδ D S Δ s
  have hev (u v : Fin n) : (rationalScore δ D S Δ s u v:ℝ)=branchScore D S (Δ:ℝ) s.real u v :=
    congrFun (congrFun he u) v
  simp only [hev] at hv
  exact hv.le.trans hvalue
end MetricKMedianRecovery.BitMachine.BinaryBranchProgram

end OAI
end

theorem solution : type_of% @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r_oai := @OAI.MetricKMedianRecovery.BitMachine.BinaryBranchProgram.favorable_literal_plan_s238r_oai
