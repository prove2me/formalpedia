-- Prove2me | solution 1 for OAI.BoundedTreewidthL1.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T16:18:42.0489+00:00
-- url     : https://prove2.me/submissions/00801182-1284-4ab4-956b-15735f1ef087

import Mathlib
import Definitions.Def_BoundedTreewidthL1

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
theorem dite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : ¬p) :
    (if hp : p then a hp else b hp) = b h := dif_neg h
/-- Mathlib's newer name for `measurable_pi_lambda` (with `f` implicit). -/
theorem Measurable.of_eval {δ ι : Type*} {π : ι → Type*} [MeasurableSpace δ]
    [∀ i, MeasurableSpace (π i)] {f : δ → ∀ i, π i}
    (h : ∀ i, Measurable fun a => f a i) : Measurable f := measurable_pi_lambda f h
alias Finset.prod_le_prod₀ := Finset.prod_le_prod
alias Finset.prod_le_one₀ := Finset.prod_le_one
alias Finset.one_le_prod₀ := Finset.one_le_prod
alias List.Nodup.getElem?_inj := List.getElem?_inj
end OAICompat434

universe u_1 treewidthLevel1 treewidthLevel2 treewidthLevel3 treewidthLevel4

section
section
namespace OAI

namespace BoundedTreewidthL1


variable {V : Type u_1} (G : SimpleGraph V)

end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1

section WeightedPaths

variable {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)

/-- Extension by zero, only used to write the sum over `Walk.edges`.
It does not add edges or change any graph-walk length. -/
noncomputable def edgeLength (e : Sym2 V) : ℝ := by
  classical
  exact if h : e ∈ G.edgeSet then ℓ ⟨e, h⟩ else 0

lemma edgeLength_of_mem {e : Sym2 V} (h : e ∈ G.edgeSet) :
    edgeLength G ℓ e = ℓ ⟨e, h⟩ := by
  simp [edgeLength, h]

lemma edgeLength_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (e : Sym2 V) :
    0 ≤ edgeLength G ℓ e := by
  unfold edgeLength
  split_ifs with h
  · exact hℓ _
  · exact le_rfl

lemma walkLength_eq_sum_edges {u v : V} (p : G.Walk u v) :
    walkLength G ℓ p = (p.edges.map (edgeLength G ℓ)).sum := by
  induction p with
  | nil => rfl
  | @cons u v w h p ih =>
    simp only [walkLength, SimpleGraph.Walk.edges_cons, List.map_cons, List.sum_cons, ih]
    rw [edgeLength_of_mem G ℓ (e := s(u, v)) h]

lemma walkLength_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) {u v : V} (p : G.Walk u v) :
    0 ≤ walkLength G ℓ p := by
  induction p with
  | nil => exact le_rfl
  | cons h p ih => exact add_nonneg (hℓ _) ih

lemma walkLength_pos (hℓ : ∀ e, 0 < ℓ e) {u v : V}
    (huv : u ≠ v) (p : G.Walk u v) : 0 < walkLength G ℓ p := by
  cases p with
  | nil => exact (huv rfl).elim
  | cons h p =>
    exact add_pos_of_pos_of_nonneg (hℓ _) (walkLength_nonneg G ℓ (fun e => (hℓ e).le) p)

lemma walkLength_append {u v w : V} (p : G.Walk u v) (q : G.Walk v w) :
    walkLength G ℓ (p.append q) = walkLength G ℓ p + walkLength G ℓ q := by
  simp only [walkLength_eq_sum_edges, SimpleGraph.Walk.edges_append,
    List.map_append, List.sum_append]

lemma walkLength_reverse {u v : V} (p : G.Walk u v) :
    walkLength G ℓ p.reverse = walkLength G ℓ p := by
  simp [walkLength_eq_sum_edges, SimpleGraph.Walk.edges_reverse]

lemma walkLength_bypass_le [DecidableEq V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) : walkLength G ℓ p.bypass ≤ walkLength G ℓ p := by
  rw [walkLength_eq_sum_edges, walkLength_eq_sum_edges]
  apply (p.edges_bypass_sublist_edges.map (edgeLength G ℓ)).sum_le_sum
  intro a ha
  obtain ⟨e, _, rfl⟩ := List.mem_map.mp ha
  exact edgeLength_nonneg G ℓ hℓ e

lemma path_length_set_finite [Fintype V] (u v : V) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Finite := by
  classical
  convert Set.finite_range (fun p : G.Path u v => walkLength G ℓ p.val) using 1
  ext r
  constructor
  · rintro ⟨p, hp, hr⟩
    exact ⟨⟨p, hp⟩, hr⟩
  · rintro ⟨p, hr⟩
    exact ⟨p.val, p.property, hr⟩

lemma path_length_set_nonempty (hG : G.Connected) (u v : V) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Nonempty := by
  obtain ⟨p, hp, _⟩ := hG.exists_path_of_dist u v
  exact ⟨walkLength G ℓ p, p, hp, rfl⟩

lemma shortestPathDistance_attained [Fintype V] (hG : G.Connected) (u v : V) :
    ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v :=
  (path_length_set_nonempty G ℓ hG u v).csInf_mem (path_length_set_finite G ℓ u v)

lemma shortestPathDistance_nonneg (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v : V) : 0 ≤ shortestPathDistance G ℓ u v := by
  apply le_csInf (path_length_set_nonempty G ℓ hG u v)
  rintro r ⟨p, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ p

lemma shortestPathDistance_le_pathLength (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) :
    shortestPathDistance G ℓ u v ≤ walkLength G ℓ p := by
  unfold shortestPathDistance
  refine csInf_le ?_ ⟨p, hp, rfl⟩
  refine ⟨0, ?_⟩
  rintro r ⟨q, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ q

lemma shortestPathDistance_le_walkLength (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (p : G.Walk u v) :
    shortestPathDistance G ℓ u v ≤ walkLength G ℓ p := by
  classical
  exact (shortestPathDistance_le_pathLength G ℓ hℓ p.bypass p.bypass_isPath).trans
    (walkLength_bypass_le G ℓ hℓ p)

lemma shortestPathDistance_self (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u : V) : shortestPathDistance G ℓ u u = 0 :=
  le_antisymm (shortestPathDistance_le_walkLength G ℓ hℓ .nil)
    (shortestPathDistance_nonneg G ℓ hG hℓ u u)

lemma shortestPathDistance_pos [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    {u v : V} (huv : u ≠ v) : 0 < shortestPathDistance G ℓ u v := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained G ℓ hG u v
  rw [← hp]
  exact walkLength_pos G ℓ hℓ huv p

lemma shortestPathDistance_comm [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v : V) : shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u := by
  have hd (a b : V) : shortestPathDistance G ℓ a b ≤ shortestPathDistance G ℓ b a := by
    obtain ⟨p, hp, heq⟩ := shortestPathDistance_attained G ℓ hG b a
    rw [← heq, ← walkLength_reverse G ℓ p]
    exact shortestPathDistance_le_pathLength G ℓ hℓ p.reverse hp.reverse
  exact le_antisymm (hd u v) (hd v u)

lemma shortestPathDistance_triangle [Fintype V] (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (u v w : V) : shortestPathDistance G ℓ u w ≤
      shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained G ℓ hG u v
  obtain ⟨q, _, hq⟩ := shortestPathDistance_attained G ℓ hG v w
  rw [← hp, ← hq, ← walkLength_append G ℓ p q]
  exact shortestPathDistance_le_walkLength G ℓ hℓ (p.append q)

theorem shortestPathDistance_metric [Fintype V] (hG : G.Connected)
    (hℓ : ∀ e, 0 < ℓ e) :
    (∀ u v, 0 ≤ shortestPathDistance G ℓ u v) ∧
    (∀ u, shortestPathDistance G ℓ u u = 0) ∧
    (∀ u v, shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u) ∧
    (∀ u v w, shortestPathDistance G ℓ u w ≤
      shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w) ∧
    (∀ u v, shortestPathDistance G ℓ u v = 0 → u = v) ∧
    (∀ u v, ∃ p : G.Walk u v,
      p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v) := by
  have hnonneg : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  refine ⟨shortestPathDistance_nonneg G ℓ hG hnonneg,
    shortestPathDistance_self G ℓ hG hnonneg,
    shortestPathDistance_comm G ℓ hG hnonneg,
    shortestPathDistance_triangle G ℓ hG hnonneg, ?_,
    shortestPathDistance_attained G ℓ hG⟩
  intro u v hzero
  by_contra huv
  have hpos := shortestPathDistance_pos G ℓ hG hℓ huv
  linarith

end WeightedPaths

end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal

variable {V : Type*} [Fintype V]

noncomputable def thresholdLabels (F : V → ℝ) (t : ℝ) : V → Bool :=
  fun v => decide (t < F v)

noncomputable def sweep (M : ℝ) (F : V → ℝ) : Measure (V → Bool) :=
  (volume.restrict (Icc (-M) M)).map (thresholdLabels F)

def complementCut (ω : V → Bool) : V → Bool := fun v => !(ω v)

noncomputable def symmetrizeCut (μ : Measure (V → Bool)) : Measure (V → Bool) :=
  (1 / 2 : ℝ≥0∞) • (μ + μ.map complementCut)

def cutEvent (P : Finset V) (z : V) (b : P → Bool) (q : Bool) : Set (V → Bool) :=
  {ω | (∀ s : P, ω s = b s) ∧ ω z = q}

noncomputable def cutUncertainty (μ : Measure (V → Bool)) (P : Finset V) (z : V) : ℝ := by
  classical
  exact ∑ b : P → Bool, min (μ.real (cutEvent P z b false)) (μ.real (cutEvent P z b true))

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma measurable_thresholdLabels
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) : Measurable (thresholdLabels F) := by
  apply Measurable.of_eval
  intro v
  have h : Measurable (fun t : ℝ => if t < F v then true else false) :=
    Measurable.ite (measurableSet_lt measurable_id measurable_const)
      measurable_const measurable_const
  convert h using 1
  ext t
  simp [thresholdLabels]

instance sweep_finite (M : ℝ) (F : V → ℝ) : IsFiniteMeasure (sweep M F) := by
  unfold sweep
  infer_instance

lemma cutEvent_measurable (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    MeasurableSet (cutEvent P z b q) := (Set.toFinite _).measurableSet

lemma measurable_complementCut : Measurable (complementCut (V := V)) :=
  measurable_of_finite _

instance symmetrizeCut_finite (μ : Measure (V → Bool)) [IsFiniteMeasure μ] :
    IsFiniteMeasure (symmetrizeCut μ) := by
  constructor
  change (1 / 2 : ℝ≥0∞) * (μ + μ.map complementCut) Set.univ < ⊤
  finiteness

lemma complementCut_involutive
    {V : Type treewidthLevel1} [Fintype V] : Function.Involutive (complementCut (V := V)) := by
  intro ω
  funext v
  simp [complementCut]

def complementEquiv (V : Type*) : (V → Bool) ≃ (V → Bool) where
  toFun := complementCut
  invFun := complementCut
  left_inv := by intro ω; funext v; simp [complementCut]
  right_inv := by intro ω; funext v; simp [complementCut]

lemma complement_preimage_event
    {V : Type treewidthLevel1} [Fintype V]
    (P : Finset V) (z : V) (b : P → Bool) (q : Bool) :
    complementCut ⁻¹' cutEvent P z b q =
      cutEvent P z (complementCut b) (!q) := by
  ext ω
  simp only [Set.mem_preimage, cutEvent, Set.mem_ofPred_eq, complementCut]
  constructor
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this
  · rintro ⟨h, hz⟩
    constructor
    · intro s
      have := congrArg Bool.not (h s)
      simpa using this
    · have := congrArg Bool.not hz
      simpa using this

lemma uncertainty_nonneg
    {V : Type treewidthLevel1} [Fintype V]
    (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    0 ≤ cutUncertainty μ P z :=
  Finset.sum_nonneg (fun _ _ => le_min measureReal_nonneg measureReal_nonneg)

lemma uncertainty_add
    {V : Type treewidthLevel1} [Fintype V]
    (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (P : Finset V) (z : V) :
    cutUncertainty μ P z + cutUncertainty ν P z ≤ cutUncertainty (μ + ν) P z := by
  classical
  simp only [cutUncertainty, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro b _
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  exact min_add_min_le_min_add_add

lemma uncertainty_complement (μ : Measure (V → Bool)) (P : Finset V) (z : V) :
    cutUncertainty (μ.map complementCut) P z = cutUncertainty μ P z := by
  classical
  simp only [cutUncertainty, map_measureReal_apply measurable_complementCut
    (cutEvent_measurable _ _ _ _), complement_preimage_event, Bool.not_false,
    Bool.not_true]
  simp_rw [min_comm]
  simpa only [complementEquiv, Equiv.coe_fn_mk] using (complementEquiv P).sum_comp
    (fun b : P → Bool => min (μ.real (cutEvent P z b false))
      (μ.real (cutEvent P z b true)))

lemma uncertainty_symmetrize (μ : Measure (V → Bool)) [IsFiniteMeasure μ]
    (P : Finset V) (z : V) :
    cutUncertainty μ P z ≤ cutUncertainty (symmetrizeCut μ) P z := by
  classical
  have h := uncertainty_add μ (μ.map complementCut) P z
  rw [uncertainty_complement] at h
  have heq : cutUncertainty (symmetrizeCut μ) P z =
      cutUncertainty (μ + μ.map complementCut) P z / 2 := by
    simp only [cutUncertainty, symmetrizeCut, measureReal_ennreal_smul_apply]
    norm_num
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    simp only [one_div_mul_eq_div, min_div_div_right (by norm_num : (0 : ℝ) ≤ 2)]
  rw [heq]
  linarith

lemma sweep_event (M : ℝ) (F : V → ℝ) (P : Finset V) (z : V)
    (b : P → Bool) (q : Bool) :
    (sweep M F).real (cutEvent P z b q) =
      volume.real ((thresholdLabels F ⁻¹' cutEvent P z b q) ∩ Icc (-M) M) := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) (cutEvent_measurable ..),
    measureReal_restrict_apply ((measurable_thresholdLabels F) (cutEvent_measurable ..))]

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma thresholdLabels_constant_gap
    {V : Type treewidthLevel1} [Fintype V]
    (F : V → ℝ) (z s : V) (t a : ℝ)
    (_ : 0 < t) (hs : t ≤ |F z - F s|)
    (ha : F z - t < a ∧ a < F z + t) :
    thresholdLabels F a s = thresholdLabels F (F z) s := by
  by_cases h : F z < F s
  · rw [abs_of_neg (sub_neg.mpr h)] at hs
    have h' : a < F s := by linarith
    simp [thresholdLabels, h, h']
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_gt h))] at hs
    have h' : ¬a < F s := by linarith
    simp [thresholdLabels, h, h']

lemma sweep_height_gap_unsymmetrized (M : ℝ) (F : V → ℝ) (P : Finset V)
    (z : V) (t : ℝ) (ht : 0 < t) (hm : -M ≤ F z - t ∧ F z + t ≤ M)
    (hgap : ∀ s ∈ P, t ≤ |F z - F s|) :
    t ≤ cutUncertainty (sweep M F) P z := by
  classical
  let b : P → Bool := fun s => thresholdLabels F (F z) s
  have hfinite (q : Bool) :
      volume ((thresholdLabels F ⁻¹' cutEvent P z b q) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hleft : Ioo (F z - t) (F z) ⊆
      (thresholdLabels F ⁻¹' cutEvent P z b true) ∩ Icc (-M) M := by
    rintro a ⟨hal, har⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      exact thresholdLabels_constant_gap F z s t a ht (hgap s s.property)
        ⟨hal, by linarith⟩
    · simp [thresholdLabels, har]
    · constructor <;> linarith [hm.1, hm.2]
  have hright : Ioo (F z) (F z + t) ⊆
      (thresholdLabels F ⁻¹' cutEvent P z b false) ∩ Icc (-M) M := by
    rintro a ⟨hal, har⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      exact thresholdLabels_constant_gap F z s t a ht (hgap s s.property)
        ⟨by linarith, har⟩
    · simp [thresholdLabels, show ¬a < F z by linarith]
    · constructor <;> linarith [hm.1, hm.2]
  have hl := measureReal_mono hleft (hfinite true)
  have hr := measureReal_mono hright (hfinite false)
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hl
  rw [Real.volume_real_Ioo_of_le (by linarith)] at hr
  rw [← sweep_event] at hl hr
  have hmin : t ≤ min ((sweep M F).real (cutEvent P z b false))
      ((sweep M F).real (cutEvent P z b true)) := by
    apply le_min <;> linarith
  exact hmin.trans (Finset.single_le_sum
    (f := fun b : P → Bool => min ((sweep M F).real (cutEvent P z b false))
      ((sweep M F).real (cutEvent P z b true)))
    (fun _ _ => le_min measureReal_nonneg measureReal_nonneg) (Finset.mem_univ b))

theorem sweep_height_gap (M : ℝ) (F : V → ℝ) (P : Finset V) (z : V) (t : ℝ)
    (ht : 0 < t) (hm : -M ≤ F z - t ∧ F z + t ≤ M)
    (hgap : ∀ s ∈ P, t ≤ |F z - F s|) :
    t ≤ cutUncertainty (symmetrizeCut (sweep M F)) P z :=
  (sweep_height_gap_unsymmetrized M F P z t ht hm hgap).trans
    (uncertainty_symmetrize (sweep M F) P z)

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma symmetrizeCut_add (μ ν : Measure (V → Bool)) :
    symmetrizeCut (μ + ν) = symmetrizeCut μ + symmetrizeCut ν := by
  simp only [symmetrizeCut, Measure.map_add _ _ measurable_complementCut, smul_add]
  ac_rfl

lemma sweep_pair_gap_ordered (M : ℝ) (F H : V → ℝ) (A : Finset V) (z : V)
    (hA : ∀ s ∈ A, F s = H s) (horder : F z ≤ H z)
    (hm : -M ≤ F z ∧ H z ≤ M) :
    H z - F z ≤ cutUncertainty (sweep M F + sweep M H) A z := by
  classical
  let E (b : A → Bool) : Set ℝ := Ioo (F z) (H z) ∩
    thresholdLabels F ⁻¹' {ω | ∀ s : A, ω s = b s}
  have hEm (b : A → Bool) : MeasurableSet (E b) :=
    measurableSet_Ioo.inter
      ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)
  have hEF (b : A → Bool) : E b ⊆
      (thresholdLabels F ⁻¹' cutEvent A z b false) ∩ Icc (-M) M := by
    rintro a ⟨⟨hal, har⟩, hb⟩
    refine ⟨⟨hb, ?_⟩, ?_⟩
    · simp [thresholdLabels, show ¬a < F z by linarith]
    · constructor <;> linarith [hm.1, hm.2]
  have hEH (b : A → Bool) : E b ⊆
      (thresholdLabels H ⁻¹' cutEvent A z b true) ∩ Icc (-M) M := by
    rintro a ⟨⟨hal, har⟩, hb⟩
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro s
      change decide (a < H s) = b s
      rw [← hA s s.property]
      exact hb s
    · simp [thresholdLabels, har]
    · constructor <;> linarith [hm.1, hm.2]
  have hfinF (b : A → Bool) : volume
      ((thresholdLabels F ⁻¹' cutEvent A z b false) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hfinH (b : A → Bool) : volume
      ((thresholdLabels H ⁻¹' cutEvent A z b true) ∩ Icc (-M) M) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_right (by rw [Real.volume_Icc]; finiteness)
  have hfinE (b : A → Bool) : volume (E b) ≠ ⊤ :=
    measure_ne_top_of_subset (hEF b) (hfinF b)
  have hdis : Pairwise (Function.onFun Disjoint E) := by
    intro b c hbc
    apply Set.disjoint_left.mpr
    intro a hb hc
    apply hbc
    funext s
    exact (hb.2 s).symm.trans (hc.2 s)
  have hcover : (⋃ b : A → Bool, E b) = Ioo (F z) (H z) := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb⟩ := Set.mem_iUnion.mp ha
      exact hb.1
    · intro ha
      exact Set.mem_iUnion.mpr ⟨fun s => thresholdLabels F a s, ha, fun _ => rfl⟩
  have hsum := measureReal_iUnion_fintype hdis hEm hfinE
  rw [hcover, Real.volume_real_Ioo_of_le horder] at hsum
  rw [hsum, cutUncertainty]
  apply Finset.sum_le_sum
  intro b _
  have hF := measureReal_mono (hEF b) (hfinF b)
  have hH := measureReal_mono (hEH b) (hfinH b)
  rw [← sweep_event] at hF hH
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  apply le_min
  · exact hF.trans (le_add_of_nonneg_right measureReal_nonneg)
  · exact hH.trans (le_add_of_nonneg_left measureReal_nonneg)

theorem sweep_launch_gap (M : ℝ) (f g : V → ℝ) (A : Finset V)
    (hg : ∀ s ∈ A, g s = 0)
    (hm : ∀ v, |f v + g v| ≤ M ∧ |f v - g v| ≤ M) (z : V) :
    2 * |g z| ≤ cutUncertainty
      (symmetrizeCut (sweep M (fun v => f v + g v)) +
       symmetrizeCut (sweep M (fun v => f v - g v))) A z := by
  classical
  rw [← symmetrizeCut_add]
  apply le_trans _ (uncertainty_symmetrize _ A z)
  have hA : ∀ s ∈ A, f s - g s = f s + g s := by
    intro s hs
    rw [hg s hs]
    ring
  rcases le_total 0 (g z) with h | h
  · have hgap := sweep_pair_gap_ordered M (fun v => f v - g v)
      (fun v => f v + g v) A z hA (by linarith)
      ⟨(abs_le.mp (hm z).2).1, (abs_le.mp (hm z).1).2⟩
    calc
      2 * |g z| = (f z + g z) - (f z - g z) := by rw [abs_of_nonneg h]; ring
      _ ≤ _ := by
        rw [add_comm (sweep M (fun v => f v + g v))
          (sweep M (fun v => f v - g v))]
        exact hgap
  · have hgap := sweep_pair_gap_ordered M (fun v => f v + g v)
      (fun v => f v - g v) A z (fun s hs => (hA s hs).symm) (by linarith)
      ⟨(abs_le.mp (hm z).1).1, (abs_le.mp (hm z).2).2⟩
    calc
      2 * |g z| = (f z - g z) - (f z + g z) := by rw [abs_of_nonpos h]; ring
      _ ≤ _ := hgap

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

noncomputable def cutTrace (μ : Measure (V → Bool)) (P : Finset V) : Measure (P → Bool) :=
  μ.map (fun ω s => ω s)

noncomputable def cutSeparation (μ : Measure (V → Bool)) (u v : V) : ℝ :=
  μ.real {ω | ω u ≠ ω v}

def CommonWeakOrder (P : Finset V) (F H : V → ℝ) : Prop :=
  ∃ e : Fin P.card ≃ P,
    Monotone (fun i => F (e i)) ∧ Monotone (fun i => H (e i))

def partialCutEvent (P Q : Finset V) : Set (V → Bool) :=
  {ω | (∀ p ∈ P, ω p = true) ∧ ∀ q ∈ Q, ω q = false}

/-- On a finite Boolean cube, all-true conjunctions determine a finite measure.
The proof retains the total mass (the conjunction over the empty set). -/
lemma cutMeasure_ext_all_true (μ ν : Measure (V → Bool)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν]
    (heq : ∀ P : Finset V, μ.real {ω | ∀ p ∈ P, ω p = true} =
      ν.real {ω | ∀ p ∈ P, ω p = true}) : μ = ν := by
  classical
  have hpartial (Q : Finset V) : ∀ P : Finset V,
      μ.real (partialCutEvent P Q) = ν.real (partialCutEvent P Q) := by
    induction Q using Finset.induction_on with
    | empty =>
      intro P
      simpa [partialCutEvent] using heq P
    | @insert a Q ha ih =>
      intro P
      have hpart : partialCutEvent P Q =
          partialCutEvent (insert a P) Q ∪ partialCutEvent P (insert a Q) := by
        ext ω
        simp only [partialCutEvent, Set.mem_ofPred_eq, Finset.mem_insert,
          forall_eq_or_imp, Set.mem_union]
        cases h : ω a <;> simp
      have hdis : Disjoint (partialCutEvent (insert a P) Q)
          (partialCutEvent P (insert a Q)) := by
        apply Set.disjoint_left.mpr
        intro ω h₁ h₂
        have ht := h₁.1 a (Finset.mem_insert_self a P)
        have hf := h₂.2 a (Finset.mem_insert_self a Q)
        simp_all
      have hμ := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := μ)
      have hν := measureReal_union hdis
        (Set.toFinite (partialCutEvent P (insert a Q))).measurableSet
        (μ := ν)
      rw [← hpart] at hμ hν
      linarith [ih P, ih (insert a P)]
  apply Measure.ext_of_singleton
  intro ω
  have hs : ({ω} : Set (V → Bool)) = partialCutEvent
      (Finset.univ.filter fun v => ω v = true)
      (Finset.univ.filter fun v => ω v = false) := by
    ext η
    simp only [Set.mem_singleton_iff, partialCutEvent, Set.mem_ofPred_eq,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro rfl
      exact ⟨fun _ h => h, fun _ h => h⟩
    · rintro ⟨h₁, h₂⟩
      funext v
      cases h : ω v
      · exact h₂ v h
      · exact h₁ v h
  apply (measureReal_eq_measureReal_iff (by finiteness) (by finiteness)).mp
  rw [hs]
  exact hpartial _ _

lemma sweep_all_true_of_min (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a : V) (ha : a ∈ P) (hmin : ∀ p ∈ P, F a ≤ F p)
    (hm : -M ≤ F a ∧ F a ≤ M) :
    (sweep M F).real {ω | ∀ p ∈ P, ω p = true} = F a + M := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F)
    (Set.toFinite _).measurableSet,
    measureReal_restrict_apply ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)]
  have hset : (thresholdLabels F ⁻¹' {ω | ∀ p ∈ P, ω p = true}) ∩ Icc (-M) M =
      Ico (-M) (F a) := by
    ext t
    constructor
    · rintro ⟨h, hM⟩
      exact ⟨hM.1, of_decide_eq_true (h a ha)⟩
    · rintro ⟨hl, hr⟩
      refine ⟨?_, ⟨hl, le_trans hr.le hm.2⟩⟩
      intro p hp
      exact decide_eq_true (hr.trans_le (hmin p hp))
  rw [hset, Real.volume_real_Ico_of_le hm.1]
  ring

lemma sweep_total_mass (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    (sweep M F).real Set.univ = 2 * M := by
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) MeasurableSet.univ]
  simp only [Set.preimage_univ, measureReal_restrict_apply_univ]
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
variable {V : Type*} [Fintype V]

lemma sweep_affine_of_common_min (M : ℝ) (hM : 0 ≤ M) (F H : V → ℝ)
    (hF : ∀ v, |F v| ≤ M) (hH : ∀ v, |H v| ≤ M)
    (hmin : ∀ P : Finset V, P.Nonempty →
      ∃ a ∈ P, ∀ p ∈ P, F a ≤ F p ∧ H a ≤ H p) :
    sweep M F + sweep M H =
      sweep M (fun v => (F v + H v) / 2) + sweep M (fun v => (F v + H v) / 2) := by
  classical
  apply cutMeasure_ext_all_true
  intro P
  rw [measureReal_add_apply (by finiteness) (by finiteness),
    measureReal_add_apply (by finiteness) (by finiteness)]
  by_cases hP : P.Nonempty
  · obtain ⟨a, ha, ham⟩ := hmin P hP
    have haF := abs_le.mp (hF a)
    have haH := abs_le.mp (hH a)
    rw [sweep_all_true_of_min M F P a ha (fun p hp => (ham p hp).1) haF,
      sweep_all_true_of_min M H P a ha (fun p hp => (ham p hp).2) haH,
      sweep_all_true_of_min M (fun v => (F v + H v) / 2) P a ha
        (by intro p hp; linarith [(ham p hp).1, (ham p hp).2])
        (by constructor <;> linarith)]
    ring
  · have hPe : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hP
    have hevent : {ω : V → Bool | ∀ p ∈ (∅ : Finset V), ω p = true} = univ := by
      ext ω
      simp
    rw [hPe, hevent, sweep_total_mass M hM, sweep_total_mass M hM, sweep_total_mass M hM]

lemma cutTrace_add (μ ν : Measure (V → Bool)) (P : Finset V) :
    cutTrace (μ + ν) P = cutTrace μ P + cutTrace ν P := by
  exact Measure.map_add _ _ (measurable_of_finite _)

lemma cutTrace_sweep (M : ℝ) (F : V → ℝ) (P : Finset V) :
    cutTrace (sweep M F) P = sweep M (fun p : P => F p) := by
  rw [cutTrace, sweep, Measure.map_map (measurable_of_finite _) (measurable_thresholdLabels F)]
  rfl

theorem sweep_trace_update (M : ℝ) (hM : 0 < M) (F H g : V → ℝ) (P : Finset V)
    (horder : CommonWeakOrder P F H) (hg : ∀ s ∈ P, g s = 0)
    (hF : ∀ v, |F v| ≤ M) (hH : ∀ v, |H v| ≤ M)
    (_ : ∀ v, |(F v + H v) / 2 + g v| ≤ M)
    (_ : ∀ v, |(F v + H v) / 2 - g v| ≤ M) :
    cutTrace (sweep M F + sweep M H) P =
      cutTrace (sweep M (fun v => (F v + H v) / 2 + g v) +
        sweep M (fun v => (F v + H v) / 2 - g v)) P := by
  classical
  simp only [cutTrace_add, cutTrace_sweep]
  have hp' : (fun p : P => (F p + H p) / 2 + g p) =
      (fun p : P => (F p + H p) / 2) := by
    funext p
    rw [hg p p.property, add_zero]
  have hn' : (fun p : P => (F p + H p) / 2 - g p) =
      (fun p : P => (F p + H p) / 2) := by
    funext p
    rw [hg p p.property, sub_zero]
  rw [hp', hn']
  apply sweep_affine_of_common_min M hM.le (fun p : P => F p) (fun p : P => H p)
    (fun p => hF p) (fun p => hH p)
  intro S hS
  obtain ⟨e, heF, heH⟩ := horder
  obtain ⟨a, ha, hmina⟩ := Finset.exists_min_image S (fun p => e.symm p) hS
  refine ⟨a, ha, ?_⟩
  intro p hp
  simpa only [Equiv.apply_symm_apply] using
    And.intro (heF (hmina p hp)) (heH (hmina p hp))

lemma sweep_separation_ordered (M : ℝ) (F : V → ℝ) (u v : V)
    (h : F u ≤ F v) (hm : -M ≤ F u ∧ F v ≤ M) :
    cutSeparation (sweep M F) u v = F v - F u := by
  rw [cutSeparation, sweep, map_measureReal_apply (measurable_thresholdLabels F)
    (Set.toFinite _).measurableSet,
    measureReal_restrict_apply ((measurable_thresholdLabels F) (Set.toFinite _).measurableSet)]
  have hset : (thresholdLabels F ⁻¹' {ω | ω u ≠ ω v}) ∩ Icc (-M) M =
      Ico (F u) (F v) := by
    ext t
    constructor
    · rintro ⟨hne, _⟩
      by_cases hu : t < F u
      · have hv : t < F v := hu.trans_le h
        simp [thresholdLabels, hu, hv] at hne
      · have hv : t < F v := by
          by_contra hv
          simp [thresholdLabels, hu, hv] at hne
        exact ⟨le_of_not_gt hu, hv⟩
    · rintro ⟨hu, hv⟩
      refine ⟨?_, ⟨hm.1.trans hu, hv.le.trans hm.2⟩⟩
      simp [thresholdLabels, show ¬t < F u from not_lt.mpr hu, hv]
  rw [hset, Real.volume_real_Ico_of_le h]

theorem sweep_separation (M : ℝ) (F : V → ℝ) (hF : ∀ v, |F v| ≤ M) (u v : V) :
    cutSeparation (sweep M F) u v = |F u - F v| := by
  rcases le_total (F u) (F v) with h | h
  · rw [sweep_separation_ordered M F u v h
      ⟨(abs_le.mp (hF u)).1, (abs_le.mp (hF v)).2⟩,
      abs_of_nonpos (sub_nonpos.mpr h)]
    ring
  · have he : cutSeparation (sweep M F) u v = cutSeparation (sweep M F) v u := by
      unfold cutSeparation
      congr 1
      ext ω
      exact ne_comm
    rw [he, sweep_separation_ordered M F v u h
      ⟨(abs_le.mp (hF v)).1, (abs_le.mp (hF u)).2⟩,
      abs_of_nonneg (sub_nonneg.mpr h)]

end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1

section ParticleInvariant

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def pairUpdate (a : ι → ℝ) (i j : ι) (e : ℝ) (x : ι) : ℝ :=
  a x + (if x = i then (a i + a j) / 2 + e - a i else 0) +
    (if x = j then (a i + a j) / 2 - e - a j else 0)

/-- Finite update histories; there is no bound on the number of updates. -/
inductive ParticleReachable : (ι → ℝ) → Prop
  | zero : ParticleReachable (fun _ => 0)
  | step {a : ι → ℝ} (ha : ParticleReachable a)
      (i j : ι) (hij : i ≠ j) (e : ℝ) (he : |e| ≤ 1) :
      ParticleReachable (pairUpdate a i j e)

/-- The quadratic subset-sum invariant controlling particle bounds.
Subtractions are real. In particular the bound at the full set is exactly zero. -/
def ParticleInvariant (a : ι → ℝ) : Prop :=
  (∑ i, a i) = 0 ∧ ∀ I : Finset ι,
    (∑ i ∈ I, a i) ≤ (I.card : ℝ) * ((Fintype.card ι : ℝ) - I.card)

end ParticleInvariant

end BoundedTreewidthL1

namespace BoundedTreewidthL1

section ParticleInvariantProof

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma sum_pairUpdate
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (i j : ι) (e : ℝ) (I : Finset ι) :
    (∑ x ∈ I, pairUpdate a i j e x) =
      (∑ x ∈ I, a x) +
        (if i ∈ I then (a i + a j) / 2 + e - a i else 0) +
        (if j ∈ I then (a i + a j) / 2 - e - a j else 0) := by
  simp [pairUpdate, Finset.sum_add_distrib]

lemma pairUpdate_swap
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι]
    (a : ι → ℝ) (i j : ι) (e : ℝ) :
    pairUpdate a i j e = pairUpdate a j i (-e) := by
  funext x
  simp only [pairUpdate]
  split_ifs <;> ring

lemma ParticleInvariant.zero
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] : ParticleInvariant (fun _ : ι => 0) := by
  constructor
  · simp
  · intro I
    simp only [Finset.sum_const_zero]
    exact mul_nonneg (Nat.cast_nonneg _)
      (sub_nonneg.mpr (by exact_mod_cast Finset.card_le_univ I))

lemma ParticleInvariant.update_one {a : ι → ℝ} (ha : ParticleInvariant a)
    (i j : ι) (e : ℝ) (he : e ≤ 1) (I : Finset ι)
    (hi : i ∈ I) (hj : j ∉ I) :
    (∑ x ∈ I, pairUpdate a i j e x) ≤
      (I.card : ℝ) * ((Fintype.card ι : ℝ) - I.card) := by
  have hsmall := ha.2 (I.erase i)
  have hlarge := ha.2 (insert j I)
  have hsumsmall := Finset.sum_erase_add I a hi
  have hsumlarge := Finset.sum_insert (f := a) hj
  have hcsmall : ((I.erase i).card : ℝ) = (I.card : ℝ) - 1 := by
    have hc := Finset.card_erase_add_one hi
    have hcast : ((I.erase i).card : ℝ) + 1 = (I.card : ℝ) := by exact_mod_cast hc
    linarith
  have hclarge : ((insert j I).card : ℝ) = (I.card : ℝ) + 1 := by
    rw [Finset.card_insert_of_notMem hj]
    norm_cast
  rw [hcsmall] at hsmall
  rw [hclarge] at hlarge
  rw [sum_pairUpdate, ite_eq_left hi, ite_eq_right hj]
  nlinarith

lemma ParticleInvariant.update {a : ι → ℝ} (ha : ParticleInvariant a)
    (i j : ι) (_ : i ≠ j) (e : ℝ) (he : |e| ≤ 1) :
    ParticleInvariant (pairUpdate a i j e) := by
  constructor
  · rw [sum_pairUpdate]
    simp only [Finset.mem_univ, ↓reduceIte, ha.1]
    ring
  · intro I
    by_cases hi : i ∈ I
    · by_cases hj : j ∈ I
      · rw [sum_pairUpdate, ite_eq_left hi, ite_eq_left hj]
        have hI := ha.2 I
        linarith
      · exact ha.update_one i j e (abs_le.mp he).2 I hi hj
    · by_cases hj : j ∈ I
      · rw [pairUpdate_swap]
        exact ha.update_one j i (-e) (by have := (abs_le.mp he).1; linarith) I hj hi
      · simpa [sum_pairUpdate, hi, hj] using ha.2 I

theorem particle_reachable_invariant {a : ι → ℝ} (ha : ParticleReachable a) :
    ParticleInvariant a := by
  induction ha with
  | zero => exact ParticleInvariant.zero
  | step ha i j hij e he ih => exact ih.update i j hij e he

/-- Exact scalar bound used for the slopes AND absolute heights of particles. -/
theorem particle_reachable_abs_le {a : ι → ℝ} (ha : ParticleReachable a) (i : ι) :
    |a i| ≤ (Fintype.card ι : ℝ) - 1 := by
  have h := particle_reachable_invariant ha
  have hi := h.2 {i}
  have hc := h.2 (Finset.univ.erase i)
  have hsum := Finset.sum_erase_add Finset.univ a (Finset.mem_univ i)
  have hcard : ((Finset.univ.erase i).card : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have ht := Finset.card_erase_add_one (Finset.mem_univ i)
    simp only [Finset.card_univ] at ht
    have hcast : ((Finset.univ.erase i).card : ℝ) + 1 = (Fintype.card ι : ℝ) := by
      exact_mod_cast ht
    linarith
  simp only [Finset.sum_singleton, Finset.card_singleton, Nat.cast_one, one_mul] at hi
  rw [hcard] at hc
  rw [h.1] at hsum
  exact abs_le.mpr ⟨by nlinarith, hi⟩

end ParticleInvariantProof

end BoundedTreewidthL1

namespace BoundedTreewidthL1

section FunctionParticles

variable {ι V : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def functionPairUpdate (F : ι → V → ℝ) (i j : ι) (g : V → ℝ) :
    ι → V → ℝ :=
  fun x v => pairUpdate (fun t => F t v) i j (g v) x

inductive FunctionParticleReachable (d : V → V → ℝ) (L H : ℝ) :
    (ι → V → ℝ) → Prop
  | zero : FunctionParticleReachable d L H (fun _ _ => 0)
  | step {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
      (i j : ι) (hij : i ≠ j) (g : V → ℝ)
      (hLip : ∀ u v, |g u - g v| ≤ L * d u v)
      (hHeight : ∀ v, |g v| ≤ H) :
      FunctionParticleReachable d L H (functionPairUpdate F i j g)

lemma functionPairUpdate_left
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g i v = (F i v + F j v) / 2 + g v := by
  simp [functionPairUpdate, pairUpdate, hij]

lemma functionPairUpdate_right
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g j v = (F i v + F j v) / 2 - g v := by
  simp [functionPairUpdate, pairUpdate, Ne.symm hij]

lemma functionPairUpdate_other
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j x : ι)
    (hxi : x ≠ i) (hxj : x ≠ j) (g : V → ℝ) (v : V) :
    functionPairUpdate F i j g x v = F x v := by
  simp [functionPairUpdate, pairUpdate, hxi, hxj]

lemma functionPairUpdate_value_normalized
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι)
    (g : V → ℝ) (v : V) (R : ℝ) :
    (fun x => functionPairUpdate F i j g x v / R) =
      pairUpdate (fun x => F x v / R) i j (g v / R) := by
  funext x
  simp only [functionPairUpdate, pairUpdate]
  split_ifs <;> ring

lemma functionPairUpdate_difference_normalized
    {ι : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype ι] [DecidableEq ι]
    (F : ι → V → ℝ) (i j : ι)
    (g : V → ℝ) (u v : V) (R : ℝ) :
    (fun x => (functionPairUpdate F i j g x u -
      functionPairUpdate F i j g x v) / R) =
      pairUpdate (fun x => (F x u - F x v) / R) i j ((g u - g v) / R) := by
  funext x
  simp only [functionPairUpdate, pairUpdate]
  split_ifs <;> ring

lemma function_particles_normalized_values {d : V → V → ℝ} {L H : ℝ}
    (hH : 0 < H) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (v : V) : ParticleReachable (fun x => F x v / H) := by
  induction hF with
  | zero => simpa using (ParticleReachable.zero (ι := ι))
  | step hF i j hij g hLip hHeight ih =>
    rw [functionPairUpdate_value_normalized]
    apply ParticleReachable.step ih i j hij
    rw [abs_div, abs_of_pos hH]
    exact (div_le_one hH).mpr (hHeight v)

lemma function_particles_normalized_differences {d : V → V → ℝ} {L H : ℝ}
    {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (u v : V) (hR : 0 < L * d u v) :
    ParticleReachable (fun x => (F x u - F x v) / (L * d u v)) := by
  induction hF with
  | zero => simpa using (ParticleReachable.zero (ι := ι))
  | step hF i j hij g hLip hHeight ih =>
    rw [functionPairUpdate_difference_normalized]
    apply ParticleReachable.step ih i j hij
    rw [abs_div, abs_of_pos hR]
    exact (div_le_one hR).mpr (hLip u v)

theorem function_particles_height_bound {d : V → V → ℝ} {L H : ℝ}
    (hH : 0 < H) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (i : ι) (v : V) : |F i v| ≤ H * ((Fintype.card ι : ℝ) - 1) := by
  have hb := particle_reachable_abs_le (function_particles_normalized_values hH hF v) i
  rw [abs_div, abs_of_pos hH] at hb
  simpa [mul_comm] using (div_le_iff₀ hH).mp hb

theorem function_particles_difference_bound {d : V → V → ℝ} {L H : ℝ}
    (hL : 0 < L) {F : ι → V → ℝ} (hF : FunctionParticleReachable d L H F)
    (i : ι) (u v : V) (hd : 0 < d u v) :
    |F i u - F i v| ≤ L * ((Fintype.card ι : ℝ) - 1) * d u v := by
  have hR := mul_pos hL hd
  have hb := particle_reachable_abs_le (function_particles_normalized_differences hF u v hR) i
  rw [abs_div, abs_of_pos hR] at hb
  simpa [mul_assoc, mul_comm, mul_left_comm] using (div_le_iff₀ hR).mp hb

theorem function_particles_metric_bound [MetricSpace V] {L H : ℝ}
    (hL : 0 < L) {F : ι → V → ℝ} (hF : FunctionParticleReachable dist L H F)
    (i : ι) (u v : V) :
    |F i u - F i v| ≤ L * ((Fintype.card ι : ℝ) - 1) * dist u v := by
  by_cases huv : u = v
  · simp [huv]
  · exact function_particles_difference_bound hL hF i u v (dist_pos.mpr huv)

end FunctionParticles

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open MeasureTheory
open scoped ENNReal
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι]

/-- The exact zero-error combined symmetric trace carried by a particle list. -/
noncomputable def particleTrace (M : ℝ) (F : ι → V → ℝ) (P : Finset V) :
    Measure (P → Bool) := ∑ i, cutTrace (symmetrizeCut (sweep M (F i))) P

/-- Any reservation set of size at most `2q`
leaves two particles with a common weak order, and the actual affine update
preserves the complete bag law and every reserved function. The pair is chosen
before the perturbation; the universal quantifier on g expresses that fact. -/
lemma exists_weak_order
    {V : Type treewidthLevel1} [Fintype V]
    (P : Finset V) (F : V → ℝ) :
    ∃ e : Fin P.card ≃ P, Monotone (fun i => F (e i)) := by
  classical
  let code := Fintype.equivFin P
  let enc : P → Lex (ℝ × Fin (Fintype.card P)) := fun p => toLex (F p, code p)
  have hinj : Function.Injective enc := by
    intro p q h
    exact code.injective (congrArg (fun z : Lex (ℝ × Fin (Fintype.card P)) => (ofLex z).2) h)
  let : LinearOrder P := LinearOrder.lift' enc hinj
  let e := Fintype.orderIsoFinOfCardEq P (by simp : Fintype.card P = P.card)
  refine ⟨e.toEquiv, ?_⟩
  intro i j hij
  have h := e.monotone hij
  change enc (e i) ≤ enc (e j) at h
  rcases Prod.Lex.le_iff.mp h with h | ⟨h, _⟩
  · exact h.le
  · exact h.le

lemma free_common_order (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (R : Finset ι) (hR : R.card ≤ 2*q)
    (F : ι → V → ℝ) :
    ∃ i j : ι, i ∉ R ∧ j ∉ R ∧ i ≠ j ∧ CommonWeakOrder P (F i) (F j) := by
  classical
  let S := Finset.univ \ R
  have hc : k.factorial < S.card := by
    have hs : S.card + R.card = Fintype.card ι := by
      simpa [S] using Finset.card_sdiff_add_card_inter Finset.univ R
    omega
  choose order horder using fun i : S => exists_weak_order P (F i)
  have hcard : Fintype.card (Fin P.card ≃ P) < Fintype.card S := by
    rw [Fintype.card_equiv (Fintype.equivOfCardEq (by simp) : Fin P.card ≃ P)]
    simpa using (Nat.factorial_le hP).trans_lt hc
  obtain ⟨i, j, hij, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt order hcard
  refine ⟨i, j, (Finset.mem_sdiff.mp i.property).2,
    (Finset.mem_sdiff.mp j.property).2, ?_, order i, horder i, ?_⟩
  · exact fun h => hij (Subtype.ext h)
  · rw [heq]
    exact horder j

lemma cutTrace_symmetrize (μ : Measure (V → Bool)) (P : Finset V) :
    cutTrace (symmetrizeCut μ) P = symmetrizeCut (cutTrace μ P) := by
  classical
  unfold cutTrace symmetrizeCut
  rw [Measure.map_smul, Measure.map_add _ _ (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) measurable_complementCut,
    Measure.map_map measurable_complementCut (measurable_of_finite _)]
  rfl

lemma symmetrize_add (μ ν : Measure (V → Bool)) :
    symmetrizeCut (μ + ν) = symmetrizeCut μ + symmetrizeCut ν := by
  unfold symmetrizeCut
  rw [Measure.map_add _ _ measurable_complementCut]
  simp [smul_add, add_assoc, add_left_comm]

lemma sum_eq_of_pair {A : Type*} [AddCommMonoid A] (a b : ι → A)
    (i j : ι) (hij : i ≠ j) (hpair : a i + a j = b i + b j)
    (hother : ∀ r, r ≠ i → r ≠ j → a r = b r) : (∑ r, a r) = ∑ r, b r := by
  classical
  let S : Finset ι := {i,j}
  have hs : (∑ r ∈ S, a r) = ∑ r ∈ S, b r := by
    simpa [S, hij] using hpair
  have ht : (∑ r ∈ Sᶜ, a r) = ∑ r ∈ Sᶜ, b r := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r ≠ i ∧ r ≠ j := by simpa [S] using hr
    exact hother r hr'.1 hr'.2
  rw [← Finset.sum_add_sum_compl S a, ←Finset.sum_add_sum_compl S b, hs, ht]

lemma particleTrace_update (M : ℝ) (hM : 0 < M) (F : ι → V → ℝ)
    (i j : ι) (hij : i ≠ j) (g : V → ℝ) (P : Finset V)
    (horder : CommonWeakOrder P (F i) (F j)) (hg : ∀ s ∈ P, g s = 0)
    (hF : ∀ r v, |F r v| ≤ M)
    (hF' : ∀ r v, |functionPairUpdate F i j g r v| ≤ M) :
    particleTrace M F P = particleTrace M (functionPairUpdate F i j g) P := by
  apply sum_eq_of_pair _ _ i j hij
  · simp only [cutTrace_symmetrize, ←symmetrize_add, ←cutTrace_add]
    apply congrArg symmetrizeCut
    have hi : functionPairUpdate F i j g i = fun v => (F i v + F j v)/2 + g v := by
      funext v; exact functionPairUpdate_left F i j hij g v
    have hj : functionPairUpdate F i j g j = fun v => (F i v + F j v)/2 - g v := by
      funext v; exact functionPairUpdate_right F i j hij g v
    rw [hi, hj]
    exact sweep_trace_update M hM (F i) (F j) g P horder hg (hF i) (hF j)
      (by simpa only [hi] using hF' i) (by simpa only [hj] using hF' j)
  · intro r hri hrj
    have hr : functionPairUpdate F i j g r = F r := by
      funext v; exact functionPairUpdate_other F i j r hri hrj g v
    rw [hr]

theorem particle_step_realization (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (R : Finset ι) (hR : R.card ≤ 2*q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (F : ι → V → ℝ) (hF : FunctionParticleReachable d L H F) :
    ∃ i j : ι, i ∉ R ∧ j ∉ R ∧ i ≠ j ∧ CommonWeakOrder P (F i) (F j) ∧
      ∀ g : V → ℝ, (∀ u v, |g u - g v| ≤ L * d u v) →
        (∀ v, |g v| ≤ H) → (∀ s ∈ P, g s = 0) →
        let F' := functionPairUpdate F i j g
        let M := H * ((Fintype.card ι : ℝ)-1) + 2*Δ
        FunctionParticleReachable d L H F' ∧
        (∀ r ∈ R, F' r = F r) ∧
        particleTrace M F P = particleTrace M F' P ∧
        (∀ r v, |F' r v| + 2*Δ ≤ M) := by
  classical
  obtain ⟨i, j, hi, hj, hij, ho⟩ := free_common_order k q hN P hP R hR F
  refine ⟨i, j, hi, hj, hij, ho, ?_⟩
  intro g hLip hHeight hg
  dsimp only
  have hF' := FunctionParticleReachable.step hF i j hij g hLip hHeight
  have hmarg : ∀ r v, |functionPairUpdate F i j g r v| + 2*Δ ≤
      H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
    intro r v
    have := function_particles_height_bound hH hF' r v
    linarith
  refine ⟨hF', ?_, ?_, hmarg⟩
  · intro r hr
    funext v
    exact functionPairUpdate_other F i j r (fun h => hi (h ▸ hr))
      (fun h => hj (h ▸ hr)) g v
  · have hcard : (1 : ℝ) ≤ Fintype.card ι := by
      have hn : 1 ≤ Fintype.card ι := by omega
      exact_mod_cast hn
    have hM : 0 < H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      have := mul_nonneg hH.le (sub_nonneg.mpr hcard)
      linarith
    apply particleTrace_update _ hM F i j hij g P ho hg
    · intro r v
      have := function_particles_height_bound hH hF r v
      linarith
    · intro r v
      have := function_particles_height_bound hH hF' r v
      linarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1

structure ReservationPath where
  last : ℕ
  finish : ℕ → ℕ
  launch_le_finish : ∀ a, a ≤ last → a ≤ finish a
  finish_le_last : ∀ a, a ≤ last → finish a ≤ last
  one_release : ∀ a b t, a ≤ t → b ≤ t → t < last →
    finish a = t → finish b = t → a = b
  root_permanent : finish 0 = last
namespace ReservationPath
noncomputable def inclusive (P : ReservationPath) (t : ℕ) : Finset ℕ := by
  classical
  exact if t ≤ P.last then (Finset.range (t + 1)).filter (fun a => t ≤ P.finish a) else ∅
end ReservationPath
end BoundedTreewidthL1

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable def before (R : ReservationPath) (t : ℕ) : Finset ℕ :=
  (R.inclusive t).filter (fun a => a < t)

noncomputable def occupied (C : Finset ℕ) (p : ℕ → ι × ι) : Finset ι := by
  classical
  exact C.image (fun a => (p a).1) ∪ C.image (fun a => (p a).2)

/-- A deterministic pair selection using only pre-launch data. Classical choice
here is a fixed function of the finite eligible-pair set, not of the fresh noise. -/
noncomputable def pickPair (P : Finset V) (C : Finset ι) (F : ι → V → ℝ) : ι × ι := by
  classical
  exact if h : ∃ p : ι × ι, p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧
      CommonWeakOrder P (F p.1) (F p.2) then h.choose
    else (Classical.choice inferInstance, Classical.choice inferInstance)

def RunEquations (R : ReservationPath) (P : ℕ → Finset V) (g : ℕ → V → ℝ)
    (n : ℕ) (F : ℕ → ι → V → ℝ) (p : ℕ → ι × ι) : Prop :=
  F 0 = (fun _ _ => 0) ∧ ∀ t < n,
    p t = pickPair (P t) (occupied (before R t) p) (F t) ∧
    F (t+1) = functionPairUpdate (F t) (p t).1 (p t).2 (g t)

lemma occupied_card
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : Finset ℕ) (p : ℕ → ι × ι) :
    (occupied C p).card ≤ 2*C.card := by
  classical
  exact (Finset.card_union_le _ _).trans (by
    have h1 := Finset.card_image_le (s := C) (f := fun a => (p a).1)
    have h2 := Finset.card_image_le (s := C) (f := fun a => (p a).2)
    omega)

lemma occupied_update
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {C : Finset ℕ} (p : ℕ → ι × ι) (n : ℕ) (z : ι × ι)
    (hn : ∀ a ∈ C, a < n) : occupied C (Function.update p n z) = occupied C p := by
  classical
  unfold occupied
  congr 1 <;> apply Finset.image_congr <;> intro a ha <;>
    simp [Function.update_of_ne (ne_of_lt (hn a ha))]

lemma pickPair_spec (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (C : Finset ι) (hC : C.card ≤ 2*q)
    (F : ι → V → ℝ) :
    let z := pickPair P C F
    z.1 ∉ C ∧ z.2 ∉ C ∧ z.1 ≠ z.2 ∧ CommonWeakOrder P (F z.1) (F z.2) := by
  classical
  obtain ⟨i,j,hi,hj,hij,ho⟩ := free_common_order k q hN P hP C hC F
  have hex : ∃ p : ι × ι, p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧
      CommonWeakOrder P (F p.1) (F p.2) := ⟨(i,j),hi,hj,hij,ho⟩
  simpa only [pickPair,dite_eq_left hex] using hex.choose_spec

lemma finite_run
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [DecidableEq ι]
    [Nonempty ι]
    (R : ReservationPath) (P : ℕ → Finset V) (g : ℕ → V → ℝ) (n : ℕ) :
    ∃ F : ℕ → ι → V → ℝ, ∃ p : ℕ → ι × ι, RunEquations R P g n F p := by
  classical
  induction n with
  | zero =>
    exact ⟨fun _ _ _ => 0, fun _ => (Classical.choice inferInstance,Classical.choice inferInstance),
      rfl,fun t ht => (Nat.not_lt_zero t ht).elim⟩
  | succ n ih =>
    obtain ⟨F,p,hzero,hsteps⟩ := ih
    let z := pickPair (P n) (occupied (before R n) p) (F n)
    let p' := Function.update p n z
    let F' := Function.update F (n+1) (functionPairUpdate (F n) z.1 z.2 (g n))
    refine ⟨F',p',?_,?_⟩
    · simpa [F'] using hzero
    · intro t ht
      have htn : t ≤ n := Nat.le_of_lt_succ ht
      have hoc : occupied (before R t) p' = occupied (before R t) p := by
        apply occupied_update
        intro a ha
        exact (Finset.mem_filter.mp ha).2.trans_le htn
      rw [hoc]
      by_cases hte : t = n
      · subst t
        simp [p',F',z]
      · have htn' : t < n := lt_of_le_of_ne htn hte
        have hne₁ : t ≠ n+1 := by omega
        have hne₂ : t+1 ≠ n+1 := by omega
        simpa only [p',F',Function.update_of_ne hte,Function.update_of_ne hne₁,
          Function.update_of_ne hne₂] using hsteps t htn'

theorem scheduled_particle_realization (R : ReservationPath)
    (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : ℕ → Finset V) (hP : ∀ t ≤ R.last, (P t).card ≤ k)
    (hsize : ∀ t, (R.inclusive t).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : ℕ → V → ℝ)
    (hLip : ∀ t ≤ R.last, ∀ u v, |g t u - g t v| ≤ L * d u v)
    (hHeight : ∀ t ≤ R.last, ∀ v, |g t v| ≤ H)
    (hvanish : ∀ t ≤ R.last, ∀ v ∈ P t, g t v = 0) :
    ∃ F : ℕ → ι → V → ℝ, ∃ p : ℕ → ι × ι,
      RunEquations R P g (R.last+1) F p ∧
      (∀ t ≤ R.last+1, FunctionParticleReachable d L H (F t)) ∧
      (∀ t ≤ R.last, (p t).1 ≠ (p t).2 ∧
        particleTrace (H * ((Fintype.card ι : ℝ)-1) + 2*Δ) (F t) (P t) =
        particleTrace (H * ((Fintype.card ι : ℝ)-1) + 2*Δ) (F (t+1)) (P t)) ∧
      (∀ t ≤ R.last, ∀ a ∈ R.inclusive t,
        F (t+1) (p a).1 = F (a+1) (p a).1 ∧
        F (t+1) (p a).2 = F (a+1) (p a).2) := by
  classical
  obtain ⟨F,p,hrun⟩ := finite_run (ι := ι) R P g (R.last+1)
  have hs (t : ℕ) (ht : t ≤ R.last) :
      (p t).1 ∉ occupied (before R t) p ∧ (p t).2 ∉ occupied (before R t) p ∧
      (p t).1 ≠ (p t).2 ∧ CommonWeakOrder (P t) (F t (p t).1) (F t (p t).2) := by
    have hc : (occupied (before R t) p).card ≤ 2*q := by
      have h1 := occupied_card (before R t) p
      have h2 : (before R t).card ≤ (R.inclusive t).card := Finset.card_filter_le _ _
      have h3 := hsize t
      omega
    have hh := pickPair_spec k q hN (P t) (hP t ht) (occupied (before R t) p) hc (F t)
    dsimp only at hh
    rw [← (hrun.2 t (by omega)).1] at hh
    exact hh
  have hreach : ∀ t ≤ R.last+1, FunctionParticleReachable d L H (F t) := by
    intro t
    induction t with
    | zero => intro _; rw [hrun.1]; exact .zero
    | succ t ih =>
      intro ht
      have htL : t ≤ R.last := by omega
      rw [(hrun.2 t (by omega)).2]
      exact .step (ih (by omega)) _ _ (hs t htL).2.2.1 (g t) (hLip t htL) (hHeight t htL)
  have hretain (t : ℕ) (ht : t ≤ R.last) (a : ℕ) (ha : a ∈ R.inclusive t) (hat : a < t) :
      F (t+1) (p a).1 = F t (p a).1 ∧ F (t+1) (p a).2 = F t (p a).2 := by
    have hab : a ∈ before R t := Finset.mem_filter.mpr ⟨ha,hat⟩
    have h1 : (p a).1 ∈ occupied (before R t) p :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a,hab,rfl⟩)
    have h2 : (p a).2 ∈ occupied (before R t) p :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a,hab,rfl⟩)
    have hei (r : ι) (hr : r ∈ occupied (before R t) p) : r ≠ (p t).1 ∧ r ≠ (p t).2 := by
      constructor
      · intro he; exact (hs t ht).1 (he ▸ hr)
      · intro he; exact (hs t ht).2.1 (he ▸ hr)
    rw [(hrun.2 t (by omega)).2]
    constructor <;> funext x
    · exact functionPairUpdate_other _ _ _ _ (hei _ h1).1 (hei _ h1).2 _ x
    · exact functionPairUpdate_other _ _ _ _ (hei _ h2).1 (hei _ h2).2 _ x
  refine ⟨F,p,hrun,hreach,?_,?_⟩
  · intro t ht
    refine ⟨(hs t ht).2.2.1,?_⟩
    have hc : (1 : ℝ) ≤ Fintype.card ι := by
      have hh : 1 ≤ Fintype.card ι := by omega
      exact_mod_cast hh
    have hM : 0 < H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      have hh := mul_nonneg hH.le (sub_nonneg.mpr hc)
      linarith
    have hb (s : ℕ) (hsl : s ≤ R.last+1) : ∀ r x,
        |F s r x| ≤ H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
      intro r x
      have hh := function_particles_height_bound hH (hreach s hsl) r x
      linarith
    rw [(hrun.2 t (by omega)).2]
    apply particleTrace_update _ hM _ _ _ (hs t ht).2.2.1 _ _ (hs t ht).2.2.2
      (hvanish t ht) (hb t (by omega))
    rw [← (hrun.2 t (by omega)).2]
    exact hb (t+1) (by omega)
  · intro t
    induction t with
    | zero =>
      intro ht a ha
      have ha0 : a = 0 := by
        simpa [ReservationPath.inclusive,ht] using (Finset.mem_filter.mp
          (show a ∈ (Finset.range 1).filter (fun a => 0 ≤ R.finish a) by
            simpa [ReservationPath.inclusive,ht] using ha)).1
      subst a
      exact ⟨rfl,rfl⟩
    | succ t ih =>
      intro ht a ha
      have hmem : a ≤ t+1 ∧ t+1 ≤ R.finish a := by
        simpa [ReservationPath.inclusive,ht,Nat.lt_succ_iff] using ha
      by_cases he : a = t+1
      · subst a; exact ⟨rfl,rfl⟩
      · have hat : a < t+1 := by omega
        have ht' : t ≤ R.last := by omega
        have ha' : a ∈ R.inclusive t := by
          simp [ReservationPath.inclusive,ht']
          omega
        have hh := hretain (t+1) ht a ha hat
        exact ⟨hh.1.trans (ih ht' a ha').1,hh.2.trans (ih ht' a ha').2⟩
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
variable {V ι Ω : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_weak_order
    {V : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype V] [MeasurableSpace Ω]
    (P : Finset V) (F H : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v))
    (hH : ∀ v, Measurable (fun ω => H ω v)) :
    MeasurableSet {ω | CommonWeakOrder P (F ω) (H ω)} := by
  classical
  simp only [CommonWeakOrder, Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro e
  have hmono (A : Ω → V → ℝ) (hA : ∀ v, Measurable (fun ω => A ω v)) :
      MeasurableSet {ω | Monotone (fun i : Fin P.card => A ω (e i))} := by
    simp only [Monotone, Set.ofPred_forall]
    exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_le (hA _) (hA _)
  exact (hmono F hF).inter (hmono H hH)

noncomputable def selectEligible (Q : ι × ι → Prop) : ι × ι := by
  classical
  exact if h : ∃ p, Q p then h.choose else
    (Classical.choice inferInstance, Classical.choice inferInstance)

lemma measurable_selectEligible
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι] : Measurable (selectEligible (ι := ι)) :=
  measurable_of_finite _

lemma measurable_eligibility
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (P : Finset V) (C : Ω → Finset ι) (F : Ω → ι → V → ℝ)
    (hC : Measurable C) (hF : ∀ i v, Measurable (fun ω => F ω i v)) :
    Measurable (fun ω => fun p : ι × ι =>
      p.1 ∉ C ω ∧ p.2 ∉ C ω ∧ p.1 ≠ p.2 ∧
        CommonWeakOrder P (F ω p.1) (F ω p.2)) := by
  classical
  apply measurable_pi_iff.mpr
  intro p
  apply measurableSet_setOfPred.mp
  have hmem (i : ι) : MeasurableSet {ω | i ∈ C ω} :=
    measurableSet_setOfPred.mpr ((measurable_finset_mem i).comp hC)
  have hneq : MeasurableSet {ω : Ω | p.1 ≠ p.2} := by
    by_cases h : p.1 = p.2 <;> simp [h]
  exact (hmem p.1).compl.inter ((hmem p.2).compl.inter
    (hneq.inter (measurable_weak_order P _ _ (hF p.1) (hF p.2))))

lemma pickPair_eq_selectEligible
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [DecidableEq ι]
    [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (P : Finset V) (C : Finset ι) (F : ι → V → ℝ) :
    pickPair P C F = selectEligible (fun p : ι × ι =>
      p.1 ∉ C ∧ p.2 ∉ C ∧ p.1 ≠ p.2 ∧ CommonWeakOrder P (F p.1) (F p.2)) := by
  classical
  unfold pickPair selectEligible
  split_ifs <;> rfl

lemma measurable_pickPair (P : Finset V) (C : Ω → Finset ι) (F : Ω → ι → V → ℝ)
    (hC : Measurable C) (hF : ∀ i v, Measurable (fun ω => F ω i v)) :
    Measurable (fun ω => pickPair P (C ω) (F ω)) := by
  simp_rw [pickPair_eq_selectEligible]
  exact measurable_selectEligible.comp (measurable_eligibility P C F hC hF)

lemma measurable_occupied
    {ι : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (C : Finset ℕ) (p : Ω → ℕ → ι × ι)
    (hp : ∀ a ∈ C, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => occupied C (p ω)) := by
  classical
  apply measurable_finset_iff.mpr
  intro i
  apply measurableSet_setOfPred.mp
  simp only [occupied, Finset.mem_union, Finset.mem_image, Set.ofPred_or,
    Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.union
  all_goals
    apply MeasurableSet.iUnion
    intro a
    by_cases ha : a ∈ C
    · simp only [ha, Set.ofPred_true, Set.univ_inter]
      first | exact measurableSet_eq_fun (hp a ha).fst measurable_const
            | exact measurableSet_eq_fun (hp a ha).snd measurable_const
    · simp [ha]

lemma measurable_selected
    {ι : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (F : Ω → ι → ℝ) (q : Ω → ι)
    (hF : ∀ i, Measurable (fun ω => F ω i)) (hq : Measurable q) :
    Measurable (fun ω => F ω (q ω)) := by
  classical
  have heq : (fun ω => F ω (q ω)) =
      (fun ω => ∑ i : ι, if q ω = i then F ω i else 0) := by
    funext ω
    simp
  rw [heq]
  apply Finset.measurable_sum
  intro i _
  exact (hF i).ite (measurableSet_eq_fun hq measurable_const) measurable_const

lemma measurable_pairUpdate
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (F : Ω → ι → V → ℝ) (p : Ω → ι × ι)
    (g : Ω → V → ℝ) (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (hp : Measurable p) (hg : ∀ v, Measurable (fun ω => g ω v)) (i : ι) (v : V) :
    Measurable (fun ω => functionPairUpdate (F ω) (p ω).1 (p ω).2 (g ω) i v) := by
  classical
  have hleft := measurable_selected (fun ω j => F ω j v) (fun ω => (p ω).1)
    (fun j => hF j v) hp.fst
  have hright := measurable_selected (fun ω j => F ω j v) (fun ω => (p ω).2)
    (fun j => hF j v) hp.snd
  have hmean := (hleft.add hright).div_const 2
  dsimp only [functionPairUpdate, pairUpdate]
  exact ((hF i v).add (((hmean.add (hg v)).sub hleft).ite
    (measurableSet_eq_fun measurable_const hp.fst) measurable_const)).add
    (((hmean.sub (hg v)).sub hright).ite
      (measurableSet_eq_fun measurable_const hp.snd) measurable_const)

/-- Measurability follows from the deterministic causal equations, for EVERY
pointwise realization. There is no assertion that an arbitrary choice operator
on an infinite real-valued space is measurable. -/
lemma run_measurable (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ)
    (F : Ω → ℕ → ι → V → ℝ) (p : Ω → ℕ → ι × ι)
    (hrun : ∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) :
    (∀ t ≤ n, ∀ i v, Measurable (fun ω => F ω t i v)) ∧
    (∀ t < n, Measurable (fun ω => p ω t)) := by
  classical
  have hi : ∀ t ≤ n,
      (∀ i v, Measurable (fun ω => F ω t i v)) ∧
      (∀ a < t, Measurable (fun ω => p ω a)) := by
    intro t
    induction t with
    | zero =>
      intro _
      constructor
      · intro i v
        have heq : (fun ω => F ω 0 i v) = (fun _ => 0) := by
          funext ω
          rw [(hrun ω).1]
        rw [heq]
        exact measurable_const
      · intro a ha
        omega
    | succ t ih =>
      intro ht
      obtain ⟨hF, hp⟩ := ih (by omega)
      have htn : t < n := by omega
      have hcurrent : Measurable (fun ω => p ω t) := by
        have heq : (fun ω => p ω t) =
            (fun ω => pickPair (P t) (occupied (before R t) (p ω)) (F ω t)) := by
          funext ω
          exact ((hrun ω).2 t htn).1
        rw [heq]
        apply measurable_pickPair _ _ _ _ hF
        apply measurable_occupied
        intro a ha
        exact hp a (Finset.mem_filter.mp ha).2
      constructor
      · intro i v
        have heq : (fun ω => F ω (t+1) i v) =
            (fun ω => functionPairUpdate (F ω t) (p ω t).1 (p ω t).2 (g ω t) i v) := by
          funext ω
          rw [((hrun ω).2 t htn).2]
        rw [heq]
        exact measurable_pairUpdate _ _ _ hF hcurrent (hg t) i v
      · intro a ha
        rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ ha) with h | h
        · exact hp a h
        · simpa [h] using hcurrent
  exact ⟨fun t ht => (hi t ht).1, fun t ht => (hi n le_rfl).2 t ht⟩

theorem measurable_particle_run (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ) :
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) ∧
      (∀ t ≤ n, ∀ i v, Measurable (fun ω => F ω t i v)) ∧
      (∀ t < n, Measurable (fun ω => p ω t)) := by
  classical
  choose F p hrun using (fun ω => finite_run (ι := ι) R P (g ω) n)
  exact ⟨F, p, hrun, run_measurable R P g hg n F p hrun⟩
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory Set
variable {V ι Ω : Type*} [Fintype V] [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_threshold_joint
    {V : Type treewidthLevel1} {Ω : Type treewidthLevel2} [Fintype V] [MeasurableSpace Ω]
    (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) :
    Measurable (fun z : Ω × ℝ => thresholdLabels (F z.1) z.2) := by
  classical
  apply measurable_pi_iff.mpr
  intro v
  have h : Measurable (fun z : Ω × ℝ => if z.2 < F z.1 v then true else false) :=
    measurable_const.ite (measurableSet_lt measurable_snd ((hF v).comp measurable_fst))
      measurable_const
  convert h using 1
  ext z
  simp [thresholdLabels]

lemma measurable_sweep_real (M : ℝ) (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) (S : Set (V → Bool)) :
    Measurable (fun ω => (sweep M (F ω)).real S) := by
  have hs := (measurable_threshold_joint F hF) ((Set.toFinite S).measurableSet)
  have hm := measurable_measure_prodMk_left
    (ν := volume.restrict (Icc (-M) M)) hs
  convert hm.ennreal_toReal using 1
  funext ω
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite S).measurableSet]
  rfl

lemma measurable_symmetrize_sweep_real (M : ℝ) (F : Ω → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v)) (S : Set (V → Bool)) :
    Measurable (fun ω => (symmetrizeCut (sweep M (F ω))).real S) := by
  have heq (ω : Ω) : (symmetrizeCut (sweep M (F ω))).real S =
      (1/2 : ℝ) * ((sweep M (F ω)).real S +
        (sweep M (F ω)).real (complementCut ⁻¹' S)) := by
    rw [symmetrizeCut, measureReal_ennreal_smul_apply,
      measureReal_add_apply (by finiteness) (by finiteness),
      map_measureReal_apply measurable_complementCut (Set.toFinite S).measurableSet]
    norm_num
  simp_rw [heq]
  exact ((measurable_sweep_real M F hF S).add
    (measurable_sweep_real M F hF _)).const_mul _

instance finite_cutTrace (μ : Measure (V → Bool)) [IsFiniteMeasure μ] (P : Finset V) :
    IsFiniteMeasure (cutTrace μ P) := by
  unfold cutTrace
  infer_instance

instance finite_particleTrace (M : ℝ) (F : ι → V → ℝ) (P : Finset V) :
    IsFiniteMeasure (particleTrace M F P) := by
  unfold particleTrace cutTrace
  infer_instance

lemma particle_real_sum
    {ι : Type treewidthLevel1} [Fintype ι] [DecidableEq ι] [Nonempty ι] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    {A : Type*} [MeasurableSpace A] (μ : ι → Measure A)
    [∀ i, IsFiniteMeasure (μ i)] (S : Set A) :
    (∑ i, μ i).real S = ∑ i, (μ i).real S := by
  simp only [measureReal_def, Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun i _ => measure_ne_top _ _)

lemma measurable_particleTrace_real (M : ℝ) (F : Ω → ι → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (P : Finset V) (S : Set (P → Bool)) :
    Measurable (fun ω => (particleTrace M (F ω) P).real S) := by
  have heq (ω : Ω) : (particleTrace M (F ω) P).real S =
      ∑ i, (symmetrizeCut (sweep M (F ω i))).real
        ((fun a : V → Bool => fun v : P => a v) ⁻¹' S) := by
    rw [particleTrace, particle_real_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact map_measureReal_apply (measurable_of_finite _) (Set.toFinite S).measurableSet
  simp_rw [heq]
  apply Finset.measurable_sum
  intro i hi
  exact measurable_symmetrize_sweep_real M (fun ω => F ω i) (hF i) _

lemma symmetrize_sweep_mass (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    (symmetrizeCut (sweep M F)).real univ = 2*M := by
  rw [symmetrizeCut, measureReal_ennreal_smul_apply,
    measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut MeasurableSet.univ]
  simp only [preimage_univ, sweep_total_mass M hM]
  norm_num
  ring

lemma particleTrace_mass (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) (P : Finset V) :
    (particleTrace M F P).real univ = 2*(Fintype.card ι : ℝ)*M := by
  rw [particleTrace, particle_real_sum]
  have heq (i : ι) : (cutTrace (symmetrizeCut (sweep M (F i))) P).real univ = 2*M := by
    rw [cutTrace, map_measureReal_apply (measurable_of_finite _) MeasurableSet.univ]
    simpa only [preimage_univ] using symmetrize_sweep_mass M hM (F i)
  simp_rw [heq]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

lemma integrable_particleTrace_real (M : ℝ) (hM : 0 ≤ M) (F : Ω → ι → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (P : Finset V) (S : Set (P → Bool)) (ν : Measure Ω) [IsFiniteMeasure ν] :
    Integrable (fun ω => (particleTrace M (F ω) P).real S) ν := by
  apply (integrable_const (2*(Fintype.card ι : ℝ)*M)).mono'
    (measurable_particleTrace_real M F hF P S).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro ω
  rw [Real.norm_eq_abs, abs_of_nonneg (measureReal_nonneg)]
  exact (measureReal_mono (subset_univ S)).trans_eq (particleTrace_mass M hM (F ω) P)

theorem measurable_branch_cut_laws (R : ReservationPath) (P : ℕ → Finset V)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v)) (n : ℕ)
    (M : ℝ) (hM : 0 ≤ M) (ν : Measure Ω) [IsFiniteMeasure ν] :
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) n (F ω) (p ω)) ∧
      (∀ t ≤ n, ∀ B : Finset V, ∀ b : B → Bool,
        Measurable (fun ω => (particleTrace M (F ω t) B).real {b}) ∧
        Integrable (fun ω => (particleTrace M (F ω t) B).real {b}) ν) ∧
      (∀ ω t, (particleTrace M (F ω t) (P t)).real Set.univ =
        2*(Fintype.card ι : ℝ)*M) := by
  obtain ⟨F,p,hrun,hF,hp⟩ := measurable_particle_run (ι := ι) R P g hg n
  refine ⟨F,p,hrun,?_,?_⟩
  · intro t ht B b
    exact ⟨measurable_particleTrace_real M (fun ω => F ω t) (hF t ht) B {b},
      integrable_particleTrace_real M hM (fun ω => F ω t) (hF t ht) B {b} ν⟩
  · intro ω t
    exact particleTrace_mass M hM (F ω t) (P t)
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleSchedule
open MeasureTheory
open scoped ENNReal
variable {V ι Ω : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  [Nonempty ι] [MeasurableSpace Ω]

/-- Literal restriction of a bag assignment to a smaller bag. -/
def restrictBagCut (P Q : Finset V) (h : Q ⊆ P) (a : P → Bool) : Q → Bool :=
  fun x => a ⟨x,h x.property⟩

lemma particleTrace_restrict
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [DecidableEq V] [Fintype ι]
    [DecidableEq ι] [Nonempty ι]
    (M : ℝ) (F : ι → V → ℝ)
    (P Q : Finset V) (h : Q ⊆ P) :
    (particleTrace M F P).map (restrictBagCut P Q h) = particleTrace M F Q := by
  classical
  rw [particleTrace, Measure.map_finset_sum' (measurable_of_finite _).aemeasurable]
  unfold particleTrace
  apply Finset.sum_congr rfl
  intro i _
  rw [cutTrace, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  rfl

theorem compatible_measurable_branch (R : ReservationPath)
    (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : ℕ → Finset V) (hP : ∀ t ≤ R.last, (P t).card ≤ k)
    (hsize : ∀ t, (R.inclusive t).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → ℕ → V → ℝ) (hg : ∀ t v, Measurable (fun ω => g ω t v))
    (hLip : ∀ ω t, t ≤ R.last → ∀ u v, |g ω t u - g ω t v| ≤ L * d u v)
    (hHeight : ∀ ω t, t ≤ R.last → ∀ v, |g ω t v| ≤ H)
    (hvanish : ∀ ω t, t ≤ R.last → ∀ v ∈ P t, g ω t v = 0)
    (ν : Measure Ω) [IsFiniteMeasure ν] :
    let M := H * ((Fintype.card ι : ℝ)-1) + 2*Δ
    ∃ F : Ω → ℕ → ι → V → ℝ, ∃ p : Ω → ℕ → ι × ι,
      (∀ ω, RunEquations R P (g ω) (R.last+1) (F ω) (p ω)) ∧
      (∀ ω t, t ≤ R.last+1 → FunctionParticleReachable d L H (F ω t)) ∧
      (∀ t ≤ R.last, ∀ b : P t → Bool,
        Measurable (fun ω => (particleTrace M (F ω (t+1)) (P t)).real {b}) ∧
        Integrable (fun ω => (particleTrace M (F ω (t+1)) (P t)).real {b}) ν) ∧
      (∀ ω t, (particleTrace M (F ω (t+1)) (P t)).real Set.univ =
        2*(Fintype.card ι : ℝ)*M) ∧
      (∀ ω t, t < R.last →
        (particleTrace M (F ω (t+1)) (P t)).map
          (restrictBagCut (P t) (P t ∩ P (t+1)) Finset.inter_subset_left) =
        (particleTrace M (F ω (t+2)) (P (t+1))).map
          (restrictBagCut (P (t+1)) (P t ∩ P (t+1)) Finset.inter_subset_right)) ∧
      (∀ ω t, t ≤ R.last → ∀ a ∈ R.inclusive t,
        F ω (t+1) (p ω a).1 = F ω (a+1) (p ω a).1 ∧
        F ω (t+1) (p ω a).2 = F ω (a+1) (p ω a).2) := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  dsimp only
  choose F p hrun hreach htrace hretain using
    fun ω => scheduled_particle_realization (ι := ι) R k q hN P hP hsize d L H Δ hH hΔ
      (g ω) (hLip ω) (hHeight ω) (hvanish ω)
  have hmeas := (run_measurable R P g hg (R.last+1) F p hrun).1
  have hc : (1 : ℝ) ≤ Fintype.card ι := by
    have hn : 1 ≤ Fintype.card ι := Fintype.card_pos
    exact_mod_cast hn
  have hM : 0 ≤ H * ((Fintype.card ι : ℝ)-1) + 2*Δ := by
    positivity
  refine ⟨F,p,hrun,hreach,?_,?_,?_,hretain⟩
  · intro t ht b
    exact ⟨measurable_particleTrace_real _ (fun ω => F ω (t+1))
        (hmeas (t+1) (by omega)) (P t) {b},
      integrable_particleTrace_real _ hM (fun ω => F ω (t+1))
        (hmeas (t+1) (by omega)) (P t) {b} ν⟩
  · intro ω t
    exact particleTrace_mass _ hM _ _
  · intro ω t ht
    rw [particleTrace_restrict, particleTrace_restrict]
    have heq := congrArg (fun μ => μ.map (restrictBagCut (P (t+1))
      (P t ∩ P (t+1)) Finset.inter_subset_right))
      (htrace ω (t+1) (by omega)).2
    simpa only [particleTrace_restrict, Nat.add_assoc] using heq
end BoundedTreewidthL1.ParticleSchedule

namespace BoundedTreewidthL1.ParticleBatch
open MeasureTheory ParticleSchedule
variable {V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def usedPairs (C : Finset J) (p : J → ι × ι) : Finset ι :=
  (C.image (fun a => (p a).1)) ∪ (C.image (fun a => (p a).2))

/-- Launch all new active keys at one interface, reserving a pair immediately
before proceeding to the next key. Retained keys are supplied in C. -/
noncomputable def launchBatch (P : Finset V) : (l : List J) → (C : Finset J) →
    (F : ι → V → ℝ) → (p : J → ι × ι) → (g : J → V → ℝ) →
    (ι → V → ℝ) × (J → ι × ι)
  | [], _, F, p, _ => (F,p)
  | a :: l, C, F, p, g =>
    let z := pickPair P (usedPairs C p) F
    launchBatch P l (insert a C) (functionPairUpdate F z.1 z.2 (g a))
      (Function.update p a z) g

lemma usedPairs_card
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    (C : Finset J) (p : J → ι × ι) :
    (usedPairs C p).card ≤ 2*C.card := by
  unfold usedPairs
  have h := Finset.card_union_le (C.image (fun a => (p a).1)) (C.image (fun a => (p a).2))
  have h₁ := Finset.card_image_le (s := C) (f := fun a => (p a).1)
  have h₂ := Finset.card_image_le (s := C) (f := fun a => (p a).2)
  omega

lemma usedPairs_mono
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C D : Finset J} (h : C ⊆ D) (p : J → ι × ι) :
    usedPairs C p ⊆ usedPairs D p :=
  Finset.union_subset_union (Finset.image_subset_image h) (Finset.image_subset_image h)

lemma usedPairs_update
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∉ C)
    (p : J → ι × ι) (z : ι × ι) : usedPairs C (Function.update p a z) = usedPairs C p := by
  unfold usedPairs
  congr 1 <;> apply Finset.image_congr <;> intro b hb <;>
    simp only [Function.update_of_ne (show b ≠ a from fun h => ha (h ▸ hb))]

lemma first_mem_used
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∈ C) (p : J → ι × ι) :
    (p a).1 ∈ usedPairs C p :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)
lemma second_mem_used
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [DecidableEq J]
    {C : Finset J} {a : J} (ha : a ∈ C) (p : J → ι × ι) :
    (p a).2 ∈ usedPairs C p :=
  Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha)

/-- The reservation-preserving finite batch required by the co-bag active-scale
construction. No bound on the total number of updates is imposed. -/
theorem launchBatch_correct (k q : ℕ)
    (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (P : Finset V) (hP : P.card ≤ k) (l : List J) (C : Finset J)
    (hl : l.Nodup) (hfresh : ∀ a ∈ l, a ∉ C)
    (hcount : (C ∪ l.toFinset).card ≤ q)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (F : ι → V → ℝ) (p : J → ι × ι)
    (hF : FunctionParticleReachable d L H F) (g : J → V → ℝ)
    (hLip : ∀ a ∈ l, ∀ u v, |g a u - g a v| ≤ L*d u v)
    (hHeight : ∀ a ∈ l, ∀ v, |g a v| ≤ H)
    (hzero : ∀ a ∈ l, ∀ v ∈ P, g a v = 0) :
    let out := launchBatch P l C F p g
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    FunctionParticleReachable d L H out.1 ∧
    particleTrace M out.1 P = particleTrace M F P ∧
    (∀ a ∈ C, out.2 a = p a) ∧
    (∀ i ∈ usedPairs C p, out.1 i = F i) ∧
    (∀ a ∈ l, (out.2 a).1 ≠ (out.2 a).2 ∧
      ∀ v, out.1 (out.2 a).1 v - out.1 (out.2 a).2 v = 2*g a v) := by
  classical
  induction l generalizing C F p with
  | nil =>
    simpa [launchBatch] using hF
  | cons a l ih =>
    have haC : a ∉ C := hfresh a (by simp)
    let z := pickPair P (usedPairs C p) F
    let F₁ := functionPairUpdate F z.1 z.2 (g a)
    let p₁ := Function.update p a z
    have hC : C.card ≤ q := (Finset.card_le_card Finset.subset_union_left).trans hcount
    have hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2 ∧
        CommonWeakOrder P (F z.1) (F z.2) :=
      pickPair_spec k q hN P hP _ ((usedPairs_card C p).trans (by omega)) F
    have hF₁ : FunctionParticleReachable d L H F₁ :=
      FunctionParticleReachable.step hF z.1 z.2 hz.2.2.1 (g a)
        (hLip a (by simp)) (hHeight a (by simp))
    have hnewCount : (insert a C ∪ l.toFinset).card ≤ q := by
      simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using hcount
    have hnewFresh : ∀ b ∈ l, b ∉ insert a C := by
      intro b hb h
      rcases Finset.mem_insert.mp h with h | h
      · subst b
        exact (List.nodup_cons.mp hl).1 hb
      · exact hfresh b (by simp [hb]) h
    have hresult := ih (insert a C) hl.of_cons hnewFresh hnewCount F₁ p₁ hF₁
      (fun b hb => hLip b (by simp [hb])) (fun b hb => hHeight b (by simp [hb]))
      (fun b hb => hzero b (by simp [hb]))
    dsimp only at hresult ⊢
    change _ ∧ _ ∧ _ ∧ _ ∧ _
    dsimp only [launchBatch]
    change FunctionParticleReachable d L H (launchBatch P l (insert a C) F₁ p₁ g).1 ∧
      particleTrace (H*((Fintype.card ι : ℝ)-1)+2*Δ)
        (launchBatch P l (insert a C) F₁ p₁ g).1 P = particleTrace
        (H*((Fintype.card ι : ℝ)-1)+2*Δ) F P ∧
      (∀ b ∈ C, (launchBatch P l (insert a C) F₁ p₁ g).2 b = p b) ∧
      (∀ i ∈ usedPairs C p, (launchBatch P l (insert a C) F₁ p₁ g).1 i = F i) ∧
      (∀ b ∈ a :: l,
        ((launchBatch P l (insert a C) F₁ p₁ g).2 b).1 ≠
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).2 ∧
        ∀ v, (launchBatch P l (insert a C) F₁ p₁ g).1
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).1 v -
          (launchBatch P l (insert a C) F₁ p₁ g).1
          ((launchBatch P l (insert a C) F₁ p₁ g).2 b).2 v = 2*g b v)
    refine ⟨hresult.1, ?_, ?_, ?_, ?_⟩
    · have hc : (1:ℝ) ≤ Fintype.card ι := by
        exact_mod_cast (Fintype.card_pos : 0 < Fintype.card ι)
      have hM : 0 < H*((Fintype.card ι : ℝ)-1)+2*Δ := by
        have := mul_nonneg hH.le (sub_nonneg.mpr hc)
        linarith
      have htrace := particleTrace_update _ hM F z.1 z.2 hz.2.2.1 (g a) P hz.2.2.2
        (hzero a (by simp))
        (fun i v => (function_particles_height_bound hH hF i v).trans (by linarith))
        (fun i v => (function_particles_height_bound hH hF₁ i v).trans (by linarith))
      exact hresult.2.1.trans htrace.symm
    · intro b hb
      rw [hresult.2.2.1 b (Finset.mem_insert_of_mem hb)]
      exact Function.update_of_ne (show b ≠ a from fun h => haC (h ▸ hb)) _ _
    · intro i hi
      have hi₁ : i ∈ usedPairs (insert a C) p₁ := by
        apply usedPairs_mono (Finset.subset_insert a C) p₁
        rwa [usedPairs_update haC]
      rw [hresult.2.2.2.1 i hi₁]
      funext v
      exact functionPairUpdate_other F z.1 z.2 i
        (fun h => hz.1 (h ▸ hi)) (fun h => hz.2.1 (h ▸ hi)) (g a) v
    · intro b hb
      rcases List.mem_cons.mp hb with h | hb
      · subst b
        have hpz : (launchBatch P l (insert a C) F₁ p₁ g).2 a = z := by
          simpa [p₁] using hresult.2.2.1 a (Finset.mem_insert_self a C)
        change ((launchBatch P l (insert a C) F₁ p₁ g).2 a).1 ≠ _ ∧ _
        rw [hpz]
        refine ⟨hz.2.2.1, ?_⟩
        intro v
        have hz₁ : z.1 ∈ usedPairs (insert a C) p₁ := by
          simpa [p₁] using first_mem_used (Finset.mem_insert_self a C) p₁
        have hz₂ : z.2 ∈ usedPairs (insert a C) p₁ := by
          simpa [p₁] using second_mem_used (Finset.mem_insert_self a C) p₁
        rw [hresult.2.2.2.1 z.1 hz₁, hresult.2.2.2.1 z.2 hz₂]
        dsimp [F₁]
        rw [functionPairUpdate_left F z.1 z.2 hz.2.2.1,
          functionPairUpdate_right F z.1 z.2 hz.2.2.1]
        ring
      · exact hresult.2.2.2.2 b hb
end BoundedTreewidthL1.ParticleBatch

namespace BoundedTreewidthL1.ParticleBatch
open MeasureTheory ParticleSchedule
variable {V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma measurable_usedPairs
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} {Ω : Type treewidthLevel3} [Fintype ι]
    [Nonempty ι] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω] [MeasurableSpace ι]
    [MeasurableSingletonClass ι]
    (C : Finset J) (p : Ω → J → ι × ι)
    (hp : ∀ a, Measurable (fun ω => p ω a)) :
    Measurable (fun ω => usedPairs C (p ω)) := by
  have hp' : Measurable p := measurable_pi_iff.mpr hp
  exact (measurable_of_finite (fun p : J → ι × ι => usedPairs C p)).comp hp'

/-- The exact finite multi-launch scheduler is measurable; all pair choice is
finite deterministic selection, not choice on the real sample space. -/
theorem measurable_launchBatch (P : Finset V) (l : List J) (C : Finset J)
    (F : Ω → ι → V → ℝ) (p : Ω → J → ι × ι) (g : Ω → J → V → ℝ)
    (hF : ∀ i v, Measurable (fun ω => F ω i v))
    (hp : ∀ a, Measurable (fun ω => p ω a))
    (hg : ∀ a v, Measurable (fun ω => g ω a v)) :
    Measurable (fun ω => launchBatch P l C (F ω) (p ω) (g ω)) := by
  classical
  induction l generalizing C F p with
  | nil =>
    exact (measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr (hF i)).prodMk
      (measurable_pi_iff.mpr hp)
  | cons a l ih =>
    let z : Ω → ι × ι := fun ω => pickPair P (usedPairs C (p ω)) (F ω)
    have hz : Measurable z := measurable_pickPair P _ F (measurable_usedPairs C p hp) hF
    have hF₁ : ∀ i v, Measurable (fun ω =>
        functionPairUpdate (F ω) (z ω).1 (z ω).2 (g ω a) i v) :=
      measurable_pairUpdate F z (fun ω => g ω a) hF hz (hg a)
    have hp₁ : ∀ b, Measurable (fun ω => Function.update (p ω) a (z ω) b) := by
      intro b
      by_cases h : b = a
      · subst b
        simpa only [Function.update_self] using hz
      · simpa only [Function.update_of_ne h] using hp b
    exact ih (insert a C) _ _ hF₁ hp₁
end BoundedTreewidthL1.ParticleBatch

end OAI
end
end

section
section
namespace OAI


/-! Deterministic causal recursion on a rooted finite tree. The depth certificate
is constructed from graph distance below; it is not an embedding hypothesis. -/
namespace BoundedTreewidthL1

structure RootedForest (I : Type*) where
  parent : I → Option I
  depth : I → ℕ
  decreases : ∀ i p, parent i = some p → depth p < depth i

namespace RootedForest
variable {I A : Type*}

noncomputable def run (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) : A :=
  step i (match h : R.parent i with
    | none => seed
    | some p =>
      have : R.depth p < R.depth i := R.decreases i p h
      R.run seed step p)
termination_by R.depth i
decreasing_by assumption

lemma run_eq (R : RootedForest I) (seed : A) (step : I → A → A) (i : I) :
    R.run seed step i = step i ((R.parent i).elim seed (R.run seed step)) := by
  rw [run]
  split <;> simp_all

lemma run_invariant (R : RootedForest I) (seed : A) (step : I → A → A)
    (Q : A → Prop) (hseed : Q seed) (hstep : ∀ i a, Q a → Q (step i a)) :
    ∀ i, Q (R.run seed step i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [run_eq]
    apply hstep
    cases hp : R.parent i with
    | none => exact hseed
    | some p =>
      apply ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl

lemma run_measurable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (R : RootedForest I) (seed : Ω → A) (step : I → Ω → A → A)
    (hseed : Measurable seed)
    (hstep : ∀ i f, Measurable f → Measurable (fun ω => step i ω (f ω))) :
    ∀ i, Measurable (fun ω => R.run (seed ω) (fun j => step j ω) i) := by
  intro i
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    simp_rw [run_eq]
    cases hp : R.parent i with
    | none => simpa only [hp, Option.elim_none] using hstep i seed hseed
    | some p =>
      simpa only [hp, Option.elim_some] using hstep i _
        (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p rfl)
end RootedForest
end BoundedTreewidthL1

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def interface (R : RootedForest I) (bag : I → Finset V) (i : I) : Finset V :=
  (R.parent i).elim ∅ bag
noncomputable def retained (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  (R.parent i).elim ∅ (fun p => A i ∩ A p)
noncomputable def fresh (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  A i \ retained R A i
noncomputable def seed : (ι → V → ℝ) × (J → ι × ι) :=
  (fun _ _ => 0, fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))
noncomputable def step (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (S : (ι → V → ℝ) × (J → ι × ι)) :=
  launchBatch (interface R bag i) (fresh R A i).toList (retained R A i) S.1 S.2 (g i)
noncomputable def state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) : (ι → V → ℝ) × (J → ι × ι) :=
  R.run seed (step R bag A g) i

lemma retained_subset (R : RootedForest I) (A : I → Finset J) (i : I) :
    retained R A i ⊆ A i := by
  unfold retained
  cases R.parent i with
  | none => exact Finset.empty_subset _
  | some p => exact Finset.inter_subset_left

lemma batch_data (R : RootedForest I) (A : I → Finset J) (i : I)
    {q : ℕ} (hA : (A i).card ≤ q) :
    (fresh R A i).toList.Nodup ∧
    (∀ a ∈ (fresh R A i).toList, a ∉ retained R A i) ∧
    (retained R A i ∪ (fresh R A i).toList.toFinset).card ≤ q := by
  classical
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  · simpa only [Finset.toList_toFinset, fresh,
      Finset.union_sdiff_of_subset (retained_subset R A i)] using hA

lemma interface_card
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} [Fintype V]
    (R : RootedForest I) (bag : I → Finset V) {k : ℕ}
    (hbag : ∀ i, (bag i).card ≤ k) (i : I) : (interface R bag i).card ≤ k := by
  unfold interface
  cases R.parent i with
  | none => exact Nat.zero_le _
  | some p => exact hbag p

lemma state_eq
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {J : Type treewidthLevel4} [Fintype V] [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq J]
    (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) :
    state (ι := ι) R bag A g i = step R bag A g i
      ((R.parent i).elim seed (state R bag A g)) := RootedForest.run_eq _ _ _ _
/-- Actual branching preparation for active-scale keys. Children use their own
copies of the parent's list; no consistency assumption on sampled bag laws. -/
theorem forest_particle_realization (R : RootedForest I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ interface R bag i, g i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let S := state (ι := ι) R bag A g
    (∀ i, FunctionParticleReachable d L H (S i).1) ∧
    (∀ i p, R.parent i = some p →
      particleTrace M (S i).1 (bag p) = particleTrace M (S p).1 (bag p)) ∧
    (∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) ∧
    (∀ i a, a ∈ fresh R A i →
      ((S i).2 a).1 ≠ ((S i).2 a).2 ∧
      ∀ v, (S i).1 ((S i).2 a).1 v - (S i).1 ((S i).2 a).2 v = 2*g i a v) := by
  classical
  dsimp only
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  let S := state (ι := ι) R bag A g
  have hstep (i : I) (F : ι → V → ℝ) (p : J → ι × ι)
      (hF : FunctionParticleReachable d L H F) :=
    launchBatch_correct k q hN (interface R bag i) (interface_card R bag hbag i)
      (fresh R A i).toList (retained R A i)
      (batch_data R A i (hA i)).1 (batch_data R A i (hA i)).2.1
      (batch_data R A i (hA i)).2.2 d L H Δ hH hΔ F p hF (g i)
      (fun a _ => hLip i a) (fun a _ => hHeight i a) (fun a _ => hzero i a)
  have hreach : ∀ i, FunctionParticleReachable d L H (S i).1 := by
    apply R.run_invariant seed (step R bag A g) (fun S => FunctionParticleReachable d L H S.1)
    · exact FunctionParticleReachable.zero
    · intro i F hF
      exact (hstep i F.1 F.2 hF).1
  have hinput (i : I) : FunctionParticleReachable d L H
      ((R.parent i).elim seed S).1 := by
    cases hp : R.parent i with
    | none => exact FunctionParticleReachable.zero
    | some p => exact hreach p
  have hstate (i : I) :
      launchBatch (interface R bag i) (fresh R A i).toList (retained R A i)
        ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 (g i) = S i :=
    (state_eq R bag A g i).symm
  refine ⟨hreach, ?_, ?_, ?_⟩
  · intro i p hp
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.1
    rw [hstate] at hj
    unfold interface at hj
    rw [hp] at hj
    exact hj
  · intro i p hp a ha
    have hj := hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)
    dsimp only at hj
    rw [hstate] at hj
    have hm : a ∈ retained R A i := by simpa only [retained, hp, Option.elim_some] using ha
    have he := hj.2.2.1 a hm
    have hleft := hj.2.2.2.1 _ (first_mem_used hm ((R.parent i).elim seed S).2)
    have hright := hj.2.2.2.1 _ (second_mem_used hm ((R.parent i).elim seed S).2)
    have he' : (S i).2 a = (S p).2 a := by
      simpa only [hp, Option.elim_some] using he
    refine ⟨he', ?_, ?_⟩
    · rw [he']
      simpa only [hp, Option.elim_some] using hleft
    · rw [he']
      simpa only [hp, Option.elim_some] using hright
  · intro i a ha
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.2.2.2 a (Finset.mem_toList.mpr ha)
    rw [hstate] at hj
    exact hj
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Measurability of the actual branching preparation, with all randomness
sampled beforehand. No measurable-choice assumption about the particle lists. -/
theorem measurable_state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : Ω → I → J → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (i : I) :
    Measurable (fun ω => state (ι := ι) R bag A (g ω) i) := by
  apply R.run_measurable (fun _ => seed) (fun j ω S => step R bag A (g ω) j S)
    measurable_const
  intro j f hf
  exact measurable_launchBatch (interface R bag j) (fresh R A j).toList (retained R A j)
    (fun ω => (f ω).1) (fun ω => (f ω).2) (fun ω => g ω j)
    (fun a v => (measurable_pi_apply v).comp ((measurable_pi_apply a).comp hf.fst))
    (fun a => (measurable_pi_apply a).comp hf.snd) (hg j)

end BoundedTreewidthL1.TreeParticles

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.TreeMarkov
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- A symmetric edge interaction; nonedge values are irrelevant. -/
abbrev Symmetric (R : (i j : I) → A i → A j → ℝ) : Prop :=
  ∀ i j a b, R i j a b = R j i b a

noncomputable def edgeFactor (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (x : (i : I) → A i) : Sym2 I → ℝ :=
  Sym2.lift ⟨fun i j => R i j (x i) (x j), fun i j => hs i j (x i) (x j)⟩

noncomputable def density (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) : ℝ :=
  (∏ i, μ i (x i)) * ∏ e ∈ T.edgeFinset, edgeFactor A R hs x e

/-- The exact local normalization needed for junction gluing. At zero-mass
states no conditional probability is required. -/
def Normalized (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) : Prop :=
  (∀ i a, 0 ≤ μ i a) ∧ (∀ i, (∑ a, μ i a) = 1) ∧
  (∀ i j, T.Adj i j → ∀ a b, 0 ≤ R i j a b) ∧
  ∀ i j, T.Adj i j → ∀ a, μ i a ≠ 0 →
    (∑ b, μ j b * R i j a b) = 1

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

@[simp] lemma edgeFactor_mk
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (x : (i : I) → A i) (i j : I) :
    edgeFactor A R hs x s(i,j) = R i j (x i) (x j) := rfl

lemma density_nonneg (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R) (x : (i : I) → A i) :
    0 ≤ density A T μ R hs x := by
  apply mul_nonneg (Finset.prod_nonneg (fun i _ => hn.1 i (x i)))
  apply Finset.prod_nonneg
  intro e he
  induction e using Sym2.ind with
  | _ i j => exact hn.2.2.1 i j (by simpa using he) (x i) (x j)

lemma density_zero
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) (i : I) (hi : μ i (x i) = 0) :
    density A T μ R hs x = 0 := by
  have hz : (∏ j, μ j (x j)) = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hi
  simp [density, hz]

lemma edgeFinset_leaf (T : SimpleGraph I) {l p : I} (hlp : T.Adj l p)
    (hp : ∀ j, T.Adj l j → j = p) :
    T.edgeFinset = insert s(l,p)
      ((T.induce {i | i ≠ l}).edgeFinset.map
        (Function.Embedding.subtype (fun i => i ≠ l)).sym2Map) := by
  erw [SimpleGraph.map_edgeFinset_induce (s := {i | i ≠ l}) (G := T)]
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    simp only [Finset.mem_insert, Finset.mem_inter, SimpleGraph.mem_edgeFinset,
      Finset.mk_mem_sym2_iff, Set.mem_toFinset, Set.mem_ofPred_eq]
    constructor
    · intro hij
      by_cases hi : i = l
      · subst i
        left
        rw [hp j hij]
      · by_cases hj : j = l
        · subst j
          left
          rw [hp i hij.symm, Sym2.eq_swap]
        · exact Or.inr ⟨hij, hi, hj⟩
    · rintro (he | ⟨hij, _, _⟩)
      · have : s(i,j) ∈ T.edgeSet := he ▸ hlp
        exact this
      · exact hij

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

@[simp] lemma edgeFactor_induce
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (S : Set I)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : I) → A i) (e : Sym2 S) :
    edgeFactor A R hs x (Sym2.map Subtype.val e) =
      edgeFactor (fun i : S => A i) (fun i j => R i j)
        (fun i j => hs i j) (fun i => x i) e := by
  induction e using Sym2.ind with
  | _ i j => rfl

lemma density_leaf (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (x : (i : I) → A i) :
    density A T μ R hs x =
      density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) (fun i => x i) *
      (μ l (x l) * R p l (x p) (x l)) := by
  have hnot : s(l,p) ∉ ((T.induce {i | i ≠ l}).edgeFinset.map
      (Function.Embedding.subtype (fun i => i ≠ l)).sym2Map) := by
    erw [SimpleGraph.map_edgeFinset_induce (s := {i | i ≠ l}) (G := T)]
    simp
  unfold density
  rw [Fintype.prod_eq_mul_prod_subtype_ne (fun i => μ i (x i)) l,
    edgeFinset_leaf T hlp hp, Finset.prod_insert hnot, Finset.prod_map]
  simp only [edgeFactor_mk]
  have hm : (∏ e ∈ (T.induce {i | i ≠ l}).edgeFinset,
      edgeFactor A R hs x ((Function.Embedding.subtype (fun i => i ≠ l)).sym2Map e)) =
      ∏ e ∈ (T.induce {i | i ≠ l}).edgeFinset,
        edgeFactor (fun i : {i // i ≠ l} => A i) (fun i j => R i j)
          (fun i j => hs i j) (fun i => x i) e := by
    apply Finset.prod_congr rfl
    intro e _
    exact edgeFactor_induce A {i | i ≠ l} R hs x e
  erw [hm]
  rw [hs l p]
  ring_nf
  congr 1

@[simp] lemma splitAt_here
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i) :
    (Equiv.piSplitAt l A).symm (a,x) l = a := by
  simp [Equiv.piSplitAt_symm_apply]

@[simp] lemma splitAt_away
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i)
    (i : I) (hi : i ≠ l) :
    (Equiv.piSplitAt l A).symm (a,x) i = x ⟨i,hi⟩ := by
  simp [Equiv.piSplitAt_symm_apply, hi]

lemma splitAt_restrict (l : I) (a : A l) (x : (i : {i // i ≠ l}) → A i) :
    (fun i : {i // i ≠ l} => (Equiv.piSplitAt l A).symm (a,x) i) = x := by
  funext i
  exact splitAt_away A l a x i i.property

lemma sum_leaf_density (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (x : (i : {i // i ≠ l}) → A i) :
    (∑ a, density A T μ R hs ((Equiv.piSplitAt l A).symm (a,x))) =
      density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x := by
  have hpne : p ≠ l := hlp.ne.symm
  let p' : {i // i ≠ l} := ⟨p,hpne⟩
  simp_rw [density_leaf A T μ R hs hlp hp, splitAt_restrict,
    splitAt_here, splitAt_away A l _ x p hpne]
  rw [← Finset.mul_sum]
  by_cases hz : μ p (x p') = 0
  · have hd := density_zero (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
      (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x p' hz
    rw [hd, zero_mul]
  · rw [hn.2.2.2 p l hlp.symm (x p') hz, mul_one]

lemma expectation_leaf (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A T μ R)
    {l p : I} (hlp : T.Adj l p) (hp : ∀ j, T.Adj l j → j = p)
    (f : ((i : {i // i ≠ l}) → A i) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun i : {i // i ≠ l} => x i)) =
      ∑ x, density (fun i : {i // i ≠ l} => A i) (T.induce {i | i ≠ l})
        (fun i => μ i) (fun i j => R i j) (fun i j => hs i j) x * f x := by
  rw [← (Equiv.piSplitAt l A).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  simp only [splitAt_restrict, ← Finset.sum_mul,
    sum_leaf_density A T μ R hs hn hlp hp]

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma Normalized.induce {I : Type*} [Fintype I] {A : I → Type*} [∀ i, Fintype (A i)]
    {T : SimpleGraph I} {μ : (i : I) → A i → ℝ}
    {R : (i j : I) → A i → A j → ℝ} (hn : Normalized A T μ R) (S : Set I) :
    Normalized (fun i : S => A i) (T.induce S) (fun i => μ i) (fun i j => R i j) := by
  exact ⟨fun i => hn.1 i, fun i => hn.2.1 i,
    fun i j hij => hn.2.2.1 i j hij, fun i j hij => hn.2.2.2 i j hij⟩

private theorem node_marginal_card (n : ℕ) :
    ∀ {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]
      (T : SimpleGraph I), Fintype.card I = n → T.IsTree →
      ∀ (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
        (hs : Symmetric A R), Normalized A T μ R →
        ∀ i a, (∑ x, if x i = a then density A T μ R hs x else 0) = μ i a := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ A _ T hn hT μ R hs hnorm i a
    by_cases hsmall : Fintype.card I ≤ 1
    · let : Subsingleton I := Fintype.card_le_one_iff_subsingleton.mp hsmall
      let : Unique I := ⟨⟨i⟩, fun j => Subsingleton.elim j i⟩
      have hbot : T = ⊥ := Subsingleton.elim _ _
      have hd (x : (j : I) → A j) : density A T μ R hs x = μ i (x i) := by
        have he : T.edgeFinset = ∅ := by
          ext e
          induction e using Sym2.ind with
          | _ j k =>
            simp [Subsingleton.elim k j]
        simp only [density, he, Finset.prod_empty, mul_one, Fintype.prod_unique]
        rfl
      rw [← (Equiv.piUnique A).symm.sum_comp]
      simp [hd, Equiv.piUnique, uniqueElim]
    · let : Nontrivial I := Fintype.one_lt_card_iff_nontrivial.mp (lt_of_not_ge hsmall)
      obtain ⟨u,v,huv,hu,hv⟩ := hT.exists_ne_and_degree_eq_one
      have hex : ∃ l : I, l ≠ i ∧ T.degree l = 1 := by
        by_cases hui : u = i
        · exact ⟨v, fun hvi => huv (hui.trans hvi.symm), hv⟩
        · exact ⟨u,hui,hu⟩
      obtain ⟨l,hli,hl⟩ := hex
      obtain ⟨p,hlp,hp⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hl
      let S : Set I := {j | j ≠ l}
      have hT' : (T.induce S).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hl, hT.isAcyclic.induce S⟩
      have hc : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun j => j ∈ S) (x := l) (by simp [S])
      let i' : S := ⟨i,hli.symm⟩
      have hi := ih (Fintype.card S) hc (fun j : S => A j) (T.induce S) rfl hT'
        (fun j => μ j) (fun j k => R j k) (fun j k => hs j k) (hnorm.induce S) i' a
      have he := expectation_leaf A T μ R hs hnorm hlp hp
        (fun x => if x i' = a then (1:ℝ) else 0)
      simp only [mul_ite, mul_one, mul_zero] at he
      apply he.trans
      convert hi using 1
      apply Finset.sum_congr (by ext; simp)
      intro x hx
      congr 1

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Canonical root-independent tree density and exact one-node marginals.
Zero-mass states, deterministic edges and arbitrary finite state spaces allowed. -/
theorem tree_density (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (hn : Normalized A T μ R) :
    (∀ x, 0 ≤ density A T μ R hs x) ∧
    (∑ x, density A T μ R hs x) = 1 ∧
    ∀ i a, (∑ x, if x i = a then density A T μ R hs x else 0) = μ i a := by
  have hm := node_marginal_card (Fintype.card I) A T rfl hT μ R hs hn
  refine ⟨density_nonneg A T μ R hs hn, ?_, hm⟩
  obtain ⟨i⟩ := hT.connected.nonempty
  have ht : (∑ a : A i, ∑ x, if x i = a then density A T μ R hs x else 0) =
      ∑ x, density A T μ R hs x := by
    rw [Finset.sum_comm]
    simp
  rw [← ht]
  simp only [hm]
  exact hn.2.1 i

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma tree_path_mem_connected {I : Type*} (T : SimpleGraph I) (hT : T.IsTree)
    {S : Set I} (hS : (T.induce S).Connected) {a b v : I}
    (ha : a ∈ S) (hb : b ∈ S) (q : T.Walk a b) (hq : q.IsPath)
    (hv : v ∈ q.support) : v ∈ S := by
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨a, ha⟩ ⟨b, hb⟩
  let f := (SimpleGraph.Embedding.induce (G := T) S).toHom
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  have heq : p.map f = q := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path a b).elim ⟨p.map f, hp'⟩ ⟨q, hq⟩)
  have hmem : v ∈ (p.map f).support := heq.symm ▸ hv
  rw [SimpleGraph.Walk.support_map] at hmem
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
  exact hz ▸ z.property

/-- A proper connected subtree can be pruned from outside without altering it. -/
lemma exists_leaf_outside {I : Type*} [Fintype I] (T : SimpleGraph I) (hT : T.IsTree)
    (S : Set I) (hc : (T.induce S).Connected) (hproper : S ≠ Set.univ) :
    ∃ l : I, l ∉ S ∧ T.degree l = 1 := by
  obtain ⟨⟨r, hr⟩⟩ := hc.nonempty
  obtain ⟨v, hv⟩ : ∃ v, v ∉ S := by
    by_contra hn
    apply hproper
    ext v
    simp only [Set.mem_univ, iff_true]
    by_contra hv
    exact hn ⟨v,hv⟩
  obtain ⟨p, hp⟩ := hT.connected.exists_isPath r v
  let lengths : Set ℕ := {n | ∃ (l : I) (q : T.Walk r l),
    q.IsPath ∧ v ∈ q.support ∧ q.length = n}
  have hfin : lengths.Finite := Set.Finite.subset
    (Set.finite_le_nat (Fintype.card I)) (fun n ⟨l,q,hq,_,heq⟩ => heq ▸ hq.length_lt.le)
  obtain ⟨n, ⟨⟨l,q,hq,hvq,heq⟩, hmax⟩⟩ := hfin.exists_maximal
    ⟨p.length, ⟨v,p,hp,p.end_mem_support,rfl⟩⟩
  have hl : l ∉ S := fun hls => hv (tree_path_mem_connected T hT hc hr hls q hq hvq)
  have hnil : ¬ q.Nil := by
    intro hnil
    exact hl (hq.nil_iff_eq.mp hnil ▸ hr)
  refine ⟨l,hl,SimpleGraph.degree_eq_one_iff_existsUnique_adj.mpr
    ⟨q.penultimate, (q.adj_penultimate hnil).symm, ?_⟩⟩
  intro w hadj
  apply hT.isAcyclic.eq_penultimate_of_adj_end hq hadj
  by_contra hn
  have hqc : (q.concat hadj).IsPath := hq.concat hn hadj
  have hvc : v ∈ (q.concat hadj).support := by
    simp only [SimpleGraph.Walk.support_concat, List.mem_append, List.mem_singleton]
    exact Or.inl hvq
  have hm := hmax ⟨w,q.concat hadj,hqc,hvc,rfl⟩
  have he : (q.concat hadj).length = q.length + 1 := q.length_concat hadj
  omega

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

lemma edgeFinset_comap_equiv {I J : Type*} [Fintype I] [Fintype J]
    (T : SimpleGraph I) (e : J ≃ I) :
    T.edgeFinset = (T.comap e).edgeFinset.map e.toEmbedding.sym2Map := by
  have hg : (T.comap e).map e.toEmbedding = T := by
    ext i j
    simp only [SimpleGraph.map_adj]
    constructor
    · rintro ⟨a,b,hab,ha,hb⟩
      subst i
      subst j
      exact hab
    · intro hij
      exact ⟨e.symm i,e.symm j,by simpa using hij,e.apply_symm_apply i,e.apply_symm_apply j⟩
  have he := SimpleGraph.edgeFinset_map e.toEmbedding (T.comap e)
  calc
    T.edgeFinset = ((T.comap e).map e.toEmbedding).edgeFinset := by
      ext z
      simp only [SimpleGraph.mem_edgeFinset]

      rw [hg]
    _ = _ := he

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

lemma density_equiv
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {J : Type*} [Fintype J] (e : J ≃ I) (x : (i : I) → A i) :
    density A T μ R hs x =
      density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) (fun j => x (e j)) := by
  unfold density
  rw [← e.prod_comp (fun i => μ i (x i)), edgeFinset_comap_equiv T e,
    Finset.prod_map]
  congr 1
  apply Finset.prod_congr rfl
  intro z hz
  induction z using Sym2.ind with
  | _ i j => rfl

lemma expectation_surjective (T : SimpleGraph I) (μ : (i : I) → A i → ℝ)
    (R : (i j : I) → A i → A j → ℝ) (hs : Symmetric A R)
    {J : Type*} [Fintype J] (e : J ↪ I) (he : Function.Surjective e)
    (f : ((j : J) → A (e j)) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
      ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  let E : J ≃ I := Equiv.ofBijective e ⟨e.injective,he⟩
  calc
    _ = ∑ x : (i : I) → A i, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k))
          (fun j => x (e j)) * f (fun j => x (e j)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [density_equiv A T μ R hs E x]
      rfl
    _ = _ := by
      have hfun (x : (i : I) → A i) :
          (Equiv.piCongrLeft A E).symm x = (fun j => x (e j)) := by
        funext j
        exact Equiv.piCongrLeft_symm_apply A E x j
      have hv := (Equiv.piCongrLeft A E).symm.sum_comp
        (fun x => density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x)
      simp_rw [hfun] at hv
      convert hv using 1 ; apply Finset.sum_congr
        (by ext x; constructor <;> intro _ <;> exact Finset.mem_univ _) ;
        intro x hx ; rfl

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable

private theorem expectation_comap_card (n : ℕ) :
    ∀ {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]
      (T : SimpleGraph I), Fintype.card I = n → T.IsTree →
      ∀ (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
        (hs : Symmetric A R), Normalized A T μ R →
      ∀ {J : Type*} [Fintype J] (e : J ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : J) → A (e j)) → ℝ),
      (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
        ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I _ A _ T hn hT μ R hs hnorm J _ e hc f
    by_cases he : Function.Surjective e
    · exact expectation_surjective A T μ R hs e he f
    · have hc' : (T.induce (Set.range e)).Connected := by
        let hom : T.comap e →g T.induce (Set.range e) :=
          ⟨fun j => ⟨e j, ⟨j,rfl⟩⟩, fun h => h⟩
        apply hc.map hom
        rintro ⟨i,j,rfl⟩
        exact ⟨j,rfl⟩
      obtain ⟨l,hl,hd⟩ := exists_leaf_outside T hT (Set.range e) hc'
        (fun h => he (Set.range_eq_univ.mp h))
      obtain ⟨p,hlp,hp⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hd
      let K : Type _ := {i : I // i ≠ l}
      let e' : J ↪ K := ⟨fun j => ⟨e j, fun h => hl ⟨j,h⟩⟩,
        fun _ _ h => e.injective (congrArg Subtype.val h)⟩
      have hT' : (T.induce {i | i ≠ l}).IsTree :=
        ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hd,
          hT.isAcyclic.induce _⟩
      have hcard : Fintype.card K < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt (p := fun i => i ≠ l) (x := l) (by simp)
      have hnew := ih (Fintype.card K) hcard (fun i : K => A i)
        (T.induce {i | i ≠ l}) rfl hT' (fun i => μ i) (fun i j => R i j)
        (fun i j => hs i j) (hnorm.induce _) e' hc f
      have hold := expectation_leaf A T μ R hs hnorm hlp hp
        (fun x => f (fun j => x (e' j)))
      apply hold.trans
      convert hnew using 1 <;>
        apply Finset.sum_congr (by ext; simp) <;>
        intro x hx <;> congr 1

variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Exact connected-subtree marginal of the canonical junction law. In particular
this applies to a simple bag path, before projection to intersection assignments. -/
theorem expectation_comap (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (R : (i j : I) → A i → A j → ℝ)
    (hs : Symmetric A R) (hn : Normalized A T μ R)
    {J : Type*} [Fintype J] (e : J ↪ I) (hc : (T.comap e).Connected)
    (f : ((j : J) → A (e j)) → ℝ) :
    (∑ x, density A T μ R hs x * f (fun j => x (e j))) =
      ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
        (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) x * f x := by
  exact expectation_comap_card (Fintype.card I) A T rfl hT μ R hs hn e hc f

end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} [Fintype I] (A : I → Type*) [∀ i, Fintype (A i)]

/-- Interaction constructed from the actual local pair mass, not assumed. -/
noncomputable def interaction (μ : (i : I) → A i → ℝ)
    (J : (i j : I) → A i → A j → ℝ) (i j : I) (a : A i) (b : A j) : ℝ :=
  J i j a b / (μ i a * μ j b)

lemma interaction_symmetric
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (μ : (i : I) → A i → ℝ)
    (J : (i j : I) → A i → A j → ℝ) (hJ : Symmetric A J) :
    Symmetric A (interaction A μ J) := by
  intro i j a b
  simp only [interaction, hJ i j a b, mul_comm]

lemma interaction_normalized
    {I : Type treewidthLevel1} [Fintype I] (A : I → Type treewidthLevel2) [(i : I) → Fintype (A i)]
    (T : SimpleGraph I)
    (μ : (i : I) → A i → ℝ) (J : (i j : I) → A i → A j → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hs : Symmetric A J)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, (∑ b, J i j a b) = μ i a) :
    Normalized A T μ (interaction A μ J) := by
  refine ⟨hμ,hμ₁,?_,?_⟩
  · intro i j hij a b
    exact div_nonneg (hJ i j hij a b) (mul_nonneg (hμ i a) (hμ j b))
  · intro i j hij a ha
    have hz (b : A j) (hb : μ j b = 0) : J i j a b = 0 := by
      have he := hrow j i hij.symm b
      rw [hb] at he
      have hz' : J j i b a = 0 := (Finset.sum_eq_zero_iff_of_nonneg
        (fun c _ => hJ j i hij.symm b c)).mp he a (Finset.mem_univ _)
      rw [hs i j a b]
      exact hz'
    calc
      _ = ∑ b, J i j a b / μ i a := by
        apply Finset.sum_congr rfl
        intro b hb
        by_cases hb' : μ j b = 0
        · simp [interaction, hb', hz b hb']
        · dsimp [interaction]
          field_simp
      _ = (∑ b, J i j a b) / μ i a := (Finset.sum_div _ _ _).symm
      _ = 1 := by rw [hrow i j hij a, div_self ha]

/-- Canonical tree law from genuinely consistent adjacent pair distributions.
No positive lower bound on local state probabilities is imposed. -/
theorem coupling_tree (T : SimpleGraph I) (hT : T.IsTree)
    (μ : (i : I) → A i → ℝ) (J : (i j : I) → A i → A j → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hs : Symmetric A J)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, (∑ b, J i j a b) = μ i a) :
    let R := interaction A μ J
    let hR := interaction_symmetric A μ J hs
    (∀ x, 0 ≤ density A T μ R hR x) ∧
    (∑ x, density A T μ R hR x) = 1 ∧
    (∀ i a, (∑ x, if x i = a then density A T μ R hR x else 0) = μ i a) ∧
    ∀ {K : Type*} [Fintype K] (e : K ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : K) → A (e j)) → ℝ),
      (∑ x, density A T μ R hR x * f (fun j => x (e j))) =
        ∑ x, density (fun j => A (e j)) (T.comap e) (fun j => μ (e j))
          (fun j k => R (e j) (e k)) (fun j k => hR (e j) (e k)) x * f x := by
  dsimp only
  have hn := interaction_normalized A T μ J hμ hμ₁ hs hJ hrow
  obtain ⟨hnon,hprob,hmarg⟩ := tree_density A T hT μ (interaction A μ J)
    (interaction_symmetric A μ J hs) hn
  refine ⟨hnon,hprob,hmarg,?_⟩
  intro K _ e hc f
  exact expectation_comap A T hT μ (interaction A μ J)
    (interaction_symmetric A μ J hs) hn e hc f
end BoundedTreewidthL1.TreeMarkov

namespace BoundedTreewidthL1.MarkovFlow
abbrev History {r : ℕ} (L : Fin (r + 1) → Type*) := (i : Fin (r + 1)) → L i
/-- Same finite stochastic-product definition as the exact CKR obligation. -/
def IsMarkovLaw {r : ℕ} (L : Fin (r + 1) → Type*) [∀ i, Fintype (L i)]
    (μ : History L → ℝ) : Prop :=
  ∃ p : L 0 → ℝ, ∃ K : (i : Fin r) → L i.castSucc → L i.succ → ℝ,
    (∀ a, 0 ≤ p a) ∧ (∑ a, p a) = 1 ∧
    (∀ i a b, 0 ≤ K i a b) ∧ (∀ i a, (∑ b, K i a b) = 1) ∧
    ∀ x, μ x = p (x 0) * ∏ i : Fin r, K i (x i.castSucc) (x i.succ)
end BoundedTreewidthL1.MarkovFlow

namespace BoundedTreewidthL1.TreeMarkov
attribute [local instance] Classical.decEq Classical.propDecidable
variable {r : ℕ} (A : Fin (r+1) → Type*) [∀ i, Fintype (A i)]

def pathEdge (n : ℕ) : Fin n ↪ Sym2 (Fin (n+1)) where
  toFun i := s(i.castSucc,i.succ)
  inj' := by
    intro i j he
    rcases Sym2.eq_iff.mp he with h | h
    · apply Fin.ext
      exact congrArg (fun k : Fin (n+1) => k.val) h.1
    · have h₁ := congrArg Fin.val h.1
      have h₂ := congrArg Fin.val h.2
      simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
      omega

lemma path_edges (n : ℕ) :
    (SimpleGraph.pathGraph (n+1)).edgeFinset = Finset.univ.map (pathEdge n) := by
  ext e
  induction e using Sym2.ind with
  | _ i j =>
    rw [SimpleGraph.mem_edgeFinset]
    change (SimpleGraph.pathGraph (n+1)).Adj i j ↔ _
    rw [SimpleGraph.pathGraph_adj]
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro h
      rcases h with h | h
      · refine ⟨⟨i.val,by omega⟩,?_⟩
        change s((⟨i.val,_⟩ : Fin (n+1)),(⟨i.val+1,_⟩ : Fin (n+1))) = s(i,j)
        congr 1
        exact Fin.ext h
      · refine ⟨⟨j.val,by omega⟩,?_⟩
        apply Sym2.eq_iff.mpr
        right
        exact ⟨Fin.ext rfl, Fin.ext h⟩
    · rintro ⟨k,hk⟩
      change s(k.castSucc,k.succ) = s(i,j) at hk
      rcases Sym2.eq_iff.mp hk with hk | hk
      · left
        rw [← hk.1,← hk.2]
        rfl
      · right
        rw [← hk.1,← hk.2]
        rfl

lemma path_density
    {r : ℕ} (A : Fin (r + 1) → Type treewidthLevel1) [(i : Fin (r + 1)) → Fintype (A i)]
    (μ : (i : Fin (r+1)) → A i → ℝ)
    (R : (i j : Fin (r+1)) → A i → A j → ℝ) (hs : Symmetric A R)
    (x : (i : Fin (r+1)) → A i) :
    density A (SimpleGraph.pathGraph (r+1)) μ R hs x =
      (∏ i, μ i (x i)) * ∏ i : Fin r, R i.castSucc i.succ (x i.castSucc) (x i.succ) := by
  rw [density, path_edges, Finset.prod_map]
  rfl

lemma product_factorization (n : ℕ) (m : Fin (n+1) → ℝ)
    (q k : Fin n → ℝ)
    (hk : ∀ i, m i.castSucc ≠ 0 → k i = m i.succ * q i) :
    (∏ i, m i) * (∏ i, q i) = m 0 * ∏ i, k i := by
  induction n with
  | zero => simp
  | succ n ih =>
    let m' : Fin (n+1) → ℝ := fun i => m i.castSucc
    let q' : Fin n → ℝ := fun i => q i.castSucc
    let k' : Fin n → ℝ := fun i => k i.castSucc
    have hk' : ∀ i, m' i.castSucc ≠ 0 → k' i = m' i.succ * q' i := by
      intro i hi
      exact hk i.castSucc hi
    have hih := ih m' q' k' hk'
    rw [Fin.prod_univ_castSucc m, Fin.prod_univ_castSucc q, Fin.prod_univ_castSucc k]
    change ((∏ i, m' i) * m (Fin.last (n+1))) * ((∏ i, q' i) * q (Fin.last n)) =
      m' 0 * ((∏ i, k' i) * k (Fin.last n))
    by_cases hz : m' (Fin.last n) = 0
    · have hprod : (∏ i, m' i) = 0 := Finset.prod_eq_zero (Finset.mem_univ _) hz
      rw [hprod,zero_mul] at hih
      calc
        _ = 0 := by simp [hprod]
        _ = (m' 0 * ∏ i, k' i) * k (Fin.last n) := by rw [← hih,zero_mul]
        _ = _ := by ring
    · have hl := hk (Fin.last n) hz
      rw [hl]
      change ((∏ i, m' i) * m (Fin.last (n+1))) * ((∏ i, q' i) * q (Fin.last n)) =
        m' 0 * ((∏ i, k' i) * (m (Fin.last (n+1)) * q (Fin.last n)))
      calc
        _ = ((∏ i, m' i) * ∏ i, q' i) * (m (Fin.last (n+1)) * q (Fin.last n)) := by ring
        _ = _ := by rw [hih]; ring

/-- The canonical marginal on any simple bag-tree path is an actual Markov
product, not merely a collection of consistent adjacent marginals. -/
theorem path_markov (μ : (i : Fin (r+1)) → A i → ℝ)
    (R : (i j : Fin (r+1)) → A i → A j → ℝ) (hs : Symmetric A R)
    (hn : Normalized A (SimpleGraph.pathGraph (r+1)) μ R) :
    MarkovFlow.IsMarkovLaw A (density A (SimpleGraph.pathGraph (r+1)) μ R hs) := by
  let K : (i : Fin r) → A i.castSucc → A i.succ → ℝ := fun i a b =>
    if μ i.castSucc a = 0 then μ i.succ b else μ i.succ b * R i.castSucc i.succ a b
  have hadj (i : Fin r) : (SimpleGraph.pathGraph (r+1)).Adj i.castSucc i.succ :=
    SimpleGraph.pathGraph_adj.mpr (Or.inl rfl)
  refine ⟨μ 0,K,hn.1 0,hn.2.1 0,?_,?_,?_⟩
  · intro i a b
    dsimp [K]
    split_ifs
    · exact hn.1 _ _
    · exact mul_nonneg (hn.1 _ _) (hn.2.2.1 _ _ (hadj i) a b)
  · intro i a
    by_cases ha : μ i.castSucc a = 0
    · simpa [K,ha] using hn.2.1 i.succ
    · simpa [K,ha] using hn.2.2.2 _ _ (hadj i) a ha
  · intro x
    rw [path_density]
    apply product_factorization
    intro i hi
    simp [K,hi]
end BoundedTreewidthL1.TreeMarkov

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]
abbrev Local (B : I → Set V) := (i : I) → B i → Bool
noncomputable def assemble (B : I → Set V) (hcover : ∀ v, ∃ i, v ∈ B i)
    (x : Local B) : V → Bool := fun v =>
  x (Classical.choose (hcover v)) ⟨v,Classical.choose_spec (hcover v)⟩
noncomputable def restrict (B : I → Set V) (ω : V → Bool) : Local B :=
  fun _ v => ω v
noncomputable def globalMass (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R) (ω : V → Bool) : ℝ :=
  ∑ x : Local B, if assemble B hcover x = ω then TreeMarkov.density
    (fun i => B i → Bool) T μ R hs x else 0

lemma coherent_equal
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected) (x : Local B)
    (hx : ∀ i j, T.Adj i j → ∀ v hi hj, x i ⟨v,hi⟩ = x j ⟨v,hj⟩)
    (i j : I) (v : V) (hi : v ∈ B i) (hj : v ∈ B j) :
    x i ⟨v,hi⟩ = x j ⟨v,hj⟩ := by
  obtain ⟨p⟩ := hrun v ⟨i,hi⟩ ⟨j,hj⟩
  let val : {i | v ∈ B i} → Bool := fun a => x a ⟨v,a.2⟩
  change val ⟨i,hi⟩ = val ⟨j,hj⟩
  have he : ∀ {a b : {i | v ∈ B i}} (q : (T.induce {i | v ∈ B i}).Walk a b), val a = val b := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a b c hab q ih =>
      exact (hx a b hab v a.2 b.2).trans ih
  exact he p

lemma assemble_on_support (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩)
    (x : Local B) (hx : TreeMarkov.density (fun i => B i → Bool) T μ R hs x ≠ 0) :
    restrict B (assemble B hcover x) = x := by
  have he : ∀ i j, T.Adj i j → R i j (x i) (x j) ≠ 0 := by
    intro i j hij
    have hprod := (mul_ne_zero_iff.mp hx).2
    have hmem : s(i,j) ∈ T.edgeFinset := by simpa using hij
    exact Finset.prod_ne_zero_iff.mp hprod _ hmem
  have hco : ∀ i j, T.Adj i j → ∀ v hi hj, x i ⟨v,hi⟩ = x j ⟨v,hj⟩ :=
    fun i j hij => hcomp i j hij (x i) (x j) (he i j hij)
  funext i v
  exact coherent_equal T B hrun x hco _ i v _ v.2

lemma expectation_global (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R) (f : (V → Bool) → ℝ) :
    (∑ ω : V → Bool, globalMass T B hcover μ R hs ω * f ω) =
      ∑ x : Local B, TreeMarkov.density (fun i => B i → Bool) T μ R hs x *
        f (assemble B hcover x) := by
  simp only [globalMass, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul,zero_mul]
  simp

lemma expectation_local (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩) (f : Local B → ℝ) :
    (∑ ω : V → Bool, globalMass T B hcover μ R hs ω * f (restrict B ω)) =
      ∑ x : Local B, TreeMarkov.density (fun i => B i → Bool) T μ R hs x * f x := by
  rw [expectation_global]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hz : TreeMarkov.density (fun i => B i → Bool) T μ R hs x = 0
  · simp [hz]
  · rw [assemble_on_support T B hcover hrun μ R hs hcomp x hz]

/-- The canonical junction law is a genuine measure on global vertex labels,
with exact connected-subtree marginals. Compatibility is enforced by the local
edge support, never assumed for independently sampled bag states. -/
theorem global_bag_law (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hn : TreeMarkov.Normalized (fun i => B i → Bool) T μ R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩) :
    let ρ := globalMass T B hcover μ R hs
    (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = 1 ∧
    (∀ i a, (∑ ω : V → Bool, if restrict B ω i = a then ρ ω else 0) = μ i a) ∧
    ∀ {K : Type*} [Fintype K] (e : K ↪ I), (T.comap e).Connected →
      ∀ (f : ((j : K) → B (e j) → Bool) → ℝ),
      (∑ ω : V → Bool, ρ ω * f (fun j => restrict B ω (e j))) =
        ∑ x, TreeMarkov.density (fun j => B (e j) → Bool) (T.comap e)
          (fun j => μ (e j)) (fun j k => R (e j) (e k))
          (fun j k => hs (e j) (e k)) x * f x := by
  dsimp only
  obtain ⟨hnon,hprob,hmarg⟩ := TreeMarkov.tree_density (fun i => B i → Bool) T hT μ R hs hn
  refine ⟨?_,?_,?_,?_⟩
  · intro ω
    apply Finset.sum_nonneg
    intro x hx
    split_ifs
    · exact hnon x
    · exact le_rfl
  · have he := expectation_global T B hcover μ R hs (fun _ => 1)
    simpa using he.trans (by simpa using hprob)
  · intro i a
    have he := expectation_local T B hcover hrun μ R hs hcomp
      (fun x => if x i = a then 1 else 0)
    simp only [mul_ite,mul_one,mul_zero] at he
    apply he.trans
    convert hmarg i a using 1
    apply Finset.sum_congr rfl
    intro x hx
    split_ifs <;> rfl
  · intro K _ e hc f
    exact (expectation_local T B hcover hrun μ R hs hcomp
      (fun x => f (fun j => x (e j)))).trans
        (TreeMarkov.expectation_comap (fun i => B i → Bool) T hT μ R hs hn e hc f)
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1

/-- Pushforward mass at a point, for a finite real nonnegative measure. -/
noncomputable def marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (c : C) : ℝ := by
  classical
  exact ∑ a, if f a = c then μ a else 0

/-- The two-part conditional product, with zero denominator interpreted as zero.
Only compatible pairs receive mass. -/
noncomputable def glueWeights {A B C : Type*} [Fintype A]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (a : A) (b : B) : ℝ := by
  classical
  exact if f a = g b then μ a * ν b / marginal f μ (f a) else 0

end BoundedTreewidthL1

namespace BoundedTreewidthL1

lemma marginal_nonneg {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (c : C) :
    0 ≤ marginal f μ c := by
  classical
  exact Finset.sum_nonneg (fun a _ => by split_ifs <;> simp_all)

lemma le_marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (a : A) :
    μ a ≤ marginal f μ (f a) := by
  classical
  unfold marginal
  have := Finset.single_le_sum
    (s := Finset.univ) (f := fun b => if f b = f a then μ b else 0)
    (fun b _ => by split_ifs <;> simp_all) (Finset.mem_univ a)
  simpa using this

lemma weight_eq_zero_of_marginal_eq_zero {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (hμ : ∀ a, 0 ≤ μ a) (a : A)
    (hzero : marginal f μ (f a) = 0) : μ a = 0 := by
  have := le_marginal f μ hμ a
  exact le_antisymm (hzero ▸ this) (hμ a)

lemma glueWeights_nonneg {A B C : Type*} [Fintype A]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (a : A) (b : B) :
    0 ≤ glueWeights f g μ ν a b := by
  classical
  unfold glueWeights
  split_ifs
  · exact div_nonneg (mul_nonneg (hμ a) (hν b)) (marginal_nonneg f μ hμ _)
  · exact le_rfl

lemma glueWeights_row {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) (a : A) :
    (∑ b, glueWeights f g μ ν a b) = μ a := by
  classical
  have hform : (∑ b, glueWeights f g μ ν a b) =
      μ a * marginal g ν (f a) / marginal f μ (f a) := by
    simp only [marginal, Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    unfold glueWeights marginal
    by_cases h : f a = g b
    · simp only [h, ↓reduceIte]
    · simp [h, Ne.symm h]
  rw [hform, ← hconsistent]
  by_cases h : marginal f μ (f a) = 0
  · rw [h, weight_eq_zero_of_marginal_eq_zero f μ hμ a h]
    simp
  · exact mul_div_cancel_right₀ (μ a) h

lemma glueWeights_swap {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) (a : A) (b : B) :
    glueWeights f g μ ν a b = glueWeights g f ν μ b a := by
  classical
  unfold glueWeights
  by_cases h : f a = g b
  · simp [h, ← hconsistent, mul_comm]
  · simp [h, Ne.symm h]

theorem glueWeights_marginals {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hconsistent : ∀ c, marginal f μ c = marginal g ν c) :
    (∀ a b, 0 ≤ glueWeights f g μ ν a b) ∧
    (∀ a, (∑ b, glueWeights f g μ ν a b) = μ a) ∧
    (∀ b, (∑ a, glueWeights f g μ ν a b) = ν b) := by
  refine ⟨glueWeights_nonneg f g μ ν hμ hν, glueWeights_row f g μ ν hμ hconsistent, ?_⟩
  intro b
  simp_rw [glueWeights_swap f g μ ν hconsistent]
  exact glueWeights_row g f ν μ hν (fun c => (hconsistent c).symm) b

end BoundedTreewidthL1

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]
noncomputable def leftTrace (B : I → Set V) (i j : I) (a : B i → Bool) : ↥(B i ∩ B j) → Bool :=
  fun v => a ⟨v,v.2.1⟩
noncomputable def rightTrace (B : I → Set V) (i j : I) (b : B j → Bool) : ↥(B i ∩ B j) → Bool :=
  fun v => b ⟨v,v.2.2⟩
noncomputable def pairMass (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ) (i j : I) (a : B i → Bool) (b : B j → Bool) : ℝ :=
  if T.Adj i j then glueWeights (leftTrace B i j) (rightTrace B i j) (μ i) (μ j) a b else 0

lemma glueWeights_map {A B C D : Type*} [Fintype A]
    (f : A → C) (g : B → C) (E : C → D) (hE : Function.Injective E)
    (μ : A → ℝ) (ν : B → ℝ) (a : A) (b : B) :
    glueWeights (E ∘ f) (E ∘ g) μ ν a b = glueWeights f g μ ν a b := by
  simp [glueWeights,marginal,hE.eq_iff]

noncomputable def overlapSwap (B : I → Set V) (i j : I) :
    (↥(B i ∩ B j) → Bool) ≃ (↥(B j ∩ B i) → Bool) where
  toFun f v := f ⟨v,⟨v.2.2,v.2.1⟩⟩
  invFun f v := f ⟨v,⟨v.2.2,v.2.1⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

lemma pairMass_symmetric
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c) :
    TreeMarkov.Symmetric (fun i => B i → Bool) (pairMass T B μ) := by
  intro i j a b
  by_cases hij : T.Adj i j
  · simp only [pairMass,hij,T.adj_symm hij,↓reduceIte]
    rw [glueWeights_swap _ _ _ _ (hcons i j hij)]
    exact (glueWeights_map (rightTrace B i j) (leftTrace B i j)
      (overlapSwap B i j) (overlapSwap B i j).injective (μ j) (μ i) b a).symm
  · have hji : ¬T.Adj j i := fun h => hij h.symm
    simp [pairMass,hij,hji]

lemma pairMass_row
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (i j : I) (hij : T.Adj i j) (a : B i → Bool) :
    (∑ b, pairMass T B μ i j a b) = μ i a := by
  simp only [pairMass,hij,↓reduceIte]
  exact glueWeights_row _ _ _ _ (hμ i) (hcons i j hij) a

theorem bag_couplings (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    ∃ _ : TreeMarkov.Symmetric (fun i => B i → Bool) R,
      TreeMarkov.Normalized (fun i => B i → Bool) T μ R ∧
      ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
        ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩ := by
  dsimp only
  have hs := pairMass_symmetric T B μ hcons
  have hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ pairMass T B μ i j a b := by
    intro i j hij a b
    simp only [pairMass,hij,↓reduceIte]
    exact glueWeights_nonneg _ _ _ _ (hμ i) (hμ j) a b
  refine ⟨TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _ hs,
    TreeMarkov.interaction_normalized (fun i => B i → Bool) T μ _ hμ hμ₁ hs hJ
      (pairMass_row T B μ hμ hcons),?_⟩
  intro i j hij a b hn v hi hj
  have he : leftTrace B i j a = rightTrace B i j b := by
    by_contra he
    apply hn
    simp [TreeMarkov.interaction,pairMass,hij,glueWeights,he]
  exact congrFun he ⟨v,hi,hj⟩
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

def flip (A : Type*) : (A → Bool) ≃ (A → Bool) where
  toFun x := fun a => !(x a)
  invFun x := fun a => !(x a)
  left_inv x := by funext a; simp
  right_inv x := by funext a; simp

noncomputable def flipLocal (B : I → Set V) : Local B ≃ Local B where
  toFun x := fun i => flip (B i) (x i)
  invFun x := fun i => flip (B i) (x i)
  left_inv x := by funext i v; simp [flip]
  right_inv x := by funext i v; simp [flip]

lemma marginal_equivariant {A C : Type*} [Fintype A]
    (e : A ≃ A) (d : C ≃ C) (f : A → C) (μ : A → ℝ)
    (hμ : ∀ a, μ (e a) = μ a) (hf : ∀ a, f (e a) = d (f a)) (c : C) :
    marginal f μ (d c) = marginal f μ c := by
  unfold marginal
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [hf, hμ, d.injective.eq_iff]

lemma pairMass_flip
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a)
    (i j : I) (a : B i → Bool) (b : B j → Bool) :
    pairMass T B μ i j (flip (B i) a) (flip (B j) b) = pairMass T B μ i j a b := by
  have hl : ∀ a, leftTrace B i j (flip (B i) a) = flip ↥(B i ∩ B j) (leftTrace B i j a) := fun _ => rfl
  have hr : rightTrace B i j (flip (B j) b) = flip ↥(B i ∩ B j) (rightTrace B i j b) := rfl
  simp only [pairMass, glueWeights, hl, hr, (flip ↥(B i ∩ B j)).injective.eq_iff, hflip,
    marginal_equivariant (flip (B i)) (flip ↥(B i ∩ B j)) (leftTrace B i j) (μ i) (hflip i) hl]
  split_ifs <;> rfl

lemma density_flip (T : SimpleGraph I) (B : I → Set V)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) (x : Local B) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _
      (pairMass_symmetric T B μ hcons)
    TreeMarkov.density (fun i => B i → Bool) T μ R hs (flipLocal B x) =
      TreeMarkov.density (fun i => B i → Bool) T μ R hs x := by
  dsimp only
  unfold TreeMarkov.density
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    exact hflip i (x i)
  · apply Finset.prod_congr rfl
    intro e he
    induction e using Sym2.ind with
    | _ i j =>
      change pairMass T B μ i j (flip (B i) (x i)) (flip (B j) (x j)) /
        (μ i (flip (B i) (x i)) * μ j (flip (B j) (x j))) =
        pairMass T B μ i j (x i) (x j) / (μ i (x i) * μ j (x j))
      rw [pairMass_flip T B μ hflip, hflip, hflip]

theorem canonical_symmetric (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) :
    let R := TreeMarkov.interaction (fun i => B i → Bool) μ (pairMass T B μ)
    let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) μ _
      (pairMass_symmetric T B μ hcons)
    ∀ ω, globalMass T B hcover μ R hs (flip V ω) =
      globalMass T B hcover μ R hs ω := by
  dsimp only
  intro ω
  unfold globalMass
  rw [← (flipLocal B).sum_comp]
  apply Finset.sum_congr rfl
  intro x hx
  have he : assemble B hcover (flipLocal B x) = flip V (assemble B hcover x) := rfl
  simp only [he, (flip V).injective.eq_iff, density_flip T B μ hcons hflip]
end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1

noncomputable def cutDistance {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (u v : V) : ℝ :=
  ∑ a, if cut a u = cut a v then 0 else w a

/-- The coordinate function of a vertex in the finite weighted cut space. -/
noncomputable def finiteCutMap {V ι : Type*} (w : ι → ℝ)
    (cut : ι → V → Bool) (v : V) : PiLp (1 : ENNReal) (fun _ : ι => ℝ) :=
  WithLp.toLp 1 (fun a => if cut a v then w a else 0)

lemma finiteCutMap_norm_sub {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (hw : ∀ a, 0 ≤ w a) (u v : V) :
    ‖finiteCutMap w cut u - finiteCutMap w cut v‖ = cutDistance w cut u v := by
  rw [PiLp.norm_eq_of_L1]
  unfold cutDistance
  apply Finset.sum_congr rfl
  intro a _
  simp only [PiLp.sub_apply, finiteCutMap, Real.norm_eq_abs]
  cases hcu : cut a u <;> cases hcv : cut a v <;> simp [hw a, abs_of_nonneg, abs_neg]

theorem finite_cut_realization {V ι : Type*} [Fintype ι]
    (w : ι → ℝ) (cut : ι → V → Bool) (hw : ∀ a, 0 ≤ w a) :
    ∃ m : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
      ∀ u v, ‖F u - F v‖ = cutDistance w cut u v := by
  let e := LinearIsometryEquiv.piLpCongrLeft (1 : ENNReal) ℝ ℝ (Fintype.equivFin ι)
  refine ⟨Fintype.card ι, fun v => e (finiteCutMap w cut v), ?_⟩
  intro u v
  rw [← e.map_sub, e.norm_map]
  exact finiteCutMap_norm_sub w cut hw u v

end BoundedTreewidthL1

namespace BoundedTreewidthL1.BagLabels
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

lemma marginal_div {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (m : ℝ) (c : C) :
    marginal f (fun a => μ a / m) c = marginal f μ c / m := by
  unfold marginal
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

lemma marginal_mul {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (m : ℝ) (c : C) :
    marginal f (fun a => m * μ a) c = m * marginal f μ c := by
  unfold marginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

lemma global_path (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ)
    (R : (i j : I) → (B i → Bool) → (B j → Bool) → ℝ)
    (hs : TreeMarkov.Symmetric (fun i => B i → Bool) R)
    (hn : TreeMarkov.Normalized (fun i => B i → Bool) T μ R)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, R i j a b ≠ 0 →
      ∀ v hi hj, a ⟨v,hi⟩ = b ⟨v,hj⟩)
    (r : ℕ) (e : Fin (r+1) ↪ I) (he : T.comap e = SimpleGraph.pathGraph (r+1)) :
    MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
      (marginal (fun ω j => restrict B ω (e j)) (globalMass T B hcover μ R hs)) := by
  have hc : (T.comap e).Connected := he ▸ SimpleGraph.pathGraph_connected r
  have hsub := (global_bag_law T hT B hcover hrun μ R hs hn hcomp).2.2.2 e hc
  have hd : marginal (fun ω j => restrict B ω (e j)) (globalMass T B hcover μ R hs) =
      TreeMarkov.density (fun j => B (e j) → Bool) (T.comap e)
        (fun j => μ (e j)) (fun j k => R (e j) (e k)) (fun j k => hs (e j) (e k)) := by
    funext x
    have hh := hsub (fun y => if y = x then 1 else 0)
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte] at hh
    apply Eq.trans ?_ hh
    unfold marginal
    apply Finset.sum_congr rfl
    intro ω hω
    split_ifs <;> rfl
  rw [hd]
  have hn' : TreeMarkov.Normalized (fun j => B (e j) → Bool) (T.comap e)
      (fun j => μ (e j)) (fun j k => R (e j) (e k)) := by
    exact ⟨fun j => hn.1 (e j), fun j => hn.2.1 (e j),
      fun j k h => hn.2.2.1 (e j) (e k) h,
      fun j k h => hn.2.2.2 (e j) (e k) h⟩
  rw [he] at hn' ⊢
  exact TreeMarkov.path_markov _ _ _ _ hn'

/-- Exact common-positive-mass gluing and genuine finite real L1 realization,
from the actual local bag masses. The path assertion concerns full bag states;
separator-only projection is a further required transport obligation. -/
theorem canonical_gluing (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = m)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (μ i) c = marginal (rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (flip (B i) a) = μ i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = m ∧
      (∀ ω, ρ (flip V ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω => restrict B ω i) ρ a = μ i a) ∧
      (∀ (r : ℕ) (e : Fin (r+1) ↪ I), T.comap e = SimpleGraph.pathGraph (r+1) →
        MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
          (marginal (fun ω j => restrict B ω (e j)) (fun ω => ρ ω / m))) ∧
      ∃ n : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        ∀ u v, ‖F u - F v‖ = cutDistance ρ (fun ω => ω) u v := by
  let p : (i : I) → (B i → Bool) → ℝ := fun i a => μ i a / m
  have hp : ∀ i a, 0 ≤ p i a := fun i a => div_nonneg (hμ i a) hm.le
  have hp₁ : ∀ i, (∑ a, p i a) = 1 := by
    intro i
    simp only [p,← Finset.sum_div,hmass,div_self hm.ne']
  have hpcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c := by
    intro i j h c
    dsimp only [p]
    rw [marginal_div,marginal_div,hcons i j h]
  have hpflip : ∀ i a, p i (flip (B i) a) = p i a := by
    intro i a
    dsimp only [p]
    rw [hflip]
  let R := TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p)
  let hs := TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
    (pairMass_symmetric T B p hpcons)
  obtain ⟨hs',hn,hcomp⟩ := bag_couplings T B p hp hp₁ hpcons
  let q := globalMass T B hcover p R hs
  obtain ⟨hq,hq₁,hqmarg,hqsub⟩ := global_bag_law.{_,_,0} T hT B hcover hrun p R hs hn hcomp
  have hqflip : ∀ ω, q (flip V ω) = q ω := canonical_symmetric T B hcover p hpcons hpflip
  let ρ := fun ω => m * q ω
  have hρ : ∀ ω, 0 ≤ ρ ω := fun ω => mul_nonneg hm.le (hq ω)
  refine ⟨ρ,hρ,?_,?_,?_,?_,finite_cut_realization ρ (fun ω => ω) hρ⟩
  · change (∑ ω, m * q ω) = m
    rw [← Finset.mul_sum,hq₁,mul_one]
  · intro ω
    exact congrArg (m * ·) (hqflip ω)
  · intro i a
    change marginal _ (fun ω => m * q ω) a = _
    rw [marginal_mul]
    have hh : marginal (fun ω => restrict B ω i) q a = p i a := by
      apply Eq.trans ?_ (hqmarg i a)
      unfold marginal
      apply Finset.sum_congr rfl
      intro ω hω
      split_ifs <;> rfl
    rw [hh]
    exact mul_div_cancel₀ (μ i a) hm.ne'
  · intro r e he
    have hscale : (fun ω => ρ ω / m) = q := by
      funext ω
      exact mul_div_cancel_left₀ (q ω) hm.ne'
    rw [hscale]
    exact global_path T hT B hcover hrun p R hs hn hcomp r e he
end BoundedTreewidthL1.BagLabels

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma singleton_sum {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (S : Set A) :
    (∑ a, if a ∈ S then μ.real {a} else 0) = μ.real S := by
  classical
  rw [← Finset.sum_filter]
  rw [sum_measureReal_singleton]
  congr 1
  ext a
  simp

lemma measure_marginal {A D : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace D] [MeasurableSingletonClass D]
    (μ : Measure A) [IsFiniteMeasure μ] (f : A → D) (c : D) :
    marginal f (fun a => μ.real {a}) c = (μ.map f).real {c} := by
  classical
  unfold marginal
  rw [show (∑ a, if f a = c then μ.real {a} else 0) =
      μ.real {a | f a = c} from singleton_sum μ _]
  rw [map_measureReal_apply (measurable_of_finite f) (measurableSet_singleton c)]
  rfl

lemma real_sum {A : Type*} [MeasurableSpace A] (μ : J → Measure A)
    [∀ j, IsFiniteMeasure (μ j)] (S : Set A) :
    (∑ j, μ j).real S = ∑ j, (μ j).real S := by
  simp only [measureReal_def, Measure.finsetSum_apply]
  exact ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)

lemma symmetrize_mass
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) [IsFiniteMeasure μ] :
    (symmetrizeCut μ).real univ = μ.real univ := by
  rw [measureReal_def, symmetrizeCut, Measure.smul_apply, Measure.add_apply,
    Measure.map_apply measurable_complementCut MeasurableSet.univ]
  simp only [preimage_univ, smul_eq_mul]
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
  norm_num [measureReal_def]
  ring

lemma symmetrize_flip
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) :
    (symmetrizeCut μ).map complementCut = symmetrizeCut μ := by
  unfold symmetrizeCut
  rw [Measure.map_smul, Measure.map_add _ _ measurable_complementCut,
    Measure.map_map measurable_complementCut measurable_complementCut]
  have h : complementCut ∘ complementCut = (id : (V → Bool) → _) := by
    funext x
    exact complementCut_involutive x
  rw [h, Measure.map_id]
  rw [add_comm]

noncomputable def particleMeasure (M : ℝ) (F : J → V → ℝ) : Measure (V → Bool) :=
  ∑ j, symmetrizeCut (sweep M (F j))

instance particleMeasure_finite (M : ℝ) (F : J → V → ℝ) :
    IsFiniteMeasure (particleMeasure M F) := by
  unfold particleMeasure
  infer_instance

lemma particleTrace_eq
    {V : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype V] [Fintype J] [DecidableEq V]
    (M : ℝ) (F : J → V → ℝ) (P : Finset V) :
    particleTrace M F P = (particleMeasure M F).map (fun ω => fun v : P => ω v) := by
  unfold particleTrace particleMeasure cutTrace
  rw [Measure.map_finset_sum (measurable_of_finite _).aemeasurable]

instance particleTrace_finite (M : ℝ) (F : J → V → ℝ) (P : Finset V) :
    IsFiniteMeasure (particleTrace M F P) := by
  rw [particleTrace_eq]
  infer_instance

lemma particle_mass (M : ℝ) (hM : 0 ≤ M) (F : J → V → ℝ) :
    (particleMeasure M F).real univ = 2*(Fintype.card J : ℝ)*M := by
  rw [particleMeasure, real_sum]
  simp only [symmetrize_mass, sweep_total_mass M hM, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  ring

lemma particle_flip (M : ℝ) (F : J → V → ℝ) :
    (particleMeasure M F).map complementCut = particleMeasure M F := by
  unfold particleMeasure
  rw [Measure.map_finset_sum measurable_complementCut.aemeasurable]
  simp only [symmetrize_flip]

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma symmetrize_separation
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) [IsFiniteMeasure μ] (u v : V) :
    cutSeparation (symmetrizeCut μ) u v = cutSeparation μ u v := by
  unfold cutSeparation symmetrizeCut
  rw [measureReal_ennreal_smul_apply, measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut (Set.toFinite _).measurableSet]
  have h : complementCut ⁻¹' {ω : V → Bool | ω u ≠ ω v} = {ω | ω u ≠ ω v} := by
    ext ω
    simp [complementCut]
  rw [h]
  norm_num
  ring

lemma particle_separation (M : ℝ) (F : J → V → ℝ) (hF : ∀ j v, |F j v| ≤ M)
    (u v : V) : cutSeparation (particleMeasure M F) u v = ∑ j, |F j u - F j v| := by
  unfold cutSeparation particleMeasure
  rw [real_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact (symmetrize_separation (sweep M (F j)) u v).trans (sweep_separation M (F j) (hF j) u v)

lemma trace_mass (M : ℝ) (hM : 0 ≤ M) (F : J → V → ℝ) (P : Finset V) :
    (particleTrace M F P).real univ = 2*(Fintype.card J : ℝ)*M := by
  rw [particleTrace_eq, map_measureReal_apply (measurable_of_finite _) MeasurableSet.univ]
  simpa only [preimage_univ] using particle_mass M hM F

lemma trace_flip (M : ℝ) (F : J → V → ℝ) (P : Finset V) :
    (particleTrace M F P).map complementCut = particleTrace M F P := by
  rw [particleTrace_eq, Measure.map_map measurable_complementCut (measurable_of_finite _)]
  have h : complementCut ∘ (fun ω : V → Bool => fun v : P => ω v) =
      (fun ω : V → Bool => fun v : P => ω v) ∘ complementCut := rfl
  rw [h, ← Measure.map_map (measurable_of_finite _) measurable_complementCut, particle_flip]

lemma flip_point_mass
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    (μ : Measure (V → Bool)) (hs : μ.map complementCut = μ) (ω : V → Bool) :
    μ.real {complementCut ω} = μ.real {ω} := by
  conv_lhs => rw [← hs]
  rw [map_measureReal_apply measurable_complementCut (measurableSet_singleton _)]
  congr 1
  ext a
  simp only [mem_preimage, mem_singleton_iff]
  exact complementCut_involutive.injective.eq_iff

lemma marginal_test {A D : Type*} [Fintype A] [Fintype D]
    (f : A → D) (μ : A → ℝ) (h : D → ℝ) :
    (∑ c, marginal f μ c * h c) = ∑ a, μ a * h (f a) := by
  classical
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [ite_mul, zero_mul]
  simp

lemma separation_of_marginal (ρ : (V → Bool) → ℝ) (P : Finset V)
    (μ : Measure (P → Bool)) [IsFiniteMeasure μ]
    (h : ∀ a, marginal (fun ω : V → Bool => fun v : P => ω v) ρ a = μ.real {a})
    (u v : P) : cutDistance ρ (fun ω => ω) u.val v.val = cutSeparation μ u v := by
  have ht := marginal_test (fun ω : V → Bool => fun v : P => ω v) ρ
    (fun a => if a u = a v then 0 else 1)
  simp only [h, mul_ite, mul_zero, mul_one] at ht
  rw [cutDistance, ← ht]
  unfold cutSeparation
  have hs := singleton_sum μ {a | a u ≠ a v}
  simp only [mem_ofPred_eq, Classical.ite_not] at hs
  convert! hs using 1
  apply Finset.sum_congr rfl
  intro label _
  split_ifs <;> rfl

lemma trace_separation (M : ℝ) (F : J → V → ℝ) (P : Finset V) (u v : P) :
    cutSeparation (particleTrace M F P) u v = cutSeparation (particleMeasure M F) u.val v.val := by
  unfold cutSeparation
  rw [particleTrace_eq, map_measureReal_apply (measurable_of_finite _) (Set.toFinite _).measurableSet]
  rfl

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma overlapping_traces
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} {J : Type treewidthLevel3} [Fintype V]
    [Fintype I] [Fintype J] [DecidableEq V]
    (M : ℝ) (B : I → Finset V) (F : I → J → V → ℝ) (i j : I)
    (h : particleTrace M (F i) (B i ∩ B j) = particleTrace M (F j) (B i ∩ B j)) :
    ∀ c, marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j)
        (fun a => (particleTrace M (F i) (B i)).real {a}) c =
      marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j)
        (fun a => (particleTrace M (F j) (B j)).real {a}) c := by
  intro c
  have hl : marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j)
      (fun a => (particleTrace M (F i) (B i)).real {a}) c =
      ((particleTrace M (F i) (B i)).map (BagLabels.leftTrace (fun i => (B i : Set V)) i j)).real {c} := by
    convert! (measure_marginal (particleTrace M (F i) (B i))
      (BagLabels.leftTrace (fun i => (B i : Set V)) i j) c) using 1
  have hr : marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j)
      (fun a => (particleTrace M (F j) (B j)).real {a}) c =
      ((particleTrace M (F j) (B j)).map (BagLabels.rightTrace (fun i => (B i : Set V)) i j)).real {c} := by
    convert! (measure_marginal (particleTrace M (F j) (B j))
      (BagLabels.rightTrace (fun i => (B i : Set V)) i j) c) using 1
  rw [hl,hr]
  let E : ((B i ∩ B j : Finset V) → Bool) → (↥((B i : Set V) ∩ (B j : Set V)) → Bool) :=
    fun a v => a ⟨v.val, Finset.mem_inter.mpr v.property⟩
  have he (A : J → V → ℝ) :
      (particleTrace M A (B i ∩ B j)).map E =
      (particleMeasure M A).map (fun ω => fun v : ↥((B i : Set V) ∩ (B j : Set V)) => ω v) := by
    rw [particleTrace_eq, Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
    rfl
  have hh := congrArg (fun μ => μ.map E) h
  rw [he, he] at hh
  rw [particleTrace_eq, particleTrace_eq,
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    Measure.map_map (measurable_of_finite _) (measurable_of_finite _)]
  exact congrArg (fun μ => μ.real {c}) hh

lemma norm_bound_from_edges
    {V : Type treewidthLevel1} [Fintype V] [DecidableEq V]
    {E : Type*} [NormedAddCommGroup E]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ)
    (U : ℝ) (Φ : V → E)
    (he : ∀ u v (h : G.Adj u v), ‖Φ u - Φ v‖ ≤ U * ℓ ⟨s(u,v),h⟩) :
    ∀ u v, ‖Φ u - Φ v‖ ≤ U * shortestPathDistance G ℓ u v := by
  have hw {u v : V} (p : G.Walk u v) : ‖Φ u - Φ v‖ ≤ U * walkLength G ℓ p := by
    induction p with
    | nil => simp [walkLength]
    | @cons u v w huv p ih =>
      calc
        ‖Φ u - Φ w‖ ≤ ‖Φ u - Φ v‖ + ‖Φ v - Φ w‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
        _ ≤ U * ℓ ⟨s(u,v),huv⟩ + U * walkLength G ℓ p := add_le_add (he u v huv) ih
        _ = U * walkLength G ℓ (.cons huv p) := by rw [walkLength, mul_add]
  intro u v
  obtain ⟨p,hp,hlen⟩ := shortestPathDistance_attained G ℓ hG u v
  rw [← hlen]
  exact hw p

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I : Type*} [Fintype V] [Fintype I]

lemma gluing_without_path (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (μ : (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = m)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ i) c = marginal (BagLabels.rightTrace B i j) (μ j) c)
    (hflip : ∀ i a, μ i (BagLabels.flip (B i) a) = μ i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = m ∧
      (∀ ω, ρ (complementCut ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω => BagLabels.restrict B ω i) ρ a = μ i a) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        ∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v := by
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ⟩ :=
    BagLabels.canonical_gluing T hT B hcover hrun μ m hm hμ
      (by intro i; convert! hmass i using 1)
      (by intro i j hij c; convert! hcons i j hij c using 1) hflip
  exact ⟨ρ,hρ,hρmass,hρflip,hρlocal,n,Φ,hΦ⟩

end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

lemma glue_particle_measures (T : SimpleGraph I) (hT : T.IsTree) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (M : ℝ) (hM : 0 < M) (hN : 1 ≤ Fintype.card J) (F : I → J → V → ℝ)
    (hcons : ∀ i j, T.Adj i j → particleTrace M (F i) (B i ∩ B j) =
      particleTrace M (F j) (B i ∩ B j)) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = 2*(Fintype.card J : ℝ)*M ∧
      (∀ ω, ρ (complementCut ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω : V → Bool => fun v : B i => ω v) ρ a =
        (particleTrace M (F i) (B i)).real {a}) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        ∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v := by
  let μ : (i : I) → (B i → Bool) → ℝ :=
    fun i a => (particleTrace M (F i) (B i)).real {a}
  have hn : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hN
  have hm : 0 < 2*(Fintype.card J : ℝ)*M := by positivity
  have hmass : ∀ i, (∑ a, μ i a) = 2*(Fintype.card J : ℝ)*M := by
    intro i
    change (∑ a, (particleTrace M (F i) (B i)).real {a}) = _
    rw [sum_measureReal_singleton]
    simpa using trace_mass M hM.le (F i) (B i)
  have hcompat : ∀ i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j) (μ i) c =
      marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j) (μ j) c := by
    intro i j hij
    exact overlapping_traces M B F i j (hcons i j hij)
  have hflip : ∀ i a, μ i (BagLabels.flip (B i) a) = μ i a := by
    intro i a
    exact flip_point_mass (particleTrace M (F i) (B i)) (trace_flip M (F i) (B i)) a
  have hn_set : ∀ i, (∑ a : ↥((fun i => (B i : Set V)) i) → Bool, μ i a) =
      2*(Fintype.card J : ℝ)*M := by
    intro i
    convert! hmass i using 1
  have hμ : ∀ i a, 0 ≤ μ i a := by
    intro i a
    exact measureReal_nonneg
  generalize hdef : μ = μ' at hμ hmass hcompat hflip hn_set
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,n,Φ,hΦ⟩ :=
    gluing_without_path T hT (fun i => (B i : Set V)) hcover hrun
      μ' (2*(Fintype.card J : ℝ)*M) hm hμ
        (by intro i; convert! hn_set i using 1 ; congr 1 ; first | exact Subsingleton.elim _ _ | (ext; simp only [Finset.mem_univ]))
        (by intro i j hij c; convert! hcompat i j hij c using 1 <;> congr 1 <;> exact Subsingleton.elim _ _) hflip
  refine ⟨ρ,hρ,?_,hρflip,?_,n,Φ,?_⟩
  · convert! hρmass using 1 ; congr 1 ; first | exact Subsingleton.elim _ _ | (ext; simp only [Finset.mem_univ])
  · intro i a
    rw [← hdef] at hρlocal
    convert! hρlocal i a using 1 ; congr 1 ; exact Subsingleton.elim _ _
  · intro u v
    convert! hΦ u v using 1 ; congr 1 ; exact Subsingleton.elim _ _

theorem particle_law_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (hN : 1 ≤ Fintype.card J) (F : I → J → V → ℝ)
    (hF : ∀ i, FunctionParticleReachable (shortestPathDistance G ℓ) L H (F i))
    (hcons : ∀ i j, T.Adj i j →
      particleTrace (H*((Fintype.card J : ℝ)-1)+2*Δ) (F i) (B i ∩ B j) =
      particleTrace (H*((Fintype.card J : ℝ)-1)+2*Δ) (F j) (B i ∩ B j)) :
    let M := H*((Fintype.card J : ℝ)-1)+2*Δ
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = 2*(Fintype.card J : ℝ)*M ∧
      (∀ ω, ρ (complementCut ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω : V → Bool => fun v : B i => ω v) ρ a =
        (particleTrace M (F i) (B i)).real {a}) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v) ∧
        ∀ u v, ‖Φ u - Φ v‖ ≤
          (Fintype.card J : ℝ)*L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v := by
  dsimp only
  let M := H*((Fintype.card J : ℝ)-1)+2*Δ
  have hn : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hN
  have hM : 0 < M := by
    dsimp [M]
    have := mul_nonneg hH.le (sub_nonneg.mpr hn)
    linarith
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,n,Φ,hΦ⟩ :=
    glue_particle_measures T hT B hcover hrun M hM hN F hcons
  refine ⟨ρ,hρ,hρmass,hρflip,hρlocal,n,Φ,hΦ,?_⟩
  apply norm_bound_from_edges G hG ℓ _ Φ
  intro u v huv
  obtain ⟨i,hu,hv⟩ := hedge u v huv
  have hh : ∀ j x, |F i j x| ≤ M := by
    intro j x
    have := function_particles_height_bound hH (hF i) j x
    dsimp [M]
    linarith
  have hd := shortestPathDistance_pos G ℓ hG hℓ huv.ne
  have hsep : ‖Φ u - Φ v‖ = ∑ j, |F i j u - F i j v| := by
    rw [hΦ, separation_of_marginal ρ (B i) (particleTrace M (F i) (B i))
      (hρlocal i) ⟨u,hu⟩ ⟨v,hv⟩, trace_separation, particle_separation M (F i) hh]
  rw [hsep]
  have hsum : (∑ j, |F i j u - F i j v|) ≤
      (Fintype.card J : ℝ)*L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v := by
    calc
      (∑ j, |F i j u - F i j v|) ≤
          ∑ _ : J, L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v :=
        Finset.sum_le_sum (fun j _ => function_particles_difference_bound hL (hF i) j u v hd)
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
  apply hsum.trans
  apply mul_le_mul_of_nonneg_left ?_ (by positivity)
  have he := shortestPathDistance_le_walkLength G ℓ (fun e => (hℓ e).le) (huv.toWalk)
  simpa [SimpleGraph.Adj.toWalk, walkLength] using he
end BoundedTreewidthL1.ParticleLaws
namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)

noncomputable def path (i : I) : T.Walk i root :=
  (hT.connected.exists_path_of_dist i root).choose
lemma path_isPath (i : I) : (path T hT root i).IsPath :=
  (hT.connected.exists_path_of_dist i root).choose_spec.1
lemma path_length (i : I) : (path T hT root i).length = T.dist i root :=
  (hT.connected.exists_path_of_dist i root).choose_spec.2

lemma snd_closer {i : I} (hi : i ≠ root) :
    T.dist (path T hT root i).snd root < T.dist i root := by
  have hlen := (path T hT root i).length_tail_add_one
    (SimpleGraph.Walk.not_nil_of_ne hi)
  have hdist := SimpleGraph.dist_le (path T hT root i).tail
  rw [path_length] at hlen
  omega

noncomputable def forest : RootedForest I where
  parent i := if i = root then none else some (path T hT root i).snd
  depth i := T.dist i root
  decreases := by
    classical
    intro i p hp
    by_cases hi : i = root
    · simp only [hi, ite_eq_left] at hp
      contradiction
    · simp only [hi, ite_false, Option.some.injEq] at hp
      subst p
      exact snd_closer T hT root hi

lemma parent_adj {i p : I} (hp : (forest T hT root).parent i = some p) : T.Adj i p := by
  classical
  change (if i = root then none else some (path T hT root i).snd) = some p at hp
  by_cases hi : i = root
  · simp only [ite_eq_left hi] at hp
    contradiction
  · simp only [ite_eq_right hi] at hp
    cases Option.some.inj hp
    exact SimpleGraph.Walk.adj_snd (SimpleGraph.Walk.not_nil_of_ne hi)

lemma parent_of_closer {i j : I} (hij : T.Adj i j)
    (hd : T.dist j root + 1 = T.dist i root) :
    (forest T hT root).parent i = some j := by
  classical
  have hi : i ≠ root := by
    intro he; subst i
    simp only [SimpleGraph.dist_self] at hd
    omega
  let q : T.Walk i root := (path T hT root j).cons hij
  have hq : q.length = T.dist i root := by
    simpa only [q, SimpleGraph.Walk.length_cons, path_length, Nat.add_comm] using hd
  have he : q = path T hT root i :=
    congrArg Subtype.val ((hT.isAcyclic.subsingleton_path i root).elim
      ⟨q,q.isPath_of_length_eq_dist hq⟩ ⟨_,path_isPath T hT root i⟩)
  change (if i = root then none else some (path T hT root i).snd) = some j
  rw [ite_eq_right hi, ← he]
  simp only [q, SimpleGraph.Walk.snd_cons]

/-- Every actual tree edge is a parent-child edge of the depth-certified forest. -/
theorem edge_orientation {i j : I} (hij : T.Adj i j) :
    (forest T hT root).parent i = some j ∨ (forest T hT root).parent j = some i := by
  have hd := hT.dist_eq_dist_add_one_of_adj root hij
  rw [SimpleGraph.dist_comm (u := root) (v := i),
    SimpleGraph.dist_comm (u := root) (v := j)] at hd
  rcases hd with hd | hd
  · exact Or.inl (parent_of_closer T hT root hij hd.symm)
  · exact Or.inr (parent_of_closer T hT root hij.symm hd.symm)

end BoundedTreewidthL1.RootedTree
namespace BoundedTreewidthL1.BagLabels
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Ω V I : Type*} [MeasurableSpace Ω] [Fintype V] [Fintype I]

/-- Explicit prepared law: the pushforward of the normalized tree density,
using the actual overlap couplings, with the convention 0/0 = 0. -/
noncomputable def canonicalLaw (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (p : (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c) :
    (V → Bool) → ℝ :=
  globalMass T B hcover p
    (TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p))
    (TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
      (pairMass_symmetric T B p hcons))

lemma marginal_measurable {A C : Type*} [Fintype A]
    (f : A → C) (p : Ω → A → ℝ) (hp : ∀ a, Measurable (fun ξ => p ξ a)) (c : C) :
    Measurable (fun ξ => marginal f (p ξ) c) := by
  unfold marginal
  apply Finset.measurable_sum
  intro a ha
  by_cases he : f a = c
  · simpa only [he, ite_true] using hp a
  · simp only [he, ite_false]
    exact measurable_const

lemma pairMass_measurable
    {Ω : Type treewidthLevel1} {V : Type treewidthLevel2} {I : Type treewidthLevel3}
    [MeasurableSpace Ω] [Fintype V] [Fintype I]
    (T : SimpleGraph I) (B : I → Set V)
    (p : Ω → (i : I) → (B i → Bool) → ℝ)
    (hp : ∀ i a, Measurable (fun ξ => p ξ i a))
    (i j : I) (a : B i → Bool) (b : B j → Bool) :
    Measurable (fun ξ => pairMass T B (p ξ) i j a b) := by
  unfold pairMass glueWeights
  by_cases hij : T.Adj i j
  · simp only [hij, ite_true]
    by_cases hab : leftTrace B i j a = rightTrace B i j b
    · simp only [hab, ite_true]
      exact ((hp i a).mul (hp j b)).div
        (marginal_measurable (leftTrace B i j) (fun ξ => p ξ i) (hp i) _)
    · simp only [hab, ite_false]
      exact measurable_const
  · simp only [hij, ite_false]
    exact measurable_const

lemma canonicalLaw_measurable (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (p : Ω → (i : I) → (B i → Bool) → ℝ)
    (hcons : ∀ ξ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p ξ i) c = marginal (rightTrace B i j) (p ξ j) c)
    (hp : ∀ i a, Measurable (fun ξ => p ξ i a)) (ω : V → Bool) :
    Measurable (fun ξ => canonicalLaw T B hcover (p ξ) (hcons ξ) ω) := by
  unfold canonicalLaw globalMass
  apply Finset.measurable_sum
  intro x hx
  by_cases he : assemble B hcover x = ω
  · simp only [he, ite_true, TreeMarkov.density]
    apply Measurable.mul
    · exact Finset.measurable_prod _ (fun i hi => hp i (x i))
    · apply Finset.measurable_prod
      intro e he
      induction e using Sym2.ind with
      | _ i j =>
        simp only [TreeMarkov.edgeFactor_mk, TreeMarkov.interaction]
        exact (pairMass_measurable T B p hp i j (x i) (x j)).div
          ((hp i (x i)).mul (hp j (x j)))
  · simp only [he, ite_false]
    exact measurable_const

lemma canonicalLaw_normalized (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (p : (i : I) → (B i → Bool) → ℝ)
    (hp : ∀ i a, 0 ≤ p i a) (hp₁ : ∀ i, (∑ a, p i a) = 1)
    (hcons : ∀ i j, T.Adj i j → ∀ c,
      marginal (leftTrace B i j) (p i) c = marginal (rightTrace B i j) (p j) c) :
    (∀ ω, 0 ≤ canonicalLaw T B hcover p hcons ω) ∧
      (∑ ω, canonicalLaw T B hcover p hcons ω) = 1 := by
  obtain ⟨hs,hn,hcomp⟩ := bag_couplings T B p hp hp₁ hcons
  have hh := global_bag_law.{_,_,0} T hT B hcover hrun p
    (TreeMarkov.interaction (fun i => B i → Bool) p (pairMass T B p))
    (TreeMarkov.interaction_symmetric (fun i => B i → Bool) p _
      (pairMass_symmetric T B p hcons)) hn hcomp
  exact ⟨hh.1, hh.2.1⟩

end BoundedTreewidthL1.BagLabels

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
variable {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]

lemma trace_restrict (M : ℝ) (F : ι → V → ℝ) (P Q : Finset V) (h : Q ⊆ P) :
    (particleTrace M F P).map (fun a : P → Bool => fun v : Q => a ⟨v,h v.property⟩) =
      particleTrace M F Q := by
  rw [particleTrace_eq, Measure.map_map (measurable_of_finite _) (measurable_of_finite _),
    particleTrace_eq]
  rfl

lemma trace_eq_of_subset (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (h : Q ⊆ P)
    (he : particleTrace M F P = particleTrace M H P) :
    particleTrace M F Q = particleTrace M H Q := by
  rw [← trace_restrict M F P Q h, he, trace_restrict]
end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.TreeParticles
open ParticleLaws
variable {I V ι J : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J]

/-- The active-key preparation produces actual compatible global cut laws,
without assuming consistency of any sampled bag laws. -/
theorem tree_particle_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (B i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*shortestPathDistance G ℓ u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ interface (RootedTree.forest T hT root) B i, g i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let S := state (ι := ι) (RootedTree.forest T hT root) B A g
    ∃ ρ : (V → Bool) → ℝ,
      (∀ ω, 0 ≤ ρ ω) ∧ (∑ ω, ρ ω) = 2*(Fintype.card ι : ℝ)*M ∧
      (∀ ω, ρ (complementCut ω) = ρ ω) ∧
      (∀ i a, marginal (fun ω : V → Bool => fun v : B i => ω v) ρ a =
        (particleTrace M (S i).1 (B i)).real {a}) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v) ∧
        ∀ u v, ‖Φ u - Φ v‖ ≤
          (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v := by
  classical
  dsimp only
  let R := RootedTree.forest T hT root
  let S := state (ι := ι) R B A g
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  obtain ⟨hreach,htrace,-,-⟩ := forest_particle_realization R B A k q hbag hA hN
    (shortestPathDistance G ℓ) L H Δ hH hΔ g hLip hHeight hzero
  have hcons (i j : I) (hij : T.Adj i j) :
      particleTrace M (S i).1 (B i ∩ B j) = particleTrace M (S j).1 (B i ∩ B j) := by
    rcases RootedTree.edge_orientation T hT root hij with hp | hp
    · exact trace_eq_of_subset M _ _ (B j) _ Finset.inter_subset_right (htrace i j hp)
    · exact (trace_eq_of_subset M _ _ (B i) _ Finset.inter_subset_left (htrace j i hp)).symm
  have hN' : 1 ≤ Fintype.card ι := by omega
  exact particle_law_realization G hG ℓ hℓ T hT B hcover hedge hrun L H Δ hL hH hΔ
    hN' (fun i => (S i).1) (by
      have hd : (Classical.decEq ι) = (inferInstance : DecidableEq ι) := Subsingleton.elim _ _
      rw [hd]
      exact hreach) hcons
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I Ω : Type*} [Fintype V] [Fintype I] [MeasurableSpace Ω]

lemma marginal_integral {A D : Type*} [Fintype A] [Fintype D]
    (ν : Measure Ω) (f : A → D) (μ : Ω → A → ℝ)
    (h : ∀ a, Integrable (fun ω => μ ω a) ν) (b : D) :
    marginal f (fun a => ∫ ω, μ ω a ∂ν) b = ∫ ω, marginal f (μ ω) b ∂ν := by
  unfold marginal
  rw [integral_finsetSum _ (fun a _ => if hfa : f a = b then
    by simpa only [hfa,↓reduceIte] using h a else
    by simp only [hfa,↓reduceIte]; exact integrable_zero Ω ℝ ν)]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp

/-- Averaging local laws first preserves exactly the co-bag metric and produces
an actual Markov-glued global law, not a measurable choice of random globals. -/
theorem averaged_bag_realization (T : SimpleGraph I) (hT : T.IsTree) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (μ : Ω → (i : I) → (B i → Bool) → ℝ) (m : ℝ) (hm : 0 < m)
    (hμ : ∀ ω i a, 0 ≤ μ ω i a) (hmass : ∀ ω i, (∑ a, μ ω i a) = m)
    (hint : ∀ i a, Integrable (fun ω => μ ω i a) ν)
    (hcons : ∀ ω i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ ω i) c =
        marginal (BagLabels.rightTrace B i j) (μ ω j) c)
    (hflip : ∀ ω i a, μ ω i (BagLabels.flip (B i) a) = μ ω i a) :
    ∃ ρ : (V → Bool) → ℝ,
      (∀ a, 0 ≤ ρ a) ∧ (∑ a, ρ a) = m ∧
      (∀ a, ρ (complementCut a) = ρ a) ∧
      (∀ i a, marginal (fun ω => BagLabels.restrict B ω i) ρ a = ∫ ω, μ ω i a ∂ν) ∧
      (∀ (r : ℕ) (e : Fin (r+1) ↪ I), T.comap e = SimpleGraph.pathGraph (r+1) →
        MarkovFlow.IsMarkovLaw (fun j => B (e j) → Bool)
          (marginal (fun ω j => BagLabels.restrict B ω (e j)) (fun ω => ρ ω / m))) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ = cutDistance ρ (fun ω => ω) u v) ∧
        ∀ i (u v : B i), ‖Φ u.val - Φ v.val‖ =
          ∫ ω, (∑ a, if a u = a v then 0 else μ ω i a) ∂ν := by
  let μ' : (i : I) → (B i → Bool) → ℝ := fun i a => ∫ ω, μ ω i a ∂ν
  have hμ' : ∀ i a, 0 ≤ μ' i a := fun i a => integral_nonneg (fun ω => hμ ω i a)
  have hm' : ∀ i, (∑ a, μ' i a) = m := by
    intro i
    dsimp only [μ']
    rw [← integral_finsetSum _ (fun a _ => hint i a)]
    simp only [hmass,integral_const,probReal_univ,one_smul]
  have hc' : ∀ i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace B i j) (μ' i) c =
        marginal (BagLabels.rightTrace B i j) (μ' j) c := by
    intro i j hij c
    rw [marginal_integral ν _ _ (hint i),marginal_integral ν _ _ (hint j)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun ω => hcons ω i j hij c)
  have hf' : ∀ i a, μ' i (BagLabels.flip (B i) a) = μ' i a := by
    intro i a
    exact integral_congr_ae (Filter.Eventually.of_forall (fun ω => hflip ω i a))
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ⟩ :=
    BagLabels.canonical_gluing T hT B hcover hrun μ' m hm hμ' hm' hc' hf'
  refine ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ,?_⟩
  intro i u v
  rw [hΦ]
  have ht := marginal_test (fun ω => BagLabels.restrict B ω i) ρ
    (fun a => if a u = a v then (0:ℝ) else 1)
  simp only [hρlocal,mul_ite,mul_zero,mul_one] at ht
  have he : cutDistance ρ (fun ω => ω) u.val v.val =
      ∑ a, if a u = a v then 0 else μ' i a := by
    rw [ht]
    rfl
  rw [he]
  rw [integral_finsetSum _ (fun a _ => if hab : a u = a v then
    by simp only [hab,↓reduceIte]; exact integrable_const 0 else
    by simpa only [hab,↓reduceIte] using hint i a)]
  apply Finset.sum_congr rfl
  intro a ha
  split_ifs <;> simp [μ']

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J Ω : Type*} [Fintype V] [Fintype I] [Fintype J]
  [DecidableEq V] [MeasurableSpace Ω]

/-- Realization of the averaged prepared particle laws, with exact local
average gaps. Neither global random-law choice nor global consistency is
postulated. This interface applies to the actual measurable tree preparation. -/
theorem averaged_particle_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (hN : 1 ≤ Fintype.card J) (F : Ω → I → J → V → ℝ)
    (hmeas : ∀ i j v, Measurable (fun ω => F ω i j v))
    (hF : ∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) L H (F ω i))
    (hcons : ∀ ω i j, T.Adj i j →
      particleTrace (H*((Fintype.card J : ℝ)-1)+2*Δ) (F ω i) (B i ∩ B j) =
      particleTrace (H*((Fintype.card J : ℝ)-1)+2*Δ) (F ω j) (B i ∩ B j)) :
    ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      (∀ u v, ‖Φ u - Φ v‖ ≤
        (Fintype.card J : ℝ)*L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v) ∧
      ∀ i (u v : B i), ‖Φ u.val - Φ v.val‖ = ∫ ω, (∑ j, |F ω i j u - F ω i j v|) ∂ν := by
  let : Nonempty J := Fintype.card_pos_iff.mp (by omega)
  let : MeasurableSpace J := ⊤
  let : MeasurableSingletonClass J := ⟨fun _ => trivial⟩
  let M := H*((Fintype.card J : ℝ)-1)+2*Δ
  have hn : (1 : ℝ) ≤ Fintype.card J := by exact_mod_cast hN
  have hM : 0 < M := by
    dsimp [M]
    have := mul_nonneg hH.le (sub_nonneg.mpr hn)
    linarith
  let μ : Ω → (i : I) → (B i → Bool) → ℝ :=
    fun ω i a => (particleTrace M (F ω i) (B i)).real {a}
  have hm : 0 < 2*(Fintype.card J : ℝ)*M := by positivity
  have hmass : ∀ ω i, (∑ a, μ ω i a) = 2*(Fintype.card J : ℝ)*M := by
    intro ω i
    dsimp only [μ]
    rw [sum_measureReal_singleton]
    simpa only [Finset.coe_univ] using trace_mass M hM.le (F ω i) (B i)
  have hi : ∀ i a, Integrable (fun ω => μ ω i a) ν := by
    intro i a
    exact ParticleSchedule.integrable_particleTrace_real M hM.le (fun ω => F ω i) (hmeas i) (B i) {a} ν
  have hc : ∀ ω i j, T.Adj i j → ∀ c,
      marginal (BagLabels.leftTrace (fun i => (B i : Set V)) i j) (μ ω i) c =
      marginal (BagLabels.rightTrace (fun i => (B i : Set V)) i j) (μ ω j) c := by
    intro ω i j hij
    exact overlapping_traces M B (F ω) i j (hcons ω i j hij)
  have hf : ∀ ω i a, μ ω i (BagLabels.flip (B i) a) = μ ω i a := by
    intro ω i a
    exact flip_point_mass (particleTrace M (F ω i) (B i)) (trace_flip M (F ω i) (B i)) a
  have hn_set : ∀ ω i, (∑ a : ↥((fun i => (B i : Set V)) i) → Bool, μ ω i a) =
      2*(Fintype.card J : ℝ)*M := by
    intro ω i
    convert! hmass ω i using 1
  have hμ : ∀ ω i a, 0 ≤ μ ω i a := by intro ω i a; exact measureReal_nonneg
  generalize hdef : μ = μ' at hμ hmass hc hf hi hn_set
  obtain ⟨ρ,hρ,hρmass,hρflip,hρlocal,hρpath,n,Φ,hΦ,hlocal⟩ :=
    averaged_bag_realization T hT (fun i => (B i : Set V)) hcover hrun ν μ'
      (2*(Fintype.card J : ℝ)*M) hm hμ
      (by intro ω i; convert! hn_set ω i using 1 ; congr 1 ; first | exact Subsingleton.elim _ _ | (ext; simp only [Finset.mem_univ]))
      hi (by intro ω i j hij c; convert! hc ω i j hij c using 1 <;> congr 1 <;> exact Subsingleton.elim _ _) hf
  have hheight (ω : Ω) (i : I) (j : J) (v : V) : |F ω i j v| ≤ M := by
    have := function_particles_height_bound hH (hF ω i) j v
    dsimp [M]
    linarith
  have heq : ∀ i (u v : B i), ‖Φ u.val - Φ v.val‖ =
      ∫ ω, (∑ j, |F ω i j u - F ω i j v|) ∂ν := by
    intro i u v
    rw [hlocal,← hdef]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro ω
    dsimp only [μ]
    have hx : (∑ a : B i → Bool,
        if a u = a v then 0 else (particleTrace M (F ω i) (B i)).real {a}) =
        ∑ j, |F ω i j u - F ω i j v| := by
      have hs := singleton_sum (particleTrace M (F ω i) (B i)) {a | a u ≠ a v}
      simp only [Set.mem_ofPred_eq, Classical.ite_not] at hs
      have heq : (∑ a : B i → Bool,
          if a u = a v then 0 else (particleTrace M (F ω i) (B i)).real {a}) =
          (particleTrace M (F ω i) (B i)).real {a | a u ≠ a v} := by
        convert! hs using 1
        apply Finset.sum_congr rfl
        intro label _
        split_ifs <;> rfl
      rw [heq]
      change cutSeparation (particleTrace M (F ω i) (B i)) u v = _
      rw [trace_separation,particle_separation M (F ω i) (hheight ω i)]
    convert! hx using 1 ; congr 1 ; first | exact Subsingleton.elim _ _ | (ext; simp only [Finset.mem_univ])
  refine ⟨n,Φ,?_,heq⟩
  apply norm_bound_from_edges G hG ℓ _ Φ
  intro u v huv
  obtain ⟨i,hu,hv⟩ := hedge u v huv
  rw [heq i ⟨u,hu⟩ ⟨v,hv⟩]
  have hsum (ω : Ω) : (∑ j, |F ω i j u - F ω i j v|) ≤
      (Fintype.card J : ℝ)*L*((Fintype.card J : ℝ)-1)*ℓ ⟨s(u,v),huv⟩ := by
    have hd := shortestPathDistance_pos G ℓ hG hℓ huv.ne
    calc
      (∑ j, |F ω i j u - F ω i j v|) ≤
          ∑ j : J, L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v :=
        Finset.sum_le_sum (fun j _ => function_particles_difference_bound hL (hF ω i) j u v hd)
      _ = (Fintype.card J : ℝ)*L*((Fintype.card J : ℝ)-1)*shortestPathDistance G ℓ u v := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have he := shortestPathDistance_le_walkLength G ℓ (fun e => (hℓ e).le) huv.toWalk
        simpa [SimpleGraph.Adj.toWalk,walkLength] using he
  apply (le_abs_self _).trans
  change ‖∫ ω, (∑ j, |F ω i j u - F ω i j v|) ∂ν‖ ≤ _
  have hb := norm_integral_le_of_norm_le_const (μ := ν)
    (Filter.Eventually.of_forall (fun ω => show ‖∑ j, |F ω i j u - F ω i j v|‖ ≤ _ from by
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
      exact hsum ω))
  simpa only [probReal_univ,mul_one] using hb
end BoundedTreewidthL1.ParticleLaws

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

noncomputable def retained (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  (R.parent i).elim ∅ (fun p => A i ∩ A p)
noncomputable def fresh (R : RootedForest I) (A : I → Finset J) (i : I) : Finset J :=
  A i \ retained R A i
noncomputable def seed : (ι → V → ℝ) × (J → ι × ι) :=
  (fun _ _ => 0, fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))
noncomputable def step (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (S : (ι → V → ℝ) × (J → ι × ι)) :=
  launchBatch (bag i) (fresh R A i).toList (retained R A i) S.1 S.2 (g i)
noncomputable def state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) : (ι → V → ℝ) × (J → ι × ι) :=
  R.run seed (step R bag A g) i

lemma retained_subset (R : RootedForest I) (A : I → Finset J) (i : I) :
    retained R A i ⊆ A i := by
  unfold retained
  cases R.parent i with
  | none => exact Finset.empty_subset _
  | some p => exact Finset.inter_subset_left

lemma batch_data (R : RootedForest I) (A : I → Finset J) (i : I)
    {q : ℕ} (hA : (A i).card ≤ q) :
    (fresh R A i).toList.Nodup ∧
    (∀ a ∈ (fresh R A i).toList, a ∉ retained R A i) ∧
    (retained R A i ∪ (fresh R A i).toList.toFinset).card ≤ q := by
  classical
  refine ⟨Finset.nodup_toList _, ?_, ?_⟩
  · intro a ha
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp ha)).2
  · simpa only [Finset.toList_toFinset, fresh,
      Finset.union_sdiff_of_subset (retained_subset R A i)] using hA

lemma state_eq
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {J : Type treewidthLevel4} [Fintype V] [Fintype ι] [Nonempty ι] [DecidableEq ι] [DecidableEq J]
    (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) :
    state (ι := ι) R bag A g i = step R bag A g i
      ((R.parent i).elim seed (state R bag A g)) := RootedForest.run_eq _ _ _ _
/-- Actual branching preparation for anchor keys, launched at their own bag. Children use their own
copies of the parent's list; no consistency assumption on sampled bag laws. -/
theorem forest_particle_realization (R : RootedForest I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ bag i, g i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let S := state (ι := ι) R bag A g
    (∀ i, FunctionParticleReachable d L H (S i).1) ∧
    (∀ i p, R.parent i = some p →
      particleTrace M (S i).1 (bag i) = particleTrace M (S p).1 (bag i)) ∧
    (∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) ∧
    (∀ i a, a ∈ fresh R A i →
      ((S i).2 a).1 ≠ ((S i).2 a).2 ∧
      ∀ v, (S i).1 ((S i).2 a).1 v - (S i).1 ((S i).2 a).2 v = 2*g i a v) := by
  classical
  dsimp only
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  let S := state (ι := ι) R bag A g
  have hstep (i : I) (F : ι → V → ℝ) (p : J → ι × ι)
      (hF : FunctionParticleReachable d L H F) :=
    launchBatch_correct k q hN (bag i) (hbag i)
      (fresh R A i).toList (retained R A i)
      (batch_data R A i (hA i)).1 (batch_data R A i (hA i)).2.1
      (batch_data R A i (hA i)).2.2 d L H Δ hH hΔ F p hF (g i)
      (fun a _ => hLip i a) (fun a _ => hHeight i a) (fun a _ => hzero i a)
  have hreach : ∀ i, FunctionParticleReachable d L H (S i).1 := by
    apply R.run_invariant seed (step R bag A g) (fun S => FunctionParticleReachable d L H S.1)
    · exact FunctionParticleReachable.zero
    · intro i F hF
      exact (hstep i F.1 F.2 hF).1
  have hinput (i : I) : FunctionParticleReachable d L H
      ((R.parent i).elim seed S).1 := by
    cases hp : R.parent i with
    | none => exact FunctionParticleReachable.zero
    | some p => exact hreach p
  have hstate (i : I) :
      launchBatch (bag i) (fresh R A i).toList (retained R A i)
        ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 (g i) = S i :=
    (state_eq R bag A g i).symm
  refine ⟨hreach, ?_, ?_, ?_⟩
  · intro i p hp
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.1
    rw [hstate] at hj
    simpa only [hp, Option.elim_some] using hj
  · intro i p hp a ha
    have hj := hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)
    dsimp only at hj
    rw [hstate] at hj
    have hm : a ∈ retained R A i := by simpa only [retained, hp, Option.elim_some] using ha
    have he := hj.2.2.1 a hm
    have hleft := hj.2.2.2.1 _ (first_mem_used hm ((R.parent i).elim seed S).2)
    have hright := hj.2.2.2.1 _ (second_mem_used hm ((R.parent i).elim seed S).2)
    have he' : (S i).2 a = (S p).2 a := by
      simpa only [hp, Option.elim_some] using he
    refine ⟨he', ?_, ?_⟩
    · rw [he']
      simpa only [hp, Option.elim_some] using hleft
    · rw [he']
      simpa only [hp, Option.elim_some] using hright
  · intro i a ha
    have hj := (hstep i ((R.parent i).elim seed S).1
      ((R.parent i).elim seed S).2 (hinput i)).2.2.2.2 a (Finset.mem_toList.mpr ha)
    rw [hstate] at hj
    exact hj
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleSchedule ParticleBatch
variable {I V ι J Ω : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]

/-- Measurability of the actual branching preparation, with all randomness
sampled beforehand. No measurable-choice assumption about the particle lists. -/
theorem measurable_state (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : Ω → I → J → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (i : I) :
    Measurable (fun ω => state (ι := ι) R bag A (g ω) i) := by
  apply R.run_measurable (fun _ => seed) (fun j ω S => step R bag A (g ω) j S)
    measurable_const
  intro j f hf
  exact measurable_launchBatch (bag j) (fresh R A j).toList (retained R A j)
    (fun ω => (f ω).1) (fun ω => (f ω).2) (fun ω => g ω j)
    (fun a v => (measurable_pi_apply v).comp ((measurable_pi_apply a).comp hf.fst))
    (fun a => (measurable_pi_apply a).comp hf.snd) (hg j)

end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
variable {I J X : Type*} [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- The discrete launch location depends only on the rooted decomposition and
active keys. In particular it does not consult any preparatory randomness. -/
noncomputable def origin (R : RootedForest I) (A : I → Finset J) (root : I) : I → J → I :=
  R.run (fun _ => root) (fun i old a => if a ∈ retained R A i then old a else i)

lemma origin_eq (R : RootedForest I) (A : I → Finset J) (root i : I) (a : J) :
    origin R A root i a = if a ∈ retained R A i then
      ((R.parent i).elim (fun _ => root) (origin R A root)) a else i := by
  unfold origin
  rw [RootedForest.run_eq]

lemma origin_fresh (R : RootedForest I) (A : I → Finset J) (root i : I)
    (a : J) (ha : a ∈ A i) : a ∈ fresh R A (origin R A root i a) := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A p := (Finset.mem_inter.mp (by simpa [retained,hp] using hk)).2
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p hap rfl
    · rw [ite_eq_right hk]
      exact Finset.mem_sdiff.mpr ⟨ha,hk⟩

lemma origin_transport (R : RootedForest I) (A : I → Finset J) (root : I)
    (E : I → J → X)
    (hkeep : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p, E i a = E p a)
    (i : I) (a : J) (ha : a ∈ A i) : E i a = E (origin R A root i a) a := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A i ∩ A p := by simpa [retained,hp] using hk
        exact (hkeep i p hp a hap).trans
          (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p
            (Finset.mem_inter.mp hap).2 rfl)
    · rw [ite_eq_right hk]
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.AnchorTreeParticles
open scoped BigOperators
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

lemma two_particle_difference
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (F : ι → V → ℝ) (a b : ι) (hab : a ≠ b)
    (g : V → ℝ) (hgap : ∀ v, F a v - F b v = 2*g v) (u v : V) :
    2*|g u-g v| ≤ ∑ t, |F t u-F t v| := by
  have hs : (∑ t ∈ ({a,b} : Finset ι), |F t u-F t v|) ≤ ∑ t, |F t u-F t v| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => abs_nonneg _)
  simp only [Finset.sum_pair hab] at hs
  have he : (F a u-F a v)-(F b u-F b v) = 2*(g u-g v) := by
    linarith [hgap u,hgap v]
  have ha := abs_sub (F a u-F a v) (F b u-F b v)
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  exact ha.trans hs

/-- The actual active pair at any descendant supplies the original launch
separation. The origin is deterministic, so no conditioning on the particle
scheduler or sampled coefficients is required. -/
theorem origin_particle_gap (R : RootedForest I) (root : I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ bag i, g i a v = 0)
    (i : I) (a : J) (ha : a ∈ A i) (u v : V) :
    2*|g (origin R A root i a) a u - g (origin R A root i a) a v| ≤
      ∑ t, |(state (ι := ι) R bag A g i).1 t u -
        (state (ι := ι) R bag A g i).1 t v| := by
  let S := state (ι := ι) R bag A g
  let o := origin R A root i a
  obtain ⟨hreach,htrace,hkeep,hnew⟩ := forest_particle_realization R bag A k q
    hbag hA hN d L H Δ hH hΔ g hLip hHeight hzero
  have hp : (S i).2 a = (S o).2 a :=
    origin_transport R A root (fun i a => (S i).2 a)
      (fun i p hip a ha => (hkeep i p hip a ha).1) i a ha
  have hl : (S i).1 ((S i).2 a).1 = (S o).1 ((S o).2 a).1 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).1)
      (fun i p hip a ha => (hkeep i p hip a ha).2.1) i a ha
  have hr : (S i).1 ((S i).2 a).2 = (S o).1 ((S o).2 a).2 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).2)
      (fun i p hip a ha => (hkeep i p hip a ha).2.2) i a ha
  have hn := hnew o a (origin_fresh R A root i a ha)
  apply two_particle_difference (S i).1 ((S i).2 a).1 ((S i).2 a).2
    (by rw [hp]; exact hn.1) (g o a) ?_ u v
  intro x
  rw [hl,hr]
  exact hn.2 x
end BoundedTreewidthL1.AnchorTreeParticles
namespace BoundedTreewidthL1.AnchorTreeParticles
open MeasureTheory ParticleLaws
open scoped BigOperators ENNReal
variable {I V ι J Ω : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]

/-- Actual global averaged L1 realization of the branching preparation, with
an unconditional integral lower bound from each deterministic active origin. -/
theorem averaged_origin_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (B i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → I → J → V → ℝ) (hmeas : ∀ i a v, Measurable (fun ω => g ω i a v))
    (hLip : ∀ ω i a, ∀ u v, |g ω i a u - g ω i a v| ≤ L*shortestPathDistance G ℓ u v)
    (hHeight : ∀ ω i a v, |g ω i a v| ≤ H)
    (hzero : ∀ ω i a, ∀ v ∈ B i, g ω i a v = 0) :
    ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      (∀ u v, ‖Φ u - Φ v‖ ≤
        (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v) ∧
      ∀ i (a : J), a ∈ A i → ∀ (u v : B i),
        2*(∫ ω, |g ω (origin (RootedTree.forest T hT root) A root i a) a u -
          g ω (origin (RootedTree.forest T hT root) A root i a) a v| ∂ν) ≤
          ‖Φ u.val - Φ v.val‖ := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := ι) R B A (g ω)
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  have hreach : ∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) L H (S ω i).1 := by
    intro ω
    exact (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).1
  have hsmeas : ∀ i t v, Measurable (fun ω => (S ω i).1 t v) := by
    intro i t v
    exact (measurable_pi_apply v).comp ((measurable_pi_apply t).comp
      (measurable_state R B A g hmeas i).fst)
  have hcons : ∀ ω i j, T.Adj i j →
      particleTrace M (S ω i).1 (B i ∩ B j) = particleTrace M (S ω j).1 (B i ∩ B j) := by
    intro ω i j hij
    have ht := (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).2.1
    rcases RootedTree.edge_orientation T hT root hij with hp | hp
    · exact trace_eq_of_subset M _ _ (B i) _ Finset.inter_subset_left (ht i j hp)
    · exact (trace_eq_of_subset M _ _ (B j) _ Finset.inter_subset_right (ht j i hp)).symm
  obtain ⟨n,Φ,hup,heq⟩ := averaged_particle_realization G hG ℓ hℓ T hT B hcover hedge hrun
    ν L H Δ hL hH hΔ (by omega : 1 ≤ Fintype.card ι) (fun ω i => (S ω i).1)
    hsmeas (by
      have hd : (Classical.decEq ι) = (inferInstance : DecidableEq ι) := Subsingleton.elim _ _
      rw [hd]
      exact hreach) hcons
  refine ⟨n,Φ,hup,?_⟩
  intro i a ha u v
  rw [heq i u v,← integral_const_mul]
  apply integral_mono
  · apply Integrable.const_mul
    apply Integrable.of_bound ((hmeas _ a u).sub (hmeas _ a v)).abs.aestronglyMeasurable (2*H)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := hHeight ω (origin R A root i a) a u
    have hv := hHeight ω (origin R A root i a) a v
    exact (abs_sub _ _).trans (by linarith)
  · apply integrable_finsetSum
    intro t ht
    apply Integrable.of_bound ((hsmeas i t u).sub (hsmeas i t v)).abs.aestronglyMeasurable
      (2*H*((Fintype.card ι : ℝ)-1))
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := function_particles_height_bound hH (hreach ω i) t u
    have hv := function_particles_height_bound hH (hreach ω i) t v
    exact (abs_sub _ _).trans (by linarith)
  · intro ω
    exact origin_particle_gap R root B A k q hbag hA hN (shortestPathDistance G ℓ)
      L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω) i a ha u v
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1

lemma tree_path_mem_connected {I : Type*} (T : SimpleGraph I) (hT : T.IsTree)
    {S : Set I} (hS : (T.induce S).Connected) {A B P : I}
    (hA : A ∈ S) (hB : B ∈ S) (q : T.Walk A B) (hq : q.IsPath)
    (hP : P ∈ q.support) : P ∈ S := by
  obtain ⟨p, hp⟩ := hS.exists_isPath ⟨A, hA⟩ ⟨B, hB⟩
  let f := (SimpleGraph.Embedding.induce (G := T) S).toHom
  have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
  have heq : p.map f = q := congrArg Subtype.val
    ((hT.isAcyclic.subsingleton_path A B).elim ⟨p.map f, hp'⟩ ⟨q, hq⟩)
  have hmem : P ∈ (p.map f).support := heq.symm ▸ hP
  rw [SimpleGraph.Walk.support_map] at hmem
  obtain ⟨z, _, hz⟩ := List.mem_map.mp hmem
  exact hz ▸ z.property

/-- The bags touched by the vertices of a graph walk form a connected subtree.
No bounded-width assumption is needed for this purely combinatorial fact. -/
lemma touched_bags_connected {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {u v : V} (p : G.Walk u v) :
    (T.induce {t | ∃ z ∈ p.support, z ∈ bag t}).Connected := by
  induction p with
  | @nil u =>
    have hset : {t | ∃ z ∈ ([u] : List V), z ∈ bag t} = {t | u ∈ bag t} := by
      ext t
      simp
    change (T.induce {t | ∃ z ∈ ([u] : List V), z ∈ bag t}).Connected
    rw [hset]
    exact hocc u
  | @cons u v w huv p ih =>
    have hset : {t | ∃ z ∈ (p.cons huv).support, z ∈ bag t} =
        {t | u ∈ bag t} ∪ {t | ∃ z ∈ p.support, z ∈ bag t} := by
      ext t
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, Set.mem_ofPred_eq,
        Set.mem_union]
      constructor
      · rintro ⟨z, rfl | hz, hb⟩
        · exact Or.inl hb
        · exact Or.inr ⟨z, hz, hb⟩
      · rintro (h | ⟨z, hz, hb⟩)
        · exact ⟨u, Or.inl rfl, h⟩
        · exact ⟨z, Or.inr hz, hb⟩
    rw [hset]
    apply SimpleGraph.induce_union_connected (hocc u).preconnected ih.preconnected
    obtain ⟨t, hut, hvt⟩ := hedge u v huv
    exact ⟨t, hut, v, p.start_mem_support, hvt⟩

theorem bag_separator {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {A B P : I} (q : T.Walk A B) (hq : q.IsPath) (hP : P ∈ q.support)
    {u v : V} (hu : u ∈ bag A) (hv : v ∈ bag B) (p : G.Walk u v) :
    ∃ z, z ∈ p.support ∧ z ∈ bag P := by
  exact tree_path_mem_connected T hT (touched_bags_connected G T bag hedge hocc p)
    ⟨u, p.start_mem_support, hu⟩ ⟨v, p.end_mem_support, hv⟩ q hq hP

end BoundedTreewidthL1

namespace BoundedTreewidthL1

/-- Exact finite minimum distance to a nonempty bag in the original weighted metric. -/
noncomputable def bagDistance {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) : ℝ :=
  A.inf' hA (shortestPathDistance G ℓ x)

lemma bagDistance_attained {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) :
    ∃ a ∈ A, bagDistance G ℓ A hA x = shortestPathDistance G ℓ x a :=
  Finset.exists_mem_eq_inf' hA _

lemma bagDistance_le {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (A : Finset V) (hA : A.Nonempty) (x : V) {a : V} (ha : a ∈ A) :
    bagDistance G ℓ A hA x ≤ shortestPathDistance G ℓ x a :=
  Finset.inf'_le _ ha

lemma bagDistance_nonneg {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e) (A : Finset V) (hA : A.Nonempty) (x : V) :
    0 ≤ bagDistance G ℓ A hA x :=
  Finset.le_inf' hA _ (fun a _ => shortestPathDistance_nonneg G ℓ hG hℓ x a)

lemma bagDistance_triangle {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x y : V) :
    bagDistance G ℓ A hA x ≤ shortestPathDistance G ℓ x y + bagDistance G ℓ A hA y := by
  obtain ⟨a,ha,heq⟩ := bagDistance_attained G ℓ A hA y
  rw [heq]
  exact (bagDistance_le G ℓ A hA x ha).trans (shortestPathDistance_triangle G ℓ hG hℓ x y a)

lemma bagDistance_lipschitz {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x y : V) :
    |bagDistance G ℓ A hA x - bagDistance G ℓ A hA y| ≤ shortestPathDistance G ℓ x y := by
  have hxy := bagDistance_triangle G ℓ hG hℓ A hA x y
  have hyx := bagDistance_triangle G ℓ hG hℓ A hA y x
  rw [shortestPathDistance_comm G ℓ hG hℓ y x] at hyx
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma geodesic_split {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e)
    {a b z : V} (p : G.Walk a b) (hmin : walkLength G ℓ p = shortestPathDistance G ℓ a b)
    (hz : z ∈ p.support) :
    shortestPathDistance G ℓ a z + shortestPathDistance G ℓ z b = shortestPathDistance G ℓ a b := by
  have heq : walkLength G ℓ (p.takeUntil z hz) + walkLength G ℓ (p.dropUntil z hz) =
      shortestPathDistance G ℓ a b := by
    rw [← walkLength_append,SimpleGraph.Walk.take_spec,hmin]
  have h1 := shortestPathDistance_le_walkLength G ℓ hℓ (p.takeUntil z hz)
  have h2 := shortestPathDistance_le_walkLength G ℓ hℓ (p.dropUntil z hz)
  have h3 := shortestPathDistance_triangle G ℓ hG hℓ a z b
  linarith

theorem separator_bag_geometry {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (bag : I → Finset V) (hne : ∀ i, (bag i).Nonempty)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    {A B P : I} (q : T.Walk A B) (hq : q.IsPath) (hP : P ∈ q.support)
    {x : V} (hx : x ∈ bag B) :
    bagDistance G ℓ (bag P) (hne P) x ≤ bagDistance G ℓ (bag A) (hne A) x ∧
    ∃ z ∈ bag P, bagDistance G ℓ (bag A) (hne A) z + shortestPathDistance G ℓ z x =
      bagDistance G ℓ (bag A) (hne A) x
 := by
  have hnn : ∀ e, 0 ≤ ℓ e := fun e => (hℓ e).le
  obtain ⟨a,ha,haeq⟩ := bagDistance_attained G ℓ (bag A) (hne A) x
  obtain ⟨p,hp,hmin⟩ := shortestPathDistance_attained G ℓ hG a x
  obtain ⟨z,hzp,hzP⟩ := bag_separator G T bag hT hedge hocc q hq hP ha hx p
  have hsplit := geodesic_split G ℓ hG hnn p hmin hzp
  have hsym := shortestPathDistance_comm G ℓ hG hnn a x
  have hnear := bagDistance_le G ℓ (bag A) (hne A) z ha
  rw [shortestPathDistance_comm G ℓ hG hnn z a] at hnear
  have htri := bagDistance_triangle G ℓ hG hnn (bag A) (hne A) x z
  rw [shortestPathDistance_comm G ℓ hG hnn x z] at htri
  have hgeod : bagDistance G ℓ (bag A) (hne A) z + shortestPathDistance G ℓ z x =
      bagDistance G ℓ (bag A) (hne A) x := by linarith
  refine ⟨?_,z,hzP,hgeod⟩
  have hznonneg := bagDistance_nonneg G ℓ hG hnn (bag A) (hne A) z
  have hm := bagDistance_le G ℓ (bag P) (hne P) x hzP
  rw [shortestPathDistance_comm G ℓ hG hnn x z] at hm
  linarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

/-- Immediately follows a strict-to-weak threshold drop in the age-ordered list. -/
def Drop (C : Finset ℕ) (v : ℕ → ℝ) (τ : ℝ) (a : ℕ) : Prop :=
  a ∈ C ∧ v a ≤ τ ∧ ∃ b ∈ C, b < a ∧ τ < v b ∧
    ∀ c ∈ C, b < c → a ≤ c

noncomputable def protectedEntries (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact (P.product P).biUnion fun pq => if pq.1 = pq.2 then ∅ else
    (Finset.univ : Finset Bool).biUnion fun b => C.filter
      (Drop C (v pq.1) (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))

def cacheBound (k : ℕ) : ℕ := 2*k^2+2

noncomputable def eligible (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact C.filter (fun a => a ≠ 0 ∧ a ∉ protectedEntries P C d v J)

/-- Retain the inclusive list if space remains; otherwise evict its oldest
unprotected nonroot entry. The fallback is unreachable on admissible input. -/
noncomputable def trim (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : Finset ℕ := by
  classical
  exact if cacheBound k < C.card then
    if h : (eligible P C d v J).Nonempty then C.erase ((eligible P C d v J).min' h)
    else C
  else C

lemma drop_unique {C : Finset ℕ} {v : ℕ → ℝ} {τ : ℝ}
    (hmono : ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v b ≤ v a)
    {a b : ℕ} (ha : Drop C v τ a) (hb : Drop C v τ b) : a = b := by
  have le_of_drop {a b : ℕ} (ha : Drop C v τ a) (hb : Drop C v τ b) : a ≤ b := by
    obtain ⟨haC,haτ,c,hcC,hca,hcτ,hnext⟩ := ha
    by_cases hcb : c < b
    · exact hnext b hb.1 hcb
    · have hbc : b ≤ c := Nat.le_of_not_gt hcb
      have hval := hmono b hb.1 c hcC hbc
      linarith [hb.2.1]
  exact Nat.le_antisymm (le_of_drop ha hb) (le_of_drop hb ha)

lemma drop_card_le {C : Finset ℕ} {v : ℕ → ℝ} {τ : ℝ}
    [DecidablePred (Drop C v τ)]
    (hmono : ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v b ≤ v a) :
    (C.filter (Drop C v τ)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro a ha b hb
  exact drop_unique hmono (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2

lemma protected_subset (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) :
    protectedEntries P C d v J ⊆ C := by
  classical
  intro a ha
  simp only [protectedEntries, Finset.mem_biUnion] at ha
  obtain ⟨⟨p,q⟩,hpq,h⟩ := ha
  split_ifs at h with hpq'
  · simp at h
  · simp only [Finset.mem_biUnion] at h
    obtain ⟨b,hb,hd⟩ := h
    exact (Finset.mem_filter.mp hd).1

lemma protected_card (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (protectedEntries P C d v J).card ≤ 2*P.card^2 := by
  classical
  unfold protectedEntries
  calc
    _ ≤ ∑ pq ∈ P.product P, (if pq.1 = pq.2 then (∅ : Finset ℕ) else
        (Finset.univ : Finset Bool).biUnion fun b => C.filter
          (Drop C (v pq.1) (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _pq ∈ P.product P, 2 := by
      apply Finset.sum_le_sum
      intro pq hpq
      split_ifs with heq
      · simp
      · calc
          _ ≤ ∑ b : Bool, (C.filter (Drop C (v pq.1)
              (if b then J*d pq.1 pq.2 else d pq.1 pq.2/100))).card :=
            Finset.card_biUnion_le
          _ ≤ ∑ _b : Bool, 1 := Finset.sum_le_sum fun b _ =>
            drop_card_le (hmono pq.1 (Finset.mem_product.mp hpq).1)
          _ = 2 := by decide
    _ = _ := by simp [pow_two, Nat.mul_comm]

lemma eligible_nonempty (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hP : P.card ≤ k) (hfull : cacheBound k < C.card)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (eligible P C d v J).Nonempty := by
  classical
  by_contra h
  have hempty : eligible P C d v J = ∅ := Finset.not_nonempty_iff_eq_empty.mp h
  have hsub : C ⊆ insert 0 (protectedEntries P C d v J) := by
    intro a ha
    by_cases ha0 : a = 0
    · simp [ha0]
    · have hmem : a ∈ protectedEntries P C d v J := by
        by_contra hn
        have : a ∈ eligible P C d v J := by simp [eligible,ha,ha0,hn]
        simp [hempty] at this
      exact Finset.mem_insert_of_mem hmem
  have hcard := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hp := protected_card P C d v J hmono
  have hsq : P.card^2 ≤ k^2 := Nat.pow_le_pow_left hP 2
  unfold cacheBound at hfull
  omega

theorem deterministic_cache_step (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    (hP : P.card ≤ k) (hC : C.card ≤ cacheBound k + 1) (hroot : 0 ∈ C)
    (hmono : ∀ p ∈ P, ∀ a ∈ C, ∀ b ∈ C, a ≤ b → v p b ≤ v p a) :
    (trim k P C d v J).card ≤ cacheBound k ∧
    0 ∈ trim k P C d v J ∧ trim k P C d v J ⊆ C ∧
    (∀ a ∈ protectedEntries P C d v J, a ∈ trim k P C d v J) ∧
    (cacheBound k < C.card → ∃ e ∈ eligible P C d v J,
      (∀ a ∈ eligible P C d v J, e ≤ a) ∧ trim k P C d v J = C.erase e)
 := by
  classical
  by_cases hfull : cacheBound k < C.card
  · have he := eligible_nonempty k P C d v J hP hfull hmono
    let e := (eligible P C d v J).min' he
    have hem : e ∈ eligible P C d v J := Finset.min'_mem _ _
    have heC : e ∈ C := (Finset.mem_filter.mp hem).1
    have he0 : e ≠ 0 := (Finset.mem_filter.mp hem).2.1
    have heprot : e ∉ protectedEntries P C d v J := (Finset.mem_filter.mp hem).2.2
    have htrim : trim k P C d v J = C.erase e := by simp only [trim,hfull,↓reduceIte,he]; rfl
    rw [htrim]
    refine ⟨?_, ?_, Finset.erase_subset _ _, ?_, ?_⟩
    · rw [Finset.card_erase_of_mem heC]
      omega
    · simp [hroot, he0.symm]
    · intro a ha
      exact Finset.mem_erase.mpr ⟨by intro h; subst a; exact heprot ha,
        protected_subset P C d v J ha⟩
    · intro _
      exact ⟨e,hem,(fun a ha => Finset.min'_le _ _ ha),rfl⟩
  · have htrim : trim k P C d v J = C := by simp only [trim,hfull,↓reduceIte]
    rw [htrim]
    exact ⟨Nat.le_of_not_gt hfull, hroot, Finset.Subset.refl _,
      (fun _ h => protected_subset P C d v J h), (fun h => (hfull h).elim)⟩
end BoundedTreewidthL1.AnchorCache
namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

noncomputable def memory (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) : ℕ → Finset ℕ
  | 0 => {0}
  | t+1 => trim k (P (t+1)) (insert (t+1) (memory k P d v J t)) d (v (t+1)) J

/-- Incoming cache plus current proposal, before the release at this bag. -/
noncomputable def inclusiveCache (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) : ℕ → Finset ℕ
  | 0 => {0}
  | t+1 => insert (t+1) (memory k P d v J t)

def ValidInput (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ) : Prop :=
  ∀ t ≤ last, (P t).card ≤ k ∧ ∀ p ∈ P t,
    ∀ a ∈ inclusiveCache k P d v J t, ∀ b ∈ inclusiveCache k P d v J t,
      a ≤ b → v t p b ≤ v t p a

lemma trim_subset (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ) : trim k P C d v J ⊆ C := by
  classical
  unfold trim
  split_ifs <;> first | exact Finset.Subset.refl _ | exact Finset.erase_subset _ _

lemma trim_removed_unique (k : ℕ) (P : Finset V) (C : Finset ℕ)
    (d : V → V → ℝ) (v : V → ℕ → ℝ) (J : ℝ)
    {a b : ℕ} (ha : a ∈ C) (hb : b ∈ C)
    (ha' : a ∉ trim k P C d v J) (hb' : b ∉ trim k P C d v J) : a = b := by
  classical
  unfold trim at ha' hb'
  split_ifs at ha' hb' with hc he
  · have hae : a = (eligible P C d v J).min' he := by
      by_contra h; exact ha' (Finset.mem_erase.mpr ⟨h,ha⟩)
    have hbe : b = (eligible P C d v J).min' he := by
      by_contra h; exact hb' (Finset.mem_erase.mpr ⟨h,hb⟩)
    exact hae.trans hbe.symm
  all_goals exact (ha' ha).elim

lemma memory_subset (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) :
    memory k P d v J t ⊆ inclusiveCache k P d v J t := by
  cases t with
  | zero => exact Finset.Subset.refl _
  | succ t => exact trim_subset ..

lemma inclusive_self (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) : t ∈ inclusiveCache k P d v J t := by
  cases t <;> simp [inclusiveCache]

lemma inclusive_age (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (t : ℕ) :
    ∀ a ∈ inclusiveCache k P d v J t, a ≤ t := by
  induction t with
  | zero => intro a ha; simpa [inclusiveCache] using ha
  | succ t ih =>
    intro a ha
    simp only [inclusiveCache,Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact le_rfl
    · exact (ih a (memory_subset k P d v J t ha)).trans (Nat.le_succ t)

lemma inclusive_backwards (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) {a t u : ℕ}
    (hatu : a ≤ t) (htu : t ≤ u) (ha : a ∈ inclusiveCache k P d v J u) :
    a ∈ inclusiveCache k P d v J t := by
  induction u with
  | zero =>
    have ht : t = 0 := by omega
    simpa [ht] using ha
  | succ u ih =>
    by_cases h : t = u+1
    · simpa [h] using ha
    · have htu' : t ≤ u := by omega
      simp only [inclusiveCache,Finset.mem_insert] at ha
      rcases ha with he | hm
      · omega
      · exact ih htu' (memory_subset k P d v J u hm)

lemma memory_invariant (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    (memory k P d v J t).card ≤ cacheBound k ∧ 0 ∈ memory k P d v J t := by
  induction t with
  | zero => simp [memory,cacheBound]
  | succ t ih =>
    have hprev := ih (by omega)
    have hinput := hvalid (t+1) ht
    have hcard : (insert (t+1) (memory k P d v J t)).card ≤ cacheBound k + 1 :=
      (Finset.card_insert_le _ _).trans (Nat.add_le_add_right hprev.1 1)
    have hroot : 0 ∈ insert (t+1) (memory k P d v J t) := Finset.mem_insert_of_mem hprev.2
    have hstep := deterministic_cache_step k (P (t+1))
      (insert (t+1) (memory k P d v J t)) d (v (t+1)) J hinput.1 hcard hroot hinput.2
    exact ⟨hstep.1,hstep.2.1⟩

lemma inclusive_invariant (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    (inclusiveCache k P d v J t).card ≤ cacheBound k + 1 ∧
      0 ∈ inclusiveCache k P d v J t := by
  cases t with
  | zero => simp [inclusiveCache,cacheBound]
  | succ t =>
    have hmem := memory_invariant k P d v J last hvalid t (by omega)
    exact ⟨(Finset.card_insert_le _ _).trans (Nat.add_le_add_right hmem.1 1),
      Finset.mem_insert_of_mem hmem.2⟩

lemma memory_protected (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) (t : ℕ) (ht : t ≤ last) :
    protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J ⊆ memory k P d v J t := by
  cases t with
  | zero => exact protected_subset ..
  | succ t =>
    have hh := inclusive_invariant k P d v J last hvalid (t+1) ht
    have hin := hvalid (t+1) ht
    exact (deterministic_cache_step k (P (t+1)) (inclusiveCache k P d v J (t+1))
      d (v (t+1)) J hin.1 hh.1 hh.2 hin.2).2.2.2.1

noncomputable def activeTimes (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (last+1)).filter (fun t => a ∈ inclusiveCache k P d v J t)

noncomputable def lastActive (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) : ℕ := by
  classical
  exact if h : (activeTimes k P d v J last a).Nonempty then
    (activeTimes k P d v J last a).max' h else a

lemma active_self (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) (ha : a ≤ last) :
    a ∈ activeTimes k P d v J last a := by
  classical
  simp [activeTimes,ha,inclusive_self]

lemma lastActive_mem (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a : ℕ) (ha : a ≤ last) :
    lastActive k P d v J last a ∈ activeTimes k P d v J last a := by
  classical
  have hn : (activeTimes k P d v J last a).Nonempty := ⟨a,active_self k P d v J last a ha⟩
  simp only [lastActive,hn,↓reduceDIte]
  exact Finset.max'_mem _ _

lemma le_lastActive (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a t : ℕ)
    (ht : t ∈ activeTimes k P d v J last a) : t ≤ lastActive k P d v J last a := by
  classical
  have hn : (activeTimes k P d v J last a).Nonempty := ⟨t,ht⟩
  simp only [lastActive,hn,↓reduceDIte]
  exact Finset.le_max' _ _ ht

lemma inclusive_iff_interval (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last a t : ℕ) (ha : a ≤ last) (ht : t ≤ last) :
    a ∈ inclusiveCache k P d v J t ↔ a ≤ t ∧ t ≤ lastActive k P d v J last a := by
  classical
  constructor
  · intro hh
    refine ⟨inclusive_age k P d v J t a hh, le_lastActive k P d v J last a t ?_⟩
    simp [activeTimes,ht,hh]
  · rintro ⟨hat,htf⟩
    have hfm := lastActive_mem k P d v J last a ha
    simp only [activeTimes,Finset.mem_filter] at hfm
    exact inclusive_backwards k P d v J hat htf hfm.2
/-- Realizes the deterministic cache as the inclusive reservation path
needed by the youngest-crossing argument. -/
theorem cache_program_realizes (k : ℕ) (P : ℕ → Finset V) (d : V → V → ℝ)
    (v : ℕ → V → ℕ → ℝ) (J : ℝ) (last : ℕ)
    (hvalid : ValidInput k P d v J last) :
    ∃ R : BoundedTreewidthL1.ReservationPath, R.last = last ∧
      (∀ t ≤ last, R.inclusive t = inclusiveCache k P d v J t) ∧
      (∀ t, (R.inclusive t).card ≤ cacheBound k + 1) ∧
      (∀ t < last, ∀ a ∈ protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J,
        t < R.finish a)
 := by
  classical
  let f := lastActive k P d v J last
  have hfl (a : ℕ) (ha : a ≤ last) : a ≤ f a :=
    le_lastActive k P d v J last a a (active_self k P d v J last a ha)
  have hfu (a : ℕ) (ha : a ≤ last) : f a ≤ last := by
    have h := (Finset.mem_filter.mp (lastActive_mem k P d v J last a ha)).1
    exact Nat.le_of_lt_succ (Finset.mem_range.mp h)
  have hroot : f 0 = last := by
    apply Nat.le_antisymm (hfu 0 (Nat.zero_le _))
    apply le_lastActive
    simp only [activeTimes,Finset.mem_filter,Finset.mem_range,Nat.lt_succ_self,true_and]
    exact (inclusive_invariant k P d v J last hvalid last le_rfl).2
  have hretained {a t : ℕ} (ht : t < last) (ha : a ∈ memory k P d v J t) : t < f a := by
    have hin : a ∈ inclusiveCache k P d v J (t+1) := Finset.mem_insert_of_mem ha
    have haage := inclusive_age k P d v J (t+1) a hin
    have happ := (inclusive_iff_interval k P d v J last a (t+1) (by omega) (by omega)).mp hin
    change a ≤ t+1 ∧ t+1 ≤ f a at happ
    exact (Nat.lt_succ_self t).trans_le happ.2
  have hrelease (a b t : ℕ) (hat : a ≤ t) (hbt : b ≤ t) (ht : t < last)
      (haf : f a = t) (hbf : f b = t) : a = b := by
    have ham := (inclusive_iff_interval k P d v J last a t (by omega) (by omega)).mpr ⟨hat,haf.ge⟩
    have hbm := (inclusive_iff_interval k P d v J last b t (by omega) (by omega)).mpr ⟨hbt,hbf.ge⟩
    have han : a ∉ memory k P d v J t := by intro h; have := hretained ht h; omega
    have hbn : b ∉ memory k P d v J t := by intro h; have := hretained ht h; omega
    cases t with
    | zero => exact (han ham).elim
    | succ t =>
      exact trim_removed_unique k (P (t+1)) (inclusiveCache k P d v J (t+1))
        d (v (t+1)) J ham hbm han hbn
  let R : BoundedTreewidthL1.ReservationPath := ⟨last,f,hfl,hfu,hrelease,hroot⟩
  have heq (t : ℕ) (ht : t ≤ last) : R.inclusive t = inclusiveCache k P d v J t := by
    ext a
    simp only [ReservationPath.inclusive,show R.last = last from rfl,ht,↓reduceIte,
      Finset.mem_filter,Finset.mem_range,Nat.lt_succ_iff]
    change (a ≤ t ∧ t ≤ f a) ↔ _
    by_cases ha : a ≤ last
    · exact (inclusive_iff_interval k P d v J last a t ha ht).symm
    · have hn : ¬a ≤ t := by omega
      have hm : a ∉ inclusiveCache k P d v J t := by
        intro h; exact hn (inclusive_age k P d v J t a h)
      simp [hn,hm]
  refine ⟨R,rfl,heq,?_,?_⟩
  · intro t
    by_cases ht : t ≤ last
    · rw [heq t ht]
      exact (inclusive_invariant k P d v J last hvalid t ht).1
    · simp [ReservationPath.inclusive,show R.last = last from rfl,ht]
  · intro t ht a ha
    exact hretained ht (memory_protected k P d v J last hvalid t ht.le ha)
end BoundedTreewidthL1.AnchorCache

namespace BoundedTreewidthL1.AnchorCache

theorem graph_cache_realizes {V I : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (bag : I → Finset V) (hne : ∀ i, (bag i).Nonempty)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (k : ℕ) (hcard : ∀ i, (bag i).card ≤ k) (J : ℝ)
    {root endBag : I} (q : T.Walk root endBag) (hq : q.IsPath) :
    let P := fun t => bag (q.getVert t)
    let d := shortestPathDistance G ℓ
    let v := fun (_ : ℕ) (p : V) a => bagDistance G ℓ (bag (q.getVert a)) (hne _) p
    ∃ R : ReservationPath, R.last = q.length ∧
      (∀ t ≤ q.length, R.inclusive t = inclusiveCache k P d v J t) ∧
      (∀ t, (R.inclusive t).card ≤ cacheBound k + 1) ∧
      (∀ t < q.length, ∀ a ∈ protectedEntries (P t) (inclusiveCache k P d v J t) d (v t) J,
        t < R.finish a) := by
  classical
  dsimp only
  apply cache_program_realizes
  intro t ht
  refine ⟨hcard _,?_⟩
  intro p hp a ha b hb hab
  have hbt := inclusive_age k (fun t => bag (q.getVert t)) (shortestPathDistance G ℓ)
    (fun (_ : ℕ) (p : V) a => bagDistance G ℓ (bag (q.getVert a)) (hne _) p) J t b hb
  have hat : a ≤ t := hab.trans hbt
  have hsup : q.getVert b ∈ ((q.take t).drop a).support := by
    have hh := ((q.take t).drop a).getVert_mem_support (b-a)
    simpa only [SimpleGraph.Walk.drop_getVert,SimpleGraph.Walk.take_getVert,
      Nat.add_sub_of_le hab,inf_eq_right.mpr hbt] using hh
  have hgeo := separator_bag_geometry G ℓ hG hℓ T bag hne hT hedge hocc
    ((q.take t).drop a) ((hq.take t).drop a) hsup hp
  simpa only [SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hat] using hgeo.1
end BoundedTreewidthL1.AnchorCache
namespace BoundedTreewidthL1.AnchorCache
variable {V : Type*} [DecidableEq V]

lemma drop_congr_on (C : Finset ℕ) (v w : ℕ → ℝ) (τ : ℝ)
    (hvw : ∀ a ∈ C, v a = w a) (a : ℕ) : Drop C v τ a ↔ Drop C w τ a := by
  constructor
  · rintro ⟨ha,hva,b,hb,hba,hτ,hnext⟩
    exact ⟨ha,by rw [← hvw a ha]; exact hva,b,hb,hba,
      by rw [← hvw b hb]; exact hτ,hnext⟩
  · rintro ⟨ha,hva,b,hb,hba,hτ,hnext⟩
    exact ⟨ha,by rw [hvw a ha]; exact hva,b,hb,hba,
      by rw [hvw b hb]; exact hτ,hnext⟩

lemma protected_congr_on (P : Finset V) (C : Finset ℕ) (d : V → V → ℝ)
    (v w : V → ℕ → ℝ) (J : ℝ) (hvw : ∀ x ∈ P, ∀ a ∈ C, v x a = w x a) :
    protectedEntries P C d v J = protectedEntries P C d w J := by
  classical
  unfold protectedEntries
  apply Finset.biUnion_congr rfl
  intro xy hxy
  split_ifs with he
  · rfl
  · apply Finset.biUnion_congr rfl
    intro b hb
    apply Finset.filter_congr
    intro a ha
    exact drop_congr_on C (v xy.1) (w xy.1) _
      (hvw xy.1 (Finset.mem_product.mp hxy).1) a

lemma trim_congr_on (k : ℕ) (P : Finset V) (C : Finset ℕ) (d : V → V → ℝ)
    (v w : V → ℕ → ℝ) (J : ℝ) (hvw : ∀ x ∈ P, ∀ a ∈ C, v x a = w x a) :
    trim k P C d v J = trim k P C d w J := by
  classical
  have he : eligible P C d v J = eligible P C d w J := by
    simp only [eligible, protected_congr_on P C d v w J hvw]
  simp only [trim, he]

lemma memory_prefix (k : ℕ) (P Q : ℕ → Finset V) (d : V → V → ℝ)
    (v w : ℕ → V → ℕ → ℝ) (J : ℝ) (l : ℕ)
    (hP : ∀ t < l, P t = Q t)
    (hv : ∀ t < l, ∀ x a, a ≤ t → v t x a = w t x a) :
    ∀ t < l, memory k P d v J t = memory k Q d w J t := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
    intro ht
    rw [memory, memory, hP (t+1) ht, ih (by omega)]
    apply trim_congr_on
    intro x hx a ha
    exact hv (t+1) ht x a (inclusive_age k Q d w J (t+1) a ha)

lemma inclusiveCache_prefix (k : ℕ) (P Q : ℕ → Finset V) (d : V → V → ℝ)
    (v w : ℕ → V → ℕ → ℝ) (J : ℝ) (l : ℕ)
    (hP : ∀ t < l, P t = Q t)
    (hv : ∀ t < l, ∀ x a, a ≤ t → v t x a = w t x a) :
    ∀ t < l, inclusiveCache k P d v J t = inclusiveCache k Q d w J t := by
  intro t ht
  cases t with
  | zero => rfl
  | succ t =>
    simp only [inclusiveCache, memory_prefix k P Q d v w J l hP hv t (by omega)]

end BoundedTreewidthL1.AnchorCache

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)

noncomputable def downPath (i : I) : T.Walk root i := (path T hT root i).reverse
lemma downPath_isPath (i : I) : (downPath T hT root i).IsPath :=
  (path_isPath T hT root i).reverse
lemma downPath_length (i : I) : (downPath T hT root i).length = (forest T hT root).depth i := by
  simp only [downPath, SimpleGraph.Walk.length_reverse, path_length, forest]

lemma depth_parent {i p : I} (hp : (forest T hT root).parent i = some p) :
    (forest T hT root).depth i = (forest T hT root).depth p + 1 := by
  have hd := hT.dist_eq_dist_add_one_of_adj root (parent_adj T hT root hp)
  rw [SimpleGraph.dist_comm (u := root) (v := i),
    SimpleGraph.dist_comm (u := root) (v := p)] at hd
  have hlt := (forest T hT root).decreases i p hp
  change T.dist p root < T.dist i root at hlt
  change T.dist i root = T.dist p root + 1
  omega

lemma path_parent {i p : I} (hp : (forest T hT root).parent i = some p) :
    path T hT root i = (path T hT root p).cons (parent_adj T hT root hp) := by
  have hd := depth_parent T hT root hp
  have hlen : ((path T hT root p).cons (parent_adj T hT root hp)).length = T.dist i root := by
    simpa only [SimpleGraph.Walk.length_cons, path_length, forest] using hd.symm
  exact congrArg Subtype.val ((hT.isAcyclic.subsingleton_path i root).elim
    ⟨_, path_isPath T hT root i⟩ ⟨_, SimpleGraph.Walk.isPath_of_length_eq_dist _ hlen⟩)

lemma downPath_parent_getVert {i p : I} (hp : (forest T hT root).parent i = some p)
    (t : ℕ) (ht : t ≤ (forest T hT root).depth p) :
    (downPath T hT root i).getVert t = (downPath T hT root p).getVert t := by
  unfold downPath
  rw [path_parent T hT root hp, SimpleGraph.Walk.reverse_cons]
  rw [SimpleGraph.Walk.getVert_append']
  rw [SimpleGraph.Walk.length_reverse, path_length]
  exact ite_eq_left (show t ≤ T.dist p root from ht)

end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.TreeCache
open AnchorCache _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

noncomputable def bags (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (i : I) (t : ℕ) := B ((downPath T hT root i).getVert t)
noncomputable def heights (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (D : I → V → ℝ) (i : I) (_ : ℕ) (v : V) (a : ℕ) := D ((downPath T hT root i).getVert a) v
noncomputable def inclusive (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  inclusiveCache k (bags T hT root B i) d (heights T hT root D i) J ((forest T hT root).depth i)
noncomputable def released (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  memory k (bags T hT root B i) d (heights T hT root D i) J ((forest T hT root).depth i)
noncomputable def active (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  (inclusive T hT root B D k d J i).image (downPath T hT root i).getVert
noncomputable def retained (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :=
  (released T hT root B D k d J i).image (downPath T hT root i).getVert

lemma inclusive_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    inclusive T hT root B D k d J i =
      insert ((forest T hT root).depth i) (released T hT root B D k d J p) := by
  have hb (t : ℕ) (ht : t < (forest T hT root).depth p + 1) :
      bags T hT root B i t = bags T hT root B p t := by
    unfold bags
    rw [downPath_parent_getVert T hT root hp t (by omega)]
  have hv (t : ℕ) (ht : t < (forest T hT root).depth p + 1) (x : V) (a : ℕ)
      (ha : a ≤ t) : heights T hT root D i t x a = heights T hT root D p t x a := by
    unfold heights
    rw [downPath_parent_getVert T hT root hp a (by omega)]
  unfold inclusive released
  rw [depth_parent T hT root hp, inclusiveCache,
    memory_prefix k _ _ d _ _ J ((forest T hT root).depth p+1) hb hv _ (by omega)]

lemma active_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i = insert i (retained T hT root B D k d J p) := by
  unfold active
  rw [inclusive_parent T hT root B D k d J hp, Finset.image_insert]
  have he : (downPath T hT root i).getVert ((forest T hT root).depth i) = i := by
    rw [← downPath_length, SimpleGraph.Walk.getVert_length]
  rw [he]
  congr 1
  apply Finset.image_congr
  intro a ha
  have hage : a ≤ (forest T hT root).depth p := inclusive_age k _ d _ J _ a
    (memory_subset k _ d _ J _ ha)
  exact downPath_parent_getVert T hT root hp a hage

lemma retained_subset (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :
    retained T hT root B D k d J i ⊆ active T hT root B D k d J i :=
  Finset.image_subset_image (memory_subset k _ d _ J _)

lemma child_not_active (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    i ∉ active T hT root B D k d J p := by
  intro h
  obtain ⟨a,ha,hai⟩ := Finset.mem_image.mp h
  have hage : a ≤ (forest T hT root).depth p := inclusive_age k _ d _ J _ a ha
  have he : (downPath T hT root i).getVert a =
      (downPath T hT root i).getVert ((forest T hT root).depth i) := by
    rw [downPath_parent_getVert T hT root hp a hage, ← downPath_length,
      SimpleGraph.Walk.getVert_length]
    exact hai
  have hh := (downPath_isPath T hT root i).getVert_injOn
    (by simp only [Set.mem_ofPred_eq,downPath_length]; have := depth_parent T hT root hp; omega)
    (by simp only [Set.mem_ofPred_eq,downPath_length,le_refl]) he
  have hd := depth_parent T hT root hp
  omega

end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.TreeCache
open AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

lemma active_root (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) :
    active T hT root B D k d J root = {root} := by
  simp only [active, inclusive, forest, SimpleGraph.dist_self, inclusiveCache,
    Finset.image_singleton, SimpleGraph.Walk.getVert_zero]

lemma active_inter_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i ∩ active T hT root B D k d J p =
      retained T hT root B D k d J p := by
  rw [active_parent T hT root B D k d J hp]
  ext a
  simp only [Finset.mem_inter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | h,hp'⟩
    · exact False.elim (child_not_active T hT root B D k d J hp hp')
    · exact h
  · intro h
    exact ⟨Or.inr h, retained_subset T hT root B D k d J p h⟩

lemma active_sdiff_parent (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    {i p : I} (hp : (forest T hT root).parent i = some p) :
    active T hT root B D k d J i \ active T hT root B D k d J p = {i} := by
  rw [active_parent T hT root B D k d J hp]
  ext a
  simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨rfl | h,hp'⟩
    · rfl
    · exact False.elim (hp' (retained_subset T hT root B D k d J p h))
  · rintro rfl
    exact ⟨Or.inl rfl, child_not_active T hT root B D k d J hp⟩

/-- Width-only cache capacity on the actual root-to-node paths. -/
theorem graph_active_bound [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (B : I → Finset V) (hne : ∀ i, (B i).Nonempty)
    (hT : T.IsTree) (root : I)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ B t ∧ v ∈ B t)
    (hocc : ∀ v, (T.induce {t | v ∈ B t}).Connected)
    (k : ℕ) (hcard : ∀ i, (B i).card ≤ k) (J : ℝ) (i : I) :
    (active T hT root B (fun a => bagDistance G ℓ (B a) (hne a)) k
      (shortestPathDistance G ℓ) J i).card ≤ cacheBound k + 1 := by
  let : DecidableEq V := Classical.decEq V
  obtain ⟨R,hR,heq,hbound,hprot⟩ := graph_cache_realizes G ℓ hG hℓ T B hne hT
    hedge hocc k hcard J (downPath T hT root i) (downPath_isPath T hT root i)
  apply (Finset.card_image_le).trans
  change (inclusiveCache k (bags T hT root B i) (shortestPathDistance G ℓ)
    (heights T hT root (fun a => bagDistance G ℓ (B a) (hne a)) i) J
    ((forest T hT root).depth i)).card ≤ _
  rw [← downPath_length]
  exact (heq _ le_rfl) ▸ hbound _
end BoundedTreewidthL1.TreeCache

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1

section ReachableWeightedPaths
variable {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)

lemma path_length_set_nonempty_of_reachable {u v : V} (hr : G.Reachable u v) :
    {r : ℝ | ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = r}.Nonempty := by
  classical
  obtain ⟨p⟩ := hr
  exact ⟨walkLength G ℓ p.toPath.val, p.toPath.val, p.toPath.property, rfl⟩

lemma shortestPathDistance_attained_of_reachable [Fintype V] {u v : V}
    (hr : G.Reachable u v) :
    ∃ p : G.Walk u v, p.IsPath ∧ walkLength G ℓ p = shortestPathDistance G ℓ u v :=
  (path_length_set_nonempty_of_reachable G ℓ hr).csInf_mem (path_length_set_finite G ℓ u v)

lemma shortestPathDistance_nonneg_of_reachable (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (hr : G.Reachable u v) : 0 ≤ shortestPathDistance G ℓ u v := by
  apply le_csInf (path_length_set_nonempty_of_reachable G ℓ hr)
  rintro r ⟨p, _, rfl⟩
  exact walkLength_nonneg G ℓ hℓ p

lemma shortestPathDistance_self_of_nonneg (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) :
    shortestPathDistance G ℓ u u = 0 :=
  le_antisymm (shortestPathDistance_le_walkLength G ℓ hℓ .nil)
    (shortestPathDistance_nonneg_of_reachable G ℓ hℓ .rfl)

lemma shortestPathDistance_comm_of_reachable [Fintype V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v : V} (hr : G.Reachable u v) :
    shortestPathDistance G ℓ u v = shortestPathDistance G ℓ v u := by
  have hle {a b : V} (hab : G.Reachable a b) :
      shortestPathDistance G ℓ a b ≤ shortestPathDistance G ℓ b a := by
    obtain ⟨p, hp, heq⟩ := shortestPathDistance_attained_of_reachable G ℓ hab.symm
    rw [← heq, ← walkLength_reverse G ℓ p]
    exact shortestPathDistance_le_pathLength G ℓ hℓ p.reverse hp.reverse
  exact le_antisymm (hle hr) (hle hr.symm)

lemma shortestPathDistance_triangle_of_reachable [Fintype V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v w : V} (huv : G.Reachable u v) (hvw : G.Reachable v w) :
    shortestPathDistance G ℓ u w ≤ shortestPathDistance G ℓ u v + shortestPathDistance G ℓ v w := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ huv
  obtain ⟨q, _, hq⟩ := shortestPathDistance_attained_of_reachable G ℓ hvw
  rw [← hp, ← hq, ← walkLength_append G ℓ p q]
  exact shortestPathDistance_le_walkLength G ℓ hℓ (p.append q)

lemma walkLength_takeUntil_le [DecidableEq V] (hℓ : ∀ e, 0 ≤ ℓ e)
    {u v z : V} (p : G.Walk u v) (hz : z ∈ p.support) :
    walkLength G ℓ (p.takeUntil z hz) ≤ walkLength G ℓ p := by
  have h := walkLength_nonneg G ℓ hℓ (p.dropUntil z hz)
  have heq := walkLength_append G ℓ (p.takeUntil z hz) (p.dropUntil z hz)
  rw [SimpleGraph.Walk.take_spec] at heq
  linarith

lemma geodesic_split_of_reachable [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) {a b z : V} (p : G.Walk a b)
    (hmin : walkLength G ℓ p = shortestPathDistance G ℓ a b) (hz : z ∈ p.support) :
    shortestPathDistance G ℓ a z + shortestPathDistance G ℓ z b = shortestPathDistance G ℓ a b := by
  have heq : walkLength G ℓ (p.takeUntil z hz) + walkLength G ℓ (p.dropUntil z hz) =
      shortestPathDistance G ℓ a b := by
    rw [← walkLength_append, SimpleGraph.Walk.take_spec, hmin]
  have h1 := shortestPathDistance_le_walkLength G ℓ hℓ (p.takeUntil z hz)
  have h2 := shortestPathDistance_le_walkLength G ℓ hℓ (p.dropUntil z hz)
  have h3 := shortestPathDistance_triangle_of_reachable G ℓ hℓ
    (p.takeUntil z hz).reachable (p.dropUntil z hz).reachable
  linarith

/-- Intrinsic balls are connected even when the ambient graph is disconnected;
reachability is explicit, so the empty-infimum convention never adds vertices. -/
lemma reachable_openBall_connected [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 < r) :
    (G.induce {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v < r}).Connected := by
  let S := {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v < r}
  have hu : u ∈ S := ⟨.rfl, by simpa [shortestPathDistance_self_of_nonneg G ℓ hℓ] using hr⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ hv.1
  have hsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    refine ⟨(p.takeUntil z hz).reachable, ?_⟩
    calc
      shortestPathDistance G ℓ u z ≤ walkLength G ℓ (p.takeUntil z hz) :=
        shortestPathDistance_le_walkLength G ℓ hℓ _
      _ ≤ walkLength G ℓ p := walkLength_takeUntil_le G ℓ hℓ p hz
      _ < r := hp ▸ hv.2
  exact ⟨(p.induce S hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

lemma reachable_closedBall_connected [Fintype V] [DecidableEq V]
    (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 ≤ r) :
    (G.induce {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r}).Connected := by
  let S := {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r}
  have hu : u ∈ S := ⟨.rfl, by simpa [shortestPathDistance_self_of_nonneg G ℓ hℓ] using hr⟩
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨u, hu⟩, ?_⟩
  rintro ⟨v, hv⟩
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G ℓ hv.1
  have hsupp : ∀ z ∈ p.support, z ∈ S := by
    intro z hz
    refine ⟨(p.takeUntil z hz).reachable, ?_⟩
    calc
      shortestPathDistance G ℓ u z ≤ walkLength G ℓ (p.takeUntil z hz) :=
        shortestPathDistance_le_walkLength G ℓ hℓ _
      _ ≤ walkLength G ℓ p := walkLength_takeUntil_le G ℓ hℓ p hz
      _ ≤ r := hp ▸ hv.2
  exact ⟨(p.induce S hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

lemma shortest_closedBall_connected [Fintype V] [DecidableEq V]
    (hG : G.Connected) (hℓ : ∀ e, 0 ≤ ℓ e) (u : V) {r : ℝ} (hr : 0 ≤ r) :
    (G.induce {v | shortestPathDistance G ℓ u v ≤ r}).Connected := by
  have heq : {v | G.Reachable u v ∧ shortestPathDistance G ℓ u v ≤ r} =
      {v | shortestPathDistance G ℓ u v ≤ r} := by
    ext v
    simp [hG u v]
  rw [← heq]
  exact reachable_closedBall_connected G ℓ hℓ u hr

end ReachableWeightedPaths

@[instance_reducible]
noncomputable def weightedMetricSpace {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (hG : G.Connected) (hℓ : ∀ e, 0 < ℓ e) : MetricSpace V where
  dist := shortestPathDistance G ℓ
  dist_self := shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)
  dist_comm := shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le)
  dist_triangle := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le)
  eq_of_dist_eq_zero := fun {_ _} h => (shortestPathDistance_metric G ℓ hG hℓ).2.2.2.2.1 _ _ h

end BoundedTreewidthL1

namespace BoundedTreewidthL1.Annulus

variable {V : Type*}

abbrev weights (H : SimpleGraph V) (w : Sym2 V → ℝ) : H.edgeSet → ℝ := fun e => w e.val

noncomputable def distance (H : SimpleGraph V) (w : Sym2 V → ℝ) : V → V → ℝ :=
  shortestPathDistance H (weights H w)

noncomputable def root (H : SimpleGraph V) (x : V) : V :=
  Quot.out (H.connectedComponentMk x)

lemma root_reachable (H : SimpleGraph V) (x : V) : H.Reachable (root H x) x :=
  SimpleGraph.ConnectedComponent.exact (Quot.out_eq _)

lemma root_eq {H : SimpleGraph V} {x y : V} (h : H.Reachable x y) :
    root H x = root H y := congrArg Quot.out (SimpleGraph.ConnectedComponent.sound h)

lemma root_idem (H : SimpleGraph V) (x : V) : root H (root H x) = root H x :=
  root_eq (root_reachable H x)

noncomputable def height (H : SimpleGraph V) (w : Sym2 V → ℝ) (x : V) : ℝ :=
  distance H w (root H x) x

lemma walkLength_weights {H : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) :
    walkLength H (weights H w) p = (p.edges.map w).sum := by
  induction p with
  | nil => rfl
  | cons h p ih => simp only [walkLength, SimpleGraph.Walk.edges_cons,
      List.map_cons, List.sum_cons, weights, ih]

lemma walkLength_transfer {H G : SimpleGraph V} (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) (hp : ∀ e ∈ p.edges, e ∈ G.edgeSet) :
    walkLength G (weights G w) (p.transfer G hp) = walkLength H (weights H w) p := by
  simp only [walkLength_weights, SimpleGraph.Walk.edges_transfer]

lemma walkLength_mono_map {H G : SimpleGraph V} (hHG : H ≤ G) (w : Sym2 V → ℝ)
    {u v : V} (p : H.Walk u v) :
    walkLength G (weights G w) (p.map (.ofLE hHG)) = walkLength H (weights H w) p := by
  induction p with
  | nil => rfl
  | @cons u v z h p ih => simpa only [SimpleGraph.Walk.map_cons, walkLength,
      SimpleGraph.Hom.ofLE_apply, weights] using congrArg (fun r => w s(u,v) + r) ih

lemma distance_mono [Fintype V] {H G : SimpleGraph V} (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) {u v : V} (huv : H.Reachable u v) :
    distance G w u v ≤ distance H w u v := by
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable H (weights H w) huv
  change shortestPathDistance G (weights G w) u v ≤ shortestPathDistance H (weights H w) u v
  rw [← hp, ← walkLength_mono_map hHG w p]
  exact shortestPathDistance_le_walkLength G (weights G w) (fun e => hw e.val) _

lemma distance_edge (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {u v : V} (huv : H.Adj u v) : distance H w u v ≤ w s(u,v) := by
  simpa [distance, walkLength, weights] using
    shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) huv.toWalk

lemma height_nonneg (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : V) : 0 ≤ height H w x :=
  shortestPathDistance_nonneg_of_reachable H (weights H w) (fun e => hw e.val)
    (root_reachable H x)

lemma height_root (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (x : V) : height H w (root H x) = 0 := by
  simp only [height, root_idem, distance]
  exact shortestPathDistance_self_of_nonneg H (weights H w) (fun e => hw e.val) _

lemma height_eq_of_reachable {H : SimpleGraph V} (w : Sym2 V → ℝ) {x y : V}
    (hxy : H.Reachable x y) : height H w y = distance H w (root H x) y := by
  simp only [height, root_eq hxy]

lemma height_le_add_distance [Fintype V] (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {x y : V} (hxy : H.Reachable x y) :
    height H w y ≤ height H w x + distance H w x y := by
  rw [height_eq_of_reachable w hxy]
  exact shortestPathDistance_triangle_of_reachable H (weights H w) (fun e => hw e.val)
    (root_reachable H x) hxy

lemma height_edge [Fintype V] (H : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) {x y : V} (hxy : H.Adj x y) :
    height H w y ≤ height H w x + w s(x,y) := by
  have h1 := height_le_add_distance H w hw hxy.reachable
  have h2 := distance_edge H w hw hxy
  linarith

/-- The predecessor of a first height crossing is strictly inside the ball. -/
lemma walk_crossing_below (H : SimpleGraph V) (f : V → ℝ) {ε t : ℝ}
    (hstep : ∀ a b, H.Adj a b → f b ≤ f a + ε)
    {u v : V} (p : H.Walk u v) (hu : f u < t) (hv : t ≤ f v) :
    ∃ z ∈ p.support, t - ε ≤ f z ∧ f z < t := by
  induction p with
  | nil => exact (not_lt_of_ge hv hu).elim
  | @cons a b c hab p ih =>
    by_cases hb : f b < t
    · obtain ⟨z, hz, hlo, hhi⟩ := ih hb hv
      exact ⟨z, by simp [hz], hlo, hhi⟩
    · have hs := hstep a b hab
      exact ⟨a, by simp, by linarith, hu⟩

/-- The strict intrinsic inner ball, with reachability explicitly imposed. -/
def inner (H : SimpleGraph V) (w : Sym2 V → ℝ) (x : V) (t : ℝ) : Set V :=
  {z | H.Reachable (root H x) z ∧ distance H w (root H x) z < t}

lemma inner_connected [Fintype V] [DecidableEq V] (H : SimpleGraph V)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e) (x : V) {t : ℝ} (ht : 0 < t) :
    (H.induce (inner H w x t)).Connected :=
  reachable_openBall_connected H (weights H w) (fun e => hw e.val) (root H x) ht

lemma inner_reachable {H : SimpleGraph V} {w : Sym2 V → ℝ} {x z : V} {t : ℝ}
    (hz : z ∈ inner H w x t) : H.Reachable x z :=
  (root_reachable H x).symm.trans hz.1

lemma inner_height {H : SimpleGraph V} {w : Sym2 V → ℝ} {x z : V} {t : ℝ}
    (hz : z ∈ inner H w x t) : height H w z < t := by
  rw [height_eq_of_reachable w (inner_reachable hz)]
  exact hz.2

lemma inner_dominates [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {ε : ℝ} (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε)
    (x c : V) (hxc : H.Reachable x c) {t R : ℝ}
    (ht : 0 < t) (hlo : t ≤ height H w c) (hhi : height H w c ≤ t + R) :
    ∃ z ∈ inner H w x t, distance H w c z ≤ R + ε := by
  have hrc := (root_reachable H x).trans hxc
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable H (weights H w) hrc
  have hstep : ∀ a b, H.Adj a b → height H w b ≤ height H w a + ε := by
    intro a b hab
    have h1 := height_edge H w hw hab
    have h2 := hmesh a b hab
    linarith
  obtain ⟨z, hz, hzlo, hzhi⟩ := walk_crossing_below H (height H w) hstep p
    (by simpa [height_root H w hw] using ht) hlo
  have hrz := (p.takeUntil z hz).reachable
  have hxz := (root_reachable H x).symm.trans hrz
  have hzheight := height_eq_of_reachable w hxz
  have hcHeight := height_eq_of_reachable w hxc
  refine ⟨z, ⟨hrz, by rwa [← hzheight]⟩, ?_⟩
  have hsplit := geodesic_split_of_reachable H (weights H w) (fun e => hw e.val) p hp hz
  have hsym := shortestPathDistance_comm_of_reachable H (weights H w) (fun e => hw e.val)
    (p.dropUntil z hz).reachable
  change distance H w (root H x) z + distance H w z c = distance H w (root H x) c at hsplit
  change distance H w z c = distance H w c z at hsym
  rw [← hzheight, ← hcHeight, hsym] at hsplit
  linarith

noncomputable def band (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) (x : V) : ℤ :=
  ⌊(height H w x + a) / R⌋

noncomputable def cut (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) : SimpleGraph V where
  Adj u v := H.Adj u v ∧ band H w R a u = band H w R a v
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

lemma cut_le (H : SimpleGraph V) (w : Sym2 V → ℝ) (R a : ℝ) : cut H w R a ≤ H :=
  fun _ _ h => h.1

lemma band_eq_of_cut_reachable {H : SimpleGraph V} {w : Sym2 V → ℝ} {R a : ℝ}
    {x y : V} (h : (cut H w R a).Reachable x y) : band H w R a x = band H w R a y := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => rfl
  | cons h p ih => exact h.2.trans ih

lemma band_bounds (H : SimpleGraph V) (w : Sym2 V → ℝ) {R : ℝ} (hR : 0 < R)
    (a : ℝ) (x : V) :
    (band H w R a x : ℝ) * R - a ≤ height H w x ∧
      height H w x < (band H w R a x : ℝ) * R - a + R := by
  have hlo := Int.floor_le ((height H w x + a) / R)
  have hhi := Int.lt_floor_add_one ((height H w x + a) / R)
  have hlo' := (le_div_iff₀ hR).mp hlo
  have hhi' := (div_lt_iff₀ hR).mp hhi
  change (band H w R a x : ℝ) * R ≤ height H w x + a at hlo'
  change height H w x + a < ((band H w R a x : ℝ) + 1) * R at hhi'
  constructor <;> nlinarith

lemma band_nonneg (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R a : ℝ} (hR : 0 < R) (ha : 0 ≤ a) (x : V) : 0 ≤ band H w R a x :=
  Int.floor_nonneg.mpr (div_nonneg (add_nonneg (height_nonneg H w hw x) ha) hR.le)

/-- A single annulus either is close to its root, or has a connected inner
ball deleted from its component and uniformly close to all of that component. -/
theorem cut_component_alternative [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R a ε : ℝ} (hR : 0 < R) (ha0 : 0 ≤ a) (haR : a < R)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε) (x : V) :
    (∀ y z, (cut H w R a).Reachable x y → (cut H w R a).Reachable x z →
      distance G w y z ≤ 2 * R) ∨
    ∃ B : Set V, (G.induce B).Connected ∧
      (∀ z ∈ B, H.Reachable x z) ∧
      (∀ z ∈ B, ¬(cut H w R a).Reachable x z) ∧
      ∀ c, (cut H w R a).Reachable x c → ∃ z ∈ B, distance G w c z ≤ R + ε := by
  let n := band H w R a x
  have hn : 0 ≤ n := band_nonneg H w hw hR ha0 x
  by_cases hn0 : n = 0
  · left
    intro y z hxy hxz
    have hy := (band_bounds H w hR a y).2
    have hz := (band_bounds H w hR a z).2
    have hby : band H w R a y = 0 := (band_eq_of_cut_reachable hxy).symm.trans hn0
    have hbz : band H w R a z = 0 := (band_eq_of_cut_reachable hxz).symm.trans hn0
    rw [hby] at hy
    rw [hbz] at hz
    have hyR : height H w y ≤ R := by simp only [Int.cast_zero, zero_mul, zero_sub] at hy; linarith
    have hzR : height H w z ≤ R := by simp only [Int.cast_zero, zero_mul, zero_sub] at hz; linarith
    have hHy := hxy.mono (cut_le H w R a)
    have hHz := hxz.mono (cut_le H w R a)
    have hry := (root_reachable H x).trans hHy
    have hrz := (root_reachable H x).trans hHz
    have hm := distance_mono hHG w hw (hHy.symm.trans hHz)
    have ht := shortestPathDistance_triangle_of_reachable H (weights H w) (fun e => hw e.val)
      hry.symm hrz
    have hs := shortestPathDistance_comm_of_reachable H (weights H w) (fun e => hw e.val) hry
    change distance H w y z ≤ distance H w y (root H x) + distance H w (root H x) z at ht
    change distance H w (root H x) y = distance H w y (root H x) at hs
    rw [← hs, ← height_eq_of_reachable w hHy, ← height_eq_of_reachable w hHz] at ht
    linarith
  · right
    have hn1 : (1 : ℤ) ≤ n := by omega
    have hn1r : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    let t : ℝ := (n : ℝ) * R - a
    have ht : 0 < t := by dsimp [t]; nlinarith
    refine ⟨inner H w x t, (inner_connected H w hw x ht).mono (fun _ _ h => hHG h),
      fun _ hz => inner_reachable hz, ?_, ?_⟩
    · intro z hz hcz
      have hzb := (band_eq_of_cut_reachable hcz).symm
      have hzlo := (band_bounds H w hR a z).1
      rw [hzb] at hzlo
      exact (inner_height hz).not_ge hzlo
    · intro c hxc
      have hHxc := hxc.mono (cut_le H w R a)
      have hcb := (band_eq_of_cut_reachable hxc).symm
      have hc := band_bounds H w hR a c
      rw [hcb] at hc
      obtain ⟨z, hz, hnear⟩ := inner_dominates H w hw hmesh x c hHxc ht hc.1 hc.2.le
      refine ⟨z, hz, (distance_mono hHG w hw ?_).trans hnear⟩
      exact hHxc.symm.trans (inner_reachable hz)

variable {A : Type*}

/-- Successive annulus cuts, with one finite random choice at each round. -/
noncomputable def run (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ) :
    (n : ℕ) → SimpleGraph V → (Fin n → A) → SimpleGraph V
  | 0, H, _ => H
  | n + 1, H, σ => run w R offset n (cut H w R (offset (σ 0))) (fun i => σ i.succ)

lemma run_le (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ)
    (n : ℕ) (H : SimpleGraph V) (σ : Fin n → A) : run w R offset n H σ ≤ H := by
  induction n generalizing H with
  | zero => exact le_rfl
  | succ n ih => exact (ih _ _).trans (cut_le H w R _)

/-- Connected barriers around a final component. The inside/outside fields are
what permit nested cuts to add one more *disjoint* barrier at each round. -/
structure BarrierFamily (G H F : SimpleGraph V) (w : Sym2 V → ℝ)
    (ρ : ℝ) (x : V) (n : ℕ) where
  sets : Fin n → Set V
  connected : ∀ i, (G.induce (sets i)).Connected
  inside : ∀ i z, z ∈ sets i → H.Reachable x z
  outside : ∀ i z, z ∈ sets i → ¬F.Reachable x z
  separated : Pairwise (fun i j => Disjoint (sets i) (sets j))
  dominates : ∀ i c, F.Reachable x c → ∃ z ∈ sets i, distance G w c z ≤ ρ

/-- Deterministic invariant of the annulus recursion. A large component has
one genuinely connected, disjoint nearby barrier for every cut round. -/
theorem run_component_alternative [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R ε : ℝ} (hR : 0 < R) (offset : A → ℝ)
    (hoff0 : ∀ a, 0 ≤ offset a) (hoffR : ∀ a, offset a < R)
    (n : ℕ) (H : SimpleGraph V) (hHG : H ≤ G)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε) (σ : Fin n → A) (x : V) :
    (∀ y z, (run w R offset n H σ).Reachable x y →
      (run w R offset n H σ).Reachable x z → distance G w y z ≤ 2 * R) ∨
    Nonempty (BarrierFamily G H (run w R offset n H σ) w (R + ε) x n) := by
  induction n generalizing H with
  | zero =>
    right
    exact ⟨{ sets := Fin.elim0
             connected := fun i => Fin.elim0 i
             inside := fun i => Fin.elim0 i
             outside := fun i => Fin.elim0 i
             separated := fun i => Fin.elim0 i
             dominates := fun i => Fin.elim0 i }⟩
  | succ n ih =>
    let H' := cut H w R (offset (σ 0))
    let τ : Fin n → A := fun i => σ i.succ
    let F := run w R offset n H' τ
    have hF : run w R offset (n + 1) H σ = F := rfl
    rw [hF]
    have hH'H : H' ≤ H := cut_le H w R _
    have hFH' : F ≤ H' := run_le w R offset n H' τ
    have halt := cut_component_alternative G H hHG w hw hR (hoff0 (σ 0))
      (hoffR (σ 0)) hmesh x
    rcases halt with hsmall | ⟨B, hB, hBin, hBout, hBdom⟩
    · left
      exact fun y z hy hz => hsmall y z (hy.mono hFH') (hz.mono hFH')
    · have hH'G := hH'H.trans hHG
      have hmesh' : ∀ u v, H'.Adj u v → w s(u,v) ≤ ε := fun u v h => hmesh u v (hH'H h)
      rcases ih H' hH'G hmesh' τ with hsmall | hex
      · exact Or.inl hsmall
      · obtain ⟨D⟩ := hex
        right
        refine ⟨{
          sets := Fin.cons B D.sets
          connected := ?_
          inside := ?_
          outside := ?_
          separated := ?_
          dominates := ?_ }⟩
        · intro i
          refine Fin.cases hB (fun j => D.connected j) i
        · intro i
          refine Fin.cases hBin ?_ i
          intro j z hz
          exact (D.inside j z hz).mono hH'H
        · intro i
          refine Fin.cases ?_ (fun j => D.outside j) i
          intro z hz hFz
          exact hBout z hz (hFz.mono hFH')
        · intro i j
          refine Fin.cases ?_ ?_ i
          · refine Fin.cases ?_ ?_ j
            · intro hij; exact (hij rfl).elim
            · intro l _
              apply Set.disjoint_left.mpr
              intro z hzB hzD
              exact hBout z hzB (D.inside l z hzD)
          · intro l
            refine Fin.cases ?_ ?_ j
            · intro _; apply Set.disjoint_left.mpr
              intro z hzD hzB
              exact hBout z hzB (D.inside l z hzD)
            · intro m hij
              exact D.separated (fun hlm => hij (congrArg Fin.succ hlm))
        · intro i
          refine Fin.cases ?_ (fun j => D.dominates j) i
          intro c hc
          exact hBdom c (hc.mono hFH')

lemma reachable_set_connected [DecidableEq V] (H : SimpleGraph V) (x : V) :
    (H.induce {z | H.Reachable x z}).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨⟨x, .rfl⟩, ?_⟩
  rintro ⟨z, hz⟩
  obtain ⟨p⟩ := hz
  have hsupp : ∀ y ∈ p.support, H.Reachable x y := fun y hy => (p.takeUntil y hy).reachable
  exact ⟨(p.induce {z | H.Reachable x z} hsupp).copy (Subtype.ext rfl) (Subtype.ext rfl)⟩

end BoundedTreewidthL1.Annulus

namespace BoundedTreewidthL1

/-- Convexity with respect to the unique simple paths in a tree. -/
def TreePathClosed {I : Type*} (T : SimpleGraph I) (S : Set I) : Prop :=
  ∀ ⦃u v : I⦄, u ∈ S → v ∈ S → ∀ (p : T.Walk u v), p.IsPath →
    ∀ z ∈ p.support, z ∈ S

private theorem tree_helly_aux (n : ℕ) :
    ∀ {I J : Type*} [Fintype I], Fintype.card I ≤ n →
    ∀ (T : SimpleGraph I), T.IsTree → ∀ (S : J → Set I),
    (∀ j, (S j).Nonempty) → (∀ j, TreePathClosed T (S j)) →
    (∀ i j, (S i ∩ S j).Nonempty) → ∃ v, ∀ j, v ∈ S j := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro I J _ hn T hT S hne hconv hpair
    have : Nonempty I := hT.connected.nonempty
    by_cases hsub : Subsingleton I
    · let := hsub
      refine ⟨Classical.choice (inferInstance : Nonempty I), ?_⟩
      intro j
      obtain ⟨z, hz⟩ := hne j
      simpa only [Subsingleton.elim (Classical.choice (inferInstance : Nonempty I)) z] using hz
    · let : Nontrivial I := not_subsingleton_iff_nontrivial.mp hsub
      obtain ⟨v, hv⟩ := hT.exists_vert_degree_one_of_nontrivial
      obtain ⟨u, hvu, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hv
      by_cases hsingle : ∃ j, S j = {v}
      · obtain ⟨j, hj⟩ := hsingle
        refine ⟨v, fun i => ?_⟩
        obtain ⟨z, hzj, hzi⟩ := hpair j i
        have hzv : z = v := by simpa [hj] using hzj
        exact hzv ▸ hzi
      · have hneighbor : ∀ j, v ∈ S j → u ∈ S j := by
          intro j hvj
          have hex : ∃ w ∈ S j, w ≠ v := by
            by_contra! hh
            apply hsingle
            refine ⟨j, Set.Subset.antisymm ?_ ?_⟩
            · intro w hw
              exact Set.mem_singleton_iff.mpr (hh w hw)
            · simpa only [Set.singleton_subset_iff] using hvj
          obtain ⟨w, hw, hwv⟩ := hex
          obtain ⟨p, hp⟩ := hT.connected.exists_isPath v w
          have hnil : ¬p.Nil := SimpleGraph.Walk.not_nil_of_ne hwv.symm
          have hsu : p.snd = u := huniq _ (p.adj_snd hnil)
          exact hsu ▸ hconv j hvj hw p hp _ (p.getVert_mem_support 1)
        let I' := {x : I // x ∈ ({v} : Set I)ᶜ}
        let T' : SimpleGraph I' := T.induce {v}ᶜ
        let S' : J → Set I' := fun j => {x | x.val ∈ S j}
        have hunv : u ∈ ({v} : Set I)ᶜ := by
          simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hvu.ne'
        have hT' : T'.IsTree :=
          ⟨hT.connected.induce_compl_singleton_of_degree_eq_one hv,
            hT.isAcyclic.induce _⟩
        have hne' : ∀ j, (S' j).Nonempty := by
          intro j
          obtain ⟨z, hz⟩ := hne j
          by_cases hzv : z = v
          · exact ⟨⟨u, hunv⟩, hneighbor j (hzv ▸ hz)⟩
          · exact ⟨⟨z, by simpa using hzv⟩, hz⟩
        have hconv' : ∀ j, TreePathClosed T' (S' j) := by
          intro j a b ha hb p hp z hz
          let f := (SimpleGraph.Embedding.induce (G := T) ({v} : Set I)ᶜ).toHom
          have hp' : (p.map f).IsPath := hp.map Subtype.val_injective
          have hmem : f z ∈ (p.map f).support := by
            rw [SimpleGraph.Walk.support_map]
            exact List.mem_map.mpr ⟨z, hz, rfl⟩
          exact hconv j ha hb (p.map f) hp' (f z) hmem
        have hpair' : ∀ i j, (S' i ∩ S' j).Nonempty := by
          intro i j
          obtain ⟨z, hzi, hzj⟩ := hpair i j
          by_cases hzv : z = v
          · exact ⟨⟨u, hunv⟩, hneighbor i (hzv ▸ hzi), hneighbor j (hzv ▸ hzj)⟩
          · exact ⟨⟨z, by simpa using hzv⟩, hzi, hzj⟩
        have hcard : Fintype.card I' < Fintype.card I :=
          Fintype.card_subtype_lt (x := v) (by simp)
        obtain ⟨z, hz⟩ := ih (Fintype.card I') (lt_of_lt_of_le hcard hn)
          (le_refl _) T' hT' S' hne' hconv' hpair'
        exact ⟨z.val, hz⟩

/-- Finite trees have the Helly property for connected vertex sets.  The index
family need not be finite. This is the exact combinatorial input for the
bounded-treewidth padded-partition construction, not a main theorem claim. -/
theorem tree_subtree_helly {I J : Type*} [Fintype I]
    (T : SimpleGraph I) (hT : T.IsTree) (S : J → Set I)
    (hS : ∀ j, (T.induce (S j)).Connected)
    (hpair : ∀ i j, (S i ∩ S j).Nonempty) :
    ∃ v, ∀ j, v ∈ S j := by
  have hne : ∀ j, (S j).Nonempty := fun j => (Set.nonempty_coe_sort.mp (hS j).nonempty)
  have hconv : ∀ j, TreePathClosed T (S j) := by
    intro j u v hu hv p hp z hz
    exact tree_path_mem_connected T hT (hS j) hu hv p hp hz
  exact tree_helly_aux (Fintype.card I) (le_refl _) T hT S hne hconv hpair

/-- An arbitrary nonempty connected vertex set touches a connected set of bags. -/
lemma touched_bags_connected_set {V I : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (S : Set V) (hS : (G.induce S).Connected) :
    (T.induce {t | ∃ z ∈ S, z ∈ bag t}).Connected := by
  obtain ⟨u, hu⟩ := hS.nonempty
  obtain ⟨A, hA⟩ := (hocc u).nonempty
  apply T.induce_connected_of_patches (s := {t | ∃ z ∈ S, z ∈ bag t}) A ⟨u, hu, hA⟩
  rintro B ⟨v, hv, hB⟩
  obtain ⟨p⟩ := hS ⟨u, hu⟩ ⟨v, hv⟩
  let f := (SimpleGraph.Embedding.induce (G := G) S).toHom
  let q := p.map f
  refine ⟨{t | ∃ z ∈ q.support, z ∈ bag t}, ?_,
    ⟨u, q.start_mem_support, hA⟩, ⟨v, q.end_mem_support, hB⟩, ?_⟩
  · rintro t ⟨z, hz, hzt⟩
    have hzS : z ∈ S := by
      change z ∈ (p.map f).support at hz
      rw [SimpleGraph.Walk.support_map] at hz
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hz
      exact a.property
    exact ⟨z, hzS, hzt⟩
  · exact touched_bags_connected G T bag hedge hocc q _ _

lemma card_le_of_pairwise_disjoint_hits {V A : Type*} [DecidableEq V] [Fintype A]
    (bag : Finset V) (X : A → Set V)
    (hdis : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hhit : ∀ i, ∃ v ∈ X i, v ∈ bag) : Fintype.card A ≤ bag.card := by
  classical
  choose f hfX hfb using hhit
  let g : A → ↥bag := fun i => ⟨f i, hfb i⟩
  have hinj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hf : f i = f j := congrArg Subtype.val hij
    exact Set.disjoint_left.mp (hdis hne) (hfX i) (hf.symm ▸ hfX j)
  simpa using Fintype.card_le_of_injective g hinj

/-- A crossbar of two internally disjoint families of connected sets forces
a bag meeting every member of one family. Consequently its size is at least
the smaller family cardinality. This is the deterministic width obstruction
used by iterated annulus partitions. -/
theorem tree_decomposition_crossbar {V I A B : Type*} [DecidableEq V]
    [Fintype I] [Fintype A] [Fintype B]
    (G : SimpleGraph V) (T : SimpleGraph I) (bag : I → Finset V)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (X : A → Set V) (Y : B → Set V)
    (hX : ∀ i, (G.induce (X i)).Connected)
    (hY : ∀ j, (G.induce (Y j)).Connected)
    (hdisX : Pairwise (fun i j => Disjoint (X i) (X j)))
    (hdisY : Pairwise (fun i j => Disjoint (Y i) (Y j)))
    (hcross : ∀ i j, (X i ∩ Y j).Nonempty) :
    ∃ t, min (Fintype.card A) (Fintype.card B) ≤ (bag t).card := by
  classical
  let S : A × B → Set I := fun p => {t | ∃ z ∈ X p.1 ∪ Y p.2, z ∈ bag t}
  have hS : ∀ p, (T.induce (S p)).Connected := by
    intro p
    exact touched_bags_connected_set G T bag hedge hocc _
      (SimpleGraph.induce_union_connected (hX p.1).preconnected (hY p.2).preconnected
        (hcross p.1 p.2))
  have hpair : ∀ p q, (S p ∩ S q).Nonempty := by
    intro p q
    obtain ⟨z, hzX, hzY⟩ := hcross p.1 q.2
    obtain ⟨t, ht⟩ := (hocc z).nonempty
    exact ⟨t, ⟨z, Or.inl hzX, ht⟩, ⟨z, Or.inr hzY, ht⟩⟩
  obtain ⟨t, ht⟩ := tree_subtree_helly T hT S hS hpair
  refine ⟨t, ?_⟩
  by_cases hall : ∀ i, ∃ z ∈ X i, z ∈ bag t
  · exact le_trans (min_le_left _ _) (card_le_of_pairwise_disjoint_hits (bag t) X hdisX hall)
  · push Not at hall
    obtain ⟨i, hi⟩ := hall
    have hYhit : ∀ j, ∃ z ∈ Y j, z ∈ bag t := by
      intro j
      obtain ⟨z, hzX | hzY, hzt⟩ := ht (i, j)
      · exact (hi z hzX hzt).elim
      · exact ⟨z, hzY, hzt⟩
    exact le_trans (min_le_right _ _) (card_le_of_pairwise_disjoint_hits (bag t) Y hdisY hYhit)

/-- A discrete intermediate-value bound with an explicit mesh error. -/
lemma walk_crossing_window {V : Type*} (H : SimpleGraph V) (f : V → ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε)
    (hstep : ∀ a b, H.Adj a b → f b ≤ f a + ε)
    {u v : V} (p : H.Walk u v) (hu : f u ≤ t) (hv : t ≤ f v) :
    ∃ z ∈ p.support, t ≤ f z ∧ f z ≤ t + ε := by
  induction p with
  | @nil x => exact ⟨x, by simp, hv, by linarith⟩
  | @cons a b c hab p ih =>
    by_cases hb : f b ≤ t
    · obtain ⟨z, hz, ht, he⟩ := ih hb hv
      exact ⟨z, by simp [hz], ht, he⟩
    · refine ⟨b, ?_, le_of_lt (lt_of_not_ge hb), ?_⟩
      · simp only [SimpleGraph.Walk.support_cons, List.mem_cons]
        exact Or.inr p.start_mem_support
      · exact (hstep a b hab).trans (by linarith : f a + ε ≤ t + ε)

/-- The deterministic diameter obstruction behind the annulus algorithm.
The radius balls are in the original metric; only the connectivity walk in C
uses the small-edge subgraph H. No intrinsic diameter replaces weak diameter. -/
theorem connected_multidomination_diameter {V I : Type*} [MetricSpace V]
    [DecidableEq V] [Fintype I]
    (G H : SimpleGraph V) (hHG : H ≤ G)
    (T : SimpleGraph I) (bag : I → Finset V) (k : ℕ)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (hwidth : ∀ t, (bag t).card ≤ k)
    {R ε : ℝ} (hR : 0 ≤ R) (hε : 0 < ε)
    (hmesh : ∀ u v, H.Adj u v → dist u v ≤ ε)
    (hballs : ∀ c, (G.induce {z | dist c z ≤ R}).Connected)
    (C : Set V) (hC : (H.induce C).Connected)
    (B : Fin k → Set V) (hB : ∀ i, (G.induce (B i)).Connected)
    (hdisB : Pairwise (fun i j => Disjoint (B i) (B j)))
    (hdisC : ∀ i, Disjoint C (B i))
    (hdom : ∀ i c, c ∈ C → ∃ z ∈ B i, dist c z ≤ R) :
    ∀ u ∈ C, ∀ v ∈ C, dist u v ≤ (k : ℝ) * (2 * R + 2 * ε) := by
  classical
  intro u hu v hv
  by_contra hle
  have hfar : (k : ℝ) * (2 * R + 2 * ε) < dist u v := lt_of_not_ge hle
  obtain ⟨p⟩ := hC ⟨u, hu⟩ ⟨v, hv⟩
  let a : ℝ := 2 * R + 2 * ε
  have ha : 0 < a := by dsimp [a]; positivity
  have hstep : ∀ x y : C, (H.induce C).Adj x y → dist u y.val ≤ dist u x.val + ε := by
    intro x y hxy
    have hm := hmesh x.val y.val hxy
    have ht := dist_triangle u x.val y.val
    linarith
  have hex : ∀ i : Fin (k + 1), ∃ c : C,
      (i.val : ℝ) * a ≤ dist u c.val ∧ dist u c.val ≤ (i.val : ℝ) * a + ε := by
    intro i
    have hstart : dist u (⟨u, hu⟩ : C).val ≤ (i.val : ℝ) * a := by
      simp only [dist_self]
      positivity
    have hend : (i.val : ℝ) * a ≤ dist u (⟨v, hv⟩ : C).val := by
      have hi : (i.val : ℝ) ≤ k := by exact_mod_cast (Nat.le_of_lt_succ i.isLt)
      exact (mul_le_mul_of_nonneg_right hi ha.le).trans hfar.le
    obtain ⟨c, _, hc⟩ := walk_crossing_window (H.induce C) (fun x : C => dist u x.val)
      hε.le hstep p hstart hend
    exact ⟨c, hc⟩
  choose c hclo hchi using hex
  have hsep : ∀ i j : Fin (k + 1), i.val < j.val → 2 * R < dist (c i).val (c j).val := by
    intro i j hij
    have hijr : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast (Nat.succ_le_iff.mpr hij)
    have hm := mul_le_mul_of_nonneg_right hijr ha.le
    have ht := dist_triangle u (c i).val (c j).val
    have hlo := hclo j
    have hhi := hchi i
    dsimp [a] at *
    nlinarith
  let Y : Fin (k + 1) → Set V := fun i => {z | dist (c i).val z ≤ R}
  have hY : ∀ i, (G.induce (Y i)).Connected := fun i => hballs _
  have hdisY : Pairwise (fun i j => Disjoint (Y i) (Y j)) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro z hzi hzj
    have hnear : dist (c i).val (c j).val ≤ 2 * R := by
      have ht := dist_triangle (c i).val z (c j).val
      have hzj' : dist z (c j).val ≤ R := by simpa [Y, dist_comm] using hzj
      change dist (c i).val z ≤ R at hzi
      linarith
    have hvne : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hvne with hlt | hgt
    · exact (hsep i j hlt).not_ge hnear
    · exact (hsep j i hgt).not_ge (by simpa [dist_comm] using hnear)
  let X : Option (Fin k) → Set V := fun i => i.elim C B
  have hCG : (G.induce C).Connected := hC.mono (fun _ _ h => hHG h)
  have hX : ∀ i, (G.induce (X i)).Connected := by
    intro i
    cases i with
    | none => exact hCG
    | some i => exact hB i
  have hdisX : Pairwise (fun i j => Disjoint (X i) (X j)) := by
    intro i j hij
    cases i with
    | none =>
      cases j with
      | none => exact (hij rfl).elim
      | some j => exact hdisC j
    | some i =>
      cases j with
      | none => exact (hdisC i).symm
      | some j => exact hdisB (fun h => hij (congrArg some h))
  have hcross : ∀ i j, (X i ∩ Y j).Nonempty := by
    intro i j
    cases i with
    | none => exact ⟨(c j).val, (c j).property, by simpa [Y] using hR⟩
    | some i => exact hdom i (c j).val (c j).property
  obtain ⟨t, ht⟩ := tree_decomposition_crossbar G T bag hT hedge hocc X Y hX hY hdisX hdisY hcross
  have ht' : k + 1 ≤ (bag t).card := by simpa using ht
  have := hwidth t
  omega

end BoundedTreewidthL1

namespace BoundedTreewidthL1.Annulus

/-- The finite-round annulus decomposition has weak diameter bounded solely
by the width and scale. The metric here remains the original graph metric. -/
theorem run_diameter {V I A : Type*} [Fintype V] [DecidableEq V] [MetricSpace V]
    [Fintype I] (G H : SimpleGraph V) (hHG : H ≤ G)
    (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hdist : ∀ u v, dist u v = distance G w u v)
    (T : SimpleGraph I) (bag : I → Finset V) (k : ℕ) (hk : 1 ≤ k)
    (hT : T.IsTree)
    (hedge : ∀ u v, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t)
    (hocc : ∀ v, (T.induce {t | v ∈ bag t}).Connected)
    (hwidth : ∀ t, (bag t).card ≤ k)
    {R ε : ℝ} (hR : 0 < R) (hε : 0 < ε)
    (hmesh : ∀ u v, H.Adj u v → w s(u,v) ≤ ε)
    (hballs : ∀ c, (G.induce {z | dist c z ≤ R + ε}).Connected)
    (offset : A → ℝ) (hoff0 : ∀ a, 0 ≤ offset a) (hoffR : ∀ a, offset a < R)
    (σ : Fin k → A) (u v : V) (huv : (run w R offset k H σ).Reachable u v) :
    dist u v ≤ (k : ℝ) * (2 * R + 4 * ε) := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rcases run_component_alternative G w hw hR offset hoff0 hoffR k H hHG hmesh σ u with hsmall | hex
  · have hs := hsmall u v .rfl huv
    rw [hdist]
    have hfac : 0 ≤ 2 * R + 4 * ε := by positivity
    have hmul := mul_le_mul_of_nonneg_right hkr hfac
    nlinarith
  · obtain ⟨B⟩ := hex
    let F := run w R offset k H σ
    have hFH : F ≤ H := run_le w R offset k H σ
    have hFG := hFH.trans hHG
    let C : Set V := {z | F.Reachable u z}
    have hC : (F.induce C).Connected := reachable_set_connected F u
    have hCdis : ∀ i, Disjoint C (B.sets i) := by
      intro i
      apply Set.disjoint_left.mpr
      intro z hzC hzB
      exact B.outside i z hzB hzC
    have hdom : ∀ i c, c ∈ C → ∃ z ∈ B.sets i, dist c z ≤ R + ε := by
      intro i c hc
      obtain ⟨z, hz, hnear⟩ := B.dominates i c hc
      exact ⟨z, hz, by rwa [hdist]⟩
    have hFmesh : ∀ a b, F.Adj a b → dist a b ≤ ε := by
      intro a b hab
      rw [hdist]
      exact (distance_edge G w hw (hFG hab)).trans (hmesh a b (hFH hab))
    have hb := connected_multidomination_diameter G F hFG T bag k hT hedge hocc hwidth
      (add_nonneg hR.le hε.le) hε hFmesh hballs C hC B.sets B.connected B.separated hCdis hdom
      u (.rfl) v huv
    convert hb using 1 ; ring

end BoundedTreewidthL1.Annulus

namespace BoundedTreewidthL1.Annulus
variable {V : Type*}
lemma floor_ne_boundary {x y : ℝ} (hxy : x ≤ y) (hne : ⌊x⌋ ≠ ⌊y⌋) :
    ∃ n : ℤ, x < n ∧ (n : ℝ) ≤ y := by
  refine ⟨⌊x⌋ + 1, ?_, ?_⟩
  · simp
  · have hle : ⌊x⌋ < ⌊y⌋ := lt_of_le_of_ne (Int.floor_mono hxy) hne
    have hn : ⌊x⌋ + 1 ≤ ⌊y⌋ := by omega
    exact (by exact_mod_cast hn : ((⌊x⌋ + 1 : ℤ) : ℝ) ≤ ⌊y⌋).trans (Int.floor_le y)

/-- A random finite grid incurs at most one bad offset at any prescribed
height. No minimum positive edge length enters this count. -/
theorem grid_bad_subsingleton (M : ℕ) (hM : 0 < M) (t β : ℝ)
    (hβ : 0 ≤ β) (hsep : 2 * (M : ℝ) * β < 1) :
    {j : Fin M | ⌊t + (j.val : ℝ) / M - β⌋ ≠ ⌊t + (j.val : ℝ) / M + β⌋}.Subsingleton := by
  intro j hj l hl
  obtain ⟨nj, hjlo, hjhi⟩ := floor_ne_boundary (by linarith) hj
  obtain ⟨nl, hllo, hlhi⟩ := floor_ne_boundary (by linarith) hl
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  let qj : ℤ := (M : ℤ) * nj - j.val
  let ql : ℤ := (M : ℤ) * nl - l.val
  have hjdiv : (j.val : ℝ) / M * M = j.val := div_mul_cancel₀ _ hMr.ne'
  have hldiv : (l.val : ℝ) / M * M = l.val := div_mul_cancel₀ _ hMr.ne'
  have hjlo' := mul_lt_mul_of_pos_right hjlo hMr
  have hjhi' := mul_le_mul_of_nonneg_right hjhi hMr.le
  have hllo' := mul_lt_mul_of_pos_right hllo hMr
  have hlhi' := mul_le_mul_of_nonneg_right hlhi hMr.le
  have hqjl : (qj : ℝ) < (ql : ℝ) + 1 := by
    dsimp [qj, ql]
    push_cast
    nlinarith
  have hqlj : (ql : ℝ) < (qj : ℝ) + 1 := by
    dsimp [qj, ql]
    push_cast
    nlinarith
  have hqjli : qj < ql + 1 := by exact_mod_cast hqjl
  have hqlji : ql < qj + 1 := by exact_mod_cast hqlj
  have hqeq : qj = ql := by omega
  have hqeqr : (qj : ℝ) = ql := by exact_mod_cast hqeq
  have hjlt : (j.val : ℝ) < M := by exact_mod_cast j.isLt
  have hllt : (l.val : ℝ) < M := by exact_mod_cast l.isLt
  have hjge : (0 : ℝ) ≤ j.val := by positivity
  have hlge : (0 : ℝ) ≤ l.val := by positivity
  have hneq : nj = nl := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hnlt | hngt
    · have hnle : nj + 1 ≤ nl := by omega
      have hnler : (nj : ℝ) + 1 ≤ nl := by exact_mod_cast hnle
      dsimp [qj, ql] at hqeqr
      push_cast at hqeqr
      nlinarith
    · have hnle : nl + 1 ≤ nj := by omega
      have hnler : (nl : ℝ) + 1 ≤ nj := by exact_mod_cast hnle
      dsimp [qj, ql] at hqeqr
      push_cast at hqeqr
      nlinarith
  have hval : j.val = l.val := by
    dsimp [qj, ql] at hqeq
    rw [hneq] at hqeq
    omega
  exact Fin.ext hval

lemma floor_eq_of_window {t s β : ℝ} (hlo : t - β ≤ s) (hhi : s ≤ t + β)
    (hgood : ⌊t - β⌋ = ⌊t + β⌋) : ⌊s⌋ = ⌊t⌋ := by
  have hβ : 0 ≤ β := by linarith
  have h1 := Int.floor_mono hlo
  have h2 := Int.floor_mono hhi
  have h3 := Int.floor_mono (by linarith : t - β ≤ t)
  have h4 := Int.floor_mono (by linarith : t ≤ t + β)
  omega

lemma walkLength_edge_le {H : SimpleGraph V} (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {u v : V} (p : H.Walk u v) {e : Sym2 V} (he : e ∈ p.edges) :
    w e ≤ walkLength H (weights H w) p := by
  induction p with
  | nil => simp at he
  | @cons u v z h p ih =>
    simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
    rcases he with rfl | he
    · have hn := walkLength_nonneg H (weights H w) (fun e => hw e.val) p
      change w s(u,v) ≤ w s(u,v) + _
      linarith
    · have hle := ih he
      have hn := hw s(u,v)
      change w e ≤ w s(u,v) + _
      linarith

noncomputable def smallEdges (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) : SimpleGraph V where
  Adj u v := G.Adj u v ∧ w s(u,v) ≤ ε
  symm := ⟨fun u v h => ⟨h.1.symm, by simpa only [Sym2.eq_swap] using h.2⟩⟩
  loopless := ⟨fun _ h => G.irrefl h.1⟩

lemma smallEdges_le (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) : smallEdges G w ε ≤ G :=
  fun _ _ h => h.1

lemma smallEdges_mesh (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) :
    ∀ u v, (smallEdges G w ε).Adj u v → w s(u,v) ≤ ε := fun _ _ h => h.2

lemma smallEdges_mem_iff (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) (e : Sym2 V) :
    e ∈ (smallEdges G w ε).edgeSet ↔ e ∈ G.edgeSet ∧ w e ≤ ε := by
  induction e using Sym2.inductionOn with
  | _ u v => rfl

/-- The ball is preserved with its actual original shortest paths, not only
with unquantified reachability. This is the induction invariant for padding. -/
def PreservesBall (G H : SimpleGraph V) (w : Sym2 V → ℝ) (ε : ℝ) (x : V) : Prop :=
  ∀ y, distance G w x y ≤ ε →
    ∃ p : H.Walk x y, walkLength H (weights H w) p = distance G w x y

lemma smallEdges_preserves [Fintype V] (G : SimpleGraph V) (w : Sym2 V → ℝ)
    (hw : ∀ e, 0 ≤ w e) (hG : G.Connected) (ε : ℝ) (x : V) :
    PreservesBall G (smallEdges G w ε) w ε x := by
  intro y hy
  obtain ⟨p, _, hp⟩ := shortestPathDistance_attained_of_reachable G (weights G w) (hG x y)
  have hedges : ∀ e ∈ p.edges, e ∈ (smallEdges G w ε).edgeSet := by
    intro e he
    rw [smallEdges_mem_iff]
    refine ⟨p.edges_subset_edgeSet he, ?_⟩
    exact (walkLength_edge_le w hw p he).trans (hp ▸ hy)
  exact ⟨p.transfer _ hedges, (walkLength_transfer w p hedges).trans hp⟩

lemma walk_height_window [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {x y z : V} (p : H.Walk x y) (hz : z ∈ p.support) {ε : ℝ}
    (hp : walkLength H (weights H w) p ≤ ε) :
    height H w x - ε ≤ height H w z ∧ height H w z ≤ height H w x + ε := by
  let q := p.takeUntil z hz
  have hq : walkLength H (weights H w) q ≤ ε :=
    (walkLength_takeUntil_le H (weights H w) (fun e => hw e.val) p hz).trans hp
  have hd : distance H w x z ≤ ε :=
    (shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) q).trans hq
  have hds : distance H w z x ≤ ε := by
    have heq := walkLength_reverse H (weights H w) q
    exact (shortestPathDistance_le_walkLength H (weights H w) (fun e => hw e.val) q.reverse).trans
      (heq ▸ hq)
  have h1 := height_le_add_distance H w hw q.reachable
  have h2 := height_le_add_distance H w hw q.reachable.symm
  constructor <;> linarith

lemma band_eq_of_height_window (H : SimpleGraph V) (w : Sym2 V → ℝ)
    {R ε a : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) {x z : V}
    (hlo : height H w x - ε ≤ height H w z)
    (hhi : height H w z ≤ height H w x + ε)
    (hgood : ⌊(height H w x + a - ε) / R⌋ = ⌊(height H w x + a + ε) / R⌋) :
    band H w R a z = band H w R a x := by
  have hzlo := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a - ε ≤ height H w z + a) hR.le)
  have hzhi := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w z + a ≤ height H w x + a + ε) hR.le)
  have hxlo := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a - ε ≤ height H w x + a) hR.le)
  have hxhi := Int.floor_mono (div_le_div_of_nonneg_right (by linarith :
      height H w x + a ≤ height H w x + a + ε) hR.le)
  unfold band
  omega

lemma preservesBall_cut [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    {R ε a : ℝ} (hR : 0 < R) (hε : 0 ≤ ε) (x : V)
    (hpres : PreservesBall G H w ε x)
    (hgood : ⌊(height H w x + a - ε) / R⌋ = ⌊(height H w x + a + ε) / R⌋) :
    PreservesBall G (cut H w R a) w ε x := by
  intro y hy
  obtain ⟨p, hp⟩ := hpres y hy
  have hlen : walkLength H (weights H w) p ≤ ε := hp ▸ hy
  have hband : ∀ z ∈ p.support, band H w R a z = band H w R a x := by
    intro z hz
    obtain ⟨hlo, hhi⟩ := walk_height_window H w hw p hz hlen
    exact band_eq_of_height_window H w hR hε hlo hhi hgood
  have hedges : ∀ e ∈ p.edges, e ∈ (cut H w R a).edgeSet := by
    intro e
    induction e using Sym2.inductionOn with
    | _ u v =>
      intro he
      exact ⟨p.edges_subset_edgeSet he,
        (hband u (p.fst_mem_support_of_mem_edges he)).trans
          (hband v (p.snd_mem_support_of_mem_edges he)).symm⟩
  exact ⟨p.transfer _ hedges, (walkLength_transfer w p hedges).trans hp⟩

noncomputable def gridOffset (M : ℕ) (R : ℝ) (a : Fin M) : ℝ := R * ((a.val : ℝ) / M)

lemma gridOffset_nonneg {M : ℕ} {R : ℝ} (hR : 0 ≤ R) (a : Fin M) :
    0 ≤ gridOffset M R a := by unfold gridOffset; positivity

lemma gridOffset_lt {M : ℕ} {R : ℝ} (hR : 0 < R) (a : Fin M) :
    gridOffset M R a < R := by
  have hM : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt a.isLt)
  have ha : (a.val : ℝ) < M := by exact_mod_cast a.isLt
  have haf : (a.val : ℝ) / M < 1 := by rwa [div_lt_one hM]
  exact (mul_lt_mul_of_pos_left haf hR).trans_eq (mul_one R)

lemma grid_window_eq {M : ℕ} {R ε t : ℝ} (hR : 0 < R) (a : Fin M) :
    (⌊(t + gridOffset M R a - ε) / R⌋ = ⌊(t + gridOffset M R a + ε) / R⌋) ↔
    (⌊t / R + (a.val : ℝ) / M - ε / R⌋ = ⌊t / R + (a.val : ℝ) / M + ε / R⌋) := by
  have hcancel : gridOffset M R a / R = (a.val : ℝ) / M := by
    dsimp [gridOffset]
    exact mul_div_cancel_left₀ _ hR.ne'
  simp only [sub_div, add_div, hcancel]

end BoundedTreewidthL1.Annulus

/-! Finite adaptive random iteration. No independence assumptions on an
intermediate state: every fresh coordinate is independently enumerated. -/
namespace FiniteRandomIteration

variable {S : Type*} {A : Type*}

def run (step : S → A → S) : (n : ℕ) → S → (Fin n → A) → S
  | 0, s, _ => s
  | n + 1, s, σ => run step n (step s (σ 0)) (Fin.tail σ)

noncomputable def count [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) : ℝ := by
  classical
  exact ∑ σ : Fin n → A, if P (run step n s σ) then 1 else 0

lemma count_nonneg [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) : 0 ≤ count step P n s := by
  classical
  exact Finset.sum_nonneg fun σ _ => by split <;> norm_num

lemma count_succ [Fintype A] (step : S → A → S) (P : S → Prop)
    (n : ℕ) (s : S) :
    count step P (n+1) s = ∑ a : A, count step P n (step s a) := by
  classical
  unfold count
  rw [← (Fin.consEquiv (fun _ : Fin (n+1) => A)).sum_comp]
  rw [Fintype.sum_prod_type]
  congr 1

lemma count_lower [Fintype A] [Nonempty A]
    (step : S → A → S) (P : S → Prop)
    (hbad : ∀ s, P s → {a : A | ¬ P (step s a)}.Subsingleton)
    (n : ℕ) (s : S) (hs : P s) :
    ((Fintype.card A : ℝ) - 1)^n ≤ count step P n s := by
  classical
  have hc : (0 : ℝ) ≤ Fintype.card A - 1 := by
    have h : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
    linarith
  induction n generalizing s with
  | zero => simp [count, run, hs]
  | succ n ih =>
    rw [count_succ]
    have hgood : (Fintype.card A : ℝ) - 1 ≤
        ∑ a : A, if P (step s a) then (1 : ℝ) else 0 := by
      rw [Finset.sum_boole]
      have hb : (Finset.univ.filter fun a : A => ¬ P (step s a)).card ≤ 1 := by
        rw [Finset.card_le_one_iff]
        intro a b ha hb
        exact hbad s hs (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
      have heq := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun a : A => P (step s a))
      have hcard : Fintype.card A ≤ (Finset.univ.filter fun a => P (step s a)).card + 1 := by
        simp only [Finset.card_univ] at heq
        omega
      have hcR : (Fintype.card A : ℝ) ≤ (Finset.univ.filter fun a => P (step s a)).card + 1 := by exact_mod_cast hcard
      linarith
    calc
      ((Fintype.card A : ℝ) - 1)^(n+1) =
          ((Fintype.card A : ℝ) - 1) * ((Fintype.card A : ℝ) - 1)^n := by rw [pow_succ'];
      _ ≤ (∑ a : A, if P (step s a) then (1 : ℝ) else 0) *
          ((Fintype.card A : ℝ) - 1)^n := mul_le_mul_of_nonneg_right hgood (pow_nonneg hc n)
      _ = ∑ a : A, if P (step s a) then ((Fintype.card A : ℝ) - 1)^n else 0 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        split <;> simp
      _ ≤ ∑ a : A, count step P n (step s a) := by
        apply Finset.sum_le_sum
        intro a _
        split_ifs with ha
        · exact ih (step s a) ha
        · exact count_nonneg step P n (step s a)

lemma fraction_lower [Fintype A] [Nonempty A]
    (step : S → A → S) (P : S → Prop)
    (hbad : ∀ s, P s → {a : A | ¬ P (step s a)}.Subsingleton)
    (n : ℕ) (s : S) (hs : P s) :
    1 - (n : ℝ) / Fintype.card A ≤
      count step P n s / (Fintype.card A : ℝ)^n := by
  have hM : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have hM1 : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos (α := A)
  have ha : (-2 : ℝ) ≤ -(1 / (Fintype.card A : ℝ)) := by
    have hh : 1 / (Fintype.card A : ℝ) ≤ 1 := (div_le_one hM).mpr hM1
    linarith
  have hbern := one_add_mul_le_pow ha n
  calc
    1 - (n : ℝ) / Fintype.card A ≤ (1 - 1 / (Fintype.card A : ℝ))^n := by
      simpa only [sub_eq_add_neg, mul_neg, mul_one_div] using hbern
    _ = (((Fintype.card A : ℝ) - 1)^n) / (Fintype.card A : ℝ)^n := by
      rw [← div_pow]
      congr 1
      field_simp
    _ ≤ count step P n s / (Fintype.card A : ℝ)^n :=
      div_le_div_of_nonneg_right (count_lower step P hbad n s hs) (pow_nonneg hM.le n)

end FiniteRandomIteration

namespace BoundedTreewidthL1.Annulus
variable {V A : Type*}

lemma run_eq_iteration (w : Sym2 V → ℝ) (R : ℝ) (offset : A → ℝ)
    (n : ℕ) (H : SimpleGraph V) (σ : Fin n → A) :
    run w R offset n H σ =
    FiniteRandomIteration.run (fun H a => cut H w R (offset a)) n H σ := by
  induction n generalizing H with
  | zero => rfl
  | succ n ih => exact ih _ _

lemma preserves_bad_subsingleton [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (M : ℕ) (hM : 0 < M) {R ε : ℝ} (hR : 0 < R) (hε : 0 ≤ ε)
    (hsep : 2 * (M : ℝ) * (ε / R) < 1) (x : V)
    (hpres : PreservesBall G H w ε x) :
    {a : Fin M | ¬ PreservesBall G (cut H w R (gridOffset M R a)) w ε x}.Subsingleton := by
  have hgrid := grid_bad_subsingleton M hM (height H w x / R) (ε / R)
    (div_nonneg hε hR.le) hsep
  have hbadfloor : ∀ a : Fin M, ¬ PreservesBall G (cut H w R (gridOffset M R a)) w ε x →
      ⌊height H w x / R + (a.val : ℝ) / M - ε / R⌋ ≠
      ⌊height H w x / R + (a.val : ℝ) / M + ε / R⌋ := by
    intro a ha hg
    exact ha (preservesBall_cut G H w hw hR hε x hpres ((grid_window_eq hR a).mpr hg))
  intro a ha b hb
  exact hgrid (hbadfloor a ha) (hbadfloor b hb)

attribute [local instance] Classical.propDecidable
lemma preserves_fraction [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (hw : ∀ e, 0 ≤ w e)
    (hG : G.Connected) (M : ℕ) (hM : 0 < M) {R ε : ℝ}
    (hR : 0 < R) (hε : 0 ≤ ε) (hsep : 2 * (M : ℝ) * (ε / R) < 1)
    (n : ℕ) (x : V) :
    1 - (n : ℝ) / M ≤
      (∑ σ : Fin n → Fin M,
        if PreservesBall G (run w R (gridOffset M R) n (smallEdges G w ε) σ) w ε x
        then (1 : ℝ) else 0) / (M : ℝ)^n := by
  classical
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  have hh := FiniteRandomIteration.fraction_lower (fun H a => cut H w R (gridOffset M R a))
    (fun H => PreservesBall G H w ε x)
    (fun H hp => preserves_bad_subsingleton G H w hw M hM hR hε hsep x hp)
    n (smallEdges G w ε) (smallEdges_preserves G w hw hG ε x)
  simpa only [FiniteRandomIteration.count, ← run_eq_iteration, Fintype.card_fin] using hh

end BoundedTreewidthL1.Annulus

namespace FiniteLawPush
attribute [local instance] Classical.propDecidable
variable {Ω B : Type*} [Fintype Ω] [Fintype B]

noncomputable def law (f : Ω → B) (b : B) : ℝ := by
  classical
  exact ∑ ω, if f ω = b then 1 / Fintype.card Ω else 0

lemma nonneg
    {Ω : Type treewidthLevel1} {B : Type treewidthLevel2} [Fintype Ω] [Fintype B]
    (f : Ω → B) (b : B) : 0 ≤ law f b := by
  classical
  exact Finset.sum_nonneg fun ω _ => by split <;> positivity

lemma total [Nonempty Ω] (f : Ω → B) : (∑ b, law f b) = 1 := by
  classical
  unfold law
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  exact mul_one_div_cancel (by exact_mod_cast Fintype.card_ne_zero (α := Ω))

lemma supported
    {Ω : Type treewidthLevel1} {B : Type treewidthLevel2} [Fintype Ω] [Fintype B]
    (f : Ω → B) (b : B) (hb : 0 < law f b) : ∃ ω, f ω = b := by
  classical
  by_contra! hh
  have hz : law f b = 0 := by simp [law, hh]
  linarith

lemma event (f : Ω → B) (Q : B → Prop) :
    (∑ b, if Q b then law f b else 0) =
    (∑ ω, if Q (f ω) then (1 : ℝ) else 0) / Fintype.card Ω := by
  classical
  unfold law
  calc
    (∑ b, if Q b then (∑ ω, if f ω = b then 1 / (Fintype.card Ω : ℝ) else 0) else 0) =
        ∑ b, ∑ ω, if f ω = b then (if Q b then 1 / (Fintype.card Ω : ℝ) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro b _
      by_cases hb : Q b <;> simp [hb]
    _ = ∑ ω, ∑ b, if f ω = b then (if Q b then 1 / (Fintype.card Ω : ℝ) else 0) else 0 := Finset.sum_comm
    _ = (∑ ω, if Q (f ω) then (1 : ℝ) else 0) / Fintype.card Ω := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      split <;> simp_all
end FiniteLawPush

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1
namespace PaddedPartitions

/-- A partition is represented by its block-label map. The fibers are the
blocks; using vertices as labels represents every partition of a finite
nonempty vertex set. Unused labels impose no extra block condition. -/
abbrev Partition (V : Type*) := V → V

/-- Weak diameter, measured in the original weighted graph metric. -/
def BoundedDiameter {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (r : ℝ) (P : Partition V) : Prop :=
  ∀ u v, P u = P v → shortestPathDistance G ℓ u v ≤ r

/-- The closed metric ball is contained in the block containing x. -/
def PaddedAt {V : Type*} (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ)
    (s : ℝ) (P : Partition V) (x : V) : Prop :=
  ∀ y, shortestPathDistance G ℓ x y ≤ s → P y = P x

noncomputable def paddingProbability {V : Type*} [Fintype V]
    (G : SimpleGraph V) (ℓ : G.edgeSet → ℝ) (s : ℝ)
    (μ : Partition V → ℝ) (x : V) : ℝ := by
  classical
  exact ∑ P, if PaddedAt G ℓ s P x then μ P else 0

def UniformPaddedPartitions : Prop :=
  ∀ k : ℕ, 2 ≤ k → ∃ α π : ℝ,
    0 < α ∧ α ≤ 1 / 8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V), G.Connected → HasTreeDecomposition G k →
      ∀ ℓ : G.edgeSet → ℝ, (∀ e, 0 < ℓ e) →
      ∀ r : ℝ, 0 < r → ∃ μ : Partition V → ℝ,
        (∀ P, 0 ≤ μ P) ∧ (∑ P, μ P) = 1 ∧
        (∀ P, 0 < μ P → BoundedDiameter G ℓ r P) ∧
        ∀ x, π ≤ paddingProbability G ℓ (α * r) μ x

end PaddedPartitions
end BoundedTreewidthL1

namespace BoundedTreewidthL1.PaddedPartitions
open Annulus

theorem uniform_padded_partitions : UniformPaddedPartitions := by
  classical
  intro k hk
  have hk0 : 0 < k := by omega
  have hkR : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hkR0 : (0 : ℝ) < k := by positivity
  let α : ℝ := 1 / (64 * (k : ℝ)^2)
  have hα : 0 < α := by dsimp [α]; positivity
  have hα8 : α ≤ 1 / 8 := by
    dsimp [α]
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
    nlinarith
  refine ⟨α, 1/2, hα, hα8, by norm_num, by norm_num, ?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ r hr
  let w : Sym2 V → ℝ := fun e => if h : e ∈ G.edgeSet then ℓ ⟨e, h⟩ else 0
  have hw : ∀ e, 0 ≤ w e := by
    intro e
    dsimp [w]
    split_ifs with h
    · exact (hℓ ⟨e, h⟩).le
    · exact le_rfl
  have hweights : weights G w = ℓ := by
    funext e
    simp [weights, w, e.property]
  let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
  have hdist : ∀ u v, dist u v = distance G w u v := by
    intro u v
    change shortestPathDistance G ℓ u v = shortestPathDistance G (weights G w) u v
    rw [hweights]
  let M := 4 * k
  have hM : 0 < M := by dsimp [M]; omega
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMR4 : (M : ℝ) = 4 * (k : ℝ) := by simp [M]
  let R := r / (4 * (k : ℝ))
  have hR : 0 < R := by dsimp [R]; positivity
  let ε := R / (4 * (M : ℝ))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεα : ε = α * r := by
    dsimp [ε, R, α]
    rw [hMR4]
    field_simp
    ; ring
  have hsep : 2 * (M : ℝ) * (ε / R) < 1 := by
    have heq : 2 * (M : ℝ) * (ε / R) = 1/2 := by
      dsimp [ε]
      field_simp
      ; ring
    rw [heq]
    norm_num
  have hdiam : (k : ℝ) * (2 * R + 4 * ε) ≤ r := by
    have hMlarge : (1 : ℝ) ≤ M := by rw [hMR4]; nlinarith
    have hεR : 4 * ε ≤ R := by
      have heq : 4 * ε = R / (M : ℝ) := by
        dsimp [ε]
        field_simp
      rw [heq]
      apply (div_le_iff₀ hMR).mpr
      nlinarith
    have hkr : (k : ℝ) * R = r/4 := by dsimp [R]; field_simp [hkR0.ne']
    nlinarith
  obtain ⟨d, T, bag, hT, hcover, hedge, hocc, hwidth⟩ := hdec
  let H := smallEdges G w ε
  let F : (Fin k → Fin M) → SimpleGraph V := run w R (gridOffset M R) k H
  let P : (Fin k → Fin M) → Partition V := fun σ => root (F σ)
  have hPdiam : ∀ σ, BoundedDiameter G ℓ r (P σ) := by
    intro σ u v huv
    have hreach : (F σ).Reachable u v := by
      have hu := root_reachable (F σ) u
      have hv := root_reachable (F σ) v
      change root (F σ) u = root (F σ) v at huv
      rw [huv] at hu
      exact hu.symm.trans hv
    have hballs : ∀ c, (G.induce {z | dist c z ≤ R + ε}).Connected := by
      intro c
      exact shortest_closedBall_connected G ℓ hG (fun e => (hℓ e).le) c (by positivity)
    have hd := run_diameter G H (smallEdges_le G w ε) w hw hdist T bag k
      (by omega) hT hedge hocc hwidth hR hε (smallEdges_mesh G w ε) hballs
      (gridOffset M R) (gridOffset_nonneg hR.le) (gridOffset_lt hR) σ u v hreach
    exact hd.trans hdiam
  let μ := FiniteLawPush.law P
  let : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
  refine ⟨μ, FiniteLawPush.nonneg P, FiniteLawPush.total P, ?_, ?_⟩
  · intro Q hQ
    obtain ⟨σ, rfl⟩ := FiniteLawPush.supported P Q hQ
    exact hPdiam σ
  · intro x
    have hcount := preserves_fraction G w hw hG M hM hR hε.le hsep k x
    have hgood : ∀ σ, PreservesBall G (F σ) w ε x → PaddedAt G ℓ (α*r) (P σ) x := by
      intro σ hp y hy
      have hdy : distance G w x y ≤ ε := by
        dsimp [distance]
        rw [hweights, hεα]
        exact hy
      obtain ⟨p, _⟩ := hp y hdy
      exact root_eq p.reachable.symm
    have hsum : (∑ σ : Fin k → Fin M,
        if PreservesBall G (F σ) w ε x then (1 : ℝ) else 0) ≤
        ∑ σ : Fin k → Fin M, if PaddedAt G ℓ (α*r) (P σ) x then (1 : ℝ) else 0 := by
      apply Finset.sum_le_sum
      intro σ _
      by_cases hp : PreservesBall G (F σ) w ε x
      · simp [hp, hgood σ hp]
      · simp only [hp, ↓reduceIte]
        split <;> norm_num
    have hhalf : (1 : ℝ)/2 ≤ 1 - (k : ℝ)/M := by
      rw [hMR4]
      have hq : (k : ℝ) / (4 * (k : ℝ)) = 1/4 := by field_simp [hkR0.ne']
      rw [hq]
      norm_num
    calc
      (1 : ℝ)/2 ≤ 1 - (k : ℝ)/M := hhalf
      _ ≤ (∑ σ : Fin k → Fin M,
          if PreservesBall G (F σ) w ε x then (1 : ℝ) else 0) / (M : ℝ)^k := hcount
      _ ≤ (∑ σ : Fin k → Fin M,
          if PaddedAt G ℓ (α*r) (P σ) x then (1 : ℝ) else 0) / (M : ℝ)^k :=
        div_le_div_of_nonneg_right hsum (pow_nonneg hMR.le k)
      _ = paddingProbability G ℓ (α*r) μ x := by
        let : DecidableEq V := Classical.decEq V
        unfold paddingProbability
        have hh := (FiniteLawPush.event P (fun Q => PaddedAt G ℓ (α*r) Q x)).symm
        simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hh

end BoundedTreewidthL1.PaddedPartitions

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1
namespace LaunchNoise
open Metric
variable {V I : Type*} [MetricSpace V] [Fintype I]
noncomputable def bump (E : Set V) (r : ℝ) (x : V) : ℝ :=
  by
    classical
    exact if Eᶜ.Nonempty then min r (infDist x Eᶜ) else r
noncomputable def noise (E : I → Set V) (r U : I → ℝ) (x : V) : ℝ :=
  ∑ i, U i * bump (E i) (r i) x

lemma bump_lipschitz (E : Set V) (r : ℝ) : LipschitzWith 1 (bump E r) := by
  classical
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases h : Eᶜ.Nonempty
  · simpa only [bump, h, ↓reduceIte] using
      ((lipschitz_infDist_pt (s := Eᶜ)).const_min r).dist_le_mul x y
  · simp [bump, h]

lemma bump_bounds (E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    0 ≤ bump E r x ∧ bump E r x ≤ r := by
  classical
  unfold bump
  split_ifs
  · exact ⟨le_min hr infDist_nonneg, min_le_left _ _⟩
  · exact ⟨hr, le_rfl⟩

lemma bump_zero (E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) (hx : x ∉ E) :
    bump E r x = 0 := by
  have h : Eᶜ.Nonempty := ⟨x, hx⟩
  simp [bump, h, infDist_zero_of_mem (show x ∈ Eᶜ from hx), hr]

lemma bump_le_dist (E : Set V) (r : ℝ) (x y : V) (hy : y ∉ E) :
    bump E r x ≤ dist x y := by
  have h : Eᶜ.Nonempty := ⟨y, hy⟩
  simp only [bump, h, ↓reduceIte]
  exact (min_le_right _ _).trans (infDist_le_dist_of_mem (show y ∈ Eᶜ from hy))

lemma bump_padding (E : Set V) (r : ℝ) (x : V) (a : ℝ)
    (har : a ≤ r) (hball : ball x a ⊆ E) : a ≤ bump E r x := by
  classical
  by_cases h : Eᶜ.Nonempty
  · simp only [bump, h, ↓reduceIte, le_min_iff]
    refine ⟨har, le_of_not_gt ?_⟩
    intro ht
    obtain ⟨y, hy, hxy⟩ := (infDist_lt_iff h).mp ht
    exact hy (hball (by simpa [mem_ball, dist_comm] using hxy))
  · simp [bump, h, har]

theorem bump_properties (E : Set V) (r : ℝ) (hr : 0 ≤ r) :
    LipschitzWith 1 (bump E r) ∧
    (∀ x, 0 ≤ bump E r x ∧ bump E r x ≤ r) ∧
    (∀ x, x ∉ E → bump E r x = 0) ∧
    (∀ x y, y ∉ E → bump E r x ≤ dist x y) ∧
    (∀ x a, a ≤ r → ball x a ⊆ E → a ≤ bump E r x) :=
  ⟨bump_lipschitz E r, bump_bounds E r hr, bump_zero E r hr,
    bump_le_dist E r, bump_padding E r⟩

lemma noise_at (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (i : I) (x : V) (hx : x ∈ E i) :
    noise E r U x = U i * bump (E i) (r i) x := by
  classical
  unfold noise
  apply Finset.sum_eq_single i
  · intro j _ hji
    have hxj : x ∉ E j := fun hxj => Set.disjoint_left.mp (hE hji) hxj hx
    simp [bump_zero _ _ (hr j) _ hxj]
  · simp

lemma noise_zero (E : I → Set V) (r U : I → ℝ) (hr : ∀ i, 0 ≤ r i)
    (x : V) (hx : ∀ i, x ∉ E i) : noise E r U x = 0 := by
  simp [noise, fun i => bump_zero (E i) (r i) (hr i) x (hx i)]

lemma noise_nonneg (E : I → Set V) (r U : I → ℝ)
    (hr : ∀ i, 0 ≤ r i) (hU : ∀ i, 0 ≤ U i) (x : V) :
    0 ≤ noise E r U x := by
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hU i) (bump_bounds _ _ (hr i) x).1

lemma noise_upper (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) (i : I) (x : V) (hx : x ∈ E i) :
    noise E r U x ≤ r i := by
  rw [noise_at E r U hE hr i x hx]
  exact (mul_le_of_le_one_left (bump_bounds _ _ (hr i) x).1 (hU i).2).trans
    (bump_bounds _ _ (hr i) x).2

lemma noise_one_sided (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) (x y : V) :
    noise E r U x - noise E r U y ≤ dist x y := by
  classical
  by_cases hx : ∃ i, x ∈ E i
  · obtain ⟨i, hi⟩ := hx
    rw [noise_at E r U hE hr i x hi]
    by_cases hy : y ∈ E i
    · rw [noise_at E r U hE hr i y hy, ← mul_sub]
      have hb := (bump_lipschitz (E i) (r i)).dist_le_mul x y
      simp only [Real.dist_eq, NNReal.coe_one, one_mul] at hb
      have hsub := (le_abs_self (bump (E i) (r i) x - bump (E i) (r i) y)).trans hb
      calc U i * (bump (E i) (r i) x - bump (E i) (r i) y)
          ≤ U i * dist x y := mul_le_mul_of_nonneg_left hsub (hU i).1
        _ ≤ dist x y := mul_le_of_le_one_left dist_nonneg (hU i).2
    · have h1 := bump_le_dist (E i) (r i) x y hy
      have h2 := noise_nonneg E r U hr (fun j => (hU j).1) y
      have h3 := mul_le_of_le_one_left (bump_bounds (E i) (r i) (hr i) x).1 (hU i).2
      linarith
  · have h0 := noise_zero E r U hr x (by simpa using hx)
    have h1 := noise_nonneg E r U hr (fun i => (hU i).1) y
    rw [h0]
    linarith [dist_nonneg (x := x) (y := y)]

theorem disjoint_noise (E : I → Set V) (r U : I → ℝ)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) (hr : ∀ i, 0 ≤ r i)
    (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (noise E r U) ∧
    (∀ x, 0 ≤ noise E r U x) ∧
    (∀ i x, x ∈ E i → noise E r U x ≤ r i) ∧
    (∀ x, (∀ i, x ∉ E i) → noise E r U x = 0) := by
  refine ⟨?_, noise_nonneg E r U hr (fun i => (hU i).1),
    noise_upper E r U hE hr hU, noise_zero E r U hr⟩
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  constructor
  · have := noise_one_sided E r U hE hr hU y x
    rw [dist_comm] at this
    linarith
  · exact noise_one_sided E r U hE hr hU x y
end LaunchNoise
end BoundedTreewidthL1
/-! Two deterministic shifted dyadic grids. A fair choice has the same
one-half interior probability needed by ordinary launch noise. -/
namespace BoundedTreewidthL1.LaunchNoise
noncomputable def bandIndex (a t : ℝ) : ℤ := ⌊Real.logb 2 (t/a)⌋
noncomputable def bandLower (a t : ℝ) : ℝ := a * (2:ℝ) ^ bandIndex a t

noncomputable def gridFactor (b : Bool) : ℝ := if b then 3/2 else 1

lemma band_bounds (a t : ℝ) (ha : 0 < a) (ht : 0 < t) :
    0 < bandLower a t ∧ bandLower a t ≤ t ∧ t < 2 * bandLower a t := by
  have hp : 0 < t/a := div_pos ht ha
  have hl := (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hp).mp
    (Int.floor_le (Real.logb 2 (t/a)))
  have hu := (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hp).mp
    (Int.lt_floor_add_one (Real.logb 2 (t/a)))
  simp only [Real.rpow_intCast] at hl
  rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_intCast, Real.rpow_one] at hu
  dsimp [bandLower, bandIndex]
  have hlow := (le_div_iff₀ ha).mp hl
  have hupp := (div_lt_iff₀ ha).mp hu
  exact ⟨mul_pos ha (zpow_pos (by norm_num) _), by nlinarith, by nlinarith⟩

lemma bandIndex_eq (a t : ℝ) (j : ℤ) (ha : 0 < a) (ht : 0 < t)
    (hl : a * (2:ℝ)^j ≤ t) (hu : t < 2 * (a * (2:ℝ)^j)) :
    bandIndex a t = j := by
  apply Int.floor_eq_iff.mpr
  have hp := div_pos ht ha
  constructor
  · apply (Real.le_logb_iff_rpow_le (by norm_num : (1:ℝ)<2) hp).mpr
    rw [Real.rpow_intCast]
    exact (le_div_iff₀ ha).mpr (by nlinarith)
  · apply (Real.logb_lt_iff_lt_rpow (by norm_num : (1:ℝ)<2) hp).mpr
    rw [Real.rpow_add (by norm_num : (0:ℝ)<2), Real.rpow_intCast, Real.rpow_one]
    exact (div_lt_iff₀ ha).mpr (by nlinarith)

lemma band_same (a t u : ℝ) (ha : 0 < a) (_ : 0 < t) (hu : 0 < u)
    (hlo : bandLower a t ≤ u) (hhi : u < 2 * bandLower a t) :
    bandIndex a u = bandIndex a t :=
  bandIndex_eq a u (bandIndex a t) ha hu hlo hhi

lemma gridFactor_pos (b : Bool) : 0 < gridFactor b := by cases b <;> norm_num [gridFactor]

/-- Every positive height lies well inside one of the two grids. -/
theorem two_grid_margin (t : ℝ) (ht : 0 < t) :
    ∃ b : Bool, t/8 ≤ t - bandLower (gridFactor b) t ∧
      t/8 ≤ 2 * bandLower (gridFactor b) t - t := by
  let j := bandIndex 1 t
  let L := bandLower 1 t
  have hb := band_bounds 1 t (by norm_num) ht
  change 0 < L ∧ L ≤ t ∧ t < 2*L at hb
  have hL : L = (2:ℝ)^j := by simp [L, bandLower, j]
  by_cases h₁ : t/8 ≤ t-L
  · by_cases h₂ : t/8 ≤ 2*L-t
    · exact ⟨false, by simpa [gridFactor, L] using h₁,
        by simpa [gridFactor, L] using h₂⟩
    · have heq : bandIndex (3/2) t = j := by
        apply bandIndex_eq _ _ _ (by norm_num) ht
        · rw [← hL]; linarith
        · rw [← hL]; linarith [hb.2.2]
      refine ⟨true, ?_, ?_⟩ <;> simp only [gridFactor, ↓reduceIte, bandLower, heq, ← hL]
      · linarith
      · linarith [hb.2.2]
  · have hp : (2:ℝ)^(j-1) = L/2 := by
      rw [zpow_sub₀ (by norm_num : (2:ℝ) ≠ 0), zpow_one, hL]
    have heq : bandIndex (3/2) t = j-1 := by
      apply bandIndex_eq _ _ _ (by norm_num) ht
      · rw [hp]; linarith [hb.2.1]
      · rw [hp]; linarith
    refine ⟨true, ?_, ?_⟩ <;> simp only [gridFactor, ↓reduceIte, bandLower, heq, hp]
    · linarith [hb.2.1]
    · linarith
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.FiniteProductLaw
variable {I A : Type*} [Fintype I] [Fintype A] [DecidableEq I]
noncomputable def mass (p : I → A → ℝ) (x : I → A) : ℝ := ∏ i, p i (x i)
lemma nonneg
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A] [DecidableEq I]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a) (x : I → A) :
    0 ≤ mass p x := Finset.prod_nonneg (fun i _ => hp i (x i))
lemma total (p : I → A → ℝ) (hp : ∀ i, (∑ a, p i a) = 1) :
    (∑ x, mass p x) = 1 := by
  classical
  simp only [mass]
  rw [← Fintype.prod_sum]
  simp only [hp, Finset.prod_const_one]
lemma factor_pos
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A] [DecidableEq I]
    (p : I → A → ℝ) (hp : ∀ i a, 0 ≤ p i a)
    (x : I → A) (hx : 0 < mass p x) (i : I) : 0 < p i (x i) := by
  by_contra h
  have hz : p i (x i) = 0 := le_antisymm (le_of_not_gt h) (hp _ _)
  have hh : mass p x = 0 := Finset.prod_eq_zero (Finset.mem_univ i) hz
  linarith
lemma event (p : I → A → ℝ) (hp : ∀ i, (∑ a, p i a) = 1)
    (j : I) (E : A → Prop) [DecidablePred E] :
    (∑ x, if E (x j) then mass p x else 0) = ∑ a, if E a then p j a else 0 := by
  classical
  let q : I → A → ℝ := fun i a => if i = j then (if E a then p i a else 0) else p i a
  have heq (x : I → A) : (if E (x j) then mass p x else 0) = ∏ i, q i (x i) := by
    by_cases hx : E (x j)
    · simp only [hx, ↓reduceIte, mass]
      apply Finset.prod_congr rfl
      intro i _
      by_cases hij : i = j
      · subst i; simp [q, hx]
      · simp [q, hij]
    · simp only [hx, ↓reduceIte]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [q, hx]
  simp_rw [heq]
  rw [← Fintype.prod_sum]
  calc
    _ = ∑ a, q j a := by
      apply Finset.prod_eq_single j
      · intro i _ hij
        simpa [q, hij] using hp i
      · simp
    _ = _ := by simp [q]
end BoundedTreewidthL1.FiniteProductLaw

namespace BoundedTreewidthL1.LaunchNoise
open Metric Classical

def MetricPaddedSupply {V : Type*} [Fintype V] [DecidableEq V] [MetricSpace V]
    (α π : ℝ) : Prop :=
  ∀ r : ℝ, 0 < r → ∃ μ : (V → V) → ℝ,
    (∀ P, 0 ≤ μ P) ∧ (∑ P, μ P) = 1 ∧
    (∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r) ∧
    ∀ x, π ≤ ∑ P, if (∀ y, dist x y ≤ α*r → P y = P x) then μ P else 0

def GoodBump {V J : Type*} [MetricSpace V]
    (h : V → ℝ) (α η : ℝ) (φ : J → V → ℝ) (x : V) : Prop :=
  ∃ j, α/8 * η * h x ≤ φ j x ∧
    (∀ y, 0 ≤ φ j y) ∧ (∀ y, 4*η*h x < dist x y → φ j y = 0)

def HasOrdinaryBumps {V : Type*} [MetricSpace V]
    (h : V → ℝ) (α π η : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ μ : Fin n → ℝ, ∃ φ : Fin n → Fin m → V → ℝ,
    (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a) = 1 ∧
    (∀ a (U : Fin m → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2) ∧
    ∀ x, 0 < h x → π/2 ≤ ∑ a, if GoodBump h α η (φ a) x then μ a else 0
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.LaunchNoise
open Metric Classical
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

noncomputable def bandSet (h : V → ℝ) : Finset ℤ :=
  Finset.univ.image (fun bx : Bool × V => bandIndex (gridFactor bx.1) (h bx.2))

noncomputable def bandKey (h : V → ℝ) (b : Bool) (x : V) : ↥(bandSet h) :=
  ⟨bandIndex (gridFactor b) (h x), Finset.mem_image.mpr ⟨(b,x), Finset.mem_univ _, rfl⟩⟩

noncomputable def bandScale (b : Bool) (j : ℤ) (η : ℝ) : ℝ :=
  η * (gridFactor b * (2:ℝ)^j) / 2

noncomputable def locationSet (h : V → ℝ) (b : Bool)
    (P : ↥(bandSet h) → V → V) (i : ↥(bandSet h) × V) : Set V :=
  {x | 0 < h x ∧ bandIndex (gridFactor b) (h x) = (i.1 : ℤ) ∧ P i.1 x = i.2}

lemma locationSet_disjoint
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (P : ↥(bandSet h) → V → V) :
    Pairwise (fun i j => Disjoint (locationSet h b P i) (locationSet h b P j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  have heq : i.1 = j.1 := Subtype.ext (hi.2.1.symm.trans hj.2.1)
  have hval : i.2 = j.2 := by rw [← hi.2.2, heq, hj.2.2]
  exact hij (Prod.ext heq hval)

lemma location_self
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (P : ↥(bandSet h) → V → V)
    (x : V) (hx : 0 < h x) :
    x ∈ locationSet h b P (bandKey h b x, P (bandKey h b x) x) := ⟨hx,rfl,rfl⟩

lemma bandScale_pos (b : Bool) (j : ℤ) (η : ℝ) (hη : 0 < η) :
    0 < bandScale b j η := by
  dsimp [bandScale]
  exact div_pos (mul_pos hη (mul_pos (gridFactor_pos b) (zpow_pos (by norm_num) j)))
    (by norm_num)

lemma bandScale_at
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ) (b : Bool) (x : V) (η : ℝ) :
    bandScale b (bandKey h b x) η = η * bandLower (gridFactor b) (h x) / 2 := rfl

lemma bump_noise_bounds (h : V → ℝ) (h0 : ∀ x, 0 ≤ h x)
    (b : Bool) (P : ↥(bandSet h) → V → V) (η : ℝ) (hη : 0 < η)
    (U : ↥(bandSet h) × V → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U) ∧
    ∀ x, 0 ≤ noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U x ∧
      noise (locationSet h b P) (fun i => bandScale b i.1 η / 2) U x ≤ η*h x/2 := by
  have hr (i : ↥(bandSet h) × V) : 0 ≤ bandScale b i.1 η/2 :=
    (div_pos (bandScale_pos b i.1 η hη) (by norm_num)).le
  have hh := disjoint_noise (locationSet h b P) (fun i => bandScale b i.1 η/2) U
    (locationSet_disjoint h b P) hr hU
  refine ⟨hh.1, fun x => ⟨hh.2.1 x, ?_⟩⟩
  by_cases hx : 0 < h x
  · have hh' := hh.2.2.1 _ x (location_self h b P x hx)
    have hB := (band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx).2.1
    rw [bandScale_at] at hh'
    have hmul := mul_le_mul_of_nonneg_left hB hη.le
    nlinarith [h0 x, mul_nonneg hη.le (h0 x)]
  · have hn : ∀ i, x ∉ locationSet h b P i := fun i hi => hx hi.1
    rw [hh.2.2.2 x hn]
    exact div_nonneg (mul_nonneg hη.le (h0 x)) (by norm_num)

lemma location_ball (h : V → ℝ) (hh : LipschitzWith 1 h)
    (b : Bool) (P : ↥(bandSet h) → V → V) (α η : ℝ)
    (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (x : V) (hx : 0 < h x)
    (hmargin : h x/8 ≤ h x - bandLower (gridFactor b) (h x) ∧
      h x/8 ≤ 2*bandLower (gridFactor b) (h x) - h x)
    (hpad : ∀ y, dist x y ≤ α*bandScale b (bandKey h b x) η →
      P (bandKey h b x) y = P (bandKey h b x) x) :
    ball x (α*bandScale b (bandKey h b x) η) ⊆
      locationSet h b P (bandKey h b x, P (bandKey h b x) x) := by
  intro y hy
  have hdist : dist x y < α*bandScale b (bandKey h b x) η := by
    simpa [mem_ball, dist_comm] using hy
  have hb := band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx
  have hscale : α*bandScale b (bandKey h b x) η < h x/8 := by
    rw [bandScale_at]
    have h₁ := mul_le_mul_of_nonneg_left hb.2.1 hη.le
    have h₂ := mul_le_mul_of_nonneg_left h₁ hα.le
    have h₃ := mul_le_mul_of_nonneg_right hα8 (mul_nonneg hη.le hx.le)
    have h₄ := mul_lt_mul_of_pos_right hη4 hx
    nlinarith
  have hL := hh.dist_le_mul x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le] at hL
  have hxy : 0 < h y := by linarith [hL.2]
  refine ⟨hxy, ?_, hpad y hdist.le⟩
  exact band_same (gridFactor b) (h x) (h y) (gridFactor_pos b) hx hxy
    (by linarith [hL.2, hmargin.1]) (by linarith [hL.1, hmargin.2])

lemma good_location (h : V → ℝ) (hh : LipschitzWith 1 h)
    (b : Bool) (P : ↥(bandSet h) → V → V) (α η : ℝ)
    (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (hdiam : ∀ j x y, P j x = P j y → dist x y ≤ bandScale b j η)
    (x : V) (hx : 0 < h x)
    (hmargin : h x/8 ≤ h x - bandLower (gridFactor b) (h x) ∧
      h x/8 ≤ 2*bandLower (gridFactor b) (h x) - h x)
    (hpad : ∀ y, dist x y ≤ α*bandScale b (bandKey h b x) η →
      P (bandKey h b x) y = P (bandKey h b x) x) :
    GoodBump h α η (fun i => bump (locationSet h b P i) (bandScale b i.1 η/2)) x := by
  let j := bandKey h b x
  let i : ↥(bandSet h) × V := (j, P j x)
  have hp := bandScale_pos b j η hη
  have hb := band_bounds (gridFactor b) (h x) (gridFactor_pos b) hx
  have hball := location_ball h hh b P α η hα hα8 hη hη4 x hx hmargin hpad
  have hcap : α*bandScale b j η ≤ bandScale b j η/2 := by nlinarith
  have hbump := bump_padding (locationSet h b P i) (bandScale b j η/2)
    x (α*bandScale b j η) hcap hball
  refine ⟨i, ?_, (fun y => (bump_bounds _ _ (by positivity) y).1), ?_⟩
  · dsimp [i]
    apply le_trans _ hbump
    change α/8*η*h x ≤ α*(η*bandLower (gridFactor b) (h x)/2)
    have hmul := mul_lt_mul_of_pos_left hb.2.2 (mul_pos hα hη)
    nlinarith [mul_pos (mul_pos hα hη) hx]
  · intro y hy
    apply bump_zero _ _ (by positivity)
    intro hmem
    have heq : P j x = P j y := hmem.2.2.symm
    have hd := hdiam j x y heq
    have hs : bandScale b j η ≤ η*h x/2 := by
      change η*bandLower (gridFactor b) (h x)/2 ≤ η*h x/2
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hb.2.1 hη.le) (by norm_num)
    nlinarith [mul_pos hη hx]
end BoundedTreewidthL1.LaunchNoise
namespace BoundedTreewidthL1.LaunchNoise
open Classical Metric
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

lemma ordinary_bumps_reindex
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    {J Ω : Type} [Fintype J] [Fintype Ω]
    (h : V → ℝ) (α π η : ℝ) (μ : Ω → ℝ) (φ : Ω → J → V → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ1 : (∑ a, μ a) = 1)
    (hb : ∀ a (U : J → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2)
    (hg : ∀ x, 0 < h x → π/2 ≤ ∑ a, if GoodBump h α η (φ a) x then μ a else 0) :
    HasOrdinaryBumps h α π η := by
  let e := (Fintype.equivFin J).symm
  let d := (Fintype.equivFin Ω).symm
  refine ⟨Fintype.card Ω, Fintype.card J, μ ∘ d, (fun a j => φ (d a) (e j)),
    (fun a => hμ _), ?_, ?_, ?_⟩
  · simpa using (d.sum_comp μ).trans hμ1
  · intro a U hU
    have hh := hb (d a) (U ∘ e.symm) (fun j => hU _)
    have heq : (fun x => ∑ j, U j * φ (d a) (e j) x) =
        (fun x => ∑ j, (U ∘ e.symm) j * φ (d a) j x) := by
      funext x
      simpa using e.sum_comp (fun j => (U ∘ e.symm) j * φ (d a) j x)
    constructor
    · rw [heq]
      exact hh.1
    · intro x
      rw [show (∑ j, U j * φ (d a) (e j) x) =
        (∑ j, (U ∘ e.symm) j * φ (d a) j x) from congrFun heq x]
      exact hh.2 x
  · intro x hx
    have heq (a : Fin (Fintype.card Ω)) :
        GoodBump h α η (fun j => φ (d a) (e j)) x ↔ GoodBump h α η (φ (d a)) x := by
      constructor
      · rintro ⟨j,hj,hj0,hjS⟩; exact ⟨e j,hj,hj0,hjS⟩
      · rintro ⟨j,hj,hj0,hjS⟩
        refine ⟨e.symm j, ?_, ?_, ?_⟩ <;> simpa using ‹_›
    simp_rw [heq]
    have he := d.sum_comp (fun a => if GoodBump h α η (φ a) x then μ a else 0)
    exact (hg x hx).trans he.ge

noncomputable def locationMass (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (a : Bool × (↥(bandSet h) → V → V)) : ℝ :=
  (1/2) * FiniteProductLaw.mass (p a.1) a.2

lemma locationMass_nonneg
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ) (hp : ∀ b j P, 0 ≤ p b j P) :
    ∀ a, 0 ≤ locationMass h p a := by
  intro a
  exact mul_nonneg (by norm_num) (FiniteProductLaw.nonneg _ (hp a.1) _)

lemma locationMass_total
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (hp : ∀ b j, (∑ P, p b j P) = 1) :
    (∑ a, locationMass h p a) = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [locationMass, ← Finset.mul_sum, FiniteProductLaw.total _ (hp _)]
  norm_num [Fintype.sum_bool]

lemma locationMass_event
    {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]
    (h : V → ℝ)
    (p : Bool → ↥(bandSet h) → (V → V) → ℝ)
    (hp : ∀ b j, (∑ P, p b j P) = 1) (b : Bool) (j : ↥(bandSet h))
    (E : (V → V) → Prop) :
    (∑ a : Bool × (↥(bandSet h) → V → V),
      if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) =
      (1/2) * ∑ P, if E P then p b j P else 0 := by
  classical
  rw [Fintype.sum_prod_type]
  have heq (b' : Bool) :
      (∑ P, if b' = b ∧ E (P j) then locationMass h p (b',P) else 0) =
        if b' = b then (1/2) * ∑ P, if E P then p b j P else 0 else 0 := by
    by_cases he : b' = b
    · subst b'
      simp only [true_and, locationMass, ite_true]
      have he (q : ↥(bandSet h) → V → V) :
          (if E (q j) then (1/2:ℝ) * FiniteProductLaw.mass (p b) q else 0) =
            (1/2) * (if E (q j) then FiniteProductLaw.mass (p b) q else 0) := by
        split_ifs <;> ring
      simp_rw [he]
      rw [← Finset.mul_sum, FiniteProductLaw.event _ (hp b)]
    · simp [he]
  simp_rw [heq]
  simp

/-- Finite ordinary noise from a padded supply, which is available
unconditionally for the weighted graph metrics by `PaddedConstruction`. -/
theorem finite_ordinary_bumps
    (h : V → ℝ) (hh : LipschitzWith 1 h) (h0 : ∀ x, 0 ≤ h x)
    (α π η : ℝ) (hα : 0 < α) (hα8 : α ≤ 1/8) (hη : 0 < η) (hη4 : η < 1/4)
    (hsupply : MetricPaddedSupply (V := V) α π) : HasOrdinaryBumps h α π η := by
  classical
  have hs (b : Bool) (j : ↥(bandSet h)) := hsupply (bandScale b j η) (bandScale_pos b j η hη)
  choose p hp hp1 hdiam hpad using hs
  let φ : (Bool × (↥(bandSet h) → V → V)) → (↥(bandSet h) × V) → V → ℝ :=
    fun a i => bump (locationSet h a.1 a.2 i) (bandScale a.1 i.1 η/2)
  apply ordinary_bumps_reindex h α π η (locationMass h p) φ
    (locationMass_nonneg h p hp) (locationMass_total h p hp1)
  · intro a U hU
    exact bump_noise_bounds h h0 a.1 a.2 η hη U hU
  · intro x hx
    obtain ⟨b,hmargin⟩ := two_grid_margin (h x) hx
    let j := bandKey h b x
    let E : (V → V) → Prop := fun P => ∀ y, dist x y ≤ α*bandScale b j η → P y = P x
    have hsum : (∑ a : Bool × (↥(bandSet h) → V → V),
        if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) =
        (1/2) * ∑ P, if E P then p b j P else 0 := by
      convert locationMass_event h p hp1 b j E using 1
      · apply Finset.sum_congr (by ext; simp)
        intro a _
        split_ifs <;> rfl
      · congr 1
        apply Finset.sum_congr (by ext; simp)
        intro P _
        split_ifs <;> rfl
    have hle : (∑ a : Bool × (↥(bandSet h) → V → V),
        if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0) ≤
        ∑ a, if GoodBump h α η (φ a) x then locationMass h p a else 0 := by
      apply Finset.sum_le_sum
      intro a _
      have hnonneg := locationMass_nonneg h p hp a
      by_cases ha : a.1 = b ∧ E (a.2 j)
      · rw [ite_eq_left ha]
        by_cases hpos : 0 < locationMass h p a
        · have hprod : 0 < FiniteProductLaw.mass (p a.1) a.2 := by
            dsimp [locationMass] at hpos
            linarith
          have hgood : GoodBump h α η (φ a) x := by
            have hda : ∀ j x y, a.2 j x = a.2 j y → dist x y ≤ bandScale a.1 j η := by
              intro j x y hxy
              exact hdiam a.1 j (a.2 j)
                (FiniteProductLaw.factor_pos _ (hp a.1) _ hprod j) x y hxy
            apply good_location h hh a.1 a.2 α η hα hα8 hη hη4 hda x hx
            · simpa [ha.1] using hmargin
            · simpa [ha.1, j, E] using ha.2
          rw [ite_eq_left hgood]
        · have hz : locationMass h p a = 0 := le_antisymm (le_of_not_gt hpos) hnonneg
          simp [hz]
      · rw [ite_eq_right ha]
        split_ifs <;> positivity
    have hle2 : (1/2) * (∑ P, if E P then p b j P else 0) ≤
        ∑ a, if GoodBump h α η (φ a) x then locationMass h p a else 0 := by
      calc
        _ = ∑ a : Bool × (↥(bandSet h) → V → V),
          if a.1 = b ∧ E (a.2 j) then locationMass h p a else 0 := hsum.symm
        _ ≤ _ := hle
    have hpπ := hpad b j x
    change π ≤ ∑ P, if E P then p b j P else 0 at hpπ
    have hh' := mul_le_mul_of_nonneg_left hpπ (by norm_num : (0:ℝ) ≤ 1/2)
    exact (by linarith : π/2 ≤ (1/2)*∑ P, if E P then p b j P else 0).trans hle2
end BoundedTreewidthL1.LaunchNoise

/-! The actual finite product probability space for the ordinary launch noise.
No random coefficient distribution or independence is supplied as an assumption.
-/
namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
attribute [local instance] Classical.propDecidable
open scoped unitInterval ENNReal
noncomputable def locationLaw {n : ℕ} (μ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ a, ENNReal.ofReal (μ a) • Measure.dirac a
abbrev CoeffCube (m : ℕ) := Fin m → I
abbrev NoiseSpace (n m : ℕ) := I × (Fin n × CoeffCube m)
noncomputable def noiseLaw {n : ℕ} (m : ℕ) (μ : Fin n → ℝ) : Measure (NoiseSpace n m) :=
  (volume : Measure I).prod ((locationLaw μ).prod volume)
def noiseXi {n m : ℕ} (ω : NoiseSpace n m) : ℝ := 1 + (ω.1 : ℝ)
noncomputable def noiseV {V : Type*} {n m : ℕ} (φ : Fin n → Fin m → V → ℝ)
    (ω : NoiseSpace n m) (x : V) : ℝ := ∑ j, (ω.2.2 j : ℝ) * φ ω.2.1 j x
noncomputable def noiseG {V : Type*} {n m : ℕ} (h : V → ℝ)
    (φ : Fin n → Fin m → V → ℝ) (ω : NoiseSpace n m) (x : V) : ℝ :=
  noiseXi ω * h x + noiseV φ ω x

lemma locationLaw_apply {n : ℕ} (μ : Fin n → ℝ) (S : Set (Fin n)) :
    locationLaw μ S = ∑ a, if a ∈ S then ENNReal.ofReal (μ a) else 0 := by
  classical
  simp [locationLaw, Set.indicator, apply_ite]

lemma locationLaw_probability {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) : IsProbabilityMeasure (locationLaw μ) := by
  constructor
  rw [locationLaw_apply]
  simp only [Set.mem_univ, ↓reduceIte]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a), hμ₁, ENNReal.ofReal_one]

lemma noiseLaw_probability {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) : IsProbabilityMeasure (noiseLaw m μ) := by
  let := locationLaw_probability μ hμ hμ₁
  unfold noiseLaw
  infer_instance

lemma noise_locationLaw {n m : ℕ} (μ : Fin n → ℝ) :
    Measure.map (fun ω : NoiseSpace n m => ω.2.1) (noiseLaw m μ) = locationLaw μ := by
  unfold noiseLaw
  change Measure.map (Prod.fst ∘ Prod.snd) _ = _
  rw [← Measure.map_map measurable_fst measurable_snd, Measure.map_snd_prod]
  simp only [measure_univ, one_smul, Measure.map_fst_prod]

lemma noise_goodProbability {n m : ℕ} (μ : Fin n → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (E : Fin n → Prop) :
    noiseLaw m μ {ω | E ω.2.1} = ENNReal.ofReal (∑ a, if E a then μ a else 0) := by
  classical
  have hm : MeasurableSet {a : Fin n | E a} := MeasurableSet.of_discrete
  change noiseLaw m μ ((Prod.fst ∘ Prod.snd) ⁻¹' {a : Fin n | E a}) = _
  rw [← Measure.map_apply (measurable_fst.comp measurable_snd) hm]
  change (Measure.map (fun ω : NoiseSpace n m => ω.2.1) (noiseLaw m μ)) {a | E a} = _
  rw [noise_locationLaw, locationLaw_apply]
  rw [ENNReal.ofReal_sum_of_nonneg (fun a _ => by split_ifs <;> simp [hμ])]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

lemma noiseXi_measurable {n m : ℕ} : Measurable (noiseXi (n := n) (m := m)) := by
  unfold noiseXi
  fun_prop

lemma noiseV_measurable {V : Type*} {n m : ℕ} (φ : Fin n → Fin m → V → ℝ) :
    Measurable (noiseV φ) := by
  apply Measurable.of_eval
  intro x
  unfold noiseV
  apply Finset.measurable_sum
  intro j _
  have hu : Measurable (fun ω : NoiseSpace n m => (ω.2.2 j : ℝ)) := by fun_prop
  have ha : Measurable (fun ω : NoiseSpace n m => φ ω.2.1 j x) :=
    (show Measurable (fun a : Fin n => φ a j x) from Measurable.of_discrete).comp
      (measurable_fst.comp measurable_snd)
  exact hu.mul ha

lemma noiseG_measurable {V : Type*} {n m : ℕ} (h : V → ℝ)
    (φ : Fin n → Fin m → V → ℝ) : Measurable (noiseG h φ) := by
  apply Measurable.of_eval
  intro x
  exact (noiseXi_measurable.mul_const (h x)).add ((measurable_pi_apply x).comp (noiseV_measurable φ))

lemma noiseXi_uniform {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    MeasurePreserving (fun ω : NoiseSpace n m => noiseXi ω - 1)
      (noiseLaw m μ) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  let := locationLaw_probability μ hμ hμ₁
  simpa [noiseLaw, noiseXi, Function.comp_def, unitInterval] using
    (unitInterval.measurePreserving_coe.comp
      (measurePreserving_fst (μ := (volume : Measure I))
        (ν := (locationLaw μ).prod (volume : Measure (CoeffCube m)))))

lemma noiseXi_indep {V : Type*} {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (φ : Fin n → Fin m → V → ℝ) :
    IndepFun noiseXi (noiseV φ) (noiseLaw m μ) := by
  let := locationLaw_probability μ hμ hμ₁
  exact indepFun_prod (X := fun t : I => 1 + (t : ℝ)) (by fun_prop)
    (Y := fun ac : Fin n × CoeffCube m => fun x => ∑ j, (ac.2 j : ℝ) * φ ac.1 j x)
    (by
      apply Measurable.of_eval
      intro x
      apply Finset.measurable_sum
      intro j _
      have hu : Measurable (fun ac : Fin n × CoeffCube m => (ac.2 j : ℝ)) := by fun_prop
      have ha : Measurable (fun ac : Fin n × CoeffCube m => φ ac.1 j x) :=
        (show Measurable (fun a : Fin n => φ a j x) from Measurable.of_discrete).comp measurable_fst
      exact hu.mul ha)

lemma cube_uniform {m : ℕ} (j : Fin m) :
    MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1)) :=
  unitInterval.measurePreserving_coe.comp (measurePreserving_eval (fun _ : Fin m => (volume : Measure I)) j)

lemma cube_independent (m : ℕ) :
    iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume :=
  iIndepFun_pi (fun _ => measurable_subtype_coe.aemeasurable)

/-- Fresh independent randomness works with any previously constructed probability space. -/
lemma fresh_noise {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν]
    {V : Type*} {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (h : V → ℝ) (φ : Fin n → Fin m → V → ℝ) :
    IndepFun (fun ω : Ω × NoiseSpace n m => ω.1)
      (fun ω => noiseG h φ ω.2) (ν.prod (noiseLaw m μ)) := by
  let := noiseLaw_probability (m := m) μ hμ hμ₁
  exact indepFun_prod measurable_id (noiseG_measurable h φ)

lemma noiseXi_uniform_interval {n m : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m μ)
      (volume.restrict (Set.Icc (1:ℝ) 2)) := by
  have he : (fun x : ℝ => 1 + x) ⁻¹' Set.Icc 1 2 = Set.Icc 0 1 := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> rintro ⟨ha,hb⟩ <;> constructor <;> linarith
  have ht := (measurePreserving_add_left (volume : Measure ℝ) 1).restrict_preimage
    (s := Set.Icc 1 2) measurableSet_Icc
  rw [he] at ht
  simpa [Function.comp_def] using ht.comp (noiseXi_uniform (m := m) μ hμ hμ₁)

lemma noise_deterministic {V : Type*} [MetricSpace V] {n m : ℕ}
    (h : V → ℝ) (hh : LipschitzWith 1 h) (hhn : ∀ x, 0 ≤ h x)
    (η : ℝ) (hη : η < 1/4) (φ : Fin n → Fin m → V → ℝ)
    (hv : ∀ a (U : Fin m → ℝ), (∀ j, 0 ≤ U j ∧ U j ≤ 1) →
      LipschitzWith 1 (fun x => ∑ j, U j * φ a j x) ∧
      ∀ x, 0 ≤ (∑ j, U j * φ a j x) ∧ (∑ j, U j * φ a j x) ≤ η*h x/2)
    (ω : NoiseSpace n m) :
    LipschitzWith 1 (noiseV φ ω) ∧
      (∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h φ ω) ∧
      ∀ x, h x ≤ noiseG h φ ω x ∧ noiseG h φ ω x ≤ (5/2) * h x := by
  obtain ⟨hlip, hbound⟩ := hv ω.2.1 (fun j => (ω.2.2 j : ℝ)) (fun j => (ω.2.2 j).property)
  change LipschitzWith 1 (noiseV φ ω) at hlip
  change ∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2 at hbound
  have hξ : 1 ≤ noiseXi ω ∧ noiseXi ω ≤ 2 := by
    have hp := ω.1.property
    dsimp [noiseXi]
    constructor <;> linarith [hp.1, hp.2]
  refine ⟨hlip, hbound, ?_, ?_⟩
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    have hhl : |h x - h y| ≤ dist x y := by simpa [Real.dist_eq] using hh.dist_le_mul x y
    have hvl : |noiseV φ ω x - noiseV φ ω y| ≤ dist x y := by
      simpa [Real.dist_eq] using hlip.dist_le_mul x y
    rw [Real.dist_eq]
    calc
      |noiseG h φ ω x - noiseG h φ ω y| =
          |noiseXi ω * (h x - h y) + (noiseV φ ω x - noiseV φ ω y)| := by
            congr 1
            dsimp [noiseG]
            ring
      _ ≤ |noiseXi ω * (h x - h y)| + |noiseV φ ω x - noiseV φ ω y| := abs_add_le _ _
      _ = noiseXi ω * |h x - h y| + |noiseV φ ω x - noiseV φ ω y| := by
        rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ noiseXi ω)]
      _ ≤ 2 * dist x y + dist x y := add_le_add
        ((mul_le_mul_of_nonneg_left hhl (by linarith)).trans
          (mul_le_mul_of_nonneg_right hξ.2 dist_nonneg)) hvl
      _ = (3 : NNReal) * dist x y := by norm_num; ring
  · intro x
    have hz := hhn x
    have hb := hbound x
    dsimp [noiseG]
    constructor
    · nlinarith [mul_le_mul_of_nonneg_right hξ.1 hz]
    · nlinarith [mul_le_mul_of_nonneg_right hξ.2 hz, mul_nonneg (le_of_lt (sub_pos.mpr hη)) hz]
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
/-- Complete finite ordinary-noise sampler; its law is the displayed product
of a fresh uniform xi, a finite location law, and independent uniform amplitudes. -/
def HasOrdinaryNoise {V : Type*} [MetricSpace V]
    (h : V → ℝ) (α π η : ℝ) : Prop :=
  ∃ n m : ℕ, ∃ μ : Fin n → ℝ, ∃ φ : Fin n → Fin m → V → ℝ,
    (∀ a, 0 ≤ μ a) ∧ (∑ a, μ a) = 1 ∧
    IsProbabilityMeasure (noiseLaw m μ) ∧
    Measurable (noiseG h φ) ∧
    MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m μ)
      (volume.restrict (Set.Icc (1:ℝ) 2)) ∧
    IndepFun noiseXi (noiseV φ) (noiseLaw m μ) ∧
    (∀ ω : NoiseSpace n m,
      LipschitzWith 1 (noiseV φ ω) ∧
      (∀ x, 0 ≤ noiseV φ ω x ∧ noiseV φ ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h φ ω) ∧
      ∀ x, h x ≤ noiseG h φ ω x ∧ noiseG h φ ω x ≤ (5/2) * h x) ∧
    (∀ x, 0 < h x → ENNReal.ofReal (π/2) ≤
      noiseLaw m μ {ω | GoodBump h α η (φ ω.2.1) x}) ∧
    (∀ j : Fin m, MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1))) ∧
    iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
variable {V : Type} [Fintype V] [DecidableEq V] [MetricSpace V]

theorem metric_ordinary_noise
    (h : V → ℝ) (hh : LipschitzWith 1 h) (h0 : ∀ x, 0 ≤ h x)
    (α π η : ℝ) (hα : 0 < α) (hα8 : α ≤ 1/8) (_ : 0 < π)
    (hη : 0 < η) (hη4 : η < 1/4)
    (hsupply : MetricPaddedSupply (V := V) α π) : HasOrdinaryNoise h α π η := by
  classical
  obtain ⟨n,m,μ,φ,hμ,hμ₁,hv,hgood⟩ :=
    finite_ordinary_bumps h hh h0 α π η hα hα8 hη hη4 hsupply
  refine ⟨n,m,μ,φ,hμ,hμ₁,noiseLaw_probability μ hμ hμ₁,
    noiseG_measurable h φ,noiseXi_uniform_interval μ hμ hμ₁,
    noiseXi_indep μ hμ hμ₁ φ,?_,?_,cube_uniform,cube_independent m⟩
  · exact noise_deterministic h hh h0 η hη4 φ hv
  · intro x hx
    rw [noise_goodProbability (m := m) μ hμ (fun a => GoodBump h α η (φ a) x)]
    exact ENNReal.ofReal_le_ofReal (hgood x hx)
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
/-- Uniform graph-metric input; the distance is definitionally the original
positive-weight shortest-path distance, with no edge-ratio restriction. -/
theorem graph_ordinary_noise (k : ℕ) (hk : 2 ≤ k) :
    ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
      ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
        (G : SimpleGraph V) (hG : G.Connected) (_ : HasTreeDecomposition G k)
        (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e),
        let := weightedMetricSpace G ℓ hG hℓ
        ∀ (A : Set V), A.Nonempty → ∀ η : ℝ, 0 < η → η < 1/4 →
          HasOrdinaryNoise (fun x => Metric.infDist x A) α π η := by
  classical
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hpad⟩ := PaddedPartitions.uniform_padded_partitions k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG hT ℓ hℓ metric
  let _ : MetricSpace V := metric
  intro A hA η hη hη4
  have hsupply : MetricPaddedSupply (V := V) α π := by
    intro r hr
    obtain ⟨μ,hμ,hμ1,hdiam,hprob⟩ := hpad V G hG hT ℓ hℓ r hr
    refine ⟨μ,hμ,hμ1,hdiam,?_⟩
    intro x
    apply le_trans (hprob x)
    apply le_of_eq
    unfold PaddedPartitions.paddingProbability
    apply Finset.sum_congr (by ext; simp)
    intro P _
    have hd (u v : V) : dist u v = shortestPathDistance G ℓ u v := rfl
    simp only [PaddedPartitions.PaddedAt, hd]
    exact congrArg (fun d : Decidable
      (∀ y : V, shortestPathDistance G ℓ x y ≤ α * r → P y = P x) =>
        @ite ℝ _ d (μ P) 0) (Subsingleton.elim _ _)
  exact metric_ordinary_noise (fun x => Metric.infDist x A)
    (Metric.lipschitz_infDist_pt A) (fun x => Metric.infDist_nonneg) α π η hα hα8 hπ hη hη4 hsupply
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.TreeCache
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*}

lemma fresh_eq_singleton (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (i : I) :
    AnchorTreeParticles.fresh (RootedTree.forest T hT root)
      (active T hT root B D k d J) i = {i} := by
  classical
  unfold AnchorTreeParticles.fresh AnchorTreeParticles.retained
  cases hp : (RootedTree.forest T hT root).parent i with
  | none =>
    have hi : i = root := by
      by_contra hi
      simp [RootedTree.forest,hi] at hp
    subst i
    simp only [Option.elim_none,Finset.sdiff_empty]
    exact active_root T hT root B D k d J
  | some p =>
    simp only [Option.elim_some]
    convert active_sdiff_parent T hT root B D k d J hp using 1
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_inter]
    tauto

lemma origin_self (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
    (i a : I) (ha : a ∈ active T hT root B D k d J i) :
    AnchorTreeParticles.origin (RootedTree.forest T hT root)
      (active T hT root B D k d J) root i a = a := by
  have hf := AnchorTreeParticles.origin_fresh (RootedTree.forest T hT root)
    (active T hT root B D k d J) root i a ha
  rw [fresh_eq_singleton,Finset.mem_singleton] at hf
  exact hf.symm
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1
open MeasureTheory
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V : Type*} [Fintype V]

lemma bagDistance_eq_infDist [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (A : Finset V) (hA : A.Nonempty) (x : V) :
    let := weightedMetricSpace G ℓ hG hℓ
    bagDistance G ℓ A hA x = Metric.infDist x (A : Set V) := by
  let := weightedMetricSpace G ℓ hG hℓ
  apply le_antisymm
  · apply (Metric.le_infDist (show (A : Set V).Nonempty from hA)).mpr
    intro a ha
    exact bagDistance_le G ℓ A hA x ha
  · obtain ⟨a,ha,heq⟩ := bagDistance_attained G ℓ A hA x
    rw [heq]
    exact Metric.infDist_le_dist_of_mem ha
end BoundedTreewidthL1

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory ProbabilityTheory
open scoped unitInterval ENNReal
/-- The complete finite launch data, retaining both independent uniform variables
and the random good-bump event required in the non-collapse argument. -/
structure OrdinarySeed {V : Type*} [MetricSpace V] (h : V → ℝ) (α π η : ℝ) where
  n : ℕ
  m : ℕ
  mass : Fin n → ℝ
  bump : Fin n → Fin m → V → ℝ
  mass_nonneg : ∀ a, 0 ≤ mass a
  mass_total : (∑ a, mass a) = 1
  probability : IsProbabilityMeasure (noiseLaw m mass)
  measurable : Measurable (noiseG h bump)
  xi_uniform : MeasurePreserving (noiseXi (n := n) (m := m)) (noiseLaw m mass)
    (volume.restrict (Set.Icc (1:ℝ) 2))
  xi_independent : IndepFun noiseXi (noiseV bump) (noiseLaw m mass)
  bounds : ∀ ω : NoiseSpace n m,
      LipschitzWith 1 (noiseV bump ω) ∧
      (∀ x, 0 ≤ noiseV bump ω x ∧ noiseV bump ω x ≤ η * h x / 2) ∧
      LipschitzWith 3 (noiseG h bump ω) ∧
      ∀ x, h x ≤ noiseG h bump ω x ∧ noiseG h bump ω x ≤ (5/2) * h x
  good : ∀ x, 0 < h x → ENNReal.ofReal (π/2) ≤
    noiseLaw m mass {ω | GoodBump h α η (bump ω.2.1) x}
  coefficients_uniform : ∀ j : Fin m,
    MeasurePreserving (fun U : CoeffCube m => (U j : ℝ)) volume
      (volume.restrict (Set.Icc (0:ℝ) 1))
  coefficients_independent : iIndepFun (fun j (U : CoeffCube m) => (U j : ℝ)) volume

lemma OrdinarySeed.exists_of_has {V : Type*} [MetricSpace V] {h : V → ℝ} {α π η : ℝ}
    (hN : HasOrdinaryNoise h α π η) : Nonempty (OrdinarySeed h α π η) := by
  obtain ⟨n,m,μ,φ,hμ,hμ₁,hprob,hmeas,hxi,hind,hbound,hgood,huni,hindep⟩ := hN
  exact ⟨⟨n,m,μ,φ,hμ,hμ₁,hprob,hmeas,hxi,hind,hbound,hgood,huni,hindep⟩⟩
end BoundedTreewidthL1.LaunchNoise

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1
open MeasureTheory LaunchNoise AnchorTreeParticles
attribute [local instance] Classical.decEq Classical.propDecidable

theorem anchor_embedding_preparation (k : ℕ) (hk : 2 ≤ k) :
    ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
      (m : ℕ) (T : SimpleGraph (Fin m)) (hT : T.IsTree) (root : Fin m)
      (B : Fin m → Finset V) (hne : ∀ i, (B i).Nonempty)
      (_ : ∀ v, ∃ i, v ∈ B i)
      (_ : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
      (_ : ∀ v, (T.induce {i | v ∈ B i}).Connected)
      (_ : ∀ i, (B i).card ≤ k) (J η : ℝ), 0 < η → η < 1/4 →
    let := weightedMetricSpace G ℓ hG hℓ
    let D := fun i => bagDistance G ℓ (B i) (hne i)
    ∃ seed : (i : Fin m) → OrdinarySeed (D i) α π η,
    let Ω := (i : Fin m) → NoiseSpace (seed i).n (seed i).m
    let law : Measure Ω := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
    let A := TreeCache.active T hT root B D k (shortestPathDistance G ℓ) J
    let N := 2*(AnchorCache.cacheBound k+1) + k.factorial + 2
    let g : Ω → Fin m → Fin m → V → ℝ :=
      fun ω i _ => noiseG (D i) (seed i).bump (ω i)
    let S := fun ω => state (ι := Fin N) (RootedTree.forest T hT root) B A (g ω)
    ∃ H : ℝ, 0 < H ∧ IsProbabilityMeasure law ∧
      (∀ i a v, Measurable (fun ω => g ω i a v)) ∧
      (∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) 3 H (S ω i).1) ∧
      (∀ ω i p, (RootedTree.forest T hT root).parent i = some p →
        particleTrace (H*((N:ℝ)-1)+2) (S ω i).1 (B i) =
          particleTrace (H*((N:ℝ)-1)+2) (S ω p).1 (B i)) ∧
      (∀ ω i p, (RootedTree.forest T hT root).parent i = some p → ∀ a ∈ A i ∩ A p,
        (S ω i).2 a = (S ω p).2 a ∧
        (S ω i).1 ((S ω i).2 a).1 = (S ω p).1 ((S ω p).2 a).1 ∧
        (S ω i).1 ((S ω i).2 a).2 = (S ω p).1 ((S ω p).2 a).2) ∧
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ ≤ 3*(N:ℝ)*((N:ℝ)-1)*shortestPathDistance G ℓ u v) ∧
        ∀ i a, a ∈ A i → ∀ (u v : B i),
          2*(∫ ω, |g ω a a u - g ω a a v| ∂law) ≤ ‖Φ u.val - Φ v.val‖ := by
  classical
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_ordinary_noise k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG ℓ hℓ m T hT root B hne hcover hedge hrun hbag J η hη hη4
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  have hdec : HasTreeDecomposition G k := ⟨m,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hnoise (i : Fin m) : HasOrdinaryNoise (D i) α π η := by
    have hn := hsampler V G hG hdec ℓ hℓ (B i : Set V) (hne i) η hη hη4
    have heq : D i = fun x => Metric.infDist x (B i : Set V) := by
      funext x
      exact bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) x
    rw [heq]
    exact hn
  let seed : (i : Fin m) → OrdinarySeed (D i) α π η :=
    fun i => Classical.choice (OrdinarySeed.exists_of_has (hnoise i))
  refine ⟨seed,?_⟩
  let Ω := (i : Fin m) → NoiseSpace (seed i).n (seed i).m
  let (i : Fin m) : IsProbabilityMeasure (noiseLaw (seed i).m (seed i).mass) := (seed i).probability
  let law : Measure Ω := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
  let A := TreeCache.active T hT root B D k (shortestPathDistance G ℓ) J
  let q := AnchorCache.cacheBound k+1
  let N := 2*q+k.factorial+2
  have hN : 2 ≤ N := by dsimp [N]; omega
  let g : Ω → Fin m → Fin m → V → ℝ := fun ω i _ => noiseG (D i) (seed i).bump (ω i)
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := Fin N) R B A (g ω)
  let H : ℝ := 1+3*∑ i, ∑ v, D i v
  have hD : ∀ i v, 0 ≤ D i v := fun i v =>
    bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  have hsum : 0 ≤ ∑ i, ∑ v, D i v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => hD i v))
  have hH : 0 < H := by dsimp [H]; positivity
  have hdH (i : Fin m) (v : V) : (5/2)*D i v ≤ H := by
    have hv := Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hD i x)
      (Finset.mem_univ v)
    have hi : (∑ x, D i x) ≤ ∑ j, ∑ x, D j x :=
      Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin m))) =>
        Finset.sum_nonneg (fun x _ => hD j x)) (Finset.mem_univ i)
    dsimp [H]
    linarith [hD i v]
  have hg : ∀ i a v, Measurable (fun ω : Ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hLip : ∀ ω i a, ∀ u v, |g ω i a u-g ω i a v| ≤ 3*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    exact ((seed i).bounds (ω i)).2.2.1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    rw [abs_of_nonneg ((hD i v).trans hb.1)]
    exact hb.2.trans (hdH i v)
  have hz : ∀ ω i a, ∀ v ∈ B i, g ω i a v = 0 := by
    intro ω i a v hv
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    have he : D i v = 0 := by
      rw [show D i v = Metric.infDist v (B i : Set V) from
        bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) v]
      exact Metric.infDist_zero_of_mem hv
    rw [he] at hb
    dsimp only [g]
    linarith
  have hA : ∀ i, (A i).card ≤ q :=
    TreeCache.graph_active_bound G ℓ hG hℓ T B hne hT root hedge hrun k hbag J
  have hf (ω : Ω) := forest_particle_realization (ι := Fin N) R B A k q hbag hA
    (by simp [N]) (shortestPathDistance G ℓ) 3 H 1 hH (by norm_num)
    (g ω) (hLip ω) (hHeight ω) (hz ω)
  refine ⟨H,hH,inferInstance,hg,?_,?_,?_,?_⟩
  · intro ω i
    exact (hf ω).1 i
  · intro ω i p hp
    simpa only [Fintype.card_fin,mul_one] using (hf ω).2.1 i p hp
  · intro ω i p hp a ha
    exact (hf ω).2.2.1 i p hp a ha
  · obtain ⟨n,Φ,hup,hlo⟩ := averaged_origin_realization (ι := Fin N) G hG ℓ hℓ T hT root B
      hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA (by simp [N])
      law 3 H 1 (by norm_num) hH (by norm_num) g hg hLip hHeight hz
    refine ⟨n,Φ,?_,?_⟩
    · intro u v
      simpa only [Fintype.card_fin,mul_comm (N:ℝ) 3] using hup u v
    · intro i a ha u v
      have hh := hlo i a ha u v
      have ho : origin R A root i a = a := by
        have hh := TreeCache.origin_self T hT root B D k (shortestPathDistance G ℓ) J i a ha
        have hd : (Classical.decEq (Fin m)) = (instDecidableEqFin m) := Subsingleton.elim _ _
        rw [hd] at hh
        exact hh
      rwa [ho] at hh
end BoundedTreewidthL1

namespace BoundedTreewidthL1

lemma marginal_mono {A C : Type*} [Fintype A]
    (f : A → C) {μ ν : A → ℝ} (h : ∀ a, μ a ≤ ν a) (c : C) :
    marginal f μ c ≤ marginal f ν c := by
  classical
  apply Finset.sum_le_sum
  intro a _
  split_ifs <;> simp_all

lemma marginal_add {A C : Type*} [Fintype A]
    (f : A → C) (μ ν : A → ℝ) (c : C) :
    marginal f (μ + ν) c = marginal f μ c + marginal f ν c := by
  classical
  unfold marginal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma marginal_smul {A C : Type*} [Fintype A]
    (f : A → C) (μ : A → ℝ) (r : ℝ) (c : C) :
    marginal f (r • μ) c = r * marginal f μ c := by
  classical
  unfold marginal
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp

lemma marginal_comp {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → B) (g : B → C) (μ : A → ℝ) (c : C) :
    marginal g (marginal f μ) c = marginal (g ∘ f) μ c := by
  classical
  unfold marginal
  have hexpand : (∑ b : B, if g b = c then ∑ a : A, if f a = b then μ a else 0 else 0) =
      ∑ b : B, ∑ a : A, if g b = c then (if f a = b then μ a else 0) else 0 := by
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> simp
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  trans ∑ b : B, if f a = b then (if g b = c then μ a else 0) else 0
  · apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  · simp

lemma marginal_total {A C : Type*} [Fintype A] [Fintype C]
    (f : A → C) (μ : A → ℝ) : (∑ c, marginal f μ c) = ∑ a, μ a := by
  classical
  simp only [marginal]
  rw [Finset.sum_comm]
  simp

lemma glueWeights_row_formula {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (a : A) :
    (∑ b, glueWeights f g μ ν a b) =
      μ a * marginal g ν (f a) / marginal f μ (f a) := by
  classical
  simp only [marginal, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  unfold glueWeights marginal
  by_cases h : f a = g b
  · simp only [h, ↓reduceIte]
  · simp [h, Ne.symm h]

lemma glueWeights_col_formula {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ) (b : B) :
    (∑ a, glueWeights f g μ ν a b) =
      marginal f μ (g b) * ν b / marginal f μ (g b) := by
  classical
  rw [marginal, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  unfold glueWeights
  by_cases h : f a = g b
  · simp [h, marginal]
  · simp [h]

theorem glueWeights_of_submarginal {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : A → ℝ) (ν : B → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hdom : ∀ c, marginal g ν c ≤ marginal f μ c) :
    (∀ a b, 0 ≤ glueWeights f g μ ν a b) ∧
    (∀ a, (∑ b, glueWeights f g μ ν a b) ≤ μ a) ∧
    (∀ b, (∑ a, glueWeights f g μ ν a b) = ν b) := by
  refine ⟨glueWeights_nonneg f g μ ν hμ hν, ?_, ?_⟩
  · intro a
    rw [glueWeights_row_formula]
    by_cases hm : marginal f μ (f a) = 0
    · simp [hm, hμ a]
    · apply (div_le_iff₀ (lt_of_le_of_ne (marginal_nonneg f μ hμ _) (Ne.symm hm))).mpr
      exact mul_le_mul_of_nonneg_left (hdom _) (hμ a)
  · intro b
    rw [glueWeights_col_formula]
    by_cases hm : marginal f μ (g b) = 0
    · have hn : ν b = 0 := by
        have h1 := le_marginal g ν hν b
        have h2 := hdom (g b)
        rw [hm] at h2
        exact le_antisymm (h1.trans h2) (hν b)
      simp [hm, hn]
    · exact mul_div_cancel_left₀ (ν b) hm

end BoundedTreewidthL1

namespace BoundedTreewidthL1.ExpandedParticleKernel
open scoped BigOperators

/-- A finite transition coupling. We compose couplings, not stochastic kernels,
so zero-mass states require no arbitrary probability distribution. -/
noncomputable def compose {A B C : Type*} [Fintype B]
    (μ : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ) (a : A) (c : C) : ℝ :=
  ∑ b, J a b * K b c / μ b

 theorem retained_or_free_marginal {A B C : Type*} [Fintype A]
    (key : A → Option B) (trace : A → C) (μ ν : A → ℝ)
    (hret : ∀ a, key a ≠ none → μ a = ν a)
    (ht : ∀ c, marginal trace μ c = marginal trace ν c) :
    ∀ z, marginal (fun a => (key a, trace a)) μ z =
      marginal (fun a => (key a, trace a)) ν z := by
  classical
  rintro ⟨k, c⟩
  cases k with
  | some b =>
    unfold marginal
    apply Finset.sum_congr rfl
    intro a _
    by_cases h : (key a, trace a) = (some b, c)
    · have hk : key a = some b := congrArg Prod.fst h
      have he := hret a (by simp [hk])
      simp only [h, ↓reduceIte, he]
    · simp only [h, ↓reduceIte]
  | none =>
    have he : (∑ a, if key a ≠ none ∧ trace a = c then μ a else 0) =
        ∑ a, if key a ≠ none ∧ trace a = c then ν a else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      split_ifs with h
      · exact hret a h.1
      · rfl
    have hs (ρ : A → ℝ) : marginal trace ρ c =
        marginal (fun a => (key a, trace a)) ρ (none, c) +
        ∑ a, if key a ≠ none ∧ trace a = c then ρ a else 0 := by
      unfold marginal
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      by_cases hk : key a = none <;> by_cases ht : trace a = c <;> simp [hk, ht]
    have ha := ht c
    rw [hs μ, hs ν, he] at ha
    exact add_right_cancel ha

 theorem compose_coupling {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : A → ℝ) (ν : B → ℝ) (ξ : C → ℝ)
    (J : A → B → ℝ) (K : B → C → ℝ)
    (_ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b) (_ : ∀ c, 0 ≤ ξ c)
    (hJ : ∀ a b, 0 ≤ J a b) (hK : ∀ b c, 0 ≤ K b c)
    (hrJ : ∀ a, ∑ b, J a b = μ a) (hcJ : ∀ b, ∑ a, J a b = ν b)
    (hrK : ∀ b, ∑ c, K b c = ν b) (hcK : ∀ c, ∑ b, K b c = ξ c) :
    (∀ a c, 0 ≤ compose ν J K a c) ∧
    (∀ a, ∑ c, compose ν J K a c = μ a) ∧
    (∀ c, ∑ a, compose ν J K a c = ξ c) := by
  classical
  have hJ0 (b : B) (hb : ν b = 0) : ∀ a, J a b = 0 := by
    intro a
    have h := Finset.single_le_sum (s := Finset.univ) (fun a _ => hJ a b)
      (Finset.mem_univ a)
    rw [hcJ, hb] at h
    exact le_antisymm h (hJ a b)
  have hK0 (b : B) (hb : ν b = 0) : ∀ c, K b c = 0 := by
    intro c
    have h := Finset.single_le_sum (s := Finset.univ) (fun c _ => hK b c)
      (Finset.mem_univ c)
    rw [hrK, hb] at h
    exact le_antisymm h (hK b c)
  refine ⟨fun a c => Finset.sum_nonneg (fun b _ =>
    div_nonneg (mul_nonneg (hJ a b) (hK b c)) (hν b)), ?_, ?_⟩
  · intro a
    unfold compose
    rw [Finset.sum_comm]
    have he (b : B) : (∑ c, J a b * K b c / ν b) = J a b := by
      rw [← Finset.sum_div, ← Finset.mul_sum, hrK]
      by_cases hb : ν b = 0
      · simp [hb, hJ0 b hb a]
      · exact mul_div_cancel_right₀ (J a b) hb
    simp_rw [he]
    exact hrJ a
  · intro c
    unfold compose
    rw [Finset.sum_comm]
    have he (b : B) : (∑ a, J a b * K b c / ν b) = K b c := by
      rw [← Finset.sum_div, ← Finset.sum_mul, hcJ]
      by_cases hb : ν b = 0
      · simp [hb, hK0 b hb c]
      · exact mul_div_cancel_left₀ (K b c) hb
    simp_rw [he]
    exact hcK c

 theorem compose_trace {A B C D : Type*} [Fintype B]
    (ν : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ)
    (f : A → D) (g : B → D) (h : C → D)
    (hJ : ∀ a b, f a ≠ g b → J a b = 0)
    (hK : ∀ b c, g b ≠ h c → K b c = 0)
    (a : A) (c : C) (hne : f a ≠ h c) : compose ν J K a c = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro b _
  by_cases hfg : f a = g b
  · have hgh : g b ≠ h c := fun he => hne (hfg.trans he)
    simp [hK b c hgh]
  · simp [hJ a b hfg]

end BoundedTreewidthL1.ExpandedParticleKernel

namespace BoundedTreewidthL1.ExpandedParticleLaw
open MeasureTheory Set
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

abbrev State (ι V : Type*) := ι × Bool × (V → Bool)

def label (a : State ι V) (v : V) : Bool :=
  if a.2.1 then !(a.2.2 v) else a.2.2 v

noncomputable def weight (M : ℝ) (F : ι → V → ℝ) (a : State ι V) : ℝ :=
  (sweep M (F a.1)).real {a.2.2} / 2

def trace (P : Finset V) (a : State ι V) : P → Bool := fun v => label a v

/-- At incoming updates, the entire state is retained on protected particles.
Every remaining state is pooled in one free class. -/
noncomputable def incomingKey (C : Finset ι) (a : State ι V) : Option (State ι V) :=
  if a.1 ∈ C then some a else none

/-- Departure reheats the fresh pair jointly and every other index separately.
Orientation is retained in either case. -/
noncomputable def departureKey (a b : ι) (x : State ι V) : ι × Bool :=
  (if x.1 = b then a else x.1, x.2.1)

noncomputable def incoming (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι) :=
  glueWeights (fun a => (incomingKey C a, trace P a))
    (fun a => (incomingKey C a, trace P a)) (weight M F) (weight M H)

noncomputable def departure (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (a b : ι) :=
  glueWeights (fun x => (departureKey a b x, trace P x))
    (fun x => (departureKey a b x, trace P x)) (weight M F) (weight M F)

lemma weight_nonneg
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (F : ι → V → ℝ) (a : State ι V) : 0 ≤ weight M F a :=
  div_nonneg measureReal_nonneg (by norm_num)

lemma finite_event {A : Type*} [Fintype A] [MeasurableSpace A]
    [MeasurableSingletonClass A] (μ : Measure A) [IsFiniteMeasure μ] (p : A → Prop) :
    (∑ a, if p a then μ.real {a} else 0) = μ.real {a | p a} := by
  classical
  have h := sum_measureReal_singleton (μ := μ) (Finset.univ.filter p)
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Finset.mem_univ, true_and] using h

lemma oriented_marginal (M : ℝ) (F : V → ℝ) (P : Finset V) (b : P → Bool) :
    (∑ q : Bool, ∑ ω : V → Bool,
      if (fun v : P => if q then !(ω v) else ω v) = b then
        (sweep M F).real {ω}/2 else 0) =
      (symmetrizeCut (sweep M F)).real {ω | (fun v : P => ω v) = b} := by
  classical
  rw [Fintype.sum_bool]
  have ht : (∑ ω : V → Bool,
      if (fun v : P => !(ω v)) = b then (sweep M F).real {ω}/2 else 0) =
      (sweep M F).real {ω | (fun v : P => !(ω v)) = b}/2 := by
    rw [← finite_event, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  have hf : (∑ ω : V → Bool,
      if (fun v : P => ω v) = b then (sweep M F).real {ω}/2 else 0) =
      (sweep M F).real {ω | (fun v : P => ω v) = b}/2 := by
    rw [← finite_event, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> simp
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ht, hf, symmetrizeCut, measureReal_ennreal_smul_apply,
    measureReal_add_apply (by finiteness) (by finiteness),
    map_measureReal_apply measurable_complementCut (Set.toFinite _).measurableSet]
  have he : complementCut ⁻¹' {ω : V → Bool | (fun v : P => ω v) = b} =
      {ω : V → Bool | (fun v : P => !(ω v)) = b} := rfl
  rw [he]
  norm_num
  ring

/-- Exact original symmetric bag trace; no change of the prepared marginal. -/
 theorem trace_marginal (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (b : P → Bool) :
    marginal (trace P) (weight M F) b = (particleTrace M F P).real {b} := by
  classical
  unfold marginal
  simp only [Fintype.sum_prod_type]
  have he (i : ι) : (∑ x : Bool, ∑ ω : V → Bool,
      if trace P (i,x,ω) = b then weight M F (i,x,ω) else 0) =
        (symmetrizeCut (sweep M (F i))).real {ω | (fun v : P => ω v) = b} :=
    oriented_marginal M (F i) P b
  trans ∑ i, (symmetrizeCut (sweep M (F i))).real {ω | (fun v : P => ω v) = b}
  · apply Finset.sum_congr rfl
    intro i _
    convert he i using 1
    apply Finset.sum_congr rfl
    intro q _
    apply Finset.sum_congr rfl
    intro ω _
    split_ifs <;> rfl
  rw [particleTrace, measureReal_def, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => by unfold cutTrace; finiteness)]
  apply Finset.sum_congr rfl
  intro i _
  exact (map_measureReal_apply (measurable_of_finite _) (measurableSet_singleton b)).symm

 theorem incoming_coupling (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι)
    (hret : ∀ i ∈ C, F i = H i) (htrace : particleTrace M F P = particleTrace M H P) :
    (∀ a b, 0 ≤ incoming M F H P C a b) ∧
    (∀ a, ∑ b, incoming M F H P C a b = weight M F a) ∧
    (∀ b, ∑ a, incoming M F H P C a b = weight M H b) ∧
    (∀ a b, trace P a ≠ trace P b → incoming M F H P C a b = 0) ∧
    (∀ a b, a.1 ∈ C → a ≠ b → incoming M F H P C a b = 0) := by
  classical
  have ht (b : P → Bool) : marginal (trace P) (weight M F) b =
      marginal (trace P) (weight M H) b := by rw [trace_marginal, trace_marginal, htrace]
  have hr (a : State ι V) (ha : incomingKey C a ≠ none) : weight M F a = weight M H a := by
    have hc : a.1 ∈ C := by simpa [incomingKey] using ha
    unfold weight
    rw [hret a.1 hc]
  have hcons := ExpandedParticleKernel.retained_or_free_marginal
    (incomingKey C) (trace P) (weight M F) (weight M H) hr ht
  refine ⟨glueWeights_nonneg _ _ _ _ (weight_nonneg M F) (weight_nonneg M H),
    glueWeights_row _ _ _ _ (weight_nonneg M F) hcons,
    (glueWeights_marginals _ _ _ _ (weight_nonneg M F) (weight_nonneg M H) hcons).2.2, ?_, ?_⟩
  · intro a b hab
    unfold incoming glueWeights
    have he : (incomingKey C a, trace P a) ≠ (incomingKey C b, trace P b) :=
      fun h => hab (congrArg Prod.snd h)
    simp [he]
  · intro a b ha hab
    unfold incoming glueWeights
    have he : (incomingKey C a, trace P a) ≠ (incomingKey C b, trace P b) := by
      intro h
      have hk : incomingKey C a = incomingKey C b := congrArg Prod.fst h
      simp only [incomingKey, ha, ↓reduceIte] at hk
      split_ifs at hk with hb
      · exact hab (Option.some.inj hk)
    simp [he]

 theorem departure_coupling (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    (∀ a b, 0 ≤ departure M F P i j a b) ∧
    (∀ a, ∑ b, departure M F P i j a b = weight M F a) ∧
    (∀ b, ∑ a, departure M F P i j a b = weight M F b) ∧
    (∀ a b, trace P a ≠ trace P b → departure M F P i j a b = 0) ∧
    (∀ a b, departureKey i j a ≠ departureKey i j b → departure M F P i j a b = 0) := by
  classical
  have hc : ∀ c, marginal (fun x => (departureKey i j x, trace P x)) (weight M F) c =
      marginal (fun x => (departureKey i j x, trace P x)) (weight M F) c := fun _ => rfl
  refine ⟨glueWeights_nonneg _ _ _ _ (weight_nonneg M F) (weight_nonneg M F),
    glueWeights_row _ _ _ _ (weight_nonneg M F) hc,
    (glueWeights_marginals _ _ _ _ (weight_nonneg M F) (weight_nonneg M F) hc).2.2, ?_, ?_⟩
  · intro a b hab
    unfold departure glueWeights
    have he : (departureKey i j a, trace P a) ≠ (departureKey i j b, trace P b) :=
      fun h => hab (congrArg Prod.snd h)
    simp [he]
  · intro a b hab
    unfold departure glueWeights
    have he : (departureKey i j a, trace P a) ≠ (departureKey i j b, trace P b) :=
      fun h => hab (congrArg Prod.fst h)
    simp [he]

end BoundedTreewidthL1.ExpandedParticleLaw

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.OrderedSweepFlow
open scoped BigOperators

variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def fiber (b : α → β) (x : α) : Finset α := by
  classical
  exact Finset.univ.filter (fun y => b y = b x)

noncomputable def mass (μ : α → ℝ) (b : α → β) (x : α) : ℝ :=
  ∑ y ∈ fiber b x, μ y

noncomputable def bath (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) : ℝ :=
  (∑ y ∈ fiber b x, μ y * f y) / mass μ b x

noncomputable def total (μ f : α → ℝ) : ℝ := ∑ x, μ x * f x

noncomputable def risk (μ f : α → ℝ) (p : α → Bool) : ℝ :=
  ∑ x, μ x * (if p x then 1 - f x else f x)

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma mem_fiber
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (b : α → β) (x y : α) : y ∈ fiber b x ↔ b y = b x := by
  classical
  simp [fiber]

lemma fiber_eq (b : α → β) {x y : α} (h : b x = b y) : fiber b x = fiber b y := by
  classical
  ext z
  simp only [mem_fiber, h]

lemma mass_pos (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β) (x : α) :
    0 < mass μ b x := by
  classical
  exact Finset.sum_pos (fun y _ => hμ y) ⟨x, (mem_fiber b x x).mpr rfl⟩

lemma bath_const_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ) {x y : α}
    (h : b x = b y) : bath μ b f x = bath μ b f y := by
  unfold bath mass
  rw [fiber_eq b h]

lemma bath_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, f y ≤ c) :
    bath μ b f x ≤ c := by
  rw [bath, div_le_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma le_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (x : α) (c : ℝ) (hc : ∀ y ∈ fiber b x, c ≤ f y) :
    c ≤ bath μ b f x := by
  rw [bath, le_div_iff₀ (mass_pos μ hμ b x)]
  unfold mass
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun y hy => by nlinarith [hμ y, hc y hy])

lemma fiber_lt (b : α → β) (hb : Monotone b) {x y s t : α}
    (hxy : b x < b y) (hs : s ∈ fiber b x) (ht : t ∈ fiber b y) : s < t := by
  have hs' := (mem_fiber b x s).mp hs
  have ht' := (mem_fiber b y t).mp ht
  by_contra h
  have := hb (le_of_not_gt h)
  rw [hs', ht'] at this
  exact (not_le_of_gt hxy) this

theorem bath_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h)
  · apply le_bath μ hμ b f y
    intro t ht
    apply bath_le μ hμ b f x
    intro s hs
    exact hf (fiber_lt b hb h hs ht).le

theorem bath_antitone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Antitone f) :
    Antitone (bath μ b f) := by
  intro x y hxy
  rcases (hb hxy).eq_or_lt with h | h
  · exact le_of_eq (bath_const_fiber μ b f h.symm)
  · apply le_bath μ hμ b f x
    intro s hs
    apply bath_le μ hμ b f y
    intro t ht
    exact hf (fiber_lt b hb h hs ht).le

lemma bath_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (x : α) :
    0 ≤ bath μ b f x ∧ bath μ b f x ≤ 1 :=
  ⟨le_bath μ hμ b f x 0 (fun y _ => (hf y).1),
   bath_le μ hμ b f x 1 (fun y _ => (hf y).2)⟩

lemma bath_expand
    {α : Type treewidthLevel1} {β : Type treewidthLevel2} [Fintype α] [LinearOrder α]
    [LinearOrder β]
    (μ : α → ℝ) (b : α → β) (f : α → ℝ) (x : α) :
    bath μ b f x = ∑ y, if b y = b x then μ y * f y / mass μ b x else 0 := by
  classical
  simp [bath, fiber, Finset.sum_filter, Finset.sum_div, ite_div]

theorem bath_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f : α → ℝ) : total μ (bath μ b f) = total μ f := by
  classical
  unfold total
  simp_rw [bath_expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  have he (x : α) :
      μ x * (if b y = b x then μ y * f y / mass μ b x else 0) =
      (if b x = b y then μ x else 0) * (μ y * f y / mass μ b y) := by
    by_cases h : b x = b y
    · have hm : mass μ b x = mass μ b y := by unfold mass; rw [fiber_eq b h]
      simp [h, hm]
    · simp [h, Ne.symm h]
  simp_rw [he]
  rw [← Finset.sum_mul]
  have hm : (∑ x, if b x = b y then μ x else 0) = mass μ b y := by
    simp [mass, fiber, Finset.sum_filter]
  rw [hm]
  field_simp [ne_of_gt (mass_pos μ hμ b y)]

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def defect (μ f p : α → ℝ) : ℝ :=
  ∑ x, μ x * (f x + p x - 2 * f x * p x)

noncomputable def optimal (μ : α → ℝ) (b : α → β) (f : α → ℝ) : α → Bool :=
  fun x => decide (1 / 2 < bath μ b f x)

noncomputable def labelReal (p : α → Bool) : α → ℝ :=
  fun x => if p x then 1 else 0

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

lemma defect_eq
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) :
    defect μ f p = total μ f + total μ p - 2 * total μ (fun x => f x * p x) := by
  classical
  simp only [defect, total, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

lemma bath_mul (μ : α → ℝ) (b : α → β) (f p : α → ℝ)
    (hp : ∀ x y, b x = b y → p x = p y) (x : α) :
    bath μ b (fun y => f y * p y) x = bath μ b f x * p x := by
  classical
  unfold bath
  have h : (∑ y ∈ fiber b x, μ y * (f y * p y)) =
      (∑ y ∈ fiber b x, μ y * f y) * p x := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y hy
    rw [hp y x ((mem_fiber b x y).mp hy)]
    ring
  rw [h]
  ring

lemma defect_bath (μ : α → ℝ) (hμ : ∀ x, 0 < μ x) (b : α → β)
    (f p : α → ℝ) (hp : ∀ x y, b x = b y → p x = p y) :
    defect μ (bath μ b f) p = defect μ f p := by
  rw [defect_eq, defect_eq, bath_total μ hμ b f]
  congr 1
  congr 1
  have h := bath_total μ hμ b (fun x => f x * p x)
  have hh : bath μ b (fun x => f x * p x) = (fun x => bath μ b f x * p x) :=
    funext (bath_mul μ b f p hp)
  rw [hh] at h
  exact h

lemma optimal_fiber (μ : α → ℝ) (b : α → β) (f : α → ℝ)
    {x y : α} (h : b x = b y) : optimal μ b f x = optimal μ b f y := by
  simp only [optimal, bath_const_fiber μ b f h]

theorem optimal_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (f : α → ℝ) (hf : Monotone f) :
    Monotone (optimal μ b f) := by
  intro x y hxy
  have h := bath_monotone μ hμ b hb f hf hxy
  simp only [optimal]
  by_cases hx : 1 / 2 < bath μ b f x
  · have hy : 1 / 2 < bath μ b f y := hx.trans_le h
    simp only [hx, hy, decide_true, le_refl]
  · simp only [hx, decide_false, Bool.false_le]

theorem optimal_defect_le (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (f p : α → ℝ) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y) :
    defect μ f (labelReal (optimal μ b f)) ≤ defect μ f p := by
  classical
  have hc : ∀ x y, b x = b y →
      labelReal (optimal μ b f) x = labelReal (optimal μ b f) y := by
    intro x y h
    simp only [labelReal, optimal_fiber μ b f h]
  rw [← defect_bath μ hμ b f _ hc, ← defect_bath μ hμ b f p hpb]
  apply Finset.sum_le_sum
  intro x _
  apply mul_le_mul_of_nonneg_left _ (hμ x).le
  dsimp [labelReal, optimal]
  split_ifs with h
  · have h' : 1 / 2 < bath μ b f x := of_decide_eq_true h
    simp only [h, ↓reduceIte]
    nlinarith [(hp x).2]
  · have h' : ¬1 / 2 < bath μ b f x := by simpa only [decide_eq_true_eq] using h
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    nlinarith [(hp x).1]

lemma labelReal_bounds
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (p : α → Bool) (x : α) :
    0 ≤ labelReal p x ∧ labelReal p x ≤ 1 := by
  simp only [labelReal]
  split <;> norm_num

lemma defect_mean_bound
    {α : Type treewidthLevel1} [Fintype α] [LinearOrder α]
    (μ f p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ p| ≤ defect μ f p := by
  classical
  have hl : total μ p - total μ f ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hf x).1 (sub_nonneg.mpr (hp x).2))])
  have hr : total μ f - total μ p ≤ defect μ f p := by
    unfold total defect
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_le_sum (fun x _ => by
      nlinarith [mul_nonneg (hμ x) (mul_nonneg (hp x).1 (sub_nonneg.mpr (hf x).2))])
  exact abs_le.mpr ⟨by linarith, hr⟩

lemma pair_mean_bound (μ f g p : α → ℝ) (hμ : ∀ x, 0 ≤ μ x)
    (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) (hg : ∀ x, 0 ≤ g x ∧ g x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1) :
    |total μ f - total μ g| ≤ defect μ f p + defect μ g p := by
  have h := abs_sub_le (total μ f) (total μ p) (total μ g)
  rw [abs_sub_comm (total μ p)] at h
  exact h.trans (add_le_add (defect_mean_bound μ f p hμ hf hp)
    (defect_mean_bound μ g p hμ hg hp))

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

/-- On a chain of nested cuts, a monotone classifier determined by its trace
on a bag is either constant or evaluation at one of that bag's vertices. -/
theorem monotone_classifier {P : Type*} (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p)) (c : α → Bool) (hc : Monotone c)
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → c x = c y) :
    c = (fun _ => false) ∨ c = (fun _ => true) ∨ ∃ p, c = (fun x => labels x p) := by
  classical
  by_cases hf : ∀ x, c x = false
  · exact Or.inl (funext hf)
  by_cases ht : ∀ x, c x = true
  · exact Or.inr (Or.inl (funext ht))
  push Not at hf ht
  obtain ⟨a, ha⟩ := ht
  obtain ⟨b, hb⟩ := hf
  have ha' : c a = false := by cases h : c a <;> simp_all
  have hb' : c b = true := by cases h : c b <;> simp_all
  let lo := Finset.univ.filter (fun x => c x = false)
  let hi := Finset.univ.filter (fun x => c x = true)
  have hlo : lo.Nonempty := ⟨a, by simp [lo, ha']⟩
  have hhi : hi.Nonempty := ⟨b, by simp [hi, hb']⟩
  let u := lo.max' hlo
  let v := hi.min' hhi
  have hu : c u = false := by simpa [lo] using lo.max'_mem hlo
  have hv : c v = true := by simpa [hi] using hi.min'_mem hhi
  have huv : u ≤ v := by
    by_contra h
    have hh := hc (le_of_lt (lt_of_not_ge h))
    rw [hu, hv] at hh
    contradiction
  have hn : ¬∀ p, labels u p = labels v p := by
    intro h
    have := htrace u v h
    rw [hu, hv] at this
    contradiction
  obtain ⟨p, hp⟩ := not_forall.mp hn
  have hlp : labels u p ≤ labels v p := hl p huv
  have hup : labels u p = false := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
    exact Bool.noConfusion (hlp rfl)
  have hvp : labels v p = true := by
    cases h : labels u p <;> cases h' : labels v p <;> simp_all
  refine Or.inr (Or.inr ⟨p, funext (fun x => ?_)⟩)
  cases hx : c x with
  | false =>
    have hxu : x ≤ u := lo.le_max' x (by simp [lo, hx])
    have h : labels x p ≤ labels u p := hl p hxu
    rw [hup] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)
  | true =>
    have hvx : v ≤ x := hi.min'_le x (by simp [hi, hx])
    have h : labels v p ≤ labels x p := hl p hvx
    rw [hvp] at h
    cases hx' : labels x p <;> simp_all
    exact Bool.noConfusion (h rfl)

/-- The height-gap transport estimate for a retained ordered sweep. `f` is the
backward endpoint response; interval heat baths keep it monotone and preserve
its mean. The comparison predictor may be arbitrarily randomized by the past. -/
theorem height_transport {P : Type*} (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (b : α → β) (hb : Monotone b) (labels : α → P → Bool)
    (hl : ∀ p, Monotone (fun x => labels x p))
    (htrace : ∀ x y, (∀ p, labels x p = labels y p) → b x = b y)
    (f p : α → ℝ) (hf : Monotone f) (hfb : ∀ x, 0 ≤ f x ∧ f x ≤ 1)
    (hp : ∀ x, 0 ≤ p x ∧ p x ≤ 1)
    (hpb : ∀ x y, b x = b y → p x = p y)
    (t : ℝ) (h0 : t ≤ total μ f) (h1 : t ≤ total μ (fun _ => 1) - total μ f)
    (hgap : ∀ v, t ≤ |total μ f - total μ (labelReal (fun x => labels x v))|) :
    t ≤ defect μ f p := by
  let c := optimal μ b f
  have hc := optimal_monotone μ hμ b hb f hf
  have hcTrace : ∀ x y, (∀ v, labels x v = labels y v) → c x = c y := by
    intro x y h
    exact optimal_fiber μ b f (htrace x y h)
  have ha := monotone_classifier labels hl c hc hcTrace
  have hmin := optimal_defect_le μ hμ b f p hp hpb
  have hmean := (defect_mean_bound μ f (labelReal c) (fun x => (hμ x).le) hfb
    (labelReal_bounds c)).trans hmin
  rcases ha with he | he | ⟨v, he⟩
  · have hm : total μ (labelReal c) = 0 := by simp [he, labelReal, total]
    rw [hm, sub_zero] at hmean
    have hn : 0 ≤ total μ f := Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x).le (hfb x).1)
    rw [abs_of_nonneg hn] at hmean
    exact h0.trans hmean
  · have hm : total μ (labelReal c) = total μ (fun _ => 1) := by simp [he, labelReal, total]
    rw [hm] at hmean
    have hn : total μ f ≤ total μ (fun _ => 1) :=
      Finset.sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hfb x).2 (hμ x).le)
    rw [abs_of_nonpos (sub_nonpos.mpr hn)] at hmean
    exact h1.trans (by linarith)
  · rw [he] at hmean
    exact (hgap v).trans hmean

end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedSweepFlow
variable {α β : Type*} [Fintype α] [LinearOrder α] [LinearOrder β]

noncomputable def execute (μ : α → ℝ) (bs : List (α → β)) (f : α → ℝ) : α → ℝ :=
  bs.foldr (fun b g => bath μ b g) f

lemma execute_monotone (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (hb : ∀ b ∈ bs, Monotone b)
    (f : α → ℝ) (hf : Monotone f) : Monotone (execute μ bs f) := by
  induction bs with
  | nil => exact hf
  | cons b bs ih =>
    exact bath_monotone μ hμ b (hb b (by simp)) _
      (ih (fun c hc => hb c (by simp [hc])))

lemma execute_total (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) : total μ (execute μ bs f) = total μ f := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    change total μ (bath μ b (execute μ bs f)) = _
    rw [bath_total μ hμ, ih]

lemma execute_bounds (μ : α → ℝ) (hμ : ∀ x, 0 < μ x)
    (bs : List (α → β)) (f : α → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    ∀ x, 0 ≤ execute μ bs f x ∧ execute μ bs f x ≤ 1 := by
  induction bs with
  | nil => exact hf
  | cons b bs ih => exact bath_bounds μ hμ b _ ih
end BoundedTreewidthL1.OrderedSweepFlow

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set
open scoped BigOperators
variable {V : Type*} [Fintype V]

noncomputable def trueSet (ω : V → Bool) : Finset V := by
  classical
  exact Finset.univ.filter (fun v => ω v = true)

def Carrier (M : ℝ) (F : V → ℝ) := {ω : V → Bool // 0 < (sweep M F).real {ω}}

noncomputable instance (M : ℝ) (F : V → ℝ) : Fintype (Carrier M F) := by
  unfold Carrier
  infer_instance

noncomputable def weight (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : ℝ :=
  (sweep M F).real {ω.val}

lemma weight_pos
    {V : Type treewidthLevel1} [Fintype V]
    (M : ℝ) (F : V → ℝ) (ω : Carrier M F) : 0 < weight M F ω := ω.property

lemma exists_threshold (M : ℝ) (F : V → ℝ) (ω : Carrier M F) :
    ∃ t ∈ Icc (-M) M, thresholdLabels F t = ω.val := by
  have hp : 0 < (sweep M F).real {ω.val} := ω.property
  change 0 < ((volume.restrict (Icc (-M) M)).map (thresholdLabels F)).real {ω.val} at hp
  rw [map_measureReal_apply (measurable_thresholdLabels F) (measurableSet_singleton ω.val),
    measureReal_restrict_apply ((measurable_thresholdLabels F) (measurableSet_singleton ω.val))] at hp
  have hn : ((thresholdLabels F ⁻¹' {ω.val}) ∩ Icc (-M) M).Nonempty := by
    by_contra he
    rw [Set.not_nonempty_iff_eq_empty.mp he, measureReal_empty] at hp
    exact (lt_irrefl 0) hp
  obtain ⟨t, ht, hm⟩ := hn
  exact ⟨t, hm, ht⟩

lemma thresholds_nested (F : V → ℝ) (s t : ℝ) (hst : s ≤ t) :
    trueSet (thresholdLabels F t) ⊆ trueSet (thresholdLabels F s) := by
  classical
  intro v hv
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and,
    thresholdLabels, decide_eq_true_eq] at hv ⊢
  exact hst.trans_lt hv

lemma carrier_nested (M : ℝ) (F : V → ℝ) (a b : Carrier M F) :
    trueSet a.val ⊆ trueSet b.val ∨ trueSet b.val ⊆ trueSet a.val := by
  obtain ⟨s, _, hs⟩ := exists_threshold M F a
  obtain ⟨t, _, ht⟩ := exists_threshold M F b
  rw [← hs, ← ht]
  rcases le_total s t with h | h
  · exact Or.inr (thresholds_nested F s t h)
  · exact Or.inl (thresholds_nested F t s h)

lemma trueSet_injective : Function.Injective (trueSet (V := V)) := by
  classical
  intro a b h
  funext v
  have he : v ∈ trueSet a ↔ v ∈ trueSet b := by rw [h]
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] at he
  cases ha : a v <;> cases hb : b v <;> simp_all

lemma rank_injective (M : ℝ) (F : V → ℝ) :
    Function.Injective (fun a : Carrier M F => (trueSet a.val).card) := by
  intro a b h
  apply Subtype.ext
  apply trueSet_injective
  rcases carrier_nested M F a b with hab | hba
  · exact Finset.eq_of_subset_of_card_le hab h.ge
  · exact (Finset.eq_of_subset_of_card_le hba h.le).symm

noncomputable instance carrierOrder (M : ℝ) (F : V → ℝ) : LinearOrder (Carrier M F) :=
  LinearOrder.lift' (fun a => (trueSet a.val).card) (rank_injective M F)

lemma labels_monotone (M : ℝ) (F : V → ℝ) (v : V) :
    Monotone (fun a : Carrier M F => a.val v) := by
  intro a b hab
  change (trueSet a.val).card ≤ (trueSet b.val).card at hab
  have hs : trueSet a.val ⊆ trueSet b.val := by
    rcases carrier_nested M F a b with h | h
    · exact h
    · exact (Finset.eq_of_subset_of_card_le h hab).symm.subset
  intro ha
  have hm : v ∈ trueSet a.val := by simp [trueSet, ha]
  simpa only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and] using hs hm

noncomputable def traceRank (M : ℝ) (F : V → ℝ) (P : Finset V) (ω : Carrier M F) : ℕ :=
  (P.filter (fun v => ω.val v = true)).card

lemma traceRank_monotone (M : ℝ) (F : V → ℝ) (P : Finset V) :
    Monotone (traceRank M F P) := by
  classical
  intro a b hab
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter] at hv ⊢
  exact ⟨hv.1, labels_monotone M F v hab hv.2⟩

lemma traceRank_fiber (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a b : Carrier M F) : traceRank M F P a = traceRank M F P b ↔
      ∀ v : P, a.val v = b.val v := by
  classical
  constructor
  · intro h
    have hn : (P.filter (fun v => a.val v = true)) ⊆ (P.filter (fun v => b.val v = true)) ∨
        (P.filter (fun v => b.val v = true)) ⊆ (P.filter (fun v => a.val v = true)) := by
      rcases le_total a b with hab | hba
      · left; intro v hv; simp only [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, labels_monotone M F v hab hv.2⟩
      · right; intro v hv; simp only [Finset.mem_filter] at hv ⊢
        exact ⟨hv.1, labels_monotone M F v hba hv.2⟩
    have he : (P.filter (fun v => a.val v = true)) = (P.filter (fun v => b.val v = true)) := by
      rcases hn with hab | hba
      · exact Finset.eq_of_subset_of_card_le hab h.ge
      · exact (Finset.eq_of_subset_of_card_le hba h.le).symm
    intro v
    have hv : v.val ∈ P.filter (fun v => a.val v = true) ↔
        v.val ∈ P.filter (fun v => b.val v = true) := by rw [he]
    simp only [Finset.mem_filter, v.property, true_and] at hv
    cases ha : a.val v <;> cases hb : b.val v <;> simp_all
  · intro h
    unfold traceRank
    congr 1
    apply Finset.filter_congr
    intro v hv
    rw [h ⟨v,hv⟩]

lemma sum_carrier (M : ℝ) (F : V → ℝ) (g : (V → Bool) → ℝ) :
    (∑ a : Carrier M F, weight M F a * g a.val) =
      ∑ a : V → Bool, (sweep M F).real {a} * g a := by
  classical
  have he := Fintype.sum_subtype_add_sum_subtype
    (fun a : V → Bool => 0 < (sweep M F).real {a})
    (fun a => (sweep M F).real {a} * g a)
  have hz : (∑ a : {a : V → Bool // ¬0 < (sweep M F).real {a}},
      (sweep M F).real {a.val} * g a.val) = 0 := by
    apply Finset.sum_eq_zero
    intro a _
    have ha : (sweep M F).real {a.val} = 0 :=
      le_antisymm (le_of_not_gt a.property) measureReal_nonneg
    simp [ha]
  rw [hz, add_zero] at he
  exact he

lemma sum_event (M : ℝ) (F : V → ℝ) (p : (V → Bool) → Prop) :
    (∑ a : V → Bool, (sweep M F).real {a} * (if p a then 1 else 0)) =
      (sweep M F).real {a | p a} := by
  classical
  have h := sum_measureReal_singleton (μ := sweep M F) (Finset.univ.filter p)
  simpa only [Finset.sum_filter, Finset.coe_filter, Finset.coe_univ,
    Set.ofPred_mem_eq, Set.mem_univ, Finset.mem_univ, true_and, mul_ite, mul_one, mul_zero] using h

lemma label_mean (M : ℝ) (F : V → ℝ) (v : V) (hv : -M ≤ F v ∧ F v ≤ M) :
    OrderedSweepFlow.total (weight M F)
      (OrderedSweepFlow.labelReal (fun a : Carrier M F => a.val v)) = F v + M := by
  classical
  rw [OrderedSweepFlow.total]
  change (∑ a : Carrier M F, weight M F a * (if a.val v then 1 else 0)) = _
  rw [sum_carrier M F (fun a => if a v then 1 else 0)]
  trans (sweep M F).real {a | a v = true}
  · convert sum_event M F (fun a => a v = true) using 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    split_ifs <;> rfl
  · rw [sweep, map_measureReal_apply (measurable_thresholdLabels F)
      ((Set.toFinite _).measurableSet),
      measureReal_restrict_apply ((measurable_thresholdLabels F) ((Set.toFinite _).measurableSet))]
    have he : (thresholdLabels F ⁻¹' {a | a v = true}) ∩ Icc (-M) M = Ico (-M) (F v) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq,
        thresholdLabels, decide_eq_true_eq, Set.mem_Icc, Set.mem_Ico]
      constructor
      · rintro ⟨h, h₁, _⟩; exact ⟨h₁,h⟩
      · rintro ⟨h₁,h⟩; exact ⟨h,h₁,h.le.trans hv.2⟩
    rw [he, Real.volume_real_Ico_of_le hv.1]
    ring

end BoundedTreewidthL1.OrderedReservation

namespace BoundedTreewidthL1.OrderedReservation
attribute [local instance] Classical.decEq Classical.propDecidable
open MeasureTheory Set OrderedSweepFlow
open scoped BigOperators
variable {V : Type*} [Fintype V]

lemma total_weight (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ) :
    total (weight M F) (fun _ => 1) = 2*M := by
  rw [total, sum_carrier M F (fun _ => 1)]
  simp only [mul_one]
  have he := sum_measureReal_singleton (μ := sweep M F) (Finset.univ : Finset (V → Bool))
  rw [he]
  simp only [Finset.coe_univ]
  rw [sweep, map_measureReal_apply (measurable_thresholdLabels F) MeasurableSet.univ]
  simp only [Set.preimage_univ, measureReal_restrict_apply_univ]
  rw [Real.volume_real_Icc_of_le (by linarith)]
  ring

/-- Explicit descending-reservation transport on the original sweep measure.
The chain may have any length, and testing and intermediate bags may repeat.
There is no width assumption or Markov-flow hypothesis. -/
theorem sweep_height_transport (M : ℝ) (hM : 0 ≤ M) (F : V → ℝ)
    (hF : ∀ v, -M ≤ F v ∧ F v ≤ M) (z : V) (P : Finset V)
    (bags : List (Finset V)) (p : Carrier M F → ℝ)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hptrace : ∀ a b, (∀ v : P, a.val v = b.val v) → p a = p b)
    (t : ℝ) (hlo : t ≤ F z + M) (hhi : t ≤ M - F z)
    (hgap : ∀ v ∈ P, t ≤ |F z - F v|) :
    t ≤ defect (weight M F)
      (execute (weight M F) (bags.map (traceRank M F))
        (labelReal (fun a => a.val z))) p := by
  let f := execute (weight M F) (bags.map (traceRank M F))
    (labelReal (fun a => a.val z))
  have hm : total (weight M F) f = F z + M := by
    rw [execute_total _ (weight_pos M F), label_mean M F z (hF z)]
  have hf : Monotone f := by
    apply execute_monotone _ (weight_pos M F)
    · intro b hb
      obtain ⟨Q,_,rfl⟩ := List.mem_map.mp hb
      exact traceRank_monotone M F Q
    · intro a b hab
      dsimp [labelReal]
      have hl := labels_monotone M F z hab
      by_cases ha : a.val z = true
      · have hb : b.val z = true := hl ha
        simp [ha, hb]
      · simp [ha]
        split_ifs <;> norm_num
  apply height_transport (weight M F) (weight_pos M F)
    (traceRank M F P) (traceRank_monotone M F P)
    (fun a (v : P) => a.val v) (fun v => labels_monotone M F v)
    (fun a b h => (traceRank_fiber M F P a b).mpr h)
    f p hf (execute_bounds _ (weight_pos M F) _ _ (labelReal_bounds _)) hp
    (fun a b h => hptrace a b ((traceRank_fiber M F P a b).mp h))
  · exact hm ▸ hlo
  · rw [total_weight M hM F, hm]
    linarith
  · intro v
    rw [hm, label_mean M F v (hF v)]
    simpa using hgap v v.property
end BoundedTreewidthL1.OrderedReservation

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ReservationCoupling
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]

structure IsCoupling (μ : A → ℝ) (ν : B → ℝ) (Q : A → B → ℝ) : Prop where
  nonneg : ∀ a b, 0 ≤ Q a b
  row : ∀ a, ∑ b, Q a b = μ a
  col : ∀ b, ∑ a, Q a b = ν b

noncomputable def action (μ : A → ℝ) (Q : A → B → ℝ) (f : B → ℝ) (a : A) : ℝ :=
  (∑ b, Q a b * f b) / μ a

noncomputable def total (μ f : A → ℝ) : ℝ := ∑ a, μ a * f a
noncomputable def defect (μ f p : A → ℝ) : ℝ :=
  ∑ a, μ a * (f a + p a - 2*f a*p a)

lemma IsCoupling.symm {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) : IsCoupling ν μ (fun b a => Q a b) :=
  ⟨fun b a => h.nonneg a b, h.col, h.row⟩

lemma IsCoupling.left_nonneg {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (a : A) : 0 ≤ μ a := by
  rw [← h.row]
  exact Finset.sum_nonneg (fun b _ => h.nonneg a b)

lemma IsCoupling.right_nonneg {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (b : B) : 0 ≤ ν b := h.symm.left_nonneg b

lemma IsCoupling.row_zero {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (a : A) (ha : μ a = 0) (b : B) : Q a b = 0 := by
  have hr := h.row a
  rw [ha] at hr
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => h.nonneg a x)).mp hr b (Finset.mem_univ _)

lemma weighted_action {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (a : A) :
    μ a * action μ Q f a = ∑ b, Q a b * f b := by
  by_cases ha : μ a = 0
  · simp [action, ha, h.row_zero a ha]
  · unfold action
    field_simp

lemma action_bounds {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b ∧ f b ≤ 1) (a : A) :
    0 ≤ action μ Q f a ∧ action μ Q f a ≤ 1 := by
  have hn : 0 ≤ ∑ b, Q a b * f b :=
    Finset.sum_nonneg (fun b _ => mul_nonneg (h.nonneg a b) (hf b).1)
  have hl : (∑ b, Q a b * f b) ≤ μ a := by
    rw [← h.row a]
    apply Finset.sum_le_sum
    intro b _
    simpa using mul_le_mul_of_nonneg_left (hf b).2 (h.nonneg a b)
  refine ⟨div_nonneg hn (h.left_nonneg a), ?_⟩
  by_cases ha : μ a = 0
  · simp [action, ha]
  · exact (div_le_one (lt_of_le_of_ne (h.left_nonneg a) (Ne.symm ha))).mpr hl

lemma action_total {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) : total μ (action μ Q f) = total ν f := by
  unfold total
  simp_rw [weighted_action h]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, h.col]

lemma action_adjoint {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (p : A → ℝ) :
    total μ (fun a => p a * action μ Q f a) =
      total ν (fun b => f b * action ν (fun b a => Q a b) p b) := by
  unfold total
  conv_lhs =>
    arg 2; ext a
    rw [← mul_assoc, mul_right_comm, weighted_action h, Finset.sum_mul]
  conv_rhs =>
    arg 2; ext b
    rw [← mul_assoc, mul_right_comm, weighted_action h.symm, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma defect_form (μ f p : A → ℝ) :
    defect μ f p = total μ f + total μ p - 2*total μ (fun a => p a*f a) := by
  unfold defect total
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

lemma defect_nonneg (μ f p : A → ℝ) (hμ : ∀ a, 0 ≤ μ a)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    0 ≤ defect μ f p := by
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (hμ a)
  have h₁ := mul_nonneg (hf a).1 (sub_nonneg.mpr (hp a).2)
  have h₂ := mul_nonneg (hp a).1 (sub_nonneg.mpr (hf a).2)
  nlinarith

/-- Move one true finite Markov transition from the endpoint response to the
past predictor. This does not lose any mass, even with zero-probability states. -/
theorem transfer_defect {μ : A → ℝ} {ν : B → ℝ} {Q : A → B → ℝ}
    (h : IsCoupling μ ν Q) (f : B → ℝ) (p : A → ℝ) :
    defect μ (action μ Q f) p = defect ν f (action ν (fun b a => Q a b) p) := by
  rw [defect_form, defect_form, action_total h, action_total h.symm,
    action_adjoint h f p]
  congr 1
  congr 1
  unfold total
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Responses through a constant finite state space, with time-dependent laws. -/
noncomputable def response (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (t : ℕ) : ℕ → (A → ℝ) → (A → ℝ)
  | 0, f => f
  | n+1, f => action (μ t) (Q t) (response μ Q (t+1) n f)

lemma response_bounds (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ t, IsCoupling (μ t) (μ (t+1)) (Q t)) (t n : ℕ) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    ∀ a, 0 ≤ response μ Q t n f a ∧ response μ Q t n f a ≤ 1 := by
  induction n generalizing t with
  | zero => exact hf
  | succ n ih => exact action_bounds (hQ t) _ (ih (t+1))

lemma response_total (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ t, IsCoupling (μ t) (μ (t+1)) (Q t)) (t n : ℕ) (f : A → ℝ) :
    total (μ t) (response μ Q t n f) = total (μ (t+n)) f := by
  induction n generalizing t with
  | zero => simp [response]
  | succ n ih =>
    change total (μ t) (action (μ t) (Q t) _) = _
    rw [action_total (hQ t), ih]
    congr 2
    omega
end BoundedTreewidthL1.ReservationCoupling

namespace BoundedTreewidthL1.ReservedKernel
open MeasureTheory ExpandedParticleLaw ReservationCoupling
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def lift (M : ℝ) (F : V → ℝ) (i : ι) (a : OrderedReservation.Carrier M F) : State ι V :=
  (i,false,a.val)

lemma glue_action {A B C : Type*} [Fintype A] [Fintype B]
    (key : A → C) (key' : B → C) (μ : A → ℝ) (ν : B → ℝ) (f : B → ℝ)
    (a : A) (ha : μ a ≠ 0) :
    action μ (glueWeights key key' μ ν) f a =
    (∑ b, if key' b = key a then ν b*f b else 0) / marginal key μ (key a) := by
  unfold action
  have he : (∑ b, glueWeights key key' μ ν a b * f b) =
      μ a * (∑ b, if key' b = key a then ν b*f b else 0) / marginal key μ (key a) := by
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro b _
    unfold glueWeights
    by_cases h : key' b = key a
    · simp only [h, ↓reduceIte]
      ring
    · simp [h, Ne.symm h]
  rw [he]
  field_simp

lemma old_key
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (i j r : ι) (q : Bool) (hir : r ≠ i) (hjr : r ≠ j)
    (x : State ι V) : departureKey i j x = (r,q) ↔ x.1 = r ∧ x.2.1 = q := by
  unfold departureKey
  simp only [Prod.mk.injEq]
  by_cases hx : x.1 = j
  · simp [hx, Ne.symm hir, Ne.symm hjr]
  · simp [hx]

lemma sum_old_key (i j r : ι) (q : Bool) (hir : r ≠ i) (hjr : r ≠ j)
    (f : State ι V → ℝ) :
    (∑ x, if departureKey i j x = (r,q) then f x else 0) =
      ∑ ω : V → Bool, f (r,q,ω) := by
  simp_rw [old_key i j r q hir hjr]
  simp only [Fintype.sum_prod_type]
  cases q <;> simp [ite_and]

lemma positive_trace_sum (M : ℝ) (F : V → ℝ) (P : Finset V)
    (a : OrderedReservation.Carrier M F) (g : (V → Bool) → ℝ) :
    (∑ ω : V → Bool, if (fun v : P => ω v) = (fun v : P => a.val v) then
      (sweep M F).real {ω} * g ω else 0) =
    ∑ b : OrderedReservation.Carrier M F,
      if OrderedReservation.traceRank M F P b = OrderedReservation.traceRank M F P a then
        OrderedReservation.weight M F b * g b.val else 0 := by
  have he := OrderedReservation.sum_carrier M F
    (fun ω => if (fun v : P => ω v) = (fun v : P => a.val v) then g ω else 0)
  simp only [mul_ite,mul_zero] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro b _
  have hb : ((fun v : P => b.val v) = (fun v : P => a.val v)) ↔
      OrderedReservation.traceRank M F P b = OrderedReservation.traceRank M F P a := by
    rw [OrderedReservation.traceRank_fiber]
    exact funext_iff
  simp only [hb]

lemma departure_old_numerator (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j r : ι)
    (hir : r ≠ i) (hjr : r ≠ j) (a : OrderedReservation.Carrier M (F r))
    (f : State ι V → ℝ) :
    (∑ b, if (departureKey i j b, trace P b) =
      (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a)) then
      weight M F b * f b else 0) =
    (∑ b : OrderedReservation.Carrier M (F r),
      if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
        OrderedReservation.weight M (F r) b * f (lift M (F r) r b) else 0)/2 := by
  have hk : departureKey i j (lift M (F r) r a) = (r,false) := by simp [departureKey,lift,hjr]
  simp only [hk, Prod.mk.injEq, ite_and]
  rw [sum_old_key i j r false hir hjr]
  change (∑ ω : V → Bool, if (fun v : P => ω v) = (fun v : P => a.val v) then
    (sweep M (F r)).real {ω} / 2 * f (r,false,ω) else 0) = _
  have he := positive_trace_sum M (F r) P a (fun ω => f (r,false,ω))
  erw [← he, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  split_ifs <;> ring

/-- Restrict the ACTUAL departure kernel to an old retained particle: it is
exactly the monotone interval heat bath, not an arbitrary common submeasure. -/
theorem departure_action_old (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j r : ι)
    (hir : r ≠ i) (hjr : r ≠ j) (a : OrderedReservation.Carrier M (F r))
    (f : State ι V → ℝ) :
    action (weight M F) (departure M F P i j) f (lift M (F r) r a) =
      OrderedSweepFlow.bath (OrderedReservation.weight M (F r))
        (OrderedReservation.traceRank M (F r) P) (fun b => f (lift M (F r) r b)) a := by
  have hpos : 0 < weight M F (lift M (F r) r a) :=
    div_pos a.property (by norm_num)
  unfold departure
  rw [glue_action _ _ _ _ _ _ hpos.ne']
  trans ((∑ b : OrderedReservation.Carrier M (F r),
      if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
        OrderedReservation.weight M (F r) b * f (lift M (F r) r b) else 0)/2) /
      marginal (fun x => (departureKey i j x, trace P x)) (weight M F)
        (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a))
  · congr 1
    convert departure_old_numerator M F P i j r hir hjr a f using 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  have hd := departure_old_numerator M F P i j r hir hjr a (fun _ => 1)
  simp only [mul_one] at hd
  have hd' : marginal (fun x : State ι V => (departureKey i j x, trace P x)) (weight M F)
      (departureKey i j (lift M (F r) r a), trace P (lift M (F r) r a)) =
      (∑ b : OrderedReservation.Carrier M (F r),
        if OrderedReservation.traceRank M (F r) P b = OrderedReservation.traceRank M (F r) P a then
          OrderedReservation.weight M (F r) b else 0)/2 := by
    unfold marginal
    convert hd using 1
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> rfl
  rw [hd']
  unfold OrderedSweepFlow.bath OrderedSweepFlow.mass OrderedSweepFlow.fiber
  simp only [Finset.sum_filter]
  ring

/-- A retained incoming particle is copied exactly, as a whole global cut. -/
lemma incoming_action_retained (M : ℝ) (F H : ι → V → ℝ) (P : Finset V) (C : Finset ι)
    (hret : ∀ i ∈ C, F i = H i) (htrace : particleTrace M F P = particleTrace M H P)
    (a : State ι V) (ha : a.1 ∈ C) (hpos : weight M F a ≠ 0) (f : State ι V → ℝ) :
    action (weight M F) (incoming M F H P C) f a = f a := by
  obtain ⟨hn, hr, hc, ht, hs⟩ := incoming_coupling M F H P C hret htrace
  unfold action
  have he : (∑ b, incoming M F H P C a b * f b) = weight M F a * f a := by
    rw [← hr a, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro b _
    by_cases hb : a = b
    · rw [← hb]
    · rw [hs a b ha hb, zero_mul, zero_mul]
  rw [he, mul_div_cancel_left₀ _ hpos]

lemma action_compose {A B C : Type*} [Fintype A] [Fintype B] [Fintype C]
    (μ : A → ℝ) (ν : B → ℝ) (J : A → B → ℝ) (K : B → C → ℝ) (f : C → ℝ) :
    action μ (ExpandedParticleKernel.compose ν J K) f = action μ J (action ν K f) := by
  funext a
  unfold action ExpandedParticleKernel.compose
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [← mul_div_assoc, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- Departure is symmetric: predictors are reheated by the same kernel. -/
lemma departure_symmetric (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    ∀ a b, departure M F P i j a b = departure M F P i j b a := by
  intro a b
  unfold departure glueWeights
  by_cases h : (departureKey i j a, trace P a) = (departureKey i j b, trace P b)
  · simp only [h, ↓reduceIte]
    ring
  · simp [h, Ne.symm h]

end BoundedTreewidthL1.ReservedKernel

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ReservedTests
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def part (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) : ℝ :=
  ∑ ω : V → Bool, weight M F (i,q,ω) *
    (f (i,q,ω)+p (i,q,ω)-2*f (i,q,ω)*p (i,q,ω))

lemma part_nonneg (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : 0 ≤ part M F i q f p := by
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg (weight_nonneg _ _ _)
  have h₁ := mul_nonneg (hf (i,q,ω)).1 (sub_nonneg.mpr (hp (i,q,ω)).2)
  have h₂ := mul_nonneg (hp (i,q,ω)).1 (sub_nonneg.mpr (hf (i,q,ω)).2)
  nlinarith

lemma sum_part (M : ℝ) (F : ι → V → ℝ) (f p : State ι V → ℝ) :
    (∑ i, ∑ q, part M F i q f p) = defect (weight M F) f p := by
  simp only [defect, part, Fintype.sum_prod_type]

lemma part_le (M : ℝ) (F : ι → V → ℝ) (i : ι) (q : Bool)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) : part M F i q f p ≤ defect (weight M F) f p := by
  rw [← sum_part]
  exact (Finset.single_le_sum (fun b _ => part_nonneg M F i b f p hf hp)
    (Finset.mem_univ q)).trans (Finset.single_le_sum
      (fun j _ => Finset.sum_nonneg (fun b _ => part_nonneg M F j b f p hf hp)) (Finset.mem_univ i))

lemma pair_part_le (M : ℝ) (F : ι → V → ℝ) (i j : ι) (hij : i ≠ j)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1)
    (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    part M F i false f p + part M F j false f p ≤ defect (weight M F) f p := by
  rw [← sum_part]
  have hb k : part M F k false f p ≤ ∑ q, part M F k q f p :=
    Finset.single_le_sum (fun b _ => part_nonneg M F k b f p hf hp) (Finset.mem_univ _)
  apply (add_le_add (hb i) (hb j)).trans
  have he : (∑ k ∈ ({i,j} : Finset ι), ∑ q, part M F k q f p) =
      (∑ q, part M F i q f p) + ∑ q, part M F j q f p := by simp [hij]
  rw [← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun k _ _ => Finset.sum_nonneg (fun q _ => part_nonneg M F k q f p hf hp))

lemma part_eq
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (F : ι → V → ℝ) (i : ι) (f p : State ι V → ℝ) :
    part M F i false f p =
      OrderedSweepFlow.defect (OrderedReservation.weight M (F i))
        (fun a => f (lift M (F i) i a)) (fun a => p (lift M (F i) i a)) / 2 := by
  unfold part OrderedSweepFlow.defect
  have he := OrderedReservation.sum_carrier M (F i)
    (fun ω => f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω))
  change (∑ ω : V → Bool, (sweep M (F i)).real {ω}/2 *
    (f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω))) = _
  trans (∑ ω : V → Bool, (sweep M (F i)).real {ω} *
    (f (i,false,ω)+p (i,false,ω)-2*f (i,false,ω)*p (i,false,ω)))/2
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    ring
  · rw [← he]
    rfl

lemma departure_isCoupling (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι) :
    IsCoupling (weight M F) (weight M F) (departure M F P i j) := by
  obtain ⟨hn,hr,hc,ht,hk⟩ := departure_coupling M F P i j
  exact ⟨hn,hr,hc⟩

/-- The exact single OLD-particle height test for the real expanded departure
coupling. The suffix is the proved interval-resampling response. -/
theorem height_test (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) (P : Finset V)
    (i j r : ι) (hir : r ≠ i) (hjr : r ≠ j)
    (hF : ∀ v, -M ≤ F r v ∧ F r v ≤ M) (z : V) (bags : List (Finset V))
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hresponse : ∀ a : OrderedReservation.Carrier M (F r),
      f (lift M (F r) r a) = OrderedSweepFlow.execute (OrderedReservation.weight M (F r))
        (bags.map (OrderedReservation.traceRank M (F r)))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) a)
    (t : ℝ) (hlo : t ≤ F r z + M) (hhi : t ≤ M - F r z)
    (hgap : ∀ v ∈ P, t ≤ |F r z - F r v|) :
    t/2 ≤ defect (weight M F) (action (weight M F) (departure M F P i j) f) p := by
  let q := action (weight M F) (departure M F P i j) p
  have hQ := departure_isCoupling M F P i j
  have hq (a : State ι V) : 0 ≤ q a ∧ q a ≤ 1 := action_bounds hQ p hp a
  have ht : ∀ a b : OrderedReservation.Carrier M (F r),
      (∀ v : P, a.val v = b.val v) → q (lift M (F r) r a) = q (lift M (F r) r b) := by
    intro a b hab
    dsimp [q]
    rw [departure_action_old M F P i j r hir hjr, departure_action_old M F P i j r hir hjr]
    apply OrderedSweepFlow.bath_const_fiber
    exact (OrderedReservation.traceRank_fiber M (F r) P a b).mpr hab
  have hl := OrderedReservation.sweep_height_transport M hM (F r) hF z P bags
    (fun a => q (lift M (F r) r a)) (fun a => hq _) ht t hlo hhi hgap
  have he : (fun a : OrderedReservation.Carrier M (F r) => f (lift M (F r) r a)) =
      OrderedSweepFlow.execute (OrderedReservation.weight M (F r))
        (bags.map (OrderedReservation.traceRank M (F r)))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) := funext hresponse
  rw [transfer_defect hQ]
  have hs : (fun b a => departure M F P i j a b) = departure M F P i j := by
    funext b a
    exact departure_symmetric M F P i j a b
  rw [hs]
  apply le_trans _ (part_le M F r false f q hf hq)
  rw [part_eq, he]
  exact div_le_div_of_nonneg_right hl (by norm_num)

lemma sum_marginal_eval {A C : Type*} [Fintype A] [Fintype C]
    (key : A → C) (μ : A → ℝ) (g : C → ℝ) :
    (∑ a, μ a * g (key a)) = ∑ c, marginal key μ c * g c := by
  unfold marginal
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp

lemma sweep_trace_marginal_eq (M : ℝ) (F H : V → ℝ) (P : Finset V)
    (h : ∀ v ∈ P, F v = H v) (b : P → Bool) :
    marginal (fun ω : V → Bool => fun v : P => ω v) (fun ω => (sweep M F).real {ω}) b =
    marginal (fun ω : V → Bool => fun v : P => ω v) (fun ω => (sweep M H).real {ω}) b := by
  unfold marginal
  rw [finite_event, finite_event]
  rw [sweep, sweep, map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite _).measurableSet,
    map_measureReal_apply (measurable_thresholdLabels _) (Set.toFinite _).measurableSet]
  congr 1
  ext t
  have he : (fun v : P => thresholdLabels F t v) = (fun v : P => thresholdLabels H t v) := by
    funext v
    simp [thresholdLabels, h v v.property]
  change ((fun v : P => thresholdLabels F t v) = b) ↔ ((fun v : P => thresholdLabels H t v) = b)
  rw [he]

noncomputable def traceAverage (M : ℝ) (F : ι → V → ℝ) (P : Finset V)
    (i j : ι) (p : State ι V → ℝ) (c : (ι × Bool) × (P → Bool)) : ℝ :=
  (∑ b, if (departureKey i j b, trace P b) = c then weight M F b * p b else 0) /
    marginal (fun a => (departureKey i j a, trace P a)) (weight M F) c

lemma action_average (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι)
    (p : State ι V → ℝ) (a : State ι V) (ha : weight M F a ≠ 0) :
    action (weight M F) (departure M F P i j) p a =
      traceAverage M F P i j p (departureKey i j a,trace P a) := by
  unfold departure
  rw [glue_action _ _ _ _ _ _ ha]
  unfold traceAverage
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  split_ifs <;> rfl

lemma fresh_keys
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (i j : ι) (hij : i ≠ j) (q : Bool) (ω : V → Bool) :
    departureKey i j (i,q,ω) = (i,q) ∧ departureKey i j (j,q,ω) = (i,q) := by
  simp [departureKey, hij]

lemma fresh_predictor_mean (M : ℝ) (F : ι → V → ℝ) (P : Finset V)
    (i j : ι) (hij : i ≠ j) (hbag : ∀ v ∈ P, F i v = F j v)
    (p : State ι V → ℝ) :
    (∑ ω : V → Bool, weight M F (i,false,ω) *
      action (weight M F) (departure M F P i j) p (i,false,ω)) =
    ∑ ω : V → Bool, weight M F (j,false,ω) *
      action (weight M F) (departure M F P i j) p (j,false,ω) := by
  let h (b : P → Bool) := traceAverage M F P i j p ((i,false),b)
  have he (r : ι) (hr : r = i ∨ r = j) :
      (∑ ω : V → Bool, weight M F (r,false,ω) *
        action (weight M F) (departure M F P i j) p (r,false,ω)) =
      (∑ ω : V → Bool, (sweep M (F r)).real {ω} * h (fun v : P => ω v))/2 := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hz : weight M F (r,false,ω) = 0
    · have hz' : (sweep M (F r)).real {ω} = 0 := by simpa [weight] using hz
      simp [hz, hz']
    · rw [action_average M F P i j p _ hz]
      have hk : departureKey i j (r,false,ω) = (i,false) := by
        rcases hr with hr | hr
        · rw [hr]
          exact (fresh_keys i j hij _ ω).1
        · rw [hr]
          exact (fresh_keys i j hij _ ω).2
      simp only [hk, ]
      change ((sweep M (F r)).real {ω}/2) * h (fun v : P => ω v) = _
      ring
  rw [he i (Or.inl rfl), he j (Or.inr rfl)]
  congr 1
  rw [sum_marginal_eval (fun ω : V → Bool => fun v : P => ω v)
    (fun ω => (sweep M (F i)).real {ω}) h,
    sum_marginal_eval (fun ω : V → Bool => fun v : P => ω v)
      (fun ω => (sweep M (F j)).real {ω}) h]
  apply Finset.sum_congr rfl
  intro b _
  rw [sweep_trace_marginal_eq M (F i) (F j) P hbag]

lemma part_mean_bound (M : ℝ) (F : ι → V → ℝ) (i : ι)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1) :
    |(∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) -
      ∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)| ≤ part M F i false f p := by
  have hl : (∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)) -
      (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) ≤ part M F i false f p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have h := mul_nonneg (weight_nonneg M F (i,false,ω))
      (mul_nonneg (hf (i,false,ω)).1 (sub_nonneg.mpr (hp (i,false,ω)).2))
    nlinarith
  have hr : (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) -
      (∑ ω : V → Bool, weight M F (i,false,ω)*p (i,false,ω)) ≤ part M F i false f p := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro ω _
    have h := mul_nonneg (weight_nonneg M F (i,false,ω))
      (mul_nonneg (hp (i,false,ω)).1 (sub_nonneg.mpr (hf (i,false,ω)).2))
    nlinarith
  exact abs_le.mpr ⟨by linarith,hr⟩

/-- EXACT fresh pair departure test. Only equal bag values, distinct reserved
indices and the true per-particle suffix means are required. -/
theorem launch_test (M : ℝ) (F : ι → V → ℝ) (P : Finset V) (i j : ι)
    (hij : i ≠ j) (hbag : ∀ v ∈ P, F i v = F j v) (z : V)
    (f p : State ι V → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (hp : ∀ a, 0 ≤ p a ∧ p a ≤ 1)
    (hi : (∑ ω : V → Bool, weight M F (i,false,ω)*f (i,false,ω)) = (F i z + M)/2)
    (hj : (∑ ω : V → Bool, weight M F (j,false,ω)*f (j,false,ω)) = (F j z + M)/2) :
    |F i z - F j z|/2 ≤ defect (weight M F) (action (weight M F) (departure M F P i j) f) p := by
  let q := action (weight M F) (departure M F P i j) p
  have hQ := departure_isCoupling M F P i j
  have hq (a : State ι V) : 0 ≤ q a ∧ q a ≤ 1 := action_bounds hQ p hp a
  have hm := fresh_predictor_mean M F P i j hij hbag p
  have h₁ := part_mean_bound M F i f q hf hq
  have h₂ := part_mean_bound M F j f q hf hq
  rw [hi] at h₁
  rw [hj] at h₂
  have ha := abs_sub_le ((F i z + M)/2)
    (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω)) ((F j z+M)/2)
  rw [abs_sub_comm (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω))] at ha
  change (∑ ω : V → Bool, weight M F (i,false,ω)*q (i,false,ω)) =
    (∑ ω : V → Bool, weight M F (j,false,ω)*q (j,false,ω)) at hm
  rw [← hm] at h₂
  have hab : |F i z - F j z|/2 ≤ part M F i false f q + part M F j false f q := by
    have he : (F i z+M)/2 - (F j z+M)/2 = (F i z-F j z)/2 := by ring
    rw [he, abs_div, abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
    exact ha.trans (add_le_add h₁ h₂)
  rw [transfer_defect hQ]
  have hs : (fun b a => departure M F P i j a b) = departure M F P i j := by
    funext b a
    exact departure_symmetric M F P i j a b
  rw [hs]
  exact hab.trans (pair_part_le M F i j hij f q hf hq)

end BoundedTreewidthL1.ReservedTests

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- The actual parent departure followed by the actual child incoming update. -/
noncomputable def edge (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V)
    (i j : ι) (C : Finset ι) : State ι V → State ι V → ℝ :=
  ExpandedParticleKernel.compose (weight M F) (departure M F P i j) (incoming M F H Q C)

lemma edge_coupling (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j : ι) (C : Finset ι)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q) :
    IsCoupling (weight M F) (weight M H) (edge M F H P Q i j C) := by
  obtain ⟨hd, hdr, hdc, _, _⟩ := departure_coupling M F P i j
  obtain ⟨hi, hir, hic, _, _⟩ := incoming_coupling M F H Q C hret htrace
  obtain ⟨hn,hr,hc⟩ := ExpandedParticleKernel.compose_coupling (weight M F) (weight M F)
    (weight M H) (departure M F P i j) (incoming M F H Q C)
    (weight_nonneg M F) (weight_nonneg M F) (weight_nonneg M H) hd hi hdr hdc hir hic
  exact ⟨hn,hr,hc⟩

lemma edge_restrict (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j r : ι) (C : Finset ι)
    (hir : r ≠ i) (hjr : r ≠ j) (hrC : r ∈ C)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q)
    (a : OrderedReservation.Carrier M (F r)) (f : State ι V → ℝ) :
    action (weight M F) (edge M F H P Q i j C) f (lift M (F r) r a) =
      OrderedSweepFlow.bath (OrderedReservation.weight M (F r))
        (OrderedReservation.traceRank M (F r) P) (fun b => f (lift M (F r) r b)) a := by
  rw [edge, action_compose, departure_action_old M F P i j r hir hjr]
  congr 1
  funext b
  exact incoming_action_retained M F H Q C hret htrace _ hrC
    (ne_of_gt (div_pos b.property (by norm_num))) f

noncomputable def kernels (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι) (t : ℕ) :=
  edge M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) (C t)

noncomputable def bags (P : ℕ → Finset V) (t n : ℕ) : List (Finset V) :=
  (List.range n).map (fun s => P (t+s))

lemma bags_succ
    {V : Type treewidthLevel1} [Fintype V]
    (P : ℕ → Finset V) (t n : ℕ) :
    bags P t (n+1) = P t :: bags P (t+1) n := by
  simp only [bags, List.range_succ_eq_map, List.map_cons, Nat.add_zero, List.map_map]
  congr 2
  funext s
  simp only [Function.comp_apply]
  congr 1
  omega

/-- A reserved old particle's true suffix response is exactly a sequence of
ordered interval heat baths. All transitions are the expanded preparation ones. -/
theorem response_restrict (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (hret : ∀ s r, r ∈ C s → F s r = F (s+1) r)
    (htrace : ∀ s, particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (t n : ℕ) (r : ι) (G : V → ℝ)
    (hfixed : ∀ s, t ≤ s → s ≤ t+n → F s r = G)
    (hkeep : ∀ s, t ≤ s → s < t+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M G) :
    response (fun s => weight M (F s)) (kernels M F P fresh₁ fresh₂ C) t n
      (fun b => if label b z then 1 else 0) (lift M G r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M G)
        ((bags P t n).map (OrderedReservation.traceRank M G))
        (OrderedSweepFlow.labelReal (fun b => b.val z)) a := by
  induction n generalizing t a with
  | zero => rfl
  | succ n ih =>
    have ht : F t r = G := hfixed t le_rfl (by omega)
    subst G
    have hk := hkeep t le_rfl (by omega)
    change action (weight M (F t)) (kernels M F P fresh₁ fresh₂ C t)
      (response (fun s => weight M (F s)) (kernels M F P fresh₁ fresh₂ C) (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) = _
    unfold kernels
    rw [edge_restrict M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) r (C t)
      hk.2.1 hk.2.2 hk.1 (hret t) (htrace t)]
    have hfixed' : ∀ s, t+1 ≤ s → s ≤ (t+1)+n → F s r = F t r := by
      intro s hs hs'
      exact hfixed s (by omega) (by omega)
    have hkeep' : ∀ s, t+1 ≤ s → s < (t+1)+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s := by
      intro s hs hs'
      exact hkeep s (by omega) (by omega)
    rw [bags_succ, List.map_cons, OrderedSweepFlow.execute]
    congr 1
    funext b
    exact ih (t+1) hfixed' hkeep' b
end BoundedTreewidthL1.ReservedSuffix

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]
abbrev History (n : ℕ) := (i : Fin (n+1)) → L i.val
noncomputable def weight (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (x : History L n) : ℝ :=
  p (x 0) * ∏ i : Fin n, K i.val (x i.castSucc) (x i.succ)
noncomputable def forward (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ) :
    (n : ℕ) → L n → ℝ
  | 0 => p
  | n+1 => fun b => ∑ a, forward p K n a * K n a b

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

lemma weight_snoc
    (L : ℕ → Type treewidthLevel1) [(i : ℕ) → Fintype (L i)]
    (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (x : History L n) (b : L (n+1)) :
    weight L p K (n+1) (Fin.snoc x b) = weight L p K n x * K n (x (Fin.last n)) b := by
  classical
  unfold weight
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.succ_last, Fin.snoc_last, ← Fin.castSucc_succ,
    Fin.snoc_castSucc, Fin.val_castSucc, Fin.val_last]
  change p (@Fin.snoc (n+1) (fun i : Fin (n+2) => L i.val) x b ((0 : Fin (n+1)).castSucc)) * _ = _
  rw [Fin.snoc_castSucc]
  ring

lemma sum_history_snoc (n : ℕ) (f : History L (n+1) → ℝ) :
    (∑ x, f x) = ∑ b : L (n+1), ∑ x : History L n, f (Fin.snoc x b) := by
  classical
  rw [← (Fin.snocEquiv (fun i : Fin (n+2) => L i.val)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

lemma terminal_marginal (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (b : L n) :
    (∑ x : History L n, if x (Fin.last n) = b then weight L p K n x else 0) =
      forward L p K n b := by
  classical
  induction n with
  | zero =>
    let he : L 0 ≃ History L 0 := (Equiv.piUnique (fun i : Fin 1 => L i.val)).symm
    rw [← he.sum_comp]
    simp [he, weight, forward, Equiv.piUnique, uniqueElim]
  | succ n ih =>
    rw [sum_history_snoc]
    simp only [Fin.snoc_last, weight_snoc]
    have h : (∑ c : L (n+1), ∑ x : History L n,
        if c = b then weight L p K n x * K n (x (Fin.last n)) c else 0) =
        ∑ x : History L n, weight L p K n x * K n (x (Fin.last n)) b := by simp
    rw [h]
    unfold forward
    conv_rhs =>
      simp only [← ih, Finset.sum_mul]
      rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    simp only [ite_mul, zero_mul]
    simp

lemma forward_total (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hK₁ : ∀ i a, (∑ b, K i a b) = 1) (n : ℕ) :
    (∑ a, forward L p K n a) = ∑ a, p a := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [forward]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, hK₁, mul_one]
    exact ih

/-- Normalization and the exact terminal marginal of the product measure. -/
theorem product_law (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hp : ∀ a, 0 ≤ p a) (hp₁ : (∑ a, p a) = 1)
    (hK : ∀ i a b, 0 ≤ K i a b) (hK₁ : ∀ i a, (∑ b, K i a b) = 1) (n : ℕ) :
    (∀ x, 0 ≤ weight L p K n x) ∧ (∑ x, weight L p K n x) = 1 ∧
      ∀ b : L n, (∑ x : History L n, if x (Fin.last n) = b then weight L p K n x else 0) =
        forward L p K n b := by
  classical
  refine ⟨fun x => mul_nonneg (hp _) (Finset.prod_nonneg fun _ _ => hK _ _ _), ?_,
    terminal_marginal L p K n⟩
  have ht := forward_total L p K hK₁ n
  simp_rw [← terminal_marginal L p K n] at ht
  rw [Finset.sum_comm] at ht
  simpa [hp₁] using ht

/-- The product has its prescribed final adjacent-pair marginal, including
zero-probability states and transitions. -/
theorem last_pair (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (n : ℕ) (a : L n) (b : L (n+1)) :
    (∑ x : History L (n+1),
      if x (Fin.last n).castSucc = a ∧ x (Fin.last (n+1)) = b
      then weight L p K (n+1) x else 0) = forward L p K n a * K n a b := by
  classical
  rw [sum_history_snoc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, weight_snoc]
  rw [Finset.sum_comm]
  have hc (x : History L n) :
      (∑ c : L (n+1), if x (Fin.last n) = a ∧ c = b
        then weight L p K n x * K n (x (Fin.last n)) c else 0) =
      (if x (Fin.last n) = a then weight L p K n x else 0) * K n a b := by
    by_cases h : x (Fin.last n) = a <;> simp [h]
  simp only [hc, ← Finset.sum_mul, terminal_marginal]

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

/-- Transition obtained from a prescribed adjacent-pair marginal. A zero-mass
row is filled with the next marginal; the row is never visited. -/
noncomputable def couplingKernel (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (i : ℕ) (a : L i) (b : L (i+1)) : ℝ :=
  if μ i a = 0 then μ (i+1) b else J i a b / μ i a

noncomputable def historyPrefix (m n : ℕ) (h : m ≤ n) (x : History L n) : History L m :=
  fun i => x (i.castLE (Nat.succ_le_succ h))

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

lemma joint_zero_row (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (i : ℕ) (a : L i) (ha : μ i a = 0) (b : L (i+1)) : J i a b = 0 := by
  have hle : J i a b ≤ ∑ c, J i a c :=
    Finset.single_le_sum (fun c _ => hJ i a c) (Finset.mem_univ b)
  rw [hrow, ha] at hle
  exact le_antisymm hle (hJ i a b)

lemma couplingKernel_stochastic (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a) :
    (∀ i a b, 0 ≤ couplingKernel L μ J i a b) ∧
      ∀ i a, (∑ b, couplingKernel L μ J i a b) = 1 := by
  constructor
  · intro i a b
    unfold couplingKernel
    split
    · exact hμ _ _
    · exact div_nonneg (hJ _ _ _) (hμ _ _)
  · intro i a
    by_cases ha : μ i a = 0
    · simp [couplingKernel, ha, hμ₁]
    · simp [couplingKernel, ha, ← Finset.sum_div, hrow]

lemma couplingKernel_balance (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (i : ℕ) (a : L i) (b : L (i+1)) :
    μ i a * couplingKernel L μ J i a b = J i a b := by
  by_cases ha : μ i a = 0
  · simp [couplingKernel, ha, joint_zero_row L μ J hJ hrow i a ha b]
  · simp [couplingKernel, ha, field]

lemma coupling_forward (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (hcol : ∀ i b, (∑ a, J i a b) = μ (i+1) b) :
    ∀ n a, forward L (μ 0) (couplingKernel L μ J) n a = μ n a := by
  intro n
  induction n with
  | zero => intro a; rfl
  | succ n ih =>
    intro b
    simp only [forward, ih, couplingKernel_balance L μ J hJ hrow]
    exact hcol n b

lemma prefix_snoc
    (L : ℕ → Type treewidthLevel1) [(i : ℕ) → Fintype (L i)]
    {m n : ℕ} (h : m ≤ n) (x : History L n) (b : L (n+1)) :
    historyPrefix L m (n+1) (h.trans (Nat.le_succ n)) (Fin.snoc x b) = historyPrefix L m n h x := by
  funext i
  change (@Fin.snoc (n+1) (fun j : Fin (n+2) => L j.val) x b)
    (Fin.castSucc (i.castLE (Nat.succ_le_succ h))) = _
  rw [Fin.snoc_castSucc]
  rfl

/-- Integrating out a stochastic suffix preserves the complete historyPrefix law,
not only one-coordinate marginals. -/
lemma prefix_expectation (p : L 0 → ℝ) (K : (i : ℕ) → L i → L (i+1) → ℝ)
    (hK₁ : ∀ i a, (∑ b, K i a b) = 1)
    (m n : ℕ) (hmn : m ≤ n) (f : History L m → ℝ) :
    (∑ x : History L n, weight L p K n x * f (historyPrefix L m n hmn x)) =
      ∑ x : History L m, weight L p K m x * f x := by
  induction n, hmn using Nat.le_induction with
  | base => rfl
  | succ n h ih =>
    rw [sum_history_snoc]
    simp only [weight_snoc, prefix_snoc L h]
    rw [Finset.sum_comm]
    have hs (x : History L n) :
        (∑ b : L (n+1), weight L p K n x * K n (x (Fin.last n)) b *
          f (historyPrefix L m n h x)) = weight L p K n x * f (historyPrefix L m n h x) := by
      simp_rw [mul_assoc, mul_comm (K n (x (Fin.last n)) _), ← mul_assoc]
      rw [← Finset.mul_sum, hK₁, mul_one]
    simp only [hs]
    exact ih

end BoundedTreewidthL1.MarkovProduct

namespace BoundedTreewidthL1.MarkovProduct
attribute [local instance] Classical.decEq
variable (L : ℕ → Type*) [∀ i, Fintype (L i)]

theorem coupling_chain (μ : (i : ℕ) → L i → ℝ)
    (J : (i : ℕ) → L i → L (i+1) → ℝ)
    (hμ : ∀ i a, 0 ≤ μ i a) (hμ₁ : ∀ i, (∑ a, μ i a) = 1)
    (hJ : ∀ i a b, 0 ≤ J i a b)
    (hrow : ∀ i a, (∑ b, J i a b) = μ i a)
    (hcol : ∀ i b, (∑ a, J i a b) = μ (i+1) b) (n : ℕ) :
    (∀ x, 0 ≤ weight L (μ 0) (couplingKernel L μ J) n x) ∧
    (∑ x, weight L (μ 0) (couplingKernel L μ J) n x) = 1 ∧
    ∀ i : Fin n, ∀ a : L i.val, ∀ b : L (i.val+1),
      (∑ x : History L n,
        if x i.castSucc = a ∧ x i.succ = b
        then weight L (μ 0) (couplingKernel L μ J) n x else 0) = J i.val a b := by
  have hK := couplingKernel_stochastic L μ J hμ hμ₁ hJ hrow
  have hlaw := product_law L (μ 0) (couplingKernel L μ J) (hμ 0) (hμ₁ 0) hK.1 hK.2 n
  refine ⟨hlaw.1, hlaw.2.1, ?_⟩
  intro i a b
  let f : History L (i.val+1) → ℝ := fun x =>
    if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b then 1 else 0
  have he := prefix_expectation L (μ 0) (couplingKernel L μ J) hK.2
    (i.val+1) n i.isLt f
  have he' :
      (∑ x : History L n, if x i.castSucc = a ∧ x i.succ = b
        then weight L (μ 0) (couplingKernel L μ J) n x else 0) =
      ∑ x : History L (i.val+1),
        if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b
        then weight L (μ 0) (couplingKernel L μ J) (i.val+1) x else 0 := by
    change (∑ x : History L n, weight L (μ 0) (couplingKernel L μ J) n x *
      (if x i.castSucc = a ∧ x i.succ = b then 1 else 0)) =
      (∑ x : History L (i.val+1), weight L (μ 0) (couplingKernel L μ J) (i.val+1) x *
      (if x (Fin.last i.val).castSucc = a ∧ x (Fin.last (i.val+1)) = b then 1 else 0)) at he
    simpa only [mul_ite, mul_one, mul_zero] using he
  rw [he', last_pair, coupling_forward L μ J hJ hrow hcol]
  exact couplingKernel_balance L μ J hJ hrow i.val a b

end BoundedTreewidthL1.MarkovProduct

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ExpandedChain
open scoped BigOperators
open ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A : Type*} [Fintype A]

noncomputable def past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ) (f : A → ℝ) : ℕ → A → ℝ
  | 0 => f
  | n+1 => action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n)

lemma past_bounds (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ)
    (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) (n : ℕ) :
    ∀ a, 0 ≤ past μ Q f n a ∧ past μ Q f n a ≤ 1 := by
  induction n with
  | zero => exact hf
  | succ n ih => exact action_bounds (hQ n).symm _ ih

lemma sum_fiber_mul {B : Type*} [Fintype B] (k : A → B) (w : A → ℝ) (g : B → ℝ) :
    (∑ a, w a * g (k a)) = ∑ b, (∑ a, if k a = b then w a else 0) * g b := by
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ite_mul, zero_mul]
  simp

/-- Conditional past means in the actual finite product law, not an assumed
Markov response. This identity includes all zero-mass states. -/
lemma weighted_terminal (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f : A → ℝ) (n : ℕ) (b : A) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      if x (Fin.last n) = b then
        MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
      else 0) = μ n b * past μ Q f n b := by
  induction n generalizing b with
  | zero =>
    let e : A ≃ (Fin 1 → A) := (Equiv.piUnique (fun _ : Fin 1 => A)).symm
    rw [← e.sum_comp]
    simp [e, MarkovProduct.weight, past, Equiv.piUnique, uniqueElim]
  | succ n ih =>
    rw [MarkovProduct.sum_history_snoc (fun _ => A)]
    simp only [Fin.snoc_last, MarkovProduct.weight_snoc]
    have hzero (x : Fin (n+1) → A) (c : A) :
        @Fin.snoc (n+1) (fun _ : Fin (n+2) => A) x c 0 = x 0 := by
      exact @Fin.snoc_castSucc (n+1) (fun _ => A) c x 0
    simp only [hzero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    let w : (Fin (n+1) → A) → ℝ := fun x =>
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x * f (x 0)
    have he : (∑ x : Fin (n+1) → A,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
      MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b * f (x 0)) =
       ∑ a, μ n a * past μ Q f n a * MarkovProduct.couplingKernel (fun _ => A) μ Q n a b := by
      trans ∑ x, w x * MarkovProduct.couplingKernel (fun _ => A) μ Q n (x (Fin.last n)) b
      · apply Finset.sum_congr rfl
        intro x _
        dsimp [w]
        ring
      · rw [sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w
          (fun a => MarkovProduct.couplingKernel (fun _ => A) μ Q n a b)]
        apply Finset.sum_congr rfl
        intro a _
        rw [show (∑ x, if x (Fin.last n) = a then w x else 0) = μ n a * past μ Q f n a from ih a]
    rw [he]
    change _ = μ (n+1) b * action (μ (n+1)) (fun b a => Q n a b) (past μ Q f n) b
    rw [weighted_action (hQ n).symm]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_right_comm, MarkovProduct.couplingKernel_balance (fun _ => A) μ Q
      (fun n => (hQ n).nonneg) (fun n => (hQ n).row)]

/-- Separation of endpoint labels in the genuine product density is precisely
its conditional-predictor defect. The identity holds for all bounded or unbounded
real endpoint observables; bounds are needed only for the subsequent tests. -/
theorem endpoint_defect (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (n : ℕ) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ n) g (past μ Q f n) := by
  let w : (Fin (n+1) → A) → ℝ := MarkovProduct.weight (fun _ => A) (μ 0)
    (MarkovProduct.couplingKernel (fun _ => A) μ Q) n
  have hm (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x else 0) = μ n b := by
    exact (MarkovProduct.terminal_marginal (fun _ => A) (μ 0)
      (MarkovProduct.couplingKernel (fun _ => A) μ Q) n b).trans
        (MarkovProduct.coupling_forward (fun _ => A) μ Q
          (fun n => (hQ n).nonneg) (fun n => (hQ n).row) (fun n => (hQ n).col) n b)
  have hw (b : A) : (∑ x : Fin (n+1) → A, if x (Fin.last n) = b then w x * f (x 0) else 0) =
      μ n b * past μ Q f n b := weighted_terminal μ Q hQ f n b
  have he : (∑ x : Fin (n+1) → A, w x * f (x 0)) =
      ∑ b, μ n b * past μ Q f n b := by
    simpa only [mul_one, hw] using
      (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) (fun x => w x*f (x 0)) (fun _ => (1:ℝ)))
  have hg : (∑ x : Fin (n+1) → A, w x * g (x (Fin.last n))) = ∑ b, μ n b*g b := by
    simpa only [hm] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n)) w g)
  have hfg : (∑ x : Fin (n+1) → A, w x * f (x 0) * g (x (Fin.last n))) =
      ∑ b, μ n b * past μ Q f n b * g b := by
    simpa only [hw] using (sum_fiber_mul (fun x : Fin (n+1) → A => x (Fin.last n))
      (fun x => w x*f (x 0)) g)
  change (∑ x, w x * _) = _
  calc
    _ = (∑ x, w x*f (x 0)) + (∑ x, w x*g (x (Fin.last n))) -
        2*(∑ x, w x*f (x 0)*g (x (Fin.last n))) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = _ := by
      rw [he,hg,hfg]
      unfold defect
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro b _
      ring

lemma response_past (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) :
    defect (μ t) (response μ Q t n g) (past μ Q f t) =
      defect (μ (t+n)) g (past μ Q f (t+n)) := by
  induction n generalizing t with
  | zero => simp only [response, Nat.add_zero]
  | succ n ih =>
    change defect (μ t) (action (μ t) (Q t) (response μ Q (t+1) n g)) (past μ Q f t) = _
    rw [transfer_defect (hQ t)]
    change defect (μ (t+1)) (response μ Q (t+1) n g) (past μ Q f (t+1)) = _
    rw [ih, show (t+1)+n = t+(n+1) by omega]

/-- One may test at ANY interior location: past and future are the honest
conditional responses of the already constructed product law. -/
theorem endpoint_defect_at (μ : ℕ → A → ℝ) (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n, IsCoupling (μ n) (μ (n+1)) (Q n)) (f g : A → ℝ) (t n : ℕ) (ht : t ≤ n) :
    (∑ x : MarkovProduct.History (fun _ => A) n,
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x *
        (f (x 0) + g (x (Fin.last n)) - 2*f (x 0)*g (x (Fin.last n)))) =
      defect (μ t) (response μ Q t (n-t) g) (past μ Q f t) := by
  rw [endpoint_defect μ Q hQ, response_past μ Q hQ, Nat.add_sub_of_le ht]
end BoundedTreewidthL1.ExpandedChain

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

/-- Local version: the arbitrary past of the path is immaterial. Only the true
reserved suffix edges are prescribed. -/
theorem response_restrict_local (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (t n : ℕ) (r : ι) (G : V → ℝ)
    (hQ : ∀ s, t ≤ s → s < t+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+n → F s r = G)
    (hkeep : ∀ s, t ≤ s → s < t+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M G) :
    response (fun s => weight M (F s)) Q t n
      (fun b => if label b z then 1 else 0) (lift M G r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M G)
        ((bags P t n).map (OrderedReservation.traceRank M G))
        (OrderedSweepFlow.labelReal (fun b => b.val z)) a := by
  induction n generalizing t a with
  | zero => rfl
  | succ n ih =>
    have ht : F t r = G := hfixed t le_rfl (by omega)
    subst G
    have hk := hkeep t le_rfl (by omega)
    change action (weight M (F t)) (Q t)
      (response (fun s => weight M (F s)) Q (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) = _
    rw [hQ t le_rfl (by omega)]
    unfold kernels
    rw [edge_restrict M (F t) (F (t+1)) (P t) (P (t+1)) (fresh₁ t) (fresh₂ t) r (C t)
      hk.2.1 hk.2.2 hk.1 (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))]
    rw [bags_succ, List.map_cons, OrderedSweepFlow.execute]
    congr 1
    funext b
    apply ih (t+1)
    · intro s hs hs'; exact hQ s (by omega) (by omega)
    · intro s hs hs'; exact hret s (by omega) (by omega)
    · intro s hs hs'; exact htrace s (by omega) (by omega)
    · intro s hs hs'; exact hfixed s (by omega) (by omega)
    · intro s hs hs'; exact hkeep s (by omega) (by omega)

lemma ordered_mean
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι]
    (M : ℝ) (_ : 0 ≤ M) (G : V → ℝ)
    (hG : ∀ v, -M ≤ G v ∧ G v ≤ M) (r : ι) (z : V)
    (bags : List (Finset V)) (f : State ι V → ℝ)
    (hres : ∀ a : OrderedReservation.Carrier M G, f (lift M G r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M G)
        (bags.map (OrderedReservation.traceRank M G))
        (OrderedSweepFlow.labelReal (fun a => a.val z)) a) :
    (∑ ω : V → Bool, (sweep M G).real {ω}/2 * f (r,false,ω)) = (G z+M)/2 := by
  have he := OrderedReservation.sum_carrier M G (fun ω => f (r,false,ω))
  have he' : (∑ a : OrderedReservation.Carrier M G,
      OrderedReservation.weight M G a * f (lift M G r a)) =
      ∑ ω : V → Bool, (sweep M G).real {ω}*f (r,false,ω) := he
  have hr := congrArg (fun h : OrderedReservation.Carrier M G → ℝ =>
      ∑ a, OrderedReservation.weight M G a * h a) (funext hres)
  rw [he'] at hr
  change _ = OrderedSweepFlow.total (OrderedReservation.weight M G)
    (OrderedSweepFlow.execute (OrderedReservation.weight M G)
      (bags.map (OrderedReservation.traceRank M G))
      (OrderedSweepFlow.labelReal (fun a => a.val z))) at hr
  rw [OrderedSweepFlow.execute_total _ (OrderedReservation.weight_pos M G),
    OrderedReservation.label_mean M G z (hG z)] at hr
  calc
    _ = (∑ ω : V → Bool, (sweep M G).real {ω}*f (r,false,ω))/2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro ω _
      ring
    _ = _ := by rw [hr]
end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ReservedSuffix
open ExpandedParticleLaw ReservationCoupling ReservedKernel
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

lemma incoming_response_restrict (M : ℝ) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ) (t n : ℕ) (r : ι)
    (hQ : ∀ s, t+1 ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hr : r ∈ C t)
    (hkeep : ∀ s, t+1 ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (z : V) (a : OrderedReservation.Carrier M (F t r)) :
    action (weight M (F t)) (incoming M (F t) (F (t+1)) (P (t+1)) (C t))
      (response (fun s => weight M (F s)) Q (t+1) n
        (fun b => if label b z then 1 else 0)) (lift M (F t r) r a) =
      OrderedSweepFlow.execute (OrderedReservation.weight M (F t r))
        ((bags P (t+1) n).map (OrderedReservation.traceRank M (F t r)))
        (OrderedSweepFlow.labelReal (fun b => b.val z)) a := by
  rw [incoming_action_retained M (F t) (F (t+1)) (P (t+1)) (C t)
    (hret t le_rfl (by omega)) (htrace t le_rfl (by omega)) _ hr
    (ne_of_gt (div_pos a.property (by norm_num)))]
  apply response_restrict_local M F P fresh₁ fresh₂ C Q (t+1) n r (F t r) hQ
  · intro s hs hs'; exact hret s (by omega) hs'
  · intro s hs hs'; exact htrace s (by omega) hs'
  · intro s hs hs'; exact hfixed s (by omega) hs'
  · exact hkeep
end BoundedTreewidthL1.ReservedSuffix

namespace BoundedTreewidthL1.ExpandedPathTests
open ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix ExpandedChain
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι]

noncomputable def distance (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ) (n : ℕ) (y z : V) : ℝ :=
  ∑ x : Fin (n+1) → State ι V,
    MarkovProduct.weight (fun _ => State ι V) (weight M (F 0))
      (MarkovProduct.couplingKernel (fun _ => State ι V) (fun s => weight M (F s)) Q) n x *
      (if label (x 0) y = label (x (Fin.last n)) z then 0 else 1)

lemma distance_at (M : ℝ) (F : ℕ → ι → V → ℝ)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (y z : V) :
    distance M F Q (t+(n+1)) y z =
      defect (weight M (F t)) (action (weight M (F t)) (Q t)
        (response (fun s => weight M (F s)) Q (t+1) n (fun b => if label b z then 1 else 0)))
        (past (fun s => weight M (F s)) Q (fun b => if label b y then 1 else 0) t) := by
  have he := endpoint_defect_at (fun s => weight M (F s)) Q hQ
    (fun b => if label b y then 1 else 0) (fun b => if label b z then 1 else 0)
    t (t+(n+1)) (by omega)
  rw [Nat.add_sub_cancel_left, response] at he
  rw [← he]
  unfold distance
  apply Finset.sum_congr rfl
  intro x _
  cases hy : label (x 0) y <;> cases hz : label (x (Fin.last (t+(n+1)))) z <;> norm_num [hy,hz]

/-- Height test for the ACTUAL arbitrarily prefixed product path. All suffix
transport and both past/future responses are derived from its couplings. -/
theorem height_test (M : ℝ) (hM : 0 ≤ M) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (r : ι)
    (hEq : ∀ s, t ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hkeep : ∀ s, t ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (hF : ∀ v, -M ≤ F t r v ∧ F t r v ≤ M) (y z : V)
    (ε : ℝ) (hlo : ε ≤ F t r z + M) (hhi : ε ≤ M-F t r z)
    (hgap : ∀ v ∈ P t, ε ≤ |F t r z-F t r v|) :
    ε/2 ≤ distance M F Q (t+(n+1)) y z := by
  rw [distance_at M F Q hQ t n y z, hEq t le_rfl (by omega)]
  unfold kernels edge
  rw [action_compose]
  have hb (v : V) (a : State ι V) : 0 ≤ (if label a v then (1:ℝ) else 0) ∧
      (if label a v then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hin : IsCoupling (weight M (F t)) (weight M (F (t+1)))
      (incoming M (F t) (F (t+1)) (P (t+1)) (C t)) := by
    obtain ⟨hn,hr,hc,_,_⟩ := incoming_coupling M (F t) (F (t+1)) (P (t+1)) (C t)
      (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))
    exact ⟨hn,hr,hc⟩
  have hk := hkeep t le_rfl (by omega)
  apply ReservedTests.height_test M hM (F t) (P t) (fresh₁ t) (fresh₂ t) r
    hk.2.1 hk.2.2 hF z (bags P (t+1) n)
  · exact action_bounds hin _ (response_bounds _ Q hQ (t+1) n _ (hb z))
  · exact past_bounds _ Q hQ _ (hb y) t
  · intro a
    apply incoming_response_restrict M F P fresh₁ fresh₂ C Q t n r
      (fun s hs hs' => hEq s (by omega) hs') hret htrace hfixed hk.1
      (fun s hs hs' => hkeep s (by omega) hs') z a
  · exact hlo
  · exact hhi
  · exact hgap
/-- Fresh-pair test on the actual product law with an arbitrary prefix. -/
theorem launch_test (M : ℝ) (hM : 0 ≤ M) (F : ℕ → ι → V → ℝ) (P : ℕ → Finset V)
    (fresh₁ fresh₂ : ℕ → ι) (C : ℕ → Finset ι)
    (Q : ℕ → State ι V → State ι V → ℝ)
    (hQ : ∀ s, IsCoupling (weight M (F s)) (weight M (F (s+1))) (Q s))
    (t n : ℕ) (hij : fresh₁ t ≠ fresh₂ t)
    (hbag : ∀ v ∈ P t, F t (fresh₁ t) v = F t (fresh₂ t) v)
    (hEq : ∀ s, t ≤ s → s < t+1+n → Q s = kernels M F P fresh₁ fresh₂ C s)
    (hret : ∀ s, t ≤ s → s < t+1+n → ∀ r ∈ C s, F s r = F (s+1) r)
    (htrace : ∀ s, t ≤ s → s < t+1+n →
      particleTrace M (F s) (P (s+1)) = particleTrace M (F (s+1)) (P (s+1)))
    (hfixed : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι),
      ∀ s, t ≤ s → s ≤ t+1+n → F s r = F t r)
    (hinit : fresh₁ t ∈ C t ∧ fresh₂ t ∈ C t)
    (hkeep : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι),
      ∀ s, t+1 ≤ s → s < t+1+n → r ∈ C s ∧ r ≠ fresh₁ s ∧ r ≠ fresh₂ s)
    (hF : ∀ r ∈ ({fresh₁ t, fresh₂ t} : Finset ι), ∀ v, -M ≤ F t r v ∧ F t r v ≤ M)
    (y z : V) :
    |F t (fresh₁ t) z - F t (fresh₂ t) z|/2 ≤ distance M F Q (t+(n+1)) y z := by
  rw [distance_at M F Q hQ t n y z, hEq t le_rfl (by omega)]
  unfold kernels edge
  rw [action_compose]
  have hb (v : V) (a : State ι V) : 0 ≤ (if label a v then (1:ℝ) else 0) ∧
      (if label a v then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  have hin : IsCoupling (weight M (F t)) (weight M (F (t+1)))
      (incoming M (F t) (F (t+1)) (P (t+1)) (C t)) := by
    obtain ⟨hn,hr,hc,_,_⟩ := incoming_coupling M (F t) (F (t+1)) (P (t+1)) (C t)
      (hret t le_rfl (by omega)) (htrace t le_rfl (by omega))
    exact ⟨hn,hr,hc⟩
  have hm (r : ι) (hr : r ∈ ({fresh₁ t, fresh₂ t} : Finset ι)) (hc : r ∈ C t) :
      (∑ ω : V → Bool, weight M (F t) (r,false,ω) *
        action (weight M (F t)) (incoming M (F t) (F (t+1)) (P (t+1)) (C t))
          (response (fun s => weight M (F s)) Q (t+1) n
            (fun b => if label b z then 1 else 0)) (r,false,ω)) = (F t r z+M)/2 := by
    apply ordered_mean M hM (F t r) (hF r hr) r z (bags P (t+1) n)
    intro a
    exact incoming_response_restrict M F P fresh₁ fresh₂ C Q t n r
      (fun s hs hs' => hEq s (by omega) hs') hret htrace (hfixed r hr) hc (hkeep r hr) z a
  apply ReservedTests.launch_test M (F t) (P t) (fresh₁ t) (fresh₂ t) hij hbag z
  · exact action_bounds hin _ (response_bounds _ Q hQ (t+1) n _ (hb z))
  · exact past_bounds _ Q hQ _ (hb y) t
  · exact hm _ (by simp) hinit.1
  · exact hm _ (by simp) hinit.2
end BoundedTreewidthL1.ExpandedPathTests

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ExpandedTree
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I A : Type*} [Fintype I] [Fintype A]

noncomputable def marginalLaw (M : ℝ) (μ : I → A → ℝ) : I → A → ℝ := fun i a => μ i a/M
noncomputable def jointLaw (M : ℝ) (J : I → I → A → A → ℝ) := fun i j a b => J i j a b/M
lemma jointLaw_symm
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    (M : ℝ) (J : I → I → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : I => A) J) :
    TreeMarkov.Symmetric (fun _ : I => A) (jointLaw M J) := by
  intro i j a b
  unfold jointLaw
  rw [hs]
noncomputable def law (T : SimpleGraph I) (M : ℝ) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J) (x : I → A) : ℝ :=
  M * TreeMarkov.density (fun _ : I => A) T (marginalLaw M μ)
    (TreeMarkov.interaction (fun _ : I => A) (marginalLaw M μ) (jointLaw M J))
    (TreeMarkov.interaction_symmetric (fun _ : I => A) (marginalLaw M μ) (jointLaw M J) (jointLaw_symm M J hs)) x

lemma normalized (T : SimpleGraph I) (M : ℝ) (hM : 0 < M) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a) :
    TreeMarkov.Normalized (fun _ : I => A) T (marginalLaw M μ)
      (TreeMarkov.interaction (fun _ : I => A) (marginalLaw M μ) (jointLaw M J)) := by
  apply TreeMarkov.interaction_normalized
  · intro i a
    exact div_nonneg (hμ i a) hM.le
  · intro i
    simp only [marginalLaw, ← Finset.sum_div, hmass i, div_self (ne_of_gt hM)]
  · exact jointLaw_symm M J hs
  · intro i j hij a b
    exact div_nonneg (hJ i j hij a b) hM.le
  · intro i j hij a
    simp only [jointLaw, marginalLaw, ← Finset.sum_div, hrow i j hij a]

/-- The expanded-state law is an actual finite tree law of the original common
mass. All local state marginals are as prescribed; no gluing existence is assumed. -/
theorem law_marginals (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a) :
    (∀ x, 0 ≤ law T M μ J hs x) ∧ (∑ x, law T M μ J hs x) = M ∧
      ∀ i a, (∑ x : I → A, if x i = a then law T M μ J hs x else 0) = μ i a := by
  let ν := marginalLaw M μ
  let R := TreeMarkov.interaction (fun _ : I => A) ν (jointLaw M J)
  let hR := TreeMarkov.interaction_symmetric (fun _ : I => A) ν (jointLaw M J) (jointLaw_symm M J hs)
  have hn := normalized T M hM μ J hs hμ hmass hJ hrow
  obtain ⟨hw,ht,hm⟩ := TreeMarkov.tree_density (fun _ : I => A) T hT ν R hR hn
  refine ⟨fun x => mul_nonneg hM.le (hw x), ?_, ?_⟩
  · simp only [law, ← Finset.mul_sum]
    change M * (∑ x, TreeMarkov.density (fun _ : I => A) T ν R hR x) = M
    rw [ht,mul_one]
  · intro i a
    have he : (∑ x : I → A, if x i = a then law T M μ J hs x else 0) =
        M * (∑ x : I → A, if x i = a then TreeMarkov.density (fun _ : I => A) T ν R hR x else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp [law,ν,R]
    rw [he,hm]
    exact mul_div_cancel₀ (μ i a) (ne_of_gt hM)

lemma path_expectation (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → ∀ a b, 0 ≤ J i j a b)
    (hrow : ∀ i j, T.Adj i j → ∀ a, ∑ b, J i j a b = μ i a)
    {K : Type*} [Fintype K] (e : K ↪ I) (hc : (T.comap e).Connected) (f : (K → A) → ℝ) :
    (∑ x : I → A, law T M μ J hs x * f (x ∘ e)) =
      ∑ x : K → A, law (T.comap e) M (fun i => μ (e i)) (fun i j => J (e i) (e j))
        (fun i j => hs (e i) (e j)) x * f x := by
  unfold law
  simp_rw [mul_assoc, ← Finset.mul_sum]
  congr 1
  exact TreeMarkov.expectation_comap (fun _ : I => A) T hT (marginalLaw M μ) _ _
    (normalized T M hM μ J hs hμ hmass hJ hrow) e hc f

lemma support_joint (T : SimpleGraph I) (M : ℝ) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (x : I → A) (hx : law T M μ J hs x ≠ 0) (i j : I) (hij : T.Adj i j) :
    J i j (x i) (x j) ≠ 0 := by
  have hp := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx).2).2
  have he : s(i,j) ∈ T.edgeFinset := by simpa using hij
  have hz := Finset.prod_ne_zero_iff.mp hp _ he
  change J i j (x i) (x j) / M / ((μ i (x i)/M)*(μ j (x j)/M)) ≠ 0 at hz
  exact (div_ne_zero_iff.mp (div_ne_zero_iff.mp hz).1).1

/-- Gluing of GLOBAL state labels along the running-intersection bags. -/
noncomputable def assemble {V : Type*} (B : I → Set V) (hcover : ∀ v, ∃ i, v ∈ B i)
    (label : A → V → Bool) (x : I → A) : V → Bool :=
  fun v => label (x (Classical.choose (hcover v))) v

lemma assembled_label
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    {V : Type*} (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (label : A → V → Bool) (x : I → A)
    (hx : ∀ i j, T.Adj i j → ∀ v, v ∈ B i → v ∈ B j → label (x i) v = label (x j) v)
    (i : I) (v : V) (hv : v ∈ B i) : assemble B hcover label x v = label (x i) v := by
  obtain ⟨p⟩ := hrun v ⟨Classical.choose (hcover v),Classical.choose_spec (hcover v)⟩ ⟨i,hv⟩
  have hc : ∀ {a b : {i | v ∈ B i}} (q : (T.induce {i | v ∈ B i}).Walk a b),
      label (x a) v = label (x b) v := by
    intro a b q
    induction q with
    | nil => rfl
    | @cons a b c hab q ih => exact (hx a b hab v a.2 b.2).trans ih
  exact hc p

lemma law_labels {V : Type*} (T : SimpleGraph I) (B : I → Set V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (M : ℝ) (μ : I → A → ℝ) (J : I → I → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : I => A) J) (label : A → V → Bool)
    (hcomp : ∀ i j, T.Adj i j → ∀ a b, J i j a b ≠ 0 →
      ∀ v, v ∈ B i → v ∈ B j → label a v = label b v)
    (x : I → A) (hx : law T M μ J hs x ≠ 0) (i : I) (v : V) (hv : v ∈ B i) :
    assemble B hcover label x v = label (x i) v := by
  exact assembled_label T B hcover hrun label x
    (fun i j hij => hcomp i j hij (x i) (x j) (support_joint T M μ J hs x hx i j hij)) i v hv

end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1.ExpandedTree
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {A : Type*} [Fintype A]

/-- On every actual bag-tree path, the law is the genuine product of the
prescribed expanded couplings, even though their common mass is not one. -/
theorem law_path_product (M : ℝ) (hM : 0 < M) (μ : ℕ → A → ℝ)
    (Q : ℕ → A → A → ℝ)
    (hQ : ∀ n a b, 0 ≤ Q n a b)
    (_ : ∀ n a, (∑ b, Q n a b) = μ n a)
    (hcol : ∀ n b, (∑ a, Q n a b) = μ (n+1) b)
    (n : ℕ) (J : Fin (n+1) → Fin (n+1) → A → A → ℝ)
    (hs : TreeMarkov.Symmetric (fun _ : Fin (n+1) => A) J)
    (hJ : ∀ (i : Fin n) a b, J i.castSucc i.succ a b = Q i.val a b) (x : Fin (n+1) → A) :
    law (SimpleGraph.pathGraph (n+1)) M (fun i => μ i.val) J hs x =
      MarkovProduct.weight (fun _ => A) (μ 0) (MarkovProduct.couplingKernel (fun _ => A) μ Q) n x := by
  unfold law
  rw [TreeMarkov.path_density]
  let m : Fin (n+1) → ℝ := fun i => μ i.val (x i)/M
  let q : Fin n → ℝ := fun i =>
    TreeMarkov.interaction (fun _ : Fin (n+1) => A) (marginalLaw M (fun i => μ i.val))
      (jointLaw M J) i.castSucc i.succ (x i.castSucc) (x i.succ)
  let k : Fin n → ℝ := fun i => MarkovProduct.couplingKernel (fun _ => A) μ Q i.val
    (x i.castSucc) (x i.succ)
  have hk (i : Fin n) (hi : m i.castSucc ≠ 0) : k i = m i.succ * q i := by
    have hi' : μ i.val (x i.castSucc) ≠ 0 := by
      intro hz
      exact hi (by simp [m,hz])
    by_cases hj : μ (i.val+1) (x i.succ) = 0
    · have hz : Q i.val (x i.castSucc) (x i.succ) = 0 := by
        have hh := hcol i.val (x i.succ)
        rw [hj] at hh
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hQ i.val a (x i.succ))).mp hh _ (Finset.mem_univ _)
      simp [k, MarkovProduct.couplingKernel,hi',hz,m,hj]
    · dsimp [k,m,q]
      simp only [MarkovProduct.couplingKernel, hi', ↓reduceIte, TreeMarkov.interaction,
        marginalLaw, jointLaw, hJ, Fin.val_castSucc, Fin.val_succ]
      field_simp [hi',hj,ne_of_gt hM]
  have he := TreeMarkov.product_factorization n m q k hk
  change M * ((∏ i, m i)*(∏ i, q i)) = _
  rw [he]
  unfold MarkovProduct.weight
  change M * ((μ 0 (x 0)/M) * ∏ i, k i) = μ 0 (x 0) * ∏ i, k i
  rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hM)]
end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1
open MeasureTheory
open scoped ENNReal

theorem averaged_cut_realization {Ω V A : Type*} [MeasurableSpace Ω] [Fintype A]
    (μ : Measure Ω) (w : Ω → A → ℝ) (cut : A → V → Bool)
    (hw : ∀ ω a, 0 ≤ w ω a)
    (hint : ∀ a, Integrable (fun ω => w ω a) μ) :
    ∃ n : ℕ, ∃ F : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      ∀ u v, ‖F u - F v‖ = ∫ ω, cutDistance (w ω) cut u v ∂μ := by
  let W : A → ℝ := fun a => ∫ ω, w ω a ∂μ
  have hW : ∀ a, 0 ≤ W a := fun a => integral_nonneg (fun ω => hw ω a)
  obtain ⟨n,F,hF⟩ := finite_cut_realization W cut hW
  refine ⟨n,F,?_⟩
  intro u v
  rw [hF]
  unfold cutDistance
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro a ha
    by_cases he : cut a u = cut a v <;> simp [he, W]
  · intro a ha
    by_cases he : cut a u = cut a v
    · simp only [he, ite_true]
      exact integrable_zero Ω ℝ μ
    · simpa only [he, ite_false] using hint a
end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ExpandedConstruction
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι I : Type*} [Fintype V] [Fintype ι] [Fintype I]

lemma weight_total (M : ℝ) (hM : 0 ≤ M) (F : ι → V → ℝ) :
    (∑ a : State ι V, weight M F a) = (Fintype.card ι : ℝ)*(2*M) := by
  have he (i : ι) : (∑ ω : V → Bool, (sweep M (F i)).real {ω}) = 2*M := by
    have h := OrderedReservation.total_weight M hM (F i)
    unfold OrderedSweepFlow.total at h
    rw [OrderedReservation.sum_carrier M (F i) (fun _ => 1)] at h
    simpa only [mul_one] using h
  simp only [Fintype.sum_prod_type, weight, ← Finset.sum_div, he]
  simp
  ; ring

lemma edge_label (M : ℝ) (F H : ι → V → ℝ) (P Q : Finset V) (i j : ι) (C : Finset ι)
    (hret : ∀ r ∈ C, F r = H r) (htrace : particleTrace M F Q = particleTrace M H Q)
    (a b : State ι V) (hab : edge M F H P Q i j C a b ≠ 0)
    (v : V) (hvP : v ∈ P) (hvQ : v ∈ Q) : label a v = label b v := by
  by_contra hne
  apply hab
  apply ExpandedParticleKernel.compose_trace (weight M F) (departure M F P i j)
    (incoming M F H Q C) (fun a => label a v) (fun a => label a v) (fun a => label a v)
  · intro a b hne
    apply (departure_coupling M F P i j).2.2.2.1 a b
    intro he
    exact hne (congrFun he ⟨v,hvP⟩)
  · intro a b hne
    apply (incoming_coupling M F H Q C hret htrace).2.2.2.1 a b
    intro he
    exact hne (congrFun he ⟨v,hvQ⟩)
  · exact hne

noncomputable def joints (parent : I → Option I) (M : ℝ) (F : I → ι → V → ℝ)
    (B : I → Finset V) (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (i j : I) (a b : State ι V) : ℝ :=
  if parent j = some i then edge M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j) a b
  else if parent i = some j then edge M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i) b a
  else 0

lemma joints_symmetric
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {I : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [Fintype I]
    (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι) :
    TreeMarkov.Symmetric (fun _ : I => State ι V) (joints parent M F B fresh₁ fresh₂ C) := by
  intro i j a b
  by_cases hij : parent j = some i
  · simp [joints,hij,hanti j i hij]
  · by_cases hji : parent i = some j <;> simp [joints,hij,hji]

lemma joints_eq
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} {I : Type treewidthLevel3} [Fintype V]
    [Fintype ι] [Fintype I]
    (parent : I → Option I) (M : ℝ) (F : I → ι → V → ℝ)
    (B : I → Finset V) (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (i j : I) (hp : parent j = some i) :
    joints parent M F B fresh₁ fresh₂ C i j =
      edge M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j) := by
  funext a b
  simp [joints,hp]

lemma joints_coupling (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i j : I) (hij : T.Adj i j) :
    IsCoupling (weight M (F i)) (weight M (F j)) (joints parent M F B fresh₁ fresh₂ C i j) := by
  rcases horient i j hij with hji | hij
  · have he : joints parent M F B fresh₁ fresh₂ C i j =
        fun a b => edge M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i) b a := by
      funext a b
      simp [joints,hji,hanti i j hji]
    rw [he]
    exact (edge_coupling M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i)
      (hret j i hji) (htrace j i hji)).symm
  · rw [joints_eq parent M F B fresh₁ fresh₂ C i j hij]
    exact edge_coupling M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j)
      (hret i j hij) (htrace i j hij)

lemma joints_label (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i j : I) (hij : T.Adj i j) (a b : State ι V)
    (hab : joints parent M F B fresh₁ fresh₂ C i j a b ≠ 0)
    (v : V) (hvi : v ∈ B i) (hvj : v ∈ B j) : label a v = label b v := by
  rcases horient i j hij with hji | hij
  · have he := joints_symmetric parent hanti M F B fresh₁ fresh₂ C i j a b
    rw [he, joints_eq parent M F B fresh₁ fresh₂ C j i hji] at hab
    exact (edge_label M (F j) (F i) (B j) (B i) (fresh₁ j) (fresh₂ j) (C i)
      (hret j i hji) (htrace j i hji) b a hab v hvj hvi).symm
  · rw [joints_eq parent M F B fresh₁ fresh₂ C i j hij] at hab
    exact edge_label M (F i) (F j) (B i) (B j) (fresh₁ i) (fresh₂ i) (C j)
      (hret i j hij) (htrace i j hij) a b hab v hvi hvj
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.ExpandedConstruction
open MeasureTheory ExpandedParticleLaw ReservationCoupling ReservedKernel ReservedSuffix
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι I : Type*} [Fintype V] [Fintype ι] [Fintype I]

lemma weight_separation (M : ℝ) (F : ι → V → ℝ)
    (hF : ∀ i v, |F i v| ≤ M) (u v : V) :
    cutDistance (weight M F) label u v = ∑ i, |F i u-F i v| := by
  unfold cutDistance
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fintype.sum_prod_type]
  have he (b : Bool) : (∑ ω : V → Bool,
      if label (i,b,ω) u = label (i,b,ω) v then 0 else weight M F (i,b,ω)) =
      |F i u-F i v|/2 := by
    have hs := OrderedReservation.sum_event M (F i) (fun ω => ω u ≠ ω v)
    rw [← cutSeparation, sweep_separation M (F i) (hF i)] at hs
    rw [← hs, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro ω _
    cases b <;> cases hu : ω u <;> cases hv : ω v <;> simp [label,weight,hu,hv]
  simp_rw [he]
  simp
  ; ring

noncomputable def ensemble (T : SimpleGraph I) (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι) : (I → State ι V) → ℝ :=
  ExpandedTree.law T ((Fintype.card ι : ℝ)*(2*M)) (fun i => weight M (F i))
    (joints parent M F B fresh₁ fresh₂ C)
    (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)

lemma ensemble_data (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j)) :
    (∀ x, 0 ≤ ensemble T parent hanti M F B fresh₁ fresh₂ C x) ∧
    (∑ x, ensemble T parent hanti M F B fresh₁ fresh₂ C x) = (Fintype.card ι : ℝ)*(2*M) ∧
    ∀ i a, (∑ x, if x i = a then ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) =
      weight M (F i) a := by
  have hmass : 0 < (Fintype.card ι : ℝ)*(2*M) := by positivity
  obtain ⟨hn,ht,hm⟩ := ExpandedTree.law_marginals T hT _ hmass _ _
    (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)
    (fun i => weight_nonneg M (F i)) (fun i => weight_total M hM.le (F i))
    (fun i j hij => (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace i j hij).nonneg)
    (fun i j hij => (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace i j hij).row)
  refine ⟨hn,ht,?_⟩
  intro i a
  convert hm i a using 1
  congr 1
  funext x
  split_ifs <;> rfl

lemma ensemble_labels (T : SimpleGraph I) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (x : I → State ι V) (hx : ensemble T parent hanti M F B fresh₁ fresh₂ C x ≠ 0)
    (i : I) (v : V) (hv : v ∈ B i) :
    ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x v = label (x i) v := by
  exact ExpandedTree.law_labels T (fun i => (B i : Set V)) hcover hrun _ _ _ _ label
    (joints_label T parent horient hanti M F B fresh₁ fresh₂ C hret htrace) x hx i v hv

/-- Every bag has the exact particle metric, while the inter-bag coupling is
chosen to retain the sweep order of each currently reserved particle. -/
lemma ensemble_cobag (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (i : I) (hF : ∀ r v, |F i r v| ≤ M) (u v : V) (hu : u ∈ B i) (hv : v ∈ B i) :
    cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) u v =
      ∑ r, |F i r u-F i r v| := by
  rw [← weight_separation M (F i) hF u v]
  have hm := (ensemble_data T hT parent horient hanti M hM hι F B fresh₁ fresh₂ C hret htrace).2.2 i
  unfold cutDistance
  have he : (∑ x : I → State ι V,
      if ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x u =
          ExpandedTree.assemble (fun i => (B i : Set V)) hcover label x v then 0
      else ensemble T parent hanti M F B fresh₁ fresh₂ C x) =
      ∑ x : I → State ι V, ensemble T parent hanti M F B fresh₁ fresh₂ C x *
        (if label (x i) u = label (x i) v then 0 else 1) := by
    apply Finset.sum_congr rfl
    intro x _
    by_cases hz : ensemble T parent hanti M F B fresh₁ fresh₂ C x = 0
    · simp [hz]
    · rw [ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hz i u hu,
        ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hz i v hv]
      split_ifs <;> simp
  rw [he, ExpandedChain.sum_fiber_mul (fun x : I → State ι V => x i)
    (ensemble T parent hanti M F B fresh₁ fresh₂ C)
    (fun a => if label a u = label a v then 0 else 1)]
  apply Finset.sum_congr rfl
  intro a _
  have hh : (∑ x : I → State ι V, if x i = a then
      ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) = weight M (F i) a := by
    convert hm a using 1
  have hh' : (∑ x : I → State ι V, if x i = a then
      ensemble T parent hanti M F B fresh₁ fresh₂ C x else 0) *
      (if label a u = label a v then (0:ℝ) else 1) =
      (if label a u = label a v then 0 else weight M (F i) a) := by
    rw [hh]
    split_ifs <;> simp
  convert hh' using 1
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.ExpandedMeasurable
open MeasureTheory ExpandedParticleLaw ExpandedParticleKernel ExpandedConstruction ReservedSuffix
open scoped BigOperators
attribute [local instance] Classical.decEq Classical.propDecidable
variable {Ω V ι I : Type*} [MeasurableSpace Ω] [Fintype V] [Fintype ι] [Fintype I]

lemma selected {A : Type*} [Fintype A] [MeasurableSpace A] [MeasurableSingletonClass A]
    (f : Ω → A → ℝ) (a : Ω → A)
    (hf : ∀ b, Measurable (fun ω => f ω b)) (ha : Measurable a) :
    Measurable (fun ω => f ω (a ω)) := by
  have he : (fun ω => f ω (a ω)) = (fun ω => ∑ b, if a ω = b then f ω b else 0) := by
    funext ω
    simp
  rw [he]
  exact Finset.measurable_sum _ (fun b _ => (hf b).ite (measurableSet_eq_fun ha measurable_const) measurable_const)

lemma measurable_marginal {A C : Type*} [Fintype A]
    (f : A → C) (μ : Ω → A → ℝ) (hμ : ∀ a, Measurable (fun ω => μ ω a)) (c : C) :
    Measurable (fun ω => marginal f (μ ω) c) := by
  unfold marginal
  apply Finset.measurable_sum
  intro a _
  by_cases h : f a = c <;> simp only [h, ↓reduceIte]
  · exact hμ a
  · exact measurable_const

lemma measurable_glue {A B C : Type*} [Fintype A] [Fintype B]
    (f : A → C) (g : B → C) (μ : Ω → A → ℝ) (ν : Ω → B → ℝ)
    (hμ : ∀ a, Measurable (fun ω => μ ω a)) (hν : ∀ b, Measurable (fun ω => ν ω b)) (a : A) (b : B) :
    Measurable (fun ω => glueWeights f g (μ ω) (ν ω) a b) := by
  unfold glueWeights
  by_cases h : f a = g b <;> simp only [h, ↓reduceIte]
  · exact ((hμ a).mul (hν b)).div (measurable_marginal f μ hμ (g b))
  · exact measurable_const

lemma measurable_edge_fixed (M : ℝ) (F H : Ω → ι → V → ℝ)
    (hF : ∀ a, Measurable (fun ω => weight M (F ω) a))
    (hH : ∀ a, Measurable (fun ω => weight M (H ω) a))
    (P Q : Finset V) (i j : ι) (C : Finset ι) (a b : State ι V) :
    Measurable (fun ω => edge M (F ω) (H ω) P Q i j C a b) := by
  unfold edge compose
  apply Finset.measurable_sum
  intro c _
  exact ((measurable_glue _ _ _ _ hF hF a c).mul
    (measurable_glue _ _ _ _ hF hH c b)).div (hF c)

lemma measurable_edge [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (M : ℝ) (F H : Ω → ι → V → ℝ)
    (hF : ∀ a, Measurable (fun ω => weight M (F ω) a))
    (hH : ∀ a, Measurable (fun ω => weight M (H ω) a))
    (P Q : Finset V) (i j : Ω → ι) (C : Ω → Finset ι)
    (hi : Measurable i) (hj : Measurable j) (hC : Measurable C) (a b : State ι V) :
    Measurable (fun ω => edge M (F ω) (H ω) P Q (i ω) (j ω) (C ω) a b) := by
  exact selected (fun ω (c : ι × ι × Finset ι) => edge M (F ω) (H ω) P Q c.1 c.2.1 c.2.2 a b)
    (fun ω => (i ω,j ω,C ω)) (fun c => measurable_edge_fixed M F H hF hH P Q c.1 c.2.1 c.2.2 a b)
    (hi.prodMk (hj.prodMk hC))

lemma measurable_joints
    {Ω : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3}
    {I : Type treewidthLevel4} [MeasurableSpace Ω] [Fintype V] [Fintype ι] [Fintype I]
    [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (parent : I → Option I) (M : ℝ) (F : Ω → I → ι → V → ℝ) (B : I → Finset V)
    (hF : ∀ i a, Measurable (fun ω => weight M (F ω i) a))
    (fresh₁ fresh₂ : Ω → I → ι) (C : Ω → I → Finset ι)
    (h₁ : ∀ i, Measurable (fun ω => fresh₁ ω i)) (h₂ : ∀ i, Measurable (fun ω => fresh₂ ω i))
    (hC : ∀ i, Measurable (fun ω => C ω i)) (i j : I) (a b : State ι V) :
    Measurable (fun ω => joints parent M (F ω) B (fresh₁ ω) (fresh₂ ω) (C ω) i j a b) := by
  unfold joints
  split_ifs
  · exact measurable_edge M _ _ (hF i) (hF j) _ _ _ _ _ (h₁ i) (h₂ i) (hC j) a b
  · exact measurable_edge M _ _ (hF j) (hF i) _ _ _ _ _ (h₁ j) (h₂ j) (hC i) b a
  · exact measurable_const

lemma measurable_law {A : Type*} [Fintype A] (T : SimpleGraph I) (M : ℝ)
    (μ : Ω → I → A → ℝ) (J : Ω → I → I → A → A → ℝ)
    (hs : ∀ ω, TreeMarkov.Symmetric (fun _ : I => A) (J ω))
    (hμ : ∀ i a, Measurable (fun ω => μ ω i a))
    (hJ : ∀ i j a b, Measurable (fun ω => J ω i j a b)) (x : I → A) :
    Measurable (fun ω => ExpandedTree.law T M (μ ω) (J ω) (hs ω) x) := by
  unfold ExpandedTree.law TreeMarkov.density
  apply Measurable.const_mul
  apply Measurable.mul
  · exact Finset.measurable_prod _ (fun i _ => (hμ i (x i)).div_const M)
  · apply Finset.measurable_prod
    intro e _
    induction e using Sym2.ind with
    | _ i j =>
      simp only [TreeMarkov.edgeFactor_mk, TreeMarkov.interaction, ExpandedTree.jointLaw, ExpandedTree.marginalLaw]
      exact ((hJ i j (x i) (x j)).div_const M).div
        (((hμ i (x i)).div_const M).mul ((hμ j (x j)).div_const M))

/-- Measurability of the actual expanded tree law, allowing the reservation
indices and free pools to depend on all the previously sampled noise. -/
lemma measurable_ensemble [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (T : SimpleGraph I) (parent : I → Option I)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (F : Ω → I → ι → V → ℝ) (B : I → Finset V)
    (hF : ∀ i a, Measurable (fun ω => weight M (F ω i) a))
    (fresh₁ fresh₂ : Ω → I → ι) (C : Ω → I → Finset ι)
    (h₁ : ∀ i, Measurable (fun ω => fresh₁ ω i)) (h₂ : ∀ i, Measurable (fun ω => fresh₂ ω i))
    (hC : ∀ i, Measurable (fun ω => C ω i)) (x : I → State ι V) :
    Measurable (fun ω => ensemble T parent hanti M (F ω) B (fresh₁ ω) (fresh₂ ω) (C ω) x) := by
  exact measurable_law T _ _ _ _ hF (measurable_joints parent M F B hF fresh₁ fresh₂ C h₁ h₂ hC) x
end BoundedTreewidthL1.ExpandedMeasurable

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.ParticleBatch
open ParticleSchedule
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]

def pairIndex (p : J → ι × ι) (a : J) (b : Bool) : ι := if b then (p a).2 else (p a).1

def PairUnique (C : Finset J) (p : J → ι × ι) : Prop :=
  ∀ a ∈ C, ∀ b ∈ C, ∀ u v : Bool, pairIndex p a u = pairIndex p b v → a = b ∧ u = v

lemma pairIndex_mem {C : Finset J} (p : J → ι × ι) {a : J} (ha : a ∈ C) (b : Bool) :
    pairIndex p a b ∈ usedPairs C p := by
  cases b
  · exact first_mem_used ha p
  · exact second_mem_used ha p

lemma PairUnique.mono
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι]
    {C D : Finset J} {p : J → ι × ι} (h : PairUnique D p) (hs : C ⊆ D) :
    PairUnique C p := fun a ha b hb u v => h a (hs ha) b (hs hb) u v

lemma PairUnique.empty
    {ι : Type treewidthLevel1} {J : Type treewidthLevel2} [Fintype ι] [Nonempty ι]
    (p : J → ι × ι) : PairUnique ∅ p := by
  intro a ha
  simp at ha

lemma PairUnique.update {C : Finset J} {p : J → ι × ι} (hp : PairUnique C p)
    (a : J) (ha : a ∉ C) (z : ι × ι)
    (hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2) :
    PairUnique (insert a C) (Function.update p a z) := by
  intro b hb c hc u v he
  have hnew (w : Bool) : pairIndex (Function.update p a z) a w ∉ usedPairs C p := by
    cases w
    · simpa [pairIndex] using hz.1
    · simpa [pairIndex] using hz.2.1
  rcases Finset.mem_insert.mp hb with hba | hb
  · subst b
    rcases Finset.mem_insert.mp hc with hca | hc
    · subst c
      refine ⟨rfl,?_⟩
      cases u <;> cases v <;> simp_all [pairIndex]
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      have he' : pairIndex (Function.update p a z) a u = pairIndex p c v := by
        simpa [pairIndex,Function.update_of_ne hca] using he
      exact False.elim (hnew u (he'.symm ▸ pairIndex_mem p hc v))
  · have hba : b ≠ a := fun h => ha (h ▸ hb)
    rcases Finset.mem_insert.mp hc with hca | hc
    · subst c
      have he' : pairIndex p b u = pairIndex (Function.update p a z) a v := by
        simpa [pairIndex,Function.update_of_ne hba] using he
      exact False.elim (hnew v (he' ▸ pairIndex_mem p hb u))
    · have hca : c ≠ a := fun h => ha (h ▸ hc)
      apply hp b hb c hc u v
      simpa [pairIndex,Function.update_of_ne hba,Function.update_of_ne hca] using he

lemma launchBatch_unique (k q : ℕ) (hN : Fintype.card ι = 2*q + k.factorial+2)
    (P : Finset V) (hP : P.card ≤ k) (l : List J) (C : Finset J)
    (hl : l.Nodup) (hfresh : ∀ a ∈ l, a ∉ C) (hcount : (C ∪ l.toFinset).card ≤ q)
    (F : ι → V → ℝ) (p : J → ι × ι) (hp : PairUnique C p) (g : J → V → ℝ) :
    PairUnique (C ∪ l.toFinset) (launchBatch P l C F p g).2 := by
  induction l generalizing C F p with
  | nil => simpa [launchBatch] using hp
  | cons a l ih =>
    have haC : a ∉ C := hfresh a (by simp)
    let z := pickPair P (usedPairs C p) F
    let F₁ := functionPairUpdate F z.1 z.2 (g a)
    let p₁ := Function.update p a z
    have hC : C.card ≤ q := (Finset.card_le_card Finset.subset_union_left).trans hcount
    have hz : z.1 ∉ usedPairs C p ∧ z.2 ∉ usedPairs C p ∧ z.1 ≠ z.2 ∧
        CommonWeakOrder P (F z.1) (F z.2) :=
      pickPair_spec k q hN P hP _ ((usedPairs_card C p).trans (by omega)) F
    have hnewCount : (insert a C ∪ l.toFinset).card ≤ q := by
      simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert] using hcount
    have hnewFresh : ∀ b ∈ l, b ∉ insert a C := by
      intro b hb h
      rcases Finset.mem_insert.mp h with h | h
      · subst b
        exact (List.nodup_cons.mp hl).1 hb
      · exact hfresh b (by simp [hb]) h
    have hn : PairUnique (insert a C) p₁ := hp.update a haC z ⟨hz.1,hz.2.1,hz.2.2.1⟩
    have hres := ih (insert a C) hl.of_cons hnewFresh hnewCount F₁ p₁ hn
    simpa only [List.toFinset_cons, Finset.insert_union, Finset.union_insert, launchBatch] using hres

end BoundedTreewidthL1.ParticleBatch

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V ι I J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]

/-- All simultaneously reserved pairs are disjoint in the ACTUAL depth-recursive
branching preparation. In particular every strictly older active reservation
avoids both indices reserved by the fresh own-bag launch. -/
theorem state_unique (R : RootedForest I) (bag : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (k q : ℕ) (hN : Fintype.card ι = 2*q+k.factorial+2)
    (hbag : ∀ i, (bag i).card ≤ k) (hA : ∀ i, (A i).card ≤ q) :
    ∀ i, PairUnique (A i) (state (ι := ι) R bag A g i).2 := by
  intro i
  induction hi : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    let S := state (ι := ι) R bag A g
    have hp : PairUnique (retained R A i) ((R.parent i).elim seed S).2 := by
      cases he : R.parent i with
      | none => simp [retained,he,PairUnique.empty]
      | some p =>
        have hu := ih (R.depth p) (by have := R.decreases i p he; omega) p rfl
        simpa only [retained,he,Option.elim_some] using hu.mono Finset.inter_subset_right
    have hb := batch_data R A i (hA i)
    have hr := launchBatch_unique k q hN (bag i) (hbag i) (fresh R A i).toList (retained R A i)
      hb.1 hb.2.1 hb.2.2 ((R.parent i).elim seed S).1 ((R.parent i).elim seed S).2 hp (g i)
    rw [state_eq]
    simpa only [step,Finset.toList_toFinset,fresh,Finset.union_sdiff_of_subset (retained_subset R A i)] using hr
end BoundedTreewidthL1.AnchorTreeParticles

namespace BoundedTreewidthL1.ExpandedAnchor
open MeasureTheory AnchorTreeParticles ParticleBatch ExpandedParticleLaw ExpandedConstruction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I ι Ω : Type*} [Fintype V] [Fintype I] [Fintype ι] [Nonempty ι]
  [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

lemma parent_antisymm
    {I : Type treewidthLevel1} [Fintype I]
    (R : RootedForest I) (i j : I)
    (h : R.parent i = some j) : R.parent j ≠ some i := by
  intro h'
  have := R.decreases i j h
  have := R.decreases j i h'
  omega

noncomputable def law (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (A : I → Finset I) (g : I → I → V → ℝ) (M : ℝ) :
    (I → State ι V) → ℝ :=
  let R := RootedTree.forest T hT root
  let S := state (ι := ι) R B A g
  ensemble T R.parent (parent_antisymm R) M (fun i => (S i).1) B
    (fun i => ((S i).2 i).1) (fun i => ((S i).2 i).2)
    (fun i => usedPairs (retained R A i) (S i).2)

lemma retained_functions
    {V : Type treewidthLevel1} {I : Type treewidthLevel2} {ι : Type treewidthLevel3} [Fintype V]
    [Fintype I] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : RootedForest I) (A : I → Finset I)
    (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2) :
    ∀ p i, R.parent i = some p → ∀ r ∈ usedPairs (retained R A i) (S i).2,
      (S p).1 r = (S i).1 r := by
  intro p i hpi r hr
  simp only [usedPairs,retained,hpi,Option.elim_some,Finset.mem_union,Finset.mem_image] at hr
  rcases hr with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
  · obtain ⟨he,hf,_⟩ := hpairs i p hpi a ha
    simpa only [he] using hf.symm
  · obtain ⟨he,_,hf⟩ := hpairs i p hpi a ha
    simpa only [he] using hf.symm

lemma measurable_law (T : SimpleGraph I) (hT : T.IsTree) (root : I)
    (B : I → Finset V) (A : I → Finset I) (g : Ω → I → I → V → ℝ) (M : ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (x : I → State ι V) :
    Measurable (fun ω => law T hT root B A (g ω) M x) := by
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := ι) R B A (g ω)
  have hs (i : I) : Measurable (fun ω => S ω i) := measurable_state R B A g hg i
  have hf (i : I) (r : ι) (v : V) : Measurable (fun ω => (S ω i).1 r v) :=
    (measurable_pi_apply v).comp ((measurable_pi_apply r).comp (hs i).fst)
  have hp (i a : I) : Measurable (fun ω => (S ω i).2 a) :=
    (measurable_pi_apply a).comp (hs i).snd
  apply ExpandedMeasurable.measurable_ensemble T R.parent (parent_antisymm R) M
    (fun ω i => (S ω i).1) B _
    (fun ω i => ((S ω i).2 i).1) (fun ω i => ((S ω i).2 i).2)
    (fun ω i => usedPairs (retained R A i) (S ω i).2)
    (fun i => (hp i i).fst) (fun i => (hp i i).snd) _ x
  · intro i a
    exact (ParticleSchedule.measurable_sweep_real M (fun ω => (S ω i).1 a.1)
      (hf i a.1) {a.2.2}).div_const 2
  · intro i
    exact (Measurable.of_discrete (f := usedPairs (retained R A i))).comp (hs i).snd

/-- Actual expanded-state law and its average L1 metric. No consistency or
measurable gluing choice is part of the hypotheses. -/
theorem realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (A : I → Finset I) (k q : ℕ) (hbag : ∀ i, (B i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q+k.factorial+2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → I → I → V → ℝ)
    (hg : ∀ i a v, Measurable (fun ω => g ω i a v))
    (hLip : ∀ ω i a u v, |g ω i a u-g ω i a v| ≤ L*shortestPathDistance G ℓ u v)
    (hHeight : ∀ ω i a v, |g ω i a v| ≤ H)
    (hzero : ∀ ω i a v, v ∈ B i → g ω i a v = 0) :
    let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
    let cut := ExpandedTree.assemble (fun i => (B i : Set V)) hcover (label (ι := ι))
    let w := fun ω => law (ι := ι) T hT root B A (g ω) M
    (∀ ω x, 0 ≤ w ω x) ∧
    (∀ ω, ∑ x, w ω x = (Fintype.card ι : ℝ)*(2*M)) ∧
    (∀ x, Integrable (fun ω => w ω x) ν) ∧
    ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      (∀ u v, ‖Φ u - Φ v‖ = ∫ ω, cutDistance (w ω) cut u v ∂ν) ∧
      (∀ u v, ‖Φ u - Φ v‖ ≤ (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v) ∧
      ∀ i (u v : B i), ‖Φ u.val - Φ v.val‖ =
        ∫ ω, ∑ r, |(state (ι := ι) (RootedTree.forest T hT root) B A (g ω) i).1 r u -
          (state (ι := ι) (RootedTree.forest T hT root) B A (g ω) i).1 r v| ∂ν := by
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := ι) R B A (g ω)
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  let cut := ExpandedTree.assemble (fun i => (B i : Set V)) hcover (label (ι := ι))
  let w := fun ω => law (ι := ι) T hT root B A (g ω) M
  have hcard : (1:ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hM : 0 < M := by
    have := mul_nonneg hH.le (sub_nonneg.mpr hcard)
    dsimp [M]; linarith
  have hs (ω : Ω) := forest_particle_realization (ι := ι) R B A k q hbag hA hN
    (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)
  have hret (ω : Ω) := retained_functions R A (S ω) (hs ω).2.2.1
  have ht (ω : Ω) : ∀ i j, R.parent j = some i →
      particleTrace M (S ω i).1 (B j) = particleTrace M (S ω j).1 (B j) :=
    fun i j hj => ((hs ω).2.1 j i hj).symm
  have hd (ω : Ω) := ensemble_data T hT R.parent
    (fun _ _ hij => RootedTree.edge_orientation T hT root hij)
    (parent_antisymm R) M hM Fintype.card_pos (fun i => (S ω i).1) B
    (fun i => ((S ω i).2 i).1) (fun i => ((S ω i).2 i).2)
    (fun i => usedPairs (retained R A i) (S ω i).2) (hret ω) (ht ω)
  have hwn : ∀ ω x, 0 ≤ w ω x := fun ω => (hd ω).1
  have hwt : ∀ ω, ∑ x, w ω x = (Fintype.card ι : ℝ)*(2*M) := fun ω => (hd ω).2.1
  have hwi (x : I → State ι V) : Integrable (fun ω => w ω x) ν := by
    apply Integrable.of_bound (measurable_law T hT root B A g M hg x).aestronglyMeasurable
      ((Fintype.card ι : ℝ)*(2*M))
    filter_upwards [] with ω
    rw [Real.norm_eq_abs,abs_of_nonneg (hwn ω x), ← hwt ω]
    exact Finset.single_le_sum (fun y _ => hwn ω y) (Finset.mem_univ x)
  obtain ⟨n,Φ,hΦ⟩ := averaged_cut_realization ν w cut hwn hwi
  have hheight (ω : Ω) (i : I) : ∀ r v, |(S ω i).1 r v| ≤ M := by
    intro r v
    have := function_particles_height_bound hH ((hs ω).1 i) r v
    dsimp [M]; linarith
  have heq (i : I) (u v : B i) : ‖Φ u.val - Φ v.val‖ =
      ∫ ω, ∑ r, |(S ω i).1 r u-(S ω i).1 r v| ∂ν := by
    rw [hΦ]
    apply integral_congr_ae
    filter_upwards [] with ω
    exact ensemble_cobag T hT R.parent
      (fun _ _ hij => RootedTree.edge_orientation T hT root hij) (parent_antisymm R)
      M hM Fintype.card_pos (fun i => (S ω i).1) B hcover hrun
      (fun i => ((S ω i).2 i).1) (fun i => ((S ω i).2 i).2)
      (fun i => usedPairs (retained R A i) (S ω i).2) (hret ω) (ht ω)
      i (hheight ω i) u v u.property v.property
  refine ⟨hwn,hwt,hwi,n,Φ,hΦ,?_,heq⟩
  apply ParticleLaws.norm_bound_from_edges G hG ℓ _ Φ
  intro u v huv
  obtain ⟨i,hu,hv⟩ := hedge u v huv
  rw [heq i ⟨u,hu⟩ ⟨v,hv⟩]
  have hsum (ω : Ω) : (∑ r, |(S ω i).1 r u-(S ω i).1 r v|) ≤
      (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*ℓ ⟨s(u,v),huv⟩ := by
    have hd := shortestPathDistance_pos G ℓ hG hℓ huv.ne
    calc
      _ ≤ ∑ r : ι, L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v :=
        Finset.sum_le_sum (fun r _ => function_particles_difference_bound hL ((hs ω).1 i) r u v hd)
      _ = (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ?_ (by positivity)
        have he := shortestPathDistance_le_walkLength G ℓ (fun e => (hℓ e).le) huv.toWalk
        simpa [SimpleGraph.Adj.toWalk,walkLength] using he
  apply (le_abs_self _).trans
  change ‖∫ ω, (∑ r, |(S ω i).1 r u-(S ω i).1 r v|) ∂ν‖ ≤ _
  have hb := norm_integral_le_of_norm_le_const (μ := ν)
    (Filter.Eventually.of_forall (fun ω => show ‖∑ r, |(S ω i).1 r u-(S ω i).1 r v|‖ ≤ _ from by
      rw [Real.norm_eq_abs,abs_of_nonneg (Finset.sum_nonneg (fun r _ => abs_nonneg _))]
      exact hsum ω))
  simpa only [probReal_univ,mul_one] using hb
end BoundedTreewidthL1.ExpandedAnchor

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X : I)
lemma downPath_take (t : ℕ) :
    downPath T hT root ((downPath T hT root X).getVert t) =
      (downPath T hT root X).take t := by
  exact congrArg Subtype.val ((hT.isAcyclic.subsingleton_path _ _).elim
    ⟨_, downPath_isPath T hT root _⟩ ⟨_, (downPath_isPath T hT root X).take t⟩)
lemma depth_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    (forest T hT root).depth ((downPath T hT root X).getVert t) = t := by
  rw [← downPath_length, downPath_take, SimpleGraph.Walk.take_length,downPath_length]
  exact min_eq_left ht
lemma downPath_getVert_getVert (t a : ℕ) (ha : a ≤ t) :
    (downPath T hT root ((downPath T hT root X).getVert t)).getVert a =
      (downPath T hT root X).getVert a := by
  rw [downPath_take,SimpleGraph.Walk.take_getVert,inf_eq_right.mpr ha]
lemma parent_getVert (t : ℕ) (ht : t < (forest T hT root).depth X) :
    (forest T hT root).parent ((downPath T hT root X).getVert (t+1)) =
      some ((downPath T hT root X).getVert t) := by
  have hadj : T.Adj ((downPath T hT root X).getVert t)
      ((downPath T hT root X).getVert (t+1)) :=
    (downPath T hT root X).adj_getVert_succ (by simpa [downPath_length] using ht)
  rcases edge_orientation T hT root hadj with h | h
  · have hdec := (forest T hT root).decreases _ _ h
    rw [depth_getVert T hT root X t (by omega),depth_getVert T hT root X (t+1) (by omega)] at hdec
    omega
  · exact h
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.TreeCache
open AnchorCache _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
lemma inclusive_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    inclusive T hT root B D k d J ((downPath T hT root X).getVert t) =
    inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J t := by
  unfold inclusive
  rw [depth_getVert T hT root X t ht]
  apply inclusiveCache_prefix (l := t+1)
  · intro a ha
    unfold bags
    rw [downPath_getVert_getVert T hT root X t a (by omega)]
  · intro a ha v b hb
    unfold heights
    rw [downPath_getVert_getVert T hT root X t b (by omega)]
  · omega
lemma active_getVert (t : ℕ) (ht : t ≤ (forest T hT root).depth X) :
    active T hT root B D k d J ((downPath T hT root X).getVert t) =
    (inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J t).image
      (downPath T hT root X).getVert := by
  unfold active
  rw [inclusive_getVert T hT root B D k d J X t ht]
  apply Finset.image_congr
  intro a ha
  exact downPath_getVert_getVert T hT root X t a (inclusive_age _ _ _ _ _ t a ha)
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (Y Z : I)
noncomputable def pathIndex : Fin ((forest T hT Y).depth Z + 1) ↪ I where
  toFun t := (downPath T hT Y Z).getVert t.val
  inj' := by
    intro a b he
    apply Fin.ext
    have ha := depth_getVert T hT Y Z a.val (by omega)
    have hb := depth_getVert T hT Y Z b.val (by omega)
    dsimp only at he
    rw [he] at ha
    omega
lemma pathIndex_comap : T.comap (pathIndex T hT Y Z) =
    SimpleGraph.pathGraph ((forest T hT Y).depth Z + 1) := by
  ext i j
  rw [SimpleGraph.pathGraph_adj]
  constructor
  · intro hij
    have hd := hT.dist_eq_dist_add_one_of_adj Y hij
    have hi := depth_getVert T hT Y Z i.val (by omega)
    have hj := depth_getVert T hT Y Z j.val (by omega)
    change T.dist ((downPath T hT Y Z).getVert i.val) Y = i.val at hi
    change T.dist ((downPath T hT Y Z).getVert j.val) Y = j.val at hj
    change T.dist Y ((downPath T hT Y Z).getVert i.val) =
      T.dist Y ((downPath T hT Y Z).getVert j.val) + 1 ∨
      T.dist Y ((downPath T hT Y Z).getVert j.val) =
      T.dist Y ((downPath T hT Y Z).getVert i.val) + 1 at hd
    rw [SimpleGraph.dist_comm (u := Y),SimpleGraph.dist_comm (u := Y),hi,hj] at hd
    omega
  · rintro (h | h)
    · change T.Adj ((downPath T hT Y Z).getVert i.val) ((downPath T hT Y Z).getVert j.val)
      rw [← h]
      exact (downPath T hT Y Z).adj_getVert_succ (by rw [downPath_length]; omega)
    · change T.Adj ((downPath T hT Y Z).getVert i.val) ((downPath T hT Y Z).getVert j.val)
      rw [← h]
      exact ((downPath T hT Y Z).adj_getVert_succ (by rw [downPath_length]; omega)).symm
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedTree
open ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I A : Type*} [Fintype I] [Fintype A]
noncomputable def pathJoint (T : SimpleGraph I) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) {Y Z : I} (p : T.Walk Y Z) (s : ℕ) (a b : A) : ℝ :=
  if s < p.length then J (p.getVert s) (p.getVert (s+1)) a b
  else if a = b then μ (p.getVert s) a else 0
lemma pathJoint_coupling
    {I : Type treewidthLevel1} {A : Type treewidthLevel2} [Fintype I] [Fintype A]
    (T : SimpleGraph I) (μ : I → A → ℝ)
    (J : I → I → A → A → ℝ) (hμ : ∀ i a, 0 ≤ μ i a)
    (hJ : ∀ i j, T.Adj i j → IsCoupling (μ i) (μ j) (J i j))
    {Y Z : I} (p : T.Walk Y Z) (s : ℕ) :
    IsCoupling (μ (p.getVert s)) (μ (p.getVert (s+1))) (pathJoint T μ J p s) := by
  by_cases hs : s < p.length
  · change IsCoupling _ _ (fun a b => if s < p.length then _ else _)
    simp only [ite_eq_left hs]
    exact hJ _ _ (p.adj_getVert_succ hs)
  · have he : p.getVert (s+1) = p.getVert s := by
      rw [p.getVert_of_length_le (by omega),p.getVert_of_length_le (by omega)]
    rw [he]
    refine ⟨?_,?_,?_⟩
    · intro a b; simp only [pathJoint,ite_eq_right hs]; split_ifs <;> first | exact hμ _ _ | exact le_rfl
    · intro a; simp [pathJoint,hs]
    · intro b; simp [pathJoint,hs]

/-- Restriction of an actual tree law to its unique endpoint path, in the
un-normalized coupling-product convention used by the reservation tests. -/
lemma endpoint_path_product (T : SimpleGraph I) (hT : T.IsTree) (M : ℝ) (hM : 0 < M)
    (μ : I → A → ℝ) (J : I → I → A → A → ℝ) (hs : TreeMarkov.Symmetric (fun _ : I => A) J)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, (∑ a, μ i a) = M)
    (hJ : ∀ i j, T.Adj i j → IsCoupling (μ i) (μ j) (J i j))
    (Y Z : I) (f : A → A → ℝ) :
    (∑ x : I → A, law T M μ J hs x * f (x Y) (x Z)) =
      ∑ x : Fin ((RootedTree.forest T hT Y).depth Z + 1) → A,
        MarkovProduct.weight (fun _ => A) (μ Y)
          (MarkovProduct.couplingKernel (fun _ => A)
            (fun s => μ ((RootedTree.downPath T hT Y Z).getVert s))
            (pathJoint T μ J (RootedTree.downPath T hT Y Z)))
          ((RootedTree.forest T hT Y).depth Z) x *
          f (x 0) (x (Fin.last ((RootedTree.forest T hT Y).depth Z))) := by
  let p := RootedTree.downPath T hT Y Z
  let n := (RootedTree.forest T hT Y).depth Z
  let e := RootedTree.pathIndex T hT Y Z
  have he := RootedTree.pathIndex_comap T hT Y Z
  have hep : e 0 = Y := p.getVert_zero
  have hez : e (Fin.last n) = Z := by
    change p.getVert ((RootedTree.forest T hT Y).depth Z) = Z
    rw [← RootedTree.downPath_length T hT Y Z]
    exact p.getVert_length
  have hc : (T.comap e).Connected := he ▸ SimpleGraph.pathGraph_connected n
  have hpath := path_expectation T hT M hM μ J hs hμ hmass
    (fun i j hij => (hJ i j hij).nonneg) (fun i j hij => (hJ i j hij).row)
    e hc (fun x => f (x 0) (x (Fin.last n)))
  simp only [Function.comp_apply,hep,hez] at hpath
  rw [hpath]
  apply Finset.sum_congr (by ext x; simp)
  intro x _
  congr 1
  rw [he]
  have hq := pathJoint_coupling T μ J hμ hJ p
  have hp := law_path_product M hM (fun s => μ (p.getVert s)) (pathJoint T μ J p)
    (fun s => (hq s).nonneg) (fun s => (hq s).row) (fun s => (hq s).col) n
    (fun i j => J (e i) (e j)) (fun i j => hs (e i) (e j))
    (by
      intro i a b
      simp only [pathJoint]
      rw [ite_eq_left (show i.val < p.length by rw [RootedTree.downPath_length]; exact i.isLt)]
      rfl) x
  convert hp using 1
  · congr 1
  · simp only [p,SimpleGraph.Walk.getVert_zero]; congr 1
end BoundedTreewidthL1.ExpandedTree

namespace BoundedTreewidthL1.ExpandedConstruction
open ExpandedParticleLaw ReservationCoupling
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
lemma ensemble_endpoint (T : SimpleGraph I) (hT : T.IsTree) (parent : I → Option I)
    (horient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i)
    (hanti : ∀ i j, parent i = some j → parent j ≠ some i)
    (M : ℝ) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (F : I → ι → V → ℝ) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i) (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (fresh₁ fresh₂ : I → ι) (C : I → Finset ι)
    (hret : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r)
    (htrace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j))
    (Y Z : I) (y z : V) (hy : y ∈ B Y) (hz : z ∈ B Z) :
    cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) y z =
      ExpandedPathTests.distance M (fun s => F ((RootedTree.downPath T hT Y Z).getVert s))
        (ExpandedTree.pathJoint T (fun i => weight M (F i))
          (joints parent M F B fresh₁ fresh₂ C) (RootedTree.downPath T hT Y Z))
        ((RootedTree.forest T hT Y).depth Z) y z := by
  have hm : 0 < (Fintype.card ι : ℝ)*(2*M) := mul_pos (by exact_mod_cast hι) (by positivity)
  have he : cutDistance (ensemble T parent hanti M F B fresh₁ fresh₂ C)
      (ExpandedTree.assemble (fun i => (B i : Set V)) hcover label) y z =
      ∑ x : I → State ι V, ensemble T parent hanti M F B fresh₁ fresh₂ C x *
        (if label (x Y) y = label (x Z) z then 0 else 1) := by
    unfold cutDistance
    apply Finset.sum_congr rfl
    intro x _
    by_cases hx : ensemble T parent hanti M F B fresh₁ fresh₂ C x = 0
    · simp [hx]
    · rw [ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hx Y y hy,
        ensemble_labels T parent horient hanti M F B hcover hrun fresh₁ fresh₂ C hret htrace x hx Z z hz]
      split_ifs <;> simp
  rw [he]
  have hp := ExpandedTree.endpoint_path_product T hT _ hm (fun i => weight M (F i))
    (joints parent M F B fresh₁ fresh₂ C) (joints_symmetric parent hanti M F B fresh₁ fresh₂ C)
    (fun i => weight_nonneg M (F i)) (fun i => weight_total M hM.le (F i))
    (joints_coupling T parent horient hanti M F B fresh₁ fresh₂ C hret htrace) Y Z
    (fun a b => if label a y = label b z then 0 else 1)
  simpa only [ensemble,ExpandedPathTests.distance,SimpleGraph.Walk.getVert_zero] using hp
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X Y : I)
lemma append_path {u v w : I} (p : T.Walk u v) (q : T.Walk v w)
    (hp : p.IsPath) (hq : q.IsPath)
    (hcommon : ∀ z, z ∈ p.support → z ∈ q.support → z = v) : (p.append q).IsPath := by
  rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append,List.nodup_append]
  refine ⟨hp.support_nodup,hq.support_nodup.tail,?_⟩
  intro z hz w hzq heq
  subst w
  have he := hcommon z hz (List.mem_of_mem_tail hzq)
  subst z
  have hn := hq.support_nodup
  rw [← q.cons_tail_support,List.nodup_cons] at hn
  exact hn.1 hzq

/-- The common root prefixes terminate at one finite, deterministic index. -/
lemma exists_join_index : ∃ s : ℕ,
    s ≤ (forest T hT root).depth X ∧ s ≤ (forest T hT root).depth Y ∧
    (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s ∧
    ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s := by
  let C := (Finset.range ((forest T hT root).depth X+1)).filter (fun a =>
    a ≤ (forest T hT root).depth Y ∧
    (downPath T hT root X).getVert a = (downPath T hT root Y).getVert a)
  have h0 : 0 ∈ C := by simp [C]
  let s := C.max' ⟨0,h0⟩
  have hs : s ∈ C := Finset.max'_mem C ⟨0,h0⟩
  have hsm := Finset.mem_filter.mp hs
  refine ⟨s,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hsm.1,hsm.2.1,hsm.2.2,?_⟩
  intro a b ha hb he
  have hda := depth_getVert T hT root X a ha
  have hdb := depth_getVert T hT root Y b hb
  have hab : a = b := by rw [he] at hda; omega
  refine ⟨hab,?_⟩
  apply Finset.le_max'
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr (by omega),?_⟩
  subst b
  exact ⟨hb,he⟩

/-- At the meet, the two descending arms form exactly the unique Y--X path. -/
lemma path_at_join (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    downPath T hT Y X =
      (((downPath T hT root Y).drop s).reverse.copy rfl hs.symm).append
        ((downPath T hT root X).drop s) := by
  apply congrArg Subtype.val ((hT.isAcyclic.subsingleton_path Y X).elim
    ⟨_,downPath_isPath T hT Y X⟩ ⟨_,?_⟩)
  apply append_path
  · simpa only [SimpleGraph.Walk.isPath_copy] using ((downPath_isPath T hT root Y).drop s).reverse
  · exact (downPath_isPath T hT root X).drop s
  · intro z hzy hzx
    simp only [SimpleGraph.Walk.support_copy,SimpleGraph.Walk.support_reverse,List.mem_reverse] at hzy
    obtain ⟨a,hae,hal⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzx
    obtain ⟨b,hbe,hbl⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hzy
    rw [SimpleGraph.Walk.drop_getVert] at hae hbe
    have ha : s+a ≤ (forest T hT root).depth X := by
      rw [SimpleGraph.Walk.drop_length,downPath_length] at hal; omega
    have hb : s+b ≤ (forest T hT root).depth Y := by
      rw [SimpleGraph.Walk.drop_length,downPath_length] at hbl; omega
    have hab := hmax (s+a) (s+b) ha hb (hae.trans hbe.symm)
    have haz : a = 0 := by omega
    subst a
    simpa only [Nat.add_zero] using hae.symm

lemma join_suffix (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (a : ℕ) :
    (downPath T hT Y X).getVert ((forest T hT root).depth Y-s+a) =
      (downPath T hT root X).getVert (s+a) := by
  rw [path_at_join T hT root X Y s hsx hsy hs hmax,
    SimpleGraph.Walk.getVert_append,SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.drop_length,downPath_length]
  rw [ite_eq_right (by omega),Nat.add_sub_cancel_left,SimpleGraph.Walk.drop_getVert]

lemma join_length (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    (forest T hT Y).depth X = (forest T hT root).depth Y-s + ((forest T hT root).depth X-s) := by
  rw [← downPath_length,path_at_join T hT root X Y s hsx hsy hs hmax]
  simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_copy,
    SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.drop_length,downPath_length]
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedConstruction
open ExpandedParticleLaw ReservationCoupling ReservedSuffix
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
/-- Data of the actual constructed ensemble. Retention and trace identities
are verified by the particle recursion, not axioms about its endpoint map. -/
structure TreeData (T : SimpleGraph I) (M : ℝ) where
  parent : I → Option I
  orient : ∀ i j, T.Adj i j → parent i = some j ∨ parent j = some i
  anti : ∀ i j, parent i = some j → parent j ≠ some i
  F : I → ι → V → ℝ
  B : I → Finset V
  cover : ∀ v, ∃ i, v ∈ B i
  run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected
  fresh₁ : I → ι
  fresh₂ : I → ι
  C : I → Finset ι
  retained : ∀ i j, parent j = some i → ∀ r ∈ C j, F i r = F j r
  trace : ∀ i j, parent j = some i → particleTrace M (F i) (B j) = particleTrace M (F j) (B j)
namespace TreeData
variable {T : SimpleGraph I} {M : ℝ} (D : TreeData (V := V) (ι := ι) T M)
noncomputable def dist (y z : V) : ℝ :=
  cutDistance (ensemble T D.parent D.anti M D.F D.B D.fresh₁ D.fresh₂ D.C)
    (ExpandedTree.assemble (fun i => (D.B i : Set V)) D.cover label) y z
noncomputable def chain (hT : T.IsTree) (Y Z : I) :=
  ExpandedTree.pathJoint T (fun i => weight M (D.F i))
    (joints D.parent M D.F D.B D.fresh₁ D.fresh₂ D.C) (RootedTree.downPath T hT Y Z)
lemma chain_coupling (hT : T.IsTree) (Y Z : I) (s : ℕ) :
    IsCoupling (weight M (D.F ((RootedTree.downPath T hT Y Z).getVert s)))
      (weight M (D.F ((RootedTree.downPath T hT Y Z).getVert (s+1)))) (D.chain hT Y Z s) :=
  ExpandedTree.pathJoint_coupling T _ _ (fun i => weight_nonneg M (D.F i))
    (joints_coupling T D.parent D.orient D.anti M D.F D.B D.fresh₁ D.fresh₂ D.C D.retained D.trace) _ s
lemma chain_eq (hT : T.IsTree) (Y Z : I) (s : ℕ)
    (hs : s < (RootedTree.forest T hT Y).depth Z)
    (hp : D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
      some ((RootedTree.downPath T hT Y Z).getVert s)) :
    D.chain hT Y Z s = kernels M
      (fun s => D.F ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.B ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
      (fun s => D.C ((RootedTree.downPath T hT Y Z).getVert (s+1))) s := by
  funext a b
  simp only [chain, ExpandedTree.pathJoint, RootedTree.downPath_length, ite_eq_left hs, kernels]
  exact congrFun (congrFun (joints_eq D.parent M D.F D.B D.fresh₁ D.fresh₂ D.C _ _ hp) a) b
lemma height_test (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (t : ℕ) (ht : t < (RootedTree.forest T hT Y).depth Z) (r : ι)
    (hdown : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
        some ((RootedTree.downPath T hT Y Z).getVert s))
    (hfixed : ∀ s, t ≤ s → s ≤ (RootedTree.forest T hT Y).depth Z →
      D.F ((RootedTree.downPath T hT Y Z).getVert s) r = D.F ((RootedTree.downPath T hT Y Z).getVert t) r)
    (hkeep : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      r ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (s+1)) ∧
      r ≠ D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s) ∧
      r ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
    (hF : ∀ v, -M ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ∧
      D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ≤ M)
    (ε : ℝ) (hlo : ε ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r z+M)
    (hhi : ε ≤ M-D.F ((RootedTree.downPath T hT Y Z).getVert t) r z)
    (hgap : ∀ v ∈ D.B ((RootedTree.downPath T hT Y Z).getVert t),
      ε ≤ |D.F ((RootedTree.downPath T hT Y Z).getVert t) r z-
        D.F ((RootedTree.downPath T hT Y Z).getVert t) r v|) : ε/2 ≤ D.dist y z := by
  rw [dist, ensemble_endpoint T hT D.parent D.orient D.anti M hM hι D.F D.B D.cover D.run
    D.fresh₁ D.fresh₂ D.C D.retained D.trace Y Z y z hy hz]
  let N := (RootedTree.forest T hT Y).depth Z
  have he : N = t+((N-t-1)+1) := by omega
  nth_rw 1 [show (RootedTree.forest T hT Y).depth Z = t+((N-t-1)+1) from he]
  apply ExpandedPathTests.height_test M hM.le _ _ _ _ _ _ (D.chain_coupling hT Y Z)
    t (N-t-1) r
  · intro s hs hs'; exact D.chain_eq hT Y Z s (by omega) (hdown s hs (by omega))
  · intro s hs hs'; exact D.retained _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact D.trace _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact hfixed s hs (by omega)
  · intro s hs hs'; exact hkeep s hs (by omega)
  · exact hF
  · exact hlo
  · exact hhi
  · exact hgap
lemma launch_test (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (t : ℕ) (ht : t < (RootedTree.forest T hT Y).depth Z)
    (hdown : ∀ s, t ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      D.parent ((RootedTree.downPath T hT Y Z).getVert (s+1)) =
        some ((RootedTree.downPath T hT Y Z).getVert s))
    (hij : D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t) ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t))
    (hbag : ∀ v ∈ D.B ((RootedTree.downPath T hT Y Z).getVert t),
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t)) v =
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)) v)
    (hfixed : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι),
      ∀ s, t ≤ s → s ≤ (RootedTree.forest T hT Y).depth Z →
      D.F ((RootedTree.downPath T hT Y Z).getVert s) r = D.F ((RootedTree.downPath T hT Y Z).getVert t) r)
    (hinit : D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t) ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (t+1)) ∧
      D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t) ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (t+1)))
    (hkeep : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι),
      ∀ s, t+1 ≤ s → s < (RootedTree.forest T hT Y).depth Z →
      r ∈ D.C ((RootedTree.downPath T hT Y Z).getVert (s+1)) ∧
      r ≠ D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert s) ∧
      r ≠ D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert s))
    (hF : ∀ r ∈ ({D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t),
        D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)} : Finset ι), ∀ v,
      -M ≤ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ∧ D.F ((RootedTree.downPath T hT Y Z).getVert t) r v ≤ M) :
    |D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₁ ((RootedTree.downPath T hT Y Z).getVert t)) z -
      D.F ((RootedTree.downPath T hT Y Z).getVert t) (D.fresh₂ ((RootedTree.downPath T hT Y Z).getVert t)) z|/2 ≤ D.dist y z := by
  rw [dist, ensemble_endpoint T hT D.parent D.orient D.anti M hM hι D.F D.B D.cover D.run
    D.fresh₁ D.fresh₂ D.C D.retained D.trace Y Z y z hy hz]
  let N := (RootedTree.forest T hT Y).depth Z
  have he : N = t+((N-t-1)+1) := by omega
  nth_rw 1 [show (RootedTree.forest T hT Y).depth Z = t+((N-t-1)+1) from he]
  apply ExpandedPathTests.launch_test M hM.le _
    (fun s => D.B ((RootedTree.downPath T hT Y Z).getVert s)) _ _
    (fun s => D.C ((RootedTree.downPath T hT Y Z).getVert (s+1))) _ (D.chain_coupling hT Y Z)
    t (N-t-1) hij hbag
  · intro s hs hs'; exact D.chain_eq hT Y Z s (by omega) (hdown s hs (by omega))
  · intro s hs hs'; exact D.retained _ _ (hdown s hs (by omega))
  · intro s hs hs'; exact D.trace _ _ (hdown s hs (by omega))
  · intro r hr s hs hs'; exact hfixed r hr s hs (by omega)
  · exact hinit
  · intro r hr s hs hs'; exact hkeep r hr s hs (by omega)
  · exact hF
end TreeData
end BoundedTreewidthL1.ExpandedConstruction

namespace BoundedTreewidthL1.TreeCache
open _root_.OAI.BoundedTreewidthL1.RootedTree AnchorCache ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
lemma active_on_path (e a t : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hat : a ≤ t) (hte : t ≤ e) :
    (downPath T hT root X).getVert a ∈
      active T hT root B D k d J ((downPath T hT root X).getVert t) := by
  rw [active_getVert T hT root B D k d J X t (hte.trans he)]
  exact Finset.mem_image.mpr ⟨a, inclusive_backwards k _ d _ J hat hte ha, rfl⟩
lemma active_self (i : I) : i ∈ active T hT root B D k d J i := by
  unfold active
  apply Finset.mem_image.mpr
  refine ⟨(forest T hT root).depth i, inclusive_self k _ d _ J _, ?_⟩
  rw [← downPath_length]
  exact SimpleGraph.Walk.getVert_length _
lemma path_ne (a t : ℕ) (ha : a ≤ (forest T hT root).depth X)
    (ht : t ≤ (forest T hT root).depth X) (hat : a ≠ t) :
    (downPath T hT root X).getVert a ≠ (downPath T hT root X).getVert t := by
  intro h
  have hd := congrArg (forest T hT root).depth h
  rw [depth_getVert T hT root X a ha,depth_getVert T hT root X t ht] at hd
  exact hat hd
/-- The actual inclusive tree cache transports an anchor's entire function and
its indices throughout every interval up to its last active bag. -/
lemma pair_transport (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
    (e a t : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hat : a ≤ t) (hte : t ≤ e) :
    let v := (downPath T hT root X).getVert
    (S (v t)).2 (v a) = (S (v a)).2 (v a) ∧
      (S (v t)).1 ((S (v t)).2 (v a)).1 = (S (v a)).1 ((S (v a)).2 (v a)).1 ∧
      (S (v t)).1 ((S (v t)).2 (v a)).2 = (S (v a)).1 ((S (v a)).2 (v a)).2 := by
  dsimp only
  induction t,hat using Nat.le_induction with
  | base => exact ⟨rfl,rfl,rfl⟩
  | succ t hat ih =>
    have htp : t < (forest T hT root).depth X := by omega
    have hact (b : ℕ) (hab : a ≤ b) (hbe : b ≤ e) :=
      active_on_path T hT root B D k d J X e a b he ha hab hbe
    have hp := hpairs _ _ (parent_getVert T hT root X t htp) _
      (Finset.mem_inter.mpr ⟨hact (t+1) (by omega) hte,hact t hat (by omega)⟩)
    obtain ⟨h₁,h₂,h₃⟩ := ih (by omega)
    exact ⟨hp.1.trans h₁,hp.2.1.trans h₂,hp.2.2.trans h₃⟩
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch ParticleSchedule
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
lemma state_congr_depth (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g g' : I → J → V → ℝ) (i : I)
    (heq : ∀ j, R.depth j ≤ R.depth i → g j = g' j) :
    state (ι := ι) R B A g i = state R B A g' i := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [state_eq,state_eq]
    have hpre : (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g) =
        (R.parent i).elim seed (state R B A g') := by
      cases hp : R.parent i with
      | none => rfl
      | some p =>
        simp only [Option.elim_some]
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases _ _ hp) p
          (fun j hj => heq j (hj.trans (R.decreases _ _ hp).le)) rfl
    rw [hpre]
    unfold step
    rw [heq i le_rfl]

lemma predecessor_congr_depth (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g g' : I → J → V → ℝ) (i : I)
    (heq : ∀ j, R.depth j < R.depth i → g j = g' j) :
    (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g) =
      (R.parent i).elim seed (state R B A g') := by
  cases hp : R.parent i with
  | none => rfl
  | some p =>
    simp only [Option.elim_some]
    apply state_congr_depth
    intro j hj
    exact heq j (lt_of_le_of_lt hj (R.decreases _ _ hp))

lemma singleton_launch (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (a : J) (hfresh : fresh R A i = {a}) :
    let pre := (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g)
    let p := pickPair (B i) (usedPairs (retained R A i) pre.2) pre.1
    state (ι := ι) R B A g i = (functionPairUpdate pre.1 p.1 p.2 (g i a), Function.update pre.2 a p) := by
  rw [state_eq]
  unfold step
  rw [hfresh,Finset.toList_singleton]
  rfl

/-- The frozen positive particle is an affine function of its OWN fresh noise;
its baseline is computed entirely before that node is processed. -/
lemma singleton_positive (R : RootedForest I) (B : I → Finset V) (A : I → Finset J)
    (g : I → J → V → ℝ) (i : I) (a : J) (hfresh : fresh R A i = {a})
    (hdistinct : ((state (ι := ι) R B A g i).2 a).1 ≠ ((state R B A g i).2 a).2) :
    let pre := (R.parent i).elim (seed (ι := ι) (V := V) (J := J)) (state R B A g)
    let p := pickPair (B i) (usedPairs (retained R A i) pre.2) pre.1
    (state (ι := ι) R B A g i).1 ((state (ι := ι) R B A g i).2 a).1 = fun v => (pre.1 p.1 v + pre.1 p.2 v)/2 + g i a v := by
  have he := singleton_launch (ι := ι) R B A g i a hfresh
  dsimp only at he ⊢
  rw [he] at hdistinct ⊢
  simp only [Function.update_self] at hdistinct ⊢
  funext v
  exact functionPairUpdate_left _ _ _ hdistinct _ v
end BoundedTreewidthL1.AnchorTreeParticles

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
theorem affine_interval_bound (A b t : ℝ) (hb : b ≠ 0) :
    volume {x : ℝ | |A + b*x| < t} = ENNReal.ofReal (2*t/|b|) := by
  have hset : {x : ℝ | |A + b*x| < t} =
      (fun x : ℝ => b*x) ⁻¹' Ioo (-t-A) (t-A) := by
    ext x
    simp only [mem_ofPred_eq, mem_preimage, mem_Ioo, abs_lt]
    constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith
  rw [hset, Real.volume_preimage_mul_left hb, Real.volume_Ioo,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_inv]
  ring

lemma unit_affine_bound (A b t β : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hb : β ≤ |b|) :
    volume {u : I | |A+b*(u:ℝ)| < t} ≤ ENNReal.ofReal (2*t/β) := by
  have hbn : b ≠ 0 := by intro he; simp [he] at hb; linarith
  have hm : MeasurableSet {u : ℝ | |A+b*u| < t} := measurableSet_lt (by fun_prop) measurable_const
  have he := unitInterval.measurePreserving_coe.measure_preimage hm.nullMeasurableSet
  change volume (Subtype.val ⁻¹' {u : ℝ | |A+b*u| < t}) ≤ _
  rw [he]
  apply (Measure.restrict_le_self _).trans
  rw [affine_interval_bound A b t hbn]
  exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_left (by positivity) hβ hb)

lemma cube_strip {m : ℕ} (j : Fin (m+1)) (c : Fin (m+1) → ℝ)
    (A t γ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    volume {U : Fin (m+1) → I | |A+∑ i, (U i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => I) j
  let E : Set (I × (Fin m → I)) := {z | |A+(z.1:ℝ)*c j+∑ i, (z.2 i:ℝ)*c (j.succAbove i)| < t}
  have he : {U : Fin (m+1) → I | |A+∑ i, (U i:ℝ)*c i| < t} = e ⁻¹' E := by
    ext U
    simp only [E,mem_ofPred_eq,mem_preimage]
    have hh := Fin.sum_univ_succAbove (fun i => (U i:ℝ)*c i) j
    change (|A+∑ i, (U i:ℝ)*c i| < t) ↔
      (|A+(U j:ℝ)*c j+∑ i, (U (j.succAbove i):ℝ)*c (j.succAbove i)| < t)
    rw [hh, add_assoc]
  rw [he,(volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => I) j).measure_preimage_equiv E]
  change (volume.prod volume) E ≤ _
  rw [Measure.prod_apply_symm (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ U : Fin m → I, ENNReal.ofReal (2*t/γ) := by
      apply lintegral_mono
      intro U
      have hs : (fun u : I => (u,U)) ⁻¹' E =
          {u : I | |(A+∑ i, (U i:ℝ)*c (j.succAbove i)) + c j*(u:ℝ)| < t} := by
        ext u
        simp only [E, mem_preimage, mem_ofPred_eq]
        ring_nf
      dsimp only
      rw [hs]
      exact unit_affine_bound (A+∑ i, (U i:ℝ)*c (j.succAbove i)) (c j) t γ ht hγ hc
    _ = _ := by simp

lemma cube_strip_any {m : ℕ} (j : Fin m) (c : Fin m → ℝ)
    (A t γ : ℝ) (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    volume {U : Fin m → I | |A+∑ i, (U i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  cases m with
  | zero => exact j.elim0
  | succ m => exact cube_strip j c A t γ ht hγ hc

lemma product_strip_first {m : ℕ} (A b t β : ℝ) (c : Fin m → ℝ)
    (ht : 0 ≤ t) (hβ : 0 < β) (hb : β ≤ |b|) :
    (volume.prod volume) {z : I × (Fin m → I) |
      |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/β) := by
  rw [Measure.prod_apply_symm (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ U : Fin m → I, ENNReal.ofReal (2*t/β) := by
      apply lintegral_mono
      intro U
      have hs : (fun u : I => (u,U)) ⁻¹'
          {z : I × (Fin m → I) | |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} =
          {u : I | |(A+b+∑ i, (U i:ℝ)*c i) + b*(u:ℝ)| < t} := by
        ext u
        simp only [mem_preimage, mem_ofPred_eq]
        ring_nf
      dsimp only
      rw [hs]
      exact unit_affine_bound (A+b+∑ i, (U i:ℝ)*c i) b t β ht hβ hb
    _ = _ := by simp

lemma product_strip_second {m : ℕ} (j : Fin m) (A b t γ : ℝ) (c : Fin m → ℝ)
    (ht : 0 ≤ t) (hγ : 0 < γ) (hc : γ ≤ |c j|) :
    (volume.prod volume) {z : I × (Fin m → I) |
      |A+b*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c i| < t} ≤ ENNReal.ofReal (2*t/γ) := by
  rw [Measure.prod_apply (measurableSet_lt (by fun_prop) measurable_const)]
  calc
    _ ≤ ∫⁻ u : I, ENNReal.ofReal (2*t/γ) := by
      apply lintegral_mono
      intro u
      exact cube_strip_any j c (A+b*(1+(u:ℝ))) t γ ht hγ hc
    _ = _ := by simp
theorem simultaneous_gap {S : Type*} [Fintype S]
    (m : ℕ) (A b : S → ℝ) (c : S → Fin m → ℝ) (t β γ : ℝ) (ht : 0 ≤ t)
    (hβ : 0 < β) (hγ : 0 < γ)
    (hamp : ∀ s, β ≤ |b s| ∨ ∃ j, γ ≤ |c s j|)
    (hbudget : (Fintype.card S : ℝ) * (2*t/β + 2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (1/2 : ℝ) ≤
      (volume.prod volume) {z : I × (Fin m → I) | ∀ s, t ≤ |A s + b s * (1+(z.1:ℝ)) + ∑ i, (z.2 i:ℝ)*c s i|} := by
  classical
  let E : Set (I × (Fin m → I)) := ⋃ s, {z : I × (Fin m → I) | |A s + b s*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c s i| < t}
  have hE : MeasurableSet E := MeasurableSet.iUnion fun s => measurableSet_lt (by fun_prop) measurable_const
  have hnonneg : 0 ≤ 2*t/β + 2*t/γ := by positivity
  have hmass : (volume.prod volume) E ≤ ENNReal.ofReal (1/2 : ℝ) := by
    calc
      _ ≤ ∑ s, (volume.prod volume) ({z : I × (Fin m → I) | |A s + b s*(1+(z.1:ℝ))+∑ i, (z.2 i:ℝ)*c s i| < t}) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ _s : S, ENNReal.ofReal (2*t/β + 2*t/γ) := by
        apply Finset.sum_le_sum
        intro s _
        rcases hamp s with h | h
        · exact (product_strip_first _ _ _ _ _ ht hβ h).trans
            (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity)))
        · obtain ⟨j,hj⟩ := h
          exact (product_strip_second j _ _ _ _ _ ht hγ hj).trans
            (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (by positivity)))
      _ = ENNReal.ofReal ((Fintype.card S : ℝ)*(2*t/β + 2*t/γ)) := by
        simp [ENNReal.ofReal_mul]
      _ ≤ _ := ENNReal.ofReal_le_ofReal hbudget
  have hfin : (volume.prod volume) E ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hgood : {z : I × (Fin m → I) | ∀ s, t ≤ |A s + b s * (1+(z.1:ℝ)) + ∑ i, (z.2 i:ℝ)*c s i|} = Eᶜ := by
    ext z
    simp [E]
  rw [hgood, measure_compl hE hfin]
  simp only [measure_univ]
  apply ENNReal.le_sub_of_add_le_right hfin
  calc
    _ ≤ ENNReal.ofReal (1/2 : ℝ) + ENNReal.ofReal (1/2 : ℝ) := add_le_add_right hmass _
    _ = 1 := by rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num

end BoundedTreewidthL1.NoiseCube

namespace BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I : Type*} (T : SimpleGraph I) (hT : T.IsTree) (root X Y : I)
lemma join_prefix_data (s : ℕ)
    (_ : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (e : ℕ) (hse : s ≤ e) (hex : e ≤ (forest T hT root).depth X) :
    let v := (downPath T hT root X).getVert
    let l := (forest T hT root).depth Y-s
    (forest T hT Y).depth (v e) = l+(e-s) ∧
    ∀ b, s ≤ b → b ≤ e → (downPath T hT Y (v e)).getVert (l+(b-s)) = v b := by
  dsimp only
  have hedepth := depth_getVert T hT root X e hex
  have hpref (b : ℕ) (hb : b ≤ e) :
      (downPath T hT root ((downPath T hT root X).getVert e)).getVert b =
        (downPath T hT root X).getVert b := by
    rw [downPath_take,SimpleGraph.Walk.take_getVert,inf_eq_right.mpr hb]
  have hse' : s ≤ (forest T hT root).depth ((downPath T hT root X).getVert e) := by omega
  have hs' : (downPath T hT root ((downPath T hT root X).getVert e)).getVert s =
      (downPath T hT root Y).getVert s := (hpref s hse).trans hs
  have hm : ∀ a b, a ≤ (forest T hT root).depth ((downPath T hT root X).getVert e) →
      b ≤ (forest T hT root).depth Y →
      (downPath T hT root ((downPath T hT root X).getVert e)).getVert a =
        (downPath T hT root Y).getVert b → a = b ∧ a ≤ s := by
    intro a b ha hb he
    rw [hedepth] at ha
    rw [hpref a ha] at he
    exact hmax a b (ha.trans hex) hb he
  constructor
  · simpa only [hedepth] using join_length T hT root ((downPath T hT root X).getVert e) Y s hse' hsy hs' hm
  · intro b hsb hbe
    have hh := join_suffix T hT root ((downPath T hT root X).getVert e) Y s hse' hsy hs' hm (b-s)
    rw [Nat.add_sub_of_le hsb,hpref b hbe] at hh
    exact hh
end BoundedTreewidthL1.RootedTree

namespace BoundedTreewidthL1.ExpandedConstruction.TreeData
open _root_.OAI.BoundedTreewidthL1.RootedTree
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι]
  {T : SimpleGraph I} {M : ℝ} (D : TreeData (V := V) (ι := ι) T M)

lemma height_segment (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (v : ℕ → I) (s e l t : ℕ) (hst : s ≤ t) (hte : t < e)
    (hlen : (forest T hT Y).depth Z = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e → (downPath T hT Y Z).getVert (l+(b-s)) = v b)
    (hpar : ∀ b, t ≤ b → b < e → D.parent (v (b+1)) = some (v b))
    (r : ι) (hfixed : ∀ b, t ≤ b → b ≤ e → D.F (v b) r = D.F (v t) r)
    (hkeep : ∀ b, t ≤ b → b < e → r ∈ D.C (v (b+1)) ∧ r ≠ D.fresh₁ (v b) ∧ r ≠ D.fresh₂ (v b))
    (hF : ∀ x, -M ≤ D.F (v t) r x ∧ D.F (v t) r x ≤ M)
    (ε : ℝ) (hlo : ε ≤ D.F (v t) r z+M) (hhi : ε ≤ M-D.F (v t) r z)
    (hgap : ∀ x ∈ D.B (v t), ε ≤ |D.F (v t) r z-D.F (v t) r x|) :
    ε/2 ≤ D.dist y z := by
  have hp (b : ℕ) (hb : l ≤ b) (hbe : b ≤ l+(e-s)) :
      (downPath T hT Y Z).getVert b = v (s+(b-l)) := by
    have hh := hpath (s+(b-l)) (by omega) (by omega)
    simpa only [show l+(s+(b-l)-s) = b by omega] using hh
  have htpath := hpath t hst hte.le
  apply D.height_test hT hM hι Y Z y z hy hz (l+(t-s)) (by omega) r
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hpar (s+(b-l)) (by omega) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),htpath]
    exact hfixed _ (by omega) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hkeep (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hF
  · simpa only [htpath] using hlo
  · simpa only [htpath] using hhi
  · simpa only [htpath] using hgap

lemma launch_segment (hT : T.IsTree) (hM : 0 < M) (hι : 0 < Fintype.card ι)
    (Y Z : I) (y z : V) (hy : y ∈ D.B Y) (hz : z ∈ D.B Z)
    (v : ℕ → I) (s e l t : ℕ) (hst : s ≤ t) (hte : t < e)
    (hlen : (forest T hT Y).depth Z = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e → (downPath T hT Y Z).getVert (l+(b-s)) = v b)
    (hpar : ∀ b, t ≤ b → b < e → D.parent (v (b+1)) = some (v b))
    (hij : D.fresh₁ (v t) ≠ D.fresh₂ (v t))
    (hbag : ∀ x ∈ D.B (v t), D.F (v t) (D.fresh₁ (v t)) x = D.F (v t) (D.fresh₂ (v t)) x)
    (hfixed : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ b, t ≤ b → b ≤ e → D.F (v b) r = D.F (v t) r)
    (hinit : D.fresh₁ (v t) ∈ D.C (v (t+1)) ∧ D.fresh₂ (v t) ∈ D.C (v (t+1)))
    (hkeep : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ b, t+1 ≤ b → b < e →
      r ∈ D.C (v (b+1)) ∧ r ≠ D.fresh₁ (v b) ∧ r ≠ D.fresh₂ (v b))
    (hF : ∀ r ∈ ({D.fresh₁ (v t),D.fresh₂ (v t)} : Finset ι), ∀ x, -M ≤ D.F (v t) r x ∧ D.F (v t) r x ≤ M) :
    |D.F (v t) (D.fresh₁ (v t)) z-D.F (v t) (D.fresh₂ (v t)) z|/2 ≤ D.dist y z := by
  have hp (b : ℕ) (hb : l ≤ b) (hbe : b ≤ l+(e-s)) :
      (downPath T hT Y Z).getVert b = v (s+(b-l)) := by
    have hh := hpath (s+(b-l)) (by omega) (by omega)
    simpa only [show l+(s+(b-l)-s) = b by omega] using hh
  have htpath := hpath t hst hte.le
  rw [← htpath]
  apply D.launch_test hT hM hι Y Z y z hy hz (l+(t-s)) (by omega)
  · intro b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hpar (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hij
  · simpa only [htpath] using hbag
  · rw [htpath]
    intro r hr b htb hbe
    rw [hp b (by omega) (by omega)]
    exact hfixed r hr _ (by omega) (by omega)
  · simpa only [htpath,show l+(t-s)+1 = l+(t+1-s) by omega,hpath (t+1) (by omega) (by omega)] using hinit
  · rw [htpath]
    intro r hr b htb hbe
    rw [hp b (by omega) (by omega),hp (b+1) (by omega) (by omega)]
    simpa only [show s+(b+1-l) = (s+(b-l))+1 by omega] using hkeep r hr (s+(b-l)) (by omega) (by omega)
  · simpa only [htpath] using hF
end BoundedTreewidthL1.ExpandedConstruction.TreeData

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set LaunchNoise
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
lemma flip_triple {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) (κ : Measure C) [SFinite μ] [SFinite ν] [SFinite κ] :
    MeasurePreserving (fun z : A × (B × C) => (z.2.1,(z.1,z.2.2)))
      (μ.prod (ν.prod κ)) (ν.prod (μ.prod κ)) := by
  have h₁ := (measurePreserving_prodAssoc μ ν κ).symm
  have h₂ := (Measure.measurePreserving_swap (μ := μ) (ν := ν)).prod (MeasurePreserving.id κ)
  have h₃ := measurePreserving_prodAssoc ν μ κ
  exact h₃.comp (h₂.comp h₁)

lemma conditioned_gap {S : Type*} [Fintype S] {n m : ℕ}
    (μ : Fin n → ℝ) (_ : ∀ a, 0 ≤ μ a) (_ : ∑ a, μ a = 1)
    (A b : S → ℝ) (c : Fin n → S → Fin m → ℝ) (E : Set (Fin n))
    (t β γ ρ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (_ : 0 ≤ ρ)
    (hgood : ENNReal.ofReal ρ ≤ locationLaw μ E)
    (hamp : ∀ a ∈ E, ∀ s, β ≤ |b s| ∨ ∃ j, γ ≤ |c a s j|)
    (hbudget : (Fintype.card S : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (ρ/2) ≤ noiseLaw m μ {ω | ∀ s,
      t ≤ |A s+b s*noiseXi ω+∑ j, (ω.2.2 j:ℝ)*c ω.2.1 s j|} := by
  let Q : Set (Fin n × (I × (Fin m → I))) := {z | ∀ s,
    t ≤ |A s+b s*(1+(z.2.1:ℝ))+∑ j, (z.2.2 j:ℝ)*c z.1 s j|}
  have hQ : MeasurableSet Q := by
    dsimp only [Q]
    simp_rw [ofPred_forall]
    apply MeasurableSet.iInter
    intro s
    apply measurableSet_le measurable_const
    apply Measurable.abs
    fun_prop
  have he : {ω : NoiseSpace n m | ∀ s,
      t ≤ |A s+b s*noiseXi ω+∑ j, (ω.2.2 j:ℝ)*c ω.2.1 s j|} =
      (fun z : I × (Fin n × (Fin m → I)) => (z.2.1,(z.1,z.2.2))) ⁻¹' Q := rfl
  rw [he,noiseLaw,(flip_triple volume (locationLaw μ) volume).measure_preimage hQ.nullMeasurableSet]
  rw [Measure.prod_apply hQ]
  calc
    ENNReal.ofReal (ρ/2) = ENNReal.ofReal (1/2 : ℝ)*ENNReal.ofReal ρ := by
      rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring
    _ ≤ ENNReal.ofReal (1/2 : ℝ)*locationLaw μ E := mul_le_mul_right hgood _
    _ = ∫⁻ a, E.indicator (fun _ => ENNReal.ofReal (1/2 : ℝ)) a ∂locationLaw μ :=
      (lintegral_indicator_const MeasurableSet.of_discrete _).symm
    _ ≤ _ := by
      apply lintegral_mono
      intro a
      by_cases ha : a ∈ E
      · rw [Set.indicator_of_mem ha]
        exact simultaneous_gap m A b (c a) t β γ ht hβ hγ (hamp a ha) hbudget
      · simp only [Set.indicator_of_notMem ha]; exact bot_le

lemma pi_conditioned {n : ℕ} {Ω : Fin (n+1) → Type*}
    [∀ i, MeasurableSpace (Ω i)] (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : Fin (n+1)) (E : Set (∀ i, Ω i)) (hE : MeasurableSet E) (p : ℝ≥0∞)
    (hfiber : ∀ rest : ∀ j : Fin n, Ω (a.succAbove j),
      p ≤ μ a {u | Fin.insertNth a u rest ∈ E}) : p ≤ Measure.pi μ E := by
  let e := MeasurableEquiv.piFinSuccAbove Ω a
  have he := (measurePreserving_piFinSuccAbove μ a).symm.measure_preimage_equiv E
  rw [← he,Measure.prod_apply_symm (e.symm.measurable hE)]
  calc
    p = ∫⁻ rest : ∀ j : Fin n, Ω (a.succAbove j), p ∂Measure.pi (fun j => μ (a.succAbove j)) := by simp
    _ ≤ _ := lintegral_mono (fun rest => hfiber rest)
end BoundedTreewidthL1.NoiseCube

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.TreeCache
open _root_.OAI.BoundedTreewidthL1.RootedTree AnchorCache ParticleBatch
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype ι] [Nonempty ι] (T : SimpleGraph I) (hT : T.IsTree) (root : I)
  (B : I → Finset V) (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I)
  (S : I → (ι → V → ℝ) × (I → ι × ι))
  (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
lemma index_transport
    {I : Type treewidthLevel1} {V : Type treewidthLevel2} {ι : Type treewidthLevel3} [Fintype ι]
    [Nonempty ι] (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V) (D : I → V → ℝ)
    (k : ℕ) (d : V → V → ℝ) (J : ℝ) (X : I) (S : I → (ι → V → ℝ) × (I → ι × ι))
    (hpairs : ∀ (i p : I), (BoundedTreewidthL1.RootedTree.forest T hT root).parent i = some p → ∀ a
      ∈ BoundedTreewidthL1.TreeCache.active T hT root B D k d J i ∩
      BoundedTreewidthL1.TreeCache.active T hT root B D k d J p, (S i).2 a = (S p).2 a ∧ (S i).1 ((S
      i).2 a).1 = (S p).1 ((S p).2 a).1 ∧ (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
    (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a ≤ b) (hbe : b ≤ e) (u : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v b)).2 (v a) u = pairIndex (S (v a)).2 (v a) u ∧
    (S (v b)).1 (pairIndex (S (v a)).2 (v a) u) = (S (v a)).1 (pairIndex (S (v a)).2 (v a) u) := by
  dsimp only
  obtain ⟨h₁,h₂,h₃⟩ := pair_transport T hT root B D k d J X S hpairs e a b he ha hab hbe
  constructor
  · simp only [pairIndex,h₁]
  · cases u
    · simpa only [pairIndex,Bool.false_eq_true,ite_false,h₁] using h₂
    · simpa only [pairIndex,ite_true,h₁] using h₃
include hpairs
lemma index_retained (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a ≤ b) (hbe : b < e) (u : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v a)).2 (v a) u ∈ usedPairs
      (AnchorTreeParticles.retained (forest T hT root) (active T hT root B D k d J) (v (b+1))) (S (v (b+1))).2 := by
  dsimp only
  rw [← (index_transport T hT root B D k d J X S hpairs e a (b+1) he ha (by omega) (by omega) u).1]
  apply pairIndex_mem
  rw [AnchorTreeParticles.retained,parent_getVert T hT root X b (by omega)]
  exact Finset.mem_inter.mpr ⟨active_on_path T hT root B D k d J X e a (b+1) he ha (by omega) (by omega),
    active_on_path T hT root B D k d J X e a b he ha hab hbe.le⟩
lemma index_avoids (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (e a b : ℕ) (he : e ≤ (forest T hT root).depth X)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hab : a < b) (hbe : b ≤ e) (u w : Bool) :
    let v := (downPath T hT root X).getVert
    pairIndex (S (v a)).2 (v a) u ≠ pairIndex (S (v b)).2 (v b) w := by
  dsimp only
  rw [← (index_transport T hT root B D k d J X S hpairs e a b he ha hab.le hbe u).1]
  intro hh
  have hn := (huniq _ _ (active_on_path T hT root B D k d J X e a b he ha hab.le hbe)
    _ (active_self T hT root B D k d J _) u w hh).1
  exact path_ne T hT root X a b (by omega) (by omega) (by omega) hn
end BoundedTreewidthL1.TreeCache

namespace BoundedTreewidthL1.CachedEnsemble
open _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
attribute [local instance] Classical.decEq Classical.propDecidable
variable {I V ι : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
  (cover : ∀ v, ∃ i, v ∈ B i) (run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
  (D : I → V → ℝ) (k : ℕ) (d : V → V → ℝ) (J : ℝ)
  (S : I → (ι → V → ℝ) × (I → ι × ι)) (M : ℝ)
  (hpairs : ∀ i p, (forest T hT root).parent i = some p →
      ∀ a ∈ active T hT root B D k d J i ∩ active T hT root B D k d J p,
      (S i).2 a = (S p).2 a ∧
      (S i).1 ((S i).2 a).1 = (S p).1 ((S p).2 a).1 ∧
      (S i).1 ((S i).2 a).2 = (S p).1 ((S p).2 a).2)
  (htrace : ∀ i p, (forest T hT root).parent i = some p →
      particleTrace M (S i).1 (B i) = particleTrace M (S p).1 (B i))
noncomputable def data : TreeData (V := V) (ι := ι) T M where
  parent := (forest T hT root).parent
  orient := fun _ _ h => edge_orientation T hT root h
  anti := ExpandedAnchor.parent_antisymm (forest T hT root)
  F := fun i => (S i).1
  B := B
  cover := cover
  run := run
  fresh₁ := fun i => ((S i).2 i).1
  fresh₂ := fun i => ((S i).2 i).2
  C := fun i => usedPairs (AnchorTreeParticles.retained (forest T hT root) (active T hT root B D k d J) i) (S i).2
  retained := ExpandedAnchor.retained_functions _ _ S hpairs
  trace := fun _ _ hi => (htrace _ _ hi).symm

include hpairs htrace
lemma height (hM : 0 < M)
    (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (X Y : I) (y z : V) (hy : y ∈ B Y) (s e l a t : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hst : s ≤ t) (hte : t < e) (hat : a < t)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (u : Bool) (ε : ℝ)
    (hF : ∀ v, |(S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) v| ≤ M)
    (hlo : ε ≤ (S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z+M)
    (hhi : ε ≤ M-(S ((downPath T hT root X).getVert a)).1
      (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z)
    (hgap : ∀ x ∈ B ((downPath T hT root X).getVert t), ε ≤
      |(S ((downPath T hT root X).getVert a)).1
        (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) z-
       (S ((downPath T hT root X).getVert a)).1
        (pairIndex (S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a) u) x|) :
    ε/2 ≤ (data T hT root B cover run D k d J S M hpairs htrace).dist y z := by
  let v := (downPath T hT root X).getVert
  let r := pairIndex (S (v a)).2 (v a) u
  have hf (b : ℕ) (hab : a ≤ b) (hbe : b ≤ e) : (S (v b)).1 r = (S (v a)).1 r :=
    (index_transport T hT root B D k d J X S hpairs e a b he ha hab hbe u).2
  refine (data T hT root B cover run D k d J S M hpairs htrace).height_segment hT hM Fintype.card_pos
    Y (v e) y z hy hz v s e l t hst hte hlen hpath ?_ r ?_ ?_ ?_ ε ?_ ?_ ?_
  · intro b htb hbe
    exact parent_getVert T hT root X b (by omega)
  · intro b htb hbe
    exact (hf b (by omega) hbe).trans (hf t hat.le hte.le).symm
  · intro b htb hbe
    refine ⟨index_retained T hT root B D k d J X S hpairs e a b he ha (by omega) hbe u, ?_, ?_⟩
    · exact index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u false
    · exact index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u true
  · change ∀ x, -M ≤ (S (v t)).1 r x ∧ (S (v t)).1 r x ≤ M
    rw [hf t hat.le hte.le]; exact fun x => abs_le.mp (hF x)
  · change ε ≤ (S (v t)).1 r z+M
    rw [hf t hat.le hte.le]; exact hlo
  · change ε ≤ M-(S (v t)).1 r z
    rw [hf t hat.le hte.le]; exact hhi
  · change ∀ x ∈ B (v t), ε ≤ |(S (v t)).1 r z-(S (v t)).1 r x|
    rw [hf t hat.le hte.le]; exact hgap

lemma launch (hM : 0 < M)
    (huniq : ∀ i, PairUnique (active T hT root B D k d J i) (S i).2)
    (X Y : I) (y z : V) (hy : y ∈ B Y) (s e l a : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hsa : s ≤ a) (hae : a < e)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) d (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (hbag : ∀ x ∈ B ((downPath T hT root X).getVert a),
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).1 x =
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).2 x)
    (hF : ∀ i r x, |(S i).1 r x| ≤ M) :
    |(S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).1 z-
      (S ((downPath T hT root X).getVert a)).1 ((S ((downPath T hT root X).getVert a)).2 ((downPath T hT root X).getVert a)).2 z|/2 ≤
    (data T hT root B cover run D k d J S M hpairs htrace).dist y z := by
  let v := (downPath T hT root X).getVert
  have hiu : ((S (v a)).2 (v a)).1 ≠ ((S (v a)).2 (v a)).2 := by
    intro hh
    have hb := (huniq (v a) _ (active_self T hT root B D k d J _) _
      (active_self T hT root B D k d J _) false true hh).2
    cases hb
  have hr (r : ι) (hr : r ∈ ({((S (v a)).2 (v a)).1,((S (v a)).2 (v a)).2} : Finset ι)) :
      ∃ u, r = pairIndex (S (v a)).2 (v a) u := by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hr
    rcases hr with rfl | rfl
    · exact ⟨false,rfl⟩
    · exact ⟨true,rfl⟩
  apply (data T hT root B cover run D k d J S M hpairs htrace).launch_segment hT hM Fintype.card_pos
    Y (v e) y z hy hz v s e l a hsa hae hlen hpath
  · intro b hab hbe; exact parent_getVert T hT root X b (by omega)
  · exact hiu
  · exact hbag
  · intro r hmem b hab hbe
    obtain ⟨u,rfl⟩ := hr r hmem
    exact (index_transport T hT root B D k d J X S hpairs e a b he ha hab hbe u).2
  · exact ⟨index_retained T hT root B D k d J X S hpairs e a a he ha le_rfl hae false,
      index_retained T hT root B D k d J X S hpairs e a a he ha le_rfl hae true⟩
  · intro r hmem b hab hbe
    obtain ⟨u,rfl⟩ := hr r hmem
    exact ⟨index_retained T hT root B D k d J X S hpairs e a b he ha (by omega) hbe u,
      index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u false,
      index_avoids T hT root B D k d J X S hpairs huniq e a b he ha (by omega) hbe.le u true⟩
  · intro r _ x; exact abs_le.mp (hF _ r x)
end BoundedTreewidthL1.CachedEnsemble

namespace BoundedTreewidthL1.NoiseCube
open MeasureTheory Set LaunchNoise
open scoped unitInterval ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
lemma OrdinarySeed.good_location {V : Type*} [MetricSpace V] {h : V → ℝ} {α π η : ℝ}
    (seed : OrdinarySeed h α π η) (x : V) (hx : 0 < h x) :
    ENNReal.ofReal (π/2) ≤ locationLaw seed.mass {a | GoodBump h α η (seed.bump a) x} := by
  have hh := seed.good x hx
  have he := Measure.map_apply (μ := noiseLaw seed.m seed.mass)
    (measurable_fst.comp measurable_snd) (MeasurableSet.of_discrete (s := {a | GoodBump h α η (seed.bump a) x}))
  change (Measure.map (fun ω : NoiseSpace seed.n seed.m => ω.2.1) (noiseLaw seed.m seed.mass)) _ = _ at he
  rw [noise_locationLaw] at he
  exact he.symm ▸ hh

lemma node_gap {V : Type*} [MetricSpace V] [Fintype V] {n : ℕ}
    (h : Fin (n+1) → V → ℝ) (α π η : ℝ)
    (seed : (i : Fin (n+1)) → OrdinarySeed (h i) α π η)
    (a : Fin (n+1)) (x : V) (B : Finset V)
    (F : ((i : Fin (n+1)) → NoiseSpace (seed i).n (seed i).m) → V → ℝ)
    (hF : ∀ v, Measurable (fun ω => F ω v))
    (haff : ∀ rest : (j : Fin n) → NoiseSpace (seed (a.succAbove j)).n (seed (a.succAbove j)).m,
      ∃ f : V → ℝ, ∀ u v, F (Fin.insertNth a u rest) v = f v + noiseG (h a) (seed a).bump u v)
    (t β γ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π) (hx : 0 < h a x)
    (hamp : ∀ loc, GoodBump (h a) α η ((seed a).bump loc) x → ∀ s ∈ B,
      β ≤ |h a x-h a s| ∨ ∃ j, γ ≤ |(seed a).bump loc j x-(seed a).bump loc j s|)
    (hbudget : (B.card : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (π/4) ≤ (Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass))
      {ω | ∀ s ∈ B, t ≤ |F ω x-F ω s|} := by
  let (i : Fin (n+1)) := (seed i).probability
  apply pi_conditioned _ a _
  · simp_rw [ofPred_forall]
    exact MeasurableSet.iInter (fun s => MeasurableSet.iInter (fun _ => measurableSet_le measurable_const ((hF x).sub (hF s)).abs))
  · intro rest
    obtain ⟨f,hf⟩ := haff rest
    have he : {u | ∀ s ∈ B, t ≤ |F (Fin.insertNth a u rest) x-F (Fin.insertNth a u rest) s|} =
        {u | ∀ s : B, t ≤ |(f x-f s)+(h a x-h a s)*noiseXi u+
          ∑ j, (u.2.2 j : ℝ)*((seed a).bump u.2.1 j x-(seed a).bump u.2.1 j s)|} := by
      ext u
      simp only [mem_ofPred_eq,hf]
      have hab (s : V) : f x+noiseG (h a) (seed a).bump u x-(f s+noiseG (h a) (seed a).bump u s) =
          (f x-f s)+(h a x-h a s)*noiseXi u+
          ∑ j, (u.2.2 j : ℝ)*((seed a).bump u.2.1 j x-(seed a).bump u.2.1 j s) := by
        simp only [noiseG,noiseV,Finset.sum_sub_distrib,mul_sub]
        ring
      simp_rw [hab]
      constructor
      · intro h s; exact h s s.property
      · intro h s hs; exact h ⟨s,hs⟩
    change ENNReal.ofReal (π/4) ≤ (noiseLaw (seed a).m (seed a).mass) {u | ∀ s ∈ B, t ≤ |F (Fin.insertNth a u rest) x-F (Fin.insertNth a u rest) s|}
    rw [he]
    have hh := conditioned_gap (seed a).mass (seed a).mass_nonneg (seed a).mass_total
      (fun s : B => f x-f s) (fun s : B => h a x-h a s)
      (fun loc (s : B) j => (seed a).bump loc j x-(seed a).bump loc j s)
      {loc | GoodBump (h a) α η ((seed a).bump loc) x} t β γ (π/2) ht hβ hγ (by positivity)
      (OrdinarySeed.good_location (seed a) x hx) (fun loc hl s => hamp loc hl s s.property)
      (by simpa only [Fintype.card_coe] using hbudget)
    convert hh using 1 ; congr 1 ; ring
end BoundedTreewidthL1.NoiseCube

namespace BoundedTreewidthL1
open MeasureTheory Set
open scoped ENNReal
lemma event_lower_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Integrable f μ) (hf0 : ∀ ω, 0 ≤ f ω)
    (E : Set Ω) (hE : MeasurableSet E) (p t : ℝ) (hp : 0 ≤ p)
    (hprob : ENNReal.ofReal p ≤ μ E) (hlower : ∀ ω ∈ E, t ≤ f ω) :
    p*t ≤ ∫ ω, f ω ∂μ := by
  by_cases ht : 0 ≤ t
  · have hd : Integrable (E.indicator (fun _ => t)) μ := (integrable_const t).indicator hE
    have hi := integral_mono hd hf (fun ω => by
      by_cases hω : ω ∈ E
      · simpa only [Set.indicator_of_mem hω] using hlower ω hω
      · simpa only [Set.indicator_of_notMem hω] using hf0 ω)
    have hpr : p ≤ μ.real E := by
      rw [measureReal_def]
      exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top μ E)).mp hprob
    rw [integral_indicator hE, setIntegral_const,smul_eq_mul] at hi
    exact (mul_le_mul_of_nonneg_right hpr ht).trans hi
  · exact (mul_nonpos_of_nonneg_of_nonpos hp (le_of_not_ge ht)).trans (integral_nonneg hf0)

lemma gap_proxy {V : Type*} (d : V → V → ℝ) (F : V → ℝ) (x z : V) (B : Finset V)
    (L ε : ℝ) (hL : |F x-F z| ≤ L*d x z)
    (hgap : ∀ s ∈ B, ε ≤ |F x-F s|) :
    ∀ s ∈ B, ε-L*d x z ≤ |F z-F s| := by
  intro s hs
  have hh := abs_sub_le (F x) (F z) (F s)
  linarith [hgap s hs]

lemma gap_budget (k : ℕ) (β γ δ : ℝ) (hβ : 0 < β) (hγ : 0 < γ)
    (_ : 0 ≤ δ) (hδβ : δ ≤ β) (hδγ : δ ≤ γ) :
    (k:ℝ)*(2*(δ/(8*((k:ℝ)+1)))/β+2*(δ/(8*((k:ℝ)+1)))/γ) ≤ 1/2 := by
  have hk : 0 < (k:ℝ)+1 := by positivity
  have h₁ : 2*(δ/(8*((k:ℝ)+1)))/β ≤ 1/(4*((k:ℝ)+1)) := by
    apply (div_le_iff₀ hβ).mpr
    have hh := mul_le_mul_of_nonneg_left hδβ (show 0 ≤ 1/(4*((k:ℝ)+1)) by positivity)
    convert hh using 1 ; field_simp ; ring
  have h₂ : 2*(δ/(8*((k:ℝ)+1)))/γ ≤ 1/(4*((k:ℝ)+1)) := by
    apply (div_le_iff₀ hγ).mpr
    have hh := mul_le_mul_of_nonneg_left hδγ (show 0 ≤ 1/(4*((k:ℝ)+1)) by positivity)
    convert hh using 1 ; field_simp ; ring
  have h := mul_le_mul_of_nonneg_left (add_le_add h₁ h₂) (Nat.cast_nonneg k : (0:ℝ) ≤ k)
  apply h.trans
  apply (le_div_iff₀ (by norm_num : (0:ℝ)<2)).mpr
  field_simp
  nlinarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1.AnchorTreeParticles
open ParticleBatch ParticleSchedule
attribute [local instance 2000] Classical.decEq Classical.propDecidable
variable {V ι : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
noncomputable def positive {I : Type*} (R : RootedForest I) (B : I → Finset V) (A : I → Finset I)
    (g : I → I → V → ℝ) (a : I) : V → ℝ :=
  (state (ι := ι) R B A g a).1 ((state (ι := ι) R B A g a).2 a).1
lemma positive_affine {n : ℕ} {Ω : Fin (n+1) → Type*} [∀ i, Nonempty (Ω i)]
    (R : RootedForest (Fin (n+1))) (B : Fin (n+1) → Finset V) (A : Fin (n+1) → Finset (Fin (n+1)))
    (H : (i : Fin (n+1)) → Ω i → V → ℝ) (a : Fin (n+1)) (hfresh : fresh R A a = {a})
    (hdistinct : ∀ ω : ∀ i, Ω i,
      ((state (ι := ι) R B A (fun i _ => H i (ω i)) a).2 a).1 ≠
      ((state (ι := ι) R B A (fun i _ => H i (ω i)) a).2 a).2) :
    ∀ rest : ∀ j : Fin n, Ω (a.succAbove j), ∃ f : V → ℝ,
      ∀ u v, positive (ι := ι) R B A (fun i _ => H i ((Fin.insertNth a u rest) i)) a v = f v+H a u v := by
  intro rest
  let u₀ : Ω a := Classical.choice inferInstance
  let ω₀ := Fin.insertNth a u₀ rest
  let pre := (R.parent a).elim (seed (ι := ι) (V := V) (J := Fin (n+1)))
    (state R B A (fun i _ => H i (ω₀ i)))
  let p := pickPair (B a) (usedPairs (retained R A a) pre.2) pre.1
  refine ⟨fun v => (pre.1 p.1 v+pre.1 p.2 v)/2,?_⟩
  intro u v
  have hpre := predecessor_congr_depth (ι := ι) R B A
    (fun i _ => H i ((Fin.insertNth a u rest) i)) (fun i _ => H i (ω₀ i)) a (by
      intro j hj
      have hja : j ≠ a := by intro hh; subst j; exact (lt_irrefl _ hj)
      obtain ⟨b,hb⟩ := Fin.exists_succAbove_eq hja
      subst j
      simp only [ω₀,Fin.insertNth_apply_succAbove])
  have hp := congrFun (singleton_positive (ι := ι) R B A
    (fun i _ => H i ((Fin.insertNth a u rest) i)) a a (by convert! hfresh using 1) (hdistinct _)) v
  rw [hpre] at hp
  simpa only [positive,Fin.insertNth_apply_same] using hp

lemma measurable_positive {I Ω : Type*} [Fintype I] [MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]
    (R : RootedForest I) (B : I → Finset V) (A : I → Finset I)
    (g : Ω → I → I → V → ℝ) (hg : ∀ i a v, Measurable (fun ω => g ω i a v)) (a : I) (v : V) :
    Measurable (fun ω => positive (ι := ι) R B A (g ω) a v) := by
  have hs := measurable_state (ι := ι) R B A g hg a
  have hf (r : ι) : Measurable (fun ω => (state (ι := ι) R B A (g ω) a).1 r v) :=
    (measurable_pi_apply v).comp ((measurable_pi_apply r).comp hs.fst)
  have hi : Measurable (fun ω => ((state (ι := ι) R B A (g ω) a).2 a).1) :=
    ((measurable_pi_apply a).comp hs.snd).fst
  exact measurable_selected (fun ω r => (state (ι := ι) R B A (g ω) a).1 r v)
    (fun ω => ((state (ι := ι) R B A (g ω) a).2 a).1) hf hi
end BoundedTreewidthL1.AnchorTreeParticles

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
open scoped ENNReal
attribute [local instance] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

def count (k : ℕ) : ℕ := 2*(cacheBound k+1)+ k.factorial+2
instance count_neZero (k : ℕ) : NeZero (count k) := ⟨by dsimp [count]; omega⟩
def particleLip (k : ℕ) : ℝ := 3*((count k:ℝ)-1)
def upper (k : ℕ) : ℝ := (count k:ℝ)*particleLip k
lemma count_ge (k : ℕ) : 2 ≤ count k := by dsimp [count]; omega
lemma particleLip_pos (k : ℕ) : 0 < particleLip k := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  dsimp [particleLip]; linarith
lemma upper_pos (k : ℕ) : 0 < upper k := by
  have hh : 0 < count k := lt_of_lt_of_le (by omega) (count_ge k)
  exact mul_pos (by exact_mod_cast hh) (particleLip_pos k)

attribute [local instance 2000] Classical.decEq
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (root : Fin (n+1))
  (B : Fin (n+1) → Finset V) (D : Fin (n+1) → V → ℝ) (k : ℕ) (J α π η : ℝ)
  (seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η)
variable {D α π η}
abbrev Space := (i : Fin (n+1)) → NoiseSpace (seed i).n (seed i).m
noncomputable def measure : Measure (Space seed) := Measure.pi (fun i => noiseLaw (seed i).m (seed i).mass)
instance probability : IsProbabilityMeasure (measure seed) := by
  let (i : Fin (n+1)) := (seed i).probability
  exact inferInstanceAs (IsProbabilityMeasure (Measure.pi _))
variable (D α π η)
noncomputable def noise (ω : Space seed) (i : Fin (n+1)) (_ : Fin (n+1)) (v : V) : ℝ := noiseG (D i) (seed i).bump (ω i) v
noncomputable def states (ω : Space seed) := state (ι := Fin (count k)) (forest T hT root) B
  (active T hT root B D k dist J) (noise D α π η seed ω)
noncomputable def raw (cover : ∀ v, ∃ i, v ∈ B i) (H Δ : ℝ) (ω : Space seed) (x y : V) : ℝ :=
  cutDistance (ExpandedAnchor.law (ι := Fin (count k)) T hT root B (active T hT root B D k dist J)
    (noise D α π η seed ω) (H*((count k:ℝ)-1)+2*Δ))
    (ExpandedTree.assemble (fun i => (B i : Set V)) cover (ExpandedParticleLaw.label (ι := Fin (count k)))) x y

structure Model (cover : ∀ v, ∃ i, v ∈ B i) (run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected) where
  H : ℝ
  Δ : ℝ
  H_pos : 0 < H
  Δ_pos : 0 < Δ
  reach : ∀ ω i, FunctionParticleReachable dist 3 H (states T hT root B D k J α π η seed ω i).1
  trace : ∀ ω i p, (forest T hT root).parent i = some p →
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω i).1 (B i) =
    particleTrace (H*((count k:ℝ)-1)+2*Δ) (states T hT root B D k J α π η seed ω p).1 (B i)
  pairs : ∀ ω i p, (forest T hT root).parent i = some p → ∀ a ∈
      active T hT root B D k dist J i ∩ active T hT root B D k dist J p,
    (states T hT root B D k J α π η seed ω i).2 a = (states T hT root B D k J α π η seed ω p).2 a ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).1 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).1 ∧
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 a).2 =
      (states T hT root B D k J α π η seed ω p).1 ((states T hT root B D k J α π η seed ω p).2 a).2
  unique : ∀ ω i, PairUnique (active T hT root B D k dist J i) (states T hT root B D k J α π η seed ω i).2
  gap : ∀ ω i v,
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).1 v-
    (states T hT root B D k J α π η seed ω i).1 ((states T hT root B D k J α π η seed ω i).2 i).2 v =
    2*noise D α π η seed ω i i v
  nonneg : ∀ ω x y, 0 ≤ raw T hT root B D k J α π η seed cover H Δ ω x y
  integrable : ∀ x y, Integrable (fun ω => raw T hT root B D k J α π η seed cover H Δ ω x y) (measure seed)
  dim : ℕ
  map : V → PiLp (1 : ENNReal) (fun _ : Fin dim => ℝ)
  average : ∀ x y, ‖map x-map y‖ = ∫ ω, raw T hT root B D k J α π η seed cover H Δ ω x y ∂measure seed
  upper_bound : ∀ x y, ‖map x-map y‖ ≤ upper k*dist x y

namespace Model
variable {T hT root B D k J α π η seed} {cover : ∀ v, ∃ i, v ∈ B i}
  {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)
noncomputable def datum (ω : Space seed) :=
  CachedEnsemble.data T hT root B cover run D k dist J (states T hT root B D k J α π η seed ω)
    (P.H*((count k:ℝ)-1)+2*P.Δ) (P.pairs ω) (P.trace ω)
lemma datum_dist (ω : Space seed) (x y : V) :
    (P.datum ω).dist x y = raw T hT root B D k J α π η seed cover P.H P.Δ ω x y := rfl
lemma M_pos : 0 < P.H*((count k:ℝ)-1)+2*P.Δ := by
  have hh : (2:ℝ) ≤ count k := by exact_mod_cast count_ge k
  nlinarith [P.H_pos,P.Δ_pos]
lemma height (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x| ≤ P.H*((count k:ℝ)-1) := by
  simpa only [Fintype.card_fin] using function_particles_height_bound P.H_pos (P.reach ω i) r x
include P
lemma lipschitz (ω : Space seed) (i : Fin (n+1)) (r : Fin (count k)) (x z : V) :
    |(states T hT root B D k J α π η seed ω i).1 r x-
      (states T hT root B D k J α π η seed ω i).1 r z| ≤ particleLip k*dist x z := by
  simpa only [Fintype.card_fin,particleLip] using function_particles_metric_bound (by norm_num : (0:ℝ)<3) (P.reach ω i) r x z
lemma pair_distinct (ω : Space seed) (i : Fin (n+1)) :
    ((states T hT root B D k J α π η seed ω i).2 i).1 ≠
    ((states T hT root B D k J α π η seed ω i).2 i).2 := by
  intro hh
  have hb := (P.unique ω i i (active_self T hT root B D k dist J i)
    i (active_self T hT root B D k dist J i) false true hh).2
  cases hb

lemma gap_probability (a : Fin (n+1)) (x : V) (C : Finset V)
    (t β γ : ℝ) (ht : 0 ≤ t) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π) (hx : 0 < D a x)
    (hamp : ∀ loc, GoodBump (D a) α η ((seed a).bump loc) x → ∀ s ∈ C,
      β ≤ |D a x-D a s| ∨ ∃ j, γ ≤ |(seed a).bump loc j x-(seed a).bump loc j s|)
    (hbudget : (C.card : ℝ)*(2*t/β+2*t/γ) ≤ 1/2) :
    ENNReal.ofReal (π/4) ≤ measure seed {ω : Space seed | ∀ s ∈ C, t ≤
      |positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a x-
       positive (ι := Fin (count k)) (forest T hT root) B (active T hT root B D k dist J)
        (noise D α π η seed ω) a s|} := by
  let (i : Fin (n+1)) := (seed i).probability
  let (i : Fin (n+1)) : Nonempty (NoiseSpace (seed i).n (seed i).m) :=
    nonempty_of_isProbabilityMeasure (noiseLaw (seed i).m (seed i).mass)
  apply NoiseCube.node_gap D α π η seed a x C _ _ _ t β γ ht hβ hγ hπ hx hamp hbudget
  · intro v
    apply measurable_positive
    intro i b v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  · exact positive_affine (forest T hT root) B (active T hT root B D k dist J)
      (fun i u => noiseG (D i) (seed i).bump u) a
      (TreeCache.fresh_eq_singleton T hT root B D k dist J a) (fun ω => P.pair_distinct ω a)

lemma height_test (X Y : Fin (n+1)) (x y z : V) (hy : y ∈ B Y) (s e l a t : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hst : s ≤ t) (hte : t < e) (hat : a < t)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b)
    (τ β γ : ℝ) (hτ : 0 ≤ τ) (hτΔ : τ ≤ 2*P.Δ) (hβ : 0 < β) (hγ : 0 < γ) (hπ : 0 ≤ π)
    (hx : 0 < D ((downPath T hT root X).getVert a) x)
    (hamp : ∀ loc, GoodBump (D ((downPath T hT root X).getVert a)) α η
      ((seed ((downPath T hT root X).getVert a)).bump loc) x →
      ∀ v ∈ B ((downPath T hT root X).getVert t),
        β ≤ |D ((downPath T hT root X).getVert a) x-D ((downPath T hT root X).getVert a) v| ∨
        ∃ j, γ ≤ |(seed ((downPath T hT root X).getVert a)).bump loc j x-
          (seed ((downPath T hT root X).getVert a)).bump loc j v|)
    (hbudget : ((B ((downPath T hT root X).getVert t)).card : ℝ)*(2*τ/β+2*τ/γ) ≤ 1/2) :
    (π/8)*(τ-particleLip k*dist x z) ≤ ‖P.map y-P.map z‖ := by
  let v := (downPath T hT root X).getVert
  let F := fun (ω : Space seed) => positive (ι := Fin (count k)) (forest T hT root) B
    (active T hT root B D k dist J) (noise D α π η seed ω) (v a)
  let E := {ω : Space seed | ∀ b ∈ B (v t), τ ≤ |F ω x-F ω b|}
  have hmeas (b : V) : Measurable (fun ω => F ω b) := by
    apply measurable_positive
    intro i c b
    exact ((measurable_pi_apply b).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hE : MeasurableSet E := by
    simp only [E,Set.ofPred_forall]
    exact MeasurableSet.iInter (fun b => MeasurableSet.iInter (fun _ =>
      measurableSet_le measurable_const ((hmeas x).sub (hmeas b)).abs))
  have hprob : ENNReal.ofReal (π/4) ≤ measure seed E :=
    P.gap_probability (v a) x (B (v t)) τ β γ hτ hβ hγ hπ hx hamp hbudget
  have hlower (ω : Space seed) (hω : ω ∈ E) :
      (τ-particleLip k*dist x z)/2 ≤ raw T hT root B D k J α π η seed cover P.H P.Δ ω y z := by
    rw [← P.datum_dist]
    apply CachedEnsemble.height T hT root B cover run D k dist J
      (states T hT root B D k J α π η seed ω) _ (P.pairs ω) (P.trace ω)
      P.M_pos (P.unique ω) X Y y z hy s e l a t he hst hte hat ha hz hlen hpath false
      (τ-particleLip k*dist x z)
    · intro b
      change |F ω b| ≤ _
      exact (P.height ω (v a) _ b).trans (by linarith [P.Δ_pos])
    · have hh := (abs_le.mp (P.height ω (v a) ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 z)).1
      have hn := mul_nonneg (particleLip_pos k).le (dist_nonneg (x := x) (y := z))
      simp only [pairIndex, Bool.false_eq_true, ite_false]
      change τ-particleLip k*dist x z ≤ _
      linarith
    · have hh := (abs_le.mp (P.height ω (v a) ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 z)).2
      have hn := mul_nonneg (particleLip_pos k).le (dist_nonneg (x := x) (y := z))
      simp only [pairIndex, Bool.false_eq_true, ite_false]
      change τ-particleLip k*dist x z ≤ _
      linarith
    · exact gap_proxy dist (F ω) x z (B (v t)) (particleLip k) τ
        (P.lipschitz ω (v a) _ x z) hω
  have hh := event_lower_integral (measure seed) _ (P.integrable y z) (fun ω => P.nonneg ω y z)
    E hE (π/4) ((τ-particleLip k*dist x z)/2) (by positivity) hprob hlower
  rw [P.average]
  convert hh using 1 ; ring

lemma launch_test (hzero : ∀ i v, v ∈ B i → D i v = 0)
    (X Y : Fin (n+1)) (y z : V) (hy : y ∈ B Y) (s e l a : ℕ)
    (he : e ≤ (forest T hT root).depth X) (hsa : s ≤ a) (hae : a < e)
    (ha : a ∈ inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J e)
    (hz : z ∈ B ((downPath T hT root X).getVert e))
    (hlen : (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-s))
    (hpath : ∀ b, s ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-s)) = (downPath T hT root X).getVert b) :
    D ((downPath T hT root X).getVert a) z ≤ ‖P.map y-P.map z‖ := by
  let v := (downPath T hT root X).getVert
  have hp (ω : Space seed) : D (v a) z ≤ raw T hT root B D k J α π η seed cover P.H P.Δ ω y z := by
    have ht := CachedEnsemble.launch T hT root B cover run D k dist J
      (states T hT root B D k J α π η seed ω) _ (P.pairs ω) (P.trace ω)
      P.M_pos (P.unique ω) X Y y z hy s e l a he hsa hae ha hz hlen hpath
    have hbag : ∀ b ∈ B (v a),
        (states T hT root B D k J α π η seed ω (v a)).1 ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).1 b =
        (states T hT root B D k J α π η seed ω (v a)).1 ((states T hT root B D k J α π η seed ω (v a)).2 (v a)).2 b := by
      intro b hb
      have hh := ((seed (v a)).bounds (ω (v a))).2.2.2 b
      rw [hzero _ _ hb] at hh
      have hg := P.gap ω (v a) b
      change _ = 2*noiseG (D (v a)) (seed (v a)).bump (ω (v a)) b at hg
      linarith
    specialize ht hbag (fun i r b => (P.height ω i r b).trans (by linarith [P.Δ_pos]))
    change |_ - _|/2 ≤ (P.datum ω).dist y z at ht
    rw [P.gap ω (v a) z,P.datum_dist] at ht
    have hh := ((seed (v a)).bounds (ω (v a))).2.2.2 z
    have ha := le_abs_self (2*noise D α π η seed ω (v a) (v a) z)
    change D (v a) z ≤ noise D α π η seed ω (v a) (v a) z ∧ _ at hh
    linarith
  rw [P.average]
  have hh := integral_mono (integrable_const (D (v a) z)) (P.integrable y z) hp
  simpa only [integral_const,probReal_univ,smul_eq_mul,one_mul] using hh

end Model
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles _root_.OAI.BoundedTreewidthL1.RootedTree TreeCache AnchorCache ParticleBatch ExpandedConstruction
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

/-- Every chosen actual finite ordinary seed produces the ensemble; no consistency
or global lower comparison is an assumption. -/
theorem model_exists {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph (Fin (n+1))) (hT : T.IsTree) (root : Fin (n+1))
    (B : Fin (n+1) → Finset V) (hne : ∀ i, (B i).Nonempty)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (k : ℕ) (hbag : ∀ i, (B i).card ≤ k) (J α π η : ℝ) :
    let := weightedMetricSpace G ℓ hG hℓ
    let D := fun i => bagDistance G ℓ (B i) (hne i)
    ∀ seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η,
    ∃ P : Model T hT root B D k J α π η seed hcover (fun v => (hrun v).preconnected),
      ∀ i v, D i v ≤ P.Δ := by
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  dsimp only
  intro seed
  let A := active T hT root B D k dist J
  let q := cacheBound k+1
  let R := forest T hT root
  let g := noise D α π η seed
  let S := states T hT root B D k J α π η seed
  let H : ℝ := 1+3*∑ i, ∑ v, D i v
  let Δ : ℝ := 1+∑ i, ∑ v, D i v
  have hD : ∀ i v, 0 ≤ D i v := fun i v =>
    bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  have hsum : 0 ≤ ∑ i, ∑ v, D i v :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun v _ => hD i v))
  have hH : 0 < H := by dsimp [H]; positivity
  have hΔ : 0 < Δ := by dsimp [Δ]; positivity
  have hdSum (i : Fin (n+1)) (v : V) : D i v ≤ ∑ j, ∑ x, D j x := by
    apply (Finset.single_le_sum (fun x (_ : x ∈ (Finset.univ : Finset V)) => hD i x) (Finset.mem_univ v)).trans
    exact Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin (n+1)))) =>
      Finset.sum_nonneg (fun x _ => hD j x)) (Finset.mem_univ i)
  have hdH (i : Fin (n+1)) (v : V) : (5/2)*D i v ≤ H := by
    dsimp [H]; linarith [hdSum i v,hD i v]
  have hg : ∀ i a v, Measurable (fun ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (seed i).measurable).comp (measurable_pi_apply i)
  have hLip : ∀ ω i a u v, |g ω i a u-g ω i a v| ≤ 3*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    exact ((seed i).bounds (ω i)).2.2.1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    change |noiseG (D i) (seed i).bump (ω i) v| ≤ H
    rw [abs_of_nonneg ((hD i v).trans hb.1)]
    exact hb.2.trans (hdH i v)
  have hz : ∀ ω i a v, v ∈ B i → g ω i a v = 0 := by
    intro ω i a v hv
    have hb := ((seed i).bounds (ω i)).2.2.2 v
    have he : D i v = 0 := by
      rw [show D i v = Metric.infDist v (B i : Set V) from
        bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) v]
      exact Metric.infDist_zero_of_mem hv
    change D i v ≤ g ω i a v ∧ g ω i a v ≤ (5/2)*D i v at hb
    rw [he] at hb
    exact le_antisymm (by simpa only [mul_zero] using hb.2) hb.1
  have hA : ∀ i, (A i).card ≤ q :=
    graph_active_bound G ℓ hG hℓ T B hne hT root hedge hrun k hbag J
  have hN : Fintype.card (Fin (count k)) = 2*q+k.factorial+2 := by exact Fintype.card_fin _
  have hf (ω : Space seed) := forest_particle_realization (ι := Fin (count k)) R B A k q hbag hA
    hN dist 3 H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hz ω)
  obtain ⟨hwn,hwt,hwi,m,Φ,hΦ,hup,hco⟩ := ExpandedAnchor.realization (ι := Fin (count k))
    G hG ℓ hℓ T hT root B hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA hN
    (measure seed) 3 H Δ (by norm_num) hH hΔ g hg hLip hHeight hz
  let P : Model T hT root B D k J α π η seed hcover (fun v => (hrun v).preconnected) := {
    H := H, Δ := Δ, H_pos := hH, Δ_pos := hΔ
    reach := fun ω i => (hf ω).1 i
    trace := fun ω i p hp => by simpa only [states,R,A,g,Fintype.card_fin] using (hf ω).2.1 i p hp
    pairs := fun ω i p hp a ha => (hf ω).2.2.1 i p hp a (by simpa only [Finset.mem_inter] using ha)
    unique := fun ω => state_unique R B A (g ω) k q hN hbag hA
    gap := fun ω i v => by
      apply ((hf ω).2.2.2 i i ?_).2 v
      rw [show fresh R A i = {i} from fresh_eq_singleton T hT root B D k dist J i]
      exact Finset.mem_singleton_self i
    nonneg := fun ω x y => Finset.sum_nonneg (fun c _ => by split_ifs; exact le_rfl; simpa only [Fintype.card_fin] using hwn ω c)
    integrable := fun x y => by
      apply integrable_finsetSum
      intro c _
      split_ifs
      · exact integrable_zero _ _ _
      · simpa only [Fintype.card_fin] using hwi c
    dim := m
    map := Φ
    average := fun x y => by simpa only [raw,A,g,Fintype.card_fin] using hΦ x y
    upper_bound := fun x y => by
      change ‖Φ x-Φ y‖ ≤ upper k*shortestPathDistance G ℓ x y
      convert hup x y using 1 ; simp only [Fintype.card_fin,upper,particleLip] ; ring }
  refine ⟨P,?_⟩
  intro i v
  change D i v ≤ Δ
  dsimp [Δ]; linarith [hdSum i v]
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1
open Filter

def InfinitesimalAlong {I : Type*} (U : Ultrafilter I) (x : I → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ i in U, x i < ε

/-- A reservation interval whose effective start is early and terminal time is
late. Validity is explicit; no anchor is created merely by taking a quotient. -/
def CrossingSequence {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ)
    (δ : I → ℕ → ℝ) (a : I → ℕ) : Prop :=
  (∀ᶠ i in U, valid i (a i)) ∧
  ¬InfinitesimalAlong U (fun i => δ i (start i (a i))) ∧
  InfinitesimalAlong U (fun i => δ i (finish i (a i)))

/-- Crossing anchor sequences identified precisely when they agree eventually. -/
def CrossingGerms {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ) :
    Set (Germ (U : Filter I) ℕ) :=
  {x | ∃ a : I → ℕ, (a : Germ (U : Filter I) ℕ) = x ∧
    CrossingSequence U valid start finish δ a}

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

lemma noninfinitesimal_iff {I : Type*} (U : Ultrafilter I) (x : I → ℝ) :
    ¬InfinitesimalAlong U x ↔ ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ i in U, ε ≤ x i := by
  classical
  simp only [InfinitesimalAlong, not_forall]
  constructor
  · rintro ⟨ε, hε, hn⟩
    refine ⟨ε, hε, ?_⟩
    simpa only [not_lt] using (Ultrafilter.eventually_not.mpr hn)
  · rintro ⟨ε, hε, hx⟩
    refine ⟨ε, hε, ?_⟩
    intro h
    obtain ⟨i, hi, hi'⟩ := (hx.and h).exists
    exact (not_lt_of_ge hi) hi'

lemma early_precedes_late {I : Type*} (U : Ultrafilter I) (δ : I → ℕ → ℝ)
    (hmono : ∀ i, Antitone (δ i)) (s t : I → ℕ)
    (hs : ¬InfinitesimalAlong U (fun i => δ i (s i)))
    (ht : InfinitesimalAlong U (fun i => δ i (t i))) :
    ∀ᶠ i in U, s i < t i := by
  obtain ⟨ε, hε, he⟩ := (noninfinitesimal_iff U _).mp hs
  filter_upwards [he, ht ε hε] with i hi hi'
  by_contra h
  have hm := hmono i (Nat.le_of_not_gt h)
  exact (not_lt_of_ge (hi.trans hm)) hi'

lemma germ_total {I : Type*} (U : Ultrafilter I)
    (a b : Germ (U : Filter I) ℕ) : a ≤ b ∨ b ≤ a := by
  induction a using Germ.inductionOn with
  | h a =>
    induction b using Germ.inductionOn with
    | h b =>
      exact Ultrafilter.eventually_or.mp (Eventually.of_forall (fun i => le_total (a i) (b i)))

/-- Any fixed finite collection of pairwise distinct crossing reservations is
simultaneously present at the latest of its effective start times. -/
theorem crossing_family_card_le {I J : Type*} [Fintype J] (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (a : J → I → ℕ) (ha : ∀ j, CrossingSequence U valid start finish δ (a j))
    (hdistinct : ∀ j k, j ≠ k → ∀ᶠ i in U, a j i ≠ a k i) :
    Fintype.card J ≤ N := by
  classical
  let latest (i : I) := Finset.univ.sup (fun j => start i (a j i))
  have hva : ∀ᶠ i in U, ∀ j, valid i (a j i) :=
    eventually_all.mpr (fun j => (ha j).1)
  have hbefore : ∀ᶠ i in U, ∀ j k, start i (a j i) < finish i (a k i) := by
    apply eventually_all.mpr
    intro j
    apply eventually_all.mpr
    intro k
    exact early_precedes_late U δ hmono _ _ (ha j).2.1 (ha k).2.2
  have hinj : ∀ᶠ i in U, Function.Injective (fun j => a j i) := by
    have hef : ∀ᶠ i in U, ∀ j k, j ≠ k → a j i ≠ a k i := by
      apply eventually_all.mpr
      intro j
      apply eventually_all.mpr
      intro k
      by_cases h : j = k
      · exact Eventually.of_forall (by simp [h])
      · exact (hdistinct j k h).mono (fun _ hi _ => hi)
    exact hef.mono (fun i hi j k hjk => by_contra (fun hne => hi j k hne hjk))
  obtain ⟨i, hvi, hbi, hii⟩ := (hva.and (hbefore.and hinj)).exists
  have hmem : ∀ j, a j i ∈ cache i (latest i) := by
    intro j
    apply hcache i (a j i) (latest i) (hvi j)
    · exact Finset.le_sup (s := Finset.univ) (f := fun j => start i (a j i)) (Finset.mem_univ j)
    · exact Finset.sup_le (fun k _ => (hbi k j).le)
  let f : J → ↥(cache i (latest i)) := fun j => ⟨a j i, hmem j⟩
  have hf : Function.Injective f := by
    intro j k h
    exact hii (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_coe] at hc
  exact hc.trans (hsize i (latest i))

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

lemma crossing_finset_card_le {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (s : Finset (Germ (U : Filter I) ℕ))
    (hs : ∀ x ∈ s, x ∈ CrossingGerms U valid start finish δ) : s.card ≤ N := by
  classical
  have hrep : ∀ j : ↥s, ∃ a : I → ℕ,
      (a : Germ (U : Filter I) ℕ) = j.val ∧ CrossingSequence U valid start finish δ a :=
    fun j => hs j.val j.property
  choose a heq ha using hrep
  have hd : ∀ j k : ↥s, j ≠ k → ∀ᶠ i in U, a j i ≠ a k i := by
    intro j k hjk
    apply Ultrafilter.eventually_not.mpr
    intro h
    apply hjk
    apply Subtype.ext
    exact (heq j).symm.trans ((Germ.coe_eq.mpr h).trans (heq k))
  have hc := crossing_family_card_le U valid start finish δ cache N hmono hcache hsize a ha hd
  simpa only [Fintype.card_coe] using hc

/-- The youngest crossing, with the inclusive cache bound and monotone
normalized distances made explicit. -/
theorem youngest_crossing {I : Type*} (U : Ultrafilter I)
    (valid : I → ℕ → Prop) (start finish : I → ℕ → ℕ) (δ : I → ℕ → ℝ)
    (cache : I → ℕ → Finset ℕ) (N : ℕ)
    (hmono : ∀ i, Antitone (δ i))
    (hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a → a ∈ cache i t)
    (hsize : ∀ i t, (cache i t).card ≤ N)
    (hne : (CrossingGerms U valid start finish δ).Nonempty) :
    (CrossingGerms U valid start finish δ).Finite ∧
    (CrossingGerms U valid start finish δ).ncard ≤ N ∧
    ∃ youngest ∈ CrossingGerms U valid start finish δ,
      ∀ a ∈ CrossingGerms U valid start finish δ, a ≤ youngest := by
  classical
  let C := CrossingGerms U valid start finish δ
  have hb : ∀ s : Finset (Germ (U : Filter I) ℕ), (∀ x ∈ s, x ∈ C) → s.card ≤ N :=
    crossing_finset_card_le U valid start finish δ cache N hmono hcache hsize
  have hfin : C.Finite := by
    by_contra h
    obtain ⟨t, ht, htf, htc⟩ := Set.Infinite.exists_subset_ncard_eq h (N + 1)
    have hbound := hb htf.toFinset (fun x hx => ht (htf.mem_toFinset.mp hx))
    have hc : htf.toFinset.card = t.ncard := (Set.ncard_eq_toFinset_card t htf).symm
    rw [hc, htc] at hbound
    omega
  refine ⟨hfin, ?_, ?_⟩
  · have hbound := hb hfin.toFinset (fun x hx => hfin.mem_toFinset.mp hx)
    rw [show CrossingGerms U valid start finish δ = C from rfl, Set.ncard_eq_toFinset_card C hfin]
    exact hbound
  · obtain ⟨a, ha, hmax⟩ := hfin.exists_maximal hne
    refine ⟨a, ha, ?_⟩
    intro b hb
    rcases germ_total U b a with hba | hab
    · exact hba
    · exact hmax hb hab

end BoundedTreewidthL1

namespace BoundedTreewidthL1

namespace ReservationPath

def Present (P : ReservationPath) (a t : ℕ) : Prop := a ≤ t ∧ t ≤ P.finish a

def Successor (P : ReservationPath) (a b t : ℕ) : Prop :=
  P.Present a t ∧ P.Present b t ∧ a < b ∧
    ∀ c, P.Present c t → a < c → b ≤ c

lemma mem_inclusive (P : ReservationPath) {a t : ℕ} (ht : t ≤ P.last) :
    a ∈ P.inclusive t ↔ P.Present a t := by
  classical
  simp only [inclusive, ht, ↓reduceIte, Finset.mem_filter, Finset.mem_range, Present]
  omega

lemma proposal_present (P : ReservationPath) (t : ℕ) (ht : t ≤ P.last) :
    P.Present t t := ⟨le_rfl, P.launch_le_finish t ht⟩

lemma successor_exists (P : ReservationPath) (a t : ℕ)
    (ht : t ≤ P.last) (ha : P.Present a t) (hat : a < t) :
    ∃ b, P.Successor a b t := by
  classical
  let S := (P.inclusive t).filter (fun b => a < b)
  have hS : S.Nonempty := ⟨t, Finset.mem_filter.mpr ⟨(P.mem_inclusive ht).mpr
    (P.proposal_present t ht), hat⟩⟩
  refine ⟨S.min' hS, ha, ?_, ?_, ?_⟩
  · exact (P.mem_inclusive ht).mp (Finset.mem_filter.mp (Finset.min'_mem S hS)).1
  · exact (Finset.mem_filter.mp (Finset.min'_mem S hS)).2
  · intro c hc hac
    exact Finset.min'_le S c (Finset.mem_filter.mpr ⟨(P.mem_inclusive ht).mpr hc, hac⟩)

lemma proposal_retained_of_other_release (P : ReservationPath) (a t : ℕ)
    (hat : a < t) (ht : t < P.last) (ha : P.finish a = t) : t < P.finish t := by
  have hp := P.launch_le_finish t ht.le
  by_contra h
  have hft : P.finish t = t := Nat.le_antisymm (Nat.le_of_not_gt h) hp
  have := P.one_release a t t hat.le le_rfl ht ha hft
  omega

/-- Once b immediately follows a after an eviction test, no subsequent insertion
can appear between them: new anchors have later launch times. -/
lemma successor_at_later_test (P : ReservationPath) (a b t u : ℕ)
    (hab : a < b) (hbt : b ≤ t) (htu : t < u)
    (ha : P.Present a u) (hb : P.Present b u)
    (hmin : ∀ c, a < c → c ≤ t → t < P.finish c → b ≤ c) :
    P.Successor a b u := by
  refine ⟨ha, hb, hab, ?_⟩
  intro c hc hac
  by_cases hct : c ≤ t
  · exact hmin c hac hct (htu.trans_le hc.2)
  · exact hbt.trans (Nat.le_of_not_ge hct)

/-- A surviving younger anchor exists after the last eviction of any younger
anchor launched above S. The only use of protection is for a successor already
launched at or after `S`. -/
lemma retained_successor (P : ReservationPath) (a S t : ℕ)
    (haS : a < S) (hSt : S ≤ t) (ht : t < P.last)
    (ha : t < P.finish a)
    (hold : ∀ c, a < c → c < S → P.finish c ≤ t)
    (hprotect : ∀ b, S ≤ b → P.Successor a b t → t < P.finish b) :
    ∃ b, a < b ∧ S ≤ b ∧ b ≤ t ∧ t < P.finish b ∧
      ∀ c, a < c → c ≤ t → t < P.finish c → b ≤ c := by
  classical
  obtain ⟨b, hb⟩ := P.successor_exists a t ht.le ⟨haS.le.trans hSt, ha.le⟩
    (haS.trans_le hSt)
  have hex : ∃ c, a < c ∧ c ≤ t ∧ t < P.finish c := by
    by_cases hSb : S ≤ b
    · exact ⟨b, hb.2.2.1, hb.2.1.1, hprotect b hSb hb⟩
    · have hbS : b < S := Nat.lt_of_not_ge hSb
      have hbf : P.finish b = t := (hold b hb.2.2.1 hbS).antisymm hb.2.1.2
      exact ⟨t, haS.trans_le hSt, le_rfl,
        P.proposal_retained_of_other_release b t (hbS.trans_le hSt) ht hbf⟩
  let A := (Finset.range (t + 1)).filter (fun c => a < c ∧ t < P.finish c)
  have hA : A.Nonempty := by
    obtain ⟨c, hac, hct, hcf⟩ := hex
    exact ⟨c, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hac, hcf⟩⟩
  let b' := A.min' hA
  have hb' : a < b' ∧ b' ≤ t ∧ t < P.finish b' := by
    have hm := Finset.mem_filter.mp (Finset.min'_mem A hA)
    exact ⟨hm.2.1, Nat.le_of_lt_succ (Finset.mem_range.mp hm.1), hm.2.2⟩
  refine ⟨b', hb'.1, ?_, hb'.2.1, hb'.2.2, ?_⟩
  · by_contra h
    have := hold b' hb'.1 (Nat.lt_of_not_ge h)
    omega
  · intro c hac hct hcf
    exact Finset.min'_le A c (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by omega), hac, hcf⟩)

end ReservationPath
end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter

def PathCrossing {I : Type*} (U : Ultrafilter I) (P : I → ReservationPath)
    (S : I → ℕ) (δ : I → ℕ → ℝ) (a : I → ℕ) : Prop :=
  CrossingSequence U
    (fun i b => b ≤ (P i).last ∧ S i ≤ (P i).finish b)
    (fun i b => max (S i) b) (fun i => (P i).finish) δ a

lemma infinitesimal_congr {I : Type*} (U : Ultrafilter I) {x y : I → ℝ}
    (h : ∀ᶠ i in U, x i = y i) : InfinitesimalAlong U x ↔ InfinitesimalAlong U y := by
  constructor
  · intro hx ε hε
    filter_upwards [h, hx ε hε] with i hi hi'
    simpa only [← hi] using hi'
  · intro hy ε hε
    filter_upwards [h, hy ε hε] with i hi hi'
    simpa only [hi] using hi'

lemma infinitesimal_mono {I : Type*} (U : Ultrafilter I) {x y : I → ℝ}
    (h : ∀ᶠ i in U, x i ≤ y i) (hy : InfinitesimalAlong U y) :
    InfinitesimalAlong U x := by
  intro ε hε
  filter_upwards [h, hy ε hε] with i hi hi'
  exact hi.trans_lt hi'

lemma eventually_choose_nat {I : Type*} (U : Ultrafilter I) (p : I → ℕ → Prop)
    (h : ∀ᶠ i in U, ∃ b, p i b) : ∃ b : I → ℕ, ∀ᶠ i in U, p i (b i) := by
  classical
  let b i := if h : ∃ a, p i a then Classical.choose h else 0
  refine ⟨b, h.mono ?_⟩
  intro i hi
  simpa only [b, dite_eq_left hi] using Classical.choose_spec hi

theorem younger_crossing {I : Type*} (U : Ultrafilter I)
    (P : I → ReservationPath) (S : I → ℕ) (δ : I → ℕ → ℝ)
    (hSL : ∀ i, S i ≤ (P i).last) (hmono : ∀ i, Antitone (δ i))
    (hSearly : ¬InfinitesimalAlong U (fun i => δ i (S i)))
    (hXlate : InfinitesimalAlong U (fun i => δ i (P i).last))
    (a : I → ℕ) (ha : PathCrossing U P S δ a)
    (haold : ∀ᶠ i in U, a i < S i)
    (hprotect : ∀ t : I → ℕ, ¬InfinitesimalAlong U (fun i => δ i (t i)) →
      ∀ᶠ i in U, ∀ b, S i ≤ b → (P i).Successor (a i) b (t i) →
        t i < (P i).finish b) :
    ∃ b : I → ℕ, PathCrossing U P S δ b ∧ ∀ᶠ i in U, a i < b i := by
  classical
  by_contra hno
  have hnone : ∀ b : I → ℕ, PathCrossing U P S δ b →
      ¬(∀ᶠ i in U, a i < b i) := by
    intro b hb hab
    exact hno ⟨b, hb, hab⟩
  let O (i : I) := (Finset.range (S i)).filter (fun b => a i < b)
  let t (i : I) := max (S i) ((O i).sup (P i).finish)
  have hSt : ∀ i, S i ≤ t i := fun i => le_max_left _ _
  have hold : ∀ i c, a i < c → c < S i → (P i).finish c ≤ t i := by
    intro i c hac hcS
    exact (Finset.le_sup (s := O i) (f := (P i).finish)
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hcS, hac⟩)).trans (le_max_right _ _)
  have htL : ∀ i, t i ≤ (P i).last := by
    intro i
    apply max_le (hSL i)
    apply Finset.sup_le
    intro b hb
    have hbS := Finset.mem_range.mp (Finset.mem_filter.mp hb).1
    exact (P i).finish_le_last b (hbS.le.trans (hSL i))
  have hattain : ∀ i, S i < t i →
      ∃ b, a i < b ∧ b < S i ∧ (P i).finish b = t i := by
    intro i hi
    have hsup : t i = (O i).sup (P i).finish := max_eq_right (by dsimp [t] at hi; omega)
    have hO : (O i).Nonempty := by
      by_contra hn
      have he := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [he, Finset.sup_empty, bot_eq_zero] at hsup
      omega
    obtain ⟨b, hb, he⟩ := Finset.exists_mem_eq_sup (O i) hO (P i).finish
    exact ⟨b, (Finset.mem_filter.mp hb).2,
      Finset.mem_range.mp (Finset.mem_filter.mp hb).1, he.symm.trans hsup.symm⟩
  have htearly : ¬InfinitesimalAlong U (fun i => δ i (t i)) := by
    intro htlate
    have hbefore := early_precedes_late U δ hmono S t hSearly htlate
    obtain ⟨b, hb⟩ := eventually_choose_nat U
      (fun i b => a i < b ∧ b < S i ∧ (P i).finish b = t i)
      (hbefore.mono fun i hi => hattain i hi)
    have hcross : PathCrossing U P S δ b := by
      refine ⟨?_, ?_, ?_⟩
      · filter_upwards [hb] with i hi
        exact ⟨hi.2.1.le.trans (hSL i), hi.2.2 ▸ hSt i⟩
      · have heq : ∀ᶠ i in U, δ i (max (S i) (b i)) = δ i (S i) := by
          filter_upwards [hb] with i hi
          rw [max_eq_left hi.2.1.le]
        exact fun h => hSearly ((infinitesimal_congr U heq).mp h)
      · have heq : ∀ᶠ i in U, δ i ((P i).finish (b i)) = δ i (t i) :=
          hb.mono (fun i hi => congrArg (δ i) hi.2.2)
        exact (infinitesimal_congr U heq).mpr htlate
    exact hnone b hcross (hb.mono (fun _ hi => hi.1))
  have hta := early_precedes_late U δ hmono t (fun i => (P i).finish (a i))
    htearly ha.2.2
  have htX := early_precedes_late U δ hmono t (fun i => (P i).last) htearly hXlate
  have hprot := hprotect t htearly
  have hex : ∀ᶠ i in U, ∃ b, a i < b ∧ S i ≤ b ∧ b ≤ t i ∧
      t i < (P i).finish b ∧
      ∀ c, a i < c → c ≤ t i → t i < (P i).finish c → b ≤ c := by
    filter_upwards [haold, hta, htX, hprot] with i hai htai htXi hpi
    exact (P i).retained_successor (a i) (S i) (t i) hai (hSt i) htXi htai
      (hold i) hpi
  obtain ⟨b, hb⟩ := eventually_choose_nat U _ hex
  have hbearly : ¬InfinitesimalAlong U (fun i => δ i (max (S i) (b i))) := by
    intro hblate
    exact htearly (infinitesimal_mono U (hb.mono (fun i hi =>
      hmono i (max_le (hSt i) hi.2.2.1))) hblate)
  have hbvalid : ∀ᶠ i in U, b i ≤ (P i).last ∧ S i ≤ (P i).finish (b i) := by
    filter_upwards [hb] with i hi
    exact ⟨hi.2.2.1.trans (htL i), (hSt i).trans hi.2.2.2.1.le⟩
  have hbendearly : ¬InfinitesimalAlong U (fun i => δ i ((P i).finish (b i))) := by
    intro hlate
    exact hnone b ⟨hbvalid, hbearly, hlate⟩ (hb.mono (fun _ hi => hi.1))
  let u i := (P i).finish (b i)
  have hua := early_precedes_late U δ hmono u (fun i => (P i).finish (a i))
    hbendearly ha.2.2
  have huprot := hprotect u hbendearly
  have hcontr : ∀ᶠ i : I in (U : Filter I), False := by
    filter_upwards [hb, hbvalid, hua, huprot] with i hi hvi huai hpi
    have hsucc : (P i).Successor (a i) (b i) (u i) := by
      apply (P i).successor_at_later_test (a i) (b i) (t i) (u i)
        hi.1 hi.2.2.1 hi.2.2.2.1
      · exact ⟨hi.1.le.trans ((P i).launch_le_finish (b i) hvi.1), huai.le⟩
      · exact ⟨(P i).launch_le_finish (b i) hvi.1, le_rfl⟩
      · exact hi.2.2.2.2
    have hbad := hpi (b i) hi.2.1 hsucc
    exact (lt_irrefl (u i)) hbad
  exact hcontr.exists.elim (fun _ h => h)

theorem cache_no_failure {I : Type*} (U : Ultrafilter I)
    (P : I → ReservationPath) (S : I → ℕ) (δ : I → ℕ → ℝ) (N : ℕ)
    (hSL : ∀ i, S i ≤ (P i).last) (hmono : ∀ i, Antitone (δ i))
    (hSearly : ¬InfinitesimalAlong U (fun i => δ i (S i)))
    (hXlate : InfinitesimalAlong U (fun i => δ i (P i).last))
    (hsize : ∀ i t, ((P i).inclusive t).card ≤ N)
    (hold : ∀ a, PathCrossing U P S δ a → ∀ᶠ i in U, a i < S i)
    (hprotect : ∀ a, PathCrossing U P S δ a →
      ∀ t : I → ℕ, ¬InfinitesimalAlong U (fun i => δ i (t i)) →
        ∀ᶠ i in U, ∀ b, S i ≤ b → (P i).Successor (a i) b (t i) →
          t i < (P i).finish b) : False := by
  classical
  let valid i b := b ≤ (P i).last ∧ S i ≤ (P i).finish b
  let start i b := max (S i) b
  let finish i := (P i).finish
  have hcache : ∀ i a t, valid i a → start i a ≤ t → t ≤ finish i a →
      a ∈ (P i).inclusive t := by
    intro i a t hv hst htf
    have htL : t ≤ (P i).last := htf.trans ((P i).finish_le_last a hv.1)
    exact ((P i).mem_inclusive htL).mpr ⟨(le_max_right _ _).trans hst, htf⟩
  have hroot : PathCrossing U P S δ (fun _ => 0) := by
    refine ⟨Eventually.of_forall ?_, ?_, ?_⟩
    · intro i
      exact ⟨Nat.zero_le _, (P i).root_permanent.symm ▸ hSL i⟩
    · simpa only [Nat.max_zero] using hSearly
    · simpa only [ReservationPath.root_permanent] using hXlate
  have hne : (CrossingGerms U valid start finish δ).Nonempty :=
    ⟨((fun _ : I => 0) : Germ (U : Filter I) ℕ), (fun _ => 0), rfl, hroot⟩
  obtain ⟨_, _, g, hg, hmax⟩ := youngest_crossing U valid start finish δ
    (fun i => (P i).inclusive) N hmono hcache hsize hne
  obtain ⟨a, heq, ha⟩ := hg
  obtain ⟨b, hb, hab⟩ := younger_crossing U P S δ hSL hmono hSearly hXlate a
    ha (hold a ha) (hprotect a ha)
  have hbg : (b : Germ (U : Filter I) ℕ) ≤ g := hmax _ ⟨b, rfl, hb⟩
  rw [← heq] at hbg
  have hba : ∀ᶠ i in U, b i ≤ a i := Germ.coe_le.mp hbg
  obtain ⟨i, hi, hi'⟩ := (hab.and hba).exists
  exact (not_lt_of_ge hi') hi

end BoundedTreewidthL1

namespace BoundedTreewidthL1
open Filter
/-- Numerical interface to the actual cached ensemble. The three tests below
are proved from that ensemble, rather than postulated in the embedding theorem. -/
structure CacheControl (N : ℕ) (Q H : ℝ) where
  path : ReservationPath
  start : ℕ
  start_le : start ≤ path.last
  delta : ℕ → ℝ
  antitone : Antitone delta
  nonneg : ∀ t, 0 ≤ delta t
  at_start : delta start = 1
  at_end : delta path.last = 0
  error : ℝ
  error_nonneg : 0 ≤ error
  size : ∀ t, (path.inclusive t).card ≤ N
  launch : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → start ≤ a →
    delta a ≤ Q*(error+delta e)
  distant : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → a < start →
    delta a ≤ H → 1 ≤ Q*(error+delta e)
  protect : ∀ a e t b, e ≤ path.last → a ∈ path.inclusive e → a < start →
    H < delta a → start ≤ t → t < e → start ≤ b → path.Successor a b t →
    Q*(error+delta e) < delta t → t < path.finish b

lemma infinitesimal_add_mul {I : Type*} (U : Ultrafilter I) (x y : I → ℝ)
    (hx : InfinitesimalAlong U x) (hy : InfinitesimalAlong U y) (Q : ℝ) (hQ : 0 < Q) :
    InfinitesimalAlong U (fun i => Q*(x i+y i)) := by
  intro ε hε
  have he : 0 < ε/(2*Q) := by positivity
  filter_upwards [hx _ he,hy _ he] with i hxi hyi
  have heq : ε/(2*Q)+ε/(2*Q) = ε/Q := by ring
  have hh : x i+y i < ε/Q := by rw [← heq]; exact add_lt_add hxi hyi
  simpa only [mul_comm] using (lt_div_iff₀ hQ).mp hh

lemma CacheControl.no_failure {I : Type*} (U : Ultrafilter I) (N : ℕ) (Q H : ℝ)
    (hQ : 0 < Q) (C : I → CacheControl N Q H)
    (herror : InfinitesimalAlong U (fun i => (C i).error)) : False := by
  have hear : ¬InfinitesimalAlong U (fun i => (C i).delta (C i).start) := by
    intro hh
    obtain ⟨i,hi⟩ := (hh 1 (by norm_num)).exists
    change (C i).delta (C i).start < 1 at hi
    rw [(C i).at_start] at hi
    exact (lt_irrefl _ hi)
  have hlate : InfinitesimalAlong U (fun i => (C i).delta (C i).path.last) := by
    intro ε hε
    exact Eventually.of_forall (fun i => by dsimp only; rw [(C i).at_end]; exact hε)
  apply cache_no_failure U (fun i => (C i).path) (fun i => (C i).start)
    (fun i => (C i).delta) N (fun i => (C i).start_le)
    (fun i => (C i).antitone) hear hlate (fun i => (C i).size)
  · intro a ha
    have herr := infinitesimal_add_mul U _ _ herror ha.2.2 Q hQ
    change ∀ᶠ i in U, a i < (C i).start
    simp only [← not_le]
    apply Ultrafilter.eventually_not.mpr
    intro hnot
    have haS : ∀ᶠ i in U, (C i).start ≤ a i := hnot.mono (fun _ hi => hi)
    apply ha.2.1
    apply infinitesimal_mono U _ herr
    filter_upwards [ha.1,haS] with i hi hiS
    rw [max_eq_right hiS]
    apply (C i).launch (a i) ((C i).path.finish (a i))
      ((C i).path.finish_le_last _ hi.1) _ hiS
    exact ((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
      ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩
  · intro a ha t ht
    have herr := infinitesimal_add_mul U _ _ herror ha.2.2 Q hQ
    have hold : ∀ᶠ i in U, a i < (C i).start := by
      simp only [← not_le]
      apply Ultrafilter.eventually_not.mpr
      intro hnot
      apply ha.2.1
      apply infinitesimal_mono U _ herr
      filter_upwards [ha.1,hnot] with i hi hiS
      rw [max_eq_right hiS]
      apply (C i).launch (a i) ((C i).path.finish (a i))
        ((C i).path.finish_le_last _ hi.1) _ hiS
      exact ((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
        ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩
    have hdist : ∀ᶠ i in U, H < (C i).delta (a i) := by
      filter_upwards [ha.1,hold,herr 1 (by norm_num)] with i hi hoi hei
      by_contra hn
      have hh := (C i).distant (a i) ((C i).path.finish (a i))
        ((C i).path.finish_le_last _ hi.1)
        (((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
          ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩) hoi (le_of_not_gt hn)
      exact (not_lt_of_ge hh) hei
    have hte := early_precedes_late U (fun i => (C i).delta)
      (fun i => (C i).antitone) t (fun i => (C i).path.finish (a i)) ht ha.2.2
    obtain ⟨ε,hε,htearly⟩ := (noninfinitesimal_iff U _).mp ht
    filter_upwards [ha.1,hold,hdist,hte,htearly,herr ε hε] with i hi hoi hdi hti het her
    intro b hbS hsucc
    apply (C i).protect (a i) ((C i).path.finish (a i)) (t i) b
      ((C i).path.finish_le_last _ hi.1)
      (((C i).path.mem_inclusive ((C i).path.finish_le_last _ hi.1)).mpr
        ⟨(C i).path.launch_le_finish _ hi.1,le_rfl⟩) hoi hdi
      (hbS.trans hsucc.2.1.1) hti hbS hsucc (her.trans_le het)

/-- Compactness is used only on numerical cache data, not on random samplers or
on a bounded number of vertices. -/
theorem CacheControl.uniform_lower (N : ℕ) (Q H : ℝ) (hQ : 0 < Q) :
    ∃ c : ℝ, 0 < c ∧ ∀ C : CacheControl N Q H, c ≤ C.error := by
  classical
  by_contra hn
  push Not at hn
  have hex (n : ℕ) : ∃ C : CacheControl N Q H, C.error < 1/((n:ℝ)+1) :=
    hn _ (by positivity)
  choose C hC using hex
  let U := Ultrafilter.of (atTop : Filter ℕ)
  apply CacheControl.no_failure U N Q H hQ C
  intro ε hε
  obtain ⟨n,hn⟩ := exists_nat_gt (1/ε)
  apply (Ultrafilter.of_le atTop) (mem_atTop_sets.mpr ⟨n,?_⟩)
  intro m hm
  have hnm : (n:ℝ) ≤ m := by exact_mod_cast hm
  have hmpos : 0 < (m:ℝ)+1 := by positivity
  apply (hC m).trans
  apply (div_lt_iff₀ hmpos).mpr
  have hh := (div_lt_iff₀ hε).mp (hn.trans_le hnm)
  nlinarith
end BoundedTreewidthL1

namespace BoundedTreewidthL1

theorem protected_threshold (K J H D₀ δ L older younger : ℝ)
    (hK : 2 < K) (hJ : J = 10 * (K + 1)) (hH : 10 ^ 5 * J < H)
    (hD : H < D₀) (hδ : 0 < δ) (_ : δ ≤ 1)
    (hLlo : δ / 4 ≤ L) (hLhi : L ≤ 10 * D₀)
    (hyδ : younger ≤ K * δ) (hy2 : younger ≤ 2)
    (holder : D₀ - 1 ≤ older) :
    ∃ τ ∈ ({L / 100, J * L} : Set ℝ), younger ≤ τ ∧ τ < older := by
  have hJpos : 0 < J := by linarith
  have hDlarge : 10 < D₀ := by norm_num at hH; linarith
  by_cases hL : L ≤ 300
  · refine ⟨J * L, by simp, ?_, ?_⟩
    · have hmul := mul_le_mul_of_nonneg_left hLlo hJpos.le
      have hgap : K * δ < J * (δ / 4) := by rw [hJ]; nlinarith
      exact hyδ.trans (hgap.le.trans hmul)
    · have hmul := mul_le_mul_of_nonneg_left hL hJpos.le
      norm_num at hH
      linarith
  · refine ⟨L / 100, by simp, ?_, ?_⟩
    · linarith
    · linarith

end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1
open AnchorCache
attribute [local instance] Classical.decEq Classical.propDecidable
theorem near_far_scaled {V : Type*} [MetricSpace V]
    (B : Finset V) (x p v₀ : V) (h φ : V → ℝ)
    (δ D R a : ℝ) (hδ : 0 < δ) (hδD : δ ≤ D)
    (hp : dist x p = δ) (hv : v₀ ∈ B)
    (hnear : ∀ s ∈ B, δ ≤ dist x s)
    (hh : ∀ u v, |h u - h v| ≤ dist u v)
    (hheight : h x = D) (hgeo : h v₀ + dist x v₀ = D)
    (hhnonneg : 0 ≤ h v₀)
    (hno : ∀ q ∈ B, ¬(δ/4 ≤ dist p q ∧ dist p q ≤ 10*D))
    (hR : R < 9*D) (ha : 0 < a) (hφx : a ≤ φ x)
    (hφ : ∀ s, R < dist x s → φ s = 0) :
    ∀ s ∈ B, δ/2 ≤ |h x-h s| ∨ a ≤ |φ x-φ s| := by
  have hvdist : dist p v₀ ≤ 2*D := by
    have ht := dist_triangle p x v₀
    rw [dist_comm p x, hp] at ht
    linarith
  have hvclose : dist p v₀ < δ/4 := by
    by_contra hn
    exact hno v₀ hv ⟨le_of_not_gt hn, by linarith⟩
  intro s hs
  by_cases hsclose : dist p s < δ/4
  · left
    have hvs : dist v₀ s < δ/2 := by
      have ht := dist_triangle v₀ p s
      rw [dist_comm v₀ p] at ht
      linarith
    have hhvs := (abs_le.mp (hh v₀ s)).1
    have hmin := hnear v₀ hv
    have hgap : δ/2 ≤ h x - h s := by rw [hheight]; linarith
    exact hgap.trans (le_abs_self _)
  · right
    have hfar : 10*D < dist p s := by
      by_contra hn
      exact hno s hs ⟨le_of_not_gt hsclose, le_of_not_gt hn⟩
    have hxs : R < dist x s := by
      have ht := dist_triangle p x s
      rw [dist_comm p x, hp] at ht
      linarith
    rw [hφ s hxs, sub_zero, abs_of_nonneg (ha.le.trans hφx)]
    exact hφx

lemma protected_threshold_scaled (K J H D₀ δ A L older younger : ℝ)
    (hK : 2 < K) (hJ : J = 10*(K+1)) (hH : 10^5*J < H)
    (hA : 0 < A) (hD : H*A < D₀) (hδ : 0 < δ) (_ : δ ≤ A)
    (hLlo : δ/4 ≤ L) (hLhi : L ≤ 10*D₀)
    (hyδ : younger ≤ K*δ) (hy2 : younger ≤ 2*A) (holder : D₀-A ≤ older) :
    ∃ τ ∈ ({L/100,J*L} : Set ℝ), younger ≤ τ ∧ τ < older := by
  have hJpos : 0 < J := by linarith
  have hHA : 10^5*J*A < H*A := mul_lt_mul_of_pos_right hH hA
  by_cases hL : L ≤ 300*A
  · refine ⟨J*L,by simp,?_,?_⟩
    · have hmul := mul_le_mul_of_nonneg_left hLlo hJpos.le
      have hgap : K*δ < J*(δ/4) := by rw [hJ]; nlinarith
      exact hyδ.trans (hgap.le.trans hmul)
    · have hmul := mul_le_mul_of_nonneg_left hL hJpos.le
      have hJA : 30*A < J*A := mul_lt_mul_of_pos_right (by linarith) hA
      norm_num at hHA
      nlinarith
  · refine ⟨L/100,by simp,by linarith,?_⟩
    have hJA : 30*A < J*A := mul_lt_mul_of_pos_right (by linarith) hA
    norm_num at hHA
    nlinarith

lemma protected_of_successor {V : Type*} [DecidableEq V]
    (R : ReservationPath) (B : Finset V) (D : V → ℕ → ℝ) (d : V → V → ℝ) (J : ℝ)
    (t a b : ℕ) (ht : t ≤ R.last) (hab : R.Successor a b t)
    (p q : V) (hp : p ∈ B) (hq : q ∈ B) (hpq : p ≠ q)
    (hw : ∃ τ ∈ ({d p q/100,J*d p q} : Set ℝ), D p b ≤ τ ∧ τ < D p a) :
    b ∈ protectedEntries B (R.inclusive t) d D J := by
  classical
  obtain ⟨τ,hτ,hlo,hhi⟩ := hw
  have hd : Drop (R.inclusive t) (D p) τ b := by
    refine ⟨(R.mem_inclusive ht).mpr hab.2.1,hlo,a,(R.mem_inclusive ht).mpr hab.1,hab.2.2.1,hhi,?_⟩
    intro c hc hac
    exact hab.2.2.2 c ((R.mem_inclusive ht).mp hc) hac
  apply Finset.mem_biUnion.mpr
  refine ⟨(p,q),Finset.mem_product.mpr ⟨hp,hq⟩,?_⟩
  simp only [ite_eq_right hpq]
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hτ
  rcases hτ with rfl | rfl
  · exact Finset.mem_biUnion.mpr ⟨false,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hd.1,hd⟩⟩
  · exact Finset.mem_biUnion.mpr ⟨true,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hd.1,hd⟩⟩

/-- Physical, unnormalized data for a single actual root-to-endpoint cache.
The probabilistic tests are discharged from the constructed ensemble below. -/
structure GeometricTrack (V : Type*) [MetricSpace V] (N : ℕ) (U J H Q : ℝ) where
  path : ReservationPath
  start : ℕ
  start_le : start ≤ path.last
  delta : ℕ → ℝ
  antitone : Antitone delta
  nonneg : ∀ t, 0 ≤ delta t
  start_pos : 0 < delta start
  end_zero : delta path.last = 0
  error : ℝ
  error_nonneg : 0 ≤ error
  size : ∀ t, (path.inclusive t).card ≤ N
  B : ℕ → Finset V
  D : ℕ → V → ℝ
  x : V
  at_x : ∀ t, D t x = delta t
  lipschitz : ∀ a u v, |D a u-D a v| ≤ dist u v
  launch : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → start ≤ a →
    delta a ≤ error+(U+1)*delta e
  small : ∀ a e, e ≤ path.last → a ∈ path.inclusive e → a < start →
    delta a ≤ H*delta start → delta start ≤ Q*(error+delta e)
  obstruction : ∀ a e t, e ≤ path.last → a ∈ path.inclusive e → a < start →
    start ≤ t → t < e → Q*(error+delta e) < delta t →
    ∃ p ∈ B t, ∃ q ∈ B t, dist x p = delta t ∧ delta t/4 ≤ dist p q ∧ dist p q ≤ 10*delta a
  protect_rule : ∀ t, t < path.last → ∀ b ∈ protectedEntries (B t) (path.inclusive t) dist
    (fun p a => D a p) J, t < path.finish b

namespace GeometricTrack
variable {V : Type*} [MetricSpace V] {N : ℕ} {U J H Q : ℝ}
  (P : GeometricTrack V N U J H Q)

lemma successor_protected (hU : 0 ≤ U) (hJ : J = 10*(U+4)) (hH : 10^5*J < H) (hQ : U+1 ≤ Q)
    (a e t b : ℕ) (he : e ≤ P.path.last) (ha : a ∈ P.path.inclusive e) (has : a < P.start)
    (hDa : H*P.delta P.start < P.delta a) (hst : P.start ≤ t) (hte : t < e)
    (hsb : P.start ≤ b) (hab : P.path.Successor a b t)
    (hgap : Q*(P.error+P.delta e) < P.delta t) : t < P.path.finish b := by
  classical
  have hQ1 : 1 ≤ Q := by linarith
  have hQ0 : 0 < Q := by linarith
  have hδ : 0 < P.delta t := lt_of_le_of_lt (mul_nonneg hQ0.le (add_nonneg P.error_nonneg (P.nonneg e))) hgap
  have hE : P.error < P.delta t := by
    have h1 := mul_le_mul_of_nonneg_right hQ1 (add_nonneg P.error_nonneg (P.nonneg e))
    nlinarith [P.nonneg e]
  obtain ⟨p,hp,q,hq,hxp,hLlo,hLhi⟩ := P.obstruction a e t he ha has hst hte hgap
  have hδA : P.delta t ≤ P.delta P.start := P.antitone hst
  have hdb : P.delta b ≤ P.delta P.start := P.antitone hsb
  have hbt : b ∈ P.path.inclusive t := (P.path.mem_inclusive (hte.le.trans he)).mpr hab.2.1
  have hl := P.launch b t (hte.le.trans he) hbt hsb
  have hbp := P.lipschitz b P.x p
  have hap := P.lipschitz a P.x p
  rw [P.at_x,hxp] at hbp hap
  have hbp' := (abs_le.mp hbp).1
  have hap' := (abs_le.mp hap).2
  have hyδ : P.D b p ≤ (U+3)*P.delta t := by nlinarith
  have hyA : P.D b p ≤ 2*P.delta P.start := by linarith
  have haA : P.delta a-P.delta P.start ≤ P.D a p := by linarith
  have hw := protected_threshold_scaled (U+3) J H (P.delta a) (P.delta t) (P.delta P.start)
    (dist p q) (P.D a p) (P.D b p) (by linarith) (by linarith) hH
    P.start_pos hDa hδ hδA hLlo hLhi hyδ hyA haA
  apply P.protect_rule t (hte.trans_le he) b
  apply protected_of_successor P.path (P.B t) (fun p a => P.D a p) dist J t a b
    (hte.le.trans he) hab p q hp hq _ hw
  intro heq; subst q; rw [dist_self] at hLlo; linarith

noncomputable def control (hU : 0 ≤ U) (hJ : J = 10*(U+4)) (hH : 10^5*J < H) (hQ : U+1 ≤ Q) :
    CacheControl N Q H where
  path := P.path
  start := P.start
  start_le := P.start_le
  delta := fun t => P.delta t/P.delta P.start
  antitone := fun _ _ h => div_le_div_of_nonneg_right (P.antitone h) P.start_pos.le
  nonneg := fun t => div_nonneg (P.nonneg t) P.start_pos.le
  at_start := div_self P.start_pos.ne'
  at_end := by rw [P.end_zero,zero_div]
  error := P.error/P.delta P.start
  error_nonneg := div_nonneg P.error_nonneg P.start_pos.le
  size := P.size
  launch := by
    intro a e he ha hs
    have hh := P.launch a e he ha hs
    have hq1 : 1 ≤ Q := by linarith
    have hb : P.error+(U+1)*P.delta e ≤ Q*(P.error+P.delta e) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hq1) P.error_nonneg,
        mul_nonneg (sub_nonneg.mpr hQ) (P.nonneg e)]
    have hd := div_le_div_of_nonneg_right (hh.trans hb) P.start_pos.le
    simpa only [mul_div_assoc,add_div] using hd
  distant := by
    intro a e he ha hs hd
    have hd' : P.delta a ≤ H*P.delta P.start := (div_le_iff₀ P.start_pos).mp hd
    have hh := div_le_div_of_nonneg_right (P.small a e he ha hs hd') P.start_pos.le
    rw [div_self P.start_pos.ne'] at hh
    simpa only [mul_div_assoc,add_div] using hh
  protect := by
    intro a e t b he ha hs hd hst hte hsb hab hgap
    have hd' : H*P.delta P.start < P.delta a := (lt_div_iff₀ P.start_pos).mp hd
    have hg : Q*(P.error+P.delta e) < P.delta t := by
      apply (div_lt_div_iff_of_pos_right P.start_pos).mp
      simpa only [mul_div_assoc,add_div] using hgap
    exact P.successor_protected hU hJ hH hQ a e t b he ha hs hd' hst hte hsb hab hg

end GeometricTrack
end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section

structure TestParameters (k : ℕ) (α π η H Q : ℝ) where
  c : ℝ
  b : ℝ
  c_eq : c = α/8*η
  c_pos : 0 < c
  c_half : c ≤ 1/2
  b_eq : b = c/(8*((k:ℝ)+1))
  b_pos : 0 < b
  b_one : b ≤ 1
  eta_pos : 0 < η
  eta_small : η < 1/4
  pi_pos : 0 < π
  pi_one : π ≤ 1
  radius : 4*η*H < 1
  qbound : 1+upper k+particleLip k ≤ (π/8*b)*Q
  qlarge : upper k+1 ≤ Q

variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

/-- All properties here are literal shortest-path/bag geometry. -/
structure PathGeometry where
  X : Fin (n+1)
  Y : Fin (n+1)
  x : V
  y : V
  start : ℕ
  start_le : start ≤ (forest T hT root).depth X
  hx : x ∈ B X
  hy : y ∈ B Y
  positive : 0 < D ((downPath T hT root X).getVert start) x
  nonneg : ∀ i v, 0 ≤ D i v
  lipschitz : ∀ i u v, |D i u-D i v| ≤ dist u v
  zero : ∀ i v, v ∈ B i → D i v = 0
  bounded : ∀ i v, D i v ≤ P.Δ
  bag_bound : ∀ i, (B i).card ≤ k
  monotone : Antitone (fun t => D ((downPath T hT root X).getVert t) x)
  near : ∀ t, ∃ p ∈ B ((downPath T hT root X).getVert t),
    dist x p = D ((downPath T hT root X).getVert t) x
  geodesic : ∀ a t, a ≤ t → t ≤ (forest T hT root).depth X →
    ∃ v ∈ B ((downPath T hT root X).getVert t),
      D ((downPath T hT root X).getVert a) v + dist x v = D ((downPath T hT root X).getVert a) x
  suffix : ∀ e, start ≤ e → e ≤ (forest T hT root).depth X → ∃ l,
    (forest T hT Y).depth ((downPath T hT root X).getVert e) = l+(e-start) ∧
    ∀ b, start ≤ b → b ≤ e →
      (downPath T hT Y ((downPath T hT root X).getVert e)).getVert (l+(b-start)) =
        (downPath T hT root X).getVert b

namespace PathGeometry
variable {P} (A : PathGeometry P)
abbrev node (t : ℕ) := (downPath T hT root A.X).getVert t
abbrev δ (t : ℕ) := D (A.node t) A.x
abbrev err := ‖P.map A.x-P.map A.y‖
abbrev cached (a e : ℕ) := a ∈ inclusiveCache k (bags T hT root B A.X) dist (heights T hT root D A.X) J e
lemma lower_near (t : ℕ) (v : V) (hv : v ∈ B (A.node t)) : A.δ t ≤ dist A.x v := by
  have hh := A.lipschitz (A.node t) A.x v
  rw [A.zero _ _ hv,sub_zero,abs_of_nonneg (A.nonneg _ _)] at hh
  exact hh
lemma proxy_upper (z : V) : ‖P.map A.y-P.map z‖ ≤ A.err+upper k*dist A.x z := by
  have hh := dist_triangle (P.map A.y) (P.map A.x) (P.map z)
  simp only [dist_eq_norm] at hh
  rw [norm_sub_rev (P.map A.y) (P.map A.x)] at hh
  have hu := P.upper_bound A.x z
  change ‖P.map A.y-P.map z‖ ≤ ‖P.map A.x-P.map A.y‖+upper k*dist A.x z
  linarith

lemma numerical_test {H Q : ℝ} (C : TestParameters k α π η H Q)
    (v d : ℝ) (hd : 0 ≤ d)
    (ht : (π/8)*(C.b*v-particleLip k*d) ≤ A.err+upper k*d) :
    v ≤ Q*(A.err+d) := by
  have hp : 0 < π/8*C.b := mul_pos (by linarith [C.pi_pos]) C.b_pos
  have hπ : 0 ≤ π/8 := by linarith [C.pi_pos]
  have hπ1 : π/8 ≤ 1 := by linarith [C.pi_one]
  have hL := particleLip_pos k
  have hU := upper_pos k
  have hE : 0 ≤ A.err := norm_nonneg _
  have hLπ : (π/8)*particleLip k ≤ particleLip k := mul_le_of_le_one_left hL.le hπ1
  have hm := mul_le_mul_of_nonneg_right C.qbound (add_nonneg hE hd)
  have he := mul_nonneg (add_nonneg hU.le hL.le) hE
  have hld := mul_le_mul_of_nonneg_right hLπ hd
  nlinarith

lemma trivial_test {H Q : ℝ} (C : TestParameters k α π η H Q) (e : ℕ) (he : e ≤ A.start) :
    A.δ A.start ≤ Q*(A.err+A.δ e) := by
  have hq : 1 ≤ Q := by linarith [C.qlarge,upper_pos k]
  have hm := mul_le_mul_of_nonneg_right hq (add_nonneg (norm_nonneg (P.map A.x-P.map A.y)) (A.nonneg (A.node e) A.x))
  have hd := A.monotone he
  nlinarith [norm_nonneg (P.map A.x-P.map A.y)]

lemma launch (a e : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (hsa : A.start ≤ a) : A.δ a ≤ A.err+(upper k+1)*A.δ e := by
  have hae : a ≤ e := inclusive_age k _ _ _ _ e a ha
  by_cases heq : a = e
  · subst a
    nlinarith [A.nonneg (A.node e) A.x, norm_nonneg (P.map A.x-P.map A.y),upper_pos k]
  obtain ⟨l,hlen,hpath⟩ := A.suffix e (hsa.trans hae) he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have ht := P.launch_test A.zero A.X A.Y A.y z A.hy A.start e l a he hsa (lt_of_le_of_ne hae heq) ha hz hlen hpath
  have hl := (abs_le.mp (A.lipschitz (A.node a) A.x z)).2
  have hu := A.proxy_upper z
  rw [hzdist] at hl hu
  change A.δ a-_ ≤ _ at hl
  linarith

lemma budget {H Q : ℝ} (C : TestParameters k α π η H Q)
    (v β γ : ℝ) (hv : 0 ≤ v) (hβ : 0 < β) (hγ : 0 < γ)
    (hvb : C.c*v ≤ β) (hvg : C.c*v ≤ γ) (t : ℕ) :
    ((B (A.node t)).card:ℝ)*(2*(C.b*v)/β+2*(C.b*v)/γ) ≤ 1/2 := by
  have hh := gap_budget k β γ (C.c*v) hβ hγ (mul_nonneg C.c_pos.le hv) hvb hvg
  have heq : C.c*v/(8*((k:ℝ)+1)) = C.b*v := by rw [C.b_eq]; ring
  rw [heq] at hh
  apply le_trans _ hh
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast A.bag_bound (A.node t)) (by positivity [C.b_pos])

lemma bounded_tau {H Q : ℝ} (C : TestParameters k α π η H Q) (t : ℕ) : C.b*A.δ t ≤ 2*P.Δ := by
  have hh := mul_le_mul_of_nonneg_right C.b_one (A.nonneg (A.node t) A.x)
  have hb := A.bounded (A.node t) A.x
  nlinarith [P.Δ_pos]

lemma small {H Q : ℝ} (C : TestParameters k α π η H Q)
    (a e : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (has : a < A.start) (hDa : A.δ a ≤ H*A.δ A.start) :
    A.δ A.start ≤ Q*(A.err+A.δ e) := by
  by_cases hes : e ≤ A.start
  · exact A.trivial_test C e hes
  have hse : A.start < e := lt_of_not_ge hes
  obtain ⟨l,hlen,hpath⟩ := A.suffix e hse.le he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have hAa : A.δ A.start ≤ A.δ a := A.monotone has.le
  have hapos : 0 < A.δ a := A.positive.trans_le hAa
  have hrad : 4*η*A.δ a < A.δ A.start := by
    have hm := mul_le_mul_of_nonneg_left hDa (show 0 ≤ 4*η by positivity [C.eta_pos])
    have hh := mul_lt_mul_of_pos_right C.radius A.positive
    nlinarith
  have hamp : ∀ loc, GoodBump (D (A.node a)) α η ((seed (A.node a)).bump loc) A.x →
      ∀ v ∈ B (A.node A.start), A.δ A.start ≤ |D (A.node a) A.x-D (A.node a) v| ∨
        ∃ j, C.c*A.δ a ≤ |(seed (A.node a)).bump loc j A.x-(seed (A.node a)).bump loc j v| := by
    intro loc hg v hv
    obtain ⟨j,hj,hn,hzero⟩ := hg
    right
    refine ⟨j,?_⟩
    rw [hzero v (hrad.trans_le (A.lower_near A.start v hv)),sub_zero,abs_of_nonneg (hn A.x)]
    simpa only [C.c_eq,mul_assoc] using hj
  have ht := P.height_test A.X A.Y A.x A.y z A.hy A.start e l a A.start he le_rfl hse has ha hz hlen hpath
    (C.b*A.δ A.start) (A.δ A.start) (C.c*A.δ a) (by positivity [C.b_pos,A.positive])
    (A.bounded_tau C A.start) A.positive (mul_pos C.c_pos hapos) C.pi_pos.le hapos hamp
    (A.budget C (A.δ A.start) (A.δ A.start) (C.c*A.δ a) A.positive.le A.positive (mul_pos C.c_pos hapos)
      (by nlinarith [C.c_half,A.positive]) (mul_le_mul_of_nonneg_left hAa C.c_pos.le) A.start)
  have hu := A.proxy_upper z
  rw [hzdist] at ht hu
  exact A.numerical_test C (A.δ A.start) (A.δ e) (A.nonneg _ _) (ht.trans hu)

lemma obstruction {H Q : ℝ} (C : TestParameters k α π η H Q)
    (a e t : ℕ) (he : e ≤ (forest T hT root).depth A.X) (ha : A.cached a e)
    (has : a < A.start) (hst : A.start ≤ t) (hte : t < e)
    (hgap : Q*(A.err+A.δ e) < A.δ t) :
    ∃ p ∈ B (A.node t), ∃ q ∈ B (A.node t), dist A.x p = A.δ t ∧
      A.δ t/4 ≤ dist p q ∧ dist p q ≤ 10*A.δ a := by
  have hQ : 0 < Q := by linarith [C.qlarge,upper_pos k]
  have hδ : 0 < A.δ t := lt_of_le_of_lt (mul_nonneg hQ.le (add_nonneg (norm_nonneg (P.map A.x-P.map A.y)) (A.nonneg _ _))) hgap
  have hDa : A.δ t ≤ A.δ a := A.monotone (has.le.trans hst)
  have hapos : 0 < A.δ a := hδ.trans_le hDa
  obtain ⟨p,hp,hpdist⟩ := A.near t
  by_contra hno
  have hno' : ∀ q ∈ B (A.node t), ¬(A.δ t/4 ≤ dist p q ∧ dist p q ≤ 10*A.δ a) := by
    intro q hq hh
    exact hno ⟨p,hp,q,hq,hpdist,hh⟩
  obtain ⟨v₀,hv₀,hgeo⟩ := A.geodesic a t (has.le.trans hst) (hte.le.trans he)
  have hamp : ∀ loc, GoodBump (D (A.node a)) α η ((seed (A.node a)).bump loc) A.x →
      ∀ v ∈ B (A.node t), A.δ t/2 ≤ |D (A.node a) A.x-D (A.node a) v| ∨
        ∃ j, C.c*A.δ a ≤ |(seed (A.node a)).bump loc j A.x-(seed (A.node a)).bump loc j v| := by
    intro loc hg v hv
    obtain ⟨j,hj,hn,hzero⟩ := hg
    have hj' : C.c*A.δ a ≤ (seed (A.node a)).bump loc j A.x := by simpa only [C.c_eq,mul_assoc] using hj
    have hr : 4*η*A.δ a < 9*A.δ a := by nlinarith [C.eta_small]
    have hh := near_far_scaled (B (A.node t)) A.x p v₀ (D (A.node a))
      ((seed (A.node a)).bump loc j) (A.δ t) (A.δ a) (4*η*A.δ a) (C.c*A.δ a)
      hδ hDa hpdist hv₀ (A.lower_near t) (A.lipschitz (A.node a)) rfl hgeo (A.nonneg _ _)
      hno' hr (mul_pos C.c_pos hapos) hj' hzero v hv
    exact hh.imp id (fun h => ⟨j,h⟩)
  obtain ⟨l,hlen,hpath⟩ := A.suffix e (hst.trans hte.le) he
  obtain ⟨z,hz,hzdist⟩ := A.near e
  have ht := P.height_test A.X A.Y A.x A.y z A.hy A.start e l a t he hst hte (has.trans_le hst) ha hz hlen hpath
    (C.b*A.δ t) (A.δ t/2) (C.c*A.δ a) (by positivity [C.b_pos])
    (A.bounded_tau C t) (by positivity) (mul_pos C.c_pos hapos) C.pi_pos.le hapos hamp
    (A.budget C (A.δ t) (A.δ t/2) (C.c*A.δ a) hδ.le (by positivity) (mul_pos C.c_pos hapos)
      (by nlinarith [C.c_half]) (mul_le_mul_of_nonneg_left hDa C.c_pos.le) t)
  have hu := A.proxy_upper z
  rw [hzdist] at ht hu
  exact (not_le_of_gt hgap) (A.numerical_test C (A.δ t) (A.δ e) (A.nonneg _ _) (ht.trans hu))

end PathGeometry
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

noncomputable def graphPath (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (hdist : ∀ u v, dist u v = shortestPathDistance G ℓ u v)
    (hne : ∀ i, (B i).Nonempty)
    (hD : ∀ i, D i = bagDistance G ℓ (B i) (hne i))
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (hbag : ∀ i, (B i).card ≤ k) (hbound : ∀ i v, D i v ≤ P.Δ)
    (X Y : Fin (n+1)) (x y : V) (hx : x ∈ B X) (hy : y ∈ B Y) (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s)
    (hpos : 0 < D ((downPath T hT root X).getVert s) x) : PathGeometry P := by
  let q := downPath T hT root X
  have hgeo (a t : ℕ) (hat : a ≤ t) :
      D (q.getVert t) x ≤ D (q.getVert a) x ∧
      ∃ v ∈ B (q.getVert t), D (q.getVert a) v+dist x v = D (q.getVert a) x := by
    have hp : q.getVert t ∈ (q.drop a).support := by
      simpa only [SimpleGraph.Walk.drop_getVert,Nat.add_sub_of_le hat] using (q.drop a).getVert_mem_support (t-a)
    have hh := separator_bag_geometry G ℓ hG hℓ T B hne hT hedge hrun (q.drop a)
      ((downPath_isPath T hT root X).drop a) hp hx
    rw [hD,hD]
    refine ⟨hh.1,?_⟩
    obtain ⟨v,hv,hhv⟩ := hh.2
    refine ⟨v,hv,?_⟩
    rw [hdist,shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le) x v]
    exact hhv
  refine {
    X := X, Y := Y, x := x, y := y, start := s, start_le := hsx, hx := hx, hy := hy,
    positive := hpos, bounded := hbound, bag_bound := hbag
    nonneg := ?_, lipschitz := ?_, zero := ?_, monotone := ?_, near := ?_, geodesic := ?_, suffix := ?_ }
  · intro i v
    rw [hD]
    exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro i u v
    rw [hD,hdist]
    exact bagDistance_lipschitz G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) u v
  · intro i v hv
    rw [hD]
    apply le_antisymm
    · have hh := bagDistance_le G ℓ (B i) (hne i) v hv
      rw [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)] at hh
      exact hh
    · exact bagDistance_nonneg G ℓ hG (fun e => (hℓ e).le) (B i) (hne i) v
  · intro a t hat
    exact (hgeo a t hat).1
  · intro t
    obtain ⟨p,hp,hpdist⟩ := bagDistance_attained G ℓ (B (q.getVert t)) (hne _) x
    exact ⟨p,hp,by rw [hD,hdist]; exact hpdist.symm⟩
  · intro a t hat ht
    exact (hgeo a t hat).2
  · intro e hse he
    exact ⟨(forest T hT root).depth Y-s,join_prefix_data T hT root X Y s hsx hsy hs hmax e hse he⟩

namespace PathGeometry
variable {P} (A : PathGeometry P)
noncomputable def track {H Q : ℝ} (C : TestParameters k α π η H Q)
    (R : ReservationPath) (hR : R.last = (forest T hT root).depth A.X)
    (hcache : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
      (heights T hT root D A.X) J t)
    (hsize : ∀ t, (R.inclusive t).card ≤ cacheBound k+1)
    (hprotect : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
      (fun p a => D (A.node a) p) J, t < R.finish b) :
    GeometricTrack V (cacheBound k+1) (upper k) J H Q where
  path := R
  start := A.start
  start_le := by rw [hR]; exact A.start_le
  delta := A.δ
  antitone := A.monotone
  nonneg := fun t => A.nonneg _ _
  start_pos := A.positive
  end_zero := by
    change D ((downPath T hT root A.X).getVert R.last) A.x = 0
    rw [hR,← downPath_length,SimpleGraph.Walk.getVert_length]
    exact A.zero A.X A.x A.hx
  error := A.err
  error_nonneg := norm_nonneg _
  size := hsize
  B := fun t => B (A.node t)
  D := fun t => D (A.node t)
  x := A.x
  at_x := fun _ => rfl
  lipschitz := fun a => A.lipschitz (A.node a)
  launch := by
    intro a e he ha hs
    rw [hcache e he] at ha
    exact A.launch a e (by rwa [← hR]) ha hs
  small := by
    intro a e he ha hs hd
    rw [hcache e he] at ha
    exact A.small C a e (by rwa [← hR]) ha hs hd
  obstruction := by
    intro a e t he ha hs hst hte hg
    rw [hcache e he] at ha
    exact A.obstruction C a e t (by rwa [← hR]) ha hs hst hte hg
  protect_rule := hprotect

lemma lower_of_track {H Q : ℝ} (C : TestParameters k α π η H Q)
    (hJ : J = 10*(upper k+4)) (hH : 10^5*J < H)
    (c : ℝ) (hc : ∀ CC : CacheControl (cacheBound k+1) Q H, c ≤ CC.error)
    (R : ReservationPath) (hR : R.last = (forest T hT root).depth A.X)
    (hcache : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
      (heights T hT root D A.X) J t)
    (hsize : ∀ t, (R.inclusive t).card ≤ cacheBound k+1)
    (hprotect : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
      (fun p a => D (A.node a) p) J, t < R.finish b) :
    c*A.δ A.start ≤ A.err := by
  let QP := A.track C R hR hcache hsize hprotect
  have hh := hc (QP.control (upper_pos k).le hJ hH C.qlarge)
  change c ≤ A.err/A.δ A.start at hh
  exact (le_div_iff₀ A.positive).mp hh
end PathGeometry
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
noncomputable section

theorem test_parameters_exist (k : ℕ) (α π : ℝ) (hα : 0 < α) (hα1 : α ≤ 1/8)
    (hπ : 0 < π) (hπ1 : π ≤ 1) :
    ∃ J H η Q : ℝ, J = 10*(upper k+4) ∧ 10^5*J < H ∧
      Nonempty (TestParameters k α π η H Q) := by
  let J := 10*(upper k+4)
  let H := 10^5*J+1
  have hU := upper_pos k
  have hL := particleLip_pos k
  have hJ : 0 < J := by dsimp [J]; positivity
  have hH : 1 < H := by dsimp [H]; nlinarith
  let η := 1/(16*H)
  have hη : 0 < η := by dsimp [η]; positivity
  have hη4 : η < 1/4 := by
    dsimp [η]; apply (div_lt_div_iff₀ (by positivity) (by norm_num)).mpr; nlinarith
  have hr : 4*η*H < 1 := by
    have hH0 : H ≠ 0 := by linarith
    dsimp [η]; field_simp; norm_num
  let c := α/8*η
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c ≤ 1/2 := by
    have hαη := mul_le_mul_of_nonneg_right hα1 hη.le
    dsimp [c]; nlinarith
  let b := c/(8*((k:ℝ)+1))
  have hb : 0 < b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by
    dsimp [b]; apply (div_le_iff₀ (by positivity)).mpr
    nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)]
  let w := π/8*b
  have hw : 0 < w := by dsimp [w]; positivity
  let Q := (1+upper k+particleLip k)/w+(upper k+1)
  have hQ : upper k+1 ≤ Q := by
    dsimp [Q]; have hh : 0 ≤ (1+upper k+particleLip k)/w := by positivity
    linarith
  have hbound : 1+upper k+particleLip k ≤ (π/8*b)*Q := by
    have hh : w*((1+upper k+particleLip k)/w) = 1+upper k+particleLip k :=
      mul_div_cancel₀ _ hw.ne'
    change _ ≤ w*Q
    dsimp only [Q]
    nlinarith [mul_nonneg hw.le (show 0 ≤ upper k+1 by positivity)]
  refine ⟨J,H,η,Q,rfl,by dsimp [H]; linarith,⟨?_⟩⟩
  exact {
    c := c, b := b, c_eq := rfl, c_pos := hc, c_half := hc2,
    b_eq := rfl, b_pos := hb, b_one := hb1, eta_pos := hη, eta_small := hη4,
    pi_pos := hπ, pi_one := hπ1, radius := hr, qbound := hbound, qlarge := hQ }
end
end BoundedTreewidthL1.AnchorExperiment

namespace BoundedTreewidthL1.AnchorExperiment
open MeasureTheory LaunchNoise AnchorTreeParticles TreeCache AnchorCache
open BoundedTreewidthL1.RootedTree
attribute [local instance 2000] Classical.decEq
attribute [local instance] Classical.propDecidable
noncomputable section
variable {V : Type*} [Fintype V] [MetricSpace V] {n : ℕ}
variable {T : SimpleGraph (Fin (n+1))} {hT : T.IsTree} {root : Fin (n+1)}
  {B : Fin (n+1) → Finset V} {D : Fin (n+1) → V → ℝ} {k : ℕ} {J α π η : ℝ}
  {seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η}
  {cover : ∀ v, ∃ i, v ∈ B i} {run : ∀ v, (T.induce {i | v ∈ B i}).Preconnected}
  (P : Model T hT root B D k J α π η seed cover run)

lemma Model.join_lower (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (hdist : ∀ u v, dist u v = shortestPathDistance G ℓ u v)
    (hne : ∀ i, (B i).Nonempty)
    (hD : ∀ i, D i = bagDistance G ℓ (B i) (hne i))
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Connected)
    (hbag : ∀ i, (B i).card ≤ k) (hbound : ∀ i v, D i v ≤ P.Δ)
    {H Q : ℝ} (C : TestParameters k α π η H Q)
    (hJ : J = 10*(upper k+4)) (hH : 10^5*J < H)
    (c : ℝ) (hc0 : 0 ≤ c) (hc : ∀ CC : CacheControl (cacheBound k+1) Q H, c ≤ CC.error)
    (X Y : Fin (n+1)) (x y : V) (hx : x ∈ B X) (hy : y ∈ B Y) (s : ℕ)
    (hsx : s ≤ (forest T hT root).depth X) (hsy : s ≤ (forest T hT root).depth Y)
    (hs : (downPath T hT root X).getVert s = (downPath T hT root Y).getVert s)
    (hmax : ∀ a b, a ≤ (forest T hT root).depth X → b ≤ (forest T hT root).depth Y →
      (downPath T hT root X).getVert a = (downPath T hT root Y).getVert b → a = b ∧ a ≤ s) :
    c*D ((downPath T hT root X).getVert s) x ≤ ‖P.map x-P.map y‖ := by
  by_cases hp : 0 < D ((downPath T hT root X).getVert s) x
  · let A := graphPath P G hG ℓ hℓ hdist hne hD hedge hrun hbag hbound X Y x y hx hy s hsx hsy hs hmax hp
    obtain ⟨R,hR,hcache,hsize,hprotect⟩ := graph_cache_realizes G ℓ hG hℓ T B hne hT hedge hrun k hbag J
      (downPath T hT root X) (downPath_isPath T hT root X)
    have hR' : R.last = (forest T hT root).depth A.X := hR.trans (downPath_length T hT root X)
    have hdF : dist = shortestPathDistance G ℓ := funext (fun u => funext (hdist u))
    have hDF : D = fun i => bagDistance G ℓ (B i) (hne i) := funext hD
    have hcache' : ∀ t ≤ R.last, R.inclusive t = inclusiveCache k (bags T hT root B A.X) dist
        (heights T hT root D A.X) J t := by
      intro t ht
      change R.inclusive t = inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J t
      rw [hdF,hDF]
      exact hcache t (by rwa [← hR])
    have hprotect' : ∀ t, t < R.last → ∀ b ∈ protectedEntries (B (A.node t)) (R.inclusive t) dist
        (fun p a => D (A.node a) p) J, t < R.finish b := by
      intro t ht b hb
      apply hprotect t (by rwa [← hR]) b
      rw [hcache' t ht.le] at hb
      change b ∈ protectedEntries (B ((downPath T hT root X).getVert t))
        (inclusiveCache k (bags T hT root B X) dist (heights T hT root D X) J t) dist
        (fun p a => D ((downPath T hT root X).getVert a) p) J at hb
      rw [hdF,hDF] at hb
      exact hb
    exact A.lower_of_track C hJ hH c hc R hR' hcache' hsize hprotect'
  · exact (mul_nonpos_of_nonneg_of_nonpos hc0 (le_of_not_gt hp)).trans (norm_nonneg _)

/-- The constructed anchor ensemble controls BOTH distances to one actual common
bag. This is enough for all-pairs lower comparison when combined with co-bag
separation, and involves no assumed contraction/Markov-flow theorem. -/
theorem anchor_common_bag_embedding (k : ℕ) (hk : 2 ≤ k) :
    ∃ U c : ℝ, 0 < U ∧ 0 < c ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (_ : G.Connected) (ℓ : G.edgeSet → ℝ) (_ : ∀ e, 0 < ℓ e)
      (n : ℕ) (T : SimpleGraph (Fin (n+1))) (_ : T.IsTree) (_ : Fin (n+1))
      (B : Fin (n+1) → Finset V) (hne : ∀ i, (B i).Nonempty)
      (_ : ∀ v, ∃ i, v ∈ B i)
      (_ : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
      (_ : ∀ v, (T.induce {i | v ∈ B i}).Connected)
      (_ : ∀ i, (B i).card ≤ k),
      ∃ m : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ),
        (∀ x y, ‖Φ x-Φ y‖ ≤ U*shortestPathDistance G ℓ x y) ∧
        ∀ x y, ∃ i, c*bagDistance G ℓ (B i) (hne i) x ≤ ‖Φ x-Φ y‖ ∧
          c*bagDistance G ℓ (B i) (hne i) y ≤ ‖Φ x-Φ y‖ := by
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_ordinary_noise k hk
  obtain ⟨J,H,η,Q,hJ,hH,⟨C⟩⟩ := test_parameters_exist k α π hα hα8 hπ hπ1
  have hQ : 0 < Q := by linarith [C.qlarge,upper_pos k]
  obtain ⟨c,hc,hccontrol⟩ := CacheControl.uniform_lower (cacheBound k+1) Q H hQ
  refine ⟨upper k,c,upper_pos k,hc,?_⟩
  intro V _ _ _ G hG ℓ hℓ n T hT root B hne hcover hedge hrun hbag
  let := weightedMetricSpace G ℓ hG hℓ
  let D := fun i => bagDistance G ℓ (B i) (hne i)
  have hdec : HasTreeDecomposition G k := ⟨n+1,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hnoise (i : Fin (n+1)) : HasOrdinaryNoise (D i) α π η := by
    have hn := hsampler V G hG hdec ℓ hℓ (B i : Set V) (hne i) η C.eta_pos C.eta_small
    have heq : D i = fun x => Metric.infDist x (B i : Set V) := by
      funext x
      exact bagDistance_eq_infDist G hG ℓ hℓ (B i) (hne i) x
    rw [heq]
    exact hn
  let seed : (i : Fin (n+1)) → OrdinarySeed (D i) α π η :=
    fun i => Classical.choice (OrdinarySeed.exists_of_has (hnoise i))
  obtain ⟨P,hbound⟩ := model_exists G hG ℓ hℓ T hT root B hne hcover hedge hrun k hbag J α π η seed
  refine ⟨P.dim,P.map,P.upper_bound,?_⟩
  intro x y
  obtain ⟨X,hx⟩ := hcover x
  obtain ⟨Y,hy⟩ := hcover y
  obtain ⟨s,hsx,hsy,hs,hmax⟩ := exists_join_index T hT root X Y
  refine ⟨(downPath T hT root X).getVert s,?_,?_⟩
  · exact P.join_lower G hG ℓ hℓ (fun _ _ => rfl) hne (fun _ => rfl) hedge hrun hbag hbound
      C hJ hH c hc.le hccontrol X Y x y hx hy s hsx hsy hs hmax
  · have hm : ∀ a b, a ≤ (forest T hT root).depth Y → b ≤ (forest T hT root).depth X →
        (downPath T hT root Y).getVert a = (downPath T hT root X).getVert b → a = b ∧ a ≤ s := by
      intro a b ha hb he
      obtain ⟨hab,hbs⟩ := hmax b a hb ha he.symm
      exact ⟨hab.symm,hab ▸ hbs⟩
    have hh := P.join_lower G hG ℓ hℓ (fun _ _ => rfl) hne (fun _ => rfl) hedge hrun hbag hbound
      C hJ hH c hc.le hccontrol Y X y x hy hx s hsy hsx hs.symm hm
    rw [norm_sub_rev,← hs] at hh
    exact hh
end
end BoundedTreewidthL1.AnchorExperiment

end OAI
end
end

section
section
namespace OAI


namespace BoundedTreewidthL1.ParticleLaws
open MeasureTheory
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable
variable {V I J : Type*} [Fintype V] [Fintype I] [Fintype J] [DecidableEq V]

end BoundedTreewidthL1.ParticleLaws

namespace BoundedTreewidthL1.TreeParticles
variable {I J X : Type*} [DecidableEq J]
attribute [local instance] Classical.propDecidable

/-- The discrete launch location depends only on the rooted decomposition and
active keys. In particular it does not consult any preparatory randomness. -/
noncomputable def origin (R : RootedForest I) (A : I → Finset J) (root : I) : I → J → I :=
  R.run (fun _ => root) (fun i old a => if a ∈ retained R A i then old a else i)

lemma origin_eq (R : RootedForest I) (A : I → Finset J) (root i : I) (a : J) :
    origin R A root i a = if a ∈ retained R A i then
      ((R.parent i).elim (fun _ => root) (origin R A root)) a else i := by
  unfold origin
  rw [RootedForest.run_eq]

lemma origin_fresh (R : RootedForest I) (A : I → Finset J) (root i : I)
    (a : J) (ha : a ∈ A i) : a ∈ fresh R A (origin R A root i a) := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A p := (Finset.mem_inter.mp (by simpa [retained,hp] using hk)).2
        exact ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p hap rfl
    · rw [ite_eq_right hk]
      exact Finset.mem_sdiff.mpr ⟨ha,hk⟩

lemma origin_transport (R : RootedForest I) (A : I → Finset J) (root : I)
    (E : I → J → X)
    (hkeep : ∀ i p, R.parent i = some p → ∀ a ∈ A i ∩ A p, E i a = E p a)
    (i : I) (a : J) (ha : a ∈ A i) : E i a = E (origin R A root i a) a := by
  induction hn : R.depth i using Nat.strong_induction_on generalizing i with
  | h n ih =>
    rw [origin_eq]
    by_cases hk : a ∈ retained R A i
    · rw [ite_eq_left hk]
      cases hp : R.parent i with
      | none => simp [retained,hp] at hk
      | some p =>
        simp only [Option.elim_some]
        have hap : a ∈ A i ∩ A p := by simpa [retained,hp] using hk
        exact (hkeep i p hp a hap).trans
          (ih (R.depth p) (by rw [← hn]; exact R.decreases i p hp) p
            (Finset.mem_inter.mp hap).2 rfl)
    · rw [ite_eq_right hk]
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open scoped BigOperators
variable {I V ι J : Type*} [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq ι] [DecidableEq J]

lemma two_particle_difference
    {V : Type treewidthLevel1} {ι : Type treewidthLevel2} [Fintype V] [Fintype ι] [Nonempty ι]
    [DecidableEq ι]
    (F : ι → V → ℝ) (a b : ι) (hab : a ≠ b)
    (g : V → ℝ) (hgap : ∀ v, F a v - F b v = 2*g v) (u v : V) :
    2*|g u-g v| ≤ ∑ t, |F t u-F t v| := by
  have hs : (∑ t ∈ ({a,b} : Finset ι), |F t u-F t v|) ≤ ∑ t, |F t u-F t v| :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun t _ _ => abs_nonneg _)
  simp only [Finset.sum_pair hab] at hs
  have he : (F a u-F a v)-(F b u-F b v) = 2*(g u-g v) := by
    linarith [hgap u,hgap v]
  have ha := abs_sub (F a u-F a v) (F b u-F b v)
  rw [he,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)] at ha
  exact ha.trans hs

/-- The actual active pair at any descendant supplies the original launch
separation. The origin is deterministic, so no conditioning on the particle
scheduler or sampled coefficients is required. -/
theorem origin_particle_gap (R : RootedForest I) (root : I) (bag : I → Finset V)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (bag i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (d : V → V → ℝ) (L H Δ : ℝ) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : I → J → V → ℝ)
    (hLip : ∀ i a, ∀ u v, |g i a u - g i a v| ≤ L*d u v)
    (hHeight : ∀ i a v, |g i a v| ≤ H)
    (hzero : ∀ i a, ∀ v ∈ interface R bag i, g i a v = 0)
    (i : I) (a : J) (ha : a ∈ A i) (u v : V) :
    2*|g (origin R A root i a) a u - g (origin R A root i a) a v| ≤
      ∑ t, |(state (ι := ι) R bag A g i).1 t u -
        (state (ι := ι) R bag A g i).1 t v| := by
  let S := state (ι := ι) R bag A g
  let o := origin R A root i a
  obtain ⟨hreach,htrace,hkeep,hnew⟩ := forest_particle_realization R bag A k q
    hbag hA hN d L H Δ hH hΔ g hLip hHeight hzero
  have hp : (S i).2 a = (S o).2 a :=
    origin_transport R A root (fun i a => (S i).2 a)
      (fun i p hip a ha => (hkeep i p hip a ha).1) i a ha
  have hl : (S i).1 ((S i).2 a).1 = (S o).1 ((S o).2 a).1 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).1)
      (fun i p hip a ha => (hkeep i p hip a ha).2.1) i a ha
  have hr : (S i).1 ((S i).2 a).2 = (S o).1 ((S o).2 a).2 :=
    origin_transport R A root (fun i a => (S i).1 ((S i).2 a).2)
      (fun i p hip a ha => (hkeep i p hip a ha).2.2) i a ha
  have hn := hnew o a (origin_fresh R A root i a ha)
  apply two_particle_difference (S i).1 ((S i).2 a).1 ((S i).2 a).2
    (by rw [hp]; exact hn.1) (g o a) ?_ u v
  intro x
  rw [hl,hr]
  exact hn.2 x
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.TreeParticles
open MeasureTheory ParticleLaws
open scoped BigOperators ENNReal
variable {I V ι J Ω : Type*} [Fintype I] [Fintype V] [Fintype ι] [Nonempty ι]
  [DecidableEq V] [DecidableEq ι] [DecidableEq J] [Fintype J] [MeasurableSpace Ω]

/-- Actual global averaged L1 realization of the branching preparation, with
an unconditional integral lower bound from each deterministic active origin. -/
theorem averaged_origin_realization
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    (T : SimpleGraph I) (hT : T.IsTree) (root : I) (B : I → Finset V)
    (hcover : ∀ v, ∃ i, v ∈ B i)
    (hedge : ∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i)
    (hrun : ∀ v, (T.induce {i | v ∈ B i}).Preconnected)
    (A : I → Finset J) (k q : ℕ) (hbag : ∀ i, (B i).card ≤ k)
    (hA : ∀ i, (A i).card ≤ q) (hN : Fintype.card ι = 2*q + k.factorial + 2)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (L H Δ : ℝ) (hL : 0 < L) (hH : 0 < H) (hΔ : 0 < Δ)
    (g : Ω → I → J → V → ℝ) (hmeas : ∀ i a v, Measurable (fun ω => g ω i a v))
    (hLip : ∀ ω i a, ∀ u v, |g ω i a u - g ω i a v| ≤ L*shortestPathDistance G ℓ u v)
    (hHeight : ∀ ω i a v, |g ω i a v| ≤ H)
    (hzero : ∀ ω i a, ∀ v ∈ interface (RootedTree.forest T hT root) B i, g ω i a v = 0) :
    ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
      (∀ u v, ‖Φ u - Φ v‖ ≤
        (Fintype.card ι : ℝ)*L*((Fintype.card ι : ℝ)-1)*shortestPathDistance G ℓ u v) ∧
      ∀ i (a : J), a ∈ A i → ∀ (u v : B i),
        2*(∫ ω, |g ω (origin (RootedTree.forest T hT root) A root i a) a u -
          g ω (origin (RootedTree.forest T hT root) A root i a) a v| ∂ν) ≤
          ‖Φ u.val - Φ v.val‖ := by
  classical
  let : MeasurableSpace ι := ⊤
  let : MeasurableSingletonClass ι := ⟨fun _ => trivial⟩
  let R := RootedTree.forest T hT root
  let S := fun ω => state (ι := ι) R B A (g ω)
  let M := H*((Fintype.card ι : ℝ)-1)+2*Δ
  have hreach : ∀ ω i, FunctionParticleReachable (shortestPathDistance G ℓ) L H (S ω i).1 := by
    intro ω
    exact (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).1
  have hsmeas : ∀ i t v, Measurable (fun ω => (S ω i).1 t v) := by
    intro i t v
    exact (measurable_pi_apply v).comp ((measurable_pi_apply t).comp
      (measurable_state R B A g hmeas i).fst)
  have hcons : ∀ ω i j, T.Adj i j →
      particleTrace M (S ω i).1 (B i ∩ B j) = particleTrace M (S ω j).1 (B i ∩ B j) := by
    intro ω i j hij
    have ht := (forest_particle_realization R B A k q hbag hA hN
      (shortestPathDistance G ℓ) L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω)).2.1
    rcases RootedTree.edge_orientation T hT root hij with hp | hp
    · exact trace_eq_of_subset M _ _ (B j) _ Finset.inter_subset_right (ht i j hp)
    · exact (trace_eq_of_subset M _ _ (B i) _ Finset.inter_subset_left (ht j i hp)).symm
  obtain ⟨n,Φ,hup,heq⟩ := averaged_particle_realization G hG ℓ hℓ T hT B hcover hedge hrun
    ν L H Δ hL hH hΔ (by omega : 1 ≤ Fintype.card ι) (fun ω i => (S ω i).1)
    hsmeas (by
      have hd : (Classical.decEq ι) = (inferInstance : DecidableEq ι) := Subsingleton.elim _ _
      rw [hd]
      exact hreach) hcons
  refine ⟨n,Φ,hup,?_⟩
  intro i a ha u v
  rw [heq i u v,← integral_const_mul]
  apply integral_mono
  · apply Integrable.const_mul
    apply Integrable.of_bound ((hmeas _ a u).sub (hmeas _ a v)).abs.aestronglyMeasurable (2*H)
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := hHeight ω (origin R A root i a) a u
    have hv := hHeight ω (origin R A root i a) a v
    exact (abs_sub _ _).trans (by linarith)
  · apply integrable_finsetSum
    intro t ht
    apply Integrable.of_bound ((hsmeas i t u).sub (hsmeas i t v)).abs.aestronglyMeasurable
      (2*H*((Fintype.card ι : ℝ)-1))
    apply Filter.Eventually.of_forall
    intro ω
    rw [Real.norm_eq_abs,abs_abs]
    have hu := function_particles_height_bound hH (hreach ω i) t u
    have hv := function_particles_height_bound hH (hreach ω i) t v
    exact (abs_sub _ _).trans (by linarith)
  · intro ω
    exact origin_particle_gap R root B A k q hbag hA hN (shortestPathDistance G ℓ)
      L H Δ hH hΔ (g ω) (hLip ω) (hHeight ω) (hzero ω) i a ha u v
end BoundedTreewidthL1.TreeParticles

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Set
open scoped unitInterval

theorem uniform_coefficient_integral_lower (a b : ℝ) :
    a/4 ≤ ∫ t : I, |a * (t : ℝ) - b| := by
  rw [unitInterval.measurePreserving_coe.integral_comp
    unitInterval.measurableEmbedding_coe (fun t : ℝ => |a*t-b|)]
  change a/4 ≤ ∫ t in Icc (0:ℝ) 1, |a*t-b|
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hi : ∀ x y : ℝ, IntervalIntegrable (fun t : ℝ => |a*t-b|) volume x y :=
    fun _ _ => (by fun_prop : Continuous (fun t : ℝ => |a*t-b|)).intervalIntegrable _ _
  have hl := intervalIntegral.integral_mono_on (by norm_num : (0:ℝ) ≤ 1/2)
    ((by fun_prop : Continuous (fun t : ℝ => b-a*t)).intervalIntegrable _ _)
    (hi 0 (1/2)) (fun t _ => by simpa only [neg_sub] using neg_le_abs (a*t-b))
  have hr := intervalIntegral.integral_mono_on (by norm_num : (1/2:ℝ) ≤ 1)
    ((by fun_prop : Continuous (fun t : ℝ => a*t-b)).intervalIntegrable _ _)
    (hi (1/2) 1) (fun t _ => le_abs_self (a*t-b))
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi 0 (1/2)) (hi (1/2) 1)
  have hli : (∫ t : ℝ in (0:ℝ)..(1/2:ℝ), b-a*t) = b/2-a/8 := by
    rw [intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  have hri : (∫ t : ℝ in (1/2:ℝ)..1, a*t-b) = 3*a/8-b/2 := by
    rw [intervalIntegral.integral_sub
      ((by fun_prop : Continuous (fun t : ℝ => a*t)).intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_id]
    simp
    ring
  rw [hli] at hl
  rw [hri] at hr
  linarith
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open Metric MeasureTheory
open scoped unitInterval
variable {V J : Type*} [MetricSpace V] [Fintype J]

noncomputable def cobagBump (A E : Set V) (r : ℝ) (x : V) : ℝ := by
  classical
  exact if A.Nonempty then min (infDist x A) (bump E r x) else bump E r x
noncomputable def cobagNoise (A : Set V) (E : J → Set V) (r : ℝ)
    (U : J → ℝ) (x : V) : ℝ := ∑ i, U i * cobagBump A (E i) r x

lemma cobagBump_eq_diff (A E : Set V) (r : ℝ) (x : V) :
    cobagBump A E r x = bump (E \ A) r x := by
  classical
  by_cases hA : A.Nonempty
  · have hd : (E \ A)ᶜ.Nonempty := by
      obtain ⟨a, ha⟩ := hA
      exact ⟨a, fun h => h.2 ha⟩
    by_cases hE : Eᶜ.Nonempty
    · have hi : infDist x (E \ A)ᶜ = min (infDist x Eᶜ) (infDist x A) := by
        have he : (E \ A)ᶜ = Eᶜ ∪ A := by ext z; simp; tauto
        rw [he, infDist, infEDist_union, ENNReal.toReal_min (infEDist_ne_top hE)
          (infEDist_ne_top hA)]
        rfl
      simp only [cobagBump, hA, ↓reduceIte, bump, hE, hd, hi]
      simp only [min_left_comm, min_comm]
    · have he : E = Set.univ := by
        apply Set.eq_univ_of_forall
        intro z
        by_contra hz
        exact hE ⟨z, hz⟩
      have hec : (Set.univ \ A : Set V)ᶜ = A := by ext z; simp
      simp [cobagBump, hA, bump, he, hec, min_comm]
  · have he : A = ∅ := Set.not_nonempty_iff_eq_empty.mp hA
    simp [cobagBump, he]

lemma cobagNoise_eq_diff (A : Set V) (E : J → Set V) (r : ℝ) (U : J → ℝ) :
    cobagNoise A E r U = noise (fun i => E i \ A) (fun _ => r) U := by
  funext x
  simp [cobagNoise, noise, cobagBump_eq_diff]

lemma cobag_diff_disjoint
    {V : Type treewidthLevel1} {J : Type treewidthLevel2} [MetricSpace V] [Fintype J]
    (A : Set V) (E : J → Set V)
    (hE : Pairwise (fun i j => Disjoint (E i) (E j))) :
    Pairwise (fun i j => Disjoint (E i \ A) (E j \ A)) :=
  fun _ _ hij => (hE hij).mono Set.sdiff_subset Set.sdiff_subset

theorem cobag_partition_properties (A : Set V) (E : J → Set V) (r : ℝ)
    (hr : 0 ≤ r) (hE : Pairwise (fun i j => Disjoint (E i) (E j)))
    (hcover : ∀ x, ∃ i, x ∈ E i) (U : J → ℝ) (hU : ∀ i, 0 ≤ U i ∧ U i ≤ 1) :
    LipschitzWith 1 (cobagNoise A E r U) ∧
    (∀ x, 0 ≤ cobagNoise A E r U x ∧ cobagNoise A E r U x ≤ r) ∧
    (∀ x ∈ A, cobagNoise A E r U x = 0) := by
  rw [cobagNoise_eq_diff]
  have h := disjoint_noise (fun i => E i \ A) (fun _ => r) U
    (cobag_diff_disjoint A E hE) (fun _ => hr) hU
  refine ⟨h.1, fun x => ⟨h.2.1 x, ?_⟩, ?_⟩
  · by_cases hx : x ∈ A
    · rw [h.2.2.2 x (fun i h => h.2 hx)]
      exact hr
    · obtain ⟨i, hi⟩ := hcover x
      exact h.2.2.1 i x ⟨hi,hx⟩
  · intro x hx
    exact h.2.2.2 x (fun i h => h.2 hx)

lemma cobagBump_bounds (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) :
    0 ≤ cobagBump A E r x ∧ cobagBump A E r x ≤ r := by
  rw [cobagBump_eq_diff]
  exact bump_bounds _ _ hr _

lemma cobagBump_zero (A E : Set V) (r : ℝ) (hr : 0 ≤ r) (x : V) (hx : x ∉ E) :
    cobagBump A E r x = 0 := by
  rw [cobagBump_eq_diff]
  exact bump_zero _ _ hr _ (fun h => hx h.1)

lemma cobagBump_padding (A E : Set V) (r a : ℝ) (x : V)
    (har : a ≤ r) (hball : ball x a ⊆ E) (hA : A.Nonempty → a ≤ infDist x A) :
    a ≤ cobagBump A E r x := by
  classical
  unfold cobagBump
  split_ifs with hne
  · exact le_min (hA hne) (bump_padding E r x a har hball)
  · exact bump_padding E r x a har hball

lemma coefficient_affine_integral_lower {m : ℕ} (j : Fin (m+1))
    (a : Fin (m+1) → ℝ) :
    a j / 4 ≤ ∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ) * a i| := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => I) j
  let f : I × (Fin m → I) → ℝ := fun z =>
    |(z.1:ℝ)*a j + ∑ i, (z.2 i:ℝ)*a (j.succAbove i)|
  have hc : Continuous f := by unfold f; fun_prop
  have hi : Integrable f := hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  have he : (∫ U : Fin (m+1) → I, |∑ i, (U i:ℝ)*a i|) = ∫ z, f z := by
    have hh := (volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => I) j).integral_comp
      e.measurableEmbedding f
    convert hh using 1
    apply integral_congr_ae
    filter_upwards [] with U
    congr 1
    exact Fin.sum_univ_succAbove (fun i => (U i:ℝ)*a i) j
  rw [he]
  change a j / 4 ≤ ∫ z, f z ∂(volume.prod volume)
  rw [integral_prod_symm f hi]
  have hb (U : Fin m → I) : a j/4 ≤ ∫ t : I, f (t,U) := by
    convert uniform_coefficient_integral_lower (a j)
      (-(∑ i, (U i:ℝ)*a (j.succAbove i))) using 1
    congr 1
    funext t
    simp [f, mul_comm, sub_neg_eq_add]
  have hm := integral_mono (integrable_const (a j/4)) hi.integral_prod_right hb
  simpa using hm

theorem cobag_partition_averaging {m : ℕ} (A : Set V)
    (E : Fin (m+1) → Set V) (r α : ℝ) (hr : 0 < r) (_ : 0 < α) (hα1 : α ≤ 1)
    (_ : Pairwise (fun i j => Disjoint (E i) (E j)))
    (_ : ∀ x, ∃ i, x ∈ E i) (j : Fin (m+1)) (x y : V)
    (hx : ball x (α*r) ⊆ E j) (hy : y ∉ E j)
    (hA : A.Nonempty → α*r ≤ infDist x A) :
    α*r/4 ≤ ∫ U : Fin (m+1) → I,
      |cobagNoise A E r (fun i => (U i:ℝ)) x -
       cobagNoise A E r (fun i => (U i:ℝ)) y| := by
  classical
  let a : Fin (m+1) → ℝ := fun i => cobagBump A (E i) r x - cobagBump A (E i) r y
  have ha : α*r ≤ a j := by
    dsimp [a]
    rw [cobagBump_zero A (E j) r hr.le y hy, sub_zero]
    apply cobagBump_padding A (E j) r (α*r) x _ hx hA
    exact mul_le_of_le_one_left hr.le hα1
  have hsum (U : Fin (m+1) → I) :
      cobagNoise A E r (fun i => (U i:ℝ)) x -
      cobagNoise A E r (fun i => (U i:ℝ)) y = ∑ i, (U i:ℝ)*a i := by
    simp only [cobagNoise, a, mul_sub, Finset.sum_sub_distrib]
  simp_rw [hsum]
  exact (div_le_div_of_nonneg_right ha (by norm_num)).trans
    (coefficient_affine_integral_lower j a)
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval ENNReal
attribute [local instance] Classical.propDecidable
noncomputable def cobagLocationLaw {n : ℕ} (μ : Fin n → ℝ) : Measure (Fin n) :=
  ∑ a, ENNReal.ofReal (μ a) • Measure.dirac a
noncomputable def cobagLaw {n : ℕ} (m : ℕ) (μ : Fin n → ℝ) :
    Measure (Fin n × (Fin (m+1) → I)) := (cobagLocationLaw μ).prod volume
noncomputable def cobagSample {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ)
    (ω : Fin n × (Fin (m+1) → I)) (x : V) : ℝ :=
  cobagNoise A (fun j => {z | P ω.1 z = j}) r (fun j => (ω.2 j:ℝ)) x

lemma cobagLocationLaw_probability {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) :
    IsProbabilityMeasure (cobagLocationLaw μ) := by
  classical
  constructor
  simp only [cobagLocationLaw, Measure.finsetSum_apply,
    Measure.smul_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun a _ => hμ a), hμ₁, ENNReal.ofReal_one]

lemma cobagLocationLaw_integral {n : ℕ} (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (f : Fin n → ℝ) :
    (∫ a, f a ∂cobagLocationLaw μ) = ∑ a, μ a * f a := by
  classical
  rw [cobagLocationLaw, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro a _
    rw [integral_smul_measure, integral_dirac]
    simp [ENNReal.toReal_ofReal (hμ a)]
  · intro a _
    exact (integrable_dirac (f := f) (by simp)).smul_measure (by simp)

lemma cobagSample_continuous {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (r : ℝ) (x : V) :
    Continuous (fun ω => cobagSample A P r ω x) := by
  unfold cobagSample cobagNoise
  apply continuous_finsetSum
  intro j _
  apply Continuous.mul
  · fun_prop
  · exact (continuous_of_discreteTopology (f := fun a : Fin n =>
      cobagBump A {z | P a z = j} r x)).comp continuous_fst

lemma cobagSample_integral {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1) (r : ℝ) (x y : V) :
    (∫ ω, |cobagSample A P r ω x - cobagSample A P r ω y| ∂cobagLaw m μ) =
      ∑ a, μ a * ∫ U : Fin (m+1) → I,
        |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| := by
  let := cobagLocationLaw_probability μ hμ hμ₁
  let : IsProbabilityMeasure (cobagLaw m μ) := by unfold cobagLaw; infer_instance
  have hc := ((cobagSample_continuous A P r x).sub (cobagSample_continuous A P r y)).abs
  have hi : Integrable (fun ω => |cobagSample A P r ω x - cobagSample A P r ω y|)
      (cobagLaw m μ) :=
    hc.integrable_of_hasCompactSupport (.of_compactSpace _)
  rw [cobagLaw, integral_prod _ hi, cobagLocationLaw_integral μ hμ]

theorem cobag_sampler {V : Type*} [MetricSpace V] {n m : ℕ}
    (A : Set V) (P : Fin n → V → Fin (m+1)) (μ : Fin n → ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hμ₁ : ∑ a, μ a = 1)
    (r α π : ℝ) (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdiam : ∀ a, 0 < μ a → ∀ x y, P a x = P a y → dist x y ≤ r) :
    IsProbabilityMeasure (cobagLaw m μ) ∧ Measurable (cobagSample A P r) ∧
    (∀ ω, LipschitzWith 1 (cobagSample A P r ω) ∧
      (∀ x, 0 ≤ cobagSample A P r ω x ∧ cobagSample A P r ω x ≤ r) ∧
      (∀ x ∈ A, cobagSample A P r ω x = 0)) ∧
    ∀ x y, r < dist x y → (A.Nonempty → α*r ≤ infDist x A) →
      (π ≤ ∑ a, if (∀ z, dist x z ≤ α*r → P a z = P a x) then μ a else 0) →
      π*α*r/4 ≤ ∫ ω, |cobagSample A P r ω x - cobagSample A P r ω y| ∂cobagLaw m μ := by
  classical
  have hloc := cobagLocationLaw_probability μ hμ hμ₁
  let := hloc
  have hlaw : IsProbabilityMeasure (cobagLaw m μ) := by unfold cobagLaw; infer_instance
  refine ⟨hlaw, ?_, ?_, ?_⟩
  · exact Measurable.of_eval (fun x => (cobagSample_continuous A P r x).measurable)
  · intro ω
    have hdis : Pairwise (fun i j : Fin (m+1) =>
        Disjoint {z | P ω.1 z = i} {z | P ω.1 z = j}) := by
      intro i j hij
      exact Set.disjoint_left.mpr (fun z hi hj => hij (hi.symm.trans hj))
    exact cobag_partition_properties A (fun j => {z | P ω.1 z = j}) r hr.le
      hdis (fun x => ⟨P ω.1 x, rfl⟩) (fun j => (ω.2 j:ℝ))
      (fun j => ⟨(ω.2 j).property.1, (ω.2 j).property.2⟩)
  · intro x y hxy hA hpad
    rw [cobagSample_integral A P μ hμ hμ₁]
    let c : ℝ := α*r/4
    let q : Fin n → ℝ := fun a =>
      if (∀ z, dist x z ≤ α*r → P a z = P a x) then μ a else 0
    have hc : 0 ≤ c := by dsimp [c]; positivity
    have hterm (a : Fin n) : c*q a ≤ μ a * ∫ U : Fin (m+1) → I,
        |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| := by
      have hnon : 0 ≤ ∫ U : Fin (m+1) → I,
          |cobagSample A P r (a,U) x - cobagSample A P r (a,U) y| :=
        integral_nonneg (fun _ => abs_nonneg _)
      by_cases hg : ∀ z, dist x z ≤ α*r → P a z = P a x
      · have hq : q a = μ a := ite_eq_left hg
        rw [hq]
        rcases eq_or_lt_of_le (hμ a) with hz | hp
        · rw [← hz]; simp
        · have hdis : Pairwise (fun i j : Fin (m+1) =>
              Disjoint {z | P a z = i} {z | P a z = j}) := by
            intro i j hij
            exact Set.disjoint_left.mpr (fun z hi hj => hij (hi.symm.trans hj))
          have hav := cobag_partition_averaging A (fun j => {z | P a z = j})
            r α hr hα hα1 hdis (fun z => ⟨P a z, rfl⟩) (P a x) x y
            (fun z hz => hg z (le_of_lt (by simpa [dist_comm] using hz)))
            (fun hy => (not_le_of_gt hxy) (hdiam a hp x y hy.symm)) hA
          exact (mul_comm c (μ a)).le.trans (mul_le_mul_of_nonneg_left hav (hμ a))
      · simp only [q, ite_eq_right hg, mul_zero]
        exact mul_nonneg (hμ a) hnon
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hterm a)
    rw [← Finset.mul_sum] at hsum
    have hh : c*π ≤ c*∑ a, q a := mul_le_mul_of_nonneg_left hpad hc
    calc
      π*α*r/4 = c*π := by dsimp [c]; ring
      _ ≤ c*∑ a, q a := hh
      _ ≤ _ := hsum
end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
open scoped unitInterval

attribute [local instance] Classical.propDecidable Classical.decEq

abbrev FiniteSampleSpace (V : Type*) [Fintype V] :=
  Fin (Fintype.card (V → V)) × (Fin (Fintype.card V + 1) → I)

/-- Convert a finite padded partition law into the actual common sampler
space, without selecting a partition or adding a separation assumption. -/
theorem finite_padded_sampler {V : Type*} [Fintype V] [MetricSpace V]
    (A : Set V) (μ : (V → V) → ℝ) (r α π : ℝ)
    (hμ : ∀ P, 0 ≤ μ P) (hμ₁ : ∑ P, μ P = 1)
    (hr : 0 < r) (hα : 0 < α) (hα1 : α ≤ 1)
    (hdiam : ∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r)
    (hpad : ∀ x, π ≤ ∑ P, if (∀ z, dist x z ≤ α*r → P z = P x) then μ P else 0) :
    ∃ ν : Measure (FiniteSampleSpace V), ∃ g : FiniteSampleSpace V → V → ℝ,
      IsProbabilityMeasure ν ∧ Measurable g ∧
      (∀ ω, LipschitzWith 1 (g ω) ∧ (∀ x, 0 ≤ g ω x ∧ g ω x ≤ r) ∧
        (∀ x ∈ A, g ω x = 0)) ∧
      ∀ x y, r < dist x y → (A.Nonempty → α*r ≤ infDist x A) →
        π*α*r/4 ≤ ∫ ω, |g ω x - g ω y| ∂ν := by
  classical
  let e := Fintype.equivFin (V → V)
  let v := Fintype.equivFin V
  let P : Fin (Fintype.card (V → V)) → V → Fin (Fintype.card V + 1) :=
    fun a x => (v (e.symm a x)).castSucc
  let μ' : Fin (Fintype.card (V → V)) → ℝ := fun a => μ (e.symm a)
  have heq (a) (x y : V) : P a x = P a y ↔ e.symm a x = e.symm a y := by
    simp only [P, Fin.castSucc_inj, Equiv.apply_eq_iff_eq]
  have hsum : ∑ a, μ' a = 1 := by
    rw [show (∑ a, μ' a) = ∑ f, μ f from e.symm.sum_comp μ]
    exact hμ₁
  have hd : ∀ a, 0 < μ' a → ∀ x y, P a x = P a y → dist x y ≤ r := by
    intro a ha x y hxy
    exact hdiam (e.symm a) ha x y ((heq a x y).mp hxy)
  have hp (x : V) : π ≤ ∑ a, if (∀ z, dist x z ≤ α*r → P a z = P a x)
      then μ' a else 0 := by
    simp only [heq]
    change π ≤ ∑ a, (fun f : V → V => if (∀ z, dist x z ≤ α*r → f z = f x)
      then μ f else 0) (e.symm a)
    have he := e.symm.sum_comp (fun f : V → V => if (∀ z, dist x z ≤ α*r → f z = f x)
      then μ f else 0)
    convert (hpad x).trans_eq he.symm using 1
  obtain ⟨hν, hg, hprop, hgap⟩ := cobag_sampler A P μ' (fun a => hμ _) hsum
    r α π hr hα hα1 hd
  exact ⟨cobagLaw (Fintype.card V) μ', cobagSample A P r, hν, hg, hprop,
    fun x y hxy hx => hgap x y hxy hx (by
      convert hp x using 1
      apply Finset.sum_congr rfl
      intro a ha
      split_ifs <;> rfl)⟩

end BoundedTreewidthL1.LaunchNoise

namespace BoundedTreewidthL1.LaunchNoise
open MeasureTheory Metric
attribute [local instance] Classical.propDecidable Classical.decEq

/-- The required uniformly padded co-bag launch now has an unconditional
sampler in the original arbitrary-weight graph metric. -/
theorem graph_cobag_sampler :
    ∀ k : ℕ, 2 ≤ k → ∃ α π : ℝ, 0 < α ∧ α ≤ 1/8 ∧ 0 < π ∧ π ≤ 1 ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (hG : G.Connected), HasTreeDecomposition G k →
      ∀ (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e),
      let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
      ∀ (A : Set V) (r : ℝ), 0 < r →
      ∃ ν : Measure (FiniteSampleSpace V), ∃ g : FiniteSampleSpace V → V → ℝ,
        IsProbabilityMeasure ν ∧ Measurable g ∧
        (∀ ω, LipschitzWith 1 (g ω) ∧ (∀ x, 0 ≤ g ω x ∧ g ω x ≤ r) ∧
          (∀ x ∈ A, g ω x = 0)) ∧
        ∀ x y, r < shortestPathDistance G ℓ x y →
          (A.Nonempty → α*r ≤ infDist x A) →
          π*α*r/4 ≤ ∫ ω, |g ω x - g ω y| ∂ν := by
  classical
  intro k hk
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hpart⟩ := PaddedPartitions.uniform_padded_partitions k hk
  refine ⟨α,π,hα,hα8,hπ,hπ1,?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ metric
  let _ : MetricSpace V := metric
  intro A r hr
  obtain ⟨μ,hμ,hμ1,hdiam,hpad⟩ := hpart V G hG hdec ℓ hℓ r hr
  have hd : ∀ P, 0 < μ P → ∀ x y, P x = P y → dist x y ≤ r := by
    intro P hP x y hxy
    exact hdiam P hP x y hxy
  have hp : ∀ x, π ≤ ∑ P, if (∀ z, dist x z ≤ α*r → P z = P x) then μ P else 0 := by
    intro x
    change π ≤ ∑ P, if (∀ z, shortestPathDistance G ℓ x z ≤ α*r → P z = P x) then μ P else 0
    have hx := hpad x
    unfold PaddedPartitions.paddingProbability PaddedPartitions.PaddedAt at hx
    convert! hx using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro P hP
      split_ifs <;> rfl
  refine finite_padded_sampler A μ r α π hμ ?_ hr hα (by linarith) hd ?_
  · convert! hμ1 using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro _ _; rfl
  · intro x
    convert! hp x using 1
    apply Finset.sum_congr
    · ext; simp only [Finset.mem_univ]
    · intro P hP
      split_ifs <;> rfl

end BoundedTreewidthL1.LaunchNoise

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1.CobagScales
open LaunchNoise
variable {V : Type*} [DecidableEq V]
attribute [local instance] Classical.propDecidable

noncomputable def pairDistance (d : V → V → ℝ) (p : Finset V) : ℝ :=
  if h : p.card = 2 then
    d (Finset.card_eq_two.mp h).choose (Finset.card_eq_two.mp h).choose_spec.choose
  else 0

lemma pairDistance_witness (d : V → V → ℝ) (p : Finset V) (hp : p.card = 2) :
    ∃ u v, u ≠ v ∧ p = {u,v} ∧ pairDistance d p = d u v := by
  unfold pairDistance
  rw [dite_eq_left hp]
  exact ⟨_,_,(Finset.card_eq_two.mp hp).choose_spec.choose_spec.1,
    (Finset.card_eq_two.mp hp).choose_spec.choose_spec.2,rfl⟩

lemma pairDistance_pair (d : V → V → ℝ) (hs : ∀ u v, d u v = d v u)
    {u v : V} (huv : u ≠ v) : pairDistance d {u,v} = d u v := by
  obtain ⟨a,b,hab,he,hd⟩ := pairDistance_witness d {u,v} (by simp [huv])
  have ha : a = u ∨ a = v := by
    have hm : a ∈ ({u,v} : Finset V) := he.symm ▸ Finset.mem_insert_self a {b}
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have hb : b = u ∨ b = v := by
    have hm : b ∈ ({u,v} : Finset V) := he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self b)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact False.elim (hab rfl)
  · exact hd
  · exact hd.trans (hs _ _)
  · exact False.elim (hab rfl)

noncomputable def distanceScales (t : ℝ) : Finset ℤ :=
  (Finset.Icc (bandIndex 1 t - 2) (bandIndex 1 t + 1)).filter
    (fun j => (2:ℝ)^j/2 ≤ t ∧ t ≤ 4*(2:ℝ)^j)

lemma score_interval (t : ℝ) (ht : 0 < t) (j : ℤ)
    (hl : (2:ℝ)^j/2 ≤ t) (hu : t ≤ 4*(2:ℝ)^j) :
    bandIndex 1 t - 2 ≤ j ∧ j ≤ bandIndex 1 t + 1 := by
  have hbase := band_bounds 1 t (by norm_num) ht
  simp only [bandLower, one_mul] at hbase
  have hpow (a : ℤ) : (2:ℝ)^(a+2) = 4*(2:ℝ)^a := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hpow' (a : ℤ) : (2:ℝ)^(a+1) = 2*(2:ℝ)^a := by
    rw [zpow_add₀ (by norm_num)]
    norm_num
    ring
  have hlo : bandIndex 1 t ≤ j+2 := by
    apply (zpow_le_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
    rw [hpow]
    exact hbase.2.1.trans hu
  have hhi : j < bandIndex 1 t+2 := by
    apply (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp
    rw [hpow]
    nlinarith [hbase.2.2]
  omega

lemma mem_distanceScales (t : ℝ) (ht : 0 < t) (j : ℤ) :
    j ∈ distanceScales t ↔ (2:ℝ)^j/2 ≤ t ∧ t ≤ 4*(2:ℝ)^j := by
  simp only [distanceScales, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨fun h => h.2, fun h => ⟨score_interval t ht j h.1 h.2,h⟩⟩

lemma distanceScales_card (t : ℝ) : (distanceScales t).card ≤ 4 := by
  apply (Finset.card_filter_le _ _).trans
  rw [Int.card_Icc]
  omega

noncomputable def active (d : V → V → ℝ) (B : Finset V) : Finset ℤ :=
  (B.powersetCard 2).biUnion (fun p => distanceScales (pairDistance d p))

lemma mem_active (d : V → V → ℝ) (hs : ∀ u v, d u v = d v u)
    (hp : ∀ u v, u ≠ v → 0 < d u v) (B : Finset V) (j : ℤ) :
    j ∈ active d B ↔ ∃ u ∈ B, ∃ v ∈ B, u ≠ v ∧
      (2:ℝ)^j/2 ≤ d u v ∧ d u v ≤ 4*(2:ℝ)^j := by
  constructor
  · intro hj
    obtain ⟨p,hpB,hj⟩ := Finset.mem_biUnion.mp hj
    obtain ⟨hpB,hp₂⟩ := Finset.mem_powersetCard.mp hpB
    obtain ⟨u,v,huv,he,hd⟩ := pairDistance_witness d p hp₂
    have hu : u ∈ B := hpB (he ▸ Finset.mem_insert_self u {v})
    have hv : v ∈ B := hpB (he ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self v))
    rw [hd] at hj
    exact ⟨u,hu,v,hv,huv,(mem_distanceScales _ (hp u v huv) j).mp hj⟩
  · rintro ⟨u,hu,v,hv,huv,hl,hh⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨{u,v},Finset.mem_powersetCard.mpr ⟨?_,by simp [huv]⟩,?_⟩
    · simpa only [Finset.insert_subset_iff, Finset.singleton_subset_iff] using And.intro hu hv
    · rw [pairDistance_pair d hs huv]
      exact (mem_distanceScales _ (hp u v huv) j).mpr ⟨hl,hh⟩

theorem active_card (d : V → V → ℝ) (B : Finset V) :
    (active d B).card ≤ 4 * B.card.choose 2 := by
  calc
    (active d B).card ≤ ∑ p ∈ B.powersetCard 2, (distanceScales (pairDistance d p)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ B.powersetCard 2, 4 := Finset.sum_le_sum (fun p _ => distanceScales_card _)
    _ = 4 * B.card.choose 2 := by simp [Finset.card_powersetCard, Nat.mul_comm]

end BoundedTreewidthL1.CobagScales

namespace BoundedTreewidthL1.CobagScales
open Metric
variable {V : Type*} [MetricSpace V] [DecidableEq V]

theorem inactive_far (A : Finset V) (j : ℤ) (x y : V)
    (hj : j ∉ active dist A) (hl : (2:ℝ)^j ≤ dist x y)
    (hu : dist x y < 2*(2:ℝ)^j) (hA : (A : Set V).Nonempty) :
    (2:ℝ)^j/8 ≤ infDist x (A : Set V) ∨
      (2:ℝ)^j/8 ≤ infDist y (A : Set V) := by
  by_contra h
  have hx : infDist x (A : Set V) < (2:ℝ)^j/8 := by
    exact lt_of_not_ge (fun hx => h (Or.inl hx))
  have hy : infDist y (A : Set V) < (2:ℝ)^j/8 := by
    exact lt_of_not_ge (fun hy => h (Or.inr hy))
  obtain ⟨a,ha,hxa⟩ := (infDist_lt_iff hA).mp hx
  obtain ⟨b,hb,hyb⟩ := (infDist_lt_iff hA).mp hy
  have hs : 0 < (2:ℝ)^j := zpow_pos (by norm_num) _
  have hxy := dist_triangle4 x a b y
  have hab := dist_triangle4 a x y b
  rw [dist_comm b y] at hxy
  rw [dist_comm a x] at hab
  have habpos : 0 < dist a b := by linarith
  apply hj
  apply (mem_active dist dist_comm (fun u v huv => dist_pos.mpr huv) A j).mpr
  exact ⟨a,ha,b,hb,dist_pos.mp habpos,by linarith,by linarith⟩

lemma small_scale_active (A : Finset V) (x y : V) (hx : x ∈ A) (hy : y ∈ A)
    (hxy : x ≠ y) :
    LaunchNoise.bandIndex 1 (dist x y) ∈ active dist A := by
  have hb := LaunchNoise.band_bounds 1 (dist x y) (by norm_num) (dist_pos.mpr hxy)
  simp only [LaunchNoise.bandLower,one_mul] at hb
  apply (mem_active dist dist_comm (fun u v huv => dist_pos.mpr huv) A _).mpr
  exact ⟨x,hx,y,hy,hxy,by linarith,by linarith⟩
end BoundedTreewidthL1.CobagScales

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1
open MeasureTheory Metric TreeParticles LaunchNoise CobagScales
open scoped BigOperators ENNReal
attribute [local instance] Classical.decEq Classical.propDecidable

theorem cobag_embedding :
    ∀ k : ℕ, 2 ≤ k → ∃ U c : ℝ, 0 < U ∧ 0 < c ∧
    ∀ (V : Type) [Fintype V] [DecidableEq V] [Nontrivial V]
      (G : SimpleGraph V) (_ : G.Connected)
      (ℓ : G.edgeSet → ℝ) (_ : ∀ e, 0 < ℓ e)
      (m : ℕ) (T : SimpleGraph (Fin m)) (_ : T.IsTree) (_ : Fin m)
      (B : Fin m → Finset V),
      (∀ v, ∃ i, v ∈ B i) →
      (∀ u v, G.Adj u v → ∃ i, u ∈ B i ∧ v ∈ B i) →
      (∀ v, (T.induce {i | v ∈ B i}).Connected) →
      (∀ i, (B i).card ≤ k) →
      ∃ n : ℕ, ∃ Φ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ),
        (∀ u v, ‖Φ u - Φ v‖ ≤ U*shortestPathDistance G ℓ u v) ∧
        ∀ i u v, u ∈ B i → v ∈ B i →
          c*shortestPathDistance G ℓ u v ≤ ‖Φ u - Φ v‖ := by
  classical
  intro k hk
  obtain ⟨α,π,hα,hα8,hπ,hπ1,hsampler⟩ := graph_cobag_sampler k hk
  let q := 4*k.choose 2
  let N := 2*q + k.factorial + 2
  have hN : 2 ≤ N := by dsimp [N]; omega
  have hNr : (2:ℝ) ≤ N := by exact_mod_cast hN
  have hNm : 0 < (N:ℝ)-1 := by linarith
  refine ⟨(N:ℝ)*((N:ℝ)-1),π*α/64,mul_pos (by linarith) hNm,by positivity,?_⟩
  intro V _ _ _ G hG ℓ hℓ m T hT root B hcover hedge hrun hbag
  let : MetricSpace V := weightedMetricSpace G ℓ hG hℓ
  let R := RootedTree.forest T hT root
  let K : Finset ℤ := Finset.univ.biUnion (fun i => active dist (B i))
  let J := ↥K
  let A : Fin m → Finset J := fun i => (active dist (B i)).subtype (fun j => j ∈ K)
  have hA : ∀ i, (A i).card ≤ q := by
    intro i
    calc
      (A i).card ≤ (active dist (B i)).card := by
        rw [Finset.card_subtype]
        exact Finset.card_filter_le _ _
      _ ≤ 4*(B i).card.choose 2 := active_card _ _
      _ ≤ q := Nat.mul_le_mul_left 4 (Nat.choose_le_choose 2 (hbag i))
  have hdec : HasTreeDecomposition G k := ⟨m,T,B,hT,hcover,hedge,hrun,hbag⟩
  have hs (p : Fin m × J) := hsampler V G hG hdec ℓ hℓ
    (interface R B p.1 : Set V) ((2:ℝ)^p.2.val/16) (by positivity)
  choose ν f hprob hf hprop hsep using hs
  let (p : Fin m × J) : IsProbabilityMeasure (ν p) := hprob p
  let Ω := (Fin m × J) → FiniteSampleSpace V
  let law : Measure Ω := Measure.pi ν
  let g : Ω → Fin m → J → V → ℝ := fun ω i a => f (i,a) (ω (i,a))
  let H : ℝ := 1 + ∑ a : J, (2:ℝ)^a.val
  have hH : 0 < H := by
    have hh : 0 ≤ ∑ a : J, (2:ℝ)^a.val := Finset.sum_nonneg (fun a _ => (zpow_pos (by norm_num) _).le)
    dsimp [H]; linarith
  have hh (a : J) : (2:ℝ)^a.val/16 ≤ H := by
    have hh := Finset.single_le_sum (fun b (_ : b ∈ (Finset.univ : Finset J)) =>
      (zpow_pos (by norm_num : (0:ℝ)<2) b.val).le) (Finset.mem_univ a)
    have hp := zpow_pos (by norm_num : (0:ℝ)<2) a.val
    dsimp [H]
    linarith
  have hg : ∀ i a v, Measurable (fun ω : Ω => g ω i a v) := by
    intro i a v
    exact ((measurable_pi_apply v).comp (hf (i,a))).comp (measurable_pi_apply (i,a))
  have hLip : ∀ ω i a, ∀ u v, |g ω i a u-g ω i a v| ≤ 1*shortestPathDistance G ℓ u v := by
    intro ω i a u v
    change |f (i,a) (ω (i,a)) u-f (i,a) (ω (i,a)) v| ≤ 1*dist u v
    exact (hprop (i,a) (ω (i,a))).1.dist_le_mul u v
  have hHeight : ∀ ω i a v, |g ω i a v| ≤ H := by
    intro ω i a v
    rw [abs_of_nonneg ((hprop (i,a) (ω (i,a))).2.1 v).1]
    exact ((hprop (i,a) (ω (i,a))).2.1 v).2.trans (hh a)
  have hz : ∀ ω i a, ∀ v ∈ interface R B i, g ω i a v = 0 := by
    intro ω i a v hv
    exact (hprop (i,a) (ω (i,a))).2.2 v hv
  obtain ⟨n,Φ,hup,hlo⟩ := averaged_origin_realization (ι := Fin N) G hG ℓ hℓ T hT root B
    hcover hedge (fun v => (hrun v).preconnected) A k q hbag hA (by simp [N])
    law 1 H 1 (by norm_num) hH (by norm_num) g hg hLip hHeight hz
  refine ⟨n,Φ,?_,?_⟩
  · simpa only [Fintype.card_fin,mul_one] using hup
  · intro i u v hu hv
    by_cases huv : u = v
    · subst v
      simp only [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le),mul_zero,sub_self,norm_zero,le_refl]
    let j := bandIndex 1 (dist u v)
    have hb : 0 < (2:ℝ)^j ∧ (2:ℝ)^j ≤ dist u v ∧ dist u v < 2*(2:ℝ)^j := by
      simpa only [bandLower,one_mul] using band_bounds 1 (dist u v) (by norm_num) (dist_pos.mpr huv)
    have haj : j ∈ active dist (B i) := small_scale_active (B i) u v hu hv huv
    let a : J := ⟨j,Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,haj⟩⟩
    have ha : a ∈ A i := Finset.mem_subtype.mpr haj
    let o := origin R A root i a
    have hof : a ∈ fresh R A o := origin_fresh R A root i a ha
    have hge (x y : V) (hxy : (2:ℝ)^j/16 < dist x y)
        (hcap : (interface R B o : Set V).Nonempty →
          α*((2:ℝ)^j/16) ≤ infDist x (interface R B o : Set V)) :
        π*α*((2:ℝ)^j/16)/4 ≤ ∫ ω : Ω, |g ω o a x-g ω o a y| ∂law := by
      have heq := integral_comp_eval (μ := ν) (i := (o,a))
        (((measurable_pi_apply x).comp (hf (o,a))).sub
          ((measurable_pi_apply y).comp (hf (o,a)))).abs.aestronglyMeasurable
      change (∫ ω : Ω, |g ω o a x-g ω o a y| ∂law) = _ at heq
      rw [heq]
      exact hsep (o,a) x y hxy hcap
    have hgap : π*α*((2:ℝ)^j/16)/4 ≤ ∫ ω : Ω, |g ω o a u-g ω o a v| ∂law := by
      have hsmall : (2:ℝ)^j/16 < dist u v := by linarith [hb.1,hb.2.1]
      have hscale : α*((2:ℝ)^j/16) ≤ (2:ℝ)^j/8 := by nlinarith [hb.1]
      cases hp : R.parent o with
      | none =>
        apply hge u v hsmall
        simp only [interface,hp,Option.elim_none,Finset.coe_empty,Set.not_nonempty_empty,IsEmpty.forall_iff]
      | some p =>
        have hn : j ∉ active dist (B p) := by
          intro hj
          have hap : a ∈ A p := Finset.mem_subtype.mpr hj
          exact (Finset.mem_sdiff.mp hof).2 (by
            simpa only [retained,hp,Option.elim_some,Finset.mem_inter] using
              And.intro (Finset.mem_sdiff.mp hof).1 hap)
        by_cases hne : (B p : Set V).Nonempty
        · rcases inactive_far (B p) j u v hn hb.2.1 hb.2.2 hne with hfar | hfar
          · apply hge u v hsmall
            intro _
            simpa only [interface,hp,Option.elim_some] using hscale.trans hfar
          · have he := hge v u (by simpa only [dist_comm] using hsmall) (by
              intro _
              simpa only [interface,hp,Option.elim_some] using hscale.trans hfar)
            apply he.trans_eq
            apply integral_congr_ae
            exact Filter.Eventually.of_forall (fun ω => abs_sub_comm _ _)
        · apply hge u v hsmall
          simpa only [interface,hp,Option.elim_some] using (fun h => False.elim (hne h))
    have hl := hlo i a ha ⟨u,hu⟩ ⟨v,hv⟩
    have hpos : 0 < π*α := mul_pos hπ hα
    change 2*(∫ ω : Ω, |g ω o a u-g ω o a v| ∂law) ≤ ‖Φ u-Φ v‖ at hl
    change π*α/64*dist u v ≤ ‖Φ u-Φ v‖
    nlinarith [hb.2.2]
end BoundedTreewidthL1

end OAI
end
end

section
section
namespace OAI

namespace BoundedTreewidthL1
variable {V : Type*} (G : SimpleGraph V)

/-- Removing empty bags preserves the exact tree-decomposition hypotheses.
The graph is only required to be nonempty and connected; no extra metric
hypothesis enters this combinatorial reduction. -/
theorem nonempty_tree_decomposition [Fintype V] [DecidableEq V] [Nonempty V]
    (hG : G.Connected) (k : ℕ) (hdec : HasTreeDecomposition G k) :
    ∃ n : ℕ, ∃ T : SimpleGraph (Fin n), ∃ bag : Fin n → Finset V,
      T.IsTree ∧
      (∀ v : V, ∃ t, v ∈ bag t) ∧
      (∀ u v : V, G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t) ∧
      (∀ v : V, (T.induce {t | v ∈ bag t}).Connected) ∧
      (∀ t, (bag t).card ≤ k) ∧ (∀ t, (bag t).Nonempty) := by
  classical
  obtain ⟨n, T, B, hT, hcover, hedge, hocc, hsize⟩ := hdec
  let S : Set (Fin n) := {i | (B i).Nonempty}
  have hS : (T.induce S).Connected := by
    have hc : (G.induce Set.univ).Connected := G.induceUnivIso.connected_iff.mpr hG
    have := touched_bags_connected_set G T B hedge hocc Set.univ hc
    have heq : {t | ∃ z ∈ (Set.univ : Set V), z ∈ B t} = S := by
      ext t
      simp [S, Finset.nonempty_def]
    rw [heq] at this
    exact this
  let I := {i : Fin n // i ∈ S}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let T' : SimpleGraph (Fin (Fintype.card I)) := (T.induce S).comap e
  let B' : Fin (Fintype.card I) → Finset V := fun i => B (e i).val
  have hT' : T'.IsTree :=
    (SimpleGraph.Iso.comap e (T.induce S)).isTree_iff.mpr ⟨hS, hT.isAcyclic.induce S⟩
  refine ⟨Fintype.card I, T', B', hT', ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    obtain ⟨i, hi⟩ := hcover v
    refine ⟨e.symm ⟨i, v, hi⟩, ?_⟩
    simpa [B'] using hi
  · intro u v huv
    obtain ⟨i, hui, hvi⟩ := hedge u v huv
    refine ⟨e.symm ⟨i, u, hui⟩, ?_, ?_⟩ <;> simpa [B']
  · intro v
    let f : {i : Fin n // v ∈ B i} → {j : Fin (Fintype.card I) // v ∈ B' j} :=
      fun i => ⟨e.symm ⟨i.val, v, i.property⟩, by simpa [B'] using i.property⟩
    let hf : (T.induce {i | v ∈ B i}) →g (T'.induce {j | v ∈ B' j}) :=
      ⟨f, by
        intro i j hij
        change T.Adj (e (f i).val).val (e (f j).val).val
        simpa [f] using hij⟩
    apply (hocc v).map hf
    intro j
    refine ⟨⟨(e j.val).val, j.property⟩, ?_⟩
    apply Subtype.ext
    change e.symm _ = j.val
    rw [Equiv.symm_apply_eq]
  · intro i
    exact hsize _
  · intro i
    exact (e i).property

end BoundedTreewidthL1

namespace BoundedTreewidthL1
noncomputable section

/-- Direct sum of two finite real L1 vectors, with the sum norm (not the maximum
norm on an ordinary product). -/
def l1Append {m n : ℕ} (x : PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (y : PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) :
    PiLp (1 : ENNReal) (fun _ : Fin (m+n) => ℝ) :=
  WithLp.toLp 1 (Fin.append x.ofLp y.ofLp)

lemma l1Append_norm_sub {m n : ℕ} (x x' : PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (y y' : PiLp (1 : ENNReal) (fun _ : Fin n => ℝ)) :
    ‖l1Append x y-l1Append x' y'‖ = ‖x-x'‖+‖y-y'‖ := by
  simp only [PiLp.norm_eq_sum (by simp : 0 < (1 : ENNReal).toReal), ENNReal.toReal_one,
    Real.rpow_one, div_self (by norm_num : (1:ℝ) ≠ 0)]
  rw [Fin.sum_univ_add]
  simp [l1Append, PiLp.sub_apply]

/-- The final purely metric bridge: a common-bag bound on both endpoints and
co-bag separation imply a global all-pairs lower comparison. -/
lemma common_bag_comparison {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (hG : G.Connected) (ℓ : G.edgeSet → ℝ) (hℓ : ∀ e, 0 < ℓ e)
    {I : Type*} (B : I → Finset V) (hne : ∀ i, (B i).Nonempty)
    {m n : ℕ} (Φ : V → PiLp (1 : ENNReal) (fun _ : Fin m => ℝ))
    (Ψ : V → PiLp (1 : ENNReal) (fun _ : Fin n => ℝ))
    (U c a : ℝ) (hU : 0 ≤ U) (hc : 0 < c) (ha : 0 < a)
    (hupper : ∀ x y, ‖Ψ x-Ψ y‖ ≤ U*shortestPathDistance G ℓ x y)
    (hcobag : ∀ i x y, x ∈ B i → y ∈ B i →
      c*shortestPathDistance G ℓ x y ≤ ‖Ψ x-Ψ y‖)
    (hanchor : ∀ x y, ∃ i, a*bagDistance G ℓ (B i) (hne i) x ≤ ‖Φ x-Φ y‖ ∧
      a*bagDistance G ℓ (B i) (hne i) y ≤ ‖Φ x-Φ y‖) (x y : V) :
    c*shortestPathDistance G ℓ x y ≤
      ‖Ψ x-Ψ y‖ + (2*(U+c)/a)*‖Φ x-Φ y‖ := by
  obtain ⟨i,hix,hiy⟩ := hanchor x y
  obtain ⟨p,hp,hpx⟩ := bagDistance_attained G ℓ (B i) (hne i) x
  obtain ⟨q,hq,hqy⟩ := bagDistance_attained G ℓ (B i) (hne i) y
  have hd := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le) x p y
  have hd' := shortestPathDistance_triangle G ℓ hG (fun e => (hℓ e).le) p q y
  have hs := shortestPathDistance_comm G ℓ hG (fun e => (hℓ e).le) q y
  have hΨ := norm_sub_le_norm_sub_add_norm_sub (Ψ p) (Ψ x) (Ψ q)
  have hΨ' := norm_sub_le_norm_sub_add_norm_sub (Ψ x) (Ψ y) (Ψ q)
  have hxp := hupper x p
  have hyq := hupper y q
  rw [norm_sub_rev (Ψ p) (Ψ x)] at hΨ
  have hco := hcobag i p q hp hq
  rw [← hpx] at hd hxp
  rw [hs,← hqy] at hd'
  rw [← hqy] at hyq
  have hda : a*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) ≤
      2*‖Φ x-Φ y‖ := by linarith
  have hmain : c*shortestPathDistance G ℓ x y ≤ ‖Ψ x-Ψ y‖+
      (U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) := by
    nlinarith
  have hsum : (U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y) ≤
      (2*(U+c)/a)*‖Φ x-Φ y‖ := by
    apply (mul_le_mul_iff_right₀ ha).mp
    have hh := mul_le_mul_of_nonneg_left hda (by linarith : 0 ≤ U+c)
    calc
      a*((U+c)*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y)) =
        (U+c)*(a*(bagDistance G ℓ (B i) (hne i) x+bagDistance G ℓ (B i) (hne i) y)) := by ring
      _ ≤ (U+c)*(2*‖Φ x-Φ y‖) := hh
      _ = a*((2*(U+c)/a)*‖Φ x-Φ y‖) := by field_simp
  exact hmain.trans (add_le_add le_rfl hsum)

end
end BoundedTreewidthL1

namespace BoundedTreewidthL1
noncomputable section

theorem main_theorem_oai : MainStatement := by
  classical
  intro k hk
  obtain ⟨Ua,ca,hUa,hca,hanchor⟩ := AnchorExperiment.anchor_common_bag_embedding k hk
  obtain ⟨Ub,cb,hUb,hcb,hcobag⟩ := cobag_embedding k hk
  let lam : ℝ := 2*(Ub+cb)/ca
  have hlam : 0 < lam := by dsimp [lam]; positivity
  let C : ℝ := max 1 ((lam*Ua+Ub)/cb)
  refine ⟨C,le_max_left _ _,?_⟩
  intro V _ _ _ G hG hdec ℓ hℓ
  rcases subsingleton_or_nontrivial V with hsub | hnontriv
  · let := hsub
    refine ⟨0,fun _ => 0,?_⟩
    intro x y
    have hxy : x = y := Subsingleton.elim _ _
    subst y
    simp [shortestPathDistance_self G ℓ hG (fun e => (hℓ e).le)]
  · let := hnontriv
    obtain ⟨n,T,B,hT,hcover,hedge,hrun,hbag,hne⟩ := nonempty_tree_decomposition G hG k hdec
    cases n with
    | zero =>
      obtain ⟨i,_⟩ := hcover (Classical.choice (inferInstance : Nonempty V))
      exact Fin.elim0 i
    | succ n =>
      let root : Fin (n+1) := ⟨0,Nat.succ_pos n⟩
      obtain ⟨ma,Φ,hΦu,hΦa⟩ := hanchor V G hG ℓ hℓ n T hT root B hne hcover hedge hrun hbag
      obtain ⟨mb,Ψ,hΨu,hΨb⟩ := hcobag V G hG ℓ hℓ (n+1) T hT root B hcover hedge hrun hbag
      let F : V → PiLp (1 : ENNReal) (fun _ : Fin (ma+mb) => ℝ) :=
        fun x => cb⁻¹ • l1Append (lam • Φ x) (Ψ x)
      refine ⟨ma+mb,F,?_⟩
      intro x y
      have hnorm : ‖F x-F y‖ = cb⁻¹*(lam*‖Φ x-Φ y‖+‖Ψ x-Ψ y‖) := by
        dsimp only [F]
        rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hcb),
          l1Append_norm_sub,← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hlam]
      rw [hnorm]
      constructor
      · have hh := common_bag_comparison G hG ℓ hℓ B hne Φ Ψ Ub cb ca hUb.le hcb hca
          hΨu hΨb hΦa x y
        have hh' := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hcb.le)
        simpa only [← mul_assoc, inv_mul_cancel₀ hcb.ne',one_mul,add_comm] using hh'
      · calc
          cb⁻¹*(lam*‖Φ x-Φ y‖+‖Ψ x-Ψ y‖) ≤
              cb⁻¹*(lam*(Ua*shortestPathDistance G ℓ x y)+Ub*shortestPathDistance G ℓ x y) :=
            mul_le_mul_of_nonneg_left (add_le_add
              (mul_le_mul_of_nonneg_left (hΦu x y) hlam.le) (hΨu x y)) (inv_nonneg.mpr hcb.le)
          _ = ((lam*Ua+Ub)/cb)*shortestPathDistance G ℓ x y := by ring
          _ ≤ C*shortestPathDistance G ℓ x y := mul_le_mul_of_nonneg_right (le_max_right _ _)
            (shortestPathDistance_nonneg G ℓ hG (fun e => (hℓ e).le) x y)

end
end BoundedTreewidthL1

end OAI
end
end

theorem solution : type_of% @OAI.BoundedTreewidthL1.main_theorem_oai := @OAI.BoundedTreewidthL1.main_theorem_oai
