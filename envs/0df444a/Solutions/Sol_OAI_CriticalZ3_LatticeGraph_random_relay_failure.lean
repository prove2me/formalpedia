-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.random_relay_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:49:26.241309+00:00
-- url     : https://prove2.me/submissions/96e954ba-c1cb-417a-b34d-8d0d83f02686

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/ShellProbability.lean:L266-L286
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.random_relay_failure. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondMeets_probability
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondObservable_probability
import Theorems.Thm_OAI_HyperedgeComparison_joint_comparison_of_lt_one
import Theorems.Thm_OAI_InfiniteConditioning_measure_select

-- ---- from OAI.Probability.CriticalZ3.ProductCylinder ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uF uI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! Exact reduction of finite cylinder observables under the infinite Bernoulli law. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace ProductCylinder
universe u
variable {E F : Type u}

theorem map_restrict (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1) :
    (law p).map J.restrict = finiteLaw J p := Measure.infinitePi_map_restrict _

theorem cylinder_probability (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (J → Bool)) :
    law p (J.restrict ⁻¹' A) = finiteLaw J p A := by
  rw [←map_restrict,Measure.map_apply (Finset.measurable_restrict _) (Set.toFinite A).measurableSet]

theorem determinedBy_eq_extend {J : Finset E} {f : (E → Bool) → F}
    (hf : DeterminedBy J f) (ω : E → Bool) : f ω = f (extend J (J.restrict ω)) := by
  apply hf
  intro e he
  simp [extend,he,Finset.restrict]

theorem probability_determined (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) :
    law p A = finiteLaw J p {ξ | extend J ξ ∈ A} := by
  rw [←cylinder_probability]
  congr 1
  ext ω
  exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])

theorem measurableSet_determined (J : Finset E) (A : Set (E → Bool))
    (hA : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → (ω' ∈ A ↔ ω ∈ A)) : MeasurableSet A := by
  have he : A = J.restrict ⁻¹' {ξ | extend J ξ ∈ A} := by
    ext ω
    exact hA (extend J (J.restrict ω)) ω (by intro e he; simp [extend,he,Finset.restrict])
  rw [he]
  exact (Finset.measurable_restrict _) (Set.toFinite _).measurableSet

end ProductCylinder

/-! Harris association for finite independent bits, including fixed coordinates. -/
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace FiniteAssociation
universe u
variable {E : Type u}

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.HyperedgeComparison ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uI uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace HyperedgeComparison

variable {V : Type uV} {E : Type uE}

section FiniteLaw
variable [Fintype E]

theorem eventProb_eq_real (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P = (law p).real {ω | P ω} := by
  simpa [eventProb, Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

/-- Polynomial weight of a specified finite configuration. -/
theorem law_mass (p : E → Set.Icc (0 : ℝ) 1) (ω : E → Bool) :
    (law p).real {ω} = ∏ e, if ω e = true then (p e : ℝ) else 1 - (p e : ℝ) := by
  classical
  rw [Measure.real_def, law, Measure.pi_singleton, ENNReal.toReal_prod]
  apply Finset.prod_congr rfl
  intro e _
  change (bernoulliMeasure true false (p e)).real {ω e} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases he : ω e <;> simp [unitInterval.coe_symm_eq]

/-- All finite event probabilities are continuous in all parameters, including
at configurations with deterministic bits. -/
theorem eventProb_tendsto (p : E → Set.Icc (0 : ℝ) 1)
    (q : ℕ → E → Set.Icc (0 : ℝ) 1)
    (hq : ∀ e, Tendsto (fun n => (q n e : ℝ)) atTop (nhds (p e : ℝ)))
    (P : (E → Bool) → Prop) :
    Tendsto (fun n => eventProb (q n) P) atTop (nhds (eventProb p P)) := by
  simp_rw [eventProb, integral_fintype (Integrable.of_finite), law_mass]
  apply tendsto_finsetSum
  intro ω _
  apply Filter.Tendsto.smul _ tendsto_const_nhds
  apply tendsto_finsetProd
  intro e _
  by_cases he : ω e = true
  · simpa [he] using hq e
  · simpa [he] using tendsto_const_nhds.sub (hq e)

omit [Fintype E] in
theorem thinParameter_lt_one (p : E → Set.Icc (0 : ℝ) 1) (n : ℕ) (e : E) :
    (thinParameter p n e : ℝ) < 1 := by
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hr0 : 0 ≤ (n : ℝ) / ((n : ℝ) + 1) := div_nonneg hn (by positivity)
  have hr1 : (n : ℝ) / ((n : ℝ) + 1) < 1 :=
    (div_lt_one (by positivity)).mpr (by linarith)
  exact (mul_le_of_le_one_right hr0 (p e).2.2).trans_lt hr1

omit [Fintype E] in
theorem thinParameter_tendsto (p : E → Set.Icc (0 : ℝ) 1) (e : E) :
    Tendsto (fun n => (thinParameter p n e : ℝ)) atTop (nhds (p e : ℝ)) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) / ((n : ℝ) + 1)) atTop (nhds 1) :=
    tendsto_natCast_div_add_atTop 1
  simpa only [thinParameter, one_mul] using h.mul_const (p e : ℝ)

theorem joint_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    b * eventProb p (fun ω => Meets H ω ∅ o A) ≤
      eventProb p (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T) := by
  let q := thinParameter p
  let d : ℕ → ℝ := fun n => ∑ a : V,
    |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)|
  have hd : Tendsto d atTop (nhds 0) := by
    have h : Tendsto d atTop (nhds (∑ _a : V, (0:ℝ))) := by
      apply tendsto_finsetSum
      intro a _
      simpa only [sub_self, abs_zero] using
        ((eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ a T)).sub
          (tendsto_const_nhds (x := eventProb p (fun ω => Meets H ω ∅ a T)))).abs
    simpa using h
  have hbound (n : ℕ) (a : V) :
      eventProb p (fun ω => Meets H ω ∅ a T) - eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤ d n := by
    apply le_trans (show eventProb p (fun ω => Meets H ω ∅ a T) -
      eventProb (q n) (fun ω => Meets H ω ∅ a T) ≤
      |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| by
        simpa only [neg_sub] using neg_le_abs
          (eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)))
    change |eventProb (q n) (fun ω => Meets H ω ∅ a T) - eventProb p (fun ω => Meets H ω ∅ a T)| ≤
      ∑ j : V, |eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)|
    exact Finset.single_le_sum (fun j _ => abs_nonneg
      (eventProb (q n) (fun ω => Meets H ω ∅ j T) - eventProb p (fun ω => Meets H ω ∅ j T)))
      (Finset.mem_univ a)
  have hi (n : ℕ) := joint_comparison_of_lt_one H (q n) (thinParameter_lt_one p n)
    o A T (b - d n) (by intro a ha; linarith [hb a ha, hbound n a])
  have hl := ((tendsto_const_nhds (x := b)).sub hd).mul
    (eventProb_tendsto p q (thinParameter_tendsto p) (fun ω => Meets H ω ∅ o A))
  have hr := eventProb_tendsto p q (thinParameter_tendsto p)
    (fun ω => Meets H ω ∅ o A ∧ Meets H ω ∅ o T)
  have h := le_of_tendsto_of_tendsto hl hr (Filter.Eventually.of_forall hi)
  simpa only [sub_zero] using h

theorem eventProb_le_one (p : E → Set.Icc (0 : ℝ) 1) (P : (E → Bool) → Prop) :
    eventProb p P ≤ 1 := by
  rw [eventProb_eq_real]
  exact measureReal_le_one

theorem eventProb_mono (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop)
    (h : ∀ ω, P ω → Q ω) : eventProb p P ≤ eventProb p Q := by
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro ω
  by_cases hp : P ω
  · simp [hp, h ω hp]
  · simp only [hp, ite_false]
    split_ifs <;> norm_num

theorem eventProb_failure (p : E → Set.Icc (0 : ℝ) 1) (P Q : (E → Bool) → Prop) :
    eventProb p (fun ω => P ω ∧ ¬Q ω) = eventProb p P - eventProb p (fun ω => P ω ∧ Q ω) := by
  unfold eventProb
  rw [← integral_sub (Integrable.of_finite) (Integrable.of_finite)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  by_cases hp : P ω <;> by_cases hq : Q ω <;> simp [hp, hq]

/-- The strengthened hyperedge failure estimate, including all fixed-bit laws. -/
theorem failure_comparison_mul [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤
      b * eventProb p (fun ω => Meets H ω ∅ o A) := by
  rw [eventProb_failure]
  have h := joint_comparison H p o A T (1-b) hb
  nlinarith

theorem failure_comparison [Fintype V] (H : Hypergraph V E)
    (p : E → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Meets H ω ∅ a T)) :
    eventProb p (fun ω => Meets H ω ∅ o A ∧ ¬Meets H ω ∅ o T) ≤ b := by
  apply (failure_comparison_mul H p o A T b hb).trans
  exact mul_le_of_le_one_right hb0 (eventProb_le_one p _)

end FiniteLaw
namespace Site
variable (G : SimpleGraph V)

theorem connected_refl {ω : V → Bool} {x : V} (hx : ω x = true) :
    Connected G ω x x := ⟨hx, .refl⟩

theorem connected_open_right {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) : ω y = true := by
  obtain ⟨hx, h⟩ := h
  induction h with
  | refl => exact hx
  | tail _ hab _ => exact hab.2.2

theorem connected_extend {ω : V → Bool} {o x y : V}
    (h : Connected G ω o x) (hxy : G.Adj x y) (hy : ω y = true) :
    Connected G ω o y :=
  ⟨h.1, h.2.tail ⟨hxy, connected_open_right G h, hy⟩⟩

theorem connected_to_stars {ω : V → Bool} {x y : V}
    (h : Connected G ω x y) :
    HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y) := by
  obtain ⟨_, h⟩ := h
  induction h with
  | refl => exact .refl
  | @tail a b _ hab ih =>
    apply ih.trans
    apply Relation.ReflTransGen.trans (b := Sum.inr (a,b))
    · exact Relation.ReflTransGen.single
        ⟨a, hab.2.1, Set.disjoint_empty _, rfl, hab.1, Or.inl rfl⟩
    · exact Relation.ReflTransGen.single
        ⟨b, hab.2.2, Set.disjoint_empty _, ⟨hab.1, Or.inr rfl⟩, rfl⟩

theorem supported_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Supported G ω o z) (hz : z ∈ stars G x) (hx : ω x = true) :
    Connected G ω o x := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    obtain ⟨_, hc | hc⟩ := h
    · rcases hm with rfl | rfl
      · exact hc
      · exact connected_extend G hc huv hx
    · rcases hm with rfl | rfl
      · exact connected_extend G hc huv.symm hx
      · exact hc

theorem supported_of_label {ω : V → Bool} {o x : V} {z : Node V}
    (h : Connected G ω o x) (hz : z ∈ stars G x) : Supported G ω o z := by
  cases z with
  | inl y =>
    change y = x at hz
    subst y
    exact h
  | inr e =>
    obtain ⟨u,v⟩ := e
    obtain ⟨huv, hm⟩ := hz
    refine ⟨huv, ?_⟩
    rcases hm with rfl | rfl
    · exact Or.inl h
    · exact Or.inr h

theorem connected_of_stars {ω : V → Bool} {x y : V} (hx : ω x = true)
    (h : HyperedgeComparison.Connected (stars G) ω ∅ (Sum.inl x) (Sum.inl y)) :
    Connected G ω x y := by
  have hp : ∀ {z z' : Node V}, Supported G ω x z →
      HyperedgeComparison.Connected (stars G) ω ∅ z z' → Supported G ω x z' := by
    intro z z' hs hh
    induction hh with
    | refl => exact hs
    | @tail a b _ hab ih =>
      obtain ⟨e,he,_,ha,hb⟩ := hab
      exact supported_of_label G (supported_label G ih ha he) hb
  exact hp (z := Sum.inl x) (z' := Sum.inl y) (connected_refl G hx) h

theorem meets_to_stars {ω : V → Bool} {o : V} {T : Set V}
    (h : Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  obtain ⟨t,ht,hc⟩ := h
  exact ⟨Sum.inl t, ⟨t,ht,rfl⟩, connected_to_stars G hc⟩

theorem meets_of_stars {ω : V → Bool} {o : V} {T : Set V} (ho : ω o = true)
    (h : HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T)) :
    Meets G ω o T := by
  obtain ⟨_,⟨t,ht,rfl⟩,hc⟩ := h
  exact ⟨t,ht,connected_of_stars G ho hc⟩

theorem failure_subset_hyperedge {ω : V → Bool} {o : V} {A T : Set V}
    (h : Meets G ω o A ∧ ¬Meets G ω o T) :
    HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' A) ∧
    ¬HyperedgeComparison.Meets (stars G) ω ∅ (Sum.inl o) (Sum.inl '' T) := by
  refine ⟨meets_to_stars G h.1, ?_⟩
  intro ht
  obtain ⟨_,_,hc⟩ := h.1
  exact h.2 (meets_of_stars G hc.1 ht)

end Site

theorem site_failure_comparison [Fintype V] (G : SimpleGraph V)
    (p : V → Set.Icc (0 : ℝ) 1) (o : V) (A T : Set V) (b : ℝ) (hb0 : 0 ≤ b)
    (hb : ∀ a ∈ A, 1 - b ≤ eventProb p (fun ω => Site.Meets G ω a T)) :
    eventProb p (fun ω => Site.Meets G ω o A ∧ ¬Site.Meets G ω o T) ≤ b := by
  apply (eventProb_mono p _ _ (fun _ => Site.failure_subset_hyperedge G)).trans
  apply failure_comparison (Site.stars G) p (Sum.inl o) (Sum.inl '' A) (Sum.inl '' T) b hb0
  rintro _ ⟨a,ha,rfl⟩
  exact (hb a ha).trans (eventProb_mono p _ _ (fun _ => Site.meets_to_stars G))

end HyperedgeComparison

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

namespace LatticeGraph
variable (G : LatticeGraph)

theorem bondAdj_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondAdj ω' x y ↔ G.BondAdj ω x y := by
  constructor <;> rintro ⟨e,he,hxy,ho⟩
  · exact ⟨e,he,hxy,(h e he) ▸ ho⟩
  · exact ⟨e,he,hxy,(h e he).symm ▸ ho⟩

theorem bondConn_determined (ω ω' : BondConfig)
    (h : ∀ e ∈ G.edges, ω' e = ω e) (x y : G.Node) :
    G.BondConn ω' x y ↔ G.BondConn ω x y := by
  have he : G.BondAdj ω' = G.BondAdj ω := by
    funext a b; exact propext (G.bondAdj_determined ω ω' h a b)
  simp only [BondConn,he]

theorem siteConn_determined (ω ω' : SiteConfig)
    (h : ∀ x ∈ G.vertices, ω' x = ω x) (x y : G.Node) :
    G.SiteConn ω' x y ↔ G.SiteConn ω x y := by
  have he : (fun z : G.Node => ω' z.1) = fun z => ω z.1 := by
    funext z; exact h z.1 z.2
  simp only [SiteConn,he]

theorem siteMeets_determined (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) G.vertices (fun ω => G.SiteMeets ω o T) := by
  intro ω ω' h
  exact propext (exists_congr (fun y => and_congr_right (fun _ => G.siteConn_determined ω ω' h o y)))

theorem siteMeets_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o T} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T}) := by
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | G.SiteMeets ω o T}
    (fun ω ω' h => eq_iff_iff.mp (G.siteMeets_determined o T ω ω' h))]
  rw [HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]

theorem siteObservable_probability (p : Vertex → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.SiteMeets ω)} =
      HyperedgeComparison.eventProb (fun x : G.Node => p x.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Site.Meets G.graph ω o {y | y.1 ∈ T})) := by
  have hd : ∀ ω ω', (∀ e ∈ G.vertices, ω' e = ω e) →
      (φ (G.SiteMeets ω') ↔ φ (G.SiteMeets ω)) := by
    intro ω ω' he
    have hm : G.SiteMeets ω' = G.SiteMeets ω := by
      funext o T; exact G.siteMeets_determined o T ω ω' he
    rw [hm]
  rw [Measure.real_def,ProductCylinder.probability_determined G.vertices p {ω | φ (G.SiteMeets ω)} hd,
    HyperedgeComparison.eventProb_eq_real]
  congr 1
  congr 1
  ext ξ
  have he : (fun x : G.Node => ProductCylinder.extend G.vertices ξ x.1) = ξ := by
    funext x; simp [ProductCylinder.extend,x.2]
  have hm : G.SiteMeets (ProductCylinder.extend G.vertices ξ) =
      fun o T => HyperedgeComparison.Site.Meets G.graph ξ o {y | y.1 ∈ T} := by
    funext o T
    apply propext
    simp only [SiteMeets,SiteConn,he,HyperedgeComparison.Site.Meets,Set.mem_ofPred_eq]
  simp only [Set.mem_ofPred_eq,hm]

/-- The comparison is now attached to actual finite lattice bond paths and
arbitrary independent laws on the entire lattice, not an assumed interface. -/
theorem bond_failure_comparison (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.BondMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o A ∧ ¬G.BondMeets ω o T} ≤ b := by
  rw [G.bondObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.bondMeets_probability] using hb a ha

theorem site_failure_comparison (p : Vertex → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.SiteMeets ω a T}) :
    (ProductCylinder.law p).real {ω | G.SiteMeets ω o A ∧ ¬G.SiteMeets ω o T} ≤ b := by
  rw [G.siteObservable_probability p (fun M => M o A ∧ ¬M o T)]
  apply HyperedgeComparison.site_failure_comparison _ _ _ _ _ b hb0
  intro a ha
  simpa only [G.siteMeets_probability] using hb a ha

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticePaths ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

namespace Model
end Model

namespace Box
end Box

namespace LatticeGraph
variable (G : LatticeGraph)
theorem conn_determined (m : Model) (ω ω' : m.Config)
    (h : ∀ e ∈ G.bits m, ω' e = ω e) (x y : G.Node) :
    G.Conn m ω' x y ↔ G.Conn m ω x y := by
  cases m
  · exact G.bondConn_determined ω ω' h x y
  · exact G.siteConn_determined ω ω' h x y

theorem meets_determined (m : Model) (o : G.Node) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) (G.bits m) (fun ω => G.Meets m ω o T) := by
  intro ω ω' h
  apply propext
  simp only [Meets,G.conn_determined m ω ω' h]

theorem measurableSet_meets (m : Model) (o : G.Node) (T : Set Vertex) :
    MeasurableSet {ω | G.Meets m ω o T} :=
  ProductCylinder.measurableSet_determined _ _ (fun ω ω' h =>
    eq_iff_iff.mp (G.meets_determined m o T ω ω' h))

theorem failure_comparison (m : Model) (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (A T : Set Vertex) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ a : G.Node, a.1 ∈ A →
      1-b ≤ (ProductCylinder.law p).real {ω | G.Meets m ω a T}) :
    (ProductCylinder.law p).real {ω | G.Meets m ω o A ∧ ¬G.Meets m ω o T} ≤ b := by
  cases m
  · exact G.bond_failure_comparison p o A T hb0 hb
  · exact G.site_failure_comparison p o A T hb0 hb

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

/-! The exact revealed-history law used by the adaptive queue.  In particular,
classifications depending only on revealed values do not change fresh bits. -/
namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem sum_pattern_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) :
    ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) = 1 := by
  simpa only [Set.mem_univ,Set.ofPred_true,probReal_univ,mul_one] using
    (measure_select p J (fun _ => Set.univ) (fun _ => MeasurableSet.univ)).symm

omit [Countable E] in
theorem fixedParameter_congr (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    {ξ ξ' : E → Bool} (h : ∀ e ∈ J, ξ e = ξ' e) :
    fixedParameter p J ξ = fixedParameter p J ξ' := by
  funext e
  by_cases he : e ∈ J
  · simp only [fixedParameter,he,ite_true,h e he]
  · simp only [fixedParameter,he,ite_false]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E I : Type}

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem select_probability_le (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real
      (A a) ≤ b) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} ≤ b := by
  rw [measure_select p J A hA]
  calc
    _ ≤ ∑ a : J → Bool, (ProductCylinder.law p).real
        (pattern J (ProductCylinder.extend J a)) * b :=
      Finset.sum_le_sum (fun a _ => mul_le_mul_of_nonneg_left (hb a) measureReal_nonneg)
    _ = b := by rw [←Finset.sum_mul,sum_pattern_real,one_mul]

end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.ConditionalQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem conditionalProbability_determined (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) :
    ProductCylinder.DeterminedBy J (conditionalProbability p J C) := by
  intro ω ω' h
  unfold conditionalProbability
  rw [fixedParameter_congr p J h]

end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.ShellProbability ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace FiniteAssociation
open Classical
variable {E : Type}

end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end ProductCylinder

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem goodRelays_determined (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (T : Set Vertex) (τ : ℝ) : ProductCylinder.DeterminedBy J (G.goodRelays m p J T τ) := by
  intro ω ω' h
  ext v
  simp only [goodRelays,Set.mem_ofPred_eq,conditionalProbability_determined p J _ ω ω' h]

theorem random_relay_failure (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} ≤ τ := by
  let A (a : J → Bool) : Set m.Config :=
    {ω | G.Meets m ω o (G.goodRelays m p J T τ (ProductCylinder.extend J a)) ∧ ¬G.Meets m ω o T}
  have he : {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} =
      {ω | ω ∈ A (J.restrict ω)} := by
    ext ω
    simp only [A,Set.mem_ofPred_eq,
      ProductCylinder.determinedBy_eq_extend (G.goodRelays_determined m p J T τ) ω]
  rw [he]
  apply select_probability_le p J A
  · intro a
    exact (G.measurableSet_meets m _ _).inter (G.measurableSet_meets m _ _).compl
  · intro a
    apply G.failure_comparison m _ o _ T hτ
    intro v ⟨u,hu,hh⟩
    have heu : u = v := Subtype.ext hu
    subst u
    exact hh.le

end CriticalZ3.LatticeGraph

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.random_relay_failure := @_root_.OAI.CriticalZ3.LatticeGraph.random_relay_failure
