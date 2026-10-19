-- Prove2me | solution 1 for OAI.CriticalZ3.exists_scales
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:06:01.896046+00:00
-- url     : https://prove2.me/submissions/3aa592f2-3381-4000-9a39-e460230cf7f1

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Scales.lean:L143-L183
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.exists_scales. The node keeps its source
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
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Theorems.Thm_OAI_CriticalZ3_bond_lower_quarterFaces
import Theorems.Thm_OAI_CriticalZ3_site_lower_quarterFaces
import Theorems.Thm_OAI_CriticalZ3_zero_one_of_finite_alteration

-- ---- from OAI.Probability.CriticalZ3.Basic ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uE uOmega uV

-- [generator] trimmed: open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory

namespace CriticalZ3

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

/-- A path with finitely many types of exceptional arrivals ends in the
unperturbed component of its starting point or of an exceptional vertex. -/
theorem rtg_covered_by_roots {V : Type uV} {r s : V → V → Prop} {F : Set V}
    (h : ∀ a b, r a b → s a b ∨ b ∈ F) {x y : V}
    (hxy : Relation.ReflTransGen r x y) :
    ∃ z ∈ insert x F, Relation.ReflTransGen s z y := by
  induction hxy with
  | refl => exact ⟨x, Set.mem_insert x F, .refl⟩
  | @tail a b _ hab ih =>
    rcases h a b hab with hs | hb
    · obtain ⟨z,hz,hza⟩ := ih
      exact ⟨z,hz,hza.tail hs⟩
    · exact ⟨b,Set.mem_insert_of_mem x hb,.refl⟩

theorem finite_components_of_finite_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hs : ∀ x, {y | Relation.ReflTransGen s x y}.Finite) (x : V) :
    {y | Relation.ReflTransGen r x y}.Finite := by
  apply ((hF.insert x).biUnion (fun z _ => hs z)).subset
  intro y hy
  obtain ⟨z,hz,hzy⟩ := rtg_covered_by_roots h hy
  exact Set.mem_iUnion₂.mpr ⟨z,hz,hzy⟩

theorem infinite_component_of_perturbation {V : Type uV} {r s : V → V → Prop}
    {F : Set V} (hF : F.Finite) (h : ∀ a b, r a b → s a b ∨ b ∈ F)
    (hr : ∃ x, {y | Relation.ReflTransGen r x y}.Infinite) :
    ∃ x, {y | Relation.ReflTransGen s x y}.Infinite := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx⟩ := hr
  exact hx (finite_components_of_finite_perturbation hF h hn x)

theorem nearestNeighbor_iff_steps (x y : Vertex) :
    NearestNeighbor x y ↔ ∃ i, y = step x i ∨ y = backstep x i := by
  constructor
  · rintro ⟨i, hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,backstep_step])⟩
  · rintro ⟨i,hi | hi⟩
    · exact ⟨i,Or.inl hi⟩
    · exact ⟨i,Or.inr (by rw [hi,step_backstep])⟩

theorem finite_neighbors (x : Vertex) : {y | NearestNeighbor x y}.Finite := by
  apply ((Set.finite_range (step x)).union (Set.finite_range (backstep x))).subset
  intro y hy
  obtain ⟨i,hi | hi⟩ := (nearestNeighbor_iff_steps x y).mp hy
  · exact Or.inl ⟨i,hi.symm⟩
  · exact Or.inr ⟨i,hi.symm⟩

theorem measurableSet_bondExistsInfinite : MeasurableSet bondExistsInfinite := by
  simpa only [bondExistsInfinite,bondInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_bondInfiniteAt x))

theorem measurableSet_siteExistsInfinite : MeasurableSet siteExistsInfinite := by
  simpa only [siteExistsInfinite,siteInfiniteAt,Set.iUnion_ofPred] using
    (MeasurableSet.iUnion (fun x => measurableSet_siteInfiniteAt x))

theorem bondExistsInfinite_of_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ bondExistsInfinite) :
    ω' ∈ bondExistsInfinite := by
  let F : Set Vertex := ((fun e : Bond => e.1) '' (J : Set Bond)) ∪
    ((fun e : Bond => step e.1 e.2) '' (J : Set Bond))
  have hF : F.Finite := (J.finite_toSet.image _).union (J.finite_toSet.image _)
  apply infinite_component_of_perturbation hF (s := BondOpen ω') (r := BondOpen ω) _ hω
  intro a b hab
  rcases hab with ⟨i,hb,hi⟩ | ⟨i,ha,hi⟩
  · by_cases hj : (a,i) ∈ J
    · exact Or.inr (Or.inr ⟨(a,i),hj,hb.symm⟩)
    · exact Or.inl (Or.inl ⟨i,hb,(hagree (a,i) hj).trans hi⟩)
  · by_cases hj : (b,i) ∈ J
    · exact Or.inr (Or.inl ⟨(b,i),hj,rfl⟩)
    · exact Or.inl (Or.inr ⟨i,ha,(hagree (b,i) hj).trans hi⟩)

theorem bondExistsInfinite_finite_alteration {ω ω' : BondConfig}
    (J : Finset Bond) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ bondExistsInfinite ↔ ω ∈ bondExistsInfinite :=
  ⟨bondExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    bondExistsInfinite_of_finite_alteration J hagree⟩

theorem siteOpen_open_left {ω : SiteConfig} {x y : Vertex} (h : SiteOpen ω x y) :
    ω x = true := h.2.1

theorem siteRtg_from_closed {ω : SiteConfig} {x y : Vertex} (hx : ω x ≠ true)
    (h : Relation.ReflTransGen (SiteOpen ω) x y) : y = x := by
  induction h with
  | refl => rfl
  | @tail a b _ hab ih =>
    exact (hx (ih ▸ siteOpen_open_left hab)).elim

theorem siteInfinite_iff_rtg_infinite (ω : SiteConfig) (x : Vertex) :
    (siteCluster ω x).Infinite ↔ {y | Relation.ReflTransGen (SiteOpen ω) x y}.Infinite := by
  by_cases hx : ω x = true
  · simp only [siteCluster,SiteConnected,hx,true_and]
  · have he : {y | Relation.ReflTransGen (SiteOpen ω) x y} = {x} := by
      ext y
      exact ⟨siteRtg_from_closed hx, fun hy => by rw [Set.mem_singleton_iff.mp hy]; exact .refl⟩
    simp [siteCluster,SiteConnected,hx,he]

theorem siteExistsInfinite_of_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) (hω : ω ∈ siteExistsInfinite) :
    ω' ∈ siteExistsInfinite := by
  let F : Set Vertex := (J : Set Vertex) ∪ ⋃ x ∈ (J : Set Vertex), {y | NearestNeighbor x y}
  have hF : F.Finite := J.finite_toSet.union
    (J.finite_toSet.biUnion (fun x _ => finite_neighbors x))
  have hh : ∀ a b, SiteOpen ω a b → SiteOpen ω' a b ∨ b ∈ F := by
    intro a b hab
    by_cases ha : a ∈ J
    · exact Or.inr (Or.inr (Set.mem_iUnion₂.mpr ⟨a,ha,hab.1⟩))
    by_cases hb : b ∈ J
    · exact Or.inr (Or.inl hb)
    · exact Or.inl ⟨hab.1,(hagree a ha).trans hab.2.1,(hagree b hb).trans hab.2.2⟩
  obtain ⟨x,hx⟩ := hω
  obtain ⟨y,hy⟩ := infinite_component_of_perturbation hF hh
    ⟨x,(siteInfinite_iff_rtg_infinite ω x).mp hx⟩
  exact ⟨y,(siteInfinite_iff_rtg_infinite ω' y).mpr hy⟩

theorem siteExistsInfinite_finite_alteration {ω ω' : SiteConfig}
    (J : Finset Vertex) (hagree : ∀ e ∉ J, ω' e = ω e) :
    ω' ∈ siteExistsInfinite ↔ ω ∈ siteExistsInfinite :=
  ⟨siteExistsInfinite_of_finite_alteration J (fun e he => (hagree e he).symm),
    siteExistsInfinite_of_finite_alteration J hagree⟩

open Filter
open scoped Topology

theorem bondExistsInfinite_zero_one (p : ℝ) :
    bondLaw p bondExistsInfinite = 0 ∨ bondLaw p bondExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (bondLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    bondExistsInfinite measurableSet_bondExistsInfinite
  intro J ω ω' h
  exact bondExistsInfinite_finite_alteration J h

theorem siteExistsInfinite_zero_one (p : ℝ) :
    siteLaw p siteExistsInfinite = 0 ∨ siteLaw p siteExistsInfinite = 1 := by
  apply zero_one_of_finite_alteration (siteLaw p)
    (iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id))
    siteExistsInfinite measurableSet_siteExistsInfinite
  intro J ω ω' h
  exact siteExistsInfinite_finite_alteration J h

theorem bondExistsInfinite_one {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) :
    bondLaw p bondExistsInfinite = 1 := by
  apply (bondExistsInfinite_zero_one p).resolve_left
  have h : 0 < bondLaw p bondExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

theorem siteExistsInfinite_one {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) :
    siteLaw p siteExistsInfinite = 1 := by
  apply (siteExistsInfinite_zero_one p).resolve_left
  have h : 0 < siteLaw p siteExistsInfinite := hp.trans_le
    (measure_mono (fun _ h => ⟨0,h⟩))
  exact ne_of_gt h

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

theorem bondSeedInfinite_mono (c : Vertex) : Monotone (bondSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩
theorem siteSeedInfinite_mono (c : Vertex) : Monotone (siteSeedInfinite c) := by
  intro m n h ω ⟨x,hx,hi⟩
  exact ⟨x,cube_mono c h hx,hi⟩

theorem measurableSet_bondSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (bondSeedInfinite c n) := by
  simp only [bondSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_bondInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]
theorem measurableSet_siteSeedInfinite (c : Vertex) (n : ℕ) :
    MeasurableSet (siteSeedInfinite c n) := by
  simp only [siteSeedInfinite,Set.ofPred_exists,Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro x
  by_cases hx : x ∈ cube c n
  · simpa only [hx,Set.ofPred_true,Set.univ_inter,Set.ofPred_mem_eq] using measurableSet_siteInfiniteAt x
  · simp only [hx,Set.ofPred_false,Set.empty_inter,MeasurableSet.empty]

theorem iUnion_bondSeedInfinite (c : Vertex) :
    (⋃ n, bondSeedInfinite c n) = bondExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,bondSeedInfinite,bondExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩
theorem iUnion_siteSeedInfinite (c : Vertex) :
    (⋃ n, siteSeedInfinite c n) = siteExistsInfinite := by
  ext ω
  simp only [Set.mem_iUnion,siteSeedInfinite,siteExistsInfinite,Set.mem_ofPred_eq]
  constructor
  · rintro ⟨n,x,_,hx⟩; exact ⟨x,hx⟩
  · rintro ⟨x,hx⟩
    obtain ⟨n,hn⟩ := exists_mem_cube c x
    exact ⟨n,x,hn,hx⟩

theorem bondSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < bondLaw p (bondInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => bondLaw p (bondSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := bondLaw p) (bondSeedInfinite_mono c)
  simpa only [iUnion_bondSeedInfinite,bondExistsInfinite_one hp,Function.comp_def] using h

theorem siteSeedInfinite_tendsto_one {p : ℝ}
    (hp : 0 < siteLaw p (siteInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun n => siteLaw p (siteSeedInfinite c n)) atTop (𝓝 1) := by
  have h := tendsto_measure_iUnion_atTop (μ := siteLaw p) (siteSeedInfinite_mono c)
  simpa only [iUnion_siteSeedInfinite,siteExistsInfinite_one hp,Function.comp_def] using h

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.QuarterFaces ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

namespace SignedSymmetry

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

theorem bondSeedMiss_tendsto_zero {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun m => (bondLaw p).real (bondSeedInfinite c m)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp (bondSeedInfinite_tendsto_one hp c)
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa only [measureReal_compl (measurableSet_bondSeedInfinite c _),probReal_univ,
    Measure.real_def,measure_univ,ENNReal.toReal_one,sub_self,Function.comp_def] using h'

theorem siteSeedMiss_tendsto_zero {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) (c : Vertex) :
    Tendsto (fun m => (siteLaw p).real (siteSeedInfinite c m)ᶜ) atTop (𝓝 0) := by
  have h := (ENNReal.tendsto_toReal (by simp : (1 : ENNReal) ≠ ⊤)).comp (siteSeedInfinite_tendsto_one hp c)
  have h' := (tendsto_const_nhds (x := (1 : ℝ))).sub h
  simpa only [measureReal_compl (measurableSet_siteSeedInfinite c _),probReal_univ,
    Measure.real_def,measure_univ,ENNReal.toReal_one,sub_self,Function.comp_def] using h'

theorem exists_bondSeed {p : ℝ} (hp : 0 < bondLaw p (bondInfiniteAt 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (bondLaw p).real (bondSeedInfinite 0 m)ᶜ < ε^24 := by
  have h := (bondSeedMiss_tendsto_zero hp 0).eventually (eventually_lt_nhds (pow_pos hε 24))
  exact (h.and (eventually_gt_atTop 0)).exists.imp (fun _ h => h.symm)

theorem exists_siteSeed {p : ℝ} (hp : 0 < siteLaw p (siteInfiniteAt 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 0 < m ∧ (siteLaw p).real (siteSeedInfinite 0 m)ᶜ < ε^24 := by
  have h := (siteSeedMiss_tendsto_zero hp 0).eventually (eventually_lt_nhds (pow_pos hε 24))
  exact (h.and (eventually_gt_atTop 0)).exists.imp (fun _ h => h.symm)

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Scales ----
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

theorem error_budgets {f : ℝ} (hf0 : 0 < f) (hf1 : f < 1) :
    ∃ δ η τ γ : ℝ,
      δ ∈ Set.Ioo 0 1 ∧ η ∈ Set.Ioo 0 1 ∧ τ ∈ Set.Ioo 0 1 ∧ γ ∈ Set.Ioo 0 1 ∧
      δ+52*η/δ < f ∧ τ < η/4 ∧ γ < δ ∧ 2*γ/τ < η/4 := by
  let δ := f/2
  let η := δ*f/208
  let τ := η/8
  let γ := min (δ/2) (τ*η/16)
  have hd0 : 0 < δ := by dsimp [δ]; positivity
  have hd1 : δ < 1 := by dsimp [δ]; linarith
  have he0 : 0 < η := by dsimp [η]; positivity
  have he1 : η < 1 := by dsimp [η]; nlinarith
  have ht0 : 0 < τ := by dsimp [τ]; positivity
  have ht1 : τ < 1 := by dsimp [τ]; linarith
  have hg0 : 0 < γ := lt_min (by positivity) (by positivity)
  have hgd : γ ≤ δ/2 := min_le_left _ _
  have hge : γ ≤ τ*η/16 := min_le_right _ _
  refine ⟨δ,η,τ,γ,⟨hd0,hd1⟩,⟨he0,he1⟩,⟨ht0,ht1⟩,⟨hg0,by linarith⟩,?_,?_,?_,?_⟩
  · have heq : 52*η/δ = f/4 := by dsimp [η]; field_simp; ring
    rw [heq]
    dsimp [δ]
    linarith
  · dsimp [τ]; linarith
  · linarith
  · apply (div_lt_iff₀ ht0).mpr
    nlinarith

end CriticalScales

namespace CriticalZ3
-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
namespace Model
theorem law_eq_product (m : Model) (p : ℝ) :
    m.law p = ProductCylinder.law (fun _ => parameter p) := by cases m <;> rfl

theorem law_coe_eq_product (m : Model) (q : Set.Icc (0 : ℝ) 1) :
    m.law q = ProductCylinder.law (fun _ => q) := by
  rw [law_eq_product]
  have h : parameter (q : ℝ) = q := Subtype.ext (parameter_coe q.property)
  rw [h]

theorem exists_seed (m : Model) {p ε : ℝ} (hp : 0 < m.law p (m.InfiniteAt 0)) (hε : 0 < ε) :
    ∃ r : ℕ, 0 < r ∧ (m.law p).real (m.SeedInfinite 0 r)ᶜ < ε^24 := by
  cases m
  · exact exists_bondSeed hp hε
  · exact exists_siteSeed hp hε

theorem lower_quarterFaces (m : Model) {p γ : ℝ} (hp : 0 < p) (hγ : 0 < γ)
    {r : ℕ} (hseed : (m.law p).real (m.SeedInfinite 0 r)ᶜ < (γ/2)^24)
    (s : Finset ℕ) (hs : ∀ n ∈ s, r ≤ n) :
    ∃ q ∈ Set.Ioo (p/2) p, ∀ n ∈ s, ∀ c f,
      1-γ < (m.law q).real (m.SeedReaches c r n (QuarterFace c n f)) := by
  cases m
  · simpa only [law,seedReaches_bond] using bond_lower_quarterFaces hp hγ hseed s hs
  · exact site_lower_quarterFaces hp hγ hseed s hs
end Model

theorem exists_scales (model : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < model.law p (model.InfiniteAt 0)) : ∃ s : ScaleData model, s.p = p := by
  obtain ⟨δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb⟩ := CriticalScales.error_budgets
    CriticalScales.contourError_pos (CriticalScales.contourError_lt_half.trans (by norm_num))
  obtain ⟨a,ha,hseed⟩ := model.exists_seed hInf (show 0 < γ/2 by linarith [hγ.1])
  let ρ : ℝ := (p/2)^(Box.seedCard model a+1)
  have hρ : 0 < ρ := pow_pos (by linarith) _
  obtain ⟨K,hK⟩ := exists_nat_gt (16/(ρ*η))
  have hK0 : 0 < K := by
    have : 0 < (K:ℝ) := (div_pos (by norm_num) (mul_pos hρ hη.1)).trans hK
    exact_mod_cast this
  have hKb : 4/((K:ℝ)*ρ) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hρ hη.1)).mp hK
    apply (div_lt_iff₀ (mul_pos (by exact_mod_cast hK0) hρ)).mpr
    nlinarith
  let α : ℝ := (1-p)^(K*(8*a+5)^3)
  have hα : 0 < α := pow_pos (by linarith) _
  obtain ⟨d,hd⟩ := exists_nat_gt (4/(α*η))
  have hd0 : 0 < d := by
    have : 0 < (d:ℝ) := (div_pos (by norm_num) (mul_pos hα hη.1)).trans hd
    exact_mod_cast this
  let R := a+d
  have haR : a < R := by dsimp [R]; omega
  have hRb : 1/(α*(R-a:ℕ)) < η/4 := by
    have hh := (div_lt_iff₀ (mul_pos hα hη.1)).mp hd
    have he : R-a = d := by dsimp [R]; omega
    rw [he]
    apply (div_lt_iff₀ (mul_pos hα (by exact_mod_cast hd0))).mpr
    nlinarith
  let r := 100*(R+1)+1
  have hlr : 100*(R+1) < r := by dsimp [r]; omega
  have har : a ≤ r := by omega
  obtain ⟨q,hq,hfaces⟩ := model.lower_quarterFaces hp hγ.1 hseed
    {2*r,2*r+1,10*r} (by intro n hn; simp only [Finset.mem_insert,Finset.mem_singleton] at hn; omega)
  let q' : Set.Icc (0:ℝ) 1 := ⟨q,⟨by linarith [hq.1],le_of_lt (hq.2.trans hp1)⟩⟩
  refine ⟨⟨p,hp,hp1,q',hq.1,hq.2,δ,η,τ,γ,hδ,hη,hτ,hγ,hb,hτb,hγδ,hγb,
    a,K,R,r,ha,hK0,haR,hlr,hKb,hRb,?_⟩,rfl⟩
  intro n hn c f
  have hh := hfaces n hn c f
  rw [show q = (q':ℝ) from rfl,model.law_coe_eq_product q'] at hh
  exact hh

namespace ScaleData
variable {model : Model} (s : ScaleData model)

end ScaleData
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3
open _root_.MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Filter Topology
open _root_.MeasureTheory ProbabilityTheory Classical


theorem solution : type_of% @_root_.OAI.CriticalZ3.exists_scales := @_root_.OAI.CriticalZ3.exists_scales
