-- Prove2me | solution 2 for OAI.CriticalZ3.critical_no_infinite
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:03:26.310224+00:00
-- url     : https://prove2.me/submissions/b2fca2c4-1930-4363-b274-8a3f560536e8

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Main.lean:L107-L110
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.CriticalZ3.critical_no_infinite.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_CriticalZ3_critical_no_infinite) verbatim and is proved by it.
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
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls
import Definitions.Def_OAI_Probability_CriticalZ3_Coarse
import Definitions.Def_OAI_Probability_CriticalZ3_AdaptiveReveals
import Definitions.Def_OAI_Probability_CriticalZ3_Exploration
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationInvariant
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationConnectivity
import Definitions.Def_OAI_Probability_CriticalZ3_ExplorationSurvival
import Definitions.Def_OAI_Probability_CriticalZ3_Subunit
import Theorems.Thm_OAI_AdaptiveReveals_Scheme_hit_bound
import Theorems.Thm_OAI_BlockPercolation_survival
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_badMass_bound
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_colored_advance
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_hit_of_bad_subset
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_valid_advance
import Theorems.Thm_OAI_CriticalZ3_Coarse_Exploration_visited_advance_mono
import Theorems.Thm_OAI_CriticalZ3_Coarse_cube_unique
import Theorems.Thm_OAI_CriticalZ3_Coarse_initial_valid
import Theorems.Thm_OAI_CriticalZ3_exists_scales
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability
import Theorems.Thm_OAI_InfiniteConditioning_map_replace
import Theorems.Thm_OAI_InfiniteConditioning_pattern_inter
import Theorems.Thm_OAI_PlanarBoundary_blocked_bound
import Theorems.Thm_OAI_PlanarBoundary_encoded_budget_hasSum
import Theorems.Thm_OAI_PlanarBoundary_finite_good_subset

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

theorem bond_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < bondLaw p (bondInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial⟩

theorem site_supercritical_nonempty :
    {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧ 0 < siteLaw p (siteInfiniteAt 0)}.Nonempty :=
  ⟨1, by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial⟩

theorem bondCritical_mem : bondCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf bond_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, bondLaw_one_infinite]; trivial)

theorem siteCritical_mem : siteCritical ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact le_csInf site_supercritical_nonempty (fun _ hp => hp.1.1)
  · exact csInf_le ⟨0, fun _ hp => hp.1.1⟩ (by norm_num only [Set.mem_ofPred_eq, Set.mem_Icc, siteLaw_one_infinite]; trivial)

theorem bond_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < bondCritical) : bondLaw p (bondInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : bondCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

theorem site_subcritical_origin {p : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hlt : p < siteCritical) : siteLaw p (siteInfiniteAt 0) = 0 := by
  by_contra h
  have hpos := bot_lt_iff_ne_bot.mpr h
  have hc : siteCritical ≤ p := csInf_le ⟨0, fun _ hr => hr.1.1⟩ ⟨hp, hpos⟩
  exact (not_le_of_gt hlt) hc

/-! Finite alterations, tail invariance, and the infinite seed limit. -/

open Filter
open scoped Topology

theorem cube_mono (c : Vertex) : Monotone (cube c) := by
  intro m n h x hx
  rw [mem_cube] at hx ⊢
  intro i
  have hn : (m : ℤ) ≤ n := by exact_mod_cast h
  obtain ⟨h₁,h₂⟩ := hx i
  constructor <;> omega

end CriticalZ3

end OAI

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

theorem map_reindex (e : E ≃ F) (p : F → Set.Icc (0 : ℝ) 1) :
    (law p).map (fun ω i => ω (e i)) = law (fun i => p (e i)) := by
  have h := Measure.infinitePi_map_piCongrLeft
    (fun i => bernoulliMeasure true false (p (e i))) e.symm
  have he : ((MeasurableEquiv.piCongrLeft (fun _ : E => Bool) e.symm) : (F → Bool) → E → Bool) =
      fun ω i => ω (e i) := by
    funext ω i
    change Equiv.piCongrLeft (fun _ : E => Bool) e.symm ω i = _
    rw [Equiv.piCongrLeft_apply_eq_cast]
    rfl
  simpa only [law,Equiv.apply_symm_apply,he] using h

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

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

theorem bond_apply (S : SignedSymmetry) (e : Bond) :
    S.bond e = (S.vertex e.1+S.edgeShift e.2,S.perm.symm e.2) := rfl

theorem edge_spec (S : SignedSymmetry) (e : Bond) :
    (S.vertex e.1 = (S.bond e).1 ∧ S.vertex (step e.1 e.2) = step (S.bond e).1 (S.bond e).2) ∨
    (S.vertex e.1 = step (S.bond e).1 (S.bond e).2 ∧ S.vertex (step e.1 e.2) = (S.bond e).1) := by
  have hi (i : Fin 3) : (e.2 = S.perm i) ↔ (S.perm.symm e.2 = i) := by
    constructor
    · intro h; rw [h,Equiv.symm_apply_apply]
    · intro h; rw [←h,Equiv.apply_symm_apply]
  by_cases hs : S.signs (S.perm.symm e.2) = true
  · left
    constructor
    · funext i
      simp [bond_apply,edgeShift,hs]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i = true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]
  · right
    constructor
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,he]
      · simp [bond_apply,vertex,edgeShift,step,hs,he]
    · funext i
      by_cases he : S.perm.symm e.2 = i
      · have hsi : S.signs i ≠ true := he ▸ hs
        simp [bond_apply,vertex,edgeShift,step,hsi,hi,he]
        ; ring
      · simp [bond_apply,vertex,edgeShift,step,hs,hi,he]

theorem endpoints_map (S : SignedSymmetry) (e : Bond) (x y : Vertex) :
    Endpoints (S.bond e) (S.vertex x) (S.vertex y) ↔ Endpoints e x y := by
  rcases S.edge_spec e with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
  · unfold Endpoints
    rw [←h₂,←h₁]
    simp only [Equiv.apply_eq_iff_eq]
  · unfold Endpoints
    rw [←h₁,←h₂]
    simp only [Equiv.apply_eq_iff_eq]
    tauto

theorem bondOpen_iff (ω : BondConfig) (x y : Vertex) :
    BondOpen ω x y ↔ ∃ e, ω e = true ∧ Endpoints e x y := by
  constructor
  · rintro (⟨i,h,hω⟩ | ⟨i,h,hω⟩)
    · exact ⟨(x,i),hω,Or.inl ⟨rfl,h⟩⟩
    · exact ⟨(y,i),hω,Or.inr ⟨rfl,h⟩⟩
  · rintro ⟨⟨z,i⟩,hω,⟨rfl,rfl⟩ | ⟨rfl,rfl⟩⟩
    · exact Or.inl ⟨i,rfl,hω⟩
    · exact Or.inr ⟨i,rfl,hω⟩

theorem bondOpen_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondOpen (fun e => ω (S.bond e)) x y ↔ BondOpen ω (S.vertex x) (S.vertex y) := by
  simp_rw [bondOpen_iff]
  constructor
  · rintro ⟨e,he,hxy⟩
    exact ⟨S.bond e,he,(S.endpoints_map e x y).mpr hxy⟩
  · rintro ⟨e,he,hxy⟩
    refine ⟨S.bond.symm e,by simpa using he,?_⟩
    apply (S.endpoints_map (S.bond.symm e) x y).mp
    simpa using hxy

theorem neighbor_map (S : SignedSymmetry) (x y : Vertex) :
    NearestNeighbor x y ↔ NearestNeighbor (S.vertex x) (S.vertex y) := by
  have he (x y : Vertex) : NearestNeighbor x y ↔ BondOpen (fun _ => true) x y := by
    simp only [NearestNeighbor,BondOpen,and_true]
    rw [exists_or]
  simpa only [he] using S.bondOpen_map (fun _ => true) x y

theorem siteOpen_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteOpen (fun e => ω (S.vertex e)) x y ↔ SiteOpen ω (S.vertex x) (S.vertex y) := by
  simp only [SiteOpen,←S.neighbor_map]

end SignedSymmetry
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.QuarterFaces ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
end Lean433MeasurableOfEval

namespace OAI

universe uE uI uV uW

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

/-! The 24 signed-coordinate quarter-faces, symmetry and the Harris root bound.
The probability statements here are for the actual infinite lattice laws. -/
namespace CriticalZ3
open Classical

theorem rtg_equiv_iff {V : Type uV} {W : Type uW} (e : V ≃ W) {r : V → V → Prop} {s : W → W → Prop}
    (h : ∀ x y, r x y ↔ s (e x) (e y)) (x y : V) :
    Relation.ReflTransGen r x y ↔ Relation.ReflTransGen s (e x) (e y) := by
  constructor
  · intro hp
    exact Relation.ReflTransGen.lift e (fun a b h' => (h a b).mp h') x y hp
  · intro hp
    have hp' := Relation.ReflTransGen.lift e.symm (fun a b h' =>
      (h (e.symm a) (e.symm b)).mpr (by simpa only [Equiv.apply_symm_apply] using h'))
      (e x) (e y) hp
    simpa only [Function.onFun,Equiv.symm_apply_apply] using hp'

namespace SignedSymmetry

end SignedSymmetry

end CriticalZ3

namespace ProductCylinder

theorem reindex_probability {E : Type uE} (e : E ≃ E) (p : Set.Icc (0 : ℝ) 1)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    law (fun _ => p) ((fun ω i => ω (e i)) ⁻¹' A) = law (fun _ => p) A := by
  rw [←Measure.map_apply (Measurable.of_eval (fun i => measurable_pi_apply (e i))) hA,
    map_reindex]

end ProductCylinder

namespace CriticalZ3
open Classical

end CriticalZ3

namespace CriticalZ3
open Filter Topology Classical

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.LatticeGraph ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open Classical MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory

theorem incidence_neighbor {e : Bond} {x y : Vertex} (h : Incidence e x y) :
    NearestNeighbor x y := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨e.2,Or.inl rfl⟩
  · exact ⟨e.2,Or.inr rfl⟩

namespace LatticeGraph
variable (G : LatticeGraph)

theorem bondAdj_open {ω : BondConfig} {x y : G.Node} (h : G.BondAdj ω x y) :
    BondOpen ω x.1 y.1 := by
  obtain ⟨e,_,h,he⟩ := h
  rcases h with ⟨hx,hy⟩ | ⟨hy,hx⟩
  · exact Or.inl ⟨e.2,by simpa [hx] using hy,by simpa [hx] using he⟩
  · exact Or.inr ⟨e.2,by simpa [hy] using hx,by simpa [hy] using he⟩

theorem bondConn_global {ω : BondConfig} {x y : G.Node} (h : G.BondConn ω x y) :
    BondConnected ω x.1 y.1 := by
  exact h.lift Subtype.val (fun _ _ h => G.bondAdj_open h)

theorem siteConn_global {ω : SiteConfig} {x y : G.Node} (h : G.SiteConn ω x y) :
    SiteConnected ω x.1 y.1 := by
  refine ⟨h.1,h.2.lift Subtype.val ?_⟩
  intro a b hab
  obtain ⟨⟨e,_,he⟩,ha,hb⟩ := hab
  exact ⟨incidence_neighbor he,ha,hb⟩

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

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
end Lean433MeasurableOfEval

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e
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

omit [Countable E] in
theorem measurable_replace (J : Finset E) (ξ : E → Bool) : Measurable (replace J ξ) := by
  apply Measurable.of_eval
  intro e
  by_cases he : e ∈ J
  · simp only [replace, ite_eq_left he]; exact measurable_const
  · simp only [replace, ite_eq_right he]; exact measurable_pi_apply e

theorem measurableSet_pattern (J : Finset E) (ξ : E → Bool) : MeasurableSet (pattern J ξ) := by
  simp only [pattern, Set.ofPred_forall]
  exact MeasurableSet.iInter (fun e => MeasurableSet.iInter (fun _ =>
    measurableSet_eq_fun (measurable_pi_apply e) measurable_const))

omit [Countable E] in
theorem replace_eq_of_pattern {J : Finset E} {ξ ω : E → Bool} (h : ω ∈ pattern J ξ) :
    replace J ξ ω = ω := by
  funext e
  by_cases he : e ∈ J
  · exact (ite_eq_left he).trans (h e he).symm
  · exact ite_eq_right he

theorem pattern_inter_real (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    (ProductCylinder.law p).real (pattern J ξ ∩ A) =
      (ProductCylinder.law p).real (pattern J ξ) *
        (ProductCylinder.law (fixedParameter p J ξ)).real A := by
  simp only [Measure.real_def,pattern_inter p J ξ A hA,ENNReal.toReal_mul]

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

theorem single_probability (p : E → Set.Icc (0 : ℝ) 1) (e : E) (b : Bool) :
    (ProductCylinder.law p).real {ω | ω e = b} = bitProbability (p e) b := by
  have h := Measure.infinitePi_map_eval (fun e : E => bernoulliMeasure true false (p e)) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = b} = (fun ω => ω e) ⁻¹' {b} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun e : E => bernoulliMeasure true false (p e))).map
    (fun ω => ω e) {b}).toReal = _
  rw [h]
  change (bernoulliMeasure true false (p e)).real {b} = _
  rw [bernoulliMeasure_real_apply (p e) (measurableSet_singleton _)]
  cases b <;> simp [bitProbability,unitInterval.coe_symm_eq]

theorem finite_pattern_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (ξ : E → Bool) :
    (ProductCylinder.law p).real (pattern J ξ) = ∏ e ∈ J, bitProbability (p e) (ξ e) := by
  classical
  have hd : Pairwise (fun e f : E => Disjoint ({e} : Finset E) {f}) := by
    intro e f h; simpa using h
  have hdet (e : E) : ProductCylinder.DeterminedBy (F := Prop) {e}
      (fun ω : E → Bool => ω e = ξ e) := by
    intro ω ω' h
    dsimp only
    rw [h e (Finset.mem_singleton_self e)]
  have h := disjoint_blocks_probability p (fun e : E => {e}) hd
    (fun e => {ω | ω e = ξ e}) hdet J
  simpa only [pattern,Set.mem_ofPred_eq,single_probability] using h

theorem allValue_probability (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = ∏ e ∈ J, bitProbability (p e) b :=
  finite_pattern_probability p J (fun _ => b)

theorem allValue_probability_constant (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (q : Set.Icc (0 : ℝ) 1) (hp : ∀ e ∈ J, p e = q) (b : Bool) :
    (ProductCylinder.law p).real (allValue J b) = (bitProbability q b)^J.card := by
  rw [allValue_probability]
  calc
    _ = ∏ _e ∈ J, bitProbability q b := Finset.prod_congr rfl (fun e he => by rw [hp e he])
    _ = _ := by rw [Finset.prod_const]

variable [Countable E]

theorem ae_fixed_pattern (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), ω ∈ pattern J ξ := by
  rw [←map_replace]
  apply (ae_map_iff (measurable_replace J ξ).aemeasurable
    (measurableSet_pattern J ξ)).mpr
  exact Filter.Eventually.of_forall (fun ω e he => ite_eq_left he)

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.SeedQuality ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

end Box

namespace Model

end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Extension ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uOmega

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace MeasureTheory
open scoped _root_.MeasureTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] {μ : _root_.MeasureTheory.Measure Ω} [_root_.MeasureTheory.IsFiniteMeasure μ]
theorem finite_measureReal_mono_ae {A B : Set Ω} (h : A ≤ᵐ[μ] B) :
    μ.real A ≤ μ.real B :=
  ENNReal.toReal_le_toReal (_root_.MeasureTheory.measure_ne_top μ A) (_root_.MeasureTheory.measure_ne_top μ B) |>.mpr (_root_.MeasureTheory.measure_mono_ae h)
end MeasureTheory

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace CriticalZ3
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Scales ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

open Filter Topology
namespace CriticalScales

end CriticalScales

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Model
theorem law_eq_product (m : Model) (p : ℝ) :
    m.law p = ProductCylinder.law (fun _ => parameter p) := by cases m <;> rfl

theorem law_coe_eq_product (m : Model) (q : Set.Icc (0 : ℝ) 1) :
    m.law q = ProductCylinder.law (fun _ => q) := by
  rw [law_eq_product]
  have h : parameter (q : ℝ) = q := Subtype.ext (parameter_coe q.property)
  rw [h]

end Model

namespace ScaleData
variable {model : Model} (s : ScaleData model)

theorem q_pos : 0 < (s.q:ℝ) := (half_pos s.p_pos).trans s.q_half

end ScaleData
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

/-! Oriented planar edge boundary with exact nearest-neighbor conventions. -/
open Classical
namespace PlanarBoundary
end PlanarBoundary

namespace PlanarBoundary
open Classical

end PlanarBoundary

namespace PlanarBoundary
open Classical

/-- The finite deterministic code family has at most 4n4^n members. -/
theorem card_code (n : ℕ) : Fintype.card (Code n) = 4*n*4^n := by
  simp only [Code,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,Fintype.card_fun,Direction]
  ring

end PlanarBoundary

end OAI

-- ---- from OAI.Probability.CriticalZ3.Peierls ----
namespace OAI

universe uOmega

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem candidates_bound (Bad : Point → Set Ω) {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) (n : ℕ) :
    μ.real (⋃ c : {c : Code n // Valid c}, candidate Bad c) ≤
      4*(n : ℝ)*4^n*(2*f)^((n : ℝ)/7) := by
  calc
    _ ≤ ∑ c : {c : Code n // Valid c}, μ.real (candidate Bad c) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _c : {c : Code n // Valid c}, (2*f)^((n : ℝ)/7) :=
      Finset.sum_le_sum (fun c _ => blocked_bound μ Bad c.val c.property hf0 hf1 hbad)
    _ = (Fintype.card {c : Code n // Valid c} : ℝ)*(2*f)^((n : ℝ)/7) := by simp
    _ ≤ (Fintype.card (Code n) : ℝ)*(2*f)^((n : ℝ)/7) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast Fintype.card_subtype_le (fun c : Code n => Valid c)
      · positivity
    _ = _ := by rw [card_code]; push_cast; ring

/-- A summable real upper bound for countably many events bounds their union. -/
theorem union_bound (A : ℕ → Set Ω) (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n)
    (hg : Summable g) (hA : ∀ n, μ.real (A n) ≤ g n) :
    μ.real (⋃ n, A n) ≤ ∑' n, g n := by
  apply (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (tsum_nonneg hg0)).mp
  rw [ENNReal.ofReal_tsum_of_nonneg hg0 hg]
  apply (measure_iUnion_le A).trans
  apply ENNReal.tsum_le_tsum
  intro n
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) (hg0 n)).mpr (hA n)

theorem finite_good_bound (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d))
    (hbad : ∀ s : Finset Point,
      μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ CriticalScales.contourError^s.card) :
    μ.real {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ≤ 25/144 := by
  apply (measureReal_mono (finite_good_subset Good Bad houtside)).trans
  have h := union_bound μ (fun n => ⋃ c : {c : Code n // Valid c}, candidate Bad c)
    (fun n => 4*(n : ℝ)*4^n*(2*CriticalScales.contourError)^((n : ℝ)/7))
    (fun n => mul_nonneg (by positivity) (Real.rpow_nonneg (by linarith [CriticalScales.contourError_pos]) _)) encoded_budget_hasSum.summable
    (candidates_bound μ Bad CriticalScales.contourError_pos
      (by linarith [CriticalScales.contourError_lt_half]) hbad)
  rwa [encoded_budget_hasSum.tsum_eq] at h

end PlanarBoundary

end OAI

-- ---- from OAI.Probability.CriticalZ3.Coarse ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace Coarse
theorem B_subset_Q (r : ℕ) (v : Point) : ∀ x, (B r v).Contains x → (Q r v).Contains x := by
  intro x hx
  apply Box.contains_cube_iff.mpr
  exact cube_mono (center r v) (by omega) (Box.contains_cube_iff.mp hx)

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
namespace LatticeGraph

end LatticeGraph

namespace Coarse
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.AdaptiveReveals ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe uF

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace AdaptiveReveals
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
open InfiniteConditioning
variable {E V S : Type} [Countable E] [DecidableEq V]

namespace Scheme
variable (P : Scheme E V S)

omit [Countable E] in
theorem hit_empty (n : ℕ) (s : S) : P.hit n s ∅ = Set.univ := by
  induction n generalizing s with
  | zero => simp [hit]
  | succ n ih =>
    simp only [hit]
    cases P.vertex s <;> simp [ih]

omit [Countable E] in
theorem hit_subset_succ (n : ℕ) (s : S) (U : Finset V) :
    P.hit n s U ⊆ P.hit (n+1) s U := by
  induction n generalizing s U with
  | zero =>
    by_cases hU : U = ∅
    · subst U; rw [P.hit_empty,P.hit_empty]
    · simp only [hit,ite_eq_right hU]; exact Set.empty_subset _
  | succ n ih =>
    cases hv : P.vertex s with
    | none => simp only [hit,hv]; exact Set.Subset.rfl
    | some v =>
      simp only [hit,hv]
      intro ω hω
      exact ⟨hω.1,ih _ _ hω.2⟩

omit [Countable E] in
theorem hit_monotone (s : S) (U : Finset V) : Monotone (fun n => P.hit n s U) :=
  monotone_nat_of_le_succ (fun n => P.hit_subset_succ n s U)

/-- Uniform control survives an unbounded possible processing time. -/
theorem everHit_bound (I : S → Prop) (f : ℝ) (hf : 0 ≤ f)
    (hbad : ∀ s, I s → P.badMass s ≤ f)
    (hchild : ∀ s, I s → ∀ a, 0 < P.weight s a → I (P.child s a))
    (s : S) (hs : I s) (U : Finset V) :
    (ProductCylinder.law (P.parameter s)).real (⋃ n, P.hit n s U) ≤ f^U.card := by
  have hlim := (ENNReal.tendsto_toReal (measure_ne_top (ProductCylinder.law (P.parameter s))
    (⋃ n, P.hit n s U))).comp
    (tendsto_measure_iUnion_atTop (μ := ProductCylinder.law (P.parameter s)) (P.hit_monotone s U))
  apply le_of_tendsto hlim
  exact Filter.Eventually.of_forall (fun n => P.hit_bound I f hf hbad hchild n s hs U)

end Scheme
end AdaptiveReveals

namespace InfiniteConditioning
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

namespace History
omit [Countable E] in
theorem observe_outcome (h : History E) {J R : Finset E} {F : Sort uF}
    (f : (E → Bool) → F) (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hJ : J ⊆ h.known ∪ R) (hR : Disjoint R h.known) (ω : E → Bool) :
    f (h.observe R ω).values = f (h.freeze ω) := by
  apply hf
  intro e he
  rcases Finset.mem_union.mp (hJ he) with hk|hr
  · have hn : e ∉ R := fun hh => Finset.disjoint_left.mp hR hh hk
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hk]
  · have hn : e ∉ h.known := fun hh => Finset.disjoint_left.mp hR hr hh
    simp only [observe,freeze,replace,ite_eq_right hn,ite_eq_left hr]

end History
end InfiniteConditioning

end OAI

-- ---- from OAI.Probability.CriticalZ3.Exploration ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Packet
variable {r : ℕ}
theorem event_determined (t : Packet r) (m : Model) :
    ProductCylinder.DeterminedBy (F := Prop) (t.graph.bits m) (fun ω => ω ∈ t.event m) :=
  t.graph.meets_determined m _ _

end Packet

namespace Exploration
variable {m : Model} {r : ℕ}
theorem reveal_disjoint (s : Exploration m r) : Disjoint s.reveal s.history.known := by
  cases h : s.queue with
  | nil => simp only [reveal,h]; exact Finset.disjoint_empty_left _
  | cons t ts => simp only [reveal,h]; exact Finset.sdiff_disjoint

end Exploration
end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

namespace Exploration
variable {m : Model} {r : ℕ}

theorem queue_visited (s : Exploration m r) {t : Packet r} (ht : t ∈ s.queue) :
    t.vertex ∈ s.visited :=
  Finset.mem_union_right _ (List.mem_toFinset.mpr (List.mem_map.mpr ⟨t,ht,rfl⟩))

theorem processed_visited (s : Exploration m r) : s.processed ⊆ s.visited := Finset.subset_union_left

theorem advance_empty (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (ω : m.Config) (h : s.queue = []) : s.advance q δ ω = s := by
  cases s with
  | mk history processed queue good bad =>
    cases history
    simp_all only [advance,after,reveal,History.observe,Finset.union_empty,Exploration.mk.injEq,History.mk.injEq,true_and,and_true]
    funext e
    exact ite_eq_right (Finset.notMem_empty e)

theorem current_support {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    t.graph.bits m ⊆ s.history.known ∪ s.reveal := by
  intro e he
  have hh := hs.support t (by simp [hq]) he
  rcases Finset.mem_union.mp hh with hh|hh
  · exact Finset.mem_union_left _ hh
  · by_cases hk : e ∈ s.history.known
    · exact Finset.mem_union_left _ hk
    · exact Finset.mem_union_right _ (by simpa only [reveal,hq,Finset.mem_sdiff] using ⟨hh,hk⟩)

end Exploration
end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationInvariant ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem accept_current_iff {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) (ω : m.Config) :
    (s.after ω).values ∈ t.event m ↔ ω ∈ s.frozenEvent t := by
  exact Eq.to_iff (s.history.observe_outcome _ (t.event_determined m)
    (by simpa only [Finset.subset_iff,Finset.mem_union] using current_support hs hq) s.reveal_disjoint ω)

theorem everHit_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      (⋃ n, (scheme (r := sc.r) sc.q sc.δ).hit n s U) ≤ CriticalScales.contourError^U.card := by
  apply AdaptiveReveals.Scheme.everHit_bound _ (Valid sc.q sc.δ) _ CriticalScales.contourError_pos.le
    (fun _ hs => badMass_bound sc hs) _ s hs U
  intro s hs a _
  exact valid_advance hs _
end Coarse.Exploration
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem advance_processed (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).processed = insert t.vertex s.processed := by simp only [advance,hq]

theorem advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    (s.advance q δ ω).queue = ts ++ if s.Accept q δ t ω then s.candidates t else [] := by
  simp only [advance,hq]

theorem mem_advance_queue (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t u : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts) :
    u ∈ (s.advance q δ ω).queue ↔ u ∈ ts ∨ (s.Accept q δ t ω ∧ u ∈ s.candidates t) := by
  rw [s.advance_queue q δ ω hq,List.mem_append]
  by_cases h : s.Accept q δ t ω <;> simp [h]

theorem good_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.good ⊆ (s.advance q δ ω).good := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.subset_insert _ _
    · exact Finset.Subset.refl _

theorem bad_advance_mono (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config) :
    s.bad ⊆ (s.advance q δ ω).bad := by
  cases hq : s.queue
  · rw [advance_empty s q δ ω hq]
  · simp only [advance,hq]
    split_ifs
    · exact Finset.Subset.refl _
    · exact Finset.subset_insert _ _

theorem new_visited (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {v : Point} (hv : v ∈ (s.advance q δ ω).visited) :
    v ∈ s.visited ∨ (s.Accept q δ t ω ∧ ∃ d : Direction, v = t.vertex+outward d) := by
  rcases Finset.mem_union.mp hv with hv|hv
  · rw [s.advance_processed q δ ω hq,Finset.mem_insert] at hv
    rcases hv with rfl|hv
    · exact Or.inl (s.queue_visited (by simp [hq]))
    · exact Or.inl (s.processed_visited hv)
  · obtain ⟨u,hu,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    rcases (s.mem_advance_queue q δ ω hq).mp hu with hu|⟨ha,hu⟩
    · exact Or.inl (s.queue_visited (by simp [hq,hu]))
    · obtain ⟨⟨d,rfl⟩,_⟩ := (mem_candidates s t u).mp hu
      exact Or.inr ⟨ha,d,rfl⟩

theorem accepted_neighbors (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (ω : m.Config)
    {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    (ha : s.Accept q δ t ω) (d : Direction) :
    t.vertex+outward d ∈ (s.advance q δ ω).visited := by
  by_cases hv : t.vertex+outward d ∈ s.visited
  · exact s.visited_advance_mono q δ ω hv
  · apply (s.advance q δ ω).queue_visited (t := t.child (t.vertex+outward d))
    apply (s.mem_advance_queue q δ ω hq).mpr
    exact Or.inr ⟨ha,(mem_candidates _ _ _).mpr ⟨⟨d,rfl⟩,hv⟩⟩

theorem closed_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Closed) (ω : m.Config) : (s.advance q δ ω).Closed := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv d
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · exact s.accepted_neighbors q δ ω hq ha d
      · exact s.visited_advance_mono q δ ω (hc _ hv d)
    · exact s.visited_advance_mono q δ ω (hc _ hv d)

theorem covered_advance (s : Exploration m r) (q : Set.Icc (0:ℝ) 1) (δ : ℝ)
    (hc : s.Covered) (ω : m.Config) : (s.advance q δ ω).Covered := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    rcases s.new_visited q δ ω hq hv with hv|⟨ha,d,rfl⟩
    · rcases hc _ hv with hv|⟨u,hu,d,he⟩
      · exact Or.inl (s.good_advance_mono q δ ω hv)
      · exact Or.inr ⟨u,s.good_advance_mono q δ ω hu,d,he⟩
    · right
      refine ⟨t.vertex,?_,d,rfl⟩
      simp only [advance,hq,ite_eq_left ha]
      exact Finset.mem_insert_self _ _

theorem run_succ_right (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (n : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (n+1) s ω = (run q δ n s ω).advance q δ ω := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => rw [run_succ,ih,run_succ]

theorem run_valid {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Valid q δ := by
  induction n generalizing s with
  | zero => exact hs
  | succ n ih => exact ih (valid_advance hs ω)

theorem run_colored {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Colored := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (valid_advance hs ω) (colored_advance hs hc ω)

theorem run_closed (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Closed) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Closed := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (closed_advance s q δ hc ω)

theorem run_covered (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r}
    (hc : s.Covered) (n : ℕ) (ω : m.Config) : (run q δ n s ω).Covered := by
  induction n generalizing s with
  | zero => exact hc
  | succ n ih => exact ih (covered_advance s q δ hc ω)

theorem run_good_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).good) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact good_advance_mono _ _ _ _

theorem run_bad_mono (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    Monotone (fun n => (run q δ n s ω).bad) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [run_succ_right]
  exact bad_advance_mono _ _ _ _

theorem run_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) {s : Exploration m r} (hs : s.queue = [])
    (n : ℕ) (ω : m.Config) : run q δ n s ω = s := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ,advance_empty s q δ ω hs,ih]

theorem initial_good_subset (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config) :
    (s.good : Set Point) ⊆ Good q δ s ω := fun _ hv => ⟨0,hv⟩

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationProbability ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem run_add (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (a b : ℕ) (s : Exploration m r) (ω : m.Config) :
    run q δ (a+b) s ω = run q δ b (run q δ a s ω) ω := by
  induction a generalizing s with
  | zero => simp only [Nat.zero_add,run_zero]
  | succ a ih => rw [Nat.succ_add,run_succ,ih,run_succ]

theorem run_stable (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N k : ℕ} (hN : (run q δ N s ω).queue = []) (hk : N ≤ k) :
    run q δ k s ω = run q δ N s ω := by
  rw [←Nat.add_sub_of_le hk,run_add]
  exact run_empty q δ hN _ ω

theorem good_eq_of_empty (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r) (ω : m.Config)
    {N : ℕ} (hN : (run q δ N s ω).queue = []) :
    Good q δ s ω = ((run q δ N s ω).good : Set Point) := by
  ext v
  constructor
  · rintro ⟨k,hk⟩
    have hh := run_good_mono q δ s ω (show k ≤ N+k by omega) hk
    dsimp only at hh
    rwa [run_stable q δ s ω hN (show N ≤ N+k by omega)] at hh
  · intro h; exact ⟨N,h⟩

theorem exists_empty_of_finite_good {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Covered) (ω : m.Config) (hfin : (Good q δ s ω).Finite) :
    ∃ n, (run q δ n s ω).queue = [] := by
  let X := Good q δ s ω
  let F := X ∪ ⋃ d : Direction, (fun v : Point => v+outward d) '' X
  have hF : F.Finite := hfin.union (Set.finite_iUnion (fun d => hfin.image _))
  have hbound (n : ℕ) : (run q δ n s ω).processed ⊆ hF.toFinset := by
    intro v hv
    apply hF.mem_toFinset.mpr
    have hh := run_covered q δ hc n ω v ((run q δ n s ω).processed_visited hv)
    rcases hh with hv|⟨u,hu,d,rfl⟩
    · exact Or.inl ⟨n,hv⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨d,u,⟨n,hu⟩,rfl⟩)
  by_contra! hn
  have hcard (n : ℕ) : s.processed.card+n ≤ (run q δ n s ω).processed.card := by
    induction n with
    | zero => simp only [run_zero,Nat.add_zero,le_refl]
    | succ n ih =>
      have hvalid := run_valid hs n ω
      cases hq : (run q δ n s ω).queue with
      | nil => exact False.elim (hn n hq)
      | cons t ts =>
        rw [run_succ_right,advance_processed _ q δ ω hq,
          Finset.card_insert_of_notMem (hvalid.unprocessed t (by simp [hq]))]
        omega
  have hh := (hcard (hF.toFinset.card+1)).trans (Finset.card_le_card (hbound _))
  omega

theorem outside_bad {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hclosed : s.Closed) (hcovered : s.Covered)
    (ω : m.Config) (hfin : (Good q δ s ω).Finite)
    {x : Point} (hx : x ∈ Good q δ s ω) (d : Direction)
    (hy : x+outward d ∉ Good q δ s ω) : ω ∈ Bad q δ s (x+outward d) := by
  obtain ⟨N,hN⟩ := exists_empty_of_finite_good hs hcovered ω hfin
  have he := good_eq_of_empty q δ s ω hN
  have hxN : x ∈ (run q δ N s ω).good := by
    change x ∈ ((run q δ N s ω).good : Set Point)
    rwa [←he]
  have hv := run_closed q δ hclosed N ω x hxN d
  have hp : x+outward d ∈ (run q δ N s ω).processed := by
    simpa only [visited,hN,List.map_nil,List.toFinset_nil,Finset.union_empty] using hv
  rw [(run_colored hs hc N ω).partition,Finset.mem_union] at hp
  rcases hp with hg|hb
  · exact False.elim (hy ⟨N,hg⟩)
  · exact ⟨N,hb⟩

theorem exists_bad_time (q : Set.Icc (0:ℝ) 1) (δ : ℝ) (s : Exploration m r)
    (ω : m.Config) (U : Finset Point) (hU : ∀ v ∈ U, ω ∈ Bad q δ s v) :
    ∃ n, U ⊆ (run q δ n s ω).bad := by
  induction U using Finset.induction_on with
  | empty => exact ⟨0,Finset.empty_subset _⟩
  | @insert a U ha ih =>
    obtain ⟨k,hk⟩ := hU a (Finset.mem_insert_self _ _)
    obtain ⟨n,hn⟩ := ih (fun v hv => hU v (Finset.mem_insert_of_mem hv))
    refine ⟨max k n,?_⟩
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact run_bad_mono q δ s ω (le_max_left _ _) hk
    · exact run_bad_mono q δ s ω (le_max_right _ _) (hn hv)

theorem bad_set_subset {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    {ω | ∀ v ∈ U, ω ∈ Bad q δ s v} ⊆ ⋃ n, (scheme (r := r) q δ).hit n s U := by
  intro ω hω
  obtain ⟨n,hn⟩ := exists_bad_time q δ s ω U hω
  apply Set.mem_iUnion.mpr
  refine ⟨n,hit_of_bad_subset hs hc n ω U ?_ hn⟩
  apply Finset.disjoint_left.mpr
  intro v hv hp
  have hg : v ∈ s.good := by simpa only [hc.partition,hb,Finset.union_empty] using hp
  have hgn := run_good_mono q δ s ω (Nat.zero_le n) hg
  exact Finset.disjoint_left.mp (run_colored hs hc n ω).disjoint hgn (hn hv)

theorem bad_set_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅) (U : Finset Point) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | ∀ v ∈ U, ω ∈ Bad sc.q sc.δ s v} ≤ CriticalScales.contourError^U.card :=
  (measureReal_mono (bad_set_subset hs hc hb U)).trans (everHit_bound sc hs U)

theorem finite_good_bound (sc : ScaleData m) {s : Exploration m sc.r}
    (hs : s.Valid sc.q sc.δ) (hc : s.Colored) (hb : s.bad = ∅)
    (hclosed : s.Closed) (hcovered : s.Covered) :
    (ProductCylinder.law (s.history.parameter sc.q)).real
      {ω | (Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Good sc.q sc.δ s ω} ≤ 25/144 := by
  apply PlanarBoundary.finite_good_bound _ (Good sc.q sc.δ s) (Bad sc.q sc.δ s)
    (fun ω hfin x hx d hy => outside_bad hs hc hclosed hcovered ω hfin hx d hy)
    (fun U => bad_set_bound sc hs hc hb U)

end Coarse.Exploration
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationConnectivity ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace LatticeGraph

end LatticeGraph

namespace Coarse

theorem initial_colored (m : Model) (r : ℕ) : (initial m r).Colored := by
  constructor
  · simp only [initial,Finset.union_empty]
  · exact Finset.disjoint_empty_right _

theorem initial_closed (m : Model) (r : ℕ) : (initial m r).Closed := by
  intro v hv d
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  rw [zero_add]
  apply Exploration.queue_visited (initial m r) (t := (rootPacket r).child (outward d))
  exact (mem_initial_queue _ _ _).mpr ⟨d,rfl⟩

theorem initial_covered (m : Model) (r : ℕ) : (initial m r).Covered := by
  intro v hv
  rcases Finset.mem_union.mp hv with hv|hv
  · exact Or.inl hv
  · obtain ⟨t,ht,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    obtain ⟨d,rfl⟩ := (mem_initial_queue _ _ _).mp ht
    exact Or.inr ⟨0,Finset.mem_singleton_self _,d,(zero_add _).symm⟩

end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.ExplorationSurvival ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace InfiniteConditioning.History
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

omit [Countable E] in
theorem observe_pattern (h : History E) (R : Finset E) {ω : E → Bool}
    (hω : ω ∈ pattern h.known h.values) :
    ω ∈ pattern (h.observe R ω).known (h.observe R ω).values := by
  intro e he
  change ω e = replace R ω h.values e
  by_cases heR : e ∈ R
  · simp only [replace,ite_eq_left heR]
  · have heK : e ∈ h.known := (Finset.mem_union.mp he).resolve_right heR
    simpa only [replace,ite_eq_right heR] using hω e heK
end InfiniteConditioning.History

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Model

theorem infiniteAt_iff (m : Model) (ω : m.Config) (x : Vertex) :
    ω ∈ m.InfiniteAt x ↔ (m.Cluster ω x).Infinite := by cases m <;> rfl

theorem measurableSet_infiniteAt (m : Model) (x : Vertex) : MeasurableSet (m.InfiniteAt x) := by
  cases m
  · exact measurableSet_bondInfiniteAt x
  · exact measurableSet_siteInfiniteAt x
end Model

namespace LatticeGraph

theorem conn_global (G : LatticeGraph) (m : Model) {ω : m.Config} {x y : G.Node}
    (h : G.Conn m ω x y) : m.Connected ω x.1 y.1 := by
  cases m
  · exact G.bondConn_global h
  · exact G.siteConn_global h
end LatticeGraph

namespace Coarse.Exploration
variable {m : Model} {r : ℕ}

theorem accepted_event {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {t : Packet r} {ts : List (Packet r)} (hq : s.queue = t::ts)
    {ω : m.Config} (hω : ω ∈ pattern s.history.known s.history.values)
    (ha : s.Accept q δ t ω) : ω ∈ t.event m := by
  have hh := (accept_current_iff hs hq ω).mp ha.1
  change s.history.freeze ω ∈ t.event m at hh
  simpa only [History.freeze,replace_eq_of_pattern hω] using hh

theorem sound_advance {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) :
    (s.advance q δ ω).Sound ω := by
  cases hq : s.queue with
  | nil => rwa [advance_empty s q δ ω hq]
  | cons t ts =>
    intro v hv
    simp only [advance,hq] at hv
    split_ifs at hv with ha
    · rcases Finset.mem_insert.mp hv with rfl|hv
      · obtain ⟨y,hy,hpath⟩ := accepted_event hs hq hω ha
        exact ⟨y.1,hy,t.graph.conn_global m hpath⟩
      · exact hS v hv
    · exact hS v hv

theorem run_sound {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω) (n : ℕ) :
    (run q δ n s ω).Sound ω := by
  induction n generalizing s with
  | zero => exact hS
  | succ n ih =>
    exact ih (valid_advance hs ω) (s.history.observe_pattern s.reveal hω)
      (sound_advance hs hω hS)

theorem good_finite_of_cluster_finite {q : Set.Icc (0:ℝ) 1} {δ : ℝ} {s : Exploration m r}
    (hs : s.Valid q δ) {ω : m.Config}
    (hω : ω ∈ pattern s.history.known s.history.values) (hS : s.Sound ω)
    (hfin : (m.Cluster ω 0).Finite) : (Good q δ s ω).Finite := by
  have hf (y : Vertex) : ({v | (B r v).Contains y} : Set Point).Finite := by
    apply Set.Subsingleton.finite
    intro v hv w hw
    exact cube_unique r (B_subset_Q r v y hv) (B_subset_Q r w y hw)
  apply (hfin.biUnion (fun y _ => hf y)).subset
  intro v hv
  obtain ⟨n,hn⟩ := hv
  obtain ⟨y,hy,hc⟩ := run_sound hs hω hS n v hn
  exact Set.mem_iUnion.mpr ⟨y,Set.mem_iUnion.mpr ⟨hc,hy⟩⟩
end Coarse.Exploration

namespace Coarse

theorem initial_sound (m : Model) (r : ℕ) {ω : m.Config}
    (hω : ω ∈ allValue (rootBits m r) true) : (initial m r).Sound ω := by
  intro v hv
  have hv0 : v = 0 := Finset.mem_singleton.mp hv
  subst v
  refine ⟨0,?_,?_⟩
  · rw [B,center_zero]
    exact Box.center_mem_cube _ _
  · cases m
    · exact Relation.ReflTransGen.refl
    · refine ⟨hω 0 ?_,Relation.ReflTransGen.refl⟩
      apply Finset.mem_union_left
      exact (Box.mem_vertices _ _).mpr (zero_in_Q r)

end Coarse
end CriticalZ3

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Coarse

theorem scales_percolate {m : Model} (sc : ScaleData m) :
    0 < m.law (sc.q : ℝ) (m.InfiniteAt 0) := by
  let s := initial m sc.r
  let μ := ProductCylinder.law (s.history.parameter sc.q)
  let ν := ProductCylinder.law (fun _ : m.Bit => sc.q)
  have hs : s.Valid sc.q sc.δ := initial_valid sc
  have hb := Exploration.finite_good_bound sc hs (initial_colored m sc.r) rfl
    (initial_closed m sc.r) (initial_covered m sc.r)
  have hle : μ.real (m.InfiniteAt 0)ᶜ ≤ μ.real
      {ω | (Exploration.Good sc.q sc.δ s ω).Finite ∧ (0,0) ∈ Exploration.Good sc.q sc.δ s ω} := by
    apply finite_measureReal_mono_ae
    filter_upwards [ae_fixed_pattern (fun _ : m.Bit => sc.q) (rootBits m sc.r) (fun _ => true)] with ω hω
    intro hn
    have hfin : (m.Cluster ω 0).Finite := by
      by_contra hnf
      exact hn ((m.infiniteAt_iff ω 0).mpr hnf)
    exact ⟨Exploration.good_finite_of_cluster_finite hs hω (initial_sound m sc.r hω) hfin,
      Exploration.initial_good_subset sc.q sc.δ s ω (Finset.mem_singleton_self _)⟩
  have hpos : 0 < μ.real (m.InfiniteAt 0) := by
    rw [measureReal_compl (m.measurableSet_infiniteAt 0),probReal_univ] at hle
    dsimp [μ] at hle
    linarith
  let H := allValue (rootBits m sc.r) true
  have hH : 0 < ν.real H := by
    rw [show ν.real H = (sc.q : ℝ)^(rootBits m sc.r).card by
      exact allValue_probability_constant (fun _ : m.Bit => sc.q) (rootBits m sc.r)
        sc.q (fun _ _ => rfl) true]
    exact pow_pos sc.q_pos _
  have he : ν.real (H ∩ m.InfiniteAt 0) = ν.real H * μ.real (m.InfiniteAt 0) :=
    pattern_inter_real _ _ _ _ (m.measurableSet_infiniteAt 0)
  have hinf : 0 < ν.real (m.InfiniteAt 0) :=
    (he ▸ mul_pos hH hpos).trans_le (measureReal_mono Set.inter_subset_right)
  rw [m.law_coe_eq_product]
  exact ENNReal.toReal_pos_iff.mp hinf |>.1

/-- Positive percolation is open to the left throughout the open unit interval. -/
theorem lower_percolating_parameter (m : Model) {p : ℝ} (hp : 0 < p) (hp1 : p < 1)
    (hInf : 0 < m.law p (m.InfiniteAt 0)) :
    ∃ q ∈ Set.Icc (0:ℝ) 1, q < p ∧ 0 < m.law q (m.InfiniteAt 0) := by
  obtain ⟨sc,hsc⟩ := exists_scales m hp hp1 hInf
  exact ⟨sc.q,sc.q.property,hsc ▸ sc.q_lt,scales_percolate sc⟩

end Coarse
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Subunit ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace BlockPercolation
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
variable {E : Type}

end BlockPercolation

namespace CriticalZ3
open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary

theorem planarEmbed_injective : Function.Injective planarEmbed := by
  intro u v h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  exact Prod.ext (by simpa [planarEmbed] using h0) (by simpa [planarEmbed] using h1)

theorem planarSiteBlock_disjoint : Pairwise (fun u v => Disjoint (planarSiteBlock u) (planarSiteBlock v)) := by
  intro u v huv
  simp only [planarSiteBlock,Finset.disjoint_singleton]
  exact fun h => huv (planarEmbed_injective h)

theorem planarBondBlock_disjoint : Pairwise (fun u v => Disjoint (planarBondBlock u) (planarBondBlock v)) := by
  intro u v huv
  rw [Finset.disjoint_left]
  intro e he he'
  have hleft (w : Point) (he : e ∈ planarBondBlock w) : e.1 = planarEmbed w := by
    simp only [planarBondBlock,Finset.mem_insert,Finset.mem_singleton] at he
    rcases he with rfl | rfl <;> rfl
  exact huv (planarEmbed_injective ((hleft u he).symm.trans (hleft v he')))

theorem planarSiteBlock_card (v : Point) : (planarSiteBlock v).card ≤ 2 := by simp [planarSiteBlock]
theorem planarBondBlock_card (v : Point) : (planarBondBlock v).card ≤ 2 := by
  simp [planarBondBlock]

theorem planar_neighbor (v : Point) (d : Direction) :
    NearestNeighbor (planarEmbed v) (planarEmbed (v+outward d)) := by
  fin_cases d
  · refine ⟨1,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨1,Or.inl ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine ⟨0,Or.inr ?_⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_site_open {ω : SiteConfig} {u v : Point}
    (h : BlockPercolation.Adj planarSiteBlock ω u v) :
    SiteOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  exact ⟨planar_neighbor u d,hu _ (Finset.mem_singleton_self _),hv _ (Finset.mem_singleton_self _)⟩

theorem planar_bond_open {ω : BondConfig} {u v : Point}
    (h : BlockPercolation.Adj planarBondBlock ω u v) :
    BondOpen ω (planarEmbed u) (planarEmbed v) := by
  obtain ⟨⟨d,rfl⟩,hu,hv⟩ := h
  have hu0 : ω (planarEmbed u,0) = true := hu _ (Finset.mem_insert_self _ _)
  have hu1 : ω (planarEmbed u,1) = true := hu _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  have hv0 : ω (planarEmbed (u+outward d),0) = true := hv _ (Finset.mem_insert_self _ _)
  have hv1 : ω (planarEmbed (u+outward d),1) = true := hv _ (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  fin_cases d
  · refine Or.inr ⟨1,?_,hv1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨0,?_,hu0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inl ⟨1,?_,hu1⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]
  · refine Or.inr ⟨0,?_,hv0⟩
    funext i; fin_cases i <;> simp [planarEmbed,outward,step]

theorem planar_bond_infinite {ω : BondConfig}
    (h : (BlockPercolation.cluster planarBondBlock ω).Infinite) : ω ∈ bondInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_bond_open h)
  change Relation.ReflTransGen (BondOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  rw [planarEmbed_zero] at hc
  exact hc

theorem planar_site_infinite {ω : SiteConfig}
    (h : (BlockPercolation.cluster planarSiteBlock ω).Infinite) : ω ∈ siteInfiniteAt 0 := by
  apply (h.image planarEmbed_injective.injOn).mono
  rintro _ ⟨v,hv,rfl⟩
  have hc := hv.2.lift planarEmbed (fun _ _ h => planar_site_open h)
  change Relation.ReflTransGen (SiteOpen ω) (planarEmbed (0,0)) (planarEmbed v) at hc
  refine ⟨?_,by simpa only [planarEmbed_zero] using hc⟩
  have ho := hv.1 (planarEmbed (0,0)) (Finset.mem_singleton_self _)
  simpa only [planarEmbed_zero] using ho

theorem subunitParameter_lt_one : (subunitParameter : ℝ) < 1 := by
  dsimp [subunitParameter]
  linarith [CriticalScales.contourError_pos]

theorem subunit_bond_positive : 0 < bondLaw subunitParameter (bondInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarBondBlock
    planarBondBlock_disjoint planarBondBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (bondInfiniteAt 0) (fun _ => planar_bond_infinite)
  simpa only [bondLaw,he,ProductCylinder.law] using h

theorem subunit_site_positive : 0 < siteLaw subunitParameter (siteInfiniteAt 0) := by
  have he : parameter subunitParameter = subunitParameter := Subtype.ext (parameter_coe subunitParameter.2)
  have h := BlockPercolation.survival subunitParameter planarSiteBlock
    planarSiteBlock_disjoint planarSiteBlock_card (by
      change 2*(1-(1-CriticalScales.contourError/4)) ≤ CriticalScales.contourError
      linarith [CriticalScales.contourError_pos]) (siteInfiniteAt 0) (fun _ => planar_site_infinite)
  simpa only [siteLaw,he,ProductCylinder.law] using h

theorem bondCritical_lt_one : bondCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < bondLaw p (bondInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_bond_positive⟩) subunitParameter_lt_one

theorem siteCritical_lt_one : siteCritical < 1 := by
  apply lt_of_le_of_lt (csInf_le (show BddBelow {p : ℝ | p ∈ Set.Icc (0 : ℝ) 1 ∧
      0 < siteLaw p (siteInfiniteAt 0)} from ⟨0,fun _ h => h.1.1⟩)
    ⟨subunitParameter.2,subunit_site_positive⟩) subunitParameter_lt_one

end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.Main ----
namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical

/-- Vanishing origin order parameter at the exact bond critical infimum. -/
theorem bond_critical_origin : bondLaw bondCritical (bondInfiniteAt 0) = 0 := by
  by_cases hc : bondCritical = 0
  · simp only [hc,bondLaw_zero_infinite]
  · have hp : 0 < bondCritical := lt_of_le_of_ne bondCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < bondLaw bondCritical (bondInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .bond hp bondCritical_lt_one hpos
    exact (ne_of_gt hqpos) (bond_subcritical_origin hq hqc)

/-- Vanishing origin order parameter at the separate site critical infimum. -/
theorem site_critical_origin : siteLaw siteCritical (siteInfiniteAt 0) = 0 := by
  by_cases hc : siteCritical = 0
  · simp only [hc,siteLaw_zero_infinite]
  · have hp : 0 < siteCritical := lt_of_le_of_ne siteCritical_mem.1 (Ne.symm hc)
    by_contra hn
    have hpos : 0 < siteLaw siteCritical (siteInfiniteAt 0) := bot_lt_iff_ne_bot.mpr hn
    obtain ⟨q,hq,hqc,hqpos⟩ := Coarse.lower_percolating_parameter .site hp siteCritical_lt_one hpos
    exact (ne_of_gt hqpos) (site_subcritical_origin hq hqc)

namespace SignedSymmetry

theorem bondConnected_map (S : SignedSymmetry) (ω : BondConfig) (x y : Vertex) :
    BondConnected (fun e => ω (S.bond e)) x y ↔ BondConnected ω (S.vertex x) (S.vertex y) :=
  rtg_equiv_iff S.vertex (S.bondOpen_map ω) x y

theorem siteConnected_map (S : SignedSymmetry) (ω : SiteConfig) (x y : Vertex) :
    SiteConnected (fun e => ω (S.vertex e)) x y ↔ SiteConnected ω (S.vertex x) (S.vertex y) :=
  and_congr_right (fun _ => rtg_equiv_iff S.vertex (S.siteOpen_map ω) x y)

theorem bondInfiniteAt_map (S : SignedSymmetry) (ω : BondConfig) (x : Vertex) :
    (fun e => ω (S.bond e)) ∈ bondInfiniteAt x ↔ ω ∈ bondInfiniteAt (S.vertex x) := by
  have he : bondCluster (fun e => ω (S.bond e)) x = S.vertex ⁻¹' bondCluster ω (S.vertex x) := by
    ext y
    exact S.bondConnected_map ω x y
  change (bondCluster (fun e => ω (S.bond e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)

theorem siteInfiniteAt_map (S : SignedSymmetry) (ω : SiteConfig) (x : Vertex) :
    (fun e => ω (S.vertex e)) ∈ siteInfiniteAt x ↔ ω ∈ siteInfiniteAt (S.vertex x) := by
  have he : siteCluster (fun e => ω (S.vertex e)) x = S.vertex ⁻¹' siteCluster ω (S.vertex x) := by
    ext y
    exact S.siteConnected_map ω x y
  change (siteCluster (fun e => ω (S.vertex e)) x).Infinite ↔ _
  rw [he]
  constructor
  · intro hi hf
    exact hi (Set.Finite.preimage S.vertex.injective.injOn hf)
  · intro hi
    exact hi.preimage (fun y _ => S.vertex.surjective y)
end SignedSymmetry

theorem bondInfiniteAt_probability (p : ℝ) (x : Vertex) :
    bondLaw p (bondInfiniteAt x) = bondLaw p (bondInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.bond e)) ⁻¹' bondInfiniteAt 0 = bondInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.bondInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.bond (parameter p) (bondInfiniteAt 0)
    (measurableSet_bondInfiniteAt 0)
  rw [he] at h
  exact h

theorem siteInfiniteAt_probability (p : ℝ) (x : Vertex) :
    siteLaw p (siteInfiniteAt x) = siteLaw p (siteInfiniteAt 0) := by
  let S := faceSymmetry x canonicalFace
  have he : (fun ω e => ω (S.vertex e)) ⁻¹' siteInfiniteAt 0 = siteInfiniteAt x := by
    ext ω
    simp only [Set.mem_preimage,S.siteInfiniteAt_map,faceSymmetry_zero,S]
  have h := ProductCylinder.reindex_probability S.vertex (parameter p) (siteInfiniteAt 0)
    (measurableSet_siteInfiniteAt 0)
  rw [he] at h
  exact h

/-- Nearest-neighbor bond percolation on Z³ has almost surely no infinite cluster at criticality. -/
theorem bond_critical_no_infinite :
    ∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (bondInfiniteAt_probability bondCritical x).trans bond_critical_origin

/-- Nearest-neighbor site percolation on Z³ has almost surely no infinite cluster at its own criticality. -/
theorem site_critical_no_infinite :
    ∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite := by
  rw [ae_all_iff]
  intro x
  rw [ae_iff]
  exact (siteInfiniteAt_probability siteCritical x).trans site_critical_origin

theorem critical_no_infinite :
    (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite) :=
  ⟨bond_critical_no_infinite, site_critical_no_infinite⟩

end CriticalZ3

end OAI

-- ---- mission target ----
open OAI OAI.CriticalZ3
open MeasureTheory ProbabilityTheory
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open _root_.MeasureTheory ProbabilityTheory Classical

namespace OAI
namespace CriticalZ3
theorem _root_.solution :
    (∀ᵐ ω ∂bondLaw bondCritical, ∀ x : Vertex, (bondCluster ω x).Finite) ∧
    (∀ᵐ ω ∂siteLaw siteCritical, ∀ x : Vertex, (siteCluster ω x).Finite) := by
  first
    | exact OAI.CriticalZ3.critical_no_infinite
    | (apply OAI.CriticalZ3.critical_no_infinite <;> assumption)
    | (intros; apply OAI.CriticalZ3.critical_no_infinite <;> assumption)
end CriticalZ3
end OAI
