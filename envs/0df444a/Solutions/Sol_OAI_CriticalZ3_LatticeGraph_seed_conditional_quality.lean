-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.seed_conditional_quality
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:52:46.438258+00:00
-- url     : https://prove2.me/submissions/143218af-3477-48d9-b3ef-b148ce5d898a

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/SeedQuality.lean:L113-L135
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.seed_conditional_quality. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_seedReaches_conn
import Theorems.Thm_OAI_FiniteAssociation_increasing
import Theorems.Thm_OAI_InfiniteConditioning_conditional_failure_mass

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
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

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

theorem prob_eq_real [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    (P : (E → Bool) → Prop) : prob p P = (law p).real {ω | P ω} := by
  simpa [prob,mean,Set.indicator] using
    (integral_indicator_one (μ := law p) (s := {ω | P ω}) (Set.toFinite _).measurableSet)

end FiniteAssociation

namespace ProductCylinder
variable {E : Type uE}

theorem extend_mono (J : Finset E) : Monotone (extend J) := by
  intro ξ ζ h e
  by_cases he : e ∈ J
  · simp only [extend, dite_eq_left he]
    exact h ⟨e,he⟩
  · simp only [extend, dite_eq_right he, le_refl]

end ProductCylinder

end OAI

-- ---- from OAI.Probability.CriticalZ3.Symmetry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical

namespace CriticalZ3
open Classical

theorem mem_internalBonds {D : Set Vertex} {hD : D.Finite} {e : Bond} :
    e ∈ internalBonds D hD ↔ e.1 ∈ D ∧ step e.1 e.2 ∈ D := by
  simp [internalBonds]

theorem bondWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : BondConfig}
    (hω : ∀ e ∈ internalBonds D hD, ω' e = ω e) :
    Within D (BondOpen ω') = Within D (BondOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,BondOpen]
    apply or_congr
    · apply exists_congr
      intro i
      by_cases he : y = step x i
      · rw [hω (x,i) (mem_internalBonds.mpr ⟨hx,he ▸ hy⟩)]
      · simp [he]
    · apply exists_congr
      intro i
      by_cases he : x = step y i
      · rw [hω (y,i) (mem_internalBonds.mpr ⟨hy,he ▸ hx⟩)]
      · simp [he]
  all_goals simp [Within,hx,hy]

theorem siteWithin_congr {D : Set Vertex} {hD : D.Finite} {ω ω' : SiteConfig}
    (hω : ∀ x ∈ hD.toFinset, ω' x = ω x) :
    Within D (SiteOpen ω') = Within D (SiteOpen ω) := by
  funext x y
  apply propext
  by_cases hx : x ∈ D <;> by_cases hy : y ∈ D
  · simp only [Within,hx,hy,true_and,SiteOpen,hω x (hD.mem_toFinset.mpr hx),
      hω y (hD.mem_toFinset.mpr hy)]
  all_goals simp [Within,hx,hy]

theorem bondSeedReaches_determined (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ internalBonds (cube c n) (cube_finite c n), ω' e = ω e) →
      (ω' ∈ bondSeedReaches c m n T ↔ ω ∈ bondSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [bondSeedReaches,Set.mem_ofPred_eq,bondWithin_congr hω]

theorem siteSeedReaches_determined (c : Vertex) (m n : ℕ) (hmn : m ≤ n) (T : Set Vertex) :
    ∀ ω ω', (∀ e ∈ (cube_finite c n).toFinset, ω' e = ω e) →
      (ω' ∈ siteSeedReaches c m n T ↔ ω ∈ siteSeedReaches c m n T) := by
  intro ω ω' hω
  simp only [siteSeedReaches,Set.mem_ofPred_eq,siteWithin_congr hω]
  apply exists_congr
  intro x
  by_cases hx : x ∈ cube c m
  · simp only [hx,true_and,hω x ((cube_finite c n).mem_toFinset.mpr (cube_mono c hmn hx))]
  · simp only [hx,false_and]

theorem bondOpen_mono {ω ω' : BondConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : BondOpen ω x y) : BondOpen ω' x y := by
  rcases hxy with ⟨i,hi,hw⟩ | ⟨i,hi,hw⟩
  · exact Or.inl ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (x,i))⟩
  · exact Or.inr ⟨i,hi,Bool.eq_true_of_true_le (hw ▸ h (y,i))⟩

theorem siteOpen_mono {ω ω' : SiteConfig} (h : ω ≤ ω') {x y : Vertex}
    (hxy : SiteOpen ω x y) : SiteOpen ω' x y :=
  ⟨hxy.1,Bool.eq_true_of_true_le (hxy.2.1 ▸ h x),Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)⟩

theorem bondSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ bondSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,y,hy,hp⟩
  refine ⟨x,hx,y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,bondOpen_mono h h'.2.2⟩

theorem siteSeedReaches_mono (c : Vertex) (m n : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ siteSeedReaches c m n T) := by
  rintro ω ω' h ⟨x,hx,hω,y,hy,hp⟩
  refine ⟨x,hx,Bool.eq_true_of_true_le (hω ▸ h x),y,hy,Relation.ReflTransGen.mono ?_ x y hp⟩
  intro a b h'
  exact ⟨h'.1,h'.2.1,siteOpen_mono h h'.2.2⟩

end CriticalZ3

namespace CriticalZ3
open Classical

namespace SignedSymmetry

end SignedSymmetry
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

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

variable [Countable E]

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

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

theorem conditional_failure_bound (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ ε : ℝ} (hδ : 0 < δ)
    (hfail : (ProductCylinder.law p).real (H ∩ Cᶜ) ≤ ε) :
    (ProductCylinder.law p).real {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤ ε/δ := by
  apply (le_div_iff₀ hδ).mpr
  simpa only [mul_comm] using (conditional_failure_mass p J H C hH hC hδ.le).trans hfail

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

theorem indicator_monotone {P : (E → Bool) → Prop} (hP : Monotone P) :
    Monotone (fun ω => if P ω then (1 : ℝ) else 0) := by
  intro ω ω' h
  by_cases h' : P ω
  · simp [h',hP h h']
  · simp only [h',ite_false]
    split_ifs <;> norm_num

theorem prob_and_increasing [Fintype E] (p : E → Set.Icc (0 : ℝ) 1)
    {P Q : (E → Bool) → Prop} (hP : Monotone P) (hQ : Monotone Q) :
    prob p P * prob p Q ≤ prob p (fun ω => P ω ∧ Q ω) := by
  have h := increasing p _ _ (indicator_monotone hP) (indicator_monotone hQ)
  change mean p _ * mean p _ ≤ mean p _
  convert h using 1
  congr 1
  funext ω
  by_cases h₁ : P ω <;> by_cases h₂ : Q ω <;> simp [h₁,h₂]
end FiniteAssociation

namespace ProductCylinder
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem determinedBy_mono {J K : Finset E} (hJK : J ⊆ K) {F : Type}
    {f : (E → Bool) → F} (hf : DeterminedBy J f) : DeterminedBy K f :=
  fun ω ω' h => hf ω ω' (fun e he => h e (hJK he))

theorem increasing_and (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (A B : Set (E → Bool))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : DeterminedBy (F := Prop) J (fun ω => ω ∈ B))
    (hmA : Monotone (fun ω => ω ∈ A)) (hmB : Monotone (fun ω => ω ∈ B)) :
    (law p).real A*(law p).real B ≤ (law p).real (A ∩ B) := by
  have he (C : Set (E → Bool)) (hC : DeterminedBy (F := Prop) J (fun ω => ω ∈ C)) :
      (law p).real C = FiniteAssociation.prob (fun e : J => p e) (fun ξ => extend J ξ ∈ C) := by
    rw [FiniteAssociation.prob_eq_real,Measure.real_def,Measure.real_def,
      probability_determined J p C (fun ω ω' h => eq_iff_iff.mp (hC ω ω' h))]
    rfl
  have hAB : DeterminedBy (F := Prop) J (fun ω => ω ∈ A ∩ B) := by
    intro ω ω' h
    simp only [Set.mem_inter_iff,hA ω ω' h,hB ω ω' h]
  rw [he A hA,he B hB,he (A ∩ B) hAB]
  exact FiniteAssociation.prob_and_increasing _ (hmA.comp (extend_mono J)) (hmB.comp (extend_mono J))

/-- The open-seed Harris estimate, with a separate increasing connecting event. -/
theorem seed_failure_bound (J : Finset E) (p : E → Set.Icc (0 : ℝ) 1)
    (O A C : Set (E → Bool))
    (hO : DeterminedBy (F := Prop) J (fun ω => ω ∈ O))
    (hA : DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hmO : Monotone (fun ω => ω ∈ O)) (hmA : Monotone (fun ω => ω ∈ A))
    (hsub : O ∩ A ⊆ C) {γ : ℝ} (hprob : 1-γ ≤ (law p).real A) :
    (law p).real (O ∩ Cᶜ) ≤ (law p).real O*γ := by
  have hm := measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h))
  have ha := increasing_and J p O A hO hA hmO hmA
  have hadd := measureReal_inter_add_sdiff (μ := law p) (s := O) hm
  have hsub' : O ∩ Cᶜ ⊆ O \ A := by
    intro ω hω
    exact ⟨hω.1,fun h => hω.2 (hsub ⟨hω.1,h⟩)⟩
  have hle := measureReal_mono (μ := law p) hsub'
  have h0 : 0 ≤ (law p).real O := measureReal_nonneg
  nlinarith
end ProductCylinder

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type}

theorem allValue_true_monotone (J : Finset E) : Monotone (fun ω => ω ∈ allValue J true) := by
  intro ω ω' h hh e he
  have hi := h e
  rw [hh e he] at hi
  exact le_antisymm le_top hi

end InfiniteConditioning

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

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

theorem seedReaches_mono (m : Model) (c : Vertex) (a b : ℕ) (T : Set Vertex) :
    Monotone (fun ω => ω ∈ m.SeedReaches c a b T) := by
  cases m
  · simpa only [seedReaches_bond] using bondSeedReaches_mono c a b T
  · exact siteSeedReaches_mono c a b T
end Model

namespace Box

theorem contains_cube_iff {c x : Vertex} {n : ℕ} : (cube c n).Contains x ↔ x ∈ CriticalZ3.cube c n :=
  mem_cube.symm

theorem cube_bonds_eq (c : Vertex) (r : ℕ) :
    (cube c r).bonds = internalBonds (CriticalZ3.cube c r) (cube_finite c r) := by
  ext e
  simp only [mem_bonds,mem_internalBonds,contains_cube_iff]

theorem cube_sites_eq (c : Vertex) (r : ℕ) :
    (cube c r).vertices = (cube_finite c r).toFinset := by
  ext e
  simp only [mem_vertices,Set.Finite.mem_toFinset,contains_cube_iff]
end Box

namespace Model

theorem seedReaches_determined (m : Model) (c : Vertex) (a b : ℕ) (hab : a ≤ b) (T : Set Vertex) :
    ProductCylinder.DeterminedBy (F := Prop) ((Box.cube c b).bits m)
      (fun ω => ω ∈ m.SeedReaches c a b T) := by
  intro ω ω' h
  apply propext
  cases m
  · rw [seedReaches_bond]
    apply bondSeedReaches_determined c a b T ω ω'
    simpa only [Box.bits,Box.cube_bonds_eq] using h
  · apply siteSeedReaches_determined c a b hab T ω ω'
    simpa only [Box.bits,Box.cube_sites_eq] using h
end Model

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

theorem seed_conditional_quality (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (T : Set Vertex) {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hseed : ∀ x, (Box.cube c a).Contains x → C.Contains x)
    (hB : G.ContainsBox (Box.cube c b)) (v : G.Node) (hv : v.1 = c)
    {γ τ : ℝ} (hτ : 0 < τ)
    (hprob : 1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c a b T)) :
    (ProductCylinder.law p).real
      {ω | ω ∈ allValue ((Box.cube c a).bits m) true ∧
        conditionalProbability p (C.bits m) {ω | G.Meets m ω v T} ω ≤ 1-τ} ≤
      (ProductCylinder.law p).real (allValue ((Box.cube c a).bits m) true)*γ/τ := by
  let O := allValue ((Box.cube c a).bits m) true
  have hdet := allValue_determined ((Box.cube c a).bits m) true
  apply conditional_failure_bound p (C.bits m) O {ω | G.Meets m ω v T}
    (ProductCylinder.determinedBy_mono (Box.bits_mono m hseed) hdet)
    (G.measurableSet_meets m v T) hτ
  apply ProductCylinder.seed_failure_bound ((Box.cube c b).bits m) p O
    (m.SeedReaches c a b T) _
    (ProductCylinder.determinedBy_mono (Box.bits_mono m (fun _ h =>
      Box.contains_cube_iff.mpr (cube_mono c hab (Box.contains_cube_iff.mp h)))) hdet)
    (m.seedReaches_determined c a b hab T) (allValue_true_monotone _) (m.seedReaches_mono c a b T)
  · intro ω h
    exact G.seedReaches_conn m hab hB T hv h.1 h.2
  · exact hprob
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

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.seed_conditional_quality := @_root_.OAI.CriticalZ3.LatticeGraph.seed_conditional_quality
