-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.large_entrants_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:02:17.642199+00:00
-- url     : https://prove2.me/submissions/1976efc6-4cb1-4c12-babc-75953ec81eb5

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Extension.lean:L115-L153
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.large_entrants_failure. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_fixed_large_entrants_failure
import Theorems.Thm_OAI_InfiniteConditioning_map_replace
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

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

namespace Box

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

end LatticeGraph
end CriticalZ3

namespace CriticalZ3.LatticeGraph
open Classical
variable (G : LatticeGraph)

theorem outsideAdj_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (x y : G.Node) :
    G.OutsideAdj m C ω' x y ↔ G.OutsideAdj m C ω x y := by
  have hh (ω ω' : m.Config) (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e)
      (ha : G.OutsideAdj m C ω' x y) : G.OutsideAdj m C ω x y := by
    refine ⟨ha.1,ha.2.1,?_⟩
    cases m
    · obtain ⟨e,he,hi,ho⟩ := ha.2.2
      refine ⟨e,he,hi,?_⟩
      have hem : e ∈ G.outsideBits .bond C := by
        apply Finset.mem_filter.mpr
        refine ⟨he,?_⟩
        rcases hi with ⟨hx,hy⟩ | ⟨hy,hx⟩
        · exact ⟨hx ▸ ha.1,hy ▸ ha.2.1⟩
        · exact ⟨hy ▸ ha.2.1,hx ▸ ha.1⟩
      rw [←h e hem]; exact ho
    · exact ⟨ha.2.2.1,(h x.1 (Finset.mem_filter.mpr ⟨x.2,ha.1⟩)) ▸ ha.2.2.2.1,
        (h y.1 (Finset.mem_filter.mpr ⟨y.2,ha.2.1⟩)) ▸ ha.2.2.2.2⟩
  exact ⟨hh ω ω' h, hh ω' ω (fun e he => (h e he).symm)⟩

theorem outsideReach_determined (m : Model) (C : Box) (ω ω' : m.Config)
    (h : ∀ e ∈ G.outsideBits m C, ω' e = ω e) (o y : G.Node) :
    G.OutsideReach m C ω' o y ↔ G.OutsideReach m C ω o y := by
  by_cases ho : C.Contains o.1
  · simp only [OutsideReach,ho,not_true_eq_false,false_and]
  have hr : G.OutsideAdj m C ω' = G.OutsideAdj m C ω := by
    funext x y; exact propext (G.outsideAdj_determined m C ω ω' h x y)
  have hop : G.Open m ω' o ↔ G.Open m ω o := by
    cases m
    · rfl
    · change (ω' o.1 = true) ↔ (ω o.1 = true)
      rw [h o.1 (Finset.mem_filter.mpr ⟨o.2,ho⟩)]
  simp only [OutsideReach,hr,hop]

theorem entrants_determined (m : Model) (C : Box) (o : G.Node) :
    ProductCylinder.DeterminedBy (G.outsideBits m C) (fun ω => G.entrants m C ω o) := by
  intro ω ω' h
  ext y
  simp only [entrants,Finset.mem_filter,G.outsideReach_determined m C ω ω' h]

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.Conditioning ----
-- Lean 4.33 compatibility: Measurable.of_eval is the renamed measurable_pi_lambda
-- (Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean at d13f23b records the alias).
section Lean433MeasurableOfEval
private theorem Measurable.of_eval {α δ : Type*} {X : δ → Type*}
    [MeasurableSpace α] [∀ a, MeasurableSpace (X a)] {f : α → ∀ a, X a}
    (hf : ∀ a, Measurable fun c => f c a) : Measurable f :=
  measurable_pi_lambda f hf
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

theorem ae_fixed_pattern (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), ω ∈ pattern J ξ := by
  rw [←map_replace]
  apply (ae_map_iff (measurable_replace J ξ).aemeasurable
    (measurableSet_pattern J ξ)).mpr
  exact Filter.Eventually.of_forall (fun ω e he => ite_eq_left he)

/-- On a fixed revealed pattern, every J-determined quantity is constant. -/
theorem ae_fixed_determined {F : Sort uF} (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (ξ : E → Bool) (f : (E → Bool) → F)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω) :
    ∀ᵐ ω ∂ProductCylinder.law (fixedParameter p J ξ), f ω = f ξ := by
  filter_upwards [ae_fixed_pattern p J ξ] with ω hω
  exact hf ξ ω hω

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

end Model

namespace Box

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

theorem measurableSet_meets_goodRelays (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) (τ : ℝ) :
    MeasurableSet {ω | G.Meets m ω o (G.goodRelays m p J T τ ω)} := by
  refine ProductCylinder.measurableSet_determined (G.bits m ∪ J) _ ?_
  intro ω ω' h
  have hg := G.goodRelays_determined m p J T τ ω ω' (fun e he => h e (Finset.mem_union_right _ he))
  simp only [Set.mem_ofPred_eq,hg]
  exact eq_iff_iff.mp (G.meets_determined m o _ ω ω' (fun e he => h e (Finset.mem_union_left _ he)))

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
end MeasureTheory

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

end CriticalZ3.LatticeGraph

namespace CriticalZ3.LatticeGraph
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem measurableSet_large_entrants (C : Box) (o : G.Node) (L : ℕ) :
    MeasurableSet {ω | L ≤ (G.entrants m C ω o).card} := by
  apply ProductCylinder.measurableSet_determined (G.outsideBits m C)
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,G.entrants_determined m C o ω ω' h]

/-- Integrating the exact separated-trial estimate, including histories with
fewer than L entries. -/
theorem large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ) :
    (ProductCylinder.law p).real
      {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
        ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let E : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  have hm : MeasurableSet E := (G.measurableSet_large_entrants m C o _).inter
    (G.measurableSet_meets_goodRelays m p (C.bits m) o T τ).compl
  have hr := select_probability_le p (G.outsideBits m C) (fun _ => E) (fun _ => hm)
    (b := 4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ) ?_
  · exact hr
  · intro a
    let ξ := ProductCylinder.extend (G.outsideBits m C) a
    by_cases hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card
    · exact (measureReal_mono (fun _ h => h.2)).trans
        (G.fixed_large_entrants_failure m p q hq C r K hK hw hC o T ξ hp hτ hqual hlarge)
    · have he : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real E = 0 := by
        have hz : (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)) E = 0 := by
          apply measure_eq_zero_iff_ae_notMem.mpr
          filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
            (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
          intro h
          exact hlarge (hω ▸ h.1)
        simp only [Measure.real_def,hz,ENNReal.toReal_zero]
      rw [he]
      positivity

end CriticalZ3.LatticeGraph

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
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


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.large_entrants_failure := @_root_.OAI.CriticalZ3.LatticeGraph.large_entrants_failure
