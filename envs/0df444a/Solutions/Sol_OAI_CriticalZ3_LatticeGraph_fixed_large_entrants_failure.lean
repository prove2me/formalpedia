-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.fixed_large_entrants_failure
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T21:59:57.50445+00:00
-- url     : https://prove2.me/submissions/76f185d5-7a86-4d22-9897-643c30024b44

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Extension.lean:L33-L101
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.fixed_large_entrants_failure. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_Box_separated_subset
import Theorems.Thm_OAI_CriticalZ3_Box_successBits_disjoint
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_fixed_bad_success_mass
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_success_reaches_center
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability
import Theorems.Thm_OAI_InfiniteConditioning_map_replace
import Theorems.Thm_OAI_TrialCounts_no_good_probability

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

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem neighbor_coordinates {x y : Vertex} (h : NearestNeighbor x y) :
    ∃ i, |y i-x i| = 1 ∧ ∀ k, k ≠ i → y k = x k := by
  obtain ⟨i, h | h⟩ := h
  · subst y
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]
  · subst x
    refine ⟨i,by simp [step],?_⟩
    intro k hk
    simp [step,Ne.symm hk]

theorem neighbor_distance {x y : Vertex} (h : NearestNeighbor x y) (i : Fin 3) :
    |y i-x i| ≤ 1 := by
  obtain ⟨k,hk,he⟩ := neighbor_coordinates h
  by_cases hik : i = k
  · simp [hik,hk]
  · simp [he i hik]

theorem neighbor_in_expand (B : Box) {x y : Vertex}
    (hx : B.Contains x) (hxy : NearestNeighbor x y) : (B.expand 1).Contains y := by
  intro i
  have hi := hx i
  have hd := neighbor_distance hxy i
  rw [abs_le] at hd
  change B.lower i-1 ≤ y i ∧ y i ≤ B.upper i+1
  omega

/-- The exact number of candidates excluded in one greedy selection. -/
theorem card_cube (c : Vertex) (m : ℕ) : (cube c m).vertices.card = (2*m+1)^3 := by
  rw [vertices,Pi.card_Icc]
  have he (i : Fin 3) : (Finset.Icc ((cube c m).lower i) ((cube c m).upper i)).card = 2*m+1 := by
    rw [Int.card_Icc]
    dsimp [cube]
    omega
  simp only [he,Finset.prod_const,Finset.card_univ,Fintype.card_fin]

theorem translateVertex_injective (c : Vertex) : Function.Injective (translateVertex c) := by
  intro x y h
  funext i
  have hi := congrFun h i
  dsimp [translateVertex] at hi
  omega

theorem translateBond_injective (c : Vertex) : Function.Injective (translateBond c) := by
  intro e e' h
  have h1 : e.1 = e'.1 := translateVertex_injective c (congrArg Prod.fst h)
  have h2 : e.2 = e'.2 := by simpa only [translateBond] using congrArg Prod.snd h
  exact Prod.ext h1 h2

theorem cube_bonds_translate (c : Vertex) (m : ℕ) :
    (cube c m).bonds = (cube 0 m).bonds.image (translateBond c) := by
  ext e
  constructor
  · intro he
    let e' : Bond := (fun i => e.1 i-c i,e.2)
    have heq : translateBond c e' = e := by
      apply Prod.ext
      · funext i; simp [translateBond,translateVertex,e']
      · rfl
    refine Finset.mem_image.mpr ⟨e',?_,heq⟩
    rw [←heq,mem_bonds] at he
    simpa [translateBond,translateVertex] using he
  · intro he
    obtain ⟨e',he',rfl⟩ := Finset.mem_image.mp he
    simpa [translateBond,translateVertex] using he'

theorem cube_bonds_card (c : Vertex) (m : ℕ) :
    (cube c m).bonds.card = (cube 0 m).bonds.card := by
  rw [cube_bonds_translate,Finset.card_image_of_injective _ (translateBond_injective c)]

end Box
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
theorem incidence_internal {B : Box} {x y : Vertex} {e : Bond}
    (hx : B.Contains x) (hy : B.Contains y) (he : Incidence e x y) : e ∈ B.bonds := by
  rw [Box.mem_bonds]
  rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact ⟨hx,hy⟩
  · exact ⟨hy,hx⟩

end LatticeGraph
end CriticalZ3

end OAI

-- ---- from OAI.Probability.CriticalZ3.EntryLayers ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical

theorem neighborBond_incidence {x y : Vertex} (h : NearestNeighbor x y) :
    Incidence (neighborBond x y) x y := by
  simp only [neighborBond,dite_eq_left h]
  exact (LatticeGraph.neighbor_incidence h).choose_spec

namespace Box

theorem entry_spec {C : Box} {y : Vertex} (h : C.Exterior y) :
    C.Contains (C.entry y) ∧ NearestNeighbor y (C.entry y) := by
  simp only [entry,dite_eq_left h]
  exact h.2.choose_spec

theorem exterior_expand {C : Box} {y : Vertex} (h : C.Exterior y) :
    (C.expand 1).Contains y := by
  obtain ⟨z,hz,hzy⟩ := h.2
  apply C.neighbor_in_expand hz
  obtain ⟨i,hi | hi⟩ := hzy
  · exact ⟨i,Or.inr hi⟩
  · exact ⟨i,Or.inl hi⟩

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

theorem outsideBits_disjoint_inside (m : Model) (C : Box) :
    Disjoint (G.outsideBits m C) (C.bits m) := by
  rw [Finset.disjoint_left]
  intro e he he'
  cases m
  · exact (Finset.mem_filter.mp he).2.1 ((Box.mem_bonds C e).mp he').1
  · exact (Finset.mem_filter.mp he).2 ((Box.mem_vertices C e).mp he')

theorem entryBit_not_outside (m : Model) {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit m y ∉ G.outsideBits m C := by
  intro he
  have hentry := (Box.entry_spec hy).1
  cases m
  · have hi := neighborBond_incidence (Box.entry_spec hy).2
    obtain ⟨_,hout,hout'⟩ := Finset.mem_filter.mp he
    rcases hi with ⟨_,hz⟩ | ⟨hz,_⟩
    · exact hout' (hz ▸ hentry)
    · exact hout (hz ▸ hentry)
  · exact (Finset.mem_filter.mp he).2 hentry

end CriticalZ3.LatticeGraph

end OAI

-- ---- from OAI.Probability.CriticalZ3.SeedTrials ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3
open Classical
namespace Box

theorem cube_bits_card (m : Model) (c : Vertex) (r : ℕ) :
    ((cube c r).bits m).card = ((cube 0 r).bits m).card := by
  cases m
  · exact cube_bonds_card _ _
  · simp only [bits,card_cube]

theorem crossing_not_internal {C : Box} {y : Vertex} (hy : C.Exterior y) :
    C.entryBit .bond y ∉ C.bonds := by
  intro he
  obtain ⟨h0,h1⟩ := (mem_bonds C _).mp he
  have hi := neighborBond_incidence (entry_spec hy).2
  rcases hi with ⟨hx,_⟩ | ⟨_,hx⟩
  · exact hy.1 (hx ▸ h0)
  · exact hy.1 (hx ▸ h1)

theorem successBits_card (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    (C.successBits r m y).card = successCard m r := by
  cases m
  · have he : C.entryBit .bond y ∉ (C.seedBox r y).bonds := fun h =>
      C.crossing_not_internal hy (bits_mono .bond (C.seedBox_contained r hw y) h)
    rw [successBits,Finset.card_insert_of_notMem he]
    change ((cube (C.relayCenter r y) r).bits .bond).card+1 = _
    rw [cube_bits_card]; rfl
  · exact cube_bits_card .site (C.relayCenter r y) r

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

theorem successBits_disjoint_outside (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    Disjoint (C.successBits r m y) (G.outsideBits m C) := by
  have hs := (G.outsideBits_disjoint_inside m C).symm.mono_left
    (Box.bits_mono m (C.seedBox_contained r hw y))
  cases m
  · rw [Box.successBits,Finset.disjoint_insert_left]
    exact ⟨G.entryBit_not_outside .bond hy,hs⟩
  · exact hs

end LatticeGraph
end CriticalZ3

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

private theorem measurable_determined_sigma (J : Finset E) (A : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A)) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] A := by
  let M := ⨆ e ∈ (J : Set E), bitSigma e
  let mask : (E → Bool) → (E → Bool) := fun ω e => if e ∈ J then ω e else false
  have hm : @Measurable (E → Bool) (E → Bool) M MeasurableSpace.pi mask := by
    apply @Measurable.of_eval (E → Bool) E (fun _ => Bool) M _ mask
    intro e
    by_cases he : e ∈ J
    · simp only [mask,ite_eq_left he]
      exact Measurable.of_comap_le (le_iSup_of_le e (le_iSup_of_le he le_rfl))
    · simp only [mask,ite_eq_right he]; exact measurable_const
  have heq : mask ⁻¹' A = A := by
    ext ω
    exact eq_iff_iff.mp (hA ω (mask ω) (fun e he => by simp [mask,he]))
  rw [←heq]
  exact hm (ProductCylinder.measurableSet_determined J A (fun ω ω' h => eq_iff_iff.mp (hA ω ω' h)))

/-- Arbitrary observables of disjoint finite blocks are independent under the
infinite product law, also when other coordinates have been fixed to 0 or 1. -/
theorem indepSet_determined (p : E → Set.Icc (0 : ℝ) 1) (J K : Finset E)
    (hJK : Disjoint J K) (A B : Set (E → Bool))
    (hA : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ A))
    (hB : ProductCylinder.DeterminedBy (F := Prop) K (fun ω => ω ∈ B)) :
    IndepSet A B (ProductCylinder.law p) := by
  have hi : iIndepFun (fun e (ω : E → Bool) => ω e) (ProductCylinder.law p) :=
    iIndepFun_infinitePi (X := fun _ => id) (fun _ => measurable_id)
  have hmi : iIndep (bitSigma (E := E)) (ProductCylinder.law p) :=
    (iIndepFun_iff_iIndep _ _ _).mp hi
  have h := indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le) hmi
    (show Disjoint (J : Set E) (K : Set E) from Finset.disjoint_coe.mpr hJK)
  exact h.indepSet_of_measurableSet (measurable_determined_sigma J A hA)
    (measurable_determined_sigma K B hB)

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

theorem allValue_determined (J : Finset E) (b : Bool) :
    ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ allValue J b) := by
  intro ω ω' h
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_allValue (J : Finset E) (b : Bool) : MeasurableSet (allValue J b) :=
  ProductCylinder.measurableSet_determined J _
    (fun ω ω' h => eq_iff_iff.mp (allValue_determined J b ω ω' h))

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

theorem measurableSet_conditional_test (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (C : Set (E → Bool)) (a : ℝ) :
    MeasurableSet {ω | conditionalProbability p J C ω ≤ a} := by
  refine ProductCylinder.measurableSet_determined J _ ?_
  intro ω ω' h
  simp only [Set.mem_ofPred_eq,conditionalProbability_determined p J C ω ω' h]
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

theorem successBits_contained (C : Box) (r : ℕ) (m : Model)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) {y : Vertex} (hy : C.Exterior y) :
    C.successBits r m y ⊆ (C.expand 1).bits m := by
  have hs := bits_mono m (fun x hx => C.contains_expand 1 (C.seedBox_contained r hw y x hx))
  cases m
  · intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · exact LatticeGraph.incidence_internal (exterior_expand hy)
        (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
    · exact hs he
  · exact hs
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

theorem entrant_exterior {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : C.Exterior y :=
  (Finset.mem_filter.mp hy).2.choose_spec.1

theorem entrant_node {C : Box} {ω : m.Config} {o : G.Node} {y : Vertex}
    (hy : y ∈ G.entrants m C ω o) : y ∈ G.vertices := (Finset.mem_filter.mp hy).1

/-- Actual separated seed trials under an arbitrary fixed outside pattern. -/
theorem fixed_large_entrants_failure (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ))
    (C : Box) (r K : ℕ) (hK : 0 < K)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    (o : G.Node) (T : Set Vertex) (ξ : m.Config)
    (hp : ∀ e ∈ (C.expand 1).bits m, p e = q) {γ τ : ℝ} (hτ : 0 < τ)
    (hqual : ∀ y, C.Exterior y → (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ)
    (hlarge : K*(8*r+5)^3 ≤ (G.entrants m C ξ o).card) :
    (ProductCylinder.law (fixedParameter p (G.outsideBits m C) ξ)).real
      {ω | ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)} ≤
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ := by
  let pf := fixedParameter p (G.outsideBits m C) ξ
  let μ := ProductCylinder.law pf
  let c := (q : ℝ)^Box.successCard m r
  obtain ⟨t,ht,hcard,hsep⟩ := Box.separated_subset (G.entrants m C ξ o) r K hlarge
  let v (y : t) := G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y.1
  let F (y : t) := {ω | conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω ≤ 1-τ}
  let A (y : t) := allValue (C.successBits r m y.1) true
  let B (y : t) := A y ∩ F y
  have hy (y : t) : C.Exterior y.1 := G.entrant_exterior m (ht y.2)
  have hF (y : t) : ProductCylinder.DeterminedBy (F := Prop) (C.bits m) (fun ω => ω ∈ F y) := by
    intro ω ω' h
    simp only [F,Set.mem_ofPred_eq,conditionalProbability_determined p (C.bits m) _ ω ω' h]
  have hfresh (y : t) : ∀ e ∈ C.successBits r m y.1, pf e = q := by
    intro e he
    change fixedParameter p (G.outsideBits m C) ξ e = q
    rw [fixedParameter,ite_eq_right (Finset.disjoint_left.mp (G.successBits_disjoint_outside m C r hw (hy y)) he)]
    exact hp e (C.successBits_contained r m hw (hy y) he)
  have hmass (y : t) : μ.real (A y) = c := by
    rw [allValue_probability_constant pf _ q (hfresh y)]
    simp only [bitProbability,ite_true,C.successBits_card r m hw (hy y)]
    rfl
  have hpair (y z : t) (hyz : y ≠ z) : μ.real (A y ∩ A z) ≤ c*c := by
    have hd := C.successBits_disjoint r m hw (hy y) (hy z)
      (hsep y y.2 z z.2 (fun h => hyz (Subtype.ext h)))
    have hind := indepSet_determined pf _ _ hd (A y) (A z)
      (allValue_determined _ _) (allValue_determined _ _)
    have hh : μ.real (A y ∩ A z) = μ.real (A y)*μ.real (A z) := by
      simp only [Measure.real_def,μ,hind.measure_inter_eq_mul,ENNReal.toReal_mul]
    rw [hh,hmass y,hmass z]
  have hbad (y : t) : μ.real (B y) ≤ c*γ/τ :=
    G.fixed_bad_success_mass m p q C r hw (hy y) ξ hp (F y) (hF y) (hqual y (hy y))
  have hbound := TrialCounts.no_good_probability μ A B
    (fun _ => measurableSet_allValue _ _)
    (fun y => (measurableSet_allValue _ _).inter (measurableSet_conditional_test _ _ _ _))
    (c := c) (γ := γ) (τ := τ)
    (by rw [Fintype.card_coe,hcard]; exact mul_pos (Nat.cast_pos.mpr hK) (pow_pos hq _))
    hτ hmass hpair hbad
  rw [Fintype.card_coe,hcard] at hbound
  apply (finite_measureReal_mono_ae (μ := μ) ?_).trans hbound
  filter_upwards [ae_fixed_determined p (G.outsideBits m C) ξ
    (fun ω => G.entrants m C ω o) (G.entrants_determined m C o)] with ω hω
  intro hfail y hAy
  refine ⟨hAy,?_⟩
  by_contra hnot
  have hg : 1-τ < conditionalProbability p (C.bits m) {ω | G.Meets m ω (v y) T} ω :=
    lt_of_not_ge hnot
  have hyω : y.1 ∈ G.entrants m C ω o := hω.symm ▸ ht y.2
  let yn : G.Node := ⟨y.1,G.entrant_node m hyω⟩
  obtain ⟨u,hu,hconn⟩ := G.success_reaches_center m C r hw hC (y := yn) hyω hAy
  have huv : u = v y := Subtype.ext hu
  apply hfail
  refine ⟨u,?_,hconn⟩
  exact ⟨v y,congrArg Subtype.val huv.symm,hg⟩

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

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.fixed_large_entrants_failure := @_root_.OAI.CriticalZ3.LatticeGraph.fixed_large_entrants_failure
