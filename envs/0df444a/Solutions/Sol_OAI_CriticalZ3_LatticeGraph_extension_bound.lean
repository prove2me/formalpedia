-- Prove2me | solution 1 for OAI.CriticalZ3.LatticeGraph.extension_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T22:04:12.094521+00:00
-- url     : https://prove2.me/submissions/9c8b9e4f-6eba-4786-bce4-68281e94b187

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Extension.lean:L172-L242
-- (upload_full_project.md Phase 4): solution for node OAI.CriticalZ3.LatticeGraph.extension_bound. The node keeps its source
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
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_exists_shell
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_large_entrants_failure
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_random_relay_failure
import Theorems.Thm_OAI_CriticalZ3_LatticeGraph_seed_conditional_quality
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability

-- ---- from OAI.Probability.CriticalZ3.BoxGeometry ----
namespace OAI

-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical Filter
open _root_.MeasureTheory ProbabilityTheory Classical Filter

open scoped ENNReal BigOperators Matrix

namespace CriticalZ3

open Classical

namespace Box

theorem expand_mono (B : Box) {j k : ℕ} (hjk : j ≤ k) {x : Vertex}
    (h : (B.expand j).Contains x) : (B.expand k).Contains x := by
  intro i
  have hi := h i
  change B.lower i-j ≤ x i ∧ x i ≤ B.upper i+j at hi
  change B.lower i-k ≤ x i ∧ x i ≤ B.upper i+k
  omega

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

theorem expanded_seed_width (B : Box) {m j : ℕ} (hmj : m ≤ j) (i : Fin 3) :
    (B.expand j).lower i+m ≤ (B.expand j).upper i-m := by
  have h : B.lower i ≤ B.upper i := B.ordered i
  dsimp [expand]
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

end Box

namespace LatticeGraph
variable (G : LatticeGraph)

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

end InfiniteConditioning

namespace InfiniteConditioning
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical
open _root_.MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

end InfiniteConditioning

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

end CriticalZ3.LatticeGraph

namespace CriticalZ3
-- [generator] trimmed: open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
open _root_.OAI.MeasureTheory ProbabilityTheory Classical InfiniteConditioning
namespace Box

theorem entryBit_internal_expand {C : Box} {y : Vertex} (hy : C.Exterior y) (m : Model) :
    C.entryBit m y ∈ (C.expand 1).bits m := by
  cases m
  · exact LatticeGraph.incidence_internal (exterior_expand hy)
      (C.contains_expand 1 (entry_spec hy).1) (neighborBond_incidence (entry_spec hy).2)
  · exact (mem_vertices _ _).mpr (C.contains_expand 1 (entry_spec hy).1)
end Box

namespace LatticeGraph
variable (G : LatticeGraph) (m : Model)

/-- The shell + separated-seed + interior-quality extension, with all probability
terms explicit. The input seed events are the exact cube-restricted events. -/
theorem extension_bound (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (q : Set.Icc (0 : ℝ) 1) (hq : 0 < (q : ℝ)) {p₀ : ℝ} (hqp : (q : ℝ) ≤ p₀) (hp₀ : p₀ < 1)
    (B : Box) (r K R : ℕ) (hK : 0 < K) (hrR : r < R)
    (hG : G.ContainsBox (B.expand R)) (o : G.Node) (T : Set Vertex)
    (ho : ¬(B.expand R).Contains o.1)
    (hp : ∀ e ∈ (B.expand R).bits m, p e = q)
    {γ τ : ℝ} (hγ : 0 ≤ γ) (hτ : 0 < τ)
    (hreach : ∀ c, (B.expand R).Contains c → ∃ ℓ : ℕ,
      r ≤ ℓ ∧ G.ContainsBox (Box.cube c ℓ) ∧
      1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c r ℓ T)) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ≤
      1/((1-p₀)^(K*(8*r+5)^3)*(R-r : ℕ)) +
        4/(K*(q : ℝ)^Box.successCard m r)+2*γ/τ+τ := by
  have hsub (j : ℕ) (hj : j < R) : ∀ x, ((B.expand j).expand 1).Contains x →
      (B.expand R).Contains x := by
    intro x hx
    rw [Box.expand_expand] at hx
    exact B.expand_mono (by omega) hx
  obtain ⟨j,hj,hlayer⟩ := G.exists_shell m p B o q hqp hp₀ (K*(8*r+5)^3) r R hrR ho (by
    intro j hj y hy
    exact hp _ (Box.bits_mono m (hsub j (Finset.mem_Ico.mp hj).2) (Box.entryBit_internal_expand hy m)))
  let C := B.expand j
  have hjR : j < R := (Finset.mem_Ico.mp hj).2
  have hw : ∀ i, C.lower i+r ≤ C.upper i-r := B.expanded_seed_width (Finset.mem_Ico.mp hj).1
  have hC : G.ContainsBox (C.expand 1) := hG.mono G (hsub j hjR)
  have hpC : ∀ e ∈ (C.expand 1).bits m, p e = q := fun e he =>
    hp e (Box.bits_mono m (hsub j hjR) he)
  have hqual (y : Vertex) (_hy : C.Exterior y) : (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩
        {ω | conditionalProbability p (C.bits m)
          {ω | G.Meets m ω (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) T} ω ≤ 1-τ})
        ≤ (q : ℝ)^Box.seedCard m r*γ/τ := by
    let c := C.relayCenter r y
    have hc : C.Contains c := C.seedBox_contained r hw y _ (Box.center_mem_cube _ _)
    obtain ⟨ℓ,hrℓ,hcube,hprob⟩ := hreach c (B.expand_mono hjR.le hc)
    have hmass : (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true) =
        (q : ℝ)^Box.seedCard m r := by
      rw [allValue_probability_constant p _ q (by
        intro e he
        exact hpC e (Box.bits_mono m (fun x hx => C.contains_expand 1
          (C.seedBox_contained r hw y x hx)) he))]
      simp only [bitProbability,ite_true,Box.seedBox,Box.cube_bits_card,Box.seedCard]
    have hh := G.seed_conditional_quality m p C T hrℓ (C.seedBox_contained r hw y)
      hcube (G.relayNode C r hw (hC.mono G (fun _ => C.contains_expand 1)) y) rfl hτ hprob
    change (ProductCylinder.law p).real
      (allValue ((C.seedBox r y).bits m) true ∩ _) ≤
      (ProductCylinder.law p).real (allValue ((C.seedBox r y).bits m) true)*γ/τ at hh
    rwa [hmass] at hh
  have hlarge := G.large_entrants_failure m p q hq C r K hK hw hC o T hpC hγ hτ hqual
  have hrelay := G.random_relay_failure m p (C.bits m) o T hτ.le
  let E₁ : Set m.Config := {ω | G.Meets m ω o {x | B.Contains x} ∧
    (G.entrants m C ω o).card < K*(8*r+5)^3}
  let E₂ : Set m.Config := {ω | K*(8*r+5)^3 ≤ (G.entrants m C ω o).card ∧
    ¬G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)}
  let E₃ : Set m.Config := {ω | G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω) ∧
    ¬G.Meets m ω o T}
  have hcontain : {ω | G.Meets m ω o {x | B.Contains x} ∧ ¬G.Meets m ω o T} ⊆ (E₁ ∪ E₂) ∪ E₃ := by
    intro ω hω
    by_cases hn : (G.entrants m C ω o).card < K*(8*r+5)^3
    · exact Or.inl (Or.inl ⟨hω.1,hn⟩)
    · by_cases hg : G.Meets m ω o (G.goodRelays m p (C.bits m) T τ ω)
      · exact Or.inr ⟨hg,hω.2⟩
      · exact Or.inl (Or.inr ⟨le_of_not_gt hn,hg⟩)
  have hh := (measureReal_mono (μ := ProductCylinder.law p) hcontain).trans
    ((measureReal_union_le (E₁ ∪ E₂) E₃).trans
      (add_le_add (measureReal_union_le E₁ E₂) le_rfl))
  have := hh.trans (add_le_add (add_le_add hlayer hlarge) hrelay)
  simpa only [add_assoc] using this

end LatticeGraph
end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning


theorem solution : type_of% @_root_.OAI.CriticalZ3.LatticeGraph.extension_bound := @_root_.OAI.CriticalZ3.LatticeGraph.extension_bound
