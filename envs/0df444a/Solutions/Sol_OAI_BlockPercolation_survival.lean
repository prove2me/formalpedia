-- Prove2me | solution 1 for OAI.BlockPercolation.survival
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T23:00:36.790932+00:00
-- url     : https://prove2.me/submissions/c039f681-013a-4b14-82a1-6a9fa33bcdbe

-- Generated from openai/math@1581d4c lean/OAI/Probability/CriticalZ3/Subunit.lean:L89-L123
-- (upload_full_project.md Phase 4): solution for node OAI.BlockPercolation.survival. The node keeps its source
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
import Theorems.Thm_OAI_InfiniteConditioning_disjoint_blocks_probability
import Theorems.Thm_OAI_PlanarBoundary_blocked_bound
import Theorems.Thm_OAI_PlanarBoundary_encoded_budget_hasSum
import Theorems.Thm_OAI_PlanarBoundary_finite_good_subset

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

-- ---- from OAI.Probability.CriticalZ3.PlanarBoundary ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

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

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Filter Topology

namespace PlanarBoundary
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open Classical _root_.MeasureTheory ProbabilityTheory
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

-- ---- from OAI.Probability.CriticalZ3.Subunit ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
private abbrev Finset.prod_le_prod₀ := @Finset.prod_le_prod

namespace OAI

-- [generator] trimmed: open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

namespace BlockPercolation
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
open Classical _root_.MeasureTheory ProbabilityTheory PlanarBoundary
variable {E : Type}

theorem root_mem_iff (J : Point → Finset E) (ω : E → Bool) :
    (0,0) ∈ cluster J ω ↔ active J ω (0,0) :=
  ⟨And.left,fun h => ⟨h,.refl⟩⟩

theorem cluster_active {J : Point → Finset E} {ω : E → Bool} {v : Point}
    (hv : v ∈ cluster J ω) : active J ω v := by
  obtain ⟨h,hv⟩ := hv
  induction hv with
  | refl => exact h
  | tail _ hab _ => exact hab.2.2

theorem outside_bad (J : Point → Finset E) (ω : E → Bool) (x : Point)
    (hx : x ∈ cluster J ω) (d : Direction) (hy : x+outward d ∉ cluster J ω) :
    ω ∈ Bad J (x+outward d) := by
  intro ha
  exact hy ⟨hx.1,hx.2.tail ⟨⟨d,rfl⟩,cluster_active hx,ha⟩⟩

theorem bad_determined (J : Point → Finset E) (v : Point) :
    ProductCylinder.DeterminedBy (F := Prop) (J v) (fun ω => ω ∈ Bad J v) := by
  intro ω ω' h
  dsimp [Bad,active]
  congr 1
  apply propext
  constructor <;> intro hh e he
  · rw [←h e he]; exact hh e he
  · rw [h e he]; exact hh e he

theorem measurableSet_bad (J : Point → Finset E) (v : Point) : MeasurableSet (Bad J v) :=
  ProductCylinder.measurableSet_determined (J v) _
    (fun ω ω' h => eq_iff_iff.mp (bad_determined J v ω ω' h))

theorem single_closed_probability (p : Set.Icc (0 : ℝ) 1) (e : E) :
    (ProductCylinder.law (fun _ : E => p)).real {ω | ω e = false} = 1-(p : ℝ) := by
  have h := Measure.infinitePi_map_eval (fun _ : E => bernoulliMeasure true false p) e
  have hm : Measurable (fun ω : E → Bool => ω e) := measurable_pi_apply e
  have he : {ω : E → Bool | ω e = false} = (fun ω => ω e) ⁻¹' {false} := rfl
  rw [he,Measure.real_def,←Measure.map_apply hm (measurableSet_singleton _)]
  change ((Measure.infinitePi (fun _ : E => bernoulliMeasure true false p)).map
    (fun ω => ω e) {false}).toReal = _
  rw [h]
  change (bernoulliMeasure true false p).real {false} = _
  rw [bernoulliMeasure_real_apply p (measurableSet_singleton _)]
  simp [unitInterval.coe_symm_eq]

theorem bad_probability_le (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E) (v : Point) :
    (ProductCylinder.law (fun _ : E => p)).real (Bad J v) ≤ (J v).card*(1-(p : ℝ)) := by
  have he : Bad J v = ⋃ e : J v, {ω | ω e.1 = false} := by
    ext ω
    simp only [Bad,active,Set.mem_ofPred_eq,Set.mem_iUnion]
    constructor
    · intro h
      push Not at h
      obtain ⟨e,he,hω⟩ := h
      exact ⟨⟨e,he⟩,Bool.eq_false_iff.mpr hω⟩
    · rintro ⟨e,he⟩ h
      have := h e.1 e.2
      simp_all
  rw [he]
  apply (measureReal_iUnion_fintype_le _).trans
  simp only [single_closed_probability,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul,le_refl]

/-- Peierls survival for independent finite blocks of at most two bits. -/
theorem survival (p : Set.Icc (0 : ℝ) 1) (J : Point → Finset E)
    (hJ : Pairwise (fun u v => Disjoint (J u) (J v))) (hcard : ∀ v, (J v).card ≤ 2)
    (hp : 2*(1-(p : ℝ)) ≤ CriticalScales.contourError)
    (A : Set (E → Bool))
    (hA : ∀ ω, (cluster J ω).Infinite → ω ∈ A) :
    0 < ProductCylinder.law (fun _ : E => p) A := by
  let μ := ProductCylinder.law (fun _ : E => p)
  have hb (v : Point) : μ.real (Bad J v) ≤ CriticalScales.contourError := by
    apply (bad_probability_le p J v).trans
    exact (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard v) (sub_nonneg.mpr p.2.2)).trans hp
  have hbad (s : Finset Point) : μ.real {ω | ∀ v ∈ s, ω ∈ Bad J v} ≤
      CriticalScales.contourError^s.card := by
    rw [InfiniteConditioning.disjoint_blocks_probability (fun _ : E => p) J hJ (Bad J) (bad_determined J) s]
    calc
      _ ≤ ∏ _v ∈ s, CriticalScales.contourError :=
        Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun v _ => hb v)
      _ = _ := by simp
  have hf := PlanarBoundary.finite_good_bound μ (cluster J) (Bad J)
    (fun ω _ x hx d hy => outside_bad J ω x hx d hy) hbad
  have hroot : 1-CriticalScales.contourError ≤ μ.real {ω | active J ω (0,0)} := by
    have he : {ω | active J ω (0,0)} = (Bad J (0,0))ᶜ := by ext ω; simp [Bad]
    rw [he,measureReal_compl (measurableSet_bad J (0,0)),probReal_univ]
    linarith [hb (0,0)]
  have hcover : {ω | active J ω (0,0)} ⊆
      {ω | (cluster J ω).Finite ∧ (0,0) ∈ cluster J ω} ∪ A := by
    intro ω hω
    by_cases hfinite : (cluster J ω).Finite
    · exact Or.inl ⟨hfinite,(root_mem_iff J ω).mpr hω⟩
    · exact Or.inr (hA ω hfinite)
  have hle := (measureReal_mono (μ := μ) hcover).trans (measureReal_union_le _ _)
  have hpos : 0 < μ.real A := by
    have hh := CriticalScales.contourError_lt_half
    linarith
  exact ENNReal.toReal_pos_iff.mp hpos |>.1

end BlockPercolation

namespace CriticalZ3
-- [generator] trimmed: open Classical _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory PlanarBoundary
open Classical _root_.MeasureTheory ProbabilityTheory PlanarBoundary

end CriticalZ3

end OAI

-- ---- platform node ----
open OAI OAI.BlockPercolation
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Classical _root_.MeasureTheory ProbabilityTheory PlanarBoundary


theorem solution : type_of% @_root_.OAI.BlockPercolation.survival := @_root_.OAI.BlockPercolation.survival
