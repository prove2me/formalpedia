-- Prove2me | solution 1 for OAI.InfiniteConditioning.pattern_inter
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:07:44.467597+00:00
-- url     : https://prove2.me/submissions/f25b0755-9895-4b86-af27-55fad753d415

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

open OAI OAI.InfiniteConditioning
universe uF
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]
theorem hc_map_replace {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by
  have hr : replace J ξ = fun ω e => (fun (b : Bool) => if e ∈ J then ξ e else b) (ω e) := by
    funext ω e; simp [replace]
  unfold ProductCylinder.law
  rw [hr, Measure.infinitePi_map_pi _ (fun e => Measurable.of_discrete)]
  congr 1; funext e
  by_cases he : e ∈ J
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = fun _ => ξ e := by funext b; simp [he]
    rw [h1, Measure.map_const, measure_univ, one_smul]
    unfold fixedParameter
    rw [if_pos he]
    cases ξ e
    · simp
    · simp
  · have h1 : (ite (e ∈ J) (ξ e) : Bool → Bool) = id := by funext b; simp [he]
    rw [h1, Measure.map_id]
    unfold fixedParameter
    rw [if_neg he]

theorem hc_bits_iIndep {E : Type} (p : E → Set.Icc (0 : ℝ) 1) :
    iIndep (fun e => bitSigma e) (ProductCylinder.law p) := by
  have := iIndepFun_infinitePi (P := fun e => bernoulliMeasure true false (p e))
    (X := fun _ (b : Bool) => b) (fun _ => measurable_id)
  rw [iIndepFun_iff_iIndep (fun _ => inferInstance)] at this
  exact this

theorem hc_indep_split {E : Type} (p : E → Set.Icc (0 : ℝ) 1) {S T : Set E} (hST : Disjoint S T)
    {s t : Set (E → Bool)} (hs : MeasurableSet[⨆ e ∈ S, bitSigma e] s)
    (ht : MeasurableSet[⨆ e ∈ T, bitSigma e] t) :
    ProductCylinder.law p (s ∩ t) = ProductCylinder.law p s * ProductCylinder.law p t :=
  (Indep_iff _ _ _).mp (indep_iSup_of_disjoint (fun e => (measurable_pi_apply e).comap_le)
    (hc_bits_iIndep p) hST) s t hs ht

theorem hc_bit_meas {E : Type} {S : Set E} {e : E} (he : e ∈ S) (b : Bool) :
    MeasurableSet[⨆ e ∈ S, bitSigma e] {ω : E → Bool | ω e = b} := by
  have h : MeasurableSet[bitSigma e] {ω : E → Bool | ω e = b} :=
    MeasurableSpace.measurableSet_comap.mpr ⟨{b}, trivial, rfl⟩
  exact (le_iSup₂ (f := fun e (_ : e ∈ S) => bitSigma e) e he) _ h

theorem hc_pattern_meas {E : Type} (J : Finset E) (ξ : E → Bool) :
    MeasurableSet[⨆ e ∈ (J : Set E), bitSigma e] (pattern J ξ) := by
  have : pattern J ξ = ⋂ e ∈ J, {ω : E → Bool | ω e = ξ e} := by
    ext ω; simp [pattern]
  rw [this]
  exact MeasurableSet.biInter J.countable_toSet (fun e he => hc_bit_meas he (ξ e))

theorem hc_replace_meas {E : Type} (J : Finset E) (ξ : E → Bool) :
    Measurable[⨆ e ∈ ((J : Set E)ᶜ), bitSigma e] (replace J ξ) := by
  rw [@measurable_pi_iff]
  intro e
  by_cases he : e ∈ J
  · have : (fun ω : E → Bool => replace J ξ ω e) = fun _ => ξ e := by funext ω; simp [replace, he]
    rw [this]; exact measurable_const
  · have : (fun ω : E → Bool => replace J ξ ω e) = fun ω => ω e := by funext ω; simp [replace, he]
    rw [this]
    exact (comap_measurable (fun ω : E → Bool => ω e)).mono
      (le_iSup₂ (f := fun e (_ : e ∈ ((J : Set E)ᶜ)) => bitSigma e) e (by simpa using he)) le_rfl

theorem hc_pattern_inter {E : Type} (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  have hset : pattern J ξ ∩ A = pattern J ξ ∩ (replace J ξ ⁻¹' A) := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : replace J ξ ω = ω := by
        funext e; by_cases he : e ∈ J
        · simp [replace, he, h1 e he]
        · simp [replace, he]
      rwa [this]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      have : replace J ξ ω = ω := by
        funext e; by_cases he : e ∈ J
        · simp [replace, he, h1 e he]
        · simp [replace, he]
      rwa [this] at h2
  rw [hset, hc_indep_split p disjoint_compl_right (hc_pattern_meas J ξ) (hc_replace_meas J ξ hA),
    ← hc_map_replace p J ξ, Measure.map_apply (hc_replace_meas J ξ |>.mono (iSup₂_le (fun e _ => (measurable_pi_apply e).comap_le)) le_rfl) hA]

theorem solution (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by
  exact hc_pattern_inter p J ξ A hA

