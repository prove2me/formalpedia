-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.exists_extension
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:32:36.056348+00:00
-- url     : https://prove2.me/submissions/439a1a7a-f5f8-482f-b3ca-6bb4ea401591

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CyclotomicCharacterPadicBasicProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ContinuousOrbitPadicComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_PadicNormZpowSubOnePadicValInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsCyclotomicTowerLevelGeneratorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TraceAlmostOntoOfLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CocycleVanishingOnFixingSubgroupDeterminedByGene

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc Filter Topology
open GlobalTheory GlobalTheory.Cyc GlobalTheory.Cyc.Procyclic
variable {Γ X : Type} [Group Γ] [NormedAddCommGroup X]
variable {G : Subgroup Γ} {A : Γ → X →+ X} {g : Γ} {w : X}
variable [IsUltrametricDist X]
variable [TopologicalSpace Γ]
omit [IsUltrametricDist X] [TopologicalSpace Γ]
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution [CompleteSpace X] (Gn : ℕ → Subgroup Γ) (hanti : Antitone Gn)
    (hcos : ∀ σ ∈ G, ∀ n, ∃ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn n) (S : ℕ → X)
    (hS : ∀ ε > 0, ∃ N, ∀ a b : ℕ, g ^ a * (g ^ b)⁻¹ ∈ Gn N → ‖S a - S b‖ ≤ ε) :
    ∃ c : Γ → X, ∀ ε > 0, ∃ N, ∀ σ ∈ G, ∀ a : ℕ, σ * (g ^ a)⁻¹ ∈ Gn N → ‖c σ - S a‖ ≤ ε := by
  choose! e he using hcos
  have key : ∀ {N : ℕ} {σ : Γ} {a b : ℕ}, σ * (g ^ a)⁻¹ ∈ Gn N → σ * (g ^ b)⁻¹ ∈ Gn N →
      g ^ a * (g ^ b)⁻¹ ∈ Gn N := by
    intro N σ a b ha hb
    have := (Gn N).mul_mem ((Gn N).inv_mem ha) hb
    simpa [mul_assoc] using this
  have hc : ∀ σ ∈ G, ∃ y, Tendsto (fun n => S (e σ n)) atTop (𝓝 y) := by
    intro σ hσ
    refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff.2 fun ε hε => ?_)
    obtain ⟨N, hN⟩ := hS (ε / 2) (half_pos hε)
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [dist_eq_norm]
    exact (hN _ _ (key (hanti hm (he σ hσ m)) (hanti hn (he σ hσ n)))).trans_lt (half_lt_self hε)
  choose! c hc using hc
  refine ⟨c, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := hS ε hε
  refine ⟨N, fun σ hσ a ha => ?_⟩
  refine le_of_tendsto ((hc σ hσ).sub_const (S a)).norm ?_
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN _ _ (key (hanti hn (he σ hσ n)) ha)
end GlobalTheory.Cyc.Procyclic
