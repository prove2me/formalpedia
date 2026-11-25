-- Prove2me | solution 1 for GlobalTheory.Cyc.Procyclic.eqOn_of_dense
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:13:36.66015+00:00
-- url     : https://prove2.me/submissions/6e7b7b7c-6cab-4c44-971c-7939bb691a58

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
omit [IsUltrametricDist X]
namespace GlobalTheory.Cyc.Procyclic
theorem _root_.solution {H : Subgroup Γ} (hg : g ∈ G) (hHG : H ≤ G)
    (hd : (G : Set Γ) ⊆ closure {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a}) {f₁ f₂ : Γ → X}
    (h₁ : ContinuousOn f₁ G) (h₂ : ContinuousOn f₂ G)
    (h : ∀ h ∈ H, ∀ a : ℕ, f₁ (h * g ^ a) = f₂ (h * g ^ a)) : ∀ σ ∈ G, f₁ σ = f₂ σ := by
  refine Set.EqOn.of_subset_closure (s := {x | ∃ h ∈ H, ∃ a : ℕ, x = h * g ^ a}) ?_ h₁ h₂ ?_ hd
  · rintro _ ⟨x, hx, a, rfl⟩
    exact h x hx a
  · rintro _ ⟨x, hx, a, rfl⟩
    exact G.mul_mem (hHG hx) (pow_mem hg a)
end GlobalTheory.Cyc.Procyclic
