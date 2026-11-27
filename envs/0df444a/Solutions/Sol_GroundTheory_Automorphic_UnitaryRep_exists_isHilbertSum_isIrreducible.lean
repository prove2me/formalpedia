-- Prove2me | solution 1 for GroundTheory.Automorphic.UnitaryRep.exists_isHilbertSum_isIrreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:46:25.707945+00:00
-- url     : https://prove2.me/submissions/371fcae6-fe61-4eee-b351-371d9cfc08e0

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_UnitaryRepresentations
import Definitions.Def_GroundTheory_AutomorphicForms_DiscreteSpectrumAbstract
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_isIrreducible_restrict_of_isMinimal
import Theorems.Thm_GroundTheory_Automorphic_UnitaryRep_exists_isHilbertSum_isMinimal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.UnitaryRep
open MeasureTheory Filter Topology Module End
open scoped InnerProductSpace ComplexConjugate
open ContinuousLinearMap
noncomputable section
variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] [OpensMeasurableSpace G]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable (π : UnitaryRep G H) (μ : Measure G)
variable {π μ}
variable [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
  [IsFiniteMeasureOnCompacts μ] [μ.IsOpenPosMeasure]
namespace GroundTheory.Automorphic.UnitaryRep
theorem _root_.solution
    (hcpt : ∀ f : CompactlySupportedContinuousMap G ℂ,
      IsCompactOperator (π.integrated μ (ccToL1 μ f))) :
    ∃ s : Set (Submodule ℂ H), ∃ _ : ∀ V : s, CompleteSpace (V : Submodule ℂ H),
      ∃ hinv : ∀ V : s, π.IsInvariant V,
      IsHilbertSum ℂ (fun V : s => (V : Submodule ℂ H)) (fun V => (V : Submodule ℂ H).subtypeₗᵢ) ∧
      ∀ V : s, (π.restrict V (hinv V)).IsIrreducible := by
  obtain ⟨s, hcomp, hmin, hsum⟩ := exists_isHilbertSum_isMinimal hcpt
  exact ⟨s, hcomp, fun V => (hmin V V.2).2.1, hsum, fun V =>
    isIrreducible_restrict_of_isMinimal _ (hmin V V.2)⟩
end GroundTheory.Automorphic.UnitaryRep
