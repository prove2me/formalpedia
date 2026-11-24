-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrobHaarR.exists_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:36.63714+00:00
-- url     : https://prove2.me/submissions/19ebc49c-4799-4243-8afb-d2c5ad565ed5

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_GroundTheory_AutomorphicForms_LocallyProfinite
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalEqHaarMultiple
import Theorems.Thm_GlobalTheory_CompanionTheory_FrobHaarR_exists_decomp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobHaarR
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
namespace GlobalTheory.CompanionTheory.FrobHaarR
theorem _root_.solution (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : SB G)
    (hf : ∀ k ∈ K, ∀ x, (f : G → ℂ) (k * x) = (f : G → ℂ) x) :
    ∃ s : ℂ, ∀ M : SB G →ₗ[ℂ] ℂ,
      (∀ (g : G) (α : SB G), M (pullHomeo (Homeomorph.mulRight g) α) = M α) →
        M f = s * M (ind K hK) := by
  obtain ⟨S, a, h⟩ := exists_decomp K hK f hf
  refine ⟨∑ t ∈ S, a t, fun M hM => ?_⟩
  rw [h, _root_.map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_smul, hM, smul_eq_mul]
end GlobalTheory.CompanionTheory.FrobHaarR
