-- Prove2me | solution 1 for GlobalTheory.isHomogeneous_span_gr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:34.969805+00:00
-- url     : https://prove2.me/submissions/fb2b2395-4733-4a17-bd41-2bad8bb1dd9b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_WeightAddLeOfMemSupportDividedContraction
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsGradedMapLinearCombination
import Theorems.Thm_GlobalTheory_IsGradedMap_sum
import Theorems.Thm_GlobalTheory_proj_smul_of_mem_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open DirectSum MvPolynomial
noncomputable section
open GlobalTheory
open GradedHilbert
variable {ι : Type*} {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
  {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
  {P : Type*} [AddCommGroup P] [Module R P] [Module (MvPolynomial ι R) P]
variable [IsScalarTower R (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) N]
namespace GlobalTheory
theorem _root_.solution (ℳ : ℤ → Submodule R M) [Decomposition ℳ] [PolyGradedSMul ι ℳ]
    {G : Set M} (hG : ∀ g ∈ G, ∃ d, g ∈ ℳ d) :
    (Submodule.span (MvPolynomial ι R) G).IsHomogeneous ℳ := by
  intro n m hm
  change proj ℳ n m ∈ _
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_iff_linearCombination _ _ _).1 hm
  rw [Finsupp.linearCombination_apply, Finsupp.sum, map_sum]
  refine Submodule.sum_mem _ fun g _ => ?_
  obtain ⟨d, hd⟩ := hG g g.2
  rw [proj_smul_of_mem_right ℳ _ hd]
  exact Submodule.smul_mem _ _ (Submodule.subset_span g.2)
end GlobalTheory
