-- Prove2me | solution 1 for GlobalTheory.exists_complete_discreteValuationRing_with_residues
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:02:43.865794+00:00
-- url     : https://prove2.me/submissions/b417268b-7fb7-4bea-aee0-6b7eb70eb100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_ExistsCompleteDiscreteValuationRingWithResidues
import Theorems.Thm_GlobalTheory_ResidueExtension_exists_finset
import Theorems.Thm_GlobalTheory_ResidueExtension_exists_completion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω]
      (r : O →+* Ω) (S : Finset Ω), RingHom.ker r = IsLocalRing.maximalIdeal O →
      ∃ (O' : Type) (_ : CommRing O') (_ : IsDomain O') (_ : IsDiscreteValuationRing O')
        (j : O →+* O') (r' : O' →+* Ω), IsAdicComplete (IsLocalRing.maximalIdeal O') O' ∧
        Function.Injective j ∧ IsLocalHom j ∧ r'.comp j = r ∧
        RingHom.ker r' = IsLocalRing.maximalIdeal O' ∧ ∀ a ∈ S, a ∈ Set.range r' := by
  intro O _ _ _ Ω _ r S hr
  obtain ⟨B, _, _, _, j, r', h1, h2, h3, h4⟩ := ResidueExtension.exists_finset r hr S
  obtain ⟨r'', h5, h6⟩ := ResidueExtension.exists_completion r' h3
  have h7 : r''.comp ((algebraMap B (AdicCompletion (maximalIdeal B) B)).comp j) = r := by
    rw [← RingHom.comp_assoc, h5, h2]
  refine ⟨AdicCompletion (maximalIdeal B) B, inferInstance, inferInstance, inferInstance,
    (algebraMap B _).comp j, r'', inferInstance,
    (algebraMap_adicCompletion_injective_of_dvr B).comp h1, ⟨fun x hx => ?_⟩, h7, h6,
    fun a ha => ?_⟩
  · rw [← notMem_maximalIdeal, ← hr, RingHom.mem_ker, ← h7]
    exact (hx.map r'').ne_zero
  · obtain ⟨y, rfl⟩ := h4 a ha
    exact ⟨_, RingHom.congr_fun h5 y⟩
end GlobalTheory
