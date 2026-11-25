-- Prove2me | solution 1 for GlobalTheory.PrimeElement.subalgebra_inf_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:15.914169+00:00
-- url     : https://prove2.me/submissions/0be7c46a-9630-43a7-bb0e-f74a3c22711b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingStalkGeneric
import Theorems.Thm_GlobalTheory_PrimeElement_range_inf_range


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeElement
namespace GlobalTheory.PrimeElement
theorem _root_.solution {R : Type*} [CommRing R] [IsDomain R] {π : R}
    [(Ideal.span {π}).IsPrime] (hπ : π ≠ 0) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] :
    Localization.subalgebra.ofField K (Submonoid.powers π)
        (powers_le_nonZeroDivisors_of_noZeroDivisors hπ) ⊓
      Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl
        (Ideal.span {π}).primeCompl_le_nonZeroDivisors = ⊥ := by
  refine eq_bot_iff.2 fun x hx ↦ ?_
  exact (range_inf_range (π := π)
    (Localization.subalgebra.ofField K (Submonoid.powers π)
      (powers_le_nonZeroDivisors_of_noZeroDivisors hπ))
    (Localization.subalgebra.ofField K (Ideal.span {π}).primeCompl
      (Ideal.span {π}).primeCompl_le_nonZeroDivisors) K hπ).le ⟨⟨⟨x, hx.1⟩, rfl⟩, ⟨⟨x, hx.2⟩, rfl⟩⟩
end GlobalTheory.PrimeElement
