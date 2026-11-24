-- Prove2me | solution 1 for GlobalTheory.Published.IdealInvariantsOneOrbitSt.exists_algEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:38:51.834833+00:00
-- url     : https://prove2.me/submissions/83271e6f-1e52-4cae-9f90-f3fead1669f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_GlobalTheta_ExistsMemIdealInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open scoped nonZeroDivisors IntermediateField
open GlobalTheory GlobalTheory.Published
variable {K : Type} [Field K] [NumberField K] [IsTotallyComplex K]
namespace GlobalTheory.Published
namespace IdealInvariantsOneOrbitSt
theorem _root_.solution [Algebra K ℂ] (h : IdealInvariantsOneOrbitSt)
    (h2 : Module.finrank ℚ K = 2) {𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L L' : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (hL' : IsIdealLattice 𝔟 L') :
    ∃ ρ : ℂ ≃ₐ[K] ℂ, ρ (latticeCurve L).j = (latticeCurve L').j := by
  have hmem : (latticeCurve L').j ∈ MulAction.orbit (ℂ ≃ₐ[K] ℂ) (latticeCurve L).j := by
    rw [(h K h2 𝔞 L hL).2]
    exact ⟨𝔟, L', hL', rfl⟩
  obtain ⟨ρ, hρ⟩ := hmem
  exact ⟨ρ, hρ⟩
end IdealInvariantsOneOrbitSt
end GlobalTheory.Published
