-- Prove2me | solution 1 for GlobalTheory.Published.IdealInvariantsOneOrbitSt.exists_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:39:56.283145+00:00
-- url     : https://prove2.me/submissions/c23ce531-a3d7-4afb-87e2-667d6725cde4

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
    (h2 : Module.finrank ℚ K = 2) {𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (ρ : ℂ ≃ₐ[K] ℂ) :
    ∃ (𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (L' : PeriodPair),
      IsIdealLattice 𝔟 L' ∧ (latticeCurve L').j = ρ (latticeCurve L).j := by
  have hmem : ρ (latticeCurve L).j ∈ idealInvariants K := by
    rw [← (h K h2 𝔞 L hL).2]
    exact ⟨ρ, rfl⟩
  obtain ⟨𝔟, L', hL', hj⟩ := hmem
  exact ⟨𝔟, L', hL', hj⟩
end IdealInvariantsOneOrbitSt
end GlobalTheory.Published
