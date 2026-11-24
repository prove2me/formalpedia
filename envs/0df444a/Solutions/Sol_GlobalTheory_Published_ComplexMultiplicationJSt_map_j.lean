-- Prove2me | solution 1 for GlobalTheory.Published.ComplexMultiplicationJSt.map_j
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:53.524689+00:00
-- url     : https://prove2.me/submissions/308d1c0b-fa57-48e7-afd8-ed066760658d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_ComplexMultiplicationJPremises
import Theorems.Thm_GlobalTheory_Published_IsHilbertClassField_unique
import Theorems.Thm_GlobalTheory_Published_IsArtinMap_unique

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
variable {K : Type} [Field K] [NumberField K] [Algebra K ℂ]
namespace GlobalTheory.Published
namespace ComplexMultiplicationJSt
theorem _root_.solution (h : ComplexMultiplicationJSt) [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) {H : IntermediateField K ℂ} (hH : IsHilbertClassField H)
    {art : ClassGroup (𝓞 K) →* (H ≃ₐ[K] H)} (hart : IsArtinMap art)
    {𝔞 𝔟 : (FractionalIdeal (𝓞 K)⁰ K)ˣ} {L L' : PeriodPair}
    (hL : IsIdealLattice 𝔞 L) (hL' : IsIdealLattice (𝔟⁻¹ * 𝔞) L') (ρ : ℂ →+* ℂ)
    (hρ : ∀ x : H, ρ x = art (ClassGroup.mk K 𝔟) x) :
    ρ (latticeCurve L).j = (latticeCurve L').j := by
  obtain ⟨H', art', hH', hart', hgen, hj⟩ := h K h2
  obtain rfl := hH.unique hH'
  obtain rfl := hart.unique hH.1 hart'
  have hm : (latticeCurve L).j ∈ H := hgen 𝔞 L hL ▸ IntermediateField.mem_adjoin_simple_self K _
  exact (hρ ⟨_, hm⟩).trans (hj 𝔞 𝔟 L L' hL hL' ⟨_, hm⟩ rfl)
end ComplexMultiplicationJSt
end GlobalTheory.Published
