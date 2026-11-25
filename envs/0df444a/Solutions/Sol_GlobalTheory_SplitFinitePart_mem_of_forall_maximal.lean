-- Prove2me | solution 1 for GlobalTheory.SplitFinitePart.mem_of_forall_maximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:15:19.573817+00:00
-- url     : https://prove2.me/submissions/56a514dc-6081-4574-8bff-a4eb7c3c2045

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsSectionOfIsIntegralHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SplitFinitePart
namespace GlobalTheory.SplitFinitePart
theorem _root_.solution {S : Type} [CommRing S] (U : (Sp S).Opens)
    (h : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → ∀ y, spMap (Ideal.Quotient.mk 𝔪) y ∈ U) (s : Sp S) : s ∈ U := by
  obtain ⟨𝔪, h𝔪, hle⟩ := Ideal.exists_le_maximal s.asIdeal s.isPrime.ne_top
  have := h𝔪.isPrime
  have h1 := h 𝔪 h𝔪 ⟨⊥, Ideal.isPrime_bot⟩
  refine Specializes.mem_open ((PrimeSpectrum.le_iff_specializes _ _).mp ?_) U.isOpen h1
  intro a ha
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (hle ha)
end GlobalTheory.SplitFinitePart
