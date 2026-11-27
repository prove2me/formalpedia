-- Prove2me | solution 1 for GlobalTheory.ZM.DwModel.densePrimes_univ_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:40:59.190747+00:00
-- url     : https://prove2.me/submissions/b9bdc92c-2fbd-4472-a7c8-6825b29b6774

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_NotIsGaloisCoverTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.DwModel
namespace GlobalTheory.ZM.DwModel
theorem _root_.solution (R : Type) [CommRing R] : DenseP (Set.univ : Set (Ideal R)) ↔ _root_.IsReduced R := by
  constructor
  · intro h
    refine ⟨fun x hx => h x fun p _ hp => ?_⟩
    obtain ⟨k, hk⟩ := hx
    exact hp.mem_of_pow_mem k (hk ▸ p.zero_mem)
  · intro hR f hf
    have hnil : f ∈ nilradical R := by
      rw [nilradical_eq_sInf, Ideal.mem_sInf]
      exact fun p hp => hf p (Set.mem_univ p) hp
    exact (mem_nilradical.mp hnil).eq_zero
end GlobalTheory.ZM.DwModel
