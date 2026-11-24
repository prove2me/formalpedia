-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.eq_zero_of_loc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:36:56.199806+00:00
-- url     : https://prove2.me/submissions/929bdbef-f4ff-4970-a985-f1bd1aec433a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PreimageEqOfSquareZeroThickeningStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartUniqueStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapCompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAffineCombinationSquareZeroLiftsChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationIndependentOfChart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SecGlue
open GlobalTheory GlobalTheory.SecGlue GlobalTheory.SecGlue.ChartIndep
namespace GlobalTheory.SecGlue.ChartIndep
theorem _root_.solution {S : Type} [CommRing S] (D : S)
    (h : ∀ p : Ideal S, p.IsMaximal → ∃ s ∉ p, algebraMap S (Localization.Away s) D = 0) : D = 0 := by
  by_contra hD
  let I : Ideal S := LinearMap.ker (LinearMap.toSpanSingleton S S D)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : S) ∈ I := hI ▸ Submodule.mem_top
    simp [I] at this
    exact hD this
  obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
  obtain ⟨s, hs, hsD⟩ := h p hp
  obtain ⟨⟨m, hm⟩, hmD⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers s) _ D).mp hsD
  obtain ⟨n, rfl⟩ := hm
  have : s ^ n ∈ I := by simp [I]; exact hmD
  exact hs (hp.isPrime.mem_of_pow_mem n (hIp this))
end GlobalTheory.SecGlue.ChartIndep
