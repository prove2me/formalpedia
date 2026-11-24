-- Prove2me | solution 1 for GlobalTheory.SecGlue.ChartIndep.locMap_ker
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:37:16.363926+00:00
-- url     : https://prove2.me/submissions/56fd3b92-a451-479a-80e6-d9e0a9124d99

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
variable {S T : Type} [CommRing S] [CommRing T] (q : S →+* T) (s : S)
namespace GlobalTheory.SecGlue.ChartIndep
theorem _root_.solution (hk : RingHom.ker q ^ 2 = ⊥) : RingHom.ker (locMap q s) ^ 2 = ⊥ := by
  have hprod : ∀ a b : S, a ∈ RingHom.ker q → b ∈ RingHom.ker q → a * b = 0 := by
    intro a b ha hb
    have : a * b ∈ RingHom.ker q ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha hb
    rw [hk] at this
    exact (Submodule.mem_bot S).mp this

  have hform : ∀ x ∈ RingHom.ker (locMap q s), ∃ (k : S) (m : Submonoid.powers s),
      k ∈ RingHom.ker q ∧ x = IsLocalization.mk' (Localization.Away s) k m := by
    intro x hx
    obtain ⟨⟨k, m⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers s) x
    rw [RingHom.mem_ker] at hx
    simp only [locMap] at hx
    rw [IsLocalization.map_mk' (M := Submonoid.powers s) (S := Localization.Away s)
      (T := (Submonoid.powers s).map q), IsLocalization.mk'_eq_zero_iff] at hx
    obtain ⟨⟨m', hm'⟩, hm'k⟩ := hx
    obtain ⟨m'', hm'', rfl⟩ := Submonoid.mem_map.mp hm'
    refine ⟨m'' * k, ⟨m'', hm''⟩ * m, ?_, ?_⟩
    · rw [RingHom.mem_ker, map_mul]; exact hm'k
    · simp only
      rw [IsLocalization.mk'_eq_iff_eq]
      simp only [Submonoid.coe_mul]
      ring_nf
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  obtain ⟨k, m, hk1, rfl⟩ := hform x hx
  obtain ⟨k', m', hk2, rfl⟩ := hform y hy
  rw [← IsLocalization.mk'_mul, hprod k k' hk1 hk2, IsLocalization.mk'_zero]
  exact Submodule.zero_mem _
end GlobalTheory.SecGlue.ChartIndep
