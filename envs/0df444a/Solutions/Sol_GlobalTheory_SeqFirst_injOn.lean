-- Prove2me | solution 1 for GlobalTheory.SeqFirst.injOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:36.21073+00:00
-- url     : https://prove2.me/submissions/ab73cdce-313a-462a-a2a7-8c67f1169317

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__GeometricallyConnectedOfIsIsoRestrict_f3ea578707b0384e
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIsoNearOrCentreMeets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.SeqFirst
namespace GlobalTheory.SeqFirst
theorem _root_.solution {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {a b : X}
    (ha : a ∈ s ⁻¹ᵁ U) (hb : b ∈ s ⁻¹ᵁ U) (h : s a = s b) : a = b := by
  obtain ⟨za, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = a := ⟨⟨a, ha⟩, rfl⟩
  obtain ⟨zb, rfl⟩ : ∃ z : ↥(s ⁻¹ᵁ U).toScheme, z.1 = b := ⟨⟨b, hb⟩, rfl⟩
  have : (s ∣_ U) za = (s ∣_ U) zb :=
    Subtype.ext ((morphismRestrict_base_coe s U za).trans (h.trans (morphismRestrict_base_coe s U zb).symm))
  exact congrArg Subtype.val ((s ∣_ U).homeomorph.injective this)
end GlobalTheory.SeqFirst
