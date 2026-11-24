-- Prove2me | solution 1 for GlobalTheory.SeqFirst.exists_preimage
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:35.500086+00:00
-- url     : https://prove2.me/submissions/906564b0-3531-4017-a0e6-edcf8e4392ce

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
theorem _root_.solution {X Y : Scheme.{0}} (s : X ⟶ Y) {U : Y.Opens} [IsIso (s ∣_ U)] {y : Y} (hy : y ∈ U) :
    ∃ x ∈ s ⁻¹ᵁ U, s x = y := by
  obtain ⟨z, hz⟩ := (s ∣_ U).homeomorph.surjective ⟨y, hy⟩
  refine ⟨z.1, z.2, ?_⟩
  have := congrArg Subtype.val hz
  rw [← morphismRestrict_base_coe]
  exact this
end GlobalTheory.SeqFirst
