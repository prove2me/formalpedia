-- Prove2me | solution 1 for GlobalTheory.SeqFirst.isIso_restrict_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:45:37.003835+00:00
-- url     : https://prove2.me/submissions/7fd06bc1-caf8-45d2-97d3-51a184ee57f8

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
theorem _root_.solution {X Y : Scheme.{0}} (s : X ⟶ Y) {U V : Y.Opens} (hVU : V ≤ U)
    [IsIso (s ∣_ U)] : IsIso (s ∣_ V) := by
  have e : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
    exact inf_eq_right.2 hVU
  have h1 : IsIso ((s ∣_ U) ∣_ (U.ι ⁻¹ᵁ V)) := inferInstance
  exact ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict s U (U.ι ⁻¹ᵁ V) ≪≫ morphismRestrictEq s e)).1 h1
end GlobalTheory.SeqFirst
