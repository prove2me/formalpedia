-- Prove2me | solution 1 for GlobalTheory.HolHom.holAt_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:28:26.125659+00:00
-- url     : https://prove2.me/submissions/e2e36c13-6a99-4a8e-99b2-a339835db89d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_holAt_of_isPullback

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HolHom
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {S : Scheme.{0}}
namespace GlobalTheory.HolHom
theorem _root_.solution {P : V → Over S} {G G' : Over S} (i : ∀ t, Sp ℂ ⟶ (P t).left) {a : ∀ t, P t ⟶ G}
    {b : ∀ t, P t ⟶ G'} {z : V} (ha : HolAt (fun t => i t ≫ (a t).left) z)
    (hb : HolAt (fun t => i t ≫ (b t).left) z) : HolAt (fun t => i t ≫ (lift (a t) (b t)).left) z := by
  have H : IsPullback (fst G G').left (snd G G').left G.hom G'.hom := IsPullback.of_hasPullback G.hom G'.hom
  refine holAt_of_isPullback H ?_ ?_
  · simpa only [Category.assoc, ← Over.comp_left, lift_fst] using ha
  · simpa only [Category.assoc, ← Over.comp_left, lift_snd] using hb
end GlobalTheory.HolHom
