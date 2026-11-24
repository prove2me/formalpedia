-- Prove2me | solution 1 for GlobalTheory.HolHom.isDerivAt_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:45:02.517016+00:00
-- url     : https://prove2.me/submissions/5bf3bb8c-5210-429a-baf7-0ea81b23232a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HasArcDataIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_HolomorphicHomDetermined
import Theorems.Thm_GlobalTheory_HolHom_HolAt_comp
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_unique
import Theorems.Thm_GlobalTheory_HolHom_IsDerivAt_comp
import Theorems.Thm_GlobalTheory_HolHom_HolAt_exists_isDerivAt
import Theorems.Thm_GlobalTheory_HolHom_holAt_lift

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
variable {G : Over S} [GrpObj G]
variable {y : Sp ℂ ⟶ S}
omit [GrpObj G]
namespace GlobalTheory.HolHom
theorem _root_.solution {G' : Over S} {a : V → (Over.mk y ⟶ G)} {b : V → (Over.mk y ⟶ G')} {z w : V}
    (ha : HolAt (fun t => (a t).left) z) (hb : HolAt (fun t => (b t).left) z) {v : epsPt y ⟶ G} {v' : epsPt y ⟶ G'}
    (hv : IsDerivAt (fun t => (a t).left) z w v.left) (hv' : IsDerivAt (fun t => (b t).left) z w v'.left) :
    IsDerivAt (fun t => (lift (a t) (b t)).left) z w (lift v v').left := by
  have hl : HolAt (fun t => (lift (a t) (b t)).left) z := by
    simpa using holAt_lift (P := fun _ => Over.mk y) (fun _ => 𝟙 (Sp ℂ)) (a := a) (b := b) (z := z)
      (by simpa using ha) (by simpa using hb)
  obtain ⟨u, hu⟩ := hl.exists_isDerivAt w
  have h1 := hu.comp (fst G G').left
  have h2 := hu.comp (snd G G').left
  simp only [← Over.comp_left, lift_fst, lift_snd] at h1 h2
  have H : IsPullback (fst G G').left (snd G G').left G.hom G'.hom := IsPullback.of_hasPullback G.hom G'.hom
  have : (lift v v').left = u := by
    refine H.hom_ext ?_ ?_
    · rw [h1.unique hv, ← Over.comp_left, lift_fst]
    · rw [h2.unique hv', ← Over.comp_left, lift_snd]
  exact this ▸ hu
end GlobalTheory.HolHom
