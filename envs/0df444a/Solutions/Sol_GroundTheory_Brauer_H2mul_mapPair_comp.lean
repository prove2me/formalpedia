-- Prove2me | solution 1 for GroundTheory.Brauer.H2mul.mapPair_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:44:24.599021+00:00
-- url     : https://prove2.me/submissions/ee203951-9ccd-4275-b424-a976c92ce4e2

import Mathlib
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open groupCohomology
universe u v u' v'
variable (G : Type u) (M : Type v) [Group G] [CommGroup M] [MulDistribMulAction G M]
open GroundTheory.Brauer.H2mul
variable {G M}
variable {G' : Type u'} {M' : Type v'} [Group G'] [CommGroup M'] [MulDistribMulAction G' M']
namespace GroundTheory.Brauer.H2mul
theorem _root_.solution {G'' : Type*} {M'' : Type*} [Group G''] [CommGroup M'']
    [MulDistribMulAction G'' M''] (f : G' →* G) (φ : M →* M')
    (hφ : ∀ (g : G') (m : M), φ (f g • m) = g • φ m) (f' : G'' →* G') (φ' : M' →* M'')
    (hφ' : ∀ (g : G'') (m : M'), φ' (f' g • m) = g • φ' m) :
    mapPair (f.comp f') (φ'.comp φ) (fun g m => by simp [hφ, hφ']) =
      (mapPair f' φ' hφ').comp (mapPair f φ hφ) := by
  ext x
  rfl
end GroundTheory.Brauer.H2mul
