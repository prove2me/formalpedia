-- Prove2me | solution 1 for GroundTheory.Global.cycHerbrand_congr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:08.894894+00:00
-- url     : https://prove2.me/submissions/0adec742-0b4d-4089-8029-cf5d63cee525

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
import Theorems.Thm_GroundTheory_Global_cycHerbrand_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V W : Type*} [CommRing k] [Group G] [Fintype G] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]
namespace GroundTheory.Global
theorem _root_.solution {ρ : Representation k G V} {ρ' : Representation k G W}
    (e : V ≃+ W) (he : ∀ g v, e (ρ g v) = ρ' g (e v)) (σ : G) :
    cycHerbrand ρ σ = cycHerbrand ρ' σ := by
  rw [cycHerbrand_eq, cycHerbrand_eq, Nat.card_congr (cycTateZeroCongr e he σ).toEquiv,
    Nat.card_congr (cycTateNegOneCongr e he σ).toEquiv]
end GroundTheory.Global
