-- Prove2me | solution 1 for GlobalTheory.isLocalHom_of_extend_adicCompletion
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:15:37.709571+00:00
-- url     : https://prove2.me/submissions/1b68d2c0-7919-47ec-9569-98fcd544803f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry IsLocalRing
universe u
open GlobalTheory
variable {A R : Type*} [CommRing A] [CommRing R]
namespace GlobalTheory
theorem _root_.solution [IsLocalRing A] [IsLocalRing R]
    (hJ : (maximalIdeal A).FG) (ψ : AdicCompletion (maximalIdeal A) A →+* R)
    [hψ : IsLocalHom (ψ.comp (algebraMap A (AdicCompletion (maximalIdeal A) A)))] :
    IsLocalHom ψ := by
  have := AdicCompletion.isLocalRing_of_fg hJ
  apply ((IsLocalRing.local_hom_TFAE ψ).out 0 2).mpr
  rw [AdicCompletion.maximalIdeal_eq_map_of_fg hJ, Ideal.map_map]
  exact ((IsLocalRing.local_hom_TFAE _).out 0 2).mp hψ
end GlobalTheory
