-- Prove2me | solution 1 for GlobalTheory.SepGen.isReduced
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:58:41.602725+00:00
-- url     : https://prove2.me/submissions/753d49d7-b375-43db-b8ea-cefd74fc770d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AdjoinEqTopAndIsReducedOfCharpolySeparable
import Theorems.Thm_GlobalTheory_SepGen_charpoly_dvd
import Theorems.Thm_GlobalTheory_SepGen_aeval_charpoly
import Theorems.Thm_GlobalTheory_SepGen_adjoin_eq_top

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.SepGen
variable {E : Type} [Field E] {A : Type} [CommRing A] [Algebra E A] [Module.Finite E A]
namespace GlobalTheory.SepGen
theorem _root_.solution (y : A) (hs : (LinearMap.mulLeft E y).charpoly.Separable) : IsReduced A := by
  have h3 := adjoin_eq_top y hs
  refine ⟨fun z ⟨k, hk⟩ => ?_⟩
  have hz : z ∈ Algebra.adjoin E ({y} : Set A) := by rw [h3]; trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
  obtain ⟨p, rfl⟩ := hz
  have h4 := charpoly_dvd y hs (p ^ k) (by rw [map_pow]; exact hk)
  obtain ⟨r, hr⟩ := hs.squarefree.isRadical k p h4
  change aeval y p = 0
  rw [hr, map_mul, aeval_charpoly, zero_mul]
end GlobalTheory.SepGen
