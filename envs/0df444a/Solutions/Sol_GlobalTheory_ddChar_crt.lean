-- Prove2me | solution 1 for GlobalTheory.ddChar_crt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:59.856298+00:00
-- url     : https://prove2.me/submissions/49986eb5-9e37-4991-9dd8-61adcca10e71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
  {A : Type} [CommGroup A]
namespace GlobalTheory
theorem _root_.solution [Finite R] (f : MaximalSpectrum R → R) :
    ∃ t : R, ∀ m : MaximalSpectrum R, t - f m ∈ m.asIdeal := by
  have : Finite (MaximalSpectrum R) :=
    Finite.of_injective (fun m : MaximalSpectrum R => (m.asIdeal : Set R))
      (fun a b hab => MaximalSpectrum.ext (SetLike.coe_injective hab))
  refine Ideal.exists_forall_sub_mem_ideal (I := fun m : MaximalSpectrum R => m.asIdeal) ?_ f
  intro a b hab
  have ha := a.isMaximal
  have hb := b.isMaximal
  exact Ideal.isCoprime_of_isMaximal (fun h => hab (MaximalSpectrum.ext h))
end GlobalTheory
