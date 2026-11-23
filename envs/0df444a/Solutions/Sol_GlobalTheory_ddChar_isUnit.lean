-- Prove2me | solution 1 for GlobalTheory.ddChar_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:59.836163+00:00
-- url     : https://prove2.me/submissions/05d1b5cc-4c1b-4e8c-afad-c6cb53a78db7

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
theorem _root_.solution {x : R} (h : ∀ m : MaximalSpectrum R, x ∉ m.asIdeal) : IsUnit x := by
  by_contra hx
  obtain ⟨M, hM, hxM⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.2 hx)
  exact h ⟨M, hM⟩ hxM
end GlobalTheory
