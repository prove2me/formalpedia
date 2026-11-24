-- Prove2me | solution 1 for GlobalTheory.le_saturation_iff_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:27:04.885012+00:00
-- url     : https://prove2.me/submissions/690e17e1-e573-4e14-83d3-88ec618d9bcb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_rank_saturation
import Theorems.Thm_GlobalTheory_le_saturation_of_rank_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Module.Finite R M] {N P : Submodule R M} (h : N ≤ P) :
    P ≤ saturation N ↔ Module.finrank R N = Module.finrank R P := by
  have hfin : ∀ Q : Submodule R M, Module.rank R Q < Cardinal.aleph0 := fun Q =>
    (Submodule.rank_le Q).trans_lt (Module.rank_lt_aleph0 R M)
  constructor
  · intro hP
    have h1 : Module.rank R N ≤ Module.rank R P := Submodule.rank_mono h
    have h2 : Module.rank R P ≤ Module.rank R N :=
      (Submodule.rank_mono hP).trans_eq (rank_saturation N)
    exact congrArg Cardinal.toNat (le_antisymm h1 h2)
  · intro he
    refine le_saturation_of_rank_le h (hfin N) ?_
    rw [← Cardinal.cast_toNat_of_lt_aleph0 (hfin P), ← Cardinal.cast_toNat_of_lt_aleph0 (hfin N)]
    exact_mod_cast he.ge
end GlobalTheory
