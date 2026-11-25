-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_of_finite_cokernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:30.683635+00:00
-- url     : https://prove2.me/submissions/6c7b13bd-976f-4cec-be5d-da41a4d21eca

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Theorems.Thm_GroundTheory_ProfCoh_finite_modN_of_exact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
universe u
open GroundTheory.LocalField ValuativeRel IsLocalRing
namespace GroundTheory.ProfCoh
theorem _root_.solution {A B : Type*} [AddCommGroup A] [AddCommGroup B] {n : ℕ}
    (f : B →+ A) [Finite (A ⧸ f.range)] [Finite (ModN B n)] : Finite (ModN A n) := by
  have hfh : Function.Exact f (QuotientAddGroup.mk' f.range) :=
    fun y ↦ by rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]; rfl
  have : Finite (ModN (A ⧸ f.range) n) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  exact finite_modN_of_exact (QuotientAddGroup.mk'_surjective f.range) hfh
end GroundTheory.ProfCoh
