-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_modN_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T06:29:36.607928+00:00
-- url     : https://prove2.me/submissions/bd3dd56d-bd9c-4431-b479-e3c5b47b430e

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_UnitsDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_SUnits
import Definitions.Def_GroundTheory_ProfiniteCohomology_GlobalEulerCharacteristic_GEqAddOfExactOfFiniteCokernel

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
universe u v
open NumberField NumberField.Units NumberField.InfinitePlace IsDedekindDomain Module
open GroundTheory.Global
open scoped TensorProduct
variable {A : Type*} [AddCommGroup A] [Module.Finite ℤ A] (n : ℕ) [NeZero n]
namespace GroundTheory.ProfCoh
theorem _root_.solution : Finite (ModN A n) := by
  apply Module.finite_of_fg_torsion
  intro y
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  change (n : ℤ) • (Submodule.Quotient.mk a : ModN A n) = 0
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact ⟨a, rfl⟩
end GroundTheory.ProfCoh
