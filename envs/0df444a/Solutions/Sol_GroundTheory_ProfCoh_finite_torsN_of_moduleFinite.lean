-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:36:46.006914+00:00
-- url     : https://prove2.me/submissions/99f188df-b8cc-4ad5-88be-de5be27dc745

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
theorem _root_.solution : Finite (TorsN A n) := by
  have : Module.Finite ℤ (TorsN A n) :=
    Module.Finite.of_injective (LinearMap.ker (LinearMap.lsmul ℤ A (n : ℤ))).subtype
      Subtype.val_injective
  apply Module.finite_of_fg_torsion
  intro x
  refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast NeZero.ne n)⟩, ?_⟩
  apply Subtype.ext
  change (n : ℤ) • (x : A) = 0
  rw [natCast_zsmul]
  exact (mem_ker_lsmul_iff n (x : A)).1 x.2
end GroundTheory.ProfCoh
