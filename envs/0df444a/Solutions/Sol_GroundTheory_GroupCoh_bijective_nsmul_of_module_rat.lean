-- Prove2me | solution 1 for GroundTheory.GroupCoh.bijective_nsmul_of_module_rat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:55.744913+00:00
-- url     : https://prove2.me/submissions/9bdcf4b5-2fc6-418b-9ab5-c2b31cd612c6

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_UniquelyDivisible

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits Rep
universe u
variable {G : Type} [Group G] [Fintype G]
namespace GroundTheory.GroupCoh
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℚ V] {n : ℕ}
    (hn : n ≠ 0) : Function.Bijective fun v : V => n • v := by
  have : (fun v : V => n • v) = LinearEquiv.smulOfUnit (M := V)
      (IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ))) := by
    funext v
    change _ = IsUnit.unit (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hn) : IsUnit (n : ℚ)) • v
    rw [Units.smul_def, IsUnit.unit_spec, Nat.cast_smul_eq_nsmul]
  rw [this]
  exact LinearEquiv.bijective _
end GroundTheory.GroupCoh
