-- Prove2me | solution 1 for GroundTheory.ProfCoh.adjoin_nthRoots_eq_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:32:39.061211+00:00
-- url     : https://prove2.me/submissions/811406e7-2e1f-41c3-a877-aad5336391ff

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerBasic
import Definitions.Def_GroundTheory_ProfiniteCohomology_KummerFinite
import Theorems.Thm_GroundTheory_ProfCoh_kummerField_kummerGroup

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.ProfCoh
open Polynomial
variable (K : Type*) [Field K] (n : ℕ) [NeZero n] [HasEnoughRootsOfUnity K n]
variable (L : Type*) [Field L] [Algebra K L]
variable {K n L}
variable (K n L)
namespace GroundTheory.ProfCoh
theorem _root_.solution [FiniteDimensional K L] [IsGalois K L]
    [IsMulCommutative Gal(L/K)] (hexp : Monoid.exponent Gal(L/K) ∣ n) :
    IntermediateField.adjoin K {α : L | α ≠ 0 ∧ α ^ n ∈ Set.range (algebraMap K L)} = ⊤ := by
  rw [eq_top_iff, ← kummerField_kummerGroup K n L hexp]
  apply IntermediateField.adjoin.mono
  rintro α ⟨a, -, hα⟩
  exact ⟨ne_zero_of_pow_eq_algebraMap hα, a, hα.symm⟩
end GroundTheory.ProfCoh
