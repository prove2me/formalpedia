-- Prove2me | solution 1 for GroundTheory.ProfCoh.finite_torsN_of_torsion_trivial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:48.284304+00:00
-- url     : https://prove2.me/submissions/84a11c73-7b84-4451-a9b0-54acc954b34f

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_UnitsLattice
import Definitions.Def_GroundTheory_LocalFields_NormalLattice
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalEulerCharacteristic_ModNEquivOfSurjectiveApplyModNRep

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
theorem _root_.solution {A : Type*} [AddCommGroup A] {n : ℕ}
    (h : ∀ a : A, n • a = 0 → a = 0) : Finite (TorsN A n) :=
  have : Subsingleton (TorsN A n) := ⟨fun x y ↦ Subtype.ext
    ((h _ ((mem_ker_lsmul_iff n _).mp x.2)).trans (h _ ((mem_ker_lsmul_iff n _).mp y.2)).symm)⟩
  Finite.of_subsingleton
end GroundTheory.ProfCoh
