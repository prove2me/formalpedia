-- Prove2me | solution 1 for GlobalTheory.PrimaryTorsionBlocks.mem_annOf
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:14:57.122382+00:00
-- url     : https://prove2.me/submissions/f20d811b-53f7-4486-b1b4-a00a4d6a5032

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory GlobalTheory.PrimaryTorsionBlocks
variable {R : Type} [CommRing R] {M : Type} [AddCommGroup M] [Module R M]
namespace GlobalTheory.PrimaryTorsionBlocks
theorem _root_.solution {x : M} {a : R} : a ∈ annOf x ↔ a • x = 0 := by
  simp [annOf]
end GlobalTheory.PrimaryTorsionBlocks
