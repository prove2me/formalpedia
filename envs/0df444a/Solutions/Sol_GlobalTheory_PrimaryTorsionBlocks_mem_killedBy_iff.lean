-- Prove2me | solution 1 for GlobalTheory.PrimaryTorsionBlocks.mem_killedBy_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:29:29.62575+00:00
-- url     : https://prove2.me/submissions/0da4bb26-c207-45bf-b260-9779ab37de72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TorsionCountMultiplicativePrimePowers
import Theorems.Thm_GlobalTheory_PrimaryTorsionBlocks_mem_annOf

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
theorem _root_.solution {I : Ideal R} {x : M} : x ∈ killedBy (M := M) I ↔ I ≤ annOf x :=
  ⟨fun h a ha => mem_annOf.2 (h a ha), fun h a ha => mem_annOf.1 (h ha)⟩
end GlobalTheory.PrimaryTorsionBlocks
