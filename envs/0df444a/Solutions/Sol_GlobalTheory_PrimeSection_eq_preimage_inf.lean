-- Prove2me | solution 1 for GlobalTheory.PrimeSection.eq_preimage_inf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:46:34.819026+00:00
-- url     : https://prove2.me/submissions/e15aa145-0a23-4c30-bc1c-5ec9d9370544

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqZeroOfForallPowDvdGerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueZpowMulAppLE

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u v
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.PrimeSection
namespace GlobalTheory.PrimeSection
theorem _root_.solution {X Y : Scheme.{u}} {j : Y ⟶ X} [IsOpenImmersion j] {D U : X.Opens}
    (hj : j.opensRange = D) {W : Y.Opens} (h : W = j ⁻¹ᵁ U) : W = j ⁻¹ᵁ (U ⊓ D) := by
  subst h hj
  exact le_antisymm (fun y hy ↦ ⟨hy, y, rfl⟩) fun y hy ↦ hy.1
end GlobalTheory.PrimeSection
