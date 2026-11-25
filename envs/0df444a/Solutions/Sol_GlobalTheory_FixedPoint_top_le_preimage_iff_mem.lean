-- Prove2me | solution 1 for GlobalTheory.FixedPoint.top_le_preimage_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:27.665958+00:00
-- url     : https://prove2.me/submissions/78da3931-c1f8-4259-b8c6-5499e39ad312

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry
open GlobalTheory GlobalTheory.FixedPoint
universe u v w
local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))
variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]
namespace GlobalTheory.FixedPoint
theorem _root_.solution {Z : Scheme.{u}} (x : Spec (.of K₁) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint K₁) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ (IsLocalRing.closedPoint K₁)), fun h p _ => ?_⟩
  rw [Subsingleton.elim p (IsLocalRing.closedPoint K₁)]
  exact h
end GlobalTheory.FixedPoint
