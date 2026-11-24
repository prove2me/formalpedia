-- Prove2me | solution 1 for GlobalTheory.FixedPoint.top_le_preimage_comp_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:03.429802+00:00
-- url     : https://prove2.me/submissions/e53c8e98-1514-4bc7-b7dc-fee98941870f

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
theorem _root_.solution {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (specAlg(K₀, K₁) ≫ y) ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ U := by
  refine ⟨fun h p _ => ?_, fun h p _ => h (Set.mem_univ (specAlg(K₀, K₁) p))⟩
  have h' := h (Set.mem_univ (IsLocalRing.closedPoint K₁))
  rw [Subsingleton.elim p (specAlg(K₀, K₁) (IsLocalRing.closedPoint K₁))]
  exact h'
end GlobalTheory.FixedPoint
