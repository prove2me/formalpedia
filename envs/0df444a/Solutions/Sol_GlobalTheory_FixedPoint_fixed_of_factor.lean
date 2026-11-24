-- Prove2me | solution 1 for GlobalTheory.FixedPoint.fixed_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:02.663927+00:00
-- url     : https://prove2.me/submissions/ea975afa-5a18-446e-a1ab-cf103369dde9

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
theorem _root_.solution {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (s : L ≃ₐ[K₀] L) :
    Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y =
      specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y := by
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext a
  simp [← IsScalarTower.algebraMap_apply]
end GlobalTheory.FixedPoint
