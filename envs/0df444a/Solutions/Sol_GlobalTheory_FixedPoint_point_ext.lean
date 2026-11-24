-- Prove2me | solution 1 for GlobalTheory.FixedPoint.point_ext
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:27:09.496498+00:00
-- url     : https://prove2.me/submissions/6f16298f-9659-4bf8-b063-c4c0834f3e9a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_epi_specAlg

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
theorem _root_.solution {Z : Scheme.{u}} {y y' : Spec (.of K₀) ⟶ Z}
    (h : specAlg(K₀, K₁) ≫ y = specAlg(K₀, K₁) ≫ y') : y = y' :=
  have := epi_specAlg (K₀ := K₀) (K₁ := K₁)
  (cancel_epi _).mp h
end GlobalTheory.FixedPoint
