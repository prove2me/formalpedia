-- Prove2me | solution 1 for GlobalTheory.FixedPoint.existsUnique_factor_of_isAlgClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:42:31.324438+00:00
-- url     : https://prove2.me/submissions/44c012d5-c639-4168-8db8-26e7bde1be2c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_existsUnique_factor

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
theorem _root_.solution [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of L) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L, Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ x = x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, L) ≫ y = x :=
  existsUnique_factor (L := L) x fun s => by simpa using hx s
end GlobalTheory.FixedPoint
