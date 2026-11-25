-- Prove2me | solution 1 for GlobalTheory.FixedPoint.exists_factor_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:47:25.586259+00:00
-- url     : https://prove2.me/submissions/5e77398a-9ce7-4692-be54-b798c4ab2949

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsRingEquivOfIsTranscendenceBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsUniqueFactorOfIsAlgClosed
import Theorems.Thm_GlobalTheory_FixedPoint_fixed_of_factor
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
    (x : Spec (.of K₁) ⟶ Z) :
    (∃ y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ↔ ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x :=
  ⟨fun ⟨y, hy⟩ s => hy ▸ fixed_of_factor y s, fun h => (existsUnique_factor x h).exists⟩
end GlobalTheory.FixedPoint
