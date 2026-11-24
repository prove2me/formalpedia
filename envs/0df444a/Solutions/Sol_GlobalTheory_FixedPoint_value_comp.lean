-- Prove2me | solution 1 for GlobalTheory.FixedPoint.value_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:08:04.415938+00:00
-- url     : https://prove2.me/submissions/812425fc-ae84-4d79-94ff-36b9f3d077ab

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
theorem _root_.solution {A B : CommRingCat.{u}} (g : A ⟶ B) {Z : Scheme.{u}} (y : Spec A ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map g ≫ y) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    (Scheme.ΓSpecIso B).hom ((Spec.map g ≫ y).appLE U ⊤ h' f) =
      g ((Scheme.ΓSpecIso A).hom (y.appLE U ⊤ h f)) := by
  have : (Spec.map g ≫ y).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso B).hom =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso A).hom ≫ g := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  exact congr(($this).hom f)
end GlobalTheory.FixedPoint
