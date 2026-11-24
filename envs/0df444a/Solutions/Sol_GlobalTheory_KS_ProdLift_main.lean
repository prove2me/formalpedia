-- Prove2me | solution 1 for GlobalTheory.KS.ProdLift.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:00:45.757077+00:00
-- url     : https://prove2.me/submissions/2f65d0f5-3546-4453-bb8f-3f8f0be5b332

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout
import Theorems.Thm_GlobalTheory_KS_ProdLift_finiteRing_sq_sub_mul_sq_eq_of_card

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
noncomputable section
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.ProdLift
namespace GlobalTheory.KS.ProdLift
theorem _root_.solution : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (x₀ : R →+* K) (A : Over (Sp R)) (A₀ : Over (Sp K)) (m : A₀.left ⟶ A.left) (m₂ : (A₀ ⊗ A₀).left ⟶ (A ⊗ A).left) (D : R → K) (W W' : A.left.Opens), m ≫ A.hom = A₀.hom ≫ spMap x₀ → IsSquare m m₂ → IsAffineOpen W → IsAffineOpen W' → ∀ Q, Q = (fst A A).left ⁻¹ᵁ W ⊓ (snd A A).left ⁻¹ᵁ W' → (∀ d d', LocDerK A₀.hom A.hom m D W d → LocDerK A₀.hom A.hom m D W' d' → ∃ d₂, LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ ∧ (∀ f, d₂ Q (pbT (fst A A).left f Q) = pbT (fst A₀ A₀).left (d W f) _) ∧ ∀ f, d₂ Q (pbT (snd A A).left f Q) = pbT (snd A₀ A₀).left (d' W' f) _) ∧ ∀ d₂ d₂', LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂ → LocDerK (A₀ ⊗ A₀).hom (A ⊗ A).hom m₂ D Q d₂' → (∀ f : Γ(A.left, W), d₂ Q (pbT (fst A A).left f Q) = d₂' Q (pbT (fst A A).left f Q)) → (∀ f : Γ(A.left, W'), d₂ Q (pbT (snd A A).left f Q) = d₂' Q (pbT (snd A A).left f Q)) → ∀ O, O ≤ Q → d₂ O = d₂' O := by
  intro K _ R _ x₀ A A₀ m m₂ D W W' _ hsq hW hW' Q hQ
  obtain ⟨hs₁, hs₂⟩ := hsq
  exact finiteRing_sq_sub_mul_sq_eq_of_card (Over.isPullback_of_binaryFan_isLimit _
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct A A))
    (Over.w (fst A A)) (Over.w (fst A₀ A₀)) (Over.w (snd A₀ A₀)) hs₁ hs₂ D hW hW' Q hQ
end GlobalTheory.KS.ProdLift
