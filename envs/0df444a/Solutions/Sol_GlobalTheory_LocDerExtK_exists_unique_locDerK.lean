-- Prove2me | solution 1 for GlobalTheory.LocDerExtK.exists_unique_locDerK
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:46:50.987589+00:00
-- url     : https://prove2.me/submissions/67b81e02-8152-4c4d-811d-d9c435da2afa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLocalDerivationExtensionOfAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffi
import Theorems.Thm_GlobalTheory_LocDerExtK_exists_locDerK
import Theorems.Thm_GlobalTheory_LocDerExtK_locDerK_unique

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
open GlobalTheory GlobalTheory.LocDerExtK
open GlobalTheory.LocDerExt
namespace GlobalTheory.LocDerExtK
theorem _root_.solution : ∀ (K : Type) [Field K] (R : Type) [CommRing R] (Y X : Scheme.{0}) (q : Y ⟶ Sp K) (p : X ⟶ Sp R) (m : Y ⟶ X) (D : R → K) (W₀ : X.Opens), IsAffineOpen W₀ → (∀ d₀ : Γ(X, W₀) → Γ(Y, m ⁻¹ᵁ W₀), (∀ a b, d₀ (a + b) = d₀ a + d₀ b) → (∀ a b, d₀ (a * b) = (m.app W₀).hom a * d₀ b + (m.app W₀).hom b * d₀ a) → (∀ r, d₀ (constFn p W₀ r) = constFn q (m ⁻¹ᵁ W₀) (D r)) → ∃ d, LocDerK q p m D W₀ d ∧ d W₀ = d₀) ∧ ∀ d d', LocDerK q p m D W₀ d → LocDerK q p m D W₀ d' → d W₀ = d' W₀ → ∀ W, W ≤ W₀ → d W = d' W :=
  fun K _ R _ Y X q p m D W₀ hW =>
    ⟨exists_locDerK K R Y X q p m D W₀ hW, fun d d' h h' e W hle => locDerK_unique hW d d' h h' e W hle⟩
end GlobalTheory.LocDerExtK
