-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.psi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:57:41.181019+00:00
-- url     : https://prove2.me/submissions/e0ff1ed9-f533-4faf-a992-d224800c3a12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMorK
variable {K : Type} [Field K] {Y Y' : Scheme.{0}} {q : Y ⟶ Sp K} (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y)
  {R : Type} [CommRing R] {D : R → K} {X : Scheme.{0}} {p : X ⟶ Sp R} {m : Y ⟶ X}
  {d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)}
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution (hd : LocDerK q p m D ⊤ d) (W : X.Opens) (f : Γ(X, W)) :
    (psi π ρ hd W f : Γ(Y', ρ ⁻¹ᵁ m ⁻¹ᵁ W)) = (ρ.app (m ⁻¹ᵁ W)).hom ((m.app W).hom f) +
    constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ W) DualNumber.eps * (ρ.app (m ⁻¹ᵁ W)).hom (d W f) := rfl
end GlobalTheory.KS.DerMorK
