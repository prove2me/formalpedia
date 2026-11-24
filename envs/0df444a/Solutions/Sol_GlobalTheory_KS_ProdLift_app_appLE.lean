-- Prove2me | solution 1 for GlobalTheory.KS.ProdLift.app_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:27:13.387026+00:00
-- url     : https://prove2.me/submissions/e9d8d786-a632-4ce7-95d5-3f050ac59b2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLocalDerivationAlongFibreFieldOfAffiStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDerOfIsPushout

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
theorem _root_.solution {Z Z₀ X Y : Scheme.{0}} {p : Z ⟶ X} {p₀ : Z₀ ⟶ Y} {m : Y ⟶ X} {m₂ : Z₀ ⟶ Z}
    (hp : m₂ ≫ p = p₀ ≫ m) {W : X.Opens} {Q : Z.Opens} (h : Q ≤ p ⁻¹ᵁ W)
    (h' : m₂ ⁻¹ᵁ Q ≤ p₀ ⁻¹ᵁ m ⁻¹ᵁ W) (f : Γ(X, W)) :
    (m₂.app Q).hom ((p.appLE W Q h).hom f) = (p₀.appLE _ _ h').hom ((m.app W).hom f) := by
  have key : ∀ (g g' : Z₀ ⟶ X) (e : g = g') (h₁ : m₂ ⁻¹ᵁ Q ≤ g ⁻¹ᵁ W) (h₂ : m₂ ⁻¹ᵁ Q ≤ g' ⁻¹ᵁ W),
      (g.appLE W (m₂ ⁻¹ᵁ Q) h₁).hom f = (g'.appLE W (m₂ ⁻¹ᵁ Q) h₂).hom f := by
    rintro g _ rfl _ _
    rfl
  have e₁ := Scheme.Hom.appLE_comp_appLE m₂ p W Q (m₂ ⁻¹ᵁ Q) h le_rfl
  have e₂ := Scheme.Hom.appLE_comp_appLE p₀ m W (m ⁻¹ᵁ W) (m₂ ⁻¹ᵁ Q) le_rfl h'
  rw [Scheme.Hom.app_eq_appLE m₂, Scheme.Hom.app_eq_appLE m]
  have l₁ := congrArg (fun g => g.hom f) e₁
  have l₂ := congrArg (fun g => g.hom f) e₂
  simp only [CommRingCat.comp_apply] at l₁ l₂
  rw [l₁, l₂]
  exact key _ _ hp _ _
end GlobalTheory.KS.ProdLift
