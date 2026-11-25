-- Prove2me | solution 1 for GlobalTheory.RigidFunction.not_mem_basicOpen_fibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:42.043455+00:00
-- url     : https://prove2.me/submissions/f7ef0528-921c-41f2-bace-c67df74e6f24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqOneOfAppLESectionEqOne

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
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.RigidFunction
namespace GlobalTheory.RigidFunction
theorem _root_.solution {X P F : Scheme.{0}} {K : Type} [Field K] {p : P ⟶ X}
    {t : Spec (CommRingCat.of K) ⟶ X} {φ : F ⟶ P} {q : F ⟶ Spec (CommRingCat.of K)} (w : φ ≫ p = q ≫ t)
    [IsIntegral F] [UniversallyClosed q] (V : X.Opens) (hV : ∀ x, t x ∈ V) (s : Γ(P, p ⁻¹ᵁ V)) (a b : F)
    (ha : φ a ∉ P.basicOpen s) : φ b ∉ P.basicOpen s := by
  have hle : (⊤ : F.Opens) ≤ φ ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    intro c _
    change p (φ c) ∈ V
    rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
    exact hV _
  have key : ∀ c : F, φ c ∈ P.basicOpen s ↔ c ∈ F.basicOpen ((φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s) := by
    intro c
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩
  rw [key] at ha ⊢
  have hF := isField_of_universallyClosed K q
  by_cases hs : (φ.appLE (p ⁻¹ᵁ V) ⊤ hle).hom s = 0
  · rw [hs, Scheme.basicOpen_zero]
    exact fun h => h
  · exfalso
    apply ha
    obtain ⟨v, hv⟩ := hF.mul_inv_cancel hs
    rw [Scheme.basicOpen_of_isUnit _ (isUnit_iff_exists_inv.mpr ⟨v, hv⟩)]
    trivial
end GlobalTheory.RigidFunction
