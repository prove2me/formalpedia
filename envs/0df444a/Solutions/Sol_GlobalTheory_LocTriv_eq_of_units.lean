-- Prove2me | solution 1 for GlobalTheory.LocTriv.eq_of_units
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:23:42.161038+00:00
-- url     : https://prove2.me/submissions/ab3fc073-379c-4a06-afe4-fcd1784ed367

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorusStableAffineOpenFunctionsWeightGradedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LocallyTrivialTorusQuotientFlatSurjectiveCosets
import Theorems.Thm_GlobalTheory_LocTriv_stable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.LocTriv
variable {S : Scheme.{0}}
variable {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] {i : splitTorus S X ⟶ G} {q : G ⟶ B}
namespace GlobalTheory.LocTriv
theorem _root_.solution {U : G.left.Opens}
    (hU : (snd (splitTorus _ X) G).left ⁻¹ᵁ U ≤ ((fst (splitTorus _ X) G ≫ i) * snd _ G).left ⁻¹ᵁ U)
    (u : X → Γ(G.left, U)ˣ) (hu : ∀ χ, IsWt i U (u χ).val χ)
    {Z : Over S} {t t' : Z ⟶ splitTorus S X} {g : Z ⟶ G} (hg : ⊤ ≤ g.left ⁻¹ᵁ U) (h : t ≫ i = t' ≫ i) : t = t' :=  by
  have h₁ := stable hU t hg
  have h₁' := stable hU t' hg
  have e3 : ∀ (s s' : Z ⟶ G) (hs : ⊤ ≤ s.left ⁻¹ᵁ U) (hs' : ⊤ ≤ s'.left ⁻¹ᵁ U), s = s' →
      s.left.appLE U ⊤ hs = s'.left.appLE U ⊤ hs' := by
    rintro s _ hs hs' rfl; rfl
  have key : ∀ χ, chV t χ = chV t' χ := by
    intro χ
    have e1 := hu χ Z t g h₁ hg
    have e2 := hu χ Z t' g h₁' hg
    rw [e3 _ _ h₁ h₁' (by rw [h])] at e1
    rw [e1] at e2
    have hunit : IsUnit ((g.left.appLE U ⊤ hg).hom (u χ).val) := (u χ).isUnit.map _
    apply Units.ext
    rw [chV_val, chV_val]
    exact hunit.mul_right_cancel e2
  apply (splitTorusPointsEquiv S X Z).injective
  refine MonoidHom.ext fun m => ?_
  exact key (Multiplicative.toAdd m)
end GlobalTheory.LocTriv
