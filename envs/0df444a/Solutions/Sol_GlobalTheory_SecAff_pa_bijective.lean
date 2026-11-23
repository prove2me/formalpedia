-- Prove2me | solution 1 for GlobalTheory.SecAff.pa_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:45.940341+00:00
-- url     : https://prove2.me/submissions/4c8e377a-6a4b-4681-9388-40980b47735a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SecAff
variable {X X' X'' : Scheme.{0}}
namespace GlobalTheory.SecAff
theorem _root_.solution (φ : X' ⟶ X) [IsOpenImmersion φ] {U : X.Opens} {V : X'.Opens}
    (h : V ≤ φ ⁻¹ᵁ U) (h' : φ ⁻¹ᵁ U ≤ V) (hU : U ≤ φ.opensRange) :
    Function.Bijective (pa φ h) := by
  obtain rfl : V = φ ⁻¹ᵁ U := le_antisymm h h'
  have := φ.isIso_app U hU
  have e : pa φ h = (φ.app U).hom := by rw [Scheme.Hom.app_eq_appLE]; rfl
  rw [e]
  exact ConcreteCategory.bijective_of_isIso (φ.app U)
end GlobalTheory.SecAff
