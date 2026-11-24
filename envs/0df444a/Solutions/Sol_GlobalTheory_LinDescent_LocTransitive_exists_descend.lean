-- Prove2me | solution 1 for GlobalTheory.LinDescent.LocTransitive.exists_descend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:46:37.766795+00:00
-- url     : https://prove2.me/submissions/a4cd8956-6e21-40dc-8d5c-8491eb015372

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueDescendOfTorsionInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoIffBijectiveOverAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Theorems.Thm_GlobalTheory_LinDescent_gs_appLE
import Theorems.Thm_GlobalTheory_LinDescent_gs_comp
import Theorems.Thm_GlobalTheory_FunDescent_exists_app_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
variable {L : LB X} {C : Type} {t : C → (X ⟶ X)} {π : X ⟶ Y}
namespace GlobalTheory.LinDescent
namespace LocTransitive
theorem _root_.solution [Flat π] [Surjective π] [QuasiCompact π]
    (h : LocTransitive t π) (V : Y.Opens) (f : Γ(X, π ⁻¹ᵁ V))
    (hf : ∀ c (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ t c) z _ f = gs r z _ f) :
    ∃ a : Γ(Y, V), ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z), r z ∈ π ⁻¹ᵁ V →
      gs (r ≫ π) z V a = gs r z _ f := by
  obtain ⟨a, rfl⟩ := FunDescent.exists_app_eq π V f fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z hz => by
    rw [gs_appLE (𝟙 Z) g₁ z _ _ _ hz, gs_appLE (𝟙 Z) g₂ z _ _ _ hz, Category.id_comp,
      Category.id_comp]
    obtain ⟨c, Z', a, _, z', rfl, h'⟩ := h Z g₁ g₂ e z
    apply (ConcreteCategory.bijective_of_isIso (a.stalkMap z')).1
    refine (gs_comp a g₁ z' _ (h₁ hz) f).symm.trans (Eq.trans ?_ (gs_comp a g₂ z' _ (h₂ hz) f))
    rw [h']
    exact hf c Z' (a ≫ g₂) z' (h₂ hz)
  exact ⟨a, fun Z r z hz => (gs_pull r π z V hz a).symm⟩
end LocTransitive
end GlobalTheory.LinDescent
