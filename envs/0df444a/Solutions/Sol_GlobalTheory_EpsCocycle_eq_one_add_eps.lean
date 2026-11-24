-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.eq_one_add_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:26:26.261896+00:00
-- url     : https://prove2.me/submissions/a614af53-c114-412b-af66-29813f57ebaf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
import Theorems.Thm_GlobalTheory_EpsCocycle_appLE_section
import Theorems.Thm_GlobalTheory_EpsCocycle_appLE_constFn_eps
import Theorems.Thm_GlobalTheory_EpsThick_thickening_functions


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
open GlobalTheory GlobalTheory.EpsCocycle
noncomputable section
namespace GlobalTheory.EpsCocycle
theorem _root_.solution {Y Y' : Scheme.{0}} {q : Y ⟶ Sp ℂ} {π : Y' ⟶ Sp (DualNumber ℂ)} {ρ : Y' ⟶ Y}
    {j : Y ⟶ Y'} (hp : IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ)))) (hj : j ≫ ρ = 𝟙 Y)
    (hq : j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom)) (O' : Y'.Opens)
    (F : Γ(Y', O')) (hF : (j.appLE O' _ le_rfl).hom F = 1) :
    ∃ k : Γ(Y, j ⁻¹ᵁ O'), ∀ h : O' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ O'),
      F = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom k := by
  obtain ⟨h₁, -, h₃⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have key : ∀ (O : Y.Opens) (O' : Y'.Opens) (_ : ρ ⁻¹ᵁ O = O') (F : Γ(Y', O')), ∃ a b : Γ(Y, O),
      ∀ h : O' ≤ ρ ⁻¹ᵁ O,
        F = (ρ.appLE _ _ h).hom a + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom b := by
    intro O O' e F
    subst e
    obtain ⟨ab, hab, -⟩ := h₃ O F
    refine ⟨ab.1, ab.2, fun h => ?_⟩
    rw [Scheme.Hom.appLE_eq_app]
    exact hab
  obtain ⟨a, b, hab⟩ := key _ O' (h₁ O') F
  refine ⟨b, fun h => ?_⟩
  have ha : a = 1 := by
    rw [hab h, map_add, map_mul, appLE_constFn_eps hq, zero_mul, add_zero,
      appLE_section hj h le_rfl le_rfl] at hF
    have e : resG Y (le_refl (j ⁻¹ᵁ O')) a = a := by
      change (Y.presheaf.map (𝟙 _)).hom a = a
      rw [Y.presheaf.map_id]
      rfl
    exact e.symm.trans hF
  rw [hab h, ha, map_one]
end GlobalTheory.EpsCocycle
