-- Prove2me | solution 1 for GlobalTheory.EpsCocycle.exists_cocycle_one_add_eps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:05:09.467865+00:00
-- url     : https://prove2.me/submissions/d57a904d-5fba-4868-980e-1abe2e23081f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsLineBundleCocycleOneAddEps
import Theorems.Thm_GlobalTheory_EpsCocycle_res_res
import Theorems.Thm_GlobalTheory_EpsCocycle_regauge_isLB
import Theorems.Thm_GlobalTheory_EpsCocycle_regauge_iso
import Theorems.Thm_GlobalTheory_EpsCocycle_eq_one_add_eps
import Theorems.Thm_GlobalTheory_EpsCocycle_pullLE_eq
import Theorems.Thm_GlobalTheory_EpsCocycle_pullLE_res
import Theorems.Thm_GlobalTheory_EpsCocycle_pullLE_section
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
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ Q : LB Y', Q.IsLB → (∃ t : (Q.pull j).Gen, t.IsGen) → ∃ (Q' : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), Q'.IsLB ∧ LBIso Q Q' ∧ (∀ i i' (h : Q'.U i ⊓ Q'.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q'.U i ⊓ Q'.U i'))), (Q'.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) := by
  intro Y Y' q π ρ j hp hj hq Q hQ ⟨t, ht⟩
  obtain ⟨h₁, -, -⟩ := GlobalTheory.EpsThick.thickening_functions Y Y' q π ρ j hp hj hq
  have hw : ∀ i : Q.ι, j ⁻¹ᵁ Q.U i ≤ (Q.pull j).U (fun _ => i) :=
    fun i _ hy => Set.mem_iInter.2 fun _ => hy
  let s : ∀ i : Q.ι, Γ(Y, j ⁻¹ᵁ Q.U i)ˣ := fun i => res (hw i) (t.s fun _ => i)
  let u : ∀ i, Γ(Y', Q.U i)ˣ := fun i => pullLE ρ (h₁ (Q.U i)).ge (s i)
  have main : ∀ i i' : Q.ι, (j.appLE (Q.U i ⊓ Q.U i') _ le_rfl).hom ((regauge Q u).g i i').val = 1 := by
    intro i i'
    have hl : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have hr : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have e := congrArg (res (le_inf (hl.trans (hw i)) (hr.trans (hw i'))))
      (ht (fun _ => i) (fun _ => i'))
    have eg : res (le_inf (hl.trans (hw i)) (hr.trans (hw i')))
        ((Q.pull j).g (fun _ => i) (fun _ => i')) =
        pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))) (Q.g i i') := by
      rw [pullLE_eq]
      change res _ (∏ _k : PUnit.{1}, (res _ (pullU j _ (Q.g i i'))) ^ (1 : ℤ)) = _
      rw [Fintype.prod_unique, zpow_one]
      exact res_res _ _ _
    rw [map_mul, res_res, res_res, eg] at e
    have : pullLE j (le_refl (j ⁻¹ᵁ (Q.U i ⊓ Q.U i')))
        ((res inf_le_left (u i))⁻¹ * Q.g i i' * res inf_le_right (u i')) = 1 := by
      rw [map_mul, map_mul, map_inv, pullLE_res j _ _ hl, pullLE_res j _ _ hr,
        pullLE_section hj _ _ hl, pullLE_section hj _ _ hr, res_res, res_res, _root_.mul_assoc, ← e,
        inv_mul_cancel]
    exact congrArg Units.val this
  choose k hk using fun i i' : Q.ι => eq_one_add_eps hp hj hq _ _ (main i i')
  exact ⟨regauge Q u, k, regauge_isLB hQ u, regauge_iso hQ u, hk⟩
end GlobalTheory.EpsCocycle
