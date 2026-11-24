-- Prove2me | solution 1 for GlobalTheory.KS.EpsBundle.trivial_iff_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:42:43.481602+00:00
-- url     : https://prove2.me/submissions/13dfa941-a03e-4de4-90ea-7105eddb90c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ConstThickeningComplexFunctionsStructureStatement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TrivialIffCoboundary
import Theorems.Thm_P2M_GlobalTheory_KS_EpsBundle_res_constFn__b3f7b6fcb762
import Theorems.Thm_GlobalTheory_KS_EpsBundle_res_appLE
import Theorems.Thm_GlobalTheory_KS_EpsBundle_eps_sq
import Theorems.Thm_GlobalTheory_KS_EpsBundle_decomp
import Theorems.Thm_GlobalTheory_KS_EpsBundle_unit_form
import Theorems.Thm_GlobalTheory_KS_EpsBundle_overlap
import Theorems.Thm_GlobalTheory_T_const_thickening_complex_functions_structure


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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.EpsBundle
namespace GlobalTheory.KS.EpsBundle
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (Q : LB Y') (k : ∀ i i', Γ(Y, j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), Q.IsLB → (∀ i i' (h : Q.U i ⊓ Q.U i' ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ (Q.U i ⊓ Q.U i'))), (Q.g i i').val = 1 + constFn π _ DualNumber.eps * (ρ.appLE _ _ h).hom (k i i')) → ((∃ t : Q.Gen, t.IsGen) ↔ ∃ a : ∀ i, Γ(Y, j ⁻¹ᵁ Q.U i), ∀ i i', k i i' = resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i from fun _ hy => hy.1) (a i) - resG Y (show j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' from fun _ hy => hy.2) (a i')) := by
  intro Y Y' q π ρ j hp hj hq Q k _ hg
  obtain ⟨hO, -, hD⟩ := GlobalTheory.T.const_thickening_complex_functions_structure Y Y' q π ρ j hp hj hq
  have le : ∀ W : Y'.Opens, W ≤ ρ ⁻¹ᵁ (j ⁻¹ᵁ W) := fun W => (hO W).ge
  have H : ∀ (W : Y'.Opens) (F : Γ(Y', W)), ∃! ab : Γ(Y, j ⁻¹ᵁ W) × Γ(Y, j ⁻¹ᵁ W),
      F = (ρ.appLE _ W (le W)).hom ab.1 + constFn π _ DualNumber.eps * (ρ.appLE _ W (le W)).hom ab.2 :=
    fun W F => decomp π ρ _ (hD _) W (hO W) (le W) F
  constructor
  · rintro ⟨t, ht⟩
    choose b b' c hb hs using fun i =>
      unit_form (ρ.appLE _ (Q.U i) (le _)).hom _ (eps_sq π _) (H (Q.U i)) (t.s i)
    refine ⟨fun i => c i * b' i, fun i i' => ?_⟩
    have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
    have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
    have E : resG Y' inf_le_left (t.s i : Γ(Y', Q.U i)) =
        (Q.g i i').val * resG Y' inf_le_right (t.s i' : Γ(Y', Q.U i')) := congrArg Units.val (ht i i')
    rw [hg i i' (le _), hs, hs, map_add, map_add, map_mul, map_mul, res_constFn', res_constFn',
      res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _),
      res_appLE ρ _ l₂ _ (le _)] at E
    rw [map_mul, map_mul]
    exact overlap _ _ (eps_sq π _) (H _) (by rw [← map_mul, hb, map_one])
      (by rw [← map_mul, hb, map_one]) E
  · rintro ⟨a, ha⟩
    refine ⟨⟨fun i => ⟨1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i),
      1 - constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i), ?_, ?_⟩⟩, fun i i' => ?_⟩
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · linear_combination (-((ρ.appLE _ (Q.U i) (le _)).hom (a i)) ^ 2) * eps_sq π (Q.U i)
    · have l₁ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i := fun _ hy => hy.1
      have l₂ : j ⁻¹ᵁ (Q.U i ⊓ Q.U i') ≤ j ⁻¹ᵁ Q.U i' := fun _ hy => hy.2
      apply Units.ext
      change resG Y' inf_le_left (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i) (le _)).hom (a i)) =
        (Q.g i i').val * resG Y' inf_le_right
          (1 + constFn π _ DualNumber.eps * (ρ.appLE _ (Q.U i') (le _)).hom (a i'))
      rw [hg i i' (le _), map_add, map_add, map_mul, map_mul, map_one, map_one, res_constFn', res_constFn',
        res_appLE ρ _ l₁ _ (le _), res_appLE ρ _ l₂ _ (le _), ha i i', map_sub]
      linear_combination (-((ρ.appLE _ _ (le _)).hom (resG Y l₁ (a i)) -
        (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) * (ρ.appLE _ _ (le _)).hom (resG Y l₂ (a i'))) *
        eps_sq π (Q.U i ⊓ Q.U i')
end GlobalTheory.KS.EpsBundle
