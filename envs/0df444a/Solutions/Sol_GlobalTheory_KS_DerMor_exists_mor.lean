-- Prove2me | solution 1 for GlobalTheory.KS.DerMor.exists_mor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:46:51.733688+00:00
-- url     : https://prove2.me/submissions/f815c03b-e268-44af-b4d0-f81155346024

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsSymm
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomFromConstThickeningOfDerivation
import Theorems.Thm_GlobalTheory_KS_DerMor_deform_app
import Theorems.Thm_GlobalTheory_KS_DerMor_cH_eq
import Theorems.Thm_GlobalTheory_KS_DerMor_appLE_cH
import Theorems.Thm_GlobalTheory_KS_DerMor_app_cH
import Theorems.Thm_GlobalTheory_KS_DerMor_res_cH
import Theorems.Thm_GlobalTheory_KS_DerMor_cH_spMap
import Theorems.Thm_GlobalTheory_KS_DerMor_res_app
import Theorems.Thm_GlobalTheory_KS_DerMor_appLE_app_of_section
import Theorems.Thm_GlobalTheory_KS_DerMor_ext_cH

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
open GlobalTheory GlobalTheory.KS GlobalTheory.KS.DerMor
namespace GlobalTheory.KS.DerMor
theorem _root_.solution : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber ℂ) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ≫ spMap xD → LocDer q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD := by
  intro Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hmp hd
  have hee : ∀ V : Y'.Opens, cH π V DualNumber.eps * cH π V DualNumber.eps = 0 := by
    intro V
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero]
  let c : ∀ W : X.Opens, Γ(X, W) →+* Γ(Y', (ρ ≫ m) ⁻¹ᵁ W) := fun W =>
    pert (m.app W).hom (ρ.app (m ⁻¹ᵁ W)).hom (cH π _ DualNumber.eps) (hee _) (d W)
      (hd.add W le_top) (hd.mul W le_top)
  have hres : ∀ W W' (h : W' ≤ W) f,
      c W' (resG X h f) = resG Y' (fun _ hy => h hy) (c W f) := by
    intro W W' h f
    show (ρ.app _).hom ((m.app W').hom (resG X h f)) +
        cH π _ DualNumber.eps * (ρ.app _).hom (d W' (resG X h f)) =
      resG Y' _ ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f))
    have h1 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (res_app m h f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) ((m.app W).hom f))
    have h2 := (congrArg (ρ.app (m ⁻¹ᵁ W')).hom (hd.res W W' h le_top f)).trans
      (res_app ρ (U := m ⁻¹ᵁ W) (V := m ⁻¹ᵁ W') (fun _ hy => h hy) (d W f))
    have h3 := (res_cH π (U := ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) (V := ρ ⁻¹ᵁ (m ⁻¹ᵁ W')) (fun _ hy => h hy)
      DualNumber.eps).symm
    rw [map_add, map_mul]
    exact congrArg₂ (· + ·) h1 (congrArg₂ (· * ·) h3 h2)
  have hnil : ∀ W f, IsNilpotent (c W f - ((ρ ≫ m).app W).hom f) := by
    intro W f
    refine ⟨2, ?_⟩
    show ((ρ.app _).hom ((m.app W).hom f) + cH π _ DualNumber.eps * (ρ.app _).hom (d W f) -
      (ρ.app _).hom ((m.app W).hom f)) ^ 2 = 0
    rw [add_sub_cancel_left, mul_pow, sq (cH π _ _), hee, zero_mul]
  have hdual : ∀ x : DualNumber ℂ,
      algebraMap ℂ (DualNumber ℂ) x.fst + DualNumber.eps * algebraMap ℂ (DualNumber ℂ) x.snd = x := by
    intro x
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have hfst : ∀ z : DualNumber ℂ, (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom z = z.fst := fun z => rfl
  have hq : ∀ (V : Y.Opens) (z : ℂ),
      (ρ.app V).hom (cH q V z) = cH π (ρ ⁻¹ᵁ V) (algebraMap ℂ (DualNumber ℂ) z) := by
    intro V z
    rw [app_cH, hpb.w, cH_spMap]
  have hc : ∀ W (r : R), c W (cH p W r) = cH π ((ρ ≫ m) ⁻¹ᵁ W) (xD r) := by
    intro W r
    show (ρ.app _).hom ((m.app W).hom (cH p W r)) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d W (cH p W r)) = _
    rw [← cH_eq p W r, hd.base W le_top r]
    simp only [cH_eq]
    rw [app_cH, hmp, ← Category.assoc, cH_spMap, cH_spMap, hq, hq, ← map_mul, ← map_add, hfst,
      hdual]
    rfl
  refine ⟨deform (ρ ≫ m) c hres hnil, ?_, ?_⟩
  · have hb : (j ≫ deform (ρ ≫ m) c hres hnil).base = m.base := by
      show (j ≫ ρ ≫ m).base = m.base
      rw [← Category.assoc, hjρ, Category.id_comp]
    refine Scheme.Hom.ext hb ?_
    intro U
    have hle : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) := by
      intro x hx
      have hx' : (j ≫ ρ) x = x := by rw [hjρ]; rfl
      show (j ≫ ρ) x ∈ m ⁻¹ᵁ U
      rw [hx']
      exact hx
    apply CommRingCat.hom_ext
    ext f
    change (j.appLE (ρ ⁻¹ᵁ (m ⁻¹ᵁ U)) (m ⁻¹ᵁ U) hle).hom
      (((deform (ρ ≫ m) c hres hnil).app U).hom f) = _
    rw [deform_app]
    show (j.appLE _ _ hle).hom ((ρ.app _).hom ((m.app U).hom f) +
      cH π _ DualNumber.eps * (ρ.app _).hom (d U f)) = _
    rw [map_add, map_mul, appLE_app_of_section ρ j hjρ _ hle, appLE_cH, hjπ, cH_spMap, hfst]
    simp
  · apply ext_cH
    intro r
    rw [cH_spMap]
    have e1 := app_cH p (deform (ρ ≫ m) c hres hnil) ⊤ r
    rw [deform_app] at e1
    have e2 := res_cH (deform (ρ ≫ m) c hres hnil ≫ p)
      (U := (deform (ρ ≫ m) c hres hnil) ⁻¹ᵁ ⊤) (V := ⊤) le_top r
    rw [← e2, ← e1]
    show resG Y' _ (c ⊤ (cH p ⊤ r)) = _
    rw [hc]
    exact res_cH π _ _
end GlobalTheory.KS.DerMor
