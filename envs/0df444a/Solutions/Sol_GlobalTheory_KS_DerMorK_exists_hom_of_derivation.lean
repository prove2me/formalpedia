-- Prove2me | solution 1 for GlobalTheory.KS.DerMorK.exists_hom_of_derivation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:59:27.54656+00:00
-- url     : https://prove2.me/submissions/6f3ee8b1-1ee7-49c3-9764-2ade41f798b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsHomOfDerivation
import Theorems.Thm_GlobalTheory_KS_DerMorK_hom_ext_appLE
import Theorems.Thm_GlobalTheory_KS_DerMorK_appLE_constFn
import Theorems.Thm_GlobalTheory_KS_DerMorK_app_constFn
import Theorems.Thm_GlobalTheory_KS_DerMorK_constFn_spMap
import Theorems.Thm_GlobalTheory_KS_DerMorK_pbT_eq_app
import Theorems.Thm_GlobalTheory_KS_DerMorK_psi_nat
import Theorems.Thm_GlobalTheory_KS_DerMorK_psi_nil

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
namespace GlobalTheory.KS.DerMorK
theorem _root_.solution : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → ∀ (R : Type) [CommRing R] (xD : R →+* DualNumber K) (X : Scheme.{0}) (p : X ⟶ Sp R) (m : Y ⟶ X) (d : ∀ W : X.Opens, Γ(X, W) → Γ(Y, m ⁻¹ᵁ W)), m ≫ p = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ≫ spMap xD → LocDerK q p m (fun r => (xD r).snd) ⊤ d → ∃ Φ : Y' ⟶ X, j ≫ Φ = m ∧ Φ ≫ p = π ≫ spMap xD ∧ ∀ (W : X.Opens) (f : Γ(X, W)), pbT Φ f (ρ ⁻¹ᵁ (m ⁻¹ᵁ W)) = pbT (ρ ≫ m) f _ + constFn π _ DualNumber.eps * pbT ρ (d W f) _ := by
  intro K _ Y Y' q π ρ j hpb hjρ hjπ R _ xD X p m d hm hd
  let Φ := deformHom (ρ ≫ m) (psi π ρ hd) (psi_nat π ρ hd) (psi_nil π ρ hd)
  have hjm : j ≫ ρ ≫ m = m := by rw [← Category.assoc, hjρ, Category.id_comp]
  refine ⟨Φ, ?_, ?_, ?_⟩
  · refine hom_ext_appLE (congr(($hjm).base)) fun U e => ?_
    ext f
    have e' : m ⁻¹ᵁ U ≤ j ⁻¹ᵁ (ρ ⁻¹ᵁ m ⁻¹ᵁ U) := e
    have h1 : ((j ≫ Φ).appLE U (m ⁻¹ᵁ U) e).hom f = (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom
        ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f) +
          constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ U) DualNumber.eps * (ρ.app (m ⁻¹ᵁ U)).hom (d U f)) := rfl
    have h2 : (j.appLE (ρ ⁻¹ᵁ m ⁻¹ᵁ U) (m ⁻¹ᵁ U) e').hom ((ρ.app (m ⁻¹ᵁ U)).hom ((m.app U).hom f)) =
        ((j ≫ ρ ≫ m).appLE U (m ⁻¹ᵁ U) e').hom f := rfl
    have h3 : ∀ (k : Y ⟶ X) (_ : k = m) (e''), k.appLE U (m ⁻¹ᵁ U) e'' = m.app U := by
      rintro k rfl e''
      exact Scheme.Hom.appLE_eq_app _
    rw [h1, map_add, map_mul, h2, h3 (j ≫ ρ ≫ m) hjm e', appLE_constFn, hjπ, constFn_spMap, constFn_eq]
    simp
  · apply ext_of_isAffine
    rw [← cancel_epi (Scheme.ΓSpecIso (CommRingCat.of R)).inv]
    ext r
    have h0 : ∀ {Z : Scheme.{0}} (k : Z ⟶ Sp R),
        ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ k.appTop).hom r = constFn k ⊤ r := by
      intro Z k
      have := Scheme.Hom.appLE_eq_app k (U := ⊤)
      exact congr(($this.symm).hom _)
    rw [h0, h0, constFn_spMap]
    have h1 : constFn (Φ ≫ p) ⊤ r = (ρ.app (m ⁻¹ᵁ ⊤)).hom ((m.app ⊤).hom (constFn p ⊤ r)) +
        constFn π (ρ ⁻¹ᵁ m ⁻¹ᵁ ⊤) DualNumber.eps * (ρ.app (m ⁻¹ᵁ ⊤)).hom (d ⊤ (constFn p ⊤ r)) :=
      (app_constFn Φ p ⊤ r).symm
    rw [h1, hd.base ⊤ le_rfl, app_constFn, hm, ← Category.assoc, constFn_spMap, constFn_spMap,
      app_constFn, app_constFn, hpb.w, constFn_spMap, constFn_spMap, constFn_eq, constFn_eq, constFn_eq,
      ← map_mul, ← map_add]
    change constHom π ⊤ _ = constHom π ⊤ _
    congr 1
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  · intro W f
    have h1 := pbT_eq_app Φ f
    have h2 := pbT_eq_app (ρ ≫ m) f
    have h3 := pbT_eq_app ρ (d W f)
    refine h1.trans ?_
    rw [h3]
    erw [h2]
    rfl
end GlobalTheory.KS.DerMorK
