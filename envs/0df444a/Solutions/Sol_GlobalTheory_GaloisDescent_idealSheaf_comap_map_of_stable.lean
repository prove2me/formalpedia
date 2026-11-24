-- Prove2me | solution 1 for GlobalTheory.GaloisDescent.idealSheaf_comap_map_of_stable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:00:52.350069+00:00
-- url     : https://prove2.me/submissions/c8b705da-5d1d-49fc-8985-ab8dde4ad148

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsAffineHomOfIsPullbackSpecMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_MvPolynomialIsHomogeneousComapWeighted
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueComapEqVanishingIdeal
import Theorems.Thm_GlobalTheory_GaloisDescent_ideal_le_comap_appLE
import Theorems.Thm_GlobalTheory_GaloisDescent_isPushout_app
import Theorems.Thm_GlobalTheory_GaloisDescent_contract_smul
import Theorems.Thm_GlobalTheory_GaloisDescent_ideal_map_comap_of_stable
import Theorems.Thm_GlobalTheory_GaloisDescent_mem_rationalPart
import Theorems.Thm_GlobalTheory_GaloisDescent_quotientEquivOfMapEq_tmul
import Theorems.Thm_GlobalTheory_GaloisDescent_rationalPart_baseChange
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_appLinearBase_apply
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_algebraMap
import Theorems.Thm_GlobalTheory_QCoh_Qcqs_baseRingHom_comp_SpecMap
import Theorems.Thm_GlobalTheory_QCoh_germLinear_apply
import Theorems.Thm_GlobalTheory_QCoh_resBasicOpen_apply
import Theorems.Thm_GlobalTheory_QCoh_resLinear_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GaloisDescent.contract_smul
attribute [local simp] GlobalTheory.GaloisDescent.mem_rationalPart
attribute [local simp] GlobalTheory.GaloisDescent.quotientEquivOfMapEq_tmul
attribute [local simp] GlobalTheory.GaloisDescent.rationalPart_baseChange
attribute [local simp] GlobalTheory.QCoh.Qcqs.appLinearBase_apply
attribute [local simp] GlobalTheory.QCoh.germLinear_apply
attribute [local simp] GlobalTheory.QCoh.resBasicOpen_apply
attribute [local simp] GlobalTheory.QCoh.resLinear_apply



set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace GlobalTheory.QCoh.Qcqs
universe u
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {X Y : Scheme.{u}}
  {p : X ⟶ Spec (.of K)} {q : Y ⟶ Spec (.of L)} {π : Y ⟶ X}
  (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap K L)))) {G : Type*}
include H
set_option backward.isDefEq.respectTransparency false
namespace GlobalTheory.GaloisDescent
theorem _root_.solution (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (a : G → (Y ⟶ Y)) (haπ : ∀ g, a g ≫ π = π)
    (haq : ∀ g, a g ≫ q = q ≫ Spec.map (CommRingCat.ofHom (s g)))
    (I : Y.IdealSheafData) (hI : ∀ g, I.comap (a g) ≤ I) : (I.map π).comap π = I := by
  have : IsAffineHom π := MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
  refine Scheme.IdealSheafData.le_of_iSup_eq_top
    (fun U : X.affineOpens => ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩) ?_ fun U => ?_
  · change ⨆ U : X.affineOpens, π ⁻¹ᵁ U.1 = ⊤
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · let := (π.app U).hom.toAlgebra
    let := (baseRingHom p U).hom.toAlgebra
    let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
    let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
    have : IsScalarTower K Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
    have : IsScalarTower K L Γ(Y, π ⁻¹ᵁ U) :=
      .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of K) (L := .of L) H _ r).symm
    have hpo : Algebra.IsPushout K Γ(X, U) L Γ(Y, π ⁻¹ᵁ U) :=
      CommRingCat.isPushout_iff_isPushout.mp (isPushout_app H U.2)
    have e : ∀ g, π ⁻¹ᵁ U.1 ≤ a g ⁻¹ᵁ (π ⁻¹ᵁ U.1) := fun g => by
      rw [← Scheme.Hom.comp_preimage, haπ]
    have h1 : ∀ g, π.app U ≫ (a g).appLE _ _ (e g) = π.app U := fun g => by
      simp only [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE, haπ]
    have h2 : ∀ g, baseRingHom q (π ⁻¹ᵁ U) ≫ (a g).appLE _ _ (e g) =
        CommRingCat.ofHom (s g) ≫ baseRingHom q (π ⁻¹ᵁ U) := fun g => by
      rw [← baseRingHom_comp_SpecMap, ← haq]
      simp only [baseRingHom, Category.assoc, Scheme.Hom.appLE_comp_appLE]
    have key := ideal_map_comap_of_stable hpo.symm.out s hs
      (fun g => ((a g).appLE _ _ (e g)).hom.toAddMonoidHom) (fun g l x => by
        have h3 := congr($(h1 g) x)
        have h4 := congr($(h2 g) l)
        change (a g).appLE _ _ (e g) (baseRingHom q (π ⁻¹ᵁ U) l * π.app U x) =
          baseRingHom q (π ⁻¹ᵁ U) (s g l) * π.app U x
        rw [map_mul]
        exact congrArg₂ (· * ·) h4 h3)
      (I.ideal ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩)
      (fun g x hx => ideal_le_comap_appLE (a g) (hI g) ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩
        ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ (e g) hx)
    rw [← key, Ideal.map_le_iff_le_comap]
    intro x hx
    have h5 := ideal_le_comap_appLE π (le_refl ((I.map π).comap π)) U
      ⟨π ⁻¹ᵁ U.1, U.2.preimage π⟩ le_rfl (x := x)
      (by rw [Scheme.IdealSheafData.ideal_map_of_isAffineHom]; exact hx)
    rw [← Scheme.Hom.app_eq_appLE] at h5
    exact h5
end GlobalTheory.GaloisDescent
