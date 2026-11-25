-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.beta_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:36.503641+00:00
-- url     : https://prove2.me/submissions/b8731ef8-be24-43b5-a09d-f63e855200ab

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_add
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_sectionsOn_equivOfSMul_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CechDR.SemiHom.coe_mOm
attribute [local simp] GlobalTheory.sectionsOn.equivOfSMul_apply



set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HypWedge
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HypWedge
theorem _root_.solution (τ : H1 F →ₗ[R] cechDeRhamTotalCocyclesOne F) (hτ : ∀ v, H1.mk F (cechDeRhamTotalCocyclesOne.fn F (τ v)) = v)
    (mu : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (hmu : ∀ (f : Z1 F) (w : Glob1 F) (T T' : C) (φ : T ⟶ T'), mu (f ⊗ₜ w) T T' φ = f.1 T T' φ • w.1 T')
    (t : Z1 F ⊗[R] Glob1 F) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'),
      mu t T T' φ - mu (sR τ (LinearMap.rTensor (Glob1 F) (H1.mk F) t)) T T' φ = β T' - p1 F φ (β T) := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | add a b ha hb =>
    obtain ⟨x, hx⟩ := ha
    obtain ⟨y, hy⟩ := hb
    refine ⟨x + y, fun T T' φ ↦ ?_⟩
    have h1 := hx T T' φ
    have h2 := hy T T' φ
    simp only [map_add, Pi.add_apply]
    rw [add_sub_add_comm, h1, h2]
    abel
  | tmul f w =>
    obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 (hτ (H1.mk F f)).symm
    refine ⟨fun T ↦ g T • w.1 T, fun T T' φ ↦ ?_⟩
    have hg' : g T' - mp F φ (g T) = f.1 T T' φ - (cechDeRhamTotalCocyclesOne.fn F (τ (H1.mk F f))).1 T T' φ :=
      congrFun (congrFun (congrFun hg T) T') φ
    simp only [LinearMap.rTensor_tmul, hmu, LinearMap.comp_apply]
    rw [oneFormsMapOfFunctorMorphism_smul, ← w.2 φ, ← sub_smul, ← sub_smul, hg']
end GlobalTheory.CompanionTheory.HypWedge
