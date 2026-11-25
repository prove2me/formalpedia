-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HypWedge.key_D
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:54:32.018699+00:00
-- url     : https://prove2.me/submissions/7b72274a-0064-4de4-966e-8b51c255afcc

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FormComponentOfWedgeClassZero
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_coe_mOm
import Theorems.Thm_GlobalTheory_CechDR_toO_mk
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
theorem _root_.solution (hs : Function.Surjective (toO F)) (f : C1 F) (hf : f ∈ Z1 F) :
    ∃ β : A0 F, (∀ (T T' : C) (φ : T ⟶ T'), D R _ (f T T' φ) = β T' - p1 F φ (β T)) ∧
      ∀ T, dOne R _ (β T) = 0 := by
  obtain ⟨c, hc⟩ := hs (H1.mk F ⟨f, hf⟩)
  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F c
  rw [toO_mk, H1.mk_eq_mk] at hc
  obtain ⟨g, hg⟩ := hc
  have hg' : ∀ (T T' : C) (φ : T ⟶ T'), g T' - mp F φ (g T) = c.1.1 T T' φ - f T T' φ :=
    fun T T' φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun T ↦ c.1.2 T - D R _ (g T), fun T T' φ ↦ ?_, fun T ↦ ?_⟩
  · have h2 : f T T' φ = c.1.1 T T' φ - (g T' - mp F φ (g T)) := by rw [hg']; ring
    change _ = (c.1.2 T' - D R _ (g T')) - p1 F φ (c.1.2 T - D R _ (g T))
    rw [h2, map_sub, map_sub, map_sub, p1_D, cechDeRhamTotalCocyclesOne.conn c φ]
    abel
  · simp [cechDeRhamTotalCocyclesOne.closed c]
end GlobalTheory.CompanionTheory.HypWedge
