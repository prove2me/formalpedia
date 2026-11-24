-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeAlt.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:28:18.340544+00:00
-- url     : https://prove2.me/submissions/3e2a41b4-13eb-46fd-9846-f3997b27d595

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F}
namespace GlobalTheory.CompanionTheory.HodgeAlt
theorem _root_.solution (hs : Function.Surjective (toO F)) (f : Z1 F) :
    ∃ α : A0 F, ((f.1, α) : Tot1 F) ∈ cechDeRhamTotalCocyclesOne F := by
  obtain ⟨c, hc⟩ := hs (H1.mk F f)
  obtain ⟨c, rfl⟩ := Hyp1.mk_surjective F c
  obtain ⟨g, hg⟩ := H1.mk_eq_mk.1 (show H1.mk F (cechDeRhamTotalCocyclesOne.fn F c) = H1.mk F f from hc)
  have hg' : ∀ (T T' : C) (φ : T ⟶ T'), c.1.1 T T' φ = f.1 T T' φ + (g T' - mp F φ (g T)) :=
    fun T T' φ ↦ by
      have := congrFun (congrFun (congrFun hg T) T') φ
      rw [amitsur_d0_apply] at this
      rw [this]
      change _ = _ + (c.1.1 T T' φ - f.1 T T' φ)
      abel
  refine ⟨fun T ↦ c.1.2 T - D R _ (g T), mem_cechDeRhamTotalCocyclesOne_iff.2 ⟨f.2, fun T T' φ ↦ ?_, fun T ↦ ?_⟩⟩
  · simp only [map_sub, p1_D]
    rw [cechDeRhamTotalCocyclesOne.conn c φ, hg', map_add, map_sub]
    abel
  · simp [cechDeRhamTotalCocyclesOne.closed c]
end GlobalTheory.CompanionTheory.HodgeAlt
