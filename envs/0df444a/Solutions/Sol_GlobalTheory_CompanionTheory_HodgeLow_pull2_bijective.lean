-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.pull2_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:46:52.56013+00:00
-- url     : https://prove2.me/submissions/809cb072-3cd3-4579-b324-3b607dee2928

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_mem_Z2_iff
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp1_mk_surjective
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CechDR_Hyp2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}
namespace GlobalTheory.CompanionTheory.HodgeLow
theorem _root_.solution (m : CoefMap (RingHom.id R) F F')
    (h : QIsoAt (d1 F) (d2 F) (d1 F') (d2 F') (pullbackTwoCochains m)) : Function.Bijective m.pull2 := by
  refine ⟨(injective_iff_map_eq_zero m.pull2).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H2.mk_surjective F c
    rw [CoefMap.pullCohomologyTwo_class] at hc
    obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 hc
    obtain ⟨y, hy⟩ := h.1 f.1 ((mem_Z2_iff _).1 f.2) ⟨g, hg⟩
    exact H2.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H2.mk_surjective F' c'
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 ((mem_Z2_iff _).1 f'.2)
    refine ⟨H2.mk F ⟨x, (mem_Z2_iff _).2 hx⟩, ?_⟩
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
    exact ⟨y, hy.symm⟩
end GlobalTheory.CompanionTheory.HodgeLow
