-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.pull1_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:27:04.000807+00:00
-- url     : https://prove2.me/submissions/9c8ff2cf-e3c7-421a-b282-f10366243487

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_commAlgFunctorCocyclesOne_eq_ker
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
    (h : QIsoAt (d0 F) (d1 F) (d0 F') (d1 F') (pullbackOneCochains m)) : Function.Bijective m.pull1 := by
  refine ⟨(injective_iff_map_eq_zero m.pull1).2 fun c hc ↦ ?_, fun c' ↦ ?_⟩
  · obtain ⟨f, rfl⟩ := H1.mk_surjective F c
    rw [CoefMap.pullCohomologyOne_class] at hc
    obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hc
    have hf : d1 F f.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F ▸ f.2)
    obtain ⟨y, hy⟩ := h.1 f.1 hf ⟨g, hg⟩
    exact H1.mk_eq_zero.2 ⟨y, hy⟩
  · obtain ⟨f', rfl⟩ := H1.mk_surjective F' c'
    have hf : d1 F' f'.1 = 0 := LinearMap.mem_ker.1 (commAlgFunctorCocyclesOne_eq_ker F' ▸ f'.2)
    obtain ⟨x, y, hx, hy⟩ := h.2 f'.1 hf
    have hxm : x ∈ Z1 F := by rw [commAlgFunctorCocyclesOne_eq_ker]; exact hx
    refine ⟨H1.mk F ⟨x, hxm⟩, ?_⟩
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
    exact ⟨y, hy.symm⟩
end GlobalTheory.CompanionTheory.HodgeLow
