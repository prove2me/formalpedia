-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HodgeLow.stein_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:38:05.654157+00:00
-- url     : https://prove2.me/submissions/f45b8e26-a93f-4f68-ae6a-32d956826e92

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_pullbackZeroCochains_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_d0_algebraMap
import Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_d0_pullbackZeroCochains

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
    (h : QIsoAt (0 : R →ₗ[R] C0 F) (d0 F) (0 : R →ₗ[R] C0 F') (d0 F') (pullbackZeroCochains m)) :
    Stein F ↔ Stein F' := by
  have hk : ∀ x, d0 F x = 0 → pullbackZeroCochains m x = 0 → x = 0 := fun x hx hp ↦ by
    obtain ⟨y, hy⟩ := h.1 x hx ⟨0, by rw [hp]; rfl⟩
    exact hy.symm
  have hs : ∀ z, d0 F' z = 0 → ∃ x, d0 F x = 0 ∧ pullbackZeroCochains m x = z := fun z hz ↦ by
    obtain ⟨x, y, hx, hy⟩ := h.2 z hz
    exact ⟨x, hx, sub_eq_zero.1 hy⟩
  constructor
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · obtain ⟨x, hx, rfl⟩ := hs y hy
      obtain ⟨r, rfl⟩ := (he x).1 hx
      exact ⟨r, (pullbackZeroCochains_algebraMap m r).symm⟩
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← sub_eq_zero, ← map_sub]
      refine hk _ (d0_algebraMap _) ?_
      rw [pullbackZeroCochains_algebraMap, map_sub, hr, sub_self]
  · rintro ⟨he, hi⟩
    refine ⟨fun y ↦ ⟨fun hy ↦ ?_, ?_⟩, fun r r' hr ↦ hi ?_⟩
    · have h0 : d0 F' (pullbackZeroCochains m y) = 0 := by rw [d0_pullbackZeroCochains, hy, map_zero]
      obtain ⟨r, hr⟩ := (he _).1 h0
      refine ⟨r, ?_⟩
      have hr' : algebraMap R (C0 F') r = pullbackZeroCochains m y := hr
      have e : y - algebraMap R (C0 F) r = 0 := hk _ (by rw [map_sub, hy, d0_algebraMap, sub_self])
        (by rw [map_sub, pullbackZeroCochains_algebraMap, hr', sub_self])
      exact (sub_eq_zero.1 e).symm
    · rintro ⟨r, rfl⟩
      exact d0_algebraMap r
    · rw [← pullbackZeroCochains_algebraMap m, ← pullbackZeroCochains_algebraMap m, hr]
end GlobalTheory.CompanionTheory.HodgeLow
