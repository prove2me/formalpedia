-- Prove2me | solution 1 for GlobalTheory.UnitBallVal.main
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:36:22.301879+00:00
-- url     : https://prove2.me/submissions/3516f57b-f0c7-4b88-aab6-c958e0743435

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ImportsBis
import Theorems.Thm_GlobalTheory_UnitBallVal_dvd_of_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Pdiv GlobalTheory.AbLaw
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.UnitBallVal
namespace GlobalTheory.UnitBallVal
theorem _root_.solution : ∀ (C O : Type) [NontriviallyNormedField C] [IsUltrametricDist C] [CommRing O] [Algebra O C], IsUnitBall O C → ∃ (_ : IsDomain O), ValuationRing O ∧ Ring.DimensionLEOne O ∧ IsFractionRing O C := by
  intro C O _ _ _ _ hO
  obtain ⟨hinj, hball⟩ := hO
  have hsurj : ∀ x : C, ‖x‖ ≤ 1 → ∃ y : O, algebraMap O C y = x := fun x hx => (hball x).mpr hx
  have hle : ∀ y : O, ‖algebraMap O C y‖ ≤ 1 := fun y => (hball _).mp ⟨y, rfl⟩
  have hdom : IsDomain O := hinj.isDomain (algebraMap O C)

  have hunit : ∀ y : O, ‖algebraMap O C y‖ = 1 → IsUnit y := fun y hy =>
    isUnit_of_dvd_one (dvd_of_norm_le hinj hsurj (by rw [map_one, norm_one, hy]))
  refine ⟨hdom, { cond' := fun a b => ?_ }, ⟨fun {P} hP0 hP => ?_⟩, ?_⟩
  · rcases le_total ‖algebraMap O C b‖ ‖algebraMap O C a‖ with h | h
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inl hc.symm⟩
    · obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj h
      exact ⟨c, Or.inr hc.symm⟩
  ·
    obtain ⟨p, hpP, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hP0
    have hp' : algebraMap O C p ≠ 0 := fun h0 => hp0 (hinj (by rw [h0, map_zero]))
    have key : ∀ m : O, m ∉ P → IsUnit m := by
      intro m hm
      apply hunit
      refine le_antisymm (hle m) (not_lt.mp fun hlt => hm ?_)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.mpr hp') hlt
      obtain ⟨c, hc⟩ := dvd_of_norm_le hinj hsurj (a := p) (b := m ^ n)
        (by rw [map_pow, norm_pow]; exact hn.le)
      refine hP.mem_of_pow_mem n ?_
      rw [hc]
      exact P.mul_mem_right c hpP
    obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P hP.ne_top
    have hMP : M ≤ P := fun m hm => by
      by_contra hmP
      exact hM.ne_top (Ideal.eq_top_of_isUnit_mem M hm (key m hmP))
    rwa [le_antisymm hPM hMP]
  · refine (isLocalization_iff (nonZeroDivisors O) C).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨y, hy⟩
      exact IsUnit.mk0 _ fun h0 => nonZeroDivisors.ne_zero hy (hinj (by rw [h0, map_zero]))
    · intro z
      by_cases hz : ‖z‖ ≤ 1
      · obtain ⟨y, hy⟩ := hsurj z hz
        exact ⟨⟨y, 1⟩, by simp [hy]⟩
      · rw [not_le] at hz
        have hz0 : z ≠ 0 := by
          rintro rfl
          rw [norm_zero] at hz
          linarith
        obtain ⟨y, hy⟩ := hsurj z⁻¹ (by rw [norm_inv]; exact inv_le_one_of_one_le₀ hz.le)
        have hy0 : y ∈ nonZeroDivisors O := mem_nonZeroDivisors_of_ne_zero (by
          rintro rfl
          rw [map_zero] at hy
          exact inv_ne_zero hz0 hy.symm)
        exact ⟨⟨1, ⟨y, hy0⟩⟩, by simp [hy, hz0]⟩
    · intro x y hxy
      exact ⟨1, by rw [hinj hxy]⟩
end GlobalTheory.UnitBallVal
