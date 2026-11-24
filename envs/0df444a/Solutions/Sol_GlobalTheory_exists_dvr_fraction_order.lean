-- Prove2me | solution 1 for GlobalTheory.exists_dvr_fraction_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:40:10.817543+00:00
-- url     : https://prove2.me/submissions/be22c7d3-2ea9-4001-a683-4fdd6e49c64d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvenQuadraticPosOfFiniteNonpos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubeRelScalarsMemMaximalIdeal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (V : Type) [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] :
    ∃ o : (FractionRing V)ˣ → ℤ, (∀ x y, o (x * y) = o x + o y) ∧
      (∀ (x y : (FractionRing V)ˣ) (u : Vˣ),
        x.val = algebraMap V (FractionRing V) u.val * y.val → o x = o y) ∧
      ∀ x, 0 < o x ↔ ∃ r ∈ IsLocalRing.maximalIdeal V,
        algebraMap V (FractionRing V) r = x.val := by
  let v := (IsDiscreteValuationRing.maximalIdeal V).valuation (FractionRing V)
  have hne : ∀ x : (FractionRing V)ˣ, v x.val ≠ 0 := fun x =>
    (Valuation.ne_zero_iff v).mpr x.ne_zero
  refine ⟨fun x => - WithZero.log (v x.val), ?_, ?_, ?_⟩
  · intro x y
    simp only [Units.val_mul, map_mul]
    rw [WithZero.log_mul (hne x) (hne y)]
    ring
  · intro x y u h
    have hu : v (algebraMap V (FractionRing V) u.val) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
      simp [IsDiscreteValuationRing.maximalIdeal]
    simp only [h, map_mul, hu, _root_.one_mul]
  · intro x
    show 0 < - WithZero.log (v x.val) ↔ _
    rw [neg_pos, WithZero.log_lt_iff_lt_exp (hne x), WithZero.exp_zero]
    constructor
    · intro h
      obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one h.le
      refine ⟨r, ?_, hr⟩
      rw [← hr] at h
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mp h
    · rintro ⟨r, hr, h⟩
      rw [← h]
      exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r).mpr hr
end GlobalTheory
