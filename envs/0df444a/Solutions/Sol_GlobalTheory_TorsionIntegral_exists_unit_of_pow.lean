-- Prove2me | solution 1 for GlobalTheory.TorsionIntegral.exists_unit_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:39:23.841806+00:00
-- url     : https://prove2.me/submissions/0a05b1c9-b435-40d5-aa26-0689df3d062a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ExistsZeroGt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsCompleteDvrFiniteSubalgebra
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TorsionPointsIntegral
import Theorems.Thm_GlobalTheory_UU_IsWt_mul


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
open GlobalTheory.UU
noncomputable section
open GlobalTheory
open GlobalTheory.TorsionIntegral
namespace GlobalTheory.TorsionIntegral
theorem _root_.solution {A S : Type} [CommRing A] [PreValuationRing A] [CommRing S] {ρ : A →+* S}
    (hρ : Function.Injective ρ) {v : Sˣ} (hv : v ∈ fracUnits ρ) {N : ℕ} (hN : 1 ≤ N) {u : Aˣ}
    (h : ρ u.val = (v ^ N).val) : ∃ u' : Aˣ, ρ u'.val = v.val := by
  obtain ⟨a, b, hb, e⟩ := hv
  obtain ⟨c, hc | hc⟩ := PreValuationRing.cond a b
  · have ha : IsUnit (ρ a) := e ▸ v.isUnit.mul hb
    have h1 : v.val * ρ c = 1 := ha.mul_right_cancel (by
      rw [_root_.one_mul, _root_.mul_assoc, ← map_mul, mul_comm c, hc, e])
    have h2 : u.val * c ^ N = 1 := hρ (by
      rw [map_mul, h, map_pow, Units.val_pow_eq_pow_val, ← mul_pow, h1, one_pow, map_one])
    have hu : IsUnit c := (isUnit_pow_iff (by omega)).1 (IsUnit.of_mul_eq_one_right _ h2)
    refine ⟨hu.unit⁻¹, ?_⟩
    calc ρ (hu.unit⁻¹).val = v.val * ρ (c * (hu.unit⁻¹).val) := by
          rw [map_mul, ← _root_.mul_assoc, h1, _root_.one_mul]
      _ = v.val := by rw [hu.mul_val_inv, map_one, _root_.mul_one]
  · have h1 : ρ c = v.val := hb.mul_right_cancel (by rw [e, ← map_mul, mul_comm c, hc])
    have h2 : c ^ N = u.val := hρ (by rw [map_pow, h1, h, Units.val_pow_eq_pow_val])
    have hu : IsUnit c := (isUnit_pow_iff (by omega)).1 (h2 ▸ u.isUnit)
    exact ⟨hu.unit, h1⟩
end GlobalTheory.TorsionIntegral
