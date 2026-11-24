-- Prove2me | solution 1 for GlobalTheory.LevelCover.zeta_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:59:56.933631+00:00
-- url     : https://prove2.me/submissions/2bb1e8ef-2dd1-4b64-978f-15e1c1f48c26

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LevelMapFiniteEtaleSurjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.LevelCover
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.LevelCover
theorem _root_.solution {a b : ℕ} (hb : 0 < b) (h : a ∣ b) : zeta a = zeta b ^ (b / a) := by
  obtain ⟨k, rfl⟩ := h
  have ha : a ≠ 0 := by rintro rfl; simp at hb
  have hk : k ≠ 0 := by rintro rfl; simp at hb
  rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero ha), zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hk' : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  push_cast
  field_simp
end GlobalTheory.LevelCover
