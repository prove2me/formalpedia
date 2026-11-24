-- Prove2me | solution 1 for GlobalTheory.Moduli.LevelAction.zeta_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:58:24.41295+00:00
-- url     : https://prove2.me/submissions/efbed90b-7ad0-455c-b2b5-b184a5372ef9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabComp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_PullCub
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CompEqIdOfTwists

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
noncomputable section
open GlobalTheory GlobalTheory.Moduli GlobalTheory.Moduli.LevelAction
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
namespace GlobalTheory.Moduli.LevelAction
theorem _root_.solution {A A₂ : ℕ} (hA : 0 < A₂) (h : A ∣ A₂) : zeta A₂ ^ (A₂ / A) = zeta A := by
  obtain ⟨d, rfl⟩ := h
  have hA' : 0 < A := Nat.pos_of_mul_pos_right hA
  have hd : 0 < d := Nat.pos_of_mul_pos_left hA
  rw [Nat.mul_div_cancel_left _ hA', zeta, zeta, ← Complex.exp_nat_mul]
  congr 1
  have : (A : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hA'.ne'
  have : (d : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hd.ne'
  push_cast
  field_simp
end GlobalTheory.Moduli.LevelAction
