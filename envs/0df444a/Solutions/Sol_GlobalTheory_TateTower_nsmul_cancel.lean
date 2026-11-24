-- Prove2me | solution 1 for GlobalTheory.TateTower.nsmul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:27:42.144194+00:00
-- url     : https://prove2.me/submissions/e1de7ef4-d84b-4a0b-b73b-1994f80fc5fc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_TateIsometryOfFiniteLevelIsometries

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory GlobalTheory.TateTower
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {K : Type} [Field K] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}
namespace GlobalTheory.TateTower
theorem _root_.solution (D : Datum H) {r : ℕ} (hr : 0 < r) {a c : D.La} (h : r • a = r • c) : a = c := by
  have := D.proj
  have : Module.Flat ℤ D.La := Module.Flat.trans ℤ (𝓞 E) D.La
  have h' : (r : ℤ) • a = (r : ℤ) • c := by simpa only [natCast_zsmul] using h
  exact smul_right_injective D.La (by exact_mod_cast hr.ne' : (r : ℤ) ≠ 0) h'
end GlobalTheory.TateTower
