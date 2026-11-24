-- Prove2me | solution 1 for GlobalTheory.SimLift.modN_of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:48:02.737987+00:00
-- url     : https://prove2.me/submissions/6ba1b2b7-423c-474f-b482-47280a6d4613

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_IsCoprimeTwoSubRtTwoAddRt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ModNOfDvdModulus
import Theorems.Thm_GlobalTheory_SimLift_ext_form
import Theorems.Thm_GlobalTheory_SimLift_exists_vec

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
open GlobalTheory GlobalTheory.SimLift
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
namespace GlobalTheory.SimLift
theorem _root_.solution {n : ℕ} (hn : 0 < n) {x : D.La} (h : ∀ b, (n : ℤ) ∣ D.EF x b) : D.ModN n x := by
  choose φ hφ using h
  have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨y, hy⟩ := exists_vec D φ fun a b => by
    apply mul_left_cancel₀ hn'
    rw [← hφ, map_add, hφ, hφ, mul_add]
  refine ⟨y, ext_form D fun b => ?_⟩
  rw [map_nsmul, LinearMap.smul_apply, hy, hφ, nsmul_eq_mul]
end GlobalTheory.SimLift
