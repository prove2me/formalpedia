-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.dbl_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:58:07.367219+00:00
-- url     : https://prove2.me/submissions/3a818a96-7ddd-4a58-861f-e46d3f94e328

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {O : Type} [CommRing O] {B B' : NumB O} (I : NumB.Iso B B')
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution (x : B.A) : dbl B'.θ B'.σ (I.φ x) * I.h (x * x) = dbl B.θ B.σ x * I.h x ^ 4 := by
  have a := I.θ_eq x x⁻¹ x
  have b := I.σ_eq x
  rw [mul_inv_cancel, inv_mul_cancel, one_mul, I.h_one, map_inv] at a
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  apply Additive.ofMul.injective
  simp only [dbl, ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at a b ⊢
  linear_combination (norm := module) a - b
end GlobalTheory.Ex.RecPeriods
