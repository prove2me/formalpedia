-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.dbl_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:17.361807+00:00
-- url     : https://prove2.me/submissions/e66dfe67-8710-4feb-a022-96ae09e4752f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport

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
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')
local notation "F" => Units.map (RingHom.toMonoidHom f)
namespace GlobalTheory.Ex.NumD.Hom
theorem _root_.solution (x : N.A) :
    dbl N'.θ N'.σ (I.φ x) * I.h (x * x) = F (dbl N.θ N.σ x) * I.h x ^ 4 := by
  have a := I.θ_eq x x⁻¹ x
  have b := I.σ_eq x
  rw [mul_inv_cancel, inv_mul_cancel, I.h_one, one_mul, map_inv, mul_one, mul_one] at a
  simp only [dbl, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := abel) a - b
end GlobalTheory.Ex.NumD.Hom
