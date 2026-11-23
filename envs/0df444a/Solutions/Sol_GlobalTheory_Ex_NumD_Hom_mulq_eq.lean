-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.mulq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:23.996201+00:00
-- url     : https://prove2.me/submissions/e9cd2976-ba59-45c2-882c-c461aee5cb4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_HomTransport
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_cubN_eq
import Theorems.Thm_GlobalTheory_Ex_NumD_Hom_dbl_eq

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
theorem _root_.solution (n : ℕ) (x : N.A) :
    mulq N'.θ N'.σ n (I.φ x) * I.h x ^ (n ^ 2) = F (mulq N.θ N.σ n x) * I.h (x ^ n) := by
  induction n with
  | zero => simp [mulq, I.h_one]
  | succ n ih =>
    have a := I.cubN_eq n x x
    have b := I.dbl_eq x
    rw [← pow_succ] at a
    simp only [mulq, Finset.prod_range_succ, map_mul, map_div, map_pow] at ih ⊢
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ih ⊢
    linear_combination (norm := module) a + ih - n • b
end GlobalTheory.Ex.NumD.Hom
