-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Hom.cubN_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:51:16.20813+00:00
-- url     : https://prove2.me/submissions/7c5429eb-0693-48b3-88ca-0ab112bf36a7

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
theorem _root_.solution (k : ℕ) (m x : N.A) :
    cubN N'.θ k 1 (I.φ m) (I.φ x) * I.h (m ^ k) * I.h x * I.h (m * x) ^ k =
      F (cubN N.θ k 1 m x) * I.h (m ^ k * x) * I.h m ^ k * I.h x ^ k := by
  induction k with
  | zero => simp [cubN, I.h_one]
  | succ k ih =>
    have a := I.θ_eq (m ^ k) m x
    simp only [cubN, Finset.prod_range_succ, one_mul, map_mul] at ih ⊢
    rw [← pow_succ, map_pow] at a
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    rw [pow_succ (I.h m), pow_succ (I.h x), pow_succ (I.h (m * x))]
    simp only [ofMul_mul] at a ih ⊢
    linear_combination (norm := abel) a + ih
end GlobalTheory.Ex.NumD.Hom
