-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.cubN_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:56:22.624234+00:00
-- url     : https://prove2.me/submissions/1b843ad7-e2a9-4cd8-a79a-c67131bb3609

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
theorem _root_.solution (k : ℕ) (y x : B.A) :
    cubN B'.θ k 1 (I.φ y) (I.φ x) * I.h (y ^ k) * I.h x * I.h (y * x) ^ k =
      cubN B.θ k 1 y x * I.h (y ^ k * x) * I.h y ^ k * I.h x ^ k := by
  induction k with
  | zero => simp [cubN, I.h_one]
  | succ k ih =>
    have a := I.θ_eq (y ^ k) y x
    simp only [cubN, Finset.prod_range_succ, one_mul] at ih ⊢
    rw [map_pow] at a
    rw [pow_succ y]
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow] at a ih ⊢
    linear_combination (norm := module) a + ih
end GlobalTheory.Ex.RecPeriods
