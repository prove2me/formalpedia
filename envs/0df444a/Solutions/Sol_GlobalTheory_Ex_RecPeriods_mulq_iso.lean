-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.mulq_iso
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:03:23.281198+00:00
-- url     : https://prove2.me/submissions/aee32a42-4678-4b60-a50c-ce933596e53e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_cubN_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_dbl_iso

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
theorem _root_.solution (k : ℕ) (x : B.A) :
    mulq B'.θ B'.σ k (I.φ x) * I.h x ^ (k ^ 2) = mulq B.θ B.σ k x * I.h (x ^ k) := by
  induction k with
  | zero => simp [mulq, I.h_one]
  | succ k ih =>
    have a := cubN_iso I k x x
    have b := dbl_iso I x
    simp only [mulq, Finset.prod_range_succ] at ih ⊢
    rw [pow_succ x, show (k + 1) ^ 2 = k ^ 2 + 2 * k + 1 by ring]
    replace a := congrArg Additive.ofMul a
    replace b := congrArg (fun u => k • Additive.ofMul u) b
    replace ih := congrArg Additive.ofMul ih
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_div] at a b ih ⊢
    linear_combination (norm := module) a - b + ih
end GlobalTheory.Ex.RecPeriods
