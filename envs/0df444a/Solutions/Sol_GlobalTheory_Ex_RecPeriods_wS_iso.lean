-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.wS_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:44:37.995005+00:00
-- url     : https://prove2.me/submissions/4aab552a-7b8a-43e0-a438-89e210b9c5d3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_cubN_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_dbl_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_mulq_iso

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
theorem _root_.solution (k : ℕ) (hk : Odd k) (x : B.A) (hx : x ^ k = 1) :
    B'.wS k (I.φ x) 1 1 * I.h x ^ k = B.wS k x 1 1 := by
  obtain ⟨r, rfl⟩ := hk
  have a := cubN_iso I (2 * r + 1) x x
  have b := dbl_iso I x
  have c := mulq_iso I (2 * r + 1) x
  rw [hx, I.h_one] at a c
  rw [one_mul] at a
  have e : (2 * r + 1 - 1) / 2 = r := by omega
  simp only [NumB.wS, e, one_mul]
  replace a := congrArg (fun u => r • Additive.ofMul u) a
  replace b := congrArg (fun u => (r * (2 * r + 1)) • Additive.ofMul u) b
  replace c := congrArg Additive.ofMul c
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_pow, ofMul_div, ofMul_one] at a b c ⊢
  linear_combination (norm := module) c - a + b
end GlobalTheory.Ex.RecPeriods
