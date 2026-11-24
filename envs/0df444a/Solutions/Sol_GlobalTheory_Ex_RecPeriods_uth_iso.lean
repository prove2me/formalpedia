-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.uth_iso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:06:17.557845+00:00
-- url     : https://prove2.me/submissions/0bdbac64-a9c9-49df-b517-3a7fb6b4455b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_cubN_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_mulq_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_wS_iso

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
theorem _root_.solution (m : ℕ) (hm : Odd m) (b x : B.A) (hb : b ^ m ^ 2 = 1) :
    B'.uth m (I.φ b) (I.φ x) = (I.lam * I.h x ^ m ^ 2 : Oˣ) * B.uth m b x := by
  have a := cubN_iso I (m ^ 2) b x
  have w := wS_iso I (m ^ 2) hm.pow b hb
  have c := mulq_iso I m (x * b)
  rw [hb, I.h_one, one_mul, mul_comm b x] at a
  have key : B'.uV (m ^ 2) 1 (I.φ b) (I.φ x) * B'.wS (m ^ 2) (I.φ b) 1 1 * (I.lam * I.h ((x * b) ^ m)) *
      (mulq B'.θ B'.σ m (I.φ (x * b)))⁻¹ =
      I.lam * I.h x ^ m ^ 2 * (B.uV (m ^ 2) 1 b x * B.wS (m ^ 2) b 1 1) * (mulq B.θ B.σ m (x * b))⁻¹ := by
    simp only [NumB.uV, B.cub.face, B'.cub.face, div_one]
    replace a := congrArg Additive.ofMul a
    replace w := congrArg Additive.ofMul w
    replace c := congrArg Additive.ofMul c
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one] at a w c ⊢
    linear_combination (norm := module) a + w - c
  replace key := congrArg Units.val key
  simp only [NumB.uth, NumB.mth, ← map_mul, ← map_pow, I.th_eq]
  simp only [Units.val_mul] at key ⊢
  linear_combination B.th ((x * b) ^ m) * key
end GlobalTheory.Ex.RecPeriods
