-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.one_sub_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:09:38.84165+00:00
-- url     : https://prove2.me/submissions/fe010876-0c5d-477d-ab5f-f7659d162e11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_norm_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Filter
open scoped RestrictedProduct
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele
variable {E : Type} [Field E] [NumberField E]
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
namespace GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
theorem _root_.solution (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) {s : ℂ}
    (hs : 0 < s.re) : 1 - χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) ≠ 0 := by
  intro h
  have h1 := χ.norm_term_le P s
  rw [← sub_eq_zero.mp h, norm_one] at h1
  have h2 : (1 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  exact absurd (Real.rpow_lt_one_of_one_lt_of_neg h2 (neg_neg_of_pos hs)) (not_lt.mpr h1)
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
