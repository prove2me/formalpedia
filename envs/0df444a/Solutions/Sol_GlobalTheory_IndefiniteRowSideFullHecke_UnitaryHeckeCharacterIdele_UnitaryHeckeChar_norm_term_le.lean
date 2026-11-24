-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.norm_term_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:56:16.998087+00:00
-- url     : https://prove2.me/submissions/b58972e0-c26e-47dc-88b1-a39eb2cd0941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_norm_valueAt_le

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
theorem _root_.solution (χ : UnitaryHeckeChar E) (P : HeightOneSpectrum (𝓞 E)) (s : ℂ) :
    ‖χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s)‖ ≤
      (Ideal.absNorm P.asIdeal : ℝ) ^ (-s.re) := by
  have h := NumberField.HeightOneSpectrum.one_lt_absNorm P
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  exact mul_le_of_le_one_left (by positivity) (χ.norm_valueAt_le P)
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
