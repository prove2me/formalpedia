-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.exists_normPow_valueAt_eq_neg_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:40:10.184037+00:00
-- url     : https://prove2.me/submissions/89623d4f-5e19-4ce3-ab39-98b6f2075672

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_normPow_valueAt

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
theorem _root_.solution (P : HeightOneSpectrum (𝓞 E)) :
    ∃ t : ℝ, (normPow E t).valueAt P = -1 := by
  have h : (1 : ℝ) < Ideal.absNorm P.asIdeal := by
    exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm P
  refine ⟨-(Real.pi / Real.log (Ideal.absNorm P.asIdeal)), ?_⟩
  rw [normPow_valueAt, neg_mul, neg_neg, div_mul_cancel₀ _ (Real.log_pos h).ne',
    Complex.exp_pi_mul_I]
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
