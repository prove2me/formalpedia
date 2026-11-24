-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar.multipliable_eulerFactor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:29:49.920573+00:00
-- url     : https://prove2.me/submissions/cee92b70-ddc3-4c2f-8402-ee0c33dfa3e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AdelicCMFields_UnitaryHeckeCharacterIdele
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_norm_term_le
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_one_sub_ne_zero
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_UnitaryHeckeCharacterIdele_UnitaryHeckeChar_summable_absNorm_rpow

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
theorem _root_.solution (χ : UnitaryHeckeChar E) {s : ℂ} (hs : 1 < s.re) :
    Multipliable fun P => χ.eulerFactor P s := by
  have h1 : Summable fun P : HeightOneSpectrum (𝓞 E) =>
      χ.valueAt P * (Ideal.absNorm P.asIdeal : ℂ) ^ (-s) :=
    Summable.of_norm_bounded (summable_absNorm_rpow hs) fun P => χ.norm_term_le P s
  have h2 := h1.clog_one_sub.neg.hasSum.cexp.multipliable
  refine h2.congr fun P => ?_
  simp only [Function.comp_apply]
  rw [Complex.exp_neg, Complex.exp_log (χ.one_sub_ne_zero P (by linarith))]
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.UnitaryHeckeChar
