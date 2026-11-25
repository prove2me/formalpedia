-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.norm_qPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T15:45:22.805735+00:00
-- url     : https://prove2.me/submissions/f3b923a0-f6e8-448e-b25c-2961038842ef

import Mathlib
import Definitions.Def_ReciprocityTheory_GaloisValuations_Global
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_ExistsNotCongPow
import Theorems.Thm_GlobalTheory_WeilDeligne_deg_ineIncl
import Theorems.Thm_GlobalTheory_WeilDeligne_unrChar_apply
import Theorems.Thm_GlobalTheory_WeilDeligne_coe_qPow
import Theorems.Thm_GlobalTheory_WeilDeligne_qPow_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.WeilDeligne.deg_ineIncl
attribute [local simp] GlobalTheory.WeilDeligne.unrChar_apply
attribute [local simp] GlobalTheory.WeilDeligne.coe_qPow
attribute [local simp] GlobalTheory.WeilDeligne.qPow_zero

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable (h : IsPlaceOver A w)
variable {h}
variable [IsAlgClosure E Ω]
omit [IsAlgClosure E Ω]
namespace GlobalTheory.WeilDeligne
theorem _root_.solution (s : ℝ) : ‖(qPow w s : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ s := by
  rw [coe_qPow, Complex.norm_natCast_cpow_of_pos (zero_lt_one.trans (one_lt_normV w))]
  simp
end GlobalTheory.WeilDeligne
