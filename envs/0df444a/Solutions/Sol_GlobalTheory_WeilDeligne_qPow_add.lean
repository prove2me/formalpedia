-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.qPow_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:37:52.074693+00:00
-- url     : https://prove2.me/submissions/c05818bc-cc06-43ac-9bcb-b532fc5fafb5

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
theorem _root_.solution (s t : ℝ) : qPow w (s + t) = qPow w s * qPow w t := Units.ext (by
  simp only [coe_qPow, Units.val_mul, Complex.ofReal_add]
  exact Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr (one_lt_normV w).ne_bot))
end GlobalTheory.WeilDeligne
