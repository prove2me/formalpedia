-- Prove2me | solution 1 for GlobalTheory.WeilDeligne.not_tempered_diag_spEig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:06.252198+00:00
-- url     : https://prove2.me/submissions/7df5870a-0346-4ca3-b322-81d4278fbf83

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsSemisimpleOfISupEigenspace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_MonodromyZeroOfWeilDeligneRepClassIff
import Theorems.Thm_GlobalTheory_WeilDeligne_WD_tempered_diag_iff
import Theorems.Thm_GlobalTheory_WeilDeligne_norm_qPow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial TensorProduct Module
open GlobalTheory GlobalTheory.WeilDeligne
variable {E Ω : Type*} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
variable [IsAlgClosure E Ω]
variable (h : IsPlaceOver A w)
namespace GlobalTheory.WeilDeligne
theorem _root_.solution : ¬ (WD.mk (WDRep.diag h (WDRep.spEig w 2))).tempered := by
  rw [WD.tempered_mk, WD.tempered_diag_iff]
  intro hc
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have := hc 0
  rw [WDRep.spEig, norm_qPow, ← Real.rpow_zero ((normV w : ℕ) : ℝ),
    Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne'] at this
  norm_num at this
end GlobalTheory.WeilDeligne
