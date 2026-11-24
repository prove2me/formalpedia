-- Prove2me | solution 1 for GlobalTheory.Reg.Transfer.vV_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:54:12.196464+00:00
-- url     : https://prove2.me/submissions/1c36bc62-6c4c-4541-9696-517fc3dca8fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg
variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
namespace GlobalTheory.Reg.Transfer
theorem _root_.solution (w : V) (hw : w ≠ 0) : 0 ≤ vV V (algebraMap V (FractionRing V) w) := by
  have hw' : algebraMap V (FractionRing V) w ≠ 0 := by
    intro h; apply hw; exact IsFractionRing.injective V (FractionRing V) (by rw [h, map_zero])
  have h1 := IsDedekindDomain.HeightOneSpectrum.valuation_le_one
    (IsDiscreteValuationRing.maximalIdeal V) (K := FractionRing V) w
  have h0 : valV V (algebraMap V (FractionRing V) w) ≠ 0 := valV_ne_zero hw'
  have h2 : WithZero.log (valV V (algebraMap V (FractionRing V) w)) ≤ WithZero.log (1 : WithZero (Multiplicative ℤ)) :=
    (WithZero.log_le_log h0 one_ne_zero).2 h1
  rw [WithZero.log_one] at h2
  unfold vV
  omega
end GlobalTheory.Reg.Transfer
