-- Prove2me | solution 1 for GlobalTheory.IntegralFrameAllCompare.vV_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:34.877395+00:00
-- url     : https://prove2.me/submissions/9717749b-cd76-4524-89e4-e779d74f9aed

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_IntAllFree
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_IntegralFrameAcquisition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_VVNonnegIffLeOne
import Theorems.Thm_Formalism_L2_Pj_valV_ne_zero
import Theorems.Thm_GlobalTheory_constDerivEval_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_C
import Theorems.Thm_GlobalTheory_mvEvalAdic_X
import Theorems.Thm_GlobalTheory_mvEvalAdic_coe
import Theorems.Thm_GlobalTheory_pderivEval_X
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.constDerivEval_X
attribute [local simp] GlobalTheory.mvEvalAdic_C
attribute [local simp] GlobalTheory.mvEvalAdic_X
attribute [local simp] GlobalTheory.mvEvalAdic_coe
attribute [local simp] GlobalTheory.pderivEval_X



set_option autoImplicit false
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GlobalTheory GlobalTheory.IntegralFrameAllCompare
open NumberField IsDedekindDomain IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.IntegralFrameAcquisition
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]
namespace GlobalTheory.IntegralFrameAllCompare
theorem _root_.solution {v : V} (h0 : v ≠ 0) (h : v ∈ maximalIdeal V) : 0 < vV V (algebraMap V K v) := by
  have h1 : algebraMap V K v ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 h0
  have h2 : valV V (algebraMap V K v) < 1 := (HeightOneSpectrum.valuation_lt_one_iff_mem _ v).2 h
  have := (WithZero.log_lt_log (valV_ne_zero (V := V) h1) one_ne_zero).2 h2
  simp only [WithZero.log_one] at this
  simp only [vV]; omega
end GlobalTheory.IntegralFrameAllCompare
