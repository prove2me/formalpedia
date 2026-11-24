-- Prove2me | solution 1 for GlobalTheory.StdChar.ce_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:21.493894+00:00
-- url     : https://prove2.me/submissions/ad233fac-d38a-43fd-94f8-3b29dec3e2a2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Theorems.Thm_GlobalTheory_StdChar_qe_eq_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
namespace GlobalTheory.StdChar
theorem _root_.solution {z : AddCircle (1 : ℚ)} (h : ce z = 1) : z = 0 := by
  induction z using QuotientAddGroup.induction_on with
  | H q =>
  obtain ⟨n, hn⟩ := qe_eq_one h
  rw [AddCircle.coe_eq_zero_iff]
  exact ⟨n, by simp [hn]⟩
end GlobalTheory.StdChar
