-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.Hpk_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:15:43.01819+00:00
-- url     : https://prove2.me/submissions/02e49a4f-633a-49c8-bc07-37df7c379711

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_param_node
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_cloud
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_DecreasingNodeGaps_sign_node
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.param_node
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_cloud
attribute [local simp] GlobalTheory.IndefiniteRowSideFullHecke.DecreasingNodeGaps.sign_node



set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
open Formalism.QuantumDeterminants (Mt lmulM Hpk UH Nset UWset Sset inWb Tz)
open PI.BesselMapUniq (psiGen)
variable {k r : ℕ}
namespace GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
theorem _root_.solution {i i' : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k))
    (e : i.val + i'.val = 2 * r + k) (l : Fin (2 * r + k + 1)) :
    Hpk k r i' l = if l = i then 1 else 0 := by
  unfold Hpk
  have := l.isLt
  simp only [Fin.ext_iff]
  split_ifs <;> first | rfl | omega
end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
