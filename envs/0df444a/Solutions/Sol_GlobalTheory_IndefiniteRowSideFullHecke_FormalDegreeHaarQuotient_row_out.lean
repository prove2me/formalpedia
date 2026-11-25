-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.row_out
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T07:14:29.087606+00:00
-- url     : https://prove2.me/submissions/ec189b19-4a1a-4ef3-9db7-72f7b3cb24f6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UpqRep
import Definitions.Def_Formalism_PeriodIntegrals_IsLowUnitH
import Definitions.Def_Formalism_PeriodIntegrals_BesselMapUniq
import Definitions.Def_Formalism_FormalDegreeBessel_StatementG
import Definitions.Def_Formalism_FormalDegreeBessel_StatementDS
import Definitions.Def_Formalism_FormalDegreeBessel_StatementBF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_DecreasingNodeGaps
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_FormalDegreeHaarQuotient
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_col_out
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_Hpk_row
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h : Mat k r} (hh : h ∈ UWset k r z)
    {i : Fin (2 * r + k + 1)} (hi : ¬ (r ≤ i.val ∧ i.val ≤ r + k)) (j : Fin (2 * r + k + 1)) :
    h i j = if i = j then 1 else 0 := by
  have hlt := i.isLt
  let i' : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have e : i.val + i'.val = 2 * r + k := by simp only [i']; omega
  have hi' : ¬ (r ≤ i'.val ∧ i'.val ≤ r + k) := by omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have h1 := congrFun (congrFun hU i') j
  have hrow : ∀ m, (hᴴ * Hpk k r) i' m = Hpk k r i' m := by
    intro m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, col_out hh hi']
    rw [Finset.sum_eq_single i'] <;> simp +contextual
  rw [Matrix.mul_apply] at h1
  simp only [hrow, Hpk_row hi e] at h1
  simpa [eq_comm] using h1
end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
