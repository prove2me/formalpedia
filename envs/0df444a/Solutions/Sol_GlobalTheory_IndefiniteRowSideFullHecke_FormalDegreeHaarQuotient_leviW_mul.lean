-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient.leviW_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:37:25.255306+00:00
-- url     : https://prove2.me/submissions/053826ed-0b41-4893-97ae-67caa7900551

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
import Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FormalDegreeHaarQuotient_row_out
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
theorem _root_.solution {z : Fin (2 * r + k + 1) → ℂ} {h n : Mat k r} (hh : h ∈ UWset k r z)
    (hn : n ∈ Nset k r) : leviW k r (h * n) = h := by
  funext i j
  unfold leviW
  split_ifs with h1 h2
  · rw [Matrix.mul_apply, Finset.sum_eq_single j]
    · rw [hn.2.2 j j h1.2.1 h1.2.2 h1.2.1]; simp
    · intro l _ hl
      by_cases hr : r ≤ l.val
      · rw [hn.2.2 l j h1.2.1 h1.2.2 hr]; simp [hl]
      · rw [col_out hh (j := l) (by omega) i, if_neg, zero_mul]
        rintro rfl
        omega
    · simp
  · subst h2
    rw [col_out hh (j := i) (by tauto) i]; simp
  · by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [row_out hh (i := i) (by tauto) j, if_neg h2]
    · rw [col_out hh hj i, if_neg h2]
end GlobalTheory.IndefiniteRowSideFullHecke.FormalDegreeHaarQuotient
