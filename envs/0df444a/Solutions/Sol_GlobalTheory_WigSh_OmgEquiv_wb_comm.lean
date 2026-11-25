-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.wb_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T07:34:18.17092+00:00
-- url     : https://prove2.me/submissions/6812dc66-371c-4479-8613-a6698b93f3ba

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_block

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmgEquiv
variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ}
namespace GlobalTheory.WigSh.OmgEquiv
theorem _root_.solution {h : Mx k r} (hh : h ∈ UWset k r z) (v : Fin (2 * r + k + 1) → ℂ) :
    (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then (h *ᵥ v) i else 0) =
      h *ᵥ (fun i : Fin (2 * r + k + 1) => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0) := by
  funext i
  simp only [Matrix.mulVec, dotProduct]
  split_ifs with hi
  · refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs with hj
    · rfl
    · have hne : i ≠ j := fun e => hj (by subst e; exact hi)
      simp [GlobalTheory.WigSh.OmgEquiv.block hh i j (fun hc => hj hc.2), hne]
  · refine (Finset.sum_eq_zero fun j _ => ?_).symm
    split_ifs with hj
    · have hne : i ≠ j := fun e => hi (by subst e; exact hj)
      simp [GlobalTheory.WigSh.OmgEquiv.block hh i j (fun hc => hi hc.1), hne]
    · rw [mul_zero]
end GlobalTheory.WigSh.OmgEquiv
