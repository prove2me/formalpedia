-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.prW_comm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:52:08.233804+00:00
-- url     : https://prove2.me/submissions/7dc631f5-e7be-481d-a464-12789fe1f3b8

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_herm_UH
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_wb_comm

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
    Formalism.FourierDecayAlt.D.prW k r z (h *ᵥ v) = h *ᵥ Formalism.FourierDecayAlt.D.prW k r z v := by
  have hh' := hh
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh'
  obtain ⟨hU, -, hz⟩ := hh'
  have key : ∀ w : Fin (2 * r + k + 1) → ℂ, herm (Hpk k r) (h *ᵥ w) z = herm (Hpk k r) w z := by
    intro w
    calc herm (Hpk k r) (h *ᵥ w) z = herm (Hpk k r) (h *ᵥ w) (h *ᵥ z) := by rw [hz]
      _ = herm (Hpk k r) w z := GlobalTheory.WigSh.OmgEquiv.herm_UH hU w z
  simp only [Formalism.FourierDecayAlt.D.prW]
  rw [GlobalTheory.WigSh.OmgEquiv.wb_comm hh v, Matrix.mulVec_sub, Matrix.mulVec_smul, hz, key]
end GlobalTheory.WigSh.OmgEquiv
