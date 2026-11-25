-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.fix_fvec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:05:35.093808+00:00
-- url     : https://prove2.me/submissions/e189614e-973b-4c45-8b36-3d309555248f

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant

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
theorem _root_.solution {h : Mx k r} (hh : h ∈ UWset k r z) (a : Fin (r + 1)) :
    h *ᵥ fvec k r z a = fvec k r z a := by
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hh
  unfold Formalism.QuantumDeterminants.fvec
  split_ifs with ha
  · exact (hh.2.1 ⟨a.val, ha⟩).1
  · exact hh.2.2
end GlobalTheory.WigSh.OmgEquiv
