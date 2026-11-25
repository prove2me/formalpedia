-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgEquiv.Zhat_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:20.151309+00:00
-- url     : https://prove2.me/submissions/225d70e2-3699-4573-8f8a-89e1f608f9ba

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_MulVecBvecApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgEquivariant
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_herm_UH
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_fix_fvec
import Theorems.Thm_GlobalTheory_WigSh_OmgEquiv_inv_mem

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
theorem _root_.solution {g h h' : Mx k r} (hh : h ∈ UWset k r z) (hh' : h' ∈ UWset k r z') :
    Zhat k r z z' (h⁻¹ * g * h') = Zhat k r z z' g := by
  have hi := GlobalTheory.WigSh.OmgEquiv.inv_mem hh
  have hiU : h⁻¹ ∈ UH (Hpk k r) := by
    have hi' := hi
    simp only [Formalism.QuantumDeterminants.UWset, Set.mem_ofPred_eq] at hi'
    exact hi'.1
  ext a b
  simp only [Formalism.QuantumDeterminants.Zhat]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, GlobalTheory.WigSh.OmgEquiv.fix_fvec hh' b]
  calc herm (Hpk k r) (h⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) (fvec k r z a)
      = herm (Hpk k r) (h⁻¹ *ᵥ (g *ᵥ fvec k r z' b)) (h⁻¹ *ᵥ fvec k r z a) := by
        rw [GlobalTheory.WigSh.OmgEquiv.fix_fvec hi a]
    _ = herm (Hpk k r) (g *ᵥ fvec k r z' b) (fvec k r z a) := GlobalTheory.WigSh.OmgEquiv.herm_UH hiU _ _
end GlobalTheory.WigSh.OmgEquiv
