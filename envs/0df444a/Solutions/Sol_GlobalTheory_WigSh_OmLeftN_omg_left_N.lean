-- Prove2me | solution 1 for GlobalTheory.WigSh.OmLeftN.omg_left_N
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:54:15.300295+00:00
-- url     : https://prove2.me/submissions/43435d8c-b562-4e51-b950-99329888ea9e

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GroupFactorizationHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_OmgMulLeft
import Theorems.Thm_GlobalTheory_WigSh_OmLeftN_omg_mul_left
import Theorems.Thm_Formalism_QuantumDeterminants_unipotent_subgroup_holds


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
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.OmLeftN
namespace GlobalTheory.WigSh.OmLeftN
theorem _root_.solution : ∀ (k r : ℕ) (z z' : (Fin (2 * r + k + 1) → ℂ)) (g m : Mx k r), inWb k r z → inWb k r z' → g ∈ UH (Hpk k r) → m ∈ Formalism.QuantumDeterminants.Nset k r → GlobalTheory.WigSh.omg k r z z' (m⁻¹ * g) = GlobalTheory.WigSh.omg k r z z' g :=
  fun k r z z' g m hz _ _ hm => omg_mul_left k r z z' g m⁻¹ hz ((unipotent_subgroup_holds k r).2.2 m hm)
end GlobalTheory.WigSh.OmLeftN
