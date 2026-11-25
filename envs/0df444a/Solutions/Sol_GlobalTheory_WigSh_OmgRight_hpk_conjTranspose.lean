-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgRight.hpk_conjTranspose
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:03:31.323531+00:00
-- url     : https://prove2.me/submissions/2d7b48eb-7944-4140-ae3c-a5b2c652d1d1

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementD
import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_BigCellVanishingOfCommute
import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_WigMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_LeadingMinorInvariant
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_SBasic
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryQuotientCompactness_NilpotentSubgroup
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CasimirSplitting
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_HpkConjTranspose

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
open GlobalTheory GlobalTheory.WigSh
open GlobalTheory.LeadingMinorInv
open GlobalTheory.WigSh.OmgRight
namespace GlobalTheory.WigSh.OmgRight
theorem _root_.solution (k r : ℕ) : (Hpk k r)ᴴ = Hpk k r := by
  ext i j
  rw [conjTranspose_apply]
  unfold Hpk
  simp only [Fin.ext_iff]
  split_ifs <;> first | (exfalso; omega) | simp
end GlobalTheory.WigSh.OmgRight
