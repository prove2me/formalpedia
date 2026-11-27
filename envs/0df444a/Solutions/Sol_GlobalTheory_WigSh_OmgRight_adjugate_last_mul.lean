-- Prove2me | solution 1 for GlobalTheory.WigSh.OmgRight.adjugate_last_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:35:50.127911+00:00
-- url     : https://prove2.me/submissions/a3ae6a5d-aac2-40af-b6f7-16d4ae7e1912

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
theorem _root_.solution {n : ℕ} (Z U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (hU : UpUni U) (a : Fin (n + 1)) :
    (Z * U).adjugate (Fin.last n) a = Z.adjugate (Fin.last n) a := by
  have hdet : U.det = 1 := by
    rw [det_of_isUpperTriangular]
    · simp [hU.2]
    · intro i j hij
      exact hU.1 _ _ hij
  have hrow : ∀ b, U.adjugate (Fin.last n) b = if Fin.last n = b then 1 else 0 := by
    intro b
    have h := congrFun (congrFun (Matrix.mul_adjugate U) (Fin.last n)) b
    rw [Matrix.mul_apply, Finset.sum_eq_single (Fin.last n), hU.2, one_mul, hdet, one_smul,
      Matrix.one_apply] at h
    · exact h
    · intro j _ hj
      rw [hU.1 _ _ (lt_of_le_of_ne (Fin.le_last j) hj), zero_mul]
    · simp
  rw [adjugate_mul_distrib, Matrix.mul_apply]
  simp [hrow]
end GlobalTheory.WigSh.OmgRight
