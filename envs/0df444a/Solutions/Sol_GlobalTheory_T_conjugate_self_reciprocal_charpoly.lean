-- Prove2me | solution 1 for GlobalTheory.T.conjugate_self_reciprocal_charpoly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:19:36.760928+00:00
-- url     : https://prove2.me/submissions/0ba3de3d-4c60-41eb-8fe3-d0aba4710891

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConjugateSelfReciprocalCharpoly
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_ConjugateSelfReciprocalCharpoly
import Theorems.Thm_GlobalTheory_UTr_isCsr_charpoly_of_cT_mul_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix Formalism.UG
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (R : Type) [CommRing R] (s : R →+* R) (n : ℕ) (M : Matrix (Fin n) (Fin n) R), cT s M * M = 1 → GlobalTheory.UTr.IsCsr s M.charpoly := by
  first | exact @GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one | (intros; apply GlobalTheory.UTr.isCsr_charpoly_of_cT_mul_eq_one <;> assumption)
end _root_.GlobalTheory.T
