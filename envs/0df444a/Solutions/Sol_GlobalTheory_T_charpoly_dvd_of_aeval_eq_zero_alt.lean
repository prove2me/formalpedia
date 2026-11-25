-- Prove2me | solution 1 for GlobalTheory.T.charpoly_dvd_of_aeval_eq_zero_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:12:27.00074+00:00
-- url     : https://prove2.me/submissions/f36d238b-e8d3-4efb-8a6d-865a1eca61fe

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CharpolyDvdOfAevalEqZero
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_CharpolyDvdOfAevalEqZero
import Theorems.Thm_GlobalTheory_SepCharpoly_charpoly_dvd_of_aeval_eq_zero


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
theorem _root_.solution : ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (M : Matrix (Fin n) (Fin n) R) (p : R[X]), M.charpoly.Separable → aeval M p = 0 → M.charpoly ∣ p := by
  first | exact @GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero | (intros; apply GlobalTheory.SepCharpoly.charpoly_dvd_of_aeval_eq_zero <;> assumption)
end _root_.GlobalTheory.T
