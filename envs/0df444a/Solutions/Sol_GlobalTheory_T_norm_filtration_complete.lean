-- Prove2me | solution 1 for GlobalTheory.T.norm_filtration_complete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:31.107859+00:00
-- url     : https://prove2.me/submissions/84b47115-475b-45fd-9ebc-302019b837e2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFiltrationComplete
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_NormFiltrationComplete
import Theorems.Thm_GlobalTheory_NormEq_filtrationComplete_filt


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
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), GroundTheory.LocalField.FiltrationComplete (GlobalTheory.NormEq.filt h P) := by
  first | exact @GlobalTheory.NormEq.filtrationComplete_filt | exact GlobalTheory.NormEq.filtrationComplete_filt | (intros; apply GlobalTheory.NormEq.filtrationComplete_filt <;> assumption)
end _root_.GlobalTheory.T
