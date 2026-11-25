-- Prove2me | solution 1 for GlobalTheory.T.eq_zero_of_mem_all_powers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:14:33.953697+00:00
-- url     : https://prove2.me/submissions/4eaabeb3-dd1d-4b7c-bdc8-a1e2a3f25758

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfMemAllPowers
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_EqZeroOfMemAllPowers
import Theorems.Thm_GlobalTheory_NormEq_sep


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
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (a : GlobalTheory.UTr.Alg P), (∀ m, a ∈ GlobalTheory.NormEq.piPow h P m) → a = 0 := by
  first | exact @GlobalTheory.NormEq.sep | (intros; apply GlobalTheory.NormEq.sep <;> assumption)
end _root_.GlobalTheory.T
