-- Prove2me | solution 1 for GlobalTheory.T.norm_approximation_filtration
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:22.68782+00:00
-- url     : https://prove2.me/submissions/06314c80-cb9a-41b6-b92c-e2b536946062

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFiltration
import Mathlib
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_NormApproximationFiltration
import Theorems.Thm_GlobalTheory_NormEq_exists_norm_lift_step


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
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)) (m : ℕ), 1 ≤ m → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → x ∈ GlobalTheory.NormEq.filt h P m → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, u ∈ GlobalTheory.NormEq.filt h P m ∧ (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P (m + 1) := by
  first | exact @GlobalTheory.NormEq.exists_norm_lift_step | (intros; apply GlobalTheory.NormEq.exists_norm_lift_step <;> assumption)
end _root_.GlobalTheory.T
