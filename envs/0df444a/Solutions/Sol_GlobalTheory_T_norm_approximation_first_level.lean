-- Prove2me | solution 1 for GlobalTheory.T.norm_approximation_first_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:23:25.034798+00:00
-- url     : https://prove2.me/submissions/96890fbc-8742-4aa1-a76a-d3ba5fd4594c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormApproximationFirstLevel
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_AevalRootEqZeroIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsUnitOneAddPiOMul
import Definitions.Def_GroundTheory_LocalFields_FilteredSurj
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_IsobaricBaseChange_IntegralCoefficientBaseChange_UnitaryBaseChangeCharacters_UnitaryBaseChangeLinks_NormApproximationFirstLevel
import Theorems.Thm_GlobalTheory_NormEq_exists_mul_conj_sub_mem_piPow_one


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
theorem _root_.solution : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (ϖ : L) (q : ℕ) (h : IsUnramInv ϖ σ q) (P : GlobalTheory.UTr.Csr (GlobalTheory.NormEq.sigO σ h.2.1)), P.1.Separable → ∀ x : (GlobalTheory.UTr.Alg P)ˣ, x ∈ GlobalTheory.UTr.plus P → ∃ u : (GlobalTheory.UTr.Alg P)ˣ, (x : GlobalTheory.UTr.Alg P) - (u : GlobalTheory.UTr.Alg P) * GlobalTheory.UTr.conj P u ∈ GlobalTheory.NormEq.piPow h P 1 := by
  first | exact @GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | exact GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one | (intros; apply GlobalTheory.NormEq.exists_mul_conj_sub_mem_piPow_one <;> assumption)
end _root_.GlobalTheory.T
