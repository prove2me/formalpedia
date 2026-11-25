-- Prove2me | solution 1 for GlobalTheory.T.exists_integral_solution_frobenius_sub_mulVec_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:01:00.426322+00:00
-- url     : https://prove2.me/submissions/2596049d-de45-4906-8845-fe1cb3138780

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MooreNorm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIntegralSolutionFrobeniusSubMulVecEqStatement
import Theorems.Thm_GlobalTheory_PMonE_LangOnto_lang_onto


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [IsAlgClosed F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e : ℕ), 0 < e → ∀ A : Matrix m m F, (∀ i j, ‖A i j‖ ≤ 1) → ∀ b : m → F, Integral b → ∃ x : m → F, Integral x ∧ ∀ i, x i ^ p ^ e - A.mulVec x i = b i := by
  first | exact @GlobalTheory.PMonE.LangOnto.lang_onto | exact GlobalTheory.PMonE.LangOnto.lang_onto | (intros; apply GlobalTheory.PMonE.LangOnto.lang_onto <;> assumption)
end _root_.GlobalTheory.T
