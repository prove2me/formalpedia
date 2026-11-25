-- Prove2me | solution 1 for GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:02:23.872431+00:00
-- url     : https://prove2.me/submissions/b5dcec96-e2fb-4abb-bddc-c4c49a9d6d40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigenStatement
import Theorems.Thm_GlobalTheory_hhJ_nonneg_of_cloud_eigen


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  first | exact @GlobalTheory.hhJ_nonneg_of_cloud_eigen | exact GlobalTheory.hhJ_nonneg_of_cloud_eigen | (intros; apply GlobalTheory.hhJ_nonneg_of_cloud_eigen <;> assumption)
end _root_.GlobalTheory.T
