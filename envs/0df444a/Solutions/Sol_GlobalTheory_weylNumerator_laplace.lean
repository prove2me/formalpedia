-- Prove2me | solution 1 for GlobalTheory.weylNumerator_laplace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:35.408983+00:00
-- url     : https://prove2.me/submissions/f459ef68-81d7-4ddb-b08d-616c4c457906

import Mathlib
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WeylNumeratorLaplace
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_glue_natAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_castAdd
import Theorems.Thm_Formalism_ResultantValuation_LaplaceProof_shuffle_natAdd
import Theorems.Thm_Formalism_ResultantValuation_laplaceExpansionRows
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.glue_natAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_castAdd
attribute [local simp] Formalism.ResultantValuation.LaplaceProof.shuffle_natAdd



set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (a b : ℕ) (α : Fin a → ℂˣ) (β : Fin b → ℂˣ) (l : Fin (a + b) → ℤ), (Matrix.of fun i j : Fin (a + b) => (((Fin.addCases α β i : ℂˣ) ^ l j : ℂˣ) : ℂ)).det = ∑ J : {J : Finset (Fin (a + b)) // J.card = a}, (-1 : ℂ) ^ ((∑ j ∈ J.1, (j : ℕ)) + a * (a - 1) / 2) * (Matrix.of fun i k : Fin a => ((α i ^ l (J.1.orderEmbOfFin J.2 k) : ℂˣ) : ℂ)).det * (Matrix.of fun i k : Fin b => ((β i ^ l (J.1ᶜ.orderEmbOfFin (by rw [Finset.card_compl, J.2]; simp) k) : ℂˣ) : ℂ)).det := by
  intro a b α β l
  rw [Formalism.ResultantValuation.laplaceExpansionRows ℂ a b]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  rw [Nat.add_comm (a * (a - 1) / 2)]
  congr 2
  · congr 1
    ext i k
    simp [Matrix.submatrix]
  · congr 1
    ext i k
    simp [Matrix.submatrix]
end GlobalTheory
