-- Prove2me | solution 1 for GlobalTheory.T.koszul_exact_inl_nonempty_of_graded_regular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:17:14.725785+00:00
-- url     : https://prove2.me/submissions/8c84bc66-88ee-4b87-9ba1-a2d9f90d35a0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegular
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_KoszulExactOfGradedRegularStatement
import Theorems.Thm_GlobalTheory_KeyKa_KosGr_koszul_exact_of_graded_regular


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [CommRing K] (g : ℕ) (N : ℕ → ℕ) (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) K), (∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2)) → (∀ (i : Fin g) (j : ℕ) (y : Fin (N (j + 1)) → K), j + 1 + i ≤ g → (m i j (j + 1)).mulVec y ∈ (⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' j (j + 1)).mulVecLin) → y ∈ ⨆ (i' : Fin g) (_ : i' < i), LinearMap.range (m i' (j + 1) (j + 2)).mulVecLin) → ∀ v : KIx g 0 N → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w : KIx g 0 N → K, ∀ p : (Σ I : Finset (Fin g), Fin (N I.card)), p.1 ≠ ∅ → v (.inl p) = (kosD m (fun _ => 0)).mulVec w (.inl p) := by
  first | exact @GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | exact GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular | (intros; apply GlobalTheory.KeyKa.KosGr.koszul_exact_of_graded_regular <;> assumption)
end _root_.GlobalTheory.T
