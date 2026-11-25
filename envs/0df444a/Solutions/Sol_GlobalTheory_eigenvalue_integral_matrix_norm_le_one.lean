-- Prove2me | solution 1 for GlobalTheory.eigenvalue_integral_matrix_norm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:17:52.650584+00:00
-- url     : https://prove2.me/submissions/31741354-ceb4-4697-b0b3-f11909c9df53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormEigenvalueLeOneOfIntegralMatrixUltrametric
import Theorems.Thm_GlobalTheory_norm_eigenvalue_le_one_of_integral_matrix

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (O K : Type) [CommRing O] [NormedField K] [IsUltrametricDist K] (emb : O →+* K),
      (∀ c, ‖emb c‖ ≤ 1) → ∀ (n : ℕ) (M : Matrix (Fin n) (Fin n) O) (μ : K) (c : Fin n → K),
      c ≠ 0 → (M.map emb).mulVec c = μ • c → ‖μ‖ ≤ 1 :=
  fun O K _ _ _ emb hemb n M μ c hc hM =>
    norm_eigenvalue_le_one_of_integral_matrix O K emb hemb n M μ c hc hM
end GlobalTheory
