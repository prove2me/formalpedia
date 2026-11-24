-- Prove2me | solution 1 for GlobalTheory.T.matrixImage_adjoint_mul_eq_of_selfDual_lattices
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:18:18.362371+00:00
-- url     : https://prove2.me/submissions/2e441cd0-9ad0-44f7-a8b1-c47f21512dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLattices
import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemMatLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MatrixImageAdjointMulEqOfSelfDualLatticesStatement
import Theorems.Thm_GlobalTheory_LatOrb_matLat_adj_mul_eq_of_selfDual


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {O K : Type} [CommRing O] [Field K] [Algebra O K] (σ : K →+* K),
    (∀ x, σ (σ x) = x) → ∀ (n : ℕ) (x : Matrix (Fin n) (Fin n) K), IsUnit x →
    ∀ M : Submodule O (Fin n → K), SelfDual O σ M → SelfDual O σ (matLat O x M) →
    matLat O ((x.map σ)ᵀ * x) M = M := by
  first | exact @GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | exact GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual | (intros; apply GlobalTheory.LatOrb.matLat_adj_mul_eq_of_selfDual <;> assumption)
end _root_.GlobalTheory.T
