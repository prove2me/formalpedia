-- Prove2me | solution 1 for GlobalTheory.T.integral_basis_change_determinant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:21:39.844092+00:00
-- url     : https://prove2.me/submissions/584e3f0a-f643-46ef-b5ea-077ed3de1785

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralBasisChangeDeterminant
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralBasisChangeDeterminantStatement
import Theorems.Thm_GlobalTheory_det_saturated_lattice_baseChange


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (O k V K : Type) [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field k] [Algebra O k] [IsFractionRing O k] [CommRing V] [Field K] [Algebra V K] [IsFractionRing V K] (f : O →+* V) (em : k →+* K), (∀ a, algebraMap V K (f a) = em (algebraMap O k a)) → ∀ (m n : ℕ) (P : Matrix (Fin m) (Fin n) k) (M : Matrix (Fin m) (Fin m) k) (C : Matrix (Fin m) (Fin m) K), (∀ c, Matrix.vecMul c P = 0 → c = 0) → M.det ≠ 0 → (∀ c : Fin m → k, (∃ a : Fin n → O, Matrix.vecMul c P = fun j => algebraMap O k (a j)) ↔ ∃ b : Fin m → O, c = Matrix.vecMul (fun i => algebraMap O k (b i)) M) → (∀ c : Fin m → K, (∃ a : Fin n → V, Matrix.vecMul c (P.map em) = fun j => algebraMap V K (a j)) ↔ ∃ b : Fin m → V, c = Matrix.vecMul (fun i => algebraMap V K (b i)) C) → ∃ u : Vˣ, C.det = algebraMap V K u * em M.det := by
  first | exact @GlobalTheory.det_saturated_lattice_baseChange | exact GlobalTheory.det_saturated_lattice_baseChange | (intros; apply GlobalTheory.det_saturated_lattice_baseChange <;> assumption)
end _root_.GlobalTheory.T
