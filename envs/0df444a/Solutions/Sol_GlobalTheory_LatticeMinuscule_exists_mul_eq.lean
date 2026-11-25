-- Prove2me | solution 1 for GlobalTheory.LatticeMinuscule.exists_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:57:47.041357+00:00
-- url     : https://prove2.me/submissions/a577db35-ae23-4f14-b2a4-35cfdd4ee9e0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsMulEqMulDiagonal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_LatticeElementaryDivisors

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
open GlobalTheory GlobalTheory.LatticeMinuscule
open Matrix
variable {R K : Type} [CommRing R] [Field K] [Algebra R K] {n : ℕ}
namespace GlobalTheory.LatticeMinuscule
theorem _root_.solution (Λ : Submodule R (Fin n → K)) (C : Matrix (Fin n) (Fin n) K)
    (hC : ∀ y, y ∈ Λ ↔ ∃ z : Fin n → R, y = C.mulVec (fun i => algebraMap R K (z i)))
    (a : Matrix (Fin n) (Fin n) K) (ha : ∀ y ∈ Λ, a.mulVec y ∈ Λ) :
    ∃ M : Matrix (Fin n) (Fin n) R, a * C = C * M.map (algebraMap R K) := by
  have h : ∀ j : Fin n, ∃ z : Fin n → R,
      a.mulVec (C.mulVec (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)))
        = C.mulVec (fun i => algebraMap R K (z i)) :=
    fun j => (hC _).mp (ha _ ((hC _).mpr ⟨_, rfl⟩))
  choose z hz using h
  refine ⟨Matrix.of fun i j => z j i, ?_⟩
  ext i j
  have h1 := congrFun (hz j) i
  have h2 : (fun i => algebraMap R K ((Pi.single j 1 : Fin n → R) i)) = Pi.single j 1 := by
    funext k
    by_cases hk : k = j
    · subst hk; simp
    · simp [hk]
  rw [h2, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h1
  exact h1
end GlobalTheory.LatticeMinuscule
