-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RootExch.comm_entry
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:09:37.100889+00:00
-- url     : https://prove2.me/submissions/583a5675-20dc-45ff-9388-26e67b40deaa

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PatternGroupStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_RootExchange

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.Ty.Fin
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RootExch
variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.CompanionTheory.RootExch
theorem _root_.solution (g : GL ι K) (r t : ι) (h : r ≠ t) (s : K) (hg : (g : Matrix ι ι K) t r = 0) (i j : ι) :
    ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) i j =
      (1 : Matrix ι ι K) i j + (if i = r ∧ j = t then s else 0) -
        s * (g : Matrix ι ι K) i r * ((g⁻¹ : GL ι K) : Matrix ι ι K) t j := by
  obtain ⟨M, hM⟩ : ∃ M : Matrix ι ι K, M = (g : Matrix ι ι K) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : Matrix ι ι K, N = ((g⁻¹ : GL ι K) : Matrix ι ι K) := ⟨_, rfl⟩
  have hMN : M * N = 1 := by rw [hM, hN, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hval : ((tv r t h s * g * (tv r t h s)⁻¹ * g⁻¹ : GL ι K) : Matrix ι ι K) =
      (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N := by
    rw [hM, hN]; rfl
  have hz : Matrix.single r t s * M * Matrix.single r t (-s) = 0 := by
    rw [Matrix.single_mul_mul_single, hM, hg]
    simp
  have hexp : (1 + Matrix.single r t s) * M * (1 + Matrix.single r t (-s)) * N =
      1 + Matrix.single r t s + M * Matrix.single r t (-s) * N := by
    calc _ = M * N + Matrix.single r t s * (M * N) + M * Matrix.single r t (-s) * N
          + Matrix.single r t s * M * Matrix.single r t (-s) * N := by noncomm_ring
      _ = _ := by rw [hMN, hz]; simp
  have hent : (M * Matrix.single r t (-s) * N) i j = - (s * M i r * N t j) := by
    have h1 : ∀ k, (M * Matrix.single r t (-s)) i k = if k = t then M i r * (-s) else 0 := by
      intro k
      rw [Matrix.mul_apply, Finset.sum_eq_single r]
      · by_cases hk : k = t
        · subst hk; simp [Matrix.single_apply]
        · simp [Matrix.single_apply, hk, Ne.symm hk]
      · intro b _ hb
        simp [Matrix.single_apply, Ne.symm hb]
      · simp
    rw [Matrix.mul_apply, Finset.sum_congr rfl fun k _ => by rw [h1 k]]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  rw [hval, hexp, Matrix.add_apply, Matrix.add_apply, hent, ← hM, ← hN, sub_eq_add_neg]
  simp [Matrix.single_apply, eq_comm]
end GlobalTheory.CompanionTheory.RootExch
