-- Prove2me | solution 1 for GlobalTheory.totalDegree_le_of_integral_at_infinity
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:37:47.803685+00:00
-- url     : https://prove2.me/submissions/0e467dbd-91b3-43aa-91e1-10a147a6b4da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TotalDegreeLeOfIntegralAtInfinity
import Theorems.Thm_GlobalTheory_DegreeBound_aeval_good
import Theorems.Thm_GlobalTheory_DegreeBound_common_order

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory.DegreeBound
namespace GlobalTheory
theorem _root_.solution : ∀ {K : Type} [Field K] {D : ℕ} (y : Fin D → K),
    AlgebraicIndependent ℤ y → ∀ (j : Fin D), y j ≠ 0 → ∀ (T₀ : MvPolynomial (Fin D) ℤ) (q : ℕ)
    {ι : Type} (z : ι → K), (∀ i, ∃ (N : ℕ) (C : MvPolynomial (Fin D) ℤ), C.totalDegree ≤ N ∧
    z i * y j ^ N = aeval y C) → ∀ (f : Polynomial (MvPolynomial ι ℤ)), f.Monic →
    f.eval₂ (aeval z).toRingHom (aeval y T₀ / y j ^ q) = 0 → T₀.totalDegree ≤ q := by
  intro K _ D y hind j hu T₀ q ι z hz f hf heq
  by_contra hlt
  push_neg at hlt
  have hw : y j ^ q ≠ 0 := pow_ne_zero _ hu
  generalize hs : aeval y T₀ / y j ^ q = s at heq
  have ht : aeval y T₀ = s * y j ^ q := by rw [← hs, div_mul_cancel₀ _ hw]
  set c : ℕ → K := fun k => aeval z (f.coeff k) with hc
  have hsum : (∑ k ∈ Finset.range f.natDegree, c k * s ^ k) + s ^ f.natDegree = 0 := by
    rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree] at heq
    simpa [c] using heq
  generalize hn : f.natDegree = n at hsum
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · subst hn0; simp at hsum
  obtain ⟨N, hN⟩ := common_order (y := y) (j := j) c (fun k => aeval_good hz (f.coeff k)) n
  have hC : ∀ k, ∃ C : MvPolynomial (Fin D) ℤ, k < n →
      C.totalDegree ≤ N ∧ c k * y j ^ N = aeval y C := by
    intro k
    by_cases hk : k < n
    · obtain ⟨C, h1, h2⟩ := hN k hk; exact ⟨C, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose Cf hCf using hC
  have hT0 : T₀ ≠ 0 := by rintro rfl; simp at hlt
  set A : MvPolynomial (Fin D) ℤ := X j ^ (N * n) * T₀ ^ n with hA
  set B : MvPolynomial (Fin D) ℤ :=
    ∑ k ∈ Finset.range n, Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1)) with hB
  have hP : aeval y (B + A) = aeval y (0 : MvPolynomial (Fin D) ℤ) := by
    rw [map_zero]
    have : aeval y (B + A) =
        y j ^ (q * n + N * n) * ((∑ k ∈ Finset.range n, c k * s ^ k) + s ^ n) := by
      rw [mul_add, Finset.mul_sum, map_add, map_sum]
      congr 1
      · refine Finset.sum_congr rfl fun k hk => ?_
        have hk' := Finset.mem_range.mp hk
        obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
        have h1 : n - k = m + 1 := by omega
        have h2 : n - 1 = k + m := by omega
        rw [map_mul, map_mul, map_pow, map_pow, aeval_X, ht, ← (hCf k hk').2, h1, h2, hm]
        ring
      · rw [hA, map_mul, map_pow, map_pow, aeval_X, ht]
        ring
    rw [this, hsum, mul_zero]
  have hBA : B + A = 0 := algebraicIndependent_iff_injective_aeval.mp hind hP
  have hpow : ∀ m, (T₀ ^ m).totalDegree = m * T₀.totalDegree := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ, totalDegree_mul_of_isDomain (pow_ne_zero _ hT0) hT0, ih]; ring
  have hAdeg : A.totalDegree = N * n + n * T₀.totalDegree := by
    rw [hA, totalDegree_mul_of_isDomain (pow_ne_zero _ (X_ne_zero _)) (pow_ne_zero _ hT0),
      totalDegree_X_pow, hpow]
  have hpos : 0 < N * n + n * T₀.totalDegree := by
    have := Nat.mul_pos hnpos (show 0 < T₀.totalDegree by omega); omega
  have hBdeg : B.totalDegree < N * n + n * T₀.totalDegree := by
    refine lt_of_le_of_lt (totalDegree_finset_sum _ _) ?_
    rw [Finset.sup_lt_iff (by simpa using hpos)]
    intro k hk
    have hk' := Finset.mem_range.mp hk
    obtain ⟨m, hm⟩ : ∃ m, n = k + m + 1 := ⟨n - k - 1, by omega⟩
    have h1 : n - k = m + 1 := by omega
    have h2 : n - 1 = k + m := by omega
    calc (Cf k * T₀ ^ k * X j ^ (q * (n - k) + N * (n - 1))).totalDegree
        ≤ N + k * T₀.totalDegree + (q * (n - k) + N * (n - 1)) := by
          refine (totalDegree_mul _ _).trans ?_
          rw [totalDegree_X_pow]
          have := (totalDegree_mul (Cf k) (T₀ ^ k)).trans
            (add_le_add (hCf k hk').1 (totalDegree_pow T₀ k))
          linarith
      _ < N * n + n * T₀.totalDegree := by
          rw [h1, h2, hm]
          have h3 : q * (m + 1) < T₀.totalDegree * (m + 1) :=
            Nat.mul_lt_mul_of_pos_right hlt (Nat.succ_pos m)
          nlinarith
  have hAB : A = -B := eq_neg_of_add_eq_zero_right hBA
  have := congrArg MvPolynomial.totalDegree hAB
  rw [totalDegree_neg, hAdeg] at this
  omega
end GlobalTheory
