-- Prove2me | solution 1 for GlobalTheory.Hk.LamRay.sum_lamIdeal_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:51:57.70483+00:00
-- url     : https://prove2.me/submissions/a3df41b8-03de-4e1e-811e-1fe4cb6d30aa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsImagQuadIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PrimeIdealsCountingBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumLamIdealLe
import Theorems.Thm_GlobalTheory_Hk_LamRay_pow_prime_norm
import Theorems.Thm_GlobalTheory_IsKroneckerChar_ne_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LamRay
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.LamRay
theorem _root_.solution (hK : Module.finrank ℚ K = 2) (n : ℕ) (S : Finset (Ideal (𝓞 K)))
    (hS : ∀ I ∈ S, Ideal.absNorm I = n) : ∑ I ∈ S, lamIdeal I ≤ 2 * Λ n := by
  set T := S.filter (fun I => ∃ (P : Ideal (𝓞 K)) (k : ℕ), P.IsPrime ∧ P ≠ ⊥ ∧ 1 ≤ k ∧ I = P ^ k) with hT
  have e : ∑ I ∈ S, lamIdeal I = ∑ I ∈ T, Real.log (Ideal.absNorm I.radical) := by
    rw [hT, Finset.sum_filter]
    rfl
  rw [e]
  rcases T.eq_empty_or_nonempty with h | ⟨I₀, hI₀⟩
  · rw [h, Finset.sum_empty]
    exact mul_nonneg zero_le_two vonMangoldt_nonneg
  have key : ∀ I ∈ T, IsPrimePow n ∧ I.radical.IsPrime ∧ I.radical ≠ ⊥ ∧
      I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} ∧ 1 < Ideal.absNorm I.radical ∧ ∃ k, I = I.radical ^ k := by
    intro I hI
    obtain ⟨hIS, P, k, hP, h0, hk, rfl⟩ := Finset.mem_filter.1 hI
    have h := pow_prime_norm hK hP h0 hk
    rw [hS _ hIS] at h
    rw [Ideal.radical_pow _ (by omega), hP.radical]
    exact ⟨h.1, hP, h0, h.2.1, h.2.2, k, rfl⟩
  have hn := (key I₀ hI₀).1
  have hp : n.minFac.Prime := Nat.minFac_prime hn.ne_one
  have hdvd : ∏ I ∈ T, I.radical ∣ Ideal.span {(n.minFac : 𝓞 K)} := by
    refine Finset.prod_dvd_of_coprime (fun I hI J hJ hIJ => ?_) (fun I hI => (key I hI).2.2.2.1)
    obtain ⟨-, a1, a2, -, a3, k, a4⟩ := key I hI
    obtain ⟨-, b1, b2, -, -, l, b4⟩ := key J hJ
    refine Ideal.isCoprime_iff_sup_eq.2 ((a1.isMaximal a2).coprime_of_ne (b1.isMaximal b2) fun h => hIJ ?_)
    have c1 := hS I (Finset.mem_filter.1 hI).1
    have c2 := hS J (Finset.mem_filter.1 hJ).1
    rw [a4, map_pow] at c1
    rw [b4, map_pow, ← h] at c2
    have := Nat.pow_right_injective a3 (c1.trans c2.symm)
    rw [a4, b4, ← h, this]
  have h2 : ∏ I ∈ T, Ideal.absNorm I.radical ∣ n.minFac ^ 2 := by
    have := map_dvd Ideal.absNorm hdvd
    rwa [map_prod, Ideal.absNorm_span_natCast, RingOfIntegers.rank, hK] at this
  have h3 : ((∏ I ∈ T, Ideal.absNorm I.radical : ℕ) : ℝ) ≤ (n.minFac ^ 2 : ℕ) :=
    Nat.cast_le.2 (Nat.le_of_dvd (pow_pos hp.pos 2) h2)
  have hpos : ∀ I ∈ T, (0 : ℝ) < Ideal.absNorm I.radical := fun I hI =>
    Nat.cast_pos.2 (lt_trans one_pos (key I hI).2.2.2.2.1)
  push_cast at h3
  rw [← Real.log_prod (fun I hI => (hpos I hI).ne'), vonMangoldt_apply, if_pos hn]
  have h4 := Real.log_le_log (Finset.prod_pos hpos) h3
  rw [Real.log_pow] at h4
  exact_mod_cast h4
end GlobalTheory.Hk.LamRay
