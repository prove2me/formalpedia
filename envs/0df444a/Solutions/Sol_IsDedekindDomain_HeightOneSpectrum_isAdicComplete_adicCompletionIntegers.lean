-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.isAdicComplete_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/dbe969b3-baef-5139-8941-d23d07015773

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers

set_option autoImplicit false
universe u v
open IsDedekindDomain
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

theorem solution
    {R : Type u} [CommRing R] [IsDedekindDomain R] (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) (v.adicCompletionIntegers K) := by
  classical
  have hv : (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).Integers (v.adicCompletionIntegers K) :=
    Valuation.valuationSubring.integers _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hball : ∀ n : ℕ, ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n : Ideal (v.adicCompletionIntegers K)) :
      Set (v.adicCompletionIntegers K)) = {y : v.adicCompletionIntegers K | Valued.v (y : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n} :=
    fun n => hv.maximalIdeal_pow_eq_setOf_le_v_algebraMap_pow hϖ n
  have hmem : ∀ (n : ℕ) (y : v.adicCompletionIntegers K), y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (y : v.adicCompletion K) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := fun n y => by
    rw [← SetLike.mem_coe, hball n]; rfl
  have hsmod : ∀ (n : ℕ) (x y : v.adicCompletionIntegers K),
      x ≡ y [SMOD (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n • ⊤ : Submodule (v.adicCompletionIntegers K) (v.adicCompletionIntegers K))] ↔
        Valued.v ((x : v.adicCompletion K) - y) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
    intro n x y
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hmem]
    rfl
  have hvϖ0 : Valued.v (ϖ : v.adicCompletion K) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    intro h; apply hϖ.ne_zero; exact Subtype.ext h
  have hvϖ1 : Valued.v (ϖ : v.adicCompletion K) < 1 := hv.valuation_irreducible_lt_one hϖ

  have hsmall : ∀ γ : WithZero (Multiplicative ℤ), γ ≠ 0 → ∃ n : ℕ, Valued.v (ϖ : v.adicCompletion K) ^ n < γ := by
    intro γ hγ
    set t := Valued.v (ϖ : v.adicCompletion K) with ht
    have hlt : WithZero.log t < 0 := by
      rw [← WithZero.exp_lt_exp (G := ℤ) (a := WithZero.log t), WithZero.exp_log hvϖ0, WithZero.exp_zero]
      exact hvϖ1
    refine ⟨(WithZero.log γ).natAbs + 1, ?_⟩
    rw [← WithZero.exp_log hvϖ0, ← WithZero.exp_nsmul]
    conv_rhs => rw [← WithZero.exp_log hγ]
    rw [WithZero.exp_lt_exp]
    have hle := Int.le_natAbs (a := -WithZero.log γ)
    rw [Int.natAbs_neg] at hle
    rw [nsmul_eq_mul]
    have h1 : (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * WithZero.log t ≤ (((WithZero.log γ).natAbs + 1 : ℕ) : ℤ) * (-1) :=
      Int.mul_le_mul_of_nonneg_left (by omega) (by positivity)
    push_cast at h1 hle ⊢
    linarith
  refine { haus' := fun x hx => ?_, prec' := fun f hf => ?_ }
  ·
    apply Subtype.ext
    show (x : v.adicCompletion K) = 0
    rw [← (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).zero_iff]
    by_contra h0
    obtain ⟨n, hn⟩ := hsmall _ h0
    have := (hsmod n x 0).1 (hx n)
    rw [ZeroMemClass.coe_zero, sub_zero] at this
    exact absurd (lt_of_le_of_lt this hn) (lt_irrefl _)
  ·
    let g : ℕ → v.adicCompletion K := fun n => (f n : v.adicCompletion K)
    have hfg : ∀ {m n : ℕ}, m ≤ n → Valued.v (g m - g n) ≤ Valued.v (ϖ : v.adicCompletion K) ^ m :=
      fun {m n} hmn => (hsmod m (f m) (f n)).1 (hf hmn)
    have hcauchy : CauchySeq g := by
      rw [(Valued.hasBasis_uniformity (v.adicCompletion K) (WithZero (Multiplicative ℤ))).cauchySeq_iff]
      intro γ _
      obtain ⟨N, hN⟩ := hsmall (MonoidWithZeroHom.ValueGroup₀.embedding γ.1) (by
        intro h0
        exact γ.ne_zero (MonoidWithZeroHom.ValueGroup₀.embedding_strictMono.injective (h0.trans (map_zero _).symm)))
      refine ⟨N, fun m hm n hn => ?_⟩
      show Valued.v.restrict (g n - g m) < γ.1
      rw [Valuation.restrict_lt_iff_lt_embedding, Valuation.map_sub_swap]
      calc Valued.v (g m - g n) = Valued.v (g m - g N + (g N - g n)) := by rw [sub_add_sub_cancel]
        _ ≤ max (Valued.v (g m - g N)) (Valued.v (g N - g n)) := Valuation.map_add _ _ _
        _ ≤ Valued.v (ϖ : v.adicCompletion K) ^ N := by
            refine max_le ?_ (hfg hn)
            rw [Valuation.map_sub_swap]; exact hfg hm
        _ < _ := hN
    obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy

    have hclosed : ∀ (c : WithZero (Multiplicative ℤ)) (a : v.adicCompletion K), IsClosed {y : v.adicCompletion K | Valued.v (a - y) ≤ c} := by
      intro c a
      rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
      intro y hy
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hy
      rw [Valued.mem_nhds]
      have hy0 : Valued.v (a - y) ≠ 0 := ne_of_gt (lt_of_le_of_lt zero_le' hy)
      refine ⟨Units.mk0 (Valued.v.restrict (a - y)) (fun h => hy0 ((Valuation.restrict_eq_zero_iff Valued.v).1 h)), fun z hz => ?_⟩
      simp only [Set.mem_setOf_eq, Units.val_mk0, Valuation.restrict_lt_iff] at hz
      simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
      have : Valued.v (a - z) = Valued.v (a - y) := by
        have h := Valuation.map_add_eq_of_lt_left Valued.v (x := a - y) (y := -(z - y)) (by rwa [Valuation.map_neg])
        rwa [← sub_eq_add_neg, sub_sub_sub_cancel_right] at h
      rwa [this]
    have hLmem : ∀ n : ℕ, Valued.v (g n - L) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n := by
      intro n
      have hev : ∀ᶠ m in Filter.atTop, g m ∈ {y : v.adicCompletion K | Valued.v (g n - y) ≤ Valued.v (ϖ : v.adicCompletion K) ^ n} :=
        Filter.eventually_atTop.2 ⟨n, fun m hm => hfg hm⟩
      exact (hclosed _ (g n)).mem_of_tendsto hL hev
    have hL1 : Valued.v L ≤ 1 := by
      have h0 := hLmem 0
      rw [pow_zero] at h0
      calc Valued.v L = Valued.v (g 0 - (g 0 - L)) := by rw [sub_sub_cancel]
        _ ≤ max (Valued.v (g 0)) (Valued.v (g 0 - L)) := Valuation.map_sub _ _ _
        _ ≤ 1 := max_le (f 0).2 h0
    refine ⟨⟨L, hL1⟩, fun n => ?_⟩
    rw [hsmod]
    exact hLmem n

end S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_isAdicComplete_adicCompletionIntegers (solution)
