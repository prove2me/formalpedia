-- Prove2me | solution 1 for GuthMaynard.Affine.lintegral_Wnear_sq_le_Sig
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-06T00:14:17.077903+00:00
-- url     : https://prove2.me/submissions/532c1e28-ea8c-4860-9eb8-ff17aff35aa0

import Mathlib
import Definitions.Def_GuthMaynard
import Definitions.Def_GuthMaynardAffine
section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal


end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartT
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine.PartT
end

section
namespace GuthMaynard.Affine
open GuthMaynard MeasureTheory FourierTransform Complex
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-! ## Fixed objects -/


























theorem ψ₁_nonneg (K x : ℝ) : 0 ≤ ψ₁ K x := (ψb K).nonneg

theorem adm_continuous {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    Continuous f :=
  hf.smooth.continuous

theorem adm_hasCompactSupport {C : ℝ} {c : ℕ → ℝ → ℝ} {T : ℝ} {f : ℝ → ℝ} (hf : Adm C c T f) :
    HasCompactSupport f :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport f)
    (closure_minimal hf.supp isClosed_Icc)

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem B₀_nonneg (K : ℝ) : 0 ≤ B₀ K :=
  integral_nonneg fun _ => ψ₁_nonneg _ _

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

alias B₀_nonneg := GuthMaynard.Affine.PartB.B₀_nonneg

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem mem_dyadic_bounds {M : ℝ} {m : ℤ} (h : m ∈ dyadic M) : M < m ∧ (m : ℝ) ≤ 2 * M := by
  simp only [dyadic, Finset.mem_Ioc] at h
  obtain ⟨h1, h2⟩ := h
  constructor
  · have : ⌊M⌋ + 1 ≤ m := h1
    have h3 : M < (⌊M⌋ : ℝ) + 1 := Int.lt_floor_add_one M
    have : ((⌊M⌋ + 1 : ℤ) : ℝ) ≤ m := by exact_mod_cast this
    push_cast at this; linarith
  · have : (m : ℝ) ≤ (⌊2 * M⌋ : ℝ) := by exact_mod_cast h2
    linarith [Int.floor_le (2 * M)]

theorem card_dyadic_le {M : ℝ} (hM : 0 ≤ M) : ((dyadic M).card : ℝ) ≤ M + 1 := by
  simp only [dyadic, Int.card_Ioc]
  have h1 : (⌊2 * M⌋ : ℝ) ≤ 2 * M := Int.floor_le _
  have h2 : M - 1 < (⌊M⌋ : ℝ) := Int.sub_one_lt_floor _
  rcases le_or_gt (⌊2 * M⌋ - ⌊M⌋) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊2 * M⌋ - ⌊M⌋).toNat : ℤ) : ℝ) = (⌊2 * M⌋ : ℝ) - ⌊M⌋ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem half_le_of_dyadic_nonempty {M : ℝ} (h : (dyadic M).Nonempty) : 1 / 2 ≤ M := by
  obtain ⟨m, hm⟩ := h
  obtain ⟨h1, h2⟩ := mem_dyadic_bounds hm
  have hm0 : (0 : ℝ) < m := by linarith
  have : (1 : ℤ) ≤ m := by exact_mod_cast hm0
  have : (1 : ℝ) ≤ m := by exact_mod_cast this
  linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem abs_of_mem_D₁ {M₁ : ℝ} {m : ℤ} (h : m ∈ D₁ M₁) : M₁ < |(m : ℝ)| ∧ |(m : ℝ)| ≤ 2 * M₁ := by
  simp only [D₁, Finset.mem_union, Finset.mem_map, Equiv.coe_toEmbedding, Equiv.neg_apply] at h
  rcases h with h | ⟨n, hn, rfl⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic_bounds h
    have hM := half_le_of_dyadic_nonempty ⟨m, h⟩
    rw [abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩
  · obtain ⟨h1, h2⟩ := mem_dyadic_bounds hn
    have hM := half_le_of_dyadic_nonempty ⟨n, hn⟩
    push_cast
    rw [abs_neg, abs_of_nonneg (by linarith)]; exact ⟨h1, h2⟩

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias abs_of_mem_D₁ := GuthMaynard.Affine.PartB.abs_of_mem_D₁

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem card_D₁_le {M₁ : ℝ} (h : 1 / 2 ≤ M₁) : ((D₁ M₁).card : ℝ) ≤ 6 * M₁ := by
  have h1 : (D₁ M₁).card ≤ (dyadic M₁).card + (dyadic M₁).card := by
    unfold D₁
    refine (Finset.card_union_le _ _).trans ?_
    rw [Finset.card_map]
  have h2 := card_dyadic_le (M := M₁) (by linarith)
  have h3 : ((D₁ M₁).card : ℝ) ≤ (dyadic M₁).card + (dyadic M₁).card := by exact_mod_cast h1
  linarith

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem sum_inv_abs_D₁_le {M₁ : ℝ} (h : 1 / 2 ≤ M₁) :
    ∑ m ∈ D₁ M₁, 1 / |(m : ℝ)| ≤ 6 := by
  have hM : 0 < M₁ := by linarith
  calc ∑ m ∈ D₁ M₁, 1 / |(m : ℝ)| ≤ ∑ m ∈ D₁ M₁, 1 / M₁ := by
        refine Finset.sum_le_sum fun m hm => ?_
        exact one_div_le_one_div_of_le hM (abs_of_mem_D₁ hm).1.le
    _ = (D₁ M₁).card * (1 / M₁) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 6 * M₁ * (1 / M₁) := mul_le_mul_of_nonneg_right (card_D₁_le h) (by positivity)
    _ = 6 := by field_simp

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias sum_inv_abs_D₁_le := GuthMaynard.Affine.PartB.sum_inv_abs_D₁_le

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem mem_nearSet {x r : ℝ} {j : ℤ} : j ∈ nearSet x r ↔ |(j : ℝ) - x| ≤ r := by
  simp only [nearSet, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

theorem card_nearSet_le (x : ℝ) {r : ℝ} (hr : 0 ≤ r) : ((nearSet x r).card : ℝ) ≤ 2 * r + 1 := by
  simp only [nearSet, Int.card_Icc]
  have h1 : (⌊x + r⌋ : ℝ) ≤ x + r := Int.floor_le _
  have h2 : x - r ≤ (⌈x - r⌉ : ℝ) := Int.le_ceil _
  rcases le_or_gt (⌊x + r⌋ + 1 - ⌈x - r⌉) 0 with h | h
  · rw [Int.toNat_of_nonpos h]; simp; linarith
  · have : (((⌊x + r⌋ + 1 - ⌈x - r⌉).toNat : ℤ) : ℝ) = (⌊x + r⌋ : ℝ) + 1 - ⌈x - r⌉ := by
      rw [Int.toNat_of_nonneg h.le]; push_cast; ring
    rw [← Int.cast_natCast, this]
    linarith

/-- One prime power: `a + 1 ≤ g · p^{aε}` with `g = 1` once `p ≥ N`, `2^{1/ε} ≤ N`. -/
theorem prime_pow_bound {ε : ℝ} (hε : 0 < ε) {N : ℕ} (hN : (2 : ℝ) ^ (1 / ε) ≤ N) {p : ℕ}
    (hp : 2 ≤ p) (a : ℕ) :
    ((a : ℝ) + 1) ≤ (if p < N then 1 + 1 / (ε * Real.log 2) else 1) * (p : ℝ) ^ ((a : ℝ) * ε) := by
  have hp0 : (0 : ℝ) < p := by positivity
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hrw : (p : ℝ) ^ ((a : ℝ) * ε) = ((p : ℝ) ^ ε) ^ a := by
    rw [mul_comm, Real.rpow_mul hp0.le, Real.rpow_natCast]
  split_ifs with h
  · set δ := ε * Real.log 2 with hδ
    have hδ0 : 0 < δ := mul_pos hε (Real.log_pos one_lt_two)
    have h1 : 1 + (a : ℝ) * δ ≤ (p : ℝ) ^ ((a : ℝ) * ε) := by
      calc 1 + (a : ℝ) * δ ≤ Real.exp ((a : ℝ) * δ) := by
            linarith [Real.add_one_le_exp ((a : ℝ) * δ)]
        _ = (2 : ℝ) ^ ((a : ℝ) * ε) := by
            rw [Real.rpow_def_of_pos two_pos, hδ]; ring_nf
        _ ≤ (p : ℝ) ^ ((a : ℝ) * ε) :=
            Real.rpow_le_rpow (by norm_num) hp2 (by positivity)
    have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc ((a : ℝ) + 1) ≤ (1 + 1 / δ) * (1 + (a : ℝ) * δ) := by
          have : (1 + 1 / δ) * (1 + (a : ℝ) * δ) = 1 + a * δ + 1 / δ + a := by
            field_simp; ring
          rw [this]; have : 0 ≤ 1 / δ := by positivity
          nlinarith [mul_pos hδ0 hδ0]
      _ ≤ _ := mul_le_mul_of_nonneg_left h1 (by positivity)
  · push Not at h
    have hpN : (N : ℝ) ≤ p := by exact_mod_cast h
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ ε := by
      calc (2 : ℝ) = ((2 : ℝ) ^ (1 / ε)) ^ ε := by
            rw [← Real.rpow_mul (by norm_num), one_div_mul_cancel hε.ne', Real.rpow_one]
        _ ≤ (p : ℝ) ^ ε := Real.rpow_le_rpow (by positivity) (hN.trans hpN) hε.le
    rw [one_mul, hrw]
    calc ((a : ℝ) + 1) = 1 + a * 1 := by ring
      _ ≤ (1 + 1) ^ a := one_add_mul_le_pow (by norm_num) a
      _ = 2 ^ a := by norm_num
      _ ≤ ((p : ℝ) ^ ε) ^ a := pow_le_pow_left₀ (by norm_num) h2 a

theorem divisor_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ Cε : ℝ, ∀ n : ℕ, 1 ≤ n → (n.divisors.card : ℝ) ≤ Cε * (n : ℝ) ^ ε := by
  obtain ⟨N, hN⟩ := exists_nat_ge ((2 : ℝ) ^ (1 / ε))
  set K : ℝ := 1 + 1 / (ε * Real.log 2) with hK
  have hK1 : 1 ≤ K := by
    have : 0 < ε * Real.log 2 := mul_pos hε (Real.log_pos one_lt_two)
    rw [hK]; have : 0 ≤ 1 / (ε * Real.log 2) := by positivity
    linarith
  refine ⟨K ^ N, fun n hn => ?_⟩
  have hn0 : n ≠ 0 := by omega
  set g : ℕ → ℝ := fun p => if p < N then K else 1 with hg
  have hg1 : ∀ p, 1 ≤ g p := fun p => by simp only [hg]; split_ifs <;> linarith
  have hcard : (n.divisors.card : ℝ) = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
    rw [Nat.card_divisors hn0]; push_cast; rfl
  have hn : (n : ℝ) ^ ε = ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hn0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
    push_cast
    rw [← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hstep : ∀ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) ≤
      g p * (p : ℝ) ^ ((n.factorization p : ℝ) * ε) := by
    intro p hp
    have := prime_pow_bound hε hN (Nat.prime_of_mem_primeFactors hp).two_le (n.factorization p)
    simpa [hg, hK] using this
  have hgprod : ∏ p ∈ n.primeFactors, g p ≤ K ^ N := by
    calc ∏ p ∈ n.primeFactors, g p
        = (∏ p ∈ n.primeFactors.filter (· < N), K) *
            ∏ p ∈ n.primeFactors.filter (fun p => ¬ p < N), (1 : ℝ) := by
          rw [← Finset.prod_filter_mul_prod_filter_not _ (· < N)]
          congr 1
          · exact Finset.prod_congr rfl fun p hp => by simp [hg, (Finset.mem_filter.1 hp).2]
          · exact Finset.prod_congr rfl fun p hp => by simp [hg, (Finset.mem_filter.1 hp).2]
      _ ≤ K ^ N := by
          rw [Finset.prod_const_one, mul_one, Finset.prod_const]
          refine pow_le_pow_right₀ hK1 ?_
          calc (n.primeFactors.filter (· < N)).card
              ≤ (Finset.range N).card := Finset.card_le_card fun p hp => by
                simpa using (Finset.mem_filter.1 hp).2
            _ = N := Finset.card_range N
  rw [hcard, hn]
  calc ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1)
      ≤ ∏ p ∈ n.primeFactors, (g p * (p : ℝ) ^ ((n.factorization p : ℝ) * ε)) :=
        Finset.prod_le_prod (fun p _ => by positivity) hstep
    _ = (∏ p ∈ n.primeFactors, g p) * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        Finset.prod_mul_distrib
    _ ≤ K ^ N * ∏ p ∈ n.primeFactors, (p : ℝ) ^ ((n.factorization p : ℝ) * ε) :=
        mul_le_mul_of_nonneg_right hgprod (Finset.prod_nonneg fun p _ => by positivity)

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

/-! ### Large `M`: Lipschitz bound, mass lower bound, Riemann sums -/

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartS
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform Complex
open scoped ENNReal Convolution SchwartzMap RealInnerProductSpace

end GuthMaynard.Affine.PartS
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem Ffun_mul_eq (M₂ : ℝ) (f : ℝ → ℝ) {m₁ : ℤ} (hm₁ : m₁ ≠ 0) (y : ℝ) :
    Ffun M₂ f m₁ (m₁ * y) = Γfun M₂ f y / ((|(m₁ : ℝ)| : ℝ) : ℂ) := by
  have h1 : (m₁ : ℝ) ≠ 0 := by exact_mod_cast hm₁
  have h2 : ((|(m₁ : ℝ)| : ℝ) : ℂ) ≠ 0 := by
    rw [Complex.ofReal_ne_zero]; exact abs_ne_zero.2 h1
  unfold Ffun Γfun
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl fun m₂ _ => ?_
  have : (m₁ : ℝ) * y * m₂ / m₁ = m₂ * y := by field_simp
  rw [this]
  push_cast
  field_simp

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartG
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartG
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

alias Ffun_mul_eq := GuthMaynard.Affine.PartG.Ffun_mul_eq

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartB
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
/-- The pairs `(m₁, ℓ)` with `m₁ ℓ = s ≠ 0` number at most `2 d(|s|)`. -/
theorem card_fiber_le (P : Finset (Σ _ : ℤ, ℤ)) (s : ℤ) (hs : s ≠ 0) :
    (P.filter (fun q => q.1 * q.2 = s)).card ≤ 2 * s.natAbs.divisors.card := by
  set D : Finset ℤ := (s.natAbs.divisors).map Nat.castEmbedding with hD
  have hDc : D.card = s.natAbs.divisors.card := Finset.card_map _
  calc (P.filter (fun q => q.1 * q.2 = s)).card
      ≤ (D ∪ D.map (Equiv.neg ℤ).toEmbedding).card := by
        refine Finset.card_le_card_of_injOn (fun q => q.1) ?_ ?_
        · intro q hq
          have hq := (Finset.mem_filter.1 hq).2
          have hdvd : q.1.natAbs ∣ s.natAbs := by
            rw [← hq, Int.natAbs_mul]; exact Dvd.intro _ rfl
          have hmem : q.1.natAbs ∈ s.natAbs.divisors :=
            Nat.mem_divisors.2 ⟨hdvd, Int.natAbs_ne_zero.2 hs⟩
          simp only [Finset.coe_union, Finset.coe_map, Set.mem_union, Set.mem_image,
            Finset.mem_coe, hD, Nat.castEmbedding_apply, Equiv.neg_apply,
            Function.Embedding.coeFn_mk]
          rcases Int.natAbs_eq q.1 with h | h
          · left; exact ⟨_, hmem, h.symm⟩
          · right; refine ⟨(q.1.natAbs : ℤ), ⟨_, hmem, rfl⟩, ?_⟩
            rw [h]; simp
        · intro q hq q' hq' hqq
          have h1 := (Finset.mem_filter.1 hq).2
          have h2 := (Finset.mem_filter.1 hq').2
          simp only at hqq
          have hne : q.1 ≠ 0 := by rintro h; rw [h, zero_mul] at h1; exact hs h1.symm
          have : q.2 = q'.2 := by
            rw [← hqq] at h2
            exact mul_left_cancel₀ hne (h1.trans h2.symm)
          rcases q with ⟨a, b⟩; rcases q' with ⟨a', b'⟩
          simp only at hqq this; subst hqq; subst this; rfl
    _ ≤ D.card + (D.map (Equiv.neg ℤ).toEmbedding).card := Finset.card_union_le _ _
    _ = 2 * s.natAbs.divisors.card := by simp only [hD, Finset.card_map]; ring

theorem sum_card_nearSet_le (η : ℝ) (hη : 0 < η) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ T : ℝ, 1 ≤ T → ∀ M₁ M₃ : ℝ, 1 / 2 ≤ M₁ → 0 < M₃ →
      ∀ ξ ∈ regII T η M₁ M₃,
        (∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) (T ^ η / M₃)).card : ℝ)) ≤
          A * T ^ η * (4 * T ^ η * M₁ / M₃ + 1) := by
  have hε : 0 < η / 20 := by positivity
  obtain ⟨Cε, hC⟩ := divisor_bound (η / 20) hε
  set C' := max Cε 0 with hC'
  refine ⟨2 * C' * 2 ^ (η / 20), by positivity, fun T hT M₁ M₃ hM₁ hM₃ ξ hξ => ?_⟩
  obtain ⟨hξ1, hξ2⟩ := hξ
  have hT0 : 0 < T := by linarith
  set Q := T ^ η with hQ
  have hQ0 : 0 < Q := Real.rpow_pos_of_pos hT0 η
  have hM₁0 : 0 < M₁ := by linarith
  set R := 4 * Q * M₁ / M₃ with hR
  have hR0 : 0 < R := by positivity
  set r := Q / M₃ with hr
  set P : Finset (Σ _ : ℤ, ℤ) := (D₁ M₁).sigma (fun m₁ => nearSet (ξ / m₁) r) with hP
  set S := nearSet ξ (R / 2) with hS
  have hPcard : ∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) r).card : ℝ) = P.card := by
    rw [hP, Finset.card_sigma]; push_cast; rfl
  -- every pair lands in `S`, and its product is nonzero with `|s| ≤ 2 T²⁰`
  have hmaps : ∀ q ∈ P, q.1 * q.2 ∈ S := by
    intro q hq
    rw [hP, Finset.mem_sigma] at hq
    obtain ⟨h1, h2⟩ := hq
    rw [mem_nearSet] at h2
    obtain ⟨hm1, hm2⟩ := abs_of_mem_D₁ h1
    have hm0 : (q.1 : ℝ) ≠ 0 := by intro h; rw [h, abs_zero] at hm1; linarith
    rw [hS, mem_nearSet]
    push_cast
    have : (q.1 : ℝ) * q.2 - ξ = q.1 * ((q.2 : ℝ) - ξ / q.1) := by field_simp
    rw [this, abs_mul]
    calc |(q.1 : ℝ)| * |(q.2 : ℝ) - ξ / q.1| ≤ (2 * M₁) * r :=
          mul_le_mul hm2 h2 (abs_nonneg _) (by positivity)
      _ = R / 2 := by rw [hR, hr]; field_simp; ring
  have hSbound : ∀ s ∈ S, s ≠ 0 ∧ (s.natAbs : ℝ) ≤ 2 * T ^ (20 : ℕ) := by
    intro s hs
    rw [hS, mem_nearSet] at hs
    have habs : |(s : ℝ)| = (s.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
    have h1 : R / 2 < |(s : ℝ)| := by
      have := abs_sub_abs_le_abs_sub ξ (s : ℝ)
      rw [abs_sub_comm] at this; linarith
    refine ⟨?_, ?_⟩
    · rintro rfl; simp at h1; linarith
    · rw [← habs]
      have := abs_sub_abs_le_abs_sub (s : ℝ) ξ
      have hRT : R < T ^ (20 : ℕ) := lt_of_lt_of_le hξ1 (by exact_mod_cast hξ2)
      linarith
  have hfib : ∀ s ∈ S, ((P.filter (fun q => q.1 * q.2 = s)).card : ℝ) ≤
      2 * C' * 2 ^ (η / 20) * Q := by
    intro s hs
    obtain ⟨hs0, hsT⟩ := hSbound s hs
    have h1 : ((P.filter (fun q => q.1 * q.2 = s)).card : ℝ) ≤ 2 * s.natAbs.divisors.card := by
      exact_mod_cast card_fiber_le P s hs0
    have h2 := hC s.natAbs (Int.natAbs_pos.2 hs0)
    have h3 : (s.natAbs : ℝ) ^ (η / 20) ≤ 2 ^ (η / 20) * Q := by
      calc (s.natAbs : ℝ) ^ (η / 20) ≤ (2 * T ^ (20 : ℕ)) ^ (η / 20) :=
            Real.rpow_le_rpow (by positivity) hsT hε.le
        _ = 2 ^ (η / 20) * Q := by
            rw [Real.mul_rpow (by norm_num) (by positivity), hQ, ← Real.rpow_natCast,
              ← Real.rpow_mul hT0.le]
            congr 2; push_cast; ring
    have h4 : (s.natAbs.divisors.card : ℝ) ≤ C' * (2 ^ (η / 20) * Q) :=
      h2.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left h3 (le_max_right _ _)))
    calc ((P.filter (fun q => q.1 * q.2 = s)).card : ℝ) ≤ 2 * s.natAbs.divisors.card := h1
      _ ≤ 2 * (C' * (2 ^ (η / 20) * Q)) := by linarith
      _ = 2 * C' * 2 ^ (η / 20) * Q := by ring
  -- double counting
  have hcount : (P.card : ℝ) ≤ ∑ s ∈ S, ((P.filter (fun q => q.1 * q.2 = s)).card : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise (f := fun q : (Σ _ : ℤ, ℤ) => q.1 * q.2) hmaps
    exact_mod_cast this.le
  have hScard : (S.card : ℝ) ≤ R + 1 := by
    have := card_nearSet_le ξ (r := R / 2) (by positivity); linarith
  rw [hPcard]
  calc (P.card : ℝ) ≤ ∑ s ∈ S, ((P.filter (fun q => q.1 * q.2 = s)).card : ℝ) := hcount
    _ ≤ ∑ s ∈ S, 2 * C' * 2 ^ (η / 20) * Q := Finset.sum_le_sum hfib
    _ = S.card * (2 * C' * 2 ^ (η / 20) * Q) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (R + 1) * (2 * C' * 2 ^ (η / 20) * Q) :=
        mul_le_mul_of_nonneg_right hScard (by positivity)
    _ = 2 * C' * 2 ^ (η / 20) * Q * (R + 1) := by ring

end GuthMaynard.Affine.PartB
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
alias sum_card_nearSet_le := GuthMaynard.Affine.PartB.sum_card_nearSet_le

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem fhat_continuous {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f) :
    Continuous (fhat f) := by
  have hFi : Integrable (fun u => (f u : ℂ)) := (hf.integrable_of_hasCompactSupport hcs).ofReal
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (by fun_prop) hFi

theorem Ffun_continuous (M₂ : ℝ) {f : ℝ → ℝ} (hf : Continuous f) (hcs : HasCompactSupport f)
    (m₁ : ℤ) : Continuous (Ffun M₂ f m₁) := by
  unfold Ffun
  exact continuous_finsetSum _ fun m₂ _ =>
    continuous_const.mul ((fhat_continuous hf hcs).comp
      ((continuous_id.mul continuous_const).div_const _))

theorem mem_nearSet {x r : ℝ} {j : ℤ} : j ∈ nearSet x r ↔ |(j : ℝ) - x| ≤ r := by
  simp only [nearSet, Finset.mem_Icc, Int.ceil_le, Int.le_floor, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- Affine change of variables for `lintegral` on `ℝ`. -/
theorem lintegral_affine (h : ℝ → ℝ≥0∞) {a : ℝ} (ha : a ≠ 0) (b : ℝ) :
    ∫⁻ ξ, h ξ = ENNReal.ofReal |a| * ∫⁻ τ, h (a * τ + b) := by
  have e1 : ∫⁻ τ, h (a * τ + b) = ENNReal.ofReal |a⁻¹| * ∫⁻ x, h (x + b) := by
    have := lintegral_map_equiv (fun x => h (x + b))
      (Homeomorph.mulLeft₀ a ha).toMeasurableEquiv (μ := volume)
    simp only [Homeomorph.toMeasurableEquiv_coe, Homeomorph.coe_mulLeft₀] at this
    rw [← this, Real.map_volume_mul_left ha, lintegral_smul_measure, smul_eq_mul]
  rw [e1, lintegral_add_right_eq_self, ← mul_assoc, ← ENNReal.ofReal_mul (abs_nonneg _),
    ← abs_mul, mul_inv_cancel₀ ha, abs_one, ENNReal.ofReal_one, one_mul]

/-- The set `|ℓ - ξ/m₁| ≤ r`. -/
def Aset (r : ℝ) (m₁ ℓ : ℤ) : Set ℝ := {ξ | |(ℓ : ℝ) - ξ / m₁| ≤ r}

noncomputable def gF (M₂ : ℝ) (f : ℝ → ℝ) (m₁ : ℤ) (ξ : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖Ffun M₂ f m₁ ξ‖ ^ 2)

theorem card_mul_eq_tsum (r : ℝ) (m₁ : ℤ) (g : ℝ → ℝ≥0∞) (ξ : ℝ) :
    ((nearSet (ξ / m₁) r).card : ℝ≥0∞) * g ξ = ∑' ℓ : ℤ, (Aset r m₁ ℓ).indicator g ξ := by
  rw [tsum_eq_sum (s := nearSet (ξ / m₁) r) (fun ℓ hℓ => ?_)]
  · rw [Finset.sum_congr rfl (g := fun _ => g ξ) (fun ℓ hℓ => Set.indicator_of_mem
      (show ξ ∈ Aset r m₁ ℓ from mem_nearSet.1 hℓ) g), Finset.sum_const, nsmul_eq_mul]
  · exact Set.indicator_of_notMem (show ξ ∉ Aset r m₁ ℓ from fun h => hℓ (mem_nearSet.2 h)) g

theorem lintegral_near_le_Sig (M₁ M₂ M₃ Q : ℝ) (hM₁ : 1 / 2 ≤ M₁) (hM₃ : 0 < M₃) (hQ : 0 < Q)
    (f : ℝ → ℝ) (hf : Continuous f) (hcs : HasCompactSupport f) :
    ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|},
      ENNReal.ofReal (∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) *
        ‖Ffun M₂ f m₁ ξ‖ ^ 2) ≤
      ENNReal.ofReal (6 / M₃) * Sig Q M₂ M₃ f := by
  have hM₁0 : 0 < M₁ := by linarith
  have hg : ∀ m₁, Measurable (gF M₂ f m₁) := fun m₁ =>
    ENNReal.measurable_ofReal.comp (((Ffun_continuous M₂ hf hcs m₁).norm.pow 2).measurable)
  have hA : ∀ m₁ ℓ, MeasurableSet (Aset (Q / M₃) m₁ ℓ) := fun m₁ ℓ =>
    measurableSet_le (by fun_prop) measurable_const
  have hpt : ∀ ξ, ENNReal.ofReal (∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) *
        ‖Ffun M₂ f m₁ ξ‖ ^ 2)
      = ∑ m₁ ∈ D₁ M₁, ∑' ℓ : ℤ, (Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁) ξ := by
    intro ξ
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, ← card_mul_eq_tsum]
    rfl
  have hterm : ∀ m₁ ∈ D₁ M₁, ∀ ℓ : ℤ,
      ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|}, (Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁) ξ ≤
        ENNReal.ofReal (1 / (|(m₁ : ℝ)| * M₃)) *
          (if ℓ = 0 then 0 else SigTerm Q M₂ M₃ f ℓ) := by
    intro m₁ hm ℓ
    obtain ⟨hlo, hhi⟩ := abs_of_mem_D₁ hm
    have hm0 : (m₁ : ℝ) ≠ 0 := by intro h; rw [h, abs_zero] at hlo; linarith
    have hm0' : m₁ ≠ 0 := by exact_mod_cast hm0
    have ha : (m₁ : ℝ) / M₃ ≠ 0 := div_ne_zero hm0 hM₃.ne'
    have hS : MeasurableSet {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|} :=
      measurableSet_lt measurable_const measurable_abs
    rw [← lintegral_indicator hS, lintegral_affine _ ha ((m₁ : ℝ) * ℓ)]
    have hpt : ∀ τ : ℝ, {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|}.indicator
        ((Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁)) ((m₁ : ℝ) / M₃ * τ + m₁ * ℓ) ≤
        ENNReal.ofReal (1 / (m₁ : ℝ) ^ 2) * (if ℓ = 0 then 0 else
          {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|}.indicator
            (fun τ => ‖Γfun M₂ f (ℓ + τ / M₃)‖ₑ ^ 2) τ) := by
      intro τ
      have hy : (m₁ : ℝ) / M₃ * τ + m₁ * ℓ = m₁ * (ℓ + τ / M₃) := by
        field_simp; ring
      rw [hy]
      by_cases hin : 4 * Q * M₁ / M₃ < |(m₁ : ℝ) * (ℓ + τ / M₃)| ∧
          |(ℓ : ℝ) - m₁ * (ℓ + τ / M₃) / m₁| ≤ Q / M₃
      · obtain ⟨h1, h2⟩ := hin
        have h2' : |τ| ≤ Q := by
          rw [mul_div_cancel_left₀ _ hm0, sub_add_cancel_left, abs_neg, abs_div,
            abs_of_pos hM₃] at h2
          exact (div_le_div_iff_of_pos_right hM₃).1 h2
        have h1' : 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃| := by
          rw [abs_mul] at h1
          by_contra hc
          push Not at hc
          have h3 : |(m₁ : ℝ)| * |(ℓ : ℝ) + τ / M₃| ≤ 2 * M₁ * (2 * Q / M₃) :=
            mul_le_mul hhi hc.le (abs_nonneg _) (by linarith)
          have h4 : 2 * M₁ * (2 * Q / M₃) = 4 * Q * M₁ / M₃ := by ring
          linarith
        have hℓ : ℓ ≠ 0 := by
          rintro rfl
          rw [Int.cast_zero, zero_add, abs_div, abs_of_pos hM₃] at h1'
          have := (div_le_div_iff_of_pos_right hM₃).1 h1'
          linarith
        rw [if_neg hℓ, Set.indicator_of_mem (show _ ∈ {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|} from h1),
          Set.indicator_of_mem (show _ ∈ Aset (Q / M₃) m₁ ℓ from h2),
          Set.indicator_of_mem (show τ ∈ {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|}
            from ⟨h2', h1'⟩)]
        simp only [gF]
        rw [Ffun_mul_eq M₂ f hm0', ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
          ← ENNReal.ofReal_mul (by positivity)]
        apply le_of_eq
        congr 1
        rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs, div_pow, sq_abs]
        ring
      · have h0 : {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|}.indicator
            ((Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁)) (m₁ * (ℓ + τ / M₃)) = 0 := by
          simp only [Set.indicator_apply, Set.mem_ofPred_eq, Aset]
          split_ifs with h1 h2 <;> first | rfl | exact absurd ⟨h1, h2⟩ hin
        rw [h0]
        exact zero_le
    calc ENNReal.ofReal |(m₁ : ℝ) / M₃| * ∫⁻ τ, {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|}.indicator
          ((Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁)) ((m₁ : ℝ) / M₃ * τ + m₁ * ℓ)
        ≤ ENNReal.ofReal |(m₁ : ℝ) / M₃| * ∫⁻ τ, ENNReal.ofReal (1 / (m₁ : ℝ) ^ 2) *
          (if ℓ = 0 then 0 else
          {τ : ℝ | |τ| ≤ Q ∧ 2 * Q / M₃ ≤ |(ℓ : ℝ) + τ / M₃|}.indicator
            (fun τ => ‖Γfun M₂ f (ℓ + τ / M₃)‖ₑ ^ 2) τ) := by
          gcongr with τ
          exact hpt τ
      _ ≤ ENNReal.ofReal (1 / (|(m₁ : ℝ)| * M₃)) *
          (if ℓ = 0 then 0 else SigTerm Q M₂ M₃ f ℓ) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← mul_assoc,
            ← ENNReal.ofReal_mul (abs_nonneg _)]
          have hc : |(m₁ : ℝ) / M₃| * (1 / (m₁ : ℝ) ^ 2) = 1 / (|(m₁ : ℝ)| * M₃) := by
            rw [abs_div, abs_of_pos hM₃, ← sq_abs]
            have : |(m₁ : ℝ)| ≠ 0 := abs_ne_zero.2 hm0
            field_simp
          rw [hc]
          gcongr
          by_cases hℓ : ℓ = 0
          · simp [hℓ]
          · simp only [if_neg hℓ]
            exact lintegral_indicator_le _ _
  calc _ = ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|},
          ∑ m₁ ∈ D₁ M₁, ∑' ℓ : ℤ, (Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁) ξ :=
        lintegral_congr fun ξ => hpt ξ
    _ = ∑ m₁ ∈ D₁ M₁, ∑' ℓ : ℤ, ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|},
          (Aset (Q / M₃) m₁ ℓ).indicator (gF M₂ f m₁) ξ := by
        rw [lintegral_finsetSum' _ fun m₁ _ =>
          (Measurable.tsum fun ℓ => (hg m₁).indicator (hA m₁ ℓ)).aemeasurable]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        exact lintegral_tsum fun ℓ => ((hg m₁).indicator (hA m₁ ℓ)).aemeasurable
    _ ≤ ∑ m₁ ∈ D₁ M₁, ∑' ℓ : ℤ, ENNReal.ofReal (1 / (|(m₁ : ℝ)| * M₃)) *
          (if ℓ = 0 then 0 else SigTerm Q M₂ M₃ f ℓ) :=
        Finset.sum_le_sum fun m₁ hm => ENNReal.tsum_le_tsum fun ℓ => hterm m₁ hm ℓ
    _ = (∑ m₁ ∈ D₁ M₁, ENNReal.ofReal (1 / (|(m₁ : ℝ)| * M₃))) * Sig Q M₂ M₃ f := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun m₁ _ => ?_
        rw [ENNReal.tsum_mul_left]; rfl
    _ ≤ ENNReal.ofReal (6 / M₃) * Sig Q M₂ M₃ f := by
        gcongr
        rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => by positivity)]
        apply ENNReal.ofReal_le_ofReal
        have := sum_inv_abs_D₁_le hM₁
        calc ∑ m₁ ∈ D₁ M₁, 1 / (|(m₁ : ℝ)| * M₃) = (∑ m₁ ∈ D₁ M₁, 1 / |(m₁ : ℝ)|) / M₃ := by
              rw [Finset.sum_div]
              exact Finset.sum_congr rfl fun _ _ => by rw [div_div]
          _ ≤ 6 / M₃ := by gcongr

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartZ
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartZ
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal
theorem lintegral_Wnear_sq_le_Sig (C : ℝ) (c : ℕ → ℝ → ℝ) (K : ℝ) (hC : 1 ≤ C) (hK : 0 < K)
    (η : ℝ) (hη : 0 < η) :
    ∃ A T₁ : ℝ, 0 ≤ A ∧ ∀ T : ℝ, T₁ ≤ T → ∀ f : ℝ → ℝ, Adm C c T f →
      ∀ M M₁ M₂ M₃ : ℝ, Regime T M M₁ M₂ M₃ →
        ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ (T ^ η) f ξ ^ 2) ≤
          ENNReal.ofReal (A * (T ^ η) ^ 2 * M) * Sig (T ^ η) M₂ M₃ f := by
  obtain ⟨A', hA', hcount⟩ := sum_card_nearSet_le η hη
  have hB : 0 ≤ B₀ K := B₀_nonneg K
  refine ⟨36 * A' * B₀ K ^ 2, 1, by positivity, ?_⟩
  intro T hT f hf M M₁ M₂ M₃ hr
  have hM₃ : 0 < M₃ := by linarith [hr.h₃]
  have hM₁0 : 0 < M₁ := by linarith [hr.h₁]
  have hQ : 1 ≤ T ^ η := Real.one_le_rpow hT hη.le
  have hQ0 : 0 < T ^ η := by linarith
  have hmeas : MeasurableSet (regII T η M₁ M₃) :=
    (measurableSet_lt measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hcount' := hcount T hT M₁ M₃ hr.h₁ hM₃
  set Q := T ^ η with hQdef
  set κ := A' * Q * (4 * Q * M₁ / M₃ + 1) * (M₃ * B₀ K) ^ 2 with hκ
  have hκ0 : 0 ≤ κ := by positivity
  have hpt : ∀ ξ ∈ regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2) ≤
      ENNReal.ofReal κ * ENNReal.ofReal (∑ m₁ ∈ D₁ M₁,
        ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2) := by
    intro ξ hξ
    rw [← ENNReal.ofReal_mul hκ0]
    apply ENNReal.ofReal_le_ofReal
    have hc := hcount' ξ hξ
    have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul (D₁ M₁)
      (r := fun m₁ => M₃ * B₀ K * ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖)
      (f := fun m₁ => ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ))
      (g := fun m₁ => (M₃ * B₀ K) ^ 2 *
        (((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2))
      (fun _ _ => Nat.cast_nonneg _) (fun _ _ => by positivity) (fun _ _ => le_of_eq (by ring))
    unfold Wnear
    refine hcs.trans ?_
    rw [← Finset.mul_sum]
    have hX : 0 ≤ ∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) *
        ‖Ffun M₂ f m₁ ξ‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
    calc _ ≤ (A' * Q * (4 * Q * M₁ / M₃ + 1)) * ((M₃ * B₀ K) ^ 2 * ∑ m₁ ∈ D₁ M₁,
            ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hc (mul_nonneg (sq_nonneg _) hX)
      _ = κ * ∑ m₁ ∈ D₁ M₁, ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) *
            ‖Ffun M₂ f m₁ ξ‖ ^ 2 := by rw [hκ]; ring
  calc ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal (Wnear K M₁ M₂ M₃ Q f ξ ^ 2)
      ≤ ∫⁻ ξ in regII T η M₁ M₃, ENNReal.ofReal κ * ENNReal.ofReal (∑ m₁ ∈ D₁ M₁,
          ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2) :=
        setLIntegral_mono' hmeas hpt
    _ ≤ ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|}, ENNReal.ofReal κ *
          ENNReal.ofReal (∑ m₁ ∈ D₁ M₁,
          ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2) :=
        lintegral_mono_set (fun ξ hξ => hξ.1)
    _ = ENNReal.ofReal κ * ∫⁻ ξ in {ξ : ℝ | 4 * Q * M₁ / M₃ < |ξ|},
          ENNReal.ofReal (∑ m₁ ∈ D₁ M₁,
          ((nearSet (ξ / m₁) (Q / M₃)).card : ℝ) * ‖Ffun M₂ f m₁ ξ‖ ^ 2) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal κ * (ENNReal.ofReal (6 / M₃) * Sig Q M₂ M₃ f) := by
        gcongr
        exact PartR.lintegral_near_le_Sig M₁ M₂ M₃ Q hr.h₁ hM₃ hQ0 f (adm_continuous hf)
          (adm_hasCompactSupport hf)
    _ = ENNReal.ofReal (κ * (6 / M₃)) * Sig Q M₂ M₃ f := by
        rw [← mul_assoc, ENNReal.ofReal_mul hκ0]
    _ ≤ ENNReal.ofReal (36 * A' * B₀ K ^ 2 * Q ^ 2 * M) * Sig Q M₂ M₃ f := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        have e : κ * (6 / M₃) = 6 * A' * B₀ K ^ 2 * Q * (4 * Q * M₁ + M₃) := by
          rw [hκ]; field_simp
        have h6 : 4 * Q * M₁ + M₃ ≤ 6 * Q * M := by nlinarith [hr.h₁M, hr.h₃M]
        rw [e]
        calc 6 * A' * B₀ K ^ 2 * Q * (4 * Q * M₁ + M₃)
            ≤ 6 * A' * B₀ K ^ 2 * Q * (6 * Q * M) := by gcongr
          _ = 36 * A' * B₀ K ^ 2 * Q ^ 2 * M := by ring

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine
end

section
namespace GuthMaynard.Affine.PartR
open GuthMaynard GuthMaynard.Affine GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

end GuthMaynard.Affine.PartR
end

section
namespace GuthMaynard.Affine
open GuthMaynard GuthMaynard.Affine MeasureTheory FourierTransform
open scoped ENNReal

alias lintegral_Wnear_sq_le_Sig_dev := GuthMaynard.Affine.PartR.lintegral_Wnear_sq_le_Sig

end GuthMaynard.Affine
end


theorem solution : type_of% @GuthMaynard.Affine.lintegral_Wnear_sq_le_Sig_dev := @GuthMaynard.Affine.lintegral_Wnear_sq_le_Sig_dev
