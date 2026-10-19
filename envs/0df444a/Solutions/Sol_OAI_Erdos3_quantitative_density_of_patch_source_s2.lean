-- Prove2me | solution 1 for OAI.Erdos3.quantitative_density_of_patch_source_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:46:50.840594+00:00
-- url     : https://prove2.me/submissions/f5439a06-0754-493d-ad3e-6e3ae9c12b4b

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B252
import Theorems.Thm_OAI_Erdos3_no_interval_invariant_of_descent_s2
import Theorems.Thm_OAI_Erdos3_polynomial_patch_density_increment_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Results.Basic
namespace OAI

section

namespace Erdos3

theorem extremalNumber_le (k N : ℕ) : extremalNumber k N ≤ N := by
  classical
  apply Finset.sup_le
  intro S hS
  have hSN := Finset.mem_powerset.mp (Finset.mem_filter.mp hS).1
  exact (Finset.card_le_card hSN).trans (by simp)

theorem exists_extremalSet {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.Icc 1 N ∧ APFree (S : Set ℕ) k ∧
      S.card = extremalNumber k N := by
  classical
  let candidates := ((Finset.Icc 1 N).powerset).filter
    (fun S : Finset ℕ ↦ APFree (S : Set ℕ) k)
  have hempty : APFree (∅ : Set ℕ) k := by
    rintro ⟨a, d, hd, h⟩
    exact h 0 hk
  have hne : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [candidates, Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset,
      Finset.coe_empty, true_and]
    exact hempty
  obtain ⟨S, hS, hmax⟩ := Finset.exists_mem_eq_sup candidates hne Finset.card
  obtain ⟨hSN, hfree⟩ := Finset.mem_filter.mp hS
  exact ⟨S, Finset.mem_powerset.mp hSN, hfree, hmax.symm⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AmplificationFinalCostGrowth
namespace OAI

section

open Filter

namespace Erdos3

theorem amplificationGain_closed {κ : ℝ} (hκ : κ ≠ 0) (H₀ : ℝ) (j : ℕ) :
    amplificationGain κ H₀ j = κ⁻¹ * (κ * H₀) ^ (2 ^ j) := by
  induction j with
  | zero => simp [amplificationGain, hκ]
  | succ j ih =>
    rw [amplificationGain, ih, show (2 : ℕ) ^ (j + 1) = 2 ^ j * 2 from pow_succ 2 j,
      pow_mul]
    field_simp

theorem amplificationGain_pos {κ H₀ : ℝ} (hκ : 0 < κ) (hH : 0 < H₀) (j : ℕ) :
    0 < amplificationGain κ H₀ j := by
  rw [amplificationGain_closed hκ.ne']
  positivity

end Erdos3

end

section

namespace Erdos3

theorem pow_log_exchange {b p : ℝ} (hb : 0 < b) (hp : 0 < p) (t : ℝ) :
    b ^ (t * Real.log p) = p ^ (t * Real.log b) := by
  rw [Real.rpow_def_of_pos hb, Real.rpow_def_of_pos hp]
  congr 1
  ring

theorem pow_floor_log_le {b p t : ℝ} (hb : 1 < b) (hp : 1 ≤ p) (ht : 0 ≤ t) :
    b ^ ⌊t * Real.log p⌋₊ ≤ p ^ (t * Real.log b) := by
  rw [← pow_log_exchange (by linarith : 0 < b) (by linarith : 0 < p) t,
    ← Real.rpow_natCast]
  apply Real.rpow_le_rpow_of_exponent_le hb.le
  exact Nat.floor_le (mul_nonneg ht (Real.log_nonneg hp))

theorem div_le_pow_floor_log {b p t : ℝ} (hb : 1 < b) (hp : 0 < p) :
    p ^ (t * Real.log b) / b ≤ b ^ ⌊t * Real.log p⌋₊ := by
  have hb0 : 0 < b := by linarith
  apply (div_le_iff₀ hb0).mpr
  calc
    p ^ (t * Real.log b) = b ^ (t * Real.log p) := (pow_log_exchange hb0 hp t).symm
    _ ≤ b ^ ((⌊t * Real.log p⌋₊ : ℝ) + 1) :=
      Real.rpow_le_rpow_of_exponent_le hb.le (Nat.lt_floor_add_one _).le
    _ = b ^ ⌊t * Real.log p⌋₊ * b := by
      rw [Real.rpow_add hb0, Real.rpow_one, Real.rpow_natCast]

theorem levelCoefficient_pos {K : ℝ} (hK : 1 < K) : 0 < levelCoefficient K := by
  unfold levelCoefficient
  exact one_div_pos.mpr (mul_pos (by norm_num) (Real.log_pos hK))

theorem levelCoefficient_mul_log {K : ℝ} (hK : 1 < K) :
    levelCoefficient K * Real.log K = 1 / 4 := by
  unfold levelCoefficient
  have hlog : Real.log K ≠ 0 := (Real.log_pos hK).ne'
  field_simp

theorem gainExponent_pos_le_quarter {K : ℝ} (hK : 2 ≤ K) :
    0 < gainExponent K ∧ gainExponent K ≤ 1 / 4 := by
  have hK1 : 1 < K := by linarith
  have ht := levelCoefficient_pos hK1
  constructor
  · exact mul_pos ht (Real.log_pos (by norm_num))
  · have hlog : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
    have h := mul_le_mul_of_nonneg_left hlog ht.le
    rwa [levelCoefficient_mul_log hK1] at h

theorem gain_base_at_selected_level {K p : ℝ} (hK : 1 < K) (hp : 1 ≤ p) :
    p ^ gainExponent K / 2 ≤ (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ∧
      (2 : ℝ) ^ ⌊levelCoefficient K * Real.log p⌋₊ ≤ p ^ gainExponent K := by
  constructor
  · exact div_le_pow_floor_log (by norm_num) (by linarith)
  · exact pow_floor_log_le (by norm_num) hp (levelCoefficient_pos hK).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ReplacementCellPotential
namespace OAI

section

open scoped BigOperators

namespace Erdos3

theorem rpow_sub_rpow_ge_tangent {u v θ : ℝ} (hu : 0 < u) (hv : 0 ≤ v)
    (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    θ * u ^ (θ - 1) * (u - v) ≤ u ^ θ - v ^ θ := by
  have hratio : (v / u) ^ θ ≤ 1 + θ * (v / u - 1) := by
    have h := rpow_one_add_le_one_add_mul_self
      (s := v / u - 1) (by have := div_nonneg hv hu.le; linarith) hθ0 hθ1
    simpa only [add_sub_cancel] using h
  have hscaled := mul_le_mul_of_nonneg_left hratio (Real.rpow_nonneg hu.le θ)
  have heq : u ^ θ * (v / u) ^ θ = v ^ θ := by
    rw [Real.div_rpow hv hu.le]
    field_simp
  rw [heq] at hscaled
  rw [Real.rpow_sub_one hu.ne']
  calc
    θ * (u ^ θ / u) * (u - v) =
        u ^ θ - u ^ θ * (1 + θ * (v / u - 1)) := by field_simp; ring
    _ ≤ _ := sub_le_sub_left hscaled _

end Erdos3

end

section

namespace Erdos3

theorem concave_power_drop {p p' β ν c : ℝ} (hp : 0 < p) (hp' : 0 ≤ p')
    (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hdrop : p' ≤ p - c * p ^ ν) :
    β * c * p ^ (β + ν - 1) ≤ p ^ β - p' ^ β := by
  have htangent := rpow_sub_rpow_ge_tangent hp hp' hβ0 hβ1
  calc
    β * c * p ^ (β + ν - 1) = β * p ^ (β - 1) * (c * p ^ ν) := by
      rw [show β + ν - 1 = (β - 1) + ν by ring, Real.rpow_add hp]
      ring
    _ ≤ β * p ^ (β - 1) * (p - p') :=
      mul_le_mul_of_nonneg_left (by linarith) (mul_nonneg hβ0 (Real.rpow_nonneg hp.le _))
    _ ≤ _ := htangent

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.SubquadraticRankPayment
namespace OAI

section

namespace Erdos3

theorem subquadratic_rank_exponents {K q : ℝ} (hK : 2 ≤ K)
    (hq : 1 ≤ q) (hq2 : q < 2) :
    let t := levelCoefficient K
    let ν := gainExponent K
    let μ := t * Real.log q
    let β := 1 - (ν - μ) / 2
    0 < t ∧ 0 < ν ∧ 0 ≤ μ ∧ μ < ν ∧ 1 / 4 < β ∧ β < 1 ∧ μ < β + ν - 1 := by
  dsimp only
  have ht := levelCoefficient_pos (show 1 < K by linarith)
  obtain ⟨hν, hνq⟩ := gainExponent_pos_le_quarter hK
  have hμ : 0 ≤ levelCoefficient K * Real.log q :=
    mul_nonneg ht.le (Real.log_nonneg hq)
  have hμν : levelCoefficient K * Real.log q < gainExponent K := by
    exact mul_lt_mul_of_pos_left
      (Real.log_lt_log (by linarith : 0 < q) hq2) ht
  refine ⟨ht, hν, hμ, hμν, ?_, ?_, ?_⟩ <;> linarith

theorem density_invariant_with_general_loss {p p' L L' A C₀ loss β ν c : ℝ}
    (hp : 0 < p) (hp' : 0 ≤ p') (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1) (hA : 0 ≤ A)
    (hinvariant : A * p ^ β + C₀ ≤ L)
    (hdrop : p' ≤ p - c * p ^ ν)
    (hlength : L - loss ≤ L')
    (hpayment : loss ≤ A * (β * c * p ^ (β + ν - 1))) :
    A * p' ^ β + C₀ ≤ L' := by
  have hpotential := mul_le_mul_of_nonneg_left
    (concave_power_drop hp hp' hβ0 hβ1 hdrop) hA
  linarith

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_rpow_log_le {μ δ A B : ℝ}
    (hgap : μ < δ) (hA : 0 < A) (hB : 0 < B) :
    ∀ᶠ p : ℝ in atTop, B * p ^ μ * Real.log (2 + p) ≤ A * p ^ δ := by
  have heps : 0 < A / (2 * B) := div_pos hA (by positivity)
  have hsmall := (isLittleO_log_rpow_atTop (sub_pos.mpr hgap)).bound heps
  filter_upwards [hsmall, eventually_ge_atTop (2 : ℝ)] with p hsmall hp
  have hp0 : 0 < p := by linarith
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hpow0 : 0 ≤ p ^ (δ - μ) := Real.rpow_nonneg hp0.le _
  simp only [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hpow0] at hsmall
  have hlog : Real.log (2 + p) ≤ 2 * Real.log p := by
    rw [show 2 * Real.log p = Real.log (p * p) by rw [Real.log_mul hp0.ne' hp0.ne']; ring]
    apply Real.log_le_log (by linarith)
    nlinarith
  have hco : 0 ≤ B * p ^ μ := mul_nonneg hB.le (Real.rpow_nonneg hp0.le _)
  calc
    B * p ^ μ * Real.log (2 + p) ≤ B * p ^ μ * (2 * Real.log p) :=
      mul_le_mul_of_nonneg_left hlog hco
    _ = (2 * B * p ^ μ) * Real.log p := by ring
    _ ≤ (2 * B * p ^ μ) * (A / (2 * B) * p ^ (δ - μ)) :=
      mul_le_mul_of_nonneg_left hsmall (by positivity)
    _ = A * p ^ δ := by
      have hpow : p ^ μ * p ^ (δ - μ) = p ^ δ := by
        rw [← Real.rpow_add hp0]
        congr 1
        ring
      calc
        _ = A * (p ^ μ * p ^ (δ - μ)) := by field_simp
        _ = _ := by rw [hpow]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialPatchProductBudget
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace PolynomialPatch

variable {σ : Type*} {s d D E : ℕ}

theorem value_mem_Icc (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end PolynomialPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.WeightedPatchReparam
namespace OAI

section

namespace Erdos3

open _root_.MvPolynomial

namespace WeightedParameterPatch

variable {σ : Type*} {p : σ → ℕ} {s d : ℕ}

theorem value_mem_Icc (A : WeightedParameterPatch σ p s d) (t : σ → ℝ) :
    A.value t ∈ Set.Icc (0 : ℝ) 1 := (A.form.slots t).patchValue_mem_Icc A.kernel

end WeightedParameterPatch

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PatchResetBudget
namespace OAI

section

namespace Erdos3

theorem exists_patch_reset_budget (s : ℕ) {K : ℝ} (hK : 1 ≤ K) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (d T : ℕ) (L σ : ℝ), 0 ≤ L → 0 < σ → σ ≤ 1 →
      C * ((d : ℝ) + 1) * (L + 1) ≤ σ * T →
      0 < T ∧ K * ((d : ℝ) + 1) ≤ T ∧
      (2 : ℝ) ^ (s + 1) * s < T ∧ 24 * (d : ℝ) * s < T ∧
      8 * L * d * s * (2 : ℝ) ^ s ≤ σ * T ∧
      (2 : ℝ) ^ (2 * s + 3) ≤ σ * T := by
  let C := 2 * (K + (2 : ℝ) ^ (s + 1) * s + 24 * s +
    8 * s * (2 : ℝ) ^ s + (2 : ℝ) ^ (2 * s + 3) + 1)
  have ha : 0 ≤ (2 : ℝ) ^ (s + 1) * s := by positivity
  have hb : 0 ≤ 24 * (s : ℝ) := by positivity
  have hc : 0 ≤ 8 * (s : ℝ) * (2 : ℝ) ^ s := by positivity
  have hd : 0 ≤ (2 : ℝ) ^ (2 * s + 3) := by positivity
  have hC : 1 ≤ C := by dsimp [C]; nlinarith
  have hCK : K ≤ C := by dsimp [C]; nlinarith
  have hClift : (2 : ℝ) ^ (s + 1) * s < C := by dsimp [C]; nlinarith
  have hCfreeze : 24 * (s : ℝ) < C := by dsimp [C]; nlinarith
  have hCroom : 8 * (s : ℝ) * (2 : ℝ) ^ s ≤ C := by dsimp [C]; nlinarith
  have hClength : (2 : ℝ) ^ (2 * s + 3) ≤ C := by dsimp [C]; nlinarith
  refine ⟨C, hC, ?_⟩
  intro d T L σ hL hσ hσ1 hbound
  let U := ((d : ℝ) + 1) * (L + 1)
  have hU : 1 ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hdU : (d : ℝ) + 1 ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hLdU : L * d ≤ U := by dsimp [U]; nlinarith [Nat.cast_nonneg (α := ℝ) d]
  have hbound' : C * U ≤ σ * T := by simpa only [U, mul_assoc] using hbound
  have hCT : C * U ≤ T := hbound'.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) T])
  have hCT' : C ≤ T := (le_mul_of_one_le_right (by linarith) hU).trans hCT
  have hT : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  refine ⟨hT, ?_, hClift.trans_le hCT', ?_, ?_, ?_⟩
  · exact (mul_le_mul hCK hdU (by positivity) (by linarith)).trans hCT
  · calc
      _ ≤ (24 * (s : ℝ)) * U := by nlinarith [mul_le_mul_of_nonneg_left hdU (by positivity : (0 : ℝ) ≤ 24 * s)]
      _ < C * U := mul_lt_mul_of_pos_right hCfreeze (by linarith)
      _ ≤ T := hCT
  · calc
      _ = (8 * (s : ℝ) * (2 : ℝ) ^ s) * (L * d) := by ring
      _ ≤ C * U := mul_le_mul hCroom hLdU (by positivity) (by linarith)
      _ ≤ σ * T := hbound'
  · exact (hClength.trans (le_mul_of_one_le_right (by linarith) hU)).trans hbound'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialProductReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem polynomial_patch_score_le_one {s d N : ℕ} (A : PolynomialPatch Unit s d)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1)
    {b : ℝ} (hb : b ∈ Set.Icc (0 : ℝ) 1) :
    (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) ≤ 1 := by
  by_cases hN : N = 0
  · subst N
    simp
  · let : NeZero N := ⟨hN⟩
    apply Finset.expect_le Finset.univ_nonempty
    intro n _
    have hB := A.value_mem_Icc (fun _ => (n.val : ℝ))
    have hle : f n.val - b ≤ 1 := by linarith [(hf n.val n.isLt).2, hb.1]
    exact (mul_le_mul_of_nonneg_right hle hB.1).trans (by simpa using hB.2)

theorem quantitative_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N T : ℕ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) ≤ σ * T →
        T ^ (P * (d + 1) ^ (2 * s * s)) ≤ N →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ T ≤ len ∧
          (∀ n < len, a + q * n < N) ∧ b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨K, p, hK, hp, hreset⟩ := polynomial_patch_density_increment_s2 s
  obtain ⟨C, hC, hbudget⟩ := exists_patch_reset_budget s hK
  refine ⟨C, (2 * p) ^ s, hC, pow_pos (by omega) _, ?_⟩
  intro d N T A f hf b σ hb hσ hscale hsize hscore
  have hσ1 := hscore.trans (polynomial_patch_score_le_one A f hf hb)
  obtain ⟨hT, hKscale, hlift, hfreeze, hroom, hlength⟩ :=
    hbudget d T A.kernel.lip σ A.kernel.lip.coe_nonneg hσ hσ1 hscale
  exact hreset d N T A hT hKscale hlift hfreeze hsize f hf b σ hb hσ hroom hlength hscore

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PatchIterationBudget
namespace OAI

section

namespace Erdos3

theorem exists_reset_scale_of_log_bound {Q N : ℕ} (hQ : 0 < Q)
    {B : ℝ} (hB : 1 ≤ B)
    (hsize : 2 * (Q : ℝ) * Real.log (2 * B) ≤ Real.log N) :
    1 < N ∧ ∃ T : ℕ, 0 < T ∧ B ≤ T ∧ T ^ Q ≤ N ∧
      Real.exp (Real.log N / (2 * Q)) ≤ T := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hB0 : 0 < 2 * B := by linarith
  have hlogB : 0 < Real.log (2 * B) := Real.log_pos (by linarith)
  have hlogN : 0 < Real.log N := (mul_pos (by positivity) hlogB).trans_le hsize
  have hN1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  let x := Real.log N / (2 * Q)
  let Y := Real.exp x
  have hBY : 2 * B ≤ Y := by
    apply (Real.log_le_iff_le_exp hB0).mp
    exact (le_div_iff₀ (by positivity)).mpr (by nlinarith [hsize])
  have hY2 : 2 ≤ Y := by linarith
  let T := ⌈Y⌉₊
  have hYT : Y ≤ (T : ℝ) := Nat.le_ceil Y
  have hT0 : 0 < T := by exact_mod_cast (show (0 : ℝ) < T by linarith)
  have hTY : (T : ℝ) ≤ Y ^ 2 := by
    have hc : (T : ℝ) < Y + 1 := Nat.ceil_lt_add_one (by linarith)
    nlinarith
  have hpower : (Y ^ 2) ^ Q = (N : ℝ) := by
    dsimp only [Y]
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]
    have heq : (Q : ℝ) * ((2 : ℕ) * x) = Real.log N := by
      dsimp [x]
      field_simp
    rw [heq, Real.exp_log hN0]
  have hTN : T ^ Q ≤ N := by
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) T) hTY Q
    rw [hpower] at hp
    exact_mod_cast hp
  exact ⟨by exact_mod_cast hN1, T, hT0, by linarith, hTN, hYT⟩

theorem log_log_length_loss {N M : ℕ} {Q : ℝ}
    (hN : 1 < N) (hQ : 0 < Q)
    (hM : Real.exp (Real.log N / Q) ≤ M) :
    1 < M ∧ Real.log (Real.log N) - Real.log Q ≤ Real.log (Real.log M) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast hN
  have hlogN : 0 < Real.log N := Real.log_pos hN1
  have hx : 0 < Real.log N / Q := div_pos hlogN hQ
  have hM1 : (1 : ℝ) < M := (Real.one_lt_exp_iff.mpr hx).trans_le hM
  have hlogM : Real.log N / Q ≤ Real.log M :=
    (Real.le_log_iff_exp_le (by linarith)).mpr hM
  have h := Real.log_le_log hx hlogM
  rw [Real.log_div hlogN.ne' hQ.ne'] at h
  exact ⟨by exact_mod_cast hM1, h⟩

end Erdos3

end

section

namespace Erdos3

theorem log_patch_reset_cost_le {C L σ U : ℝ} (hC : 0 < C) (hL : 0 ≤ L)
    (hσ : 0 < σ) (hLip : L + 1 ≤ Real.exp U) (hscore : Real.exp (-U) ≤ σ)
    (d : ℕ) :
    Real.log (2 * C * ((d : ℝ) + 1) * (L + 1) / σ) ≤
      Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U := by
  have hLp : 0 < L + 1 := by linarith
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hlogL : Real.log (L + 1) ≤ U := (Real.log_le_iff_le_exp hLp).mpr hLip
  have hlogσ : -U ≤ Real.log σ := (Real.le_log_iff_exp_le hσ).mpr hscore
  rw [Real.log_div (by positivity) hσ.ne',
    Real.log_mul (by positivity) hLp.ne', Real.log_mul (by positivity) hd.ne']
  linarith

theorem slice_reset_log_room {Q C U : ℝ} {d N M : ℕ}
    (hQ : 1 ≤ Q) (hC : 1 ≤ C) (hU : 1 ≤ U)
    (hslice : Real.log N - U ≤ Real.log M)
    (hsize : 4 * Q * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N) :
    1 < N ∧ Real.log N / 2 ≤ Real.log M ∧
      2 * Q * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log M := by
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hlogd : 0 ≤ Real.log ((d : ℝ) + 1) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) d; linarith)
  have hlogN : 2 * U ≤ Real.log N := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ Q) (add_nonneg hlogC hlogd)]
  have hN : (1 : ℝ) < N :=
    (Real.log_pos_iff (Nat.cast_nonneg N)).mp (by linarith)
  refine ⟨by exact_mod_cast hN, by linarith, ?_⟩
  linarith

end Erdos3

end

section

namespace Erdos3

theorem patch_reset_cutoff_bound {C P U : ℝ} (hC : 1 ≤ C) (hP : 0 ≤ P)
    (hU : 1 ≤ U) (d a : ℕ) :
    4 * P * ((d : ℝ) + 1) ^ a * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤
      (4 * P * (Real.log (2 * C) + 3)) * ((d : ℝ) + 1) ^ (a + 1) * U := by
  have hd : (1 : ℝ) ≤ d + 1 := by have := Nat.cast_nonneg (α := ℝ) d; linarith
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hprod : 1 ≤ ((d : ℝ) + 1) * U := one_le_mul_of_one_le_of_one_le hd hU
  have hD : (d : ℝ) + 1 ≤ ((d : ℝ) + 1) * U := le_mul_of_one_le_right (by positivity) hU
  have hU' : U ≤ ((d : ℝ) + 1) * U := le_mul_of_one_le_left (by linarith) hd
  have hlogD : Real.log ((d : ℝ) + 1) ≤ ((d : ℝ) + 1) * U :=
    (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have hC' : Real.log (2 * C) ≤ Real.log (2 * C) * (((d : ℝ) + 1) * U) :=
    le_mul_of_one_le_right hlogC hprod
  have hsum : Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U ≤
      (Real.log (2 * C) + 3) * ((d : ℝ) + 1) * U := by nlinarith
  calc
    _ ≤ (4 * P * ((d : ℝ) + 1) ^ a) * ((Real.log (2 * C) + 3) * ((d : ℝ) + 1) * U) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by rw [pow_succ]; ring

theorem patch_reset_cutoff_of_loglog {C P U R V : ℝ} {N : ℕ}
    (hC : 1 ≤ C) (hP : 0 < P) (hU : 1 ≤ U) (hN : 1 < N) (d a : ℕ)
    (hR : Real.log ((d : ℝ) + 1) ≤ R) (hV : Real.log U ≤ V)
    (hsize : Real.log (4 * P * (Real.log (2 * C) + 3)) + (a + 1 : ℕ) * R + V ≤
      Real.log (Real.log N)) :
    4 * P * ((d : ℝ) + 1) ^ a * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤
      Real.log N := by
  have hlogC : 0 ≤ Real.log (2 * C) := Real.log_nonneg (by linarith)
  have hconst : 0 < 4 * P * (Real.log (2 * C) + 3) := by positivity
  have hd : (0 : ℝ) < d + 1 := by positivity
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
  apply (patch_reset_cutoff_bound hC hP.le hU d a).trans
  have hlog : Real.log ((4 * P * (Real.log (2 * C) + 3)) * ((d : ℝ) + 1) ^ (a + 1) * U) ≤
      Real.log (Real.log N) := by
    rw [Real.log_mul (by positivity) (by linarith),
      Real.log_mul hconst.ne' (by positivity), Real.log_pow]
    have hr := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (α := ℝ) (a + 1))
    linarith
  exact (Real.log_le_log_iff (by positivity) hlogN).mp hlog

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_two_resource_costs_fit {μ γ β A B D : ℝ}
    (hμ : μ < β) (hγ : γ < β) (hA : 0 < A) (hB : 0 < B) (hD : 0 < D) :
    ∀ᶠ p : ℝ in atTop,
      B * p ^ μ * Real.log (2 + p) + D * p ^ γ * Real.log (2 + p) ≤ A * p ^ β := by
  have hfirst := eventually_rpow_log_le hμ (by linarith : 0 < A / 2) hB
  have hsecond := eventually_rpow_log_le hγ (by linarith : 0 < A / 2) hD
  filter_upwards [hfirst, hsecond] with p hp hq
  linarith

theorem eventually_constant_add_rank_loss_paid {μ δ A B L₀ : ℝ}
    (hμ : 0 ≤ μ) (hgap : μ < δ) (hA : 0 < A) (hB : 0 ≤ B) (hL : 0 ≤ L₀) :
    ∀ᶠ p : ℝ in atTop, L₀ + B * p ^ μ * Real.log (2 + p) ≤ A * p ^ δ := by
  have hlarge := eventually_rpow_log_le hgap hA (by linarith : 0 < B + L₀ + 1)
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℝ), eventually_ge_atTop (Real.exp 1)] with
    p hlarge hp he
  have hpow : 1 ≤ p ^ μ := Real.one_le_rpow hp hμ
  have hlog : 1 ≤ Real.log (2 + p) :=
    (Real.le_log_iff_exp_le (by linarith)).mpr (by linarith)
  have hprod : 1 ≤ p ^ μ * Real.log (2 + p) := one_le_mul_of_one_le_of_one_le hpow hlog
  have hconstant := mul_le_mul_of_nonneg_left hprod hL
  nlinarith

theorem subquadratic_patch_iteration_budgets {K q A c B D L₀ : ℝ}
    (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2) (hA : 0 < A) (hc : 0 < c)
    (hB : 0 < B) (hD : 0 < D) (hL : 0 ≤ L₀) (a : ℕ) :
    let μ := levelCoefficient K * Real.log q
    let ν := gainExponent K
    let β := 1 - (ν - μ) / 2
    ∀ᶠ p : ℝ in atTop,
      ((a + 1 : ℕ) * B * p ^ μ * Real.log (2 + p) +
        D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A * p ^ β) ∧
      (L₀ + (a : ℝ) * B * p ^ μ * Real.log (2 + p) ≤
        A * (β * c * p ^ (β + ν - 1))) := by
  dsimp only
  obtain ⟨_, _, hμ, hμν, hβ, _, hgap⟩ := subquadratic_rank_exponents hK hq hq2
  have hν4 := (gainExponent_pos_le_quarter hK).2
  have hfit := eventually_two_resource_costs_fit
    (by linarith : levelCoefficient K * Real.log q < 1 - (gainExponent K - levelCoefficient K * Real.log q) / 2)
    hβ hA (by positivity : 0 < (a + 1 : ℕ) * B) hD
  have hco : 0 < A * ((1 - (gainExponent K - levelCoefficient K * Real.log q) / 2) * c) :=
    mul_pos hA (mul_pos (by linarith) hc)
  have hpaid := eventually_constant_add_rank_loss_paid hμ hgap hco
    (by positivity : 0 ≤ (a : ℝ) * B) hL
  filter_upwards [hfit, hpaid] with p hfit hpaid
  exact ⟨hfit, by simpa only [mul_assoc] using hpaid⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.SlicedPolynomialPatchReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem patch_reset_log_loss_eq {P : ℕ} (hP : 0 < P) (d a : ℕ) :
    Real.log (2 * (P * (d + 1) ^ a : ℕ)) =
      Real.log (2 * (P : ℝ)) + (a : ℝ) * Real.log ((d : ℝ) + 1) := by
  push_cast
  rw [show 2 * ((P : ℝ) * ((d : ℝ) + 1) ^ a) =
    (2 * P) * ((d : ℝ) + 1) ^ a by ring, Real.log_mul (by positivity) (by positivity),
    Real.log_pow]

theorem logarithmic_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N : ℕ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) →
        ∀ b σ : ℝ, b ∈ Set.Icc (0 : ℝ) 1 → 0 < σ →
        let Q := P * (d + 1) ^ (2 * s * s)
        2 * (Q : ℝ) * Real.log (2 * C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) / σ)
          ≤ Real.log N →
        σ ≤ (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.exp (Real.log N / (2 * Q)) ≤ len ∧
          Real.log (Real.log N) -
            (Real.log (2 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1)) ≤
              Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := quantitative_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N A f hf b σ hb hσ Q hsize hscore
  have hQ : 0 < Q := Nat.mul_pos hP (pow_pos (by omega) _)
  let cost := C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1)
  have hcost : 1 ≤ cost := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hC (by have := Nat.cast_nonneg (α := ℝ) d; linarith))
    (by have := A.kernel.lip.coe_nonneg; linarith)
  have hσ1 := hscore.trans (polynomial_patch_score_le_one A f hf hb)
  have hB : 1 ≤ cost / σ := (le_div_iff₀ hσ).mpr (by linarith)
  have hsize' : 2 * (Q : ℝ) * Real.log (2 * (cost / σ)) ≤ Real.log N := by
    convert hsize using 1
    congr 2
    dsimp [cost]
    ring
  obtain ⟨hN, T, _, hBT, hTN, hroot⟩ := exists_reset_scale_of_log_bound hQ hB hsize'
  have hscale : C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) ≤ σ * T := by
    have h := (div_le_iff₀ hσ).mp hBT
    change cost ≤ σ * T
    simpa only [mul_comm] using h
  obtain ⟨q, a, len, hq, hlen, hin, hdense⟩ := hreset d N T A f hf b σ hb hσ hscale hTN hscore
  have hroot' : Real.exp (Real.log N / (2 * Q)) ≤ len :=
    hroot.trans (by exact_mod_cast hlen)
  obtain ⟨hlen1, hloss⟩ := log_log_length_loss hN (by positivity : (0 : ℝ) < 2 * Q) hroot'
  refine ⟨q, a, len, hq, hlen1, hin, hroot', ?_, hdense⟩
  simpa only [Q, patch_reset_log_loss_eq hP] using hloss

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem sliced_polynomial_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) 1 →
        let Q := P * (d + 1) ^ (2 * s * s)
        4 * (Q : ℝ) * (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.exp (Real.log N / (4 * Q)) ≤ len ∧
          Real.log (Real.log N) -
            (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1)) ≤
              Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := logarithmic_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U A f hq₀ hslice hf hU hlogM hLip b hb Q hsize hscore
  have hQ : 0 < Q := Nat.mul_pos hP (pow_pos (by omega) _)
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast hQ
  obtain ⟨hN, hhalf, hroom⟩ := slice_reset_log_room hQ1 hC hU hlogM hsize
  have hcost := log_patch_reset_cost_le (by linarith : 0 < C) A.kernel.lip.coe_nonneg
    (Real.exp_pos (-U)) hLip le_rfl d
  have hresetSize : 2 * (Q : ℝ) *
      Real.log (2 * C * ((d : ℝ) + 1) * ((A.kernel.lip : ℝ) + 1) / Real.exp (-U)) ≤
        Real.log M :=
    (mul_le_mul_of_nonneg_left hcost (by positivity)).trans hroom
  obtain ⟨q, a, len, hq, hlen, hin, hroot, _, hdense⟩ := hreset d M A
    (fun n => f (a₀ + q₀ * n)) (fun n hn => hf _ (hslice n hn)) b (Real.exp (-U))
    hb (Real.exp_pos (-U)) hresetSize hscore
  have hrootParent : Real.exp (Real.log N / (4 * Q)) ≤ len := by
    apply le_trans (Real.exp_le_exp.mpr ?_) hroot
    calc
      _ = (Real.log N / 2) / (2 * Q) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hhalf (by positivity)
  obtain ⟨_, hloss⟩ := log_log_length_loss hN (by positivity : (0 : ℝ) < 4 * Q) hrootParent
  have hfactor : Real.log (4 * (Q : ℝ)) =
      Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * Real.log ((d : ℝ) + 1) := by
    dsimp [Q]
    push_cast
    rw [show 4 * ((P : ℝ) * ((d : ℝ) + 1) ^ (2 * s * s)) =
      (4 * P) * ((d : ℝ) + 1) ^ (2 * s * s) by ring,
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    rfl
  rw [hfactor] at hloss
  refine ⟨q₀ * q, a₀ + q₀ * a, len, Nat.mul_pos hq₀ hq, hlen, ?_, hrootParent, hloss, ?_⟩
  · intro n hn
    convert hslice (a + q * n) (hin n hn) using 1
    ring
  · convert hdense using 1
    congr 1
    funext n
    congr 1
    ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ResourceControlledPatchReset
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem resource_controlled_patch_reset (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U R V : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
        Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) + (2 * s * s + 1 : ℕ) * R + V ≤
          Real.log (Real.log N) →
        ∀ b : ℝ, b ∈ Set.Icc (0 : ℝ) 1 →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - b) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.log (Real.log N) - (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * R) ≤
            Real.log (Real.log len) ∧
          b < 𝔼 n : Fin len, f (a + q * n.val) := by
  obtain ⟨C, P, hC, hP, hreset⟩ := sliced_polynomial_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U R V A f hN hq₀ hslice hf hU hM hLip hR hV hsize b hb hscore
  have hcutoff := patch_reset_cutoff_of_loglog hC (by exact_mod_cast hP : (0 : ℝ) < P)
    hU hN d (2 * s * s) hR hV hsize
  have hcutoff' : 4 * (P * (d + 1) ^ (2 * s * s) : ℕ) *
      (Real.log (2 * C) + Real.log ((d : ℝ) + 1) + 2 * U) ≤ Real.log N := by
    push_cast
    simpa only [mul_assoc] using hcutoff
  obtain ⟨q, a, len, hq, hlen, hin, _, hloss, hdense⟩ :=
    hreset d N M a₀ q₀ U A f hq₀ hslice hf hU hM hLip b hb hcutoff' hscore
  refine ⟨q, a, len, hq, hlen, hin, ?_, hdense⟩
  have hR' := mul_le_mul_of_nonneg_left hR (Nat.cast_nonneg (α := ℝ) (2 * s * s))
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.RelativeSourceDensityParameter
namespace OAI

section

namespace Erdos3

theorem densityParameter_ge_two (α : ℝ) : 2 ≤ densityParameter α := le_max_left _ _

theorem densityParameter_drop {α α' G p δ : ℝ}
    (hα : 0 < α) (hG : 0 < G) (hgain : G * α ≤ α')
    (hp : Real.log (2 / α) ≤ p) (hδ : δ ≤ Real.log G) (hroom : 2 ≤ p - δ) :
    densityParameter α' ≤ p - δ := by
  have hα' : 0 < α' := (mul_pos hG hα).trans_le hgain
  apply max_le hroom
  have hratio : 2 / α' ≤ 2 / (G * α) :=
    div_le_div_of_nonneg_left (by norm_num) (mul_pos hG hα) hgain
  have hlog := Real.log_le_log (by positivity : 0 < 2 / α') hratio
  have heq : Real.log (2 / (G * α)) = Real.log (2 / α) - Real.log G := by
    rw [Real.log_div (by norm_num) (mul_ne_zero hG.ne' hα.ne'),
      Real.log_mul hG.ne' hα.ne', Real.log_div (by norm_num) hα.ne']
    ring
  rw [heq] at hlog
  linarith

theorem selected_amplification_log_gain {κ H₀ K p : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 1 < K) (hp : 1 ≤ p) :
    p ^ gainExponent K * (Real.log (κ * H₀) / 2) - Real.log 2 ≤
      Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2) := by
  have hbase : 0 < κ * H₀ := by linarith
  have hid : κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ =
      (κ * H₀) ^ (2 ^ ⌊levelCoefficient K * Real.log p⌋₊) := by
    rw [amplificationGain_closed hκ.ne']
    field_simp
  rw [Real.log_div (by rw [hid]; positivity) (by norm_num), hid, Real.log_pow]
  have hlow := mul_le_mul_of_nonneg_right (gain_base_at_selected_level hK hp).1
    (Real.log_nonneg hH.le)
  norm_cast at hlow ⊢
  linarith

end Erdos3

end

section

namespace Erdos3

theorem density_le_exp_sub_parameter {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    α ≤ Real.exp (2 - densityParameter α) := by
  have hlogα : Real.log α ≤ 0 := Real.log_nonpos hα.le hα1
  have hlog2 : Real.log 2 ≤ 2 := (Real.log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
  have hp : densityParameter α ≤ 2 - Real.log α := by
    apply max_le (by linarith)
    rw [Real.log_div (by norm_num) hα.ne']
    linarith
  exact (Real.log_le_iff_le_exp hα).mp (by linarith)

theorem density_parameter_ge_of_invariant_failure {α A β C L : ℝ}
    (hA : 0 < A) (hβ : 0 < β) (hL : 0 ≤ L) (hC : 2 * C ≤ L)
    (hfail : L < A * densityParameter α ^ β + C) :
    (1 / (2 * A)) ^ (1 / β) * L ^ (1 / β) ≤ densityParameter α := by
  have hp : 0 < densityParameter α := by linarith [densityParameter_ge_two α]
  have hpower : L / (2 * A) ≤ densityParameter α ^ β := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hroot := Real.rpow_le_rpow (div_nonneg hL (by positivity)) hpower (by positivity : 0 ≤ 1 / β)
  have heq : (densityParameter α ^ β) ^ (1 / β) = densityParameter α := by
    rw [← Real.rpow_mul hp.le, mul_one_div_cancel hβ.ne', Real.rpow_one]
  rw [heq] at hroot
  have hleft : (L / (2 * A)) ^ (1 / β) = (1 / (2 * A)) ^ (1 / β) * L ^ (1 / β) := by
    rw [show L / (2 * A) = (1 / (2 * A)) * L by ring,
      Real.mul_rpow (by positivity) hL]
  rwa [hleft] at hroot

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem intervalIndicator_mem_Icc (S : Finset ℕ) (n : ℕ) :
    intervalIndicator S n ∈ Set.Icc (0 : ℝ) 1 := by
  unfold intervalIndicator
  split <;> norm_num

theorem mean_intervalIndicator {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    (𝔼 n : Fin N, intervalIndicator S n.val) = intervalDensity N S := by
  classical
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
  have hfilter : (Finset.range N).filter (fun n => n ∈ S) = S := by
    ext n
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hS h, h⟩⟩
  have hsum : (∑ n : Fin N, intervalIndicator S n.val) = (S.card : ℝ) := by
    rw [Fin.sum_univ_eq_sum_range]
    simp only [intervalIndicator, ← Finset.sum_filter, Finset.sum_const,
      nsmul_eq_mul, mul_one, hfilter]
  rw [hsum]
  rfl

theorem intervalDensity_le_one {N : ℕ} {S : Finset ℕ} (hS : S ⊆ Finset.range N) :
    intervalDensity N S ≤ 1 := by
  have hcard : S.card ≤ N := (Finset.card_le_card hS).trans_eq (Finset.card_range N)
  exact div_le_one_of_le₀ (by exact_mod_cast hcard) (Nat.cast_nonneg N)

theorem mean_progression_indicator (S : Finset ℕ) (a q M : ℕ) :
    (𝔼 n : Fin M, intervalIndicator S (a + q * n.val)) =
      intervalDensity M (progressionPreimage S a q M) := by
  rw [← mean_intervalIndicator (progressionPreimage_subset S a q M)]
  apply Finset.expect_congr rfl
  intro n _
  simp only [intervalIndicator, progressionPreimage, Finset.mem_filter, Finset.mem_range,
    n.isLt, true_and]

end Erdos3

end

section

namespace Erdos3

open Filter

theorem eventually_sublinear_drop_room {ν c : ℝ} (hν : ν < 1) :
    ∀ᶠ p : ℝ in atTop, 2 ≤ p - c * p ^ ν := by
  have hgrowth := (tendsto_rpow_atTop (sub_pos.mpr hν)).eventually_ge_atTop (2 * c)
  filter_upwards [hgrowth, eventually_ge_atTop (4 : ℝ)] with p hp hp4
  have hp0 : 0 < p := by linarith
  have hmul := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hp0.le ν)
  have heq : p ^ (1 - ν) * p ^ ν = p := by
    rw [← Real.rpow_add hp0, sub_add_cancel, Real.rpow_one]
  rw [heq] at hmul
  linarith

theorem exists_selected_density_drop {κ H₀ K : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ p : ℝ in atTop,
      c * p ^ gainExponent K ≤
        Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2) ∧
      2 ≤ p - c * p ^ gainExponent K := by
  let c := Real.log (κ * H₀) / 4
  have hc : 0 < c := div_pos (Real.log_pos hH) (by norm_num)
  obtain ⟨hν, hν4⟩ := gainExponent_pos_le_quarter hK
  have hroom := eventually_sublinear_drop_room (c := c) (by linarith : gainExponent K < 1)
  have hlarge := (tendsto_rpow_atTop hν).eventually_ge_atTop (Real.log 2 / c)
  refine ⟨c, hc, ?_⟩
  filter_upwards [hroom, hlarge, eventually_ge_atTop (1 : ℝ)] with p hroom hlarge hp
  refine ⟨?_, hroom⟩
  have hgain := selected_amplification_log_gain hκ hH (by linarith : 1 < K) hp
  have hlog2 : Real.log 2 ≤ c * p ^ gainExponent K := by
    have h := (div_le_iff₀ hc).mp hlarge
    simpa only [mul_comm] using h
  dsimp only [c] at hlog2 ⊢
  nlinarith

end Erdos3

end

section

namespace Erdos3

namespace APFreeInterval

variable {k : ℕ}

theorem density_pos (S : APFreeInterval k) : 0 < S.density :=
  intervalDensity_pos (by have := S.length_gt_one; omega) S.nonempty

end APFreeInterval

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ZeroBasedExtremalSet
namespace OAI

section

namespace Erdos3

theorem exists_zero_based_extremalSet {k : ℕ} (hk : 0 < k) (N : ℕ) :
    ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ APFree (S : Set ℕ) k ∧ S.card = extremalNumber k N := by
  classical
  obtain ⟨S, hS, hfree, hcard⟩ := exists_extremalSet hk N
  let T := S.image (fun n => n - 1)
  have hT : T ⊆ Finset.range N := by
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxs := Finset.mem_Icc.mp (hS hx)
    exact Finset.mem_range.mpr (by omega)
  have hTf : APFree (T : Set ℕ) k := by
    apply (hfree.affine_preimage 1 1 (by omega)).mono
    intro n hn
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hn
    have hxs := Finset.mem_Icc.mp (hS hx)
    have he : 1 + 1 * (x - 1) = x := by omega
    simpa only [Set.mem_preimage, he, Finset.mem_coe] using hx
  have hTc : T.card = S.card := by
    apply Finset.card_image_of_injOn
    intro x hx y hy he
    have hx1 := (Finset.mem_Icc.mp (hS hx)).1
    have hy1 := (Finset.mem_Icc.mp (hS hy)).1
    change x - 1 = y - 1 at he
    omega
  exact ⟨T, hT, hTf, hTc.trans hcard⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.DensityBoundFromInvariant
namespace OAI

section

namespace Erdos3

open Filter
open scoped BigOperators

theorem quantitativeDensityBound_of_eventually {k : ℕ} {C c η : ℝ}
    (hC : 0 < C) (hc : 0 < c) (hη : 0 < η)
    (hbound : ∀ᶠ N : ℕ in atTop, (extremalNumber k N : ℝ) ≤
      C * N * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) : QuantitativeDensityBound k := by
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  let C' := C + ∑ n ∈ Finset.range N₀, Real.exp (c * (Real.log (Real.log n)) ^ (1 + η))
  have hCC' : C ≤ C' := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)
  refine ⟨C', c, η, hC.trans_le hCC', hc, hη, ?_⟩
  intro N _
  by_cases hlarge : N₀ ≤ N
  · exact (hN₀ N hlarge).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC' (Nat.cast_nonneg N)) (Real.exp_pos _).le)
  · have hNmem : N ∈ Finset.range N₀ := Finset.mem_range.mpr (by omega)
    have hterm : Real.exp (c * (Real.log (Real.log N)) ^ (1 + η)) ≤ C' := by
      have hsum := Finset.single_le_sum (fun n (_ : n ∈ Finset.range N₀) => (Real.exp_pos
        (c * (Real.log (Real.log n)) ^ (1 + η))).le) hNmem
      exact hsum.trans (le_add_of_nonneg_left hC.le)
    have hscale : 1 ≤ C' * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
      have h := mul_le_mul_of_nonneg_right hterm
        (Real.exp_pos (-c * (Real.log (Real.log N)) ^ (1 + η))).le
      have heq : Real.exp (c * (Real.log (Real.log N)) ^ (1 + η)) *
          Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) = 1 := by
        rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      rwa [heq] at h
    have hcard : (extremalNumber k N : ℝ) ≤ N := by exact_mod_cast extremalNumber_le k N
    have hmul := mul_le_mul_of_nonneg_right hscale (Nat.cast_nonneg (α := ℝ) N)
    nlinarith

end Erdos3

end

section

namespace Erdos3

open Filter

theorem quantitative_density_of_no_invariant {k : ℕ} (hk : 0 < k)
    {A β C₀ : ℝ} (hA : 0 < A) (hβ : 0 < β) (hβ1 : β < 1)
    (hno : ∀ S : APFreeInterval k,
      ¬ A * S.parameter ^ β + C₀ ≤ Real.log (Real.log S.length)) : QuantitativeDensityBound k := by
  let c := (1 / (2 * A)) ^ (1 / β)
  let η := 1 / β - 1
  have hc : 0 < c := Real.rpow_pos_of_pos (by positivity) _
  have hη : 0 < η := by
    have hid : (1 / β) * β = 1 := one_div_mul_cancel hβ.ne'
    have hip : 0 < 1 / β := one_div_pos.mpr hβ
    dsimp [η]
    nlinarith
  have hηeq : 1 + η = 1 / β := by dsimp [η]; ring
  apply quantitativeDensityBound_of_eventually (Real.exp_pos 2) hc hη
  have hloglog : Tendsto (fun N : ℕ => Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hloglog.eventually_ge_atTop (max 0 (2 * C₀)), eventually_ge_atTop (3 : ℕ)] with
    N hlarge hN
  obtain ⟨S, hS, hfree, hcard⟩ := exists_zero_based_extremalSet hk N
  by_cases hnonempty : S.Nonempty
  · let X : APFreeInterval k := ⟨N, by omega, S, hS, hnonempty, hfree⟩
    have hα : 0 < intervalDensity N S := intervalDensity_pos (by omega) hnonempty
    have hα1 : intervalDensity N S ≤ 1 := intervalDensity_le_one hS
    have hL : 0 ≤ Real.log (Real.log N) := (le_max_left _ _).trans hlarge
    have hC : 2 * C₀ ≤ Real.log (Real.log N) := (le_max_right _ _).trans hlarge
    have hfail : Real.log (Real.log N) < A * densityParameter (intervalDensity N S) ^ β + C₀ :=
      lt_of_not_ge (hno X)
    have hp := density_parameter_ge_of_invariant_failure hA hβ hL hC hfail
    have hdensity : intervalDensity N S ≤
        Real.exp 2 * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η)) := by
      calc
        _ ≤ Real.exp (2 - densityParameter (intervalDensity N S)) := density_le_exp_sub_parameter hα hα1
        _ ≤ Real.exp (2 - c * (Real.log (Real.log N)) ^ (1 + η)) := by
          apply Real.exp_le_exp.mpr
          rw [hηeq]
          linarith
        _ = _ := by simp only [sub_eq_add_neg, Real.exp_add, neg_mul]
    have hN0 : (N : ℝ) ≠ 0 := by positivity
    calc
      (extremalNumber k N : ℝ) = intervalDensity N S * N := by
        rw [← hcard]
        exact (div_mul_cancel₀ _ hN0).symm
      _ ≤ (Real.exp 2 * Real.exp (-c * (Real.log (Real.log N)) ^ (1 + η))) * N :=
        mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg N)
      _ = _ := by ring
  · have hS0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [← hcard, hS0]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ScoredPatchDensityStep
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem positive_patch_score_target_lt_one {s d N : ℕ} (A : PolynomialPatch Unit s d)
    (f : ℕ → ℝ) (hf : ∀ n < N, f n ≤ 1) {b : ℝ}
    (hscore : 0 < 𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) : b < 1 := by
  by_contra hb
  have hb1 : 1 ≤ b := le_of_not_gt hb
  have hnonpos : (𝔼 n : Fin N, (f n.val - b) * A.value (fun _ => (n.val : ℝ))) ≤ 0 := by
    calc
      _ ≤ 𝔼 _n : Fin N, (0 : ℝ) := by
        apply Finset.expect_le_expect
        intro n _
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith [hf n.val n.isLt]) (A.value_mem_Icc _).1
      _ = 0 := by simp
  exact (not_lt_of_ge hnonpos) hscore

theorem scored_patch_density_step (s : ℕ) :
    ∃ (C : ℝ) (P : ℕ), 1 ≤ C ∧ 0 < P ∧
      ∀ (d N M a₀ q₀ : ℕ) (U R V G δ : ℝ) (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ R → Real.log U ≤ V →
        Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) + (2 * s * s + 1 : ℕ) * R + V ≤
          Real.log (Real.log N) →
        let α := 𝔼 n : Fin N, f n.val
        0 < α → 0 < G → δ ≤ Real.log G → 2 ≤ densityParameter α - δ →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - G * α) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q a len : ℕ, 0 < q ∧ 1 < len ∧ (∀ n < len, a + q * n < N) ∧
          Real.log (Real.log N) - (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * R) ≤
            Real.log (Real.log len) ∧
          G * α < (𝔼 n : Fin len, f (a + q * n.val)) ∧
          densityParameter (𝔼 n : Fin len, f (a + q * n.val)) ≤ densityParameter α - δ := by
  obtain ⟨C, P, hC, hP, hreset⟩ := resource_controlled_patch_reset s
  refine ⟨C, P, hC, hP, ?_⟩
  intro d N M a₀ q₀ U R V G δ A f hN hq₀ hslice hf hU hM hLip hR hV hsize α hα hG hδ hroom hscore
  have hb1 : G * α < 1 := positive_patch_score_target_lt_one A
    (fun n => f (a₀ + q₀ * n)) (fun n hn => (hf _ (hslice n hn)).2)
    ((Real.exp_pos (-U)).trans_le hscore)
  have hb : G * α ∈ Set.Icc (0 : ℝ) 1 := ⟨(mul_pos hG hα).le, hb1.le⟩
  obtain ⟨q, a, len, hq, hlen, hin, hloss, hdense⟩ :=
    hreset d N M a₀ q₀ U R V A f hN hq₀ hslice hf hU hM hLip hR hV hsize (G * α) hb hscore
  refine ⟨q, a, len, hq, hlen, hin, hloss, hdense, ?_⟩
  exact densityParameter_drop hα hG hdense.le (le_max_right _ _) hδ hroom

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformRelativePatchSource
namespace OAI

section

namespace Erdos3

open Filter
open scoped BigOperators

theorem subquadratic_patch_descent (s : ℕ) {κ H₀ K q A₀ B D : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A₀) (hB : 0 < B) (hD : 0 < D) :
    let μ := levelCoefficient K * Real.log q
    let ν := gainExponent K
    let β := 1 - (ν - μ) / 2
    ∃ c p₀ Cmin : ℝ, 0 < c ∧ 0 ≤ Cmin ∧
      ∀ C₀ : ℝ, Cmin ≤ C₀ → ∀ p : ℝ, p₀ ≤ p → ∀ (d N M a₀ q₀ : ℕ) (U : ℝ)
        (A : PolynomialPatch Unit s d) (f : ℕ → ℝ),
        1 < N → 0 < q₀ → (∀ n < M, a₀ + q₀ * n < N) →
        (∀ n < N, f n ∈ Set.Icc (0 : ℝ) 1) → 1 ≤ U →
        Real.log N - U ≤ Real.log M → (A.kernel.lip : ℝ) + 1 ≤ Real.exp U →
        Real.log ((d : ℝ) + 1) ≤ B * p ^ μ * Real.log (2 + p) →
        Real.log U ≤ D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) →
        A₀ * p ^ β + C₀ ≤ Real.log (Real.log N) →
        let α := 𝔼 n : Fin N, f n.val
        let G := κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2
        0 < α → densityParameter α = p →
        Real.exp (-U) ≤ (𝔼 n : Fin M,
          (f (a₀ + q₀ * n.val) - G * α) * A.value (fun _ => (n.val : ℝ))) →
        ∃ q' a len : ℕ, 0 < q' ∧ 1 < len ∧ (∀ n < len, a + q' * n < N) ∧
          0 < (𝔼 n : Fin len, f (a + q' * n.val)) ∧
          let p' := densityParameter (𝔼 n : Fin len, f (a + q' * n.val))
          p' ≤ p - c * p ^ ν ∧ p' + 1 ≤ p ∧
            A₀ * p' ^ β + C₀ ≤ Real.log (Real.log len) := by
  intro μ ν β
  obtain ⟨C, P, hC, hP, hstep⟩ := scored_patch_density_step s
  obtain ⟨c, hc, hdrop⟩ := exists_selected_density_drop hκ hH hK
  let Cmin := max 0 (Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)))
  have hCmin : 0 ≤ Cmin := le_max_left _ _
  have hbase : Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) ≤ Cmin := le_max_right _ _
  have hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hL : 0 ≤ Real.log (4 * (P : ℝ)) := Real.log_nonneg (by linarith)
  have hbudgets := subquadratic_patch_iteration_budgets hK hq hq2 hA hc hB hD hL (2 * s * s)
  have hν : 0 < ν := (gainExponent_pos_le_quarter hK).1
  have hlarge := (tendsto_rpow_atTop hν).eventually_ge_atTop (1 / c)
  have hall : ∀ᶠ p : ℝ in atTop, 1 ≤ p ∧
      ((2 * s * s + 1 : ℕ) * B * p ^ μ * Real.log (2 + p) +
        D * p ^ (1 / 4 : ℝ) * Real.log (2 + p) ≤ A₀ * p ^ β) ∧
      (Real.log (4 * (P : ℝ)) + (2 * s * s : ℕ) * B * p ^ μ * Real.log (2 + p) ≤
        A₀ * (β * c * p ^ (β + ν - 1))) ∧
      (c * p ^ ν ≤ Real.log (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log p⌋₊ / 2)) ∧
      2 ≤ p - c * p ^ ν ∧ 1 ≤ c * p ^ ν := by
    filter_upwards [hbudgets, hdrop, hlarge, eventually_ge_atTop (1 : ℝ)] with p hbud hd hu hp
    refine ⟨hp, hbud.1, hbud.2, hd.1, hd.2, ?_⟩
    have h := (div_le_iff₀ hc).mp hu
    simpa only [mul_comm] using h
  obtain ⟨p₀, hp₀⟩ := eventually_atTop.mp hall
  refine ⟨c, p₀, Cmin, hc, hCmin, ?_⟩
  intro C₀ hreserve p hp d N M a₀ q₀ U A f hN hq₀ hslice hf hU hM hLip hRank hResource hinvariant α G hα hpα hscore
  obtain ⟨hp1, hfit, hpaid, hgain, hroom, hunit⟩ := hp₀ p hp
  have hp0 : 0 < p := by linarith
  let R := B * p ^ μ * Real.log (2 + p)
  let V := D * p ^ (1 / 4 : ℝ) * Real.log (2 + p)
  have hsize : Real.log (4 * (P : ℝ) * (Real.log (2 * C) + 3)) +
      (2 * s * s + 1 : ℕ) * R + V ≤ Real.log (Real.log N) := by
    have hfit' : (2 * s * s + 1 : ℕ) * R + V ≤ A₀ * p ^ β := by
      simpa only [R, V, mul_assoc] using hfit
    linarith
  have hH0 : 0 < H₀ := by nlinarith
  have hG : 0 < G := div_pos (mul_pos hκ (amplificationGain_pos hκ hH0 _)) (by norm_num)
  have hpmean : densityParameter (𝔼 n : Fin N, f n.val) = p := hpα
  obtain ⟨q', a, len, hq', hlen, hin, hloss, hdense, hparam⟩ :=
    hstep d N M a₀ q₀ U R V G (c * p ^ ν) A f hN hq₀ hslice hf hU hM hLip
      hRank hResource hsize hα hG hgain (by simpa only [hpmean] using hroom) hscore
  rw [hpmean] at hparam
  refine ⟨q', a, len, hq', hlen, hin, (mul_pos hG hα).trans hdense, hparam, by linarith, ?_⟩
  obtain ⟨_, _, _, _, hβ, hβ1, _⟩ := subquadratic_rank_exponents hK hq hq2
  apply density_invariant_with_general_loss hp0
    ((by norm_num : (0 : ℝ) ≤ 2).trans (densityParameter_ge_two _))
    (by linarith) hβ1.le hA.le hinvariant hparam hloss
  simpa only [R, mul_assoc] using hpaid

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem quantitative_density_of_patch_source_s2_oai {k s : ℕ} (hk : 0 < k)
    {κ H₀ K q A₀ B D pmin Csrc : ℝ}
    (hκ : 0 < κ) (hH : 1 < κ * H₀) (hK : 2 ≤ K) (hq : 1 ≤ q) (hq2 : q < 2)
    (hA : 0 < A₀) (hB : 0 < B) (hD : 0 < D)
    (hsource : SubquadraticPatchSource k s κ H₀ K q A₀ B D pmin Csrc) :
    QuantitativeDensityBound k := by
  let μ := levelCoefficient K * Real.log q
  let ν := gainExponent K
  let β := 1 - (ν - μ) / 2
  obtain ⟨c, p₀, Cdesc, _, _, hdesc⟩ := subquadratic_patch_descent s hκ hH hK hq hq2 hA hB hD
  let T := max pmin p₀
  obtain ⟨C₀, hC₀, _, hclosed⟩ := no_interval_invariant_of_descent_s2 k T (max Csrc Cdesc)
  have hCsrc : Csrc ≤ C₀ := (le_max_left _ _).trans hC₀
  have hCdesc : Cdesc ≤ C₀ := (le_max_right _ _).trans hC₀
  obtain ⟨_, _, _, _, hβ, hβ1, _⟩ := subquadratic_rank_exponents hK hq hq2
  apply quantitative_density_of_no_invariant hk hA (by dsimp [β, ν, μ]; linarith : 0 < β) hβ1
  apply hclosed A₀ β hA.le
  intro S hinvariant hlarge
  have hpmin : pmin ≤ S.parameter := (le_max_left _ _).trans hlarge.le
  have hp₀ : p₀ ≤ S.parameter := (le_max_right _ _).trans hlarge.le
  have hsourceSize : A₀ * S.parameter ^ β + Csrc ≤ Real.log (Real.log S.length) := by linarith
  obtain ⟨d, M, a, q₀, U, A, hq₀, hslice, hU, hM, hLip, hRank, hResource, hscore⟩ :=
    hsource S hpmin hsourceSize
  have hmean : (𝔼 n : Fin S.length, intervalIndicator S.points n.val) = S.density :=
    mean_intervalIndicator S.subset
  have hpositive : 0 < (𝔼 n : Fin S.length, intervalIndicator S.points n.val) := by
    rw [hmean]
    exact S.density_pos
  have hpmean : densityParameter (𝔼 n : Fin S.length, intervalIndicator S.points n.val) = S.parameter :=
    congrArg densityParameter hmean
  have hscore' : Real.exp (-U) ≤ (𝔼 n : Fin M,
      (intervalIndicator S.points (a + q₀ * n.val) -
        (κ * amplificationGain κ H₀ ⌊levelCoefficient K * Real.log S.parameter⌋₊ / 2) *
          (𝔼 j : Fin S.length, intervalIndicator S.points j.val)) * A.value (fun _ => (n.val : ℝ))) := by
    simpa only [hmean] using hscore
  obtain ⟨q', a', len, hq', hlen, _, hnewpos, _, hunit, hnewinv⟩ :=
    hdesc C₀ hCdesc S.parameter hp₀ d S.length M a q₀ U A (intervalIndicator S.points)
      S.length_gt_one hq₀ hslice (fun n _ => intervalIndicator_mem_Icc S.points n)
      hU hM hLip hRank hResource hinvariant hpositive hpmean hscore'
  have hnewmean := mean_progression_indicator S.points a' q' len
  have hpos : 0 < intervalDensity len (progressionPreimage S.points a' q' len) := by
    rw [← hnewmean]
    exact hnewpos
  let S' := S.reindex a' q' len hq' hlen hpos
  refine ⟨S', ?_, ?_⟩
  · change A₀ * densityParameter (intervalDensity len (progressionPreimage S.points a' q' len)) ^ β + C₀ ≤
      Real.log (Real.log len)
    rw [← hnewmean]
    exact hnewinv
  · change densityParameter (intervalDensity len (progressionPreimage S.points a' q' len)) + 1 ≤ S.parameter
    rw [← hnewmean]
    exact hunit

end Erdos3

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.quantitative_density_of_patch_source_s2_oai := @OAI.Erdos3.quantitative_density_of_patch_source_s2_oai
