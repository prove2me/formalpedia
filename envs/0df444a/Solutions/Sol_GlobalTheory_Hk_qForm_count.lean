-- Prove2me | solution 1 for GlobalTheory.Hk.qForm_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:05.503802+00:00
-- url     : https://prove2.me/submissions/b6c409de-8d7d-457f-bf17-a90d94786bc6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_QFormCount
import Theorems.Thm_GlobalTheory_Hk_unimodal_sum_integral
import Theorems.Thm_GlobalTheory_Hk_integral_ellipse_width
import Theorems.Thm_GlobalTheory_Hk_row_count

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
open GlobalTheory GlobalTheory.Hk
namespace GlobalTheory.Hk
theorem _root_.solution : ∀ α γ l θ₁ θ₂ x : ℝ, 1 ≤ α → 1 ≤ γ → 1 ≤ x →
    {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.Finite ∧
    |(({v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}.ncard : ℕ) : ℝ) - Real.pi / Real.sqrt (α * γ) * x|
      ≤ 10 * Real.sqrt x := by
  intro α γ l θ₁ θ₂ x hα hγ hx
  have hα0 : 0 < α := by linarith
  have hγ0 : 0 < γ := by linarith
  have hx0 : 0 < x := by linarith
  choose F hF hFb using fun k : ℤ => row_count α (θ₁ + l * k) (x - γ * (k + θ₂) ^ 2) hα0
  obtain ⟨R, hR⟩ : ∃ R, R = Real.sqrt (x / γ) := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := hR ▸ Real.sqrt_nonneg _
  obtain ⟨k0, hk0⟩ : ∃ k0 : ℤ, k0 = ⌊-θ₂ - R⌋ := ⟨_, rfl⟩
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = ⌈2 * R⌉₊ + 2 := ⟨_, rfl⟩
  have hk0a : (k0 : ℝ) ≤ -θ₂ - R := by rw [hk0]; exact Int.floor_le _
  have hk0b : -θ₂ - R - 1 < (k0 : ℝ) := by rw [hk0]; exact Int.sub_one_lt_floor _
  have hna : 2 * R + 2 ≤ (n : ℝ) := by
    rw [hn]; push_cast; linarith [Nat.le_ceil (2 * R)]
  have hnb : (n : ℝ) < 2 * R + 3 := by
    rw [hn]; push_cast; linarith [Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ 2 * R)]
  have hrow : ∀ k : ℤ, γ * (k + θ₂) ^ 2 ≤ x → ∃ i ∈ Finset.range n, k = k0 + i := by
    intro k hk
    have hk' : ((k : ℝ) + θ₂) ^ 2 ≤ x / γ := by rw [le_div_iff₀ hγ0]; linarith
    rw [Real.sq_le (div_nonneg hx0.le hγ0.le), ← hR] at hk'
    have h1 : k0 ≤ k := by
      have : (k0 : ℝ) ≤ k := by linarith [hk'.1]
      exact_mod_cast this
    have h2 : k < k0 + n := by
      have : (k : ℝ) < k0 + n := by linarith [hk'.2]
      exact_mod_cast this
    refine ⟨(k - k0).toNat, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · omega
  have hset : {v : ℤ × ℤ | qForm α γ l θ₁ θ₂ v ≤ x}
      = ↑((Finset.range n).biUnion (fun i : ℕ => (F (k0 + i)).image (fun m => (m, k0 + (i : ℤ))))) := by
    ext ⟨m, k⟩
    simp only [Set.mem_setOf_eq, Finset.coe_biUnion, Finset.coe_image, Set.mem_iUnion,
      Set.mem_image, Finset.mem_coe, Prod.mk.injEq, qForm]
    constructor
    · intro hq
      have hk : γ * ((k : ℝ) + θ₂) ^ 2 ≤ x := by
        have := mul_nonneg hα0.le (sq_nonneg ((m : ℝ) + θ₁ + l * k))
        linarith
      obtain ⟨i, hi, rfl⟩ := hrow k hk
      refine ⟨i, hi, m, ?_, rfl, rfl⟩
      rw [hF]
      push_cast at hq ⊢
      have e : (m : ℝ) + (θ₁ + l * ((k0 : ℝ) + i)) = m + θ₁ + l * ((k0 : ℝ) + i) := by ring
      rw [e]
      linarith
    · rintro ⟨i, hi, m', hm', h1, h2⟩
      subst h1 h2
      rw [hF] at hm'
      push_cast at hm' ⊢
      have e : (m' : ℝ) + (θ₁ + l * ((k0 : ℝ) + i)) = m' + θ₁ + l * ((k0 : ℝ) + i) := by ring
      rw [e] at hm'
      linarith
  refine ⟨hset ▸ Finset.finite_toSet _, ?_⟩
  rw [hset, Set.ncard_coe_finset, Finset.card_biUnion]
  swap
  · intro i _ j _ hij
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro v hvi hvj
    rw [Finset.mem_image] at hvi hvj
    obtain ⟨a, _, rfl⟩ := hvi
    obtain ⟨b, _, hb⟩ := hvj
    have := congrArg Prod.snd hb
    simp only at this
    exact hij (by exact_mod_cast (add_left_cancel this).symm)
  have hcard : ∀ i ∈ Finset.range n,
      ((F (k0 + i)).image (fun m => (m, k0 + (i : ℤ)))).card = (F (k0 + i)).card :=
    fun i _ => Finset.card_image_of_injective _ (fun a b h => congrArg Prod.fst h)
  rw [Finset.sum_congr rfl hcard]
  push_cast
  have hU := unimodal_sum_integral (fun t => 2 * Real.sqrt ((x - γ * t ^ 2) / α))
    (fun t => by positivity)
    (fun s t hst => by
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0:ℝ) ≤ 2)
      apply Real.sqrt_le_sqrt
      apply div_le_div_of_nonneg_right _ hα0.le
      have := mul_le_mul_of_nonneg_left (sq_le_sq.mpr hst) hγ0.le
      linarith)
    ((k0 : ℝ) + θ₂) n
  have hE := integral_ellipse_width α γ x ((k0 : ℝ) + θ₂) ((k0 : ℝ) + θ₂ + n) hα0 hγ0 hx0
    (by rw [← hR]; linarith) (by rw [← hR]; linarith)
  beta_reduce at hU
  rw [hE] at hU
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero] at hU
  have hrowb : ∀ i ∈ Finset.range n, |((F (k0 + i)).card : ℝ)
      - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α)| ≤ 1 := by
    intro i _
    have := hFb (k0 + i)
    push_cast at this
    rw [show (k0 : ℝ) + θ₂ + i = k0 + i + θ₂ by ring]
    exact this
  have h1 : |∑ i ∈ Finset.range n, (((F (k0 + i)).card : ℝ)
      - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α))| ≤ n :=
    (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hrowb).trans (by simp))
  have hsx : (1:ℝ) ≤ Real.sqrt x := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hx
  have hRx : R ≤ Real.sqrt x := by
    rw [hR]; exact Real.sqrt_le_sqrt (div_le_self hx0.le hγ)
  have hαx : Real.sqrt (x / α) ≤ Real.sqrt x := Real.sqrt_le_sqrt (div_le_self hx0.le hα)
  calc |(∑ i ∈ Finset.range n, ((F (k0 + i)).card : ℝ)) - Real.pi / Real.sqrt (α * γ) * x|
      = |(∑ i ∈ Finset.range n, (((F (k0 + i)).card : ℝ)
          - 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α)))
        + ((∑ i ∈ Finset.range n, 2 * Real.sqrt ((x - γ * ((k0 : ℝ) + θ₂ + i) ^ 2) / α))
          - Real.pi / Real.sqrt (α * γ) * x)| := by
        rw [Finset.sum_sub_distrib]; congr 1; ring
    _ ≤ _ := abs_add_le _ _
    _ ≤ n + 2 * Real.sqrt (x / α) := add_le_add h1 hU
    _ ≤ 10 * Real.sqrt x := by linarith
end GlobalTheory.Hk
