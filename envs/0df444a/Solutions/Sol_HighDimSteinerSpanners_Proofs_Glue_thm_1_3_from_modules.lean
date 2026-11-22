-- Prove2me | solution 1 for HighDimSteinerSpanners.Proofs.Glue.thm_1_3_from_modules
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:48:29.482333+00:00
-- url     : https://prove2.me/submissions/036c5463-3eac-4ae5-a6f1-d45b2411eac6

module
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Definitions.Def_LeanPool_SteinerSpanners_Defs
public import Definitions.Def_LeanPool_SteinerSpanners_Geometry
public import Definitions.Def_LeanPool_SteinerSpanners_Glue
section
@[expose] public section
open scoped ENNReal
open HighDimSteinerSpanners
namespace HighDimSteinerSpanners.Proofs.Glue
open Classical in
private lemma glue_hc_bound_4p :
    ∀ (M_L : ℝ),
      (0 : ℝ) < M_L →
        let M : ℝ := (2 : ℝ) * M_L + (5 : ℝ);
        ∀ (p C : ℝ),
          (1 : ℝ) ≤ C →
            (1 : ℝ) ≤ C ^ p →
              (2 : ℝ) ^ (-((81 : ℝ) * M) * C ^ ((4 : ℝ) * p)) ≤
                (2 : ℝ) ^ (-((81 : ℝ) * M) * C ^ ((3 : ℝ) * p) * Real.logb (2 : ℝ) (C ^ p + (1 :
                    ℝ))) := by
  classical
  intro M_L hML_pos M p C hC hCp1
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hexp_le : C ^ p + 1 ≤ (2 : ℝ) ^ (C ^ p) := by
    have h2log2 : (1 : ℝ) ≤ 2 * Real.log 2 := by
      have hexp4 : Real.exp 1 ≤ (4 : ℝ) := by linarith [Real.exp_one_lt_d9]
      have hlog4 : Real.log (Real.exp 1) ≤ Real.log 4 :=
        Real.log_le_log (Real.exp_pos 1) hexp4
      have h4eq : Real.log (4 : ℝ) = 2 * Real.log 2 := by
        have : (4 : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
        rw [this, Real.log_pow]; ring
      rw [Real.log_exp, h4eq] at hlog4
      exact hlog4
    have hlin : C ^ p + 1 ≤ 2 * (1 + (C ^ p - 1) * Real.log 2) := by nlinarith
    have hexp_t : 1 + (C ^ p - 1) * Real.log 2 ≤ Real.exp ((C ^ p - 1) * Real.log 2) := by
      linarith [Real.add_one_le_exp ((C ^ p - 1) * Real.log 2)]
    have hrpow_eq : (2 : ℝ) ^ (C ^ p) = 2 * Real.exp ((C ^ p - 1) * Real.log 2) := by
      have hsplit : C ^ p = 1 + (C ^ p - 1) := by ring
      rw [hsplit, Real.rpow_add (by norm_num), Real.rpow_one,
        Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      congr 2; ring
    linarith
  have hlog_Cp : Real.logb 2 (C ^ p + 1) ≤ C ^ p := by
    have hb : Real.logb 2 (C ^ p + 1) ≤ Real.logb 2 ((2 : ℝ) ^ (C ^ p)) :=
      Real.logb_le_logb_of_le (by norm_num) (by positivity) hexp_le
    rwa [Real.logb_rpow (by norm_num) (by norm_num)] at hb
  have hC4p : C ^ (3 * p) * C ^ p = C ^ (4 * p) := by
    rw [← Real.rpow_add (by positivity)]
    congr 1; ring
  have hMC_nn : 0 ≤ 81 * M * C ^ (3 * p) := by dsimp [M]; positivity
  have hmul := mul_le_mul_of_nonneg_left hlog_Cp hMC_nn
  have hrhs : 81 * M * C ^ (3 * p) * C ^ p = 81 * M * C ^ (4 * p) := by
    rw [mul_assoc, hC4p]
  linarith
private lemma spanner_exponent_bound (M_L : ℝ) (C₁ L : ℕ) (hC₁ : 3 ≤ C₁)
    (hL_ub : (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) :
    ((2 * L + 5 : ℕ) : ℝ) ≤ (2 * M_L + 5) * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
  have hC1_pow : (1 : ℝ) ≤ (C₁ : ℝ) ^ 3 := by
    have : (1 : ℝ) ≤ (C₁ : ℝ) := by exact_mod_cast (by omega : 1 ≤ C₁)
    exact one_le_pow₀ this
  have hlog1 : (1 : ℝ) ≤ Real.logb 2 (C₁ : ℝ) := by
    have h1 : Real.logb 2 (2 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
    have h2 : Real.logb 2 (2 : ℝ) ≤ Real.logb 2 (C₁ : ℝ) :=
      Real.logb_le_logb_of_le (by norm_num) (by norm_num) (by exact_mod_cast (by omega : 2 ≤ C₁))
    linarith
  have hprod1 : (1 : ℝ) ≤ (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by nlinarith
  push_cast
  nlinarith
end HighDimSteinerSpanners.Proofs.Glue
end
end

set_option autoImplicit true
@[expose] public section
public section
open scoped ENNReal
open HighDimSteinerSpanners
open HighDimSteinerSpanners HighDimSteinerSpanners.Proofs HighDimSteinerSpanners.Proofs.Glue
namespace HighDimSteinerSpanners.Proofs.Glue
theorem _root_.solution
    (h21b : ∀ (N q L rStar C₁ : ℕ), 2 ≤ N → 2 ≤ q → 1 ≤ rStar → N = 2 ^ L * rStar →
      ∀ (p C : ℝ), 1 ≤ p → 1 ≤ C → ⌈C ^ p⌉₊ ≤ C₁ →
        (∀ x y : Fin N → Fin q,
          lpDist p (oneHotEmbed x) (oneHotEmbed y) = (2 * (hammingDist x y : ℝ)) ^ (1 / p)) ∧
        (∀ (X : Finset (Fin N → Fin q)),
          2 ≤ X.card →
          (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) →
          ∀ (e : Fin X.card ≃ ↥X),
            let P : Fin X.card → (Fin (N * q) → ℝ) := fun i => oneHotEmbed (e i).val
            (∀ i : Fin X.card, ∀ k : Fin (N * q), P i k = 0 ∨ P i k = 1) ∧
            Function.Injective P ∧
            aspectRatio p P ≤ (2 : ℝ) ^ (L + 1) ∧
            ∀ (S : Type) [Fintype S]
              (H : SimpleGraph (Fin X.card ⊕ S))
              (w : Sym2 (Fin X.card ⊕ S) → ℝ),
              IsNonMetricSteinerSpanner p P C H w →
              ∃ G_hat : SimpleGraph ↥X,
                Nat.card G_hat.edgeSet ≤ Nat.card H.edgeSet ∧
                (∀ a b : ↥X, G_hat.Adj a b →
                  0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) ∧
                (∀ x y : ↥X, hammingDist x.val y.val = rStar →
                  ∃ q_walk : G_hat.Walk x y,
                    q_walk.IsPath ∧
                    ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar)))
    (h22a : ∀ (C₁ rStar N q K : ℕ), 2 ≤ C₁ → 1 ≤ rStar → 2 ≤ N → 2 ≤ q → 1 ≤ K →
      ∀ (X : Finset (Fin N → Fin q)) (G_hat : SimpleGraph ↥X)
        (L : ↥X → ↥X → Finset ↥X),
        (∀ a b : ↥X, G_hat.Adj a b →
          0 < hammingDist a.val b.val ∧ hammingDist a.val b.val ≤ C₁ * rStar) →
        (∀ x y : ↥X, hammingDist x.val y.val = rStar →
          ∃ q_walk : G_hat.Walk x y,
            q_walk.IsPath ∧ ∀ z ∈ q_walk.support, hammingDist x.val z.val ≤ C₁ * rStar) →
        ListSizeCond C₁ rStar K X L →
        OverlapCond C₁ rStar K X →
        ListHitCond C₁ rStar X L →
        (exactDistPairs X rStar).card ≤ 2 * K ^ 2 * Nat.card G_hat.edgeSet)
    (h23 : ∃ M_L : ℝ, 0 < M_L ∧
      ∀ C₁ : ℕ, 3 ≤ C₁ →
        ∃ (L q K R₀ : ℕ) (μ₀ : ℝ),
          2 ≤ L ∧ (L : ℝ) ≤ M_L * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ∧
          2 ≤ q ∧ K = 20 * C₁ ^ 2 ∧ 160 * C₁ < R₀ ∧ 0 < μ₀ ∧
          let c : ℝ := (2 : ℝ) ^ (-((2 * L + 5 : ℕ) : ℝ))
          ∀ rStar : ℕ, R₀ ≤ rStar →
            let N : ℕ := 2 ^ L * rStar
            ∃ (X : Finset (Fin N → Fin q)) (L_X : ↥X → ↥X → Finset ↥X),
              2 ≤ X.card ∧
              (2 : ℝ) / 5 * μ₀ * (rStar : ℝ) ≤ Real.logb 2 (X.card : ℝ) ∧
              Real.logb 2 (X.card : ℝ) ≤ (3 : ℝ) / 2 * μ₀ * (rStar : ℝ) ∧
              (1 : ℝ) / 192 * (X.card : ℝ) ^ (1 + c) ≤ ((exactDistPairs X rStar).card : ℝ) ∧
              (∀ x ∈ X, ∀ y ∈ X, x ≠ y → (rStar : ℝ) / 2 ≤ (hammingDist x y : ℝ)) ∧
              ListSizeCond C₁ rStar K X L_X ∧
              OverlapCond C₁ rStar K X ∧
              ListHitCond C₁ rStar X L_X) :
    ∃ (M : ℝ) (c c₀ β₁ β₂ A : ℕ → ℝ),
      0 < M ∧
      (∀ C₁ : ℕ, 3 ≤ C₁ →
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤ c C₁ ∧
        0 < c₀ C₁ ∧ 0 < β₁ C₁ ∧ β₁ C₁ ≤ β₂ C₁ ∧ 0 < A C₁) ∧
      ∀ (p : ℝ), 1 ≤ p →
        ∀ (C : ℝ), 1 ≤ C →
          let C₁ : ℕ := max 3 ⌈C ^ p⌉₊
          (2 : ℝ) ^ (-(81 * M) * C ^ (4 * p)) ≤
            (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ∧
          (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c C₁ ∧
          ∃ nSeq : ℕ → ℕ, StrictMono nSeq ∧ (∀ j : ℕ, 2 ≤ nSeq j) ∧
            ∀ j : ℕ,
              ∃ (d : ℕ) (P : Fin (nSeq j) → (Fin d → ℝ)),
                1 ≤ d ∧
                β₁ C₁ * Real.logb 2 (nSeq j : ℝ) ≤ (d : ℝ) ∧
                (d : ℝ) ≤ β₂ C₁ * Real.logb 2 (nSeq j : ℝ) ∧
                (∀ i : Fin (nSeq j), ∀ k : Fin d, P i k = 0 ∨ P i k = 1) ∧
                Function.Injective P ∧
                aspectRatio p P ≤ A C₁ ∧
                ∀ (S : Type) [Fintype S]
                  (H : SimpleGraph (Fin (nSeq j) ⊕ S))
                  (w : Sym2 (Fin (nSeq j) ⊕ S) → ℝ),
                  IsNonMetricSteinerSpanner p P C H w →
                  c₀ C₁ * (nSeq j : ℝ) ^ (1 + c C₁) ≤ (Nat.card H.edgeSet : ℝ) := by
  obtain ⟨M_L, hML_pos, h23_C1⟩ := h23
  choose L_f q_f K_f R0_f mu_f h_spec using fun (C₁ : {x : ℕ // 3 ≤ x}) => h23_C1 C₁.1 C₁.2
  let M : ℝ := 2 * M_L + 5
  let c_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then (2 : ℝ) ^ (-((2 * L_f ⟨C₁, h⟩ + 5 : ℕ) : ℝ)) else 1
  let c0_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 1 / (384 * (K_f ⟨C₁, h⟩ : ℝ) ^ 2) else 1
  let beta1_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 2 * (2 : ℝ) ^ (L_f ⟨C₁, h⟩) * (q_f ⟨C₁, h⟩ : ℝ) / (3 * mu_f ⟨C₁, h⟩) else 1
  let beta2_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then 5 * (2 : ℝ) ^ (L_f ⟨C₁, h⟩) * (q_f ⟨C₁, h⟩ : ℝ) / (2 * mu_f ⟨C₁, h⟩) else 1
  let A_fn (C₁ : ℕ) : ℝ :=
    if h : 3 ≤ C₁ then (2 : ℝ) ^ (L_f ⟨C₁, h⟩ + 1) else 1
  have hc_C1 : ∀ (C₁ : ℕ) (hC₁ : 3 ≤ C₁),
      ((2 * L_f ⟨C₁, hC₁⟩ + 5 : ℕ) : ℝ) ≤ M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) := by
    intro C₁ hC₁
    exact spanner_exponent_bound M_L C₁ (L_f ⟨C₁, hC₁⟩) hC₁ (h_spec ⟨C₁, hC₁⟩).2.1
  refine ⟨M, c_fn, c0_fn, beta1_fn, beta2_fn, A_fn, by positivity, ?_, ?_⟩
  · intro C₁ hC₁
    simp only [c_fn, c0_fn, beta1_fn, beta2_fn, A_fn, dif_pos hC₁]
    obtain ⟨hL2, _, hq2, hK_eq, hR0, hmu_pos, _⟩ := h_spec ⟨C₁, hC₁⟩
    have hc_le :
        (2 : ℝ) ^ (-M * (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ)) ≤
          (2 : ℝ) ^ (-((2 * L_f ⟨C₁, hC₁⟩ + 5 : ℕ) : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      linarith [hc_C1 C₁ hC₁]
    have hK_pos : (0 : ℝ) < (K_f ⟨C₁, hC₁⟩ : ℝ) := by
      rw [hK_eq]; push_cast; positivity
    refine ⟨hc_le, by positivity, by positivity, ?_, by positivity⟩
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0 : ℝ) ≤ (2 : ℝ) ^ L_f ⟨C₁, hC₁⟩ * (q_f ⟨C₁, hC₁⟩ : ℝ) := by positivity
    nlinarith
  · intro p hp C hC
    dsimp only
    set C₁ : ℕ := max 3 ⌈C ^ p⌉₊
    have hC₁ : 3 ≤ C₁ := le_max_left 3 _
    have hC₁_ceil : ⌈C ^ p⌉₊ ≤ C₁ := le_max_right 3 _
    obtain ⟨hL2, hL_ub, hq2, hK_eq, hR0, hmu_pos, h_cloud⟩ := h_spec ⟨C₁, hC₁⟩
    have hCp1 : 1 ≤ C ^ p := Real.one_le_rpow hC (by linarith)
    have hceil : (⌈C ^ p⌉₊ : ℝ) ≤ 3 * C ^ p := by
      have h1 : (⌈C ^ p⌉₊ : ℝ) < C ^ p + 1 := Nat.ceil_lt_add_one (by positivity)
      linarith
    have hC1_le : (C₁ : ℝ) ≤ 3 * C ^ p := by
      dsimp [C₁]; push_cast; exact max_le (by linarith) hceil
    have hC1_cubed : (C₁ : ℝ) ^ 3 ≤ 27 * C ^ (3 * p) := by
      calc (C₁ : ℝ) ^ 3
          ≤ (3 * C ^ p) ^ 3 := pow_le_pow_left₀ (by positivity) hC1_le 3
        _ = 27 * (C ^ p) ^ (3 : ℕ) := by ring
        _ = 27 * C ^ (p * 3) := by
            rw [← Real.rpow_natCast (C ^ p) 3, ← Real.rpow_mul (by linarith)]
            push_cast; rfl
        _ = 27 * C ^ (3 * p) := by ring_nf
    have hC1_log : Real.logb 2 (C₁ : ℝ) ≤ 3 * Real.logb 2 (C ^ p + 1) := by
      have hle_pow : (C₁ : ℝ) ≤ (C ^ p + 1) ^ (3 : ℕ) := by
        have hpos_Cp : 0 ≤ C ^ p := by linarith
        nlinarith [sq_nonneg (C ^ p), pow_nonneg hpos_Cp 3]
      have hC1_pos : (0 : ℝ) < (C₁ : ℝ) := by exact_mod_cast (by omega : 0 < C₁)
      have hb : Real.logb 2 (C₁ : ℝ) ≤ Real.logb 2 ((C ^ p + 1) ^ (3 : ℕ)) :=
        Real.logb_le_logb_of_le (by norm_num) hC1_pos hle_pow
      have heq : Real.logb 2 ((C ^ p + 1) ^ (3 : ℕ)) = 3 * Real.logb 2 (C ^ p + 1) := by
        simp only [Real.logb, Real.log_pow]; ring
      linarith
    have hc_bound_3p :
        (2 : ℝ) ^ (-(81 * M) * C ^ (3 * p) * Real.logb 2 (C ^ p + 1)) ≤ c_fn C₁ := by
      simp only [c_fn, dif_pos hC₁]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      have hlog_C1_nn : 0 ≤ Real.logb 2 (C₁ : ℝ) :=
        Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ C₁))
      have hprod :
          (C₁ : ℝ) ^ 3 * Real.logb 2 (C₁ : ℝ) ≤
            (27 * C ^ (3 * p)) * (3 * Real.logb 2 (C ^ p + 1)) :=
        mul_le_mul hC1_cubed hC1_log hlog_C1_nn (by positivity)
      have hM_nn : 0 ≤ M := by dsimp [M]; positivity
      have hMprod := mul_le_mul_of_nonneg_left hprod hM_nn
      linarith [hc_C1 C₁ hC₁]
    have hc_bound_4p :=
      @glue_hc_bound_4p M_L hML_pos p C hC hCp1
    refine ⟨hc_bound_4p, hc_bound_3p, ?_⟩
    let r_seq (j : ℕ) : ℕ := 4 ^ (j + 1) * R0_f ⟨C₁, hC₁⟩
    have hr_ge : ∀ j : ℕ, R0_f ⟨C₁, hC₁⟩ ≤ r_seq j := by
      intro j
      dsimp [r_seq]
      exact Nat.le_mul_of_pos_left _ (by positivity)
    choose X_seq LX_seq hX_spec using fun j => h_cloud (r_seq j) (hr_ge j)
    refine ⟨fun j => (X_seq j).card, ?_, fun j => (hX_spec j).1, ?_⟩
    · apply strictMono_nat_of_lt_succ
      intro j
      have h_lo := (hX_spec (j + 1)).2.1
      have h_hi := (hX_spec j).2.2.1
      have hr_pos : (0 : ℝ) < (R0_f ⟨C₁, hC₁⟩ : ℝ) := by
        have : 0 < R0_f ⟨C₁, hC₁⟩ := by omega
        exact_mod_cast this
      have h_strict_log : Real.logb 2 ((X_seq j).card : ℝ) < Real.logb 2 ((X_seq (j + 1)).card :
          ℝ) := by
        have h_r : (r_seq (j + 1) : ℝ) = 4 * (r_seq j : ℝ) := by
          dsimp [r_seq]; push_cast; ring
        have hrj_pos : (0 : ℝ) < (r_seq j : ℝ) := by
          have : 0 < r_seq j := by
            have := hr_ge j
            omega
          exact_mod_cast this
        nlinarith
      by_contra! hle
      have h1 : (0 : ℝ) < ((X_seq (j + 1)).card : ℝ) := by
        have := (hX_spec (j + 1)).1; exact_mod_cast (by omega : 0 < (X_seq (j + 1)).card)
      have hmono : Real.logb 2 ((X_seq (j + 1)).card : ℝ) ≤ Real.logb 2 ((X_seq j).card : ℝ) :=
        Real.logb_le_logb_of_le (by norm_num) h1 (by exact_mod_cast hle)
      linarith
    · intro j
      obtain ⟨hXcard2, hlog_lo, hlog_hi, hE_lb, hmin_dist, hLS, hOv, hLH⟩ := hX_spec j
      let L := L_f ⟨C₁, hC₁⟩
      let q := q_f ⟨C₁, hC₁⟩
      let K := K_f ⟨C₁, hC₁⟩
      let rStar := r_seq j
      let N := 2 ^ L * rStar
      let d := N * q
      let e : Fin (X_seq j).card ≃ ↥(X_seq j) :=
        (Fin.castOrderIso (Fintype.card_coe (X_seq j)).symm).toEquiv.trans (Fintype.equivFin
            ↥(X_seq j)).symm
      let P : Fin (X_seq j).card → (Fin d → ℝ) := fun i => oneHotEmbed (e i).val
      have hrStar1 : 1 ≤ rStar := by
        have := hr_ge j
        have : 3 ≤ (⟨C₁, hC₁⟩ : {x : ℕ // 3 ≤ x}).1 := hC₁
        omega
      have hN2 : 2 ≤ N := by
        dsimp [N]
        have : 4 ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num : 0 < 2) hL2
        nlinarith
      have hd1 : 1 ≤ d := by dsimp [d]; nlinarith
      have h_mod1 := (h21b N q L rStar C₁ hN2 hq2 hrStar1 rfl p C hp hC hC₁_ceil).2
        (X_seq j) hXcard2 hmin_dist e
      obtain ⟨hP_bool, hP_inj, hP_ar, hP_proj⟩ := h_mod1
      refine ⟨d, P, hd1, ?_, ?_, hP_bool, hP_inj, ?_, ?_⟩
      · simp only [beta1_fn, dif_pos hC₁]
        have hd_eq : (d : ℝ) = (2 : ℝ) ^ L * (q : ℝ) * (rStar : ℝ) := by
          dsimp [d, N]; push_cast; ring
        rw [hd_eq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ L * (q : ℝ) := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hlog_hi hscale
        nlinarith only [hscaled]
      · simp only [beta2_fn, dif_pos hC₁]
        have hd_eq : (d : ℝ) = (2 : ℝ) ^ L * (q : ℝ) * (rStar : ℝ) := by
          dsimp [d, N]; push_cast; ring
        rw [hd_eq, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
        have hscale : (0 : ℝ) ≤ (2 : ℝ) ^ L * (q : ℝ) := by positivity
        have hscaled := mul_le_mul_of_nonneg_left hlog_lo hscale
        nlinarith only [hscaled]
      · simp only [A_fn, dif_pos hC₁]
        exact hP_ar
      · intro S _ H w hH
        obtain ⟨G_hat, hG_edges, hG_adj, hG_path⟩ := hP_proj S H w hH
        have hK1 : 1 ≤ K := by
          dsimp [K]
          rw [hK_eq]
          change 1 ≤ 20 * C₁ ^ 2
          nlinarith only [hC₁]
        have h_charge := h22a C₁ rStar N q K (le_trans (by norm_num) hC₁) hrStar1 hN2 hq2 hK1
          (X_seq j) G_hat (LX_seq j) hG_adj hG_path hLS hOv hLH
        dsimp only [c0_fn, c_fn]
        rw [dif_pos hC₁, dif_pos hC₁]
        have hK_pos : (0 : ℝ) < (K : ℝ) ^ 2 := by
          have : 0 < K := by omega
          positivity
        have h_card_ineq : ((exactDistPairs (X_seq j) rStar).card : ℝ) ≤
            2 * (K : ℝ) ^ 2 * (Nat.card H.edgeSet : ℝ) := by
          have h1 : ((exactDistPairs (X_seq j) rStar).card : ℝ) ≤
              2 * (K : ℝ) ^ 2 * (Nat.card G_hat.edgeSet : ℝ) := by exact_mod_cast h_charge
          have h2 : (Nat.card G_hat.edgeSet : ℝ) ≤ (Nat.card H.edgeSet : ℝ) := by exact_mod_cast
              hG_edges
          nlinarith only [h1, h2]
        rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
        nlinarith only [hE_lb, h_card_ineq]
end HighDimSteinerSpanners.Proofs.Glue
