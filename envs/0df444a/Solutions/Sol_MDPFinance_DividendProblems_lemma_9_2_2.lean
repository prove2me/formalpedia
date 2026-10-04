-- Prove2me | solution 1 for MDPFinance.DividendProblems.lemma_9_2_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T19:57:52.507706+00:00
-- url     : https://prove2.me/submissions/f10f9f39-5094-4cf7-8f94-e0af12adb3a9

import Mathlib
import Definitions.Def_MDPFinance_DividendProblems_MDM
import Definitions.Def_MDPFinance_DividendProblems_Dividend

open scoped ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter MDPFinance.DividendProblems

namespace Div922

variable (M : DividendModel)

theorem q_nonneg (k : ℤ) : 0 ≤ M.q k := ENNReal.toReal_nonneg

theorem q_summable : Summable M.q :=
  ENNReal.summable_toReal (by rw [M.Zpmf.tsum_coe]; exact ENNReal.one_ne_top)

theorem q_sum : ∑' k, M.q k = 1 := by
  unfold DividendModel.q
  rw [← ENNReal.tsum_toReal_eq (fun k => M.Zpmf.apply_ne_top k), M.Zpmf.tsum_coe]
  rfl

theorem EZplus_nonneg : 0 ≤ M.EZplus :=
  tsum_nonneg fun k => mul_nonneg (q_nonneg M k) (le_max_right _ _)

theorem step_lint (x : ℤ) (a : ℕ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) = ∑' k, M.Zpmf k * f (DividendModel.Tnext x a k) := by
  show ∫⁻ y, f y ∂(M.Zpmf.map (DividendModel.Tnext x a)).toMeasure = _
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _),
    lintegral_map (measurable_of_countable _) (measurable_of_countable _), lintegral_countable']
  congr 1
  funext k
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), mul_comm]

/-- `∑ q_k (c + A k⁺) = c + A 𝔼Z⁺`, as an `ℝ≥0∞` identity. -/
theorem tsum_bound (c A : ℝ) (hc : 0 ≤ c) (hA : 0 ≤ A) :
    ∑' k, M.Zpmf k * ENNReal.ofReal (c + A * max (k : ℝ) 0) =
      ENNReal.ofReal (c + A * M.EZplus) := by
  have hs1 : Summable fun k => c * M.q k := (q_summable M).mul_left c
  have hs2 : Summable fun k => A * (M.q k * max (k : ℝ) 0) := M.hEZplus.mul_left A
  have hsum : Summable fun k => M.q k * (c + A * max (k : ℝ) 0) := by
    refine (hs1.add hs2).congr fun k => ?_
    ring
  have hnn : ∀ k, 0 ≤ M.q k * (c + A * max (k : ℝ) 0) := fun k =>
    mul_nonneg (q_nonneg M k) (by positivity)
  have : ∀ k, M.Zpmf k * ENNReal.ofReal (c + A * max (k : ℝ) 0) =
      ENNReal.ofReal (M.q k * (c + A * max (k : ℝ) 0)) := by
    intro k
    rw [ENNReal.ofReal_mul (q_nonneg M k), DividendModel.q,
      ENNReal.ofReal_toReal (M.Zpmf.apply_ne_top k)]
  simp only [this]
  rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  congr 1
  rw [show (fun k => M.q k * (c + A * max (k : ℝ) 0)) =
    fun k => c * M.q k + A * (M.q k * max (k : ℝ) 0) by funext k; ring]
  rw [hs1.tsum_add hs2, tsum_mul_left, tsum_mul_left, q_sum]
  unfold DividendModel.EZplus DividendModel.q
  ring

/-- The basic one-step estimate: from `x ≥ 0` paying `a ≤ x`, a function bounded by
`A y⁺ + B` integrates to at most `A (x - a) + B + A 𝔼Z⁺`. -/
theorem step_bound (x : ℤ) (hx : 0 ≤ x) (a : ℕ) (ha : (a : ℤ) ≤ x) (f : ℤ → ℝ≥0∞) (A B : ℝ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hf : ∀ y, f y ≤ ENNReal.ofReal (A * max (y : ℝ) 0 + B)) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) ≤
      ENNReal.ofReal (A * ((x : ℝ) - a) + B + A * M.EZplus) := by
  rw [step_lint]
  have hxa : (0 : ℝ) ≤ (x : ℝ) - a := by
    have : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
    simpa using this
  calc ∑' k, M.Zpmf k * f (DividendModel.Tnext x a k)
      ≤ ∑' k, M.Zpmf k * ENNReal.ofReal ((A * ((x : ℝ) - a) + B) + A * max (k : ℝ) 0) := by
        refine ENNReal.tsum_le_tsum fun k => mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine (hf _).trans (ENNReal.ofReal_le_ofReal ?_)
        unfold DividendModel.Tnext
        rw [if_pos hx]
        push_cast
        have : max ((x : ℝ) - a + k) 0 ≤ ((x : ℝ) - a) + max (k : ℝ) 0 := by
          apply max_le
          · linarith [le_max_left (k : ℝ) 0]
          · linarith [le_max_right (k : ℝ) 0]
        nlinarith [mul_le_mul_of_nonneg_left this hA]
    _ = ENNReal.ofReal (A * ((x : ℝ) - a) + B + A * M.EZplus) :=
        tsum_bound M _ _ (by positivity) hA

/-- From a ruined state `x < 0` the state is frozen. -/
theorem step_neg (x : ℤ) (hx : x < 0) (a : ℕ) (f : ℤ → ℝ≥0∞) :
    ∫⁻ y, f y ∂(M.toMDM.step (x, a)) = f x := by
  rw [step_lint]
  unfold DividendModel.Tnext
  simp only [if_neg (show ¬ 0 ≤ x by omega)]
  rw [ENNReal.tsum_mul_right, M.Zpmf.tsum_coe, one_mul]

theorem memD (x : ℤ) (a : ℕ) : a ∈ M.toMDM.Dx x ↔ (0 ≤ x → (a : ℤ) ≤ x) ∧ (x < 0 → a = 0) := by
  show a ∈ DividendModel.D x ↔ _
  unfold DividendModel.D
  split_ifs with h
  · simp only [Set.mem_setOf_eq]
    constructor
    · intro ha; exact ⟨fun _ => ha, fun h' => absurd h h'.not_ge⟩
    · intro ha; exact ha.1 h
  · simp only [Set.mem_singleton_iff]
    constructor
    · intro ha; exact ⟨fun h' => absurd h' h, fun _ => ha⟩
    · intro ha; exact ha.2 (lt_of_not_ge h)

/-- The bounding function `b(x) = 1 + x` on `x ≥ 0`, `0` on the ruin states. -/
noncomputable def bfun (x : ℤ) : ℝ := if 0 ≤ x then 1 + (x : ℝ) else 0

theorem bfun_le (y : ℤ) : bfun y ≤ max (y : ℝ) 0 + 1 := by
  unfold bfun; split_ifs
  · linarith [le_max_left (y : ℝ) 0]
  · linarith [le_max_right (y : ℝ) 0]

theorem bfun_nonneg (y : ℤ) : 0 ≤ bfun y := by
  unfold bfun; split_ifs with h
  · have : (0 : ℝ) ≤ y := by exact_mod_cast h
    linarith
  · exact le_rfl

theorem beta_pos : 0 < M.β := M.hβ.1
theorem beta_lt : M.β < 1 := M.hβ.2

noncomputable def K : ℝ := M.β * M.EZplus / (1 - M.β)

theorem K_nonneg : 0 ≤ K M := by
  unfold K
  exact div_nonneg (mul_nonneg (beta_pos M).le (EZplus_nonneg M)) (by linarith [beta_lt M])

theorem K_eq : K M * (1 - M.β) = M.β * M.EZplus := by
  unfold K
  field_simp [show (1 - M.β) ≠ 0 by linarith [beta_lt M]]

/-- `H(x) := x + β𝔼Z⁺/(1-β)` on `x ≥ 0`, `0` on the ruin states. -/
noncomputable def H (x : ℤ) : ℝ := if 0 ≤ x then (x : ℝ) + K M else 0

theorem H_le (y : ℤ) : H M y ≤ 1 * max (y : ℝ) 0 + K M := by
  unfold H; split_ifs
  · linarith [le_max_left (y : ℝ) 0]
  · linarith [le_max_right (y : ℝ) 0, K_nonneg M]

theorem Jnpi_le : ∀ (n : ℕ) (π : ℕ → ℤ → ℕ), M.toMDM.IsPolicyOf π → ∀ x,
    Jnpi M.toMDM π n x ≤ ENNReal.ofReal (H M x) := by
  intro n
  induction n with
  | zero => intro π _ x; exact bot_le
  | succ n ih =>
    intro π hπ x
    have hπ' : M.toMDM.IsPolicyOf (fun k => π (k + 1)) := fun k => hπ (k + 1)
    have hmem : π 0 x ∈ M.toMDM.Dx x := (hπ 0).2 x
    rw [memD] at hmem
    show M.toMDM.r (x, π 0 x) + ENNReal.ofReal M.toMDM.β *
      ∫⁻ y, Jnpi M.toMDM (fun k => π (k + 1)) n y ∂(M.toMDM.step (x, π 0 x)) ≤ _
    by_cases hx : 0 ≤ x
    · have ha := hmem.1 hx
      have hI := step_bound M x hx (π 0 x) ha _ 1 (K M) zero_le_one (K_nonneg M)
        (fun y => (ih _ hπ' y).trans (ENNReal.ofReal_le_ofReal (H_le M y)))
      have hr : M.toMDM.r (x, π 0 x) = ENNReal.ofReal (π 0 x : ℝ) := by
        show ((π 0 x : ℕ) : ℝ≥0∞) = _
        rw [ENNReal.ofReal_natCast]
      rw [hr]
      calc ENNReal.ofReal (π 0 x : ℝ) + ENNReal.ofReal M.toMDM.β *
            ∫⁻ y, Jnpi M.toMDM (fun k => π (k + 1)) n y ∂(M.toMDM.step (x, π 0 x))
          ≤ ENNReal.ofReal (π 0 x : ℝ) + ENNReal.ofReal M.β *
            ENNReal.ofReal (1 * ((x : ℝ) - π 0 x) + K M + 1 * M.EZplus) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hI (by positivity) :
              ENNReal.ofReal M.β * _ ≤ ENNReal.ofReal M.β * _)
        _ = ENNReal.ofReal ((π 0 x : ℝ) +
              M.β * (1 * ((x : ℝ) - π 0 x) + K M + 1 * M.EZplus)) := by
            rw [← ENNReal.ofReal_mul (beta_pos M).le, ← ENNReal.ofReal_add (by positivity)]
            have : (0 : ℝ) ≤ (x : ℝ) - π 0 x := by
              have : ((π 0 x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
              simpa using this
            exact mul_nonneg (beta_pos M).le (by nlinarith [K_nonneg M, EZplus_nonneg M])
        _ ≤ ENNReal.ofReal (H M x) := by
            apply ENNReal.ofReal_le_ofReal
            unfold H; rw [if_pos hx]
            have hax : ((π 0 x : ℕ) : ℝ) ≤ (x : ℝ) := by
              have : ((π 0 x : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha
              simpa using this
            have := K_eq M
            nlinarith [beta_lt M, beta_pos M]
    · have hx' : x < 0 := lt_of_not_ge hx
      have h0 := hmem.2 hx'
      rw [step_neg M x hx', h0]
      have := ih _ hπ' x
      unfold H at this ⊢
      rw [if_neg hx] at this ⊢
      rw [ENNReal.ofReal_zero, nonpos_iff_eq_zero] at this
      rw [this]
      show ((0 : ℕ) : ℝ≥0∞) + _ * 0 ≤ _
      simp

theorem Jinf_le (x : ℤ) : M.Jinf x ≤ ENNReal.ofReal (H M x) :=
  iSup₂_le fun π hπ => iSup_le fun n => Jnpi_le M n π hπ x

theorem Tcirc_bound (n : ℕ) (f : ℤ → ℝ≥0∞)
    (hf : ∀ y, f y ≤ ENNReal.ofReal (M.β ^ n * bfun y + n * M.EZplus)) (x : ℤ) :
    TcircL M.toMDM f x ≤ ENNReal.ofReal (M.β ^ (n + 1) * bfun x + (n + 1 : ℕ) * M.EZplus) := by
  refine iSup₂_le fun a ha => ?_
  rw [memD] at ha
  have hβ := beta_pos M
  have hβ1 := beta_lt M
  have hE := EZplus_nonneg M
  have hpow : 0 ≤ M.β ^ n := pow_nonneg hβ.le n
  have hpow1 : M.β ^ n ≤ 1 := pow_le_one₀ hβ.le hβ1.le
  show ENNReal.ofReal M.toMDM.β * ∫⁻ y, f y ∂(M.toMDM.step (x, a)) ≤ _
  by_cases hx : 0 ≤ x
  · have hI := step_bound M x hx a (ha.1 hx) f (M.β ^ n) (M.β ^ n + n * M.EZplus) hpow
      (by positivity) (fun y => (hf y).trans (ENNReal.ofReal_le_ofReal (by
        nlinarith [bfun_le y, mul_le_mul_of_nonneg_left (bfun_le y) hpow])))
    have hxa : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha.1 hx
    push_cast at hxa
    have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
    calc ENNReal.ofReal M.toMDM.β * ∫⁻ y, f y ∂(M.toMDM.step (x, a))
        ≤ ENNReal.ofReal M.β * ENNReal.ofReal (M.β ^ n * ((x : ℝ) - a) +
            (M.β ^ n + n * M.EZplus) + M.β ^ n * M.EZplus) := mul_le_mul_of_nonneg_left hI (by positivity)
      _ = ENNReal.ofReal (M.β * (M.β ^ n * ((x : ℝ) - a) +
            (M.β ^ n + n * M.EZplus) + M.β ^ n * M.EZplus)) := by
          rw [ENNReal.ofReal_mul hβ.le]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          unfold bfun; rw [if_pos hx]
          push_cast
          rw [pow_succ]
          have h1 : M.β ^ n * M.β * ((x : ℝ) - a) ≤ M.β ^ n * M.β * (x : ℝ) := by
            have : 0 ≤ M.β ^ n * M.β := by positivity
            nlinarith
          have h2 : M.β * (n * M.EZplus) ≤ n * M.EZplus := by
            have : 0 ≤ (n : ℝ) * M.EZplus := by positivity
            nlinarith
          have h3 : M.β * (M.β ^ n * M.EZplus) ≤ M.EZplus := by
            have : M.β * M.β ^ n ≤ 1 := by nlinarith
            nlinarith
          nlinarith
  · have hx' : x < 0 := lt_of_not_ge hx
    rw [step_neg M x hx']
    calc ENNReal.ofReal M.toMDM.β * f x
        ≤ ENNReal.ofReal M.β * ENNReal.ofReal (M.β ^ n * bfun x + n * M.EZplus) := by
          exact mul_le_mul_of_nonneg_left (hf x) (by positivity)
      _ = ENNReal.ofReal (M.β * (M.β ^ n * bfun x + n * M.EZplus)) := by
          rw [ENNReal.ofReal_mul hβ.le]
      _ ≤ _ := by
          apply ENNReal.ofReal_le_ofReal
          unfold bfun; rw [if_neg hx]
          push_cast
          have : 0 ≤ (n : ℝ) * M.EZplus := by positivity
          nlinarith

end Div922

open Div922 in
theorem solution (M : DividendModel) :
    (∃ cr αb : ℝ, IsBoundingFunction M.toMDM
        (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) cr αb) ∧
      (∀ n : ℕ, ∀ x : ℤ,
        (TcircL M.toMDM)^[n] (fun x : ℤ => ENNReal.ofReal (if 0 ≤ x then 1 + (x : ℝ) else 0)) x ≤
          ENNReal.ofReal (M.β ^ n * (if 0 ≤ x then 1 + (x : ℝ) else 0) + n * M.EZplus)) ∧
      (∀ x : ℤ, 0 ≤ x → M.Jinf x ≤ ENNReal.ofReal ((x : ℝ) + M.β * M.EZplus / (1 - M.β))) ∧
      (∀ x, M.Jinf x < ⊤) ∧
      (fun x => (M.Jinf x).toReal) ∈ IBb (fun x : ℤ => if 0 ≤ x then 1 + (x : ℝ) else 0) := by
  have hE := EZplus_nonneg M
  refine ⟨⟨1, 1 + M.EZplus, ?_⟩, ?_, ?_, ?_, ?_⟩
  · refine ⟨measurable_of_countable _, bfun_nonneg, zero_le_one, by positivity, ?_, ?_⟩
    · rintro ⟨x, a⟩ hxa
      have ha : a ∈ M.toMDM.Dx x := hxa
      rw [memD] at ha
      show ((a : ℕ) : ℝ≥0∞) ≤ _
      rw [← ENNReal.ofReal_natCast]
      apply ENNReal.ofReal_le_ofReal
      split_ifs with hx
      · have : ((a : ℤ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast ha.1 hx
        push_cast at this; linarith
      · rw [ha.2 (lt_of_not_ge hx)]; simp
    · rintro ⟨x, a⟩ hxa
      have ha : a ∈ M.toMDM.Dx x := hxa
      rw [memD] at ha
      by_cases hx : 0 ≤ x
      · refine (step_bound M x hx a (ha.1 hx) _ 1 1 zero_le_one zero_le_one
          (fun y => ENNReal.ofReal_le_ofReal (by have := bfun_le y; unfold bfun at this; linarith))).trans
          (ENNReal.ofReal_le_ofReal ?_)
        show _ ≤ (1 + M.EZplus) * (if 0 ≤ x then 1 + (x : ℝ) else 0)
        rw [if_pos hx]
        have hx0 : (0 : ℝ) ≤ x := by exact_mod_cast hx
        have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
        nlinarith
      · rw [step_neg M x (lt_of_not_ge hx)]
        show ENNReal.ofReal (bfun x) ≤ _
        unfold bfun; rw [if_neg hx]; simp
  · intro n
    induction n with
    | zero =>
      intro x
      simp only [Function.iterate_zero, id_eq, pow_zero, one_mul, Nat.cast_zero, zero_mul,
        add_zero, le_refl]
    | succ n ih =>
      intro x
      rw [Function.iterate_succ_apply']
      exact Tcirc_bound M n _ (fun y => ih y) x
  · intro x hx
    refine (Jinf_le M x).trans (ENNReal.ofReal_le_ofReal ?_)
    unfold H K; rw [if_pos hx]
  · intro x
    exact lt_of_le_of_lt (Jinf_le M x) ENNReal.ofReal_lt_top
  · refine ⟨measurable_of_countable _, max 1 (K M), le_max_of_le_left zero_le_one, fun x => ?_⟩
    have h1 := Jinf_le M x
    have h2 : (M.Jinf x).toReal ≤ H M x := by
      have hH : 0 ≤ H M x := by
        unfold H; split_ifs with h
        · have : (0 : ℝ) ≤ x := by exact_mod_cast h
          linarith [K_nonneg M]
        · exact le_rfl
      exact (ENNReal.toReal_le_of_le_ofReal hH h1)
    show |(M.Jinf x).toReal| ≤ max 1 (K M) * (if 0 ≤ x then 1 + (x : ℝ) else 0)
    rw [abs_of_nonneg ENNReal.toReal_nonneg]
    refine h2.trans ?_
    unfold H; split_ifs with h
    · have : (0 : ℝ) ≤ x := by exact_mod_cast h
      nlinarith [le_max_left 1 (K M), le_max_right 1 (K M)]
    · simp

#print axioms solution
