-- Prove2me | solution 1 for GuthMaynard.energy_le_of_large_values_of_three_quarters
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T21:06:26.437423+00:00
-- url     : https://prove2.me/submissions/14239ceb-6deb-4af6-b3f2-3e7889d06c32

import Mathlib
import Definitions.Def_GuthMaynard
import Theorems.Thm_GuthMaynard_heath_brown_large_values

section
namespace GuthMaynard.E111
open GuthMaynard Complex
/-!
Blueprint for Guth–Maynard Proposition 11.1 (energy bound), pp. 38–46.

`Rl W τ = ∑_{t ∈ W} e^{i t τ}`, so the paper's `R(n₁/n₂) = Rl W (log n₁ - log n₂)`.
-/
/-- `R` in logarithmic coordinates: `Rl W τ = ∑_{t ∈ W} e^{i t τ}`. -/
noncomputable def Rl (W : Finset ℝ) (τ : ℝ) : ℂ :=
  ∑ t ∈ W, Complex.exp (((t * τ : ℝ) : ℂ) * I)

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartA
open GuthMaynard Complex
lemma deriv_bound (a b c d lam : ℝ) (hlam : 0 < lam) :
    |2 * (a * c + b * d)| ≤ lam * (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) / lam := by
  have e1 : ((lam * a + c) ^ 2 + (lam * b + d) ^ 2) / lam =
      lam * (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) / lam + 2 * (a * c + b * d) := by
    field_simp; ring
  have e2 : ((lam * a - c) ^ 2 + (lam * b - d) ^ 2) / lam =
      lam * (a ^ 2 + b ^ 2) + (c ^ 2 + d ^ 2) / lam - 2 * (a * c + b * d) := by
    field_simp; ring
  have p1 : 0 ≤ ((lam * a + c) ^ 2 + (lam * b + d) ^ 2) / lam := by positivity
  have p2 : 0 ≤ ((lam * a - c) ^ 2 + (lam * b - d) ^ 2) / lam := by positivity
  rw [abs_le]; constructor <;> linarith

/-- Gallagher-type pointwise bound (replaces Lemmas 11.3 and 11.7): for `x` in `[c, c + L]`,
`|g x|² ≤ L⁻¹ ∫ |g|² + ∫ (lam |g|² + |g'|² / lam)` over `[c, c + L]`. -/
theorem sq_norm_le_avg (g g' : ℝ → ℂ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (c L : ℝ) (hL : 0 < L) (lam : ℝ) (hlam : 0 < lam) (x : ℝ) (hx : x ∈ Set.Icc c (c + L)) :
    ‖g x‖ ^ 2 ≤ (1 / L) * ∫ y in c..(c + L), ‖g y‖ ^ 2 +
      ∫ y in c..(c + L), (lam * ‖g y‖ ^ 2 + ‖g' y‖ ^ 2 / lam) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hn : ∀ y, ‖g y‖ ^ 2 = (g y).re ^ 2 + (g y).im ^ 2 := fun y => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hn' : ∀ y, ‖g' y‖ ^ 2 = (g' y).re ^ 2 + (g' y).im ^ 2 := fun y => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hderiv : ∀ y, HasDerivAt (fun y => ‖g y‖ ^ 2)
      (2 * ((g y).re * (g' y).re + (g y).im * (g' y).im)) y := by
    intro y
    have hre : HasDerivAt (fun y => (g y).re) (g' y).re y := by
      have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt y (hg y)
      simp only [Complex.reCLM_apply] at this
      exact this
    have him : HasDerivAt (fun y => (g y).im) (g' y).im y := by
      have := Complex.imCLM.hasFDerivAt.comp_hasDerivAt y (hg y)
      simp only [Complex.imCLM_apply] at this
      exact this
    have := (hre.mul hre).add (him.mul him)
    have e : (fun y => ‖g y‖ ^ 2) = fun y => (g y).re * (g y).re + (g y).im * (g y).im := by
      funext y; rw [hn]; ring
    rw [e]
    convert this using 1
    all_goals first
      | rfl
      | ring
  have hh'c : Continuous fun y => 2 * ((g y).re * (g' y).re + (g y).im * (g' y).im) := by
    fun_prop
  have hhc : Continuous fun y => ‖g y‖ ^ 2 := by fun_prop
  have hBc : Continuous fun y => lam * ‖g y‖ ^ 2 + ‖g' y‖ ^ 2 / lam := by fun_prop
  set B := ∫ y in c..(c + L), (lam * ‖g y‖ ^ 2 + ‖g' y‖ ^ 2 / lam) with hB
  have key : ∀ y ∈ Set.Icc c (c + L), ‖g x‖ ^ 2 ≤ ‖g y‖ ^ 2 + B := by
    intro y hy
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := y) (b := x)
      (fun z _ => hderiv z) (hh'c.intervalIntegrable _ _)
    have h1 := intervalIntegral.norm_integral_le_integral_norm_uIoc
      (f := fun y => 2 * ((g y).re * (g' y).re + (g y).im * (g' y).im)) (a := y) (b := x)
      (μ := MeasureTheory.volume)
    have hsub : Set.uIoc y x ⊆ Set.Ioc c (c + L) := by
      intro z hz
      rw [Set.mem_uIoc] at hz
      rcases hz with hz | hz <;> constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    have h2 : ∫ z in Set.uIoc y x, ‖2 * ((g z).re * (g' z).re + (g z).im * (g' z).im)‖ ≤
        ∫ z in Set.Ioc c (c + L), ‖2 * ((g z).re * (g' z).re + (g z).im * (g' z).im)‖ :=
      MeasureTheory.setIntegral_mono_set
        (hh'c.norm.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun z => norm_nonneg _) (Filter.Eventually.of_forall hsub)
    rw [← intervalIntegral.integral_of_le (by linarith)] at h2
    have h4 : ∫ z in c..(c + L), ‖2 * ((g z).re * (g' z).re + (g z).im * (g' z).im)‖ ≤ B :=
      intervalIntegral.integral_mono_on (by linarith) (hh'c.norm.intervalIntegrable _ _)
        (hBc.intervalIntegrable _ _) (fun z _ => by
          rw [Real.norm_eq_abs, hn, hn']; exact deriv_bound _ _ _ _ _ hlam)
    rw [hFTC, Real.norm_eq_abs] at h1
    linarith [le_abs_self (‖g x‖ ^ 2 - ‖g y‖ ^ 2)]
  have hint : ∫ y in c..(c + L), ‖g x‖ ^ 2 ≤ ∫ y in c..(c + L), (‖g y‖ ^ 2 + B) :=
    intervalIntegral.integral_mono_on (by linarith : c ≤ c + L)
      (continuous_const.intervalIntegrable _ _) ((hhc.add continuous_const).intervalIntegrable _ _) key
  rw [intervalIntegral.integral_const] at hint
  simp only [add_sub_cancel_left, smul_eq_mul] at hint
  rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hL]
  linarith

end GuthMaynard.E111.PartA
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias sq_norm_le_avg := GuthMaynard.E111.PartA.sq_norm_le_avg

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartA
open GuthMaynard Complex
lemma avg4 (g g' : ℝ → ℂ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g')
    (x : ℝ) (hx : x ∈ Set.Icc (-2 : ℝ) 2) :
    ‖g x‖ ^ 2 ≤ ∫ s in (-2 : ℝ)..2, ((5 / 4 : ℝ) * ‖g s‖ ^ 2 + ‖g' s‖ ^ 2) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have h := sq_norm_le_avg g g' hg hg' (-2) 4 (by norm_num) 1 one_pos x
    (by norm_num; exact ⟨hx.1, hx.2⟩)
  norm_num at h
  have i1 : IntervalIntegrable (fun s => ‖g s‖ ^ 2) MeasureTheory.volume (-2 : ℝ) 2 :=
    (by fun_prop : Continuous fun s => ‖g s‖ ^ 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => ‖g' s‖ ^ 2) MeasureTheory.volume (-2 : ℝ) 2 :=
    (by fun_prop : Continuous fun s => ‖g' s‖ ^ 2).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 i2] at h
  rw [intervalIntegral.integral_add i1 intervalIntegrable_const, intervalIntegral.integral_const]
    at h
  rw [intervalIntegral.integral_add (i1.const_mul _) i2, intervalIntegral.integral_const_mul]
  norm_num at h
  linarith

/-- `n^{iy}` in exponential form. -/
noncomputable def ex (n : ℕ) (y : ℝ) : ℂ := Complex.exp (((Real.log n * y : ℝ) : ℂ) * I)

lemma cpow_eq_ex (n : ℕ) (hn : 1 ≤ n) (t : ℝ) : (n : ℂ) ^ ((t : ℂ) * I) = ex n t := by
  unfold ex
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (by omega : n ≠ 0)),
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  push_cast; ring_nf

lemma hasDerivAt_ex (n : ℕ) (y : ℝ) :
    HasDerivAt (ex n) (((Real.log n : ℝ) : ℂ) * I * ex n y) y := by
  have h1 : HasDerivAt (fun y : ℝ => ((Real.log n * y : ℝ) : ℂ)) ((Real.log n : ℝ) : ℂ) y := by
    have := ((hasDerivAt_id y).const_mul (Real.log n)).ofReal_comp
    simpa using this
  have := (h1.mul_const I).cexp
  unfold ex
  convert this using 1
  ring

lemma continuous_ex (n : ℕ) : Continuous (ex n) := by unfold ex; fun_prop

lemma ex_mul_conj (n₁ n₂ : ℕ) (t₁ t₂ t₃ s : ℝ) :
    ex n₁ (t₁ + t₂ - t₃ + s) * (starRingEnd ℂ) (ex n₂ (t₁ + t₂ - t₃ + s)) =
      Complex.exp (((s * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I) *
      Complex.exp (((t₁ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I) *
      Complex.exp (((t₂ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I) *
      (starRingEnd ℂ) (Complex.exp (((t₃ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I)) := by
  unfold ex
  simp only [← Complex.exp_conj, ← Complex.exp_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

lemma swap_in {α β γ : Type*} (A : Finset α) (B : Finset β) (C : Finset γ) (G : α → β → γ → ℂ) :
    ∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, G a b c = ∑ b ∈ B, ∑ c ∈ C, ∑ a ∈ A, G a b c := by
  rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun b _ => Finset.sum_comm

lemma rev3 {α : Type*} (A : Finset α) (F : α → α → α → ℂ) :
    ∑ a₁ ∈ A, ∑ a₂ ∈ A, ∑ a₃ ∈ A, F a₁ a₂ a₃ = ∑ a₃ ∈ A, ∑ a₂ ∈ A, ∑ a₁ ∈ A, F a₁ a₂ a₃ := by
  rw [Finset.sum_congr rfl fun a₁ _ => Finset.sum_comm]
  exact swap_in A A A (fun a₁ a₃ a₂ => F a₁ a₂ a₃)

lemma swap5 {α β : Type*} (A : Finset α) (B : Finset β) (F : α → α → α → β → β → ℂ) :
    ∑ a₁ ∈ A, ∑ a₂ ∈ A, ∑ a₃ ∈ A, ∑ b₁ ∈ B, ∑ b₂ ∈ B, F a₁ a₂ a₃ b₁ b₂ =
      ∑ b₁ ∈ B, ∑ b₂ ∈ B, ∑ a₁ ∈ A, ∑ a₂ ∈ A, ∑ a₃ ∈ A, F a₁ a₂ a₃ b₁ b₂ := by
  rw [Finset.sum_congr rfl fun a₁ _ => Finset.sum_congr rfl fun a₂ _ =>
    swap_in A B B (fun a₃ b₁ b₂ => F a₁ a₂ a₃ b₁ b₂)]
  rw [Finset.sum_congr rfl fun a₁ _ =>
    swap_in A B B (fun a₂ b₁ b₂ => ∑ a₃ ∈ A, F a₁ a₂ a₃ b₁ b₂)]
  exact swap_in A B B (fun a₁ b₁ b₂ => ∑ a₂ ∈ A, ∑ a₃ ∈ A, F a₁ a₂ a₃ b₁ b₂)

/-- The pointwise (in `s`) third-moment identity, bounded. -/
lemma triple_sum_le (X : Finset ℕ) (W : Finset ℝ) (c : ℕ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hc : ∀ n ∈ X, ‖c n‖ ≤ K) (s : ℝ) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ‖∑ n ∈ X, c n * ex n (t₁ + t₂ - t₃ + s)‖ ^ 2 ≤
      K ^ 2 * ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖E111.Rl W (Real.log n₁ - Real.log n₂)‖ ^ 3 := by
  have step1 : ∀ t₁ t₂ t₃ : ℝ, ((‖∑ n ∈ X, c n * ex n (t₁ + t₂ - t₃ + s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ X, ∑ n₂ ∈ X, (c n₁ * (starRingEnd ℂ) (c n₂) *
        Complex.exp (((s * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I)) *
        Complex.exp (((t₁ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I) *
        Complex.exp (((t₂ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I) *
        (starRingEnd ℂ) (Complex.exp (((t₃ * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I)) := by
    intro t₁ t₂ t₃
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    have := ex_mul_conj n₁ n₂ t₁ t₂ t₃ s
    rw [map_mul]
    linear_combination (c n₁ * (starRingEnd ℂ) (c n₂)) * this
  have step2 : ((∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖∑ n ∈ X, c n * ex n (t₁ + t₂ - t₃ + s)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n₁ ∈ X, ∑ n₂ ∈ X, (c n₁ * (starRingEnd ℂ) (c n₂) *
        Complex.exp (((s * (Real.log n₁ - Real.log n₂) : ℝ) : ℂ) * I)) *
        E111.Rl W (Real.log n₁ - Real.log n₂) * E111.Rl W (Real.log n₁ - Real.log n₂) *
        (starRingEnd ℂ) (E111.Rl W (Real.log n₁ - Real.log n₂)) := by
    simp only [Complex.ofReal_sum]
    simp_rw [step1]
    rw [swap5]
    refine Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
    unfold E111.Rl
    simp only [map_sum, Finset.mul_sum, Finset.sum_mul]
    exact rev3 W _
  have hnn : 0 ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W,
      ‖∑ n ∈ X, c n * ex n (t₁ + t₂ - t₃ + s)‖ ^ 2 := by positivity
  rw [← abs_of_nonneg hnn, ← Real.norm_eq_abs, ← Complex.norm_real, step2, Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₁ h₁ => ?_)
  rw [Finset.mul_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n₂ h₂ => ?_)
  simp only [norm_mul, Complex.norm_conj, Complex.norm_exp_ofReal_mul_I, mul_one]
  have a1 := hc n₁ h₁
  have a2 := hc n₂ h₂
  have : ‖c n₁‖ * ‖c n₂‖ ≤ K ^ 2 := by
    rw [sq]; exact mul_le_mul a1 a2 (norm_nonneg _) hK
  have hR := norm_nonneg (E111.Rl W (Real.log n₁ - Real.log n₂))
  calc ‖c n₁‖ * ‖c n₂‖ * ‖E111.Rl W (Real.log ↑n₁ - Real.log ↑n₂)‖ *
        ‖E111.Rl W (Real.log ↑n₁ - Real.log ↑n₂)‖ * ‖E111.Rl W (Real.log ↑n₁ - Real.log ↑n₂)‖
      = (‖c n₁‖ * ‖c n₂‖) * ‖E111.Rl W (Real.log ↑n₁ - Real.log ↑n₂)‖ ^ 3 := by ring
    _ ≤ K ^ 2 * ‖E111.Rl W (Real.log ↑n₁ - Real.log ↑n₂)‖ ^ 3 :=
      mul_le_mul_of_nonneg_right this (by positivity)

lemma card_le_three (W : Finset ℝ) (hW : IsSeparated 1 W) (x : ℝ) :
    (W.filter fun t => |x - t| ≤ 1).card ≤ 3 := by
  have h : (W.filter fun t => |x - t| ≤ 1).card ≤ (Finset.Icc (0 : ℤ) 2).card := by
    apply Finset.card_le_card_of_injOn (fun t => ⌊t - x + 1⌋)
    · intro t ht
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
      have := abs_le.mp ht.2
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · exact Int.floor_nonneg.mpr (by linarith)
      · exact Int.floor_le_iff.mpr (by push_cast; linarith)
    · intro t ht t' ht' he
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
      by_contra hne
      have hs := hW t ht.1 t' ht'.1 hne
      have a1 := Int.floor_le (t - x + 1)
      have a2 := Int.lt_floor_add_one (t - x + 1)
      have b1 := Int.floor_le (t' - x + 1)
      have b2 := Int.lt_floor_add_one (t' - x + 1)
      simp only at he
      rw [he] at a1 a2
      rcases le_abs.mp hs with hs | hs <;> linarith
  simpa using h

lemma sum_int_le (W : Finset ℝ) (f : ℝ → ℝ) (hf : Continuous f) (M : ℝ)
    (hM : ∀ s, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f (t₁ + t₂ - t₃ + s) ≤ M) :
    ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∫ s in (-2 : ℝ)..2, f (t₁ + t₂ - t₃ + s) ≤ 4 * M := by
  have e : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∫ s in (-2 : ℝ)..2, f (t₁ + t₂ - t₃ + s) =
      ∫ s in (-2 : ℝ)..2, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f (t₁ + t₂ - t₃ + s) := by
    have hc : ∀ g : ℝ → ℝ, Continuous g → IntervalIntegrable g MeasureTheory.volume (-2 : ℝ) 2 :=
      fun g hg => hg.intervalIntegrable _ _
    rw [intervalIntegral.integral_finsetSum (fun _ _ => hc _ (by fun_prop))]
    refine Finset.sum_congr rfl fun t₁ _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun _ _ => hc _ (by fun_prop))]
    refine Finset.sum_congr rfl fun t₂ _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun _ _ => hc _ (by fun_prop))]
  rw [e]
  have : ∫ s in (-2 : ℝ)..2, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f (t₁ + t₂ - t₃ + s) ≤
      ∫ s in (-2 : ℝ)..2, M := intervalIntegral.integral_mono_on (by norm_num : (-2 : ℝ) ≤ 2)
    ((by fun_prop : Continuous fun s =>
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f (t₁ + t₂ - t₃ + s)).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _) (fun s _ => hM s)
  rw [intervalIntegral.integral_const, smul_eq_mul] at this
  linarith

/-- Lemma 11.4 (energy controlled by the discrete third moment), with an explicit loss. -/
theorem energy_le_third_moment (N : ℕ) (hN : 1 ≤ N) (b : ℕ → ℂ) (hb : ∀ n, ‖b n‖ ≤ 1) (σ : ℝ)
    (W : Finset ℝ) (hW : IsSeparated 1 W)
    (hD : ∀ t ∈ W, (N : ℝ) ^ σ ≤
      ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) :
    (energy W : ℝ) ≤ 20 * (1 + Real.log (2 * N)) ^ 2 * (N : ℝ) ^ (-2 * σ) *
      ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖Rl W (Real.log n₁ - Real.log n₂)‖ ^ 3 := by
  set X := Finset.Ioc N (2 * N) with hX
  set S := ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖Rl W (Real.log n₁ - Real.log n₂)‖ ^ 3 with hS
  set Lg := Real.log (2 * N) with hLg
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hLg0 : 0 ≤ Lg := Real.log_nonneg (by linarith)
  have hS0 : 0 ≤ S := by positivity
  set D : ℝ → ℂ := fun y => ∑ n ∈ X, b n * ex n y with hDdef
  set D' : ℝ → ℂ := fun y => ∑ n ∈ X, (b n * (((Real.log n : ℝ) : ℂ) * I)) * ex n y with hD'def
  have hDer : ∀ y, HasDerivAt D (D' y) y := by
    intro y
    have := HasDerivAt.sum (u := X) (A := fun n y => b n * ex n y)
      (fun n _ => (hasDerivAt_ex n y).const_mul (b n))
    convert this using 1
    all_goals first
      | rfl
      | exact Finset.sum_congr rfl fun n _ => by ring
      | (funext z; simp only [hDdef, Finset.sum_apply])
  have hD'c : Continuous D' :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_ex n)
  have hDc : Continuous D :=
    continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_ex n)
  have hDt : ∀ t ∈ W, (N : ℝ) ^ σ ≤ ‖D t‖ := by
    intro t ht
    have := hD t ht
    convert this using 2
    simp only [hDdef]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [cpow_eq_ex n (by simp only [hX, Finset.mem_Ioc] at hn; omega)]
  have h3 : 0 ≤ (N : ℝ) ^ (-2 * σ) := by positivity
  have hone : ∀ t ∈ W, 1 ≤ (N : ℝ) ^ (-2 * σ) * ‖D t‖ ^ 2 := by
    intro t ht
    have h1 : ((N : ℝ) ^ σ) ^ 2 ≤ ‖D t‖ ^ 2 := pow_le_pow_left₀ (by positivity) (hDt t ht) 2
    have h2 : (N : ℝ) ^ (-2 * σ) * ((N : ℝ) ^ σ) ^ 2 = 1 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le, ← Real.rpow_add hNpos,
        show (-2 * σ + σ * ((2 : ℕ) : ℝ)) = 0 by push_cast; ring, Real.rpow_zero]
    nlinarith
  set f : ℝ → ℝ := fun y => (5 / 4 : ℝ) * ‖D y‖ ^ 2 + ‖D' y‖ ^ 2 with hfdef
  have hfc : Continuous f := by simp only [hfdef]; fun_prop
  set F : ℝ → ℝ := fun x => ∫ s in (-2 : ℝ)..2, f (x + s) with hFdef
  have hF : ∀ x t, |x - t| ≤ 1 → ‖D t‖ ^ 2 ≤ F x := by
    intro x t h
    have := avg4 (fun s => D (x + s)) (fun s => D' (x + s))
      (fun s => HasDerivAt.comp_const_add x s (hDer (x + s)))
      (hD'c.comp (continuous_const.add continuous_id)) (t - x)
      ⟨by linarith [(abs_le.mp h).2], by linarith [(abs_le.mp h).1]⟩
    simpa only [add_sub_cancel] using this
  have hFnn : ∀ x, 0 ≤ F x := fun x =>
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => by simp only [hfdef]; positivity)
  have hE : (energy W : ℝ) ≤
      ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, 3 * ((N : ℝ) ^ (-2 * σ) * F (t₁ + t₂ - t₃)) := by
    unfold energy
    rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
    calc _ ≤ ∑ q ∈ (W ×ˢ W ×ˢ W ×ˢ W).filter
          (fun p => |p.1 + p.2.1 - p.2.2.1 - p.2.2.2| ≤ 1),
          (N : ℝ) ^ (-2 * σ) * F (q.1 + q.2.1 - q.2.2.1) := by
          refine Finset.sum_le_sum fun q hq => ?_
          simp only [Finset.mem_filter, Finset.mem_product] at hq
          exact (hone _ hq.1.2.2.2).trans (mul_le_mul_of_nonneg_left (hF _ _ hq.2) h3)
      _ = ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W, if |t₁ + t₂ - t₃ - t₄| ≤ 1 then
            (N : ℝ) ^ (-2 * σ) * F (t₁ + t₂ - t₃) else 0 := by
          rw [Finset.sum_filter]; simp only [Finset.sum_product]
      _ ≤ _ := by
          refine Finset.sum_le_sum fun t₁ _ => Finset.sum_le_sum fun t₂ _ =>
            Finset.sum_le_sum fun t₃ _ => ?_
          rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_three W hW _)
            (mul_nonneg h3 (hFnn _))
  have hcD' : ∀ n ∈ X, ‖b n * (((Real.log n : ℝ) : ℂ) * I)‖ ≤ Lg := by
    intro n hn
    simp only [hX, Finset.mem_Ioc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
    have hn2 : (n : ℝ) ≤ 2 * N := by exact_mod_cast hn.2
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hn1)]
    calc ‖b n‖ * Real.log n ≤ 1 * Lg :=
          mul_le_mul (hb n) (Real.log_le_log (by linarith) hn2) (Real.log_nonneg hn1) zero_le_one
      _ = Lg := one_mul _
  have hsum : ∀ s, ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, f (t₁ + t₂ - t₃ + s) ≤
      ((5 / 4 : ℝ) + Lg ^ 2) * S := by
    intro s
    have a1 := triple_sum_le X W b 1 zero_le_one (fun n _ => hb n) s
    have a2 := triple_sum_le X W (fun n => b n * (((Real.log n : ℝ) : ℂ) * I)) Lg hLg0 hcD' s
    simp only [hfdef, hDdef, hD'def, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [← hS] at a1 a2
    nlinarith
  have hint := sum_int_le W f hfc _ hsum
  have hE2 : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, 3 * ((N : ℝ) ^ (-2 * σ) * F (t₁ + t₂ - t₃)) =
      3 * (N : ℝ) ^ (-2 * σ) * ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, F (t₁ + t₂ - t₃) := by
    simp only [Finset.mul_sum]; ring_nf
  rw [hE2] at hE
  have hFsum : ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, F (t₁ + t₂ - t₃) ≤ 4 * (((5 / 4 : ℝ) + Lg ^ 2) * S) :=
    hint
  have key : 3 * (4 * (((5 / 4 : ℝ) + Lg ^ 2) * S)) ≤ 20 * (1 + Lg) ^ 2 * S := by
    have e : 3 * (4 * (((5 / 4 : ℝ) + Lg ^ 2) * S)) = (15 + 12 * Lg ^ 2) * S := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by nlinarith) hS0
  calc (energy W : ℝ) ≤ 3 * (N : ℝ) ^ (-2 * σ) * (4 * (((5 / 4 : ℝ) + Lg ^ 2) * S)) :=
        hE.trans (mul_le_mul_of_nonneg_left hFsum (by positivity))
    _ = (N : ℝ) ^ (-2 * σ) * (3 * (4 * (((5 / 4 : ℝ) + Lg ^ 2) * S))) := by ring
    _ ≤ (N : ℝ) ^ (-2 * σ) * (20 * (1 + Lg) ^ 2 * S) := mul_le_mul_of_nonneg_left key h3
    _ = _ := by ring

end GuthMaynard.E111.PartA
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias energy_le_third_moment := GuthMaynard.E111.PartA.energy_le_third_moment

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartC
open GuthMaynard GuthMaynard.E111 Complex
/-- `E x = e^{ix}`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_E (x : ℝ) : (starRingEnd ℂ) (E x) = E (-x) := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

lemma cpow_eq (n : ℕ) (hn : 1 ≤ n) (s : ℝ) : (n : ℂ) ^ ((s : ℂ) * I) = E (Real.log n * s) := by
  unfold E
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast (Nat.pos_of_ne_zero (by omega)).ne')]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_log (by positivity)]
  congr 1; push_cast; ring

lemma Rl_eq (W : Finset ℝ) (τ : ℝ) : Rl W τ = ∑ t ∈ W, E (t * τ) := rfl

lemma sq_eq_mul_conj (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']; push_cast; ring

lemma swap4 {α β : Type*} (A : Finset α) (B : Finset β) (f : α → α → β → β → ℂ) :
    ∑ a ∈ A, ∑ a' ∈ A, ∑ b ∈ B, ∑ b' ∈ B, f a a' b b' =
      ∑ b ∈ B, ∑ b' ∈ B, ∑ a ∈ A, ∑ a' ∈ A, f a a' b b' := by
  have h1 : ∀ a, ∑ a' ∈ A, ∑ b ∈ B, ∑ b' ∈ B, f a a' b b' =
      ∑ b ∈ B, ∑ b' ∈ B, ∑ a' ∈ A, f a a' b b' := by
    intro a
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun a _ => h1 a), Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.sum_comm]

/-- The second-moment identity, for any frequencies. -/
lemma moment_identity {ι : Type*} (X : Finset ℕ) (S : Finset ι) (f : ι → ℝ) :
    ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖∑ i ∈ S, E (f i * (Real.log n₁ - Real.log n₂))‖ ^ 2 =
      ∑ i ∈ S, ∑ i' ∈ S, ‖∑ n ∈ X, E (Real.log n * (f i - f i'))‖ ^ 2 := by
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum, sq_eq_mul_conj, map_sum, conj_E, Finset.sum_mul_sum, ← E_add]
  rw [swap4]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun n₁ _ => Finset.sum_congr rfl fun n₂ _ => ?_
  congr 1; ring

lemma split_sum (M : ℕ) (X : Finset ℕ) (hX : X ⊆ Finset.Icc M (4 * M)) (g : ℕ → ℂ) :
    ∑ n ∈ X, g n = ∑ n ∈ Finset.Icc M (2 * M), (if n ∈ X then g n else 0) +
      ∑ n ∈ Finset.Icc (2 * M) (2 * (2 * M)), (if n ∈ X ∧ 2 * M < n then g n else 0) := by
  rw [← Finset.sum_filter, ← Finset.sum_filter,
    ← Finset.sum_filter_add_sum_filter_not X (fun n => n ≤ 2 * M)]
  congr 1
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n; have := @hX n; simp only [Finset.mem_filter, Finset.mem_Icc] at this ⊢
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨⟨(this h1).1, h2⟩, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1.2⟩
  · apply Finset.sum_congr _ (fun _ _ => rfl)
    ext n; have := @hX n; simp only [Finset.mem_filter, Finset.mem_Icc] at this ⊢
    constructor
    · rintro ⟨h1, h2⟩; have := this h1; exact ⟨⟨by omega, by omega⟩, h1, by omega⟩
    · rintro ⟨_, h1, h2⟩; exact ⟨h1, by omega⟩

lemma norm_add_sq_le (u v : ℂ) : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h := norm_add_le u v
  have h0 := norm_nonneg (u + v)
  nlinarith [sq_nonneg (‖u‖ - ‖v‖), norm_nonneg u, norm_nonneg v]

/-- Heath-Brown for any `X ⊆ [M, 4M]`, any bounded coefficients. -/
lemma hbX : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (M : ℕ), 1 ≤ M →
    ∀ X : Finset ℕ, X ⊆ Finset.Icc M (4 * M) → ∀ b : ℕ → ℂ, (∀ n ∈ X, ‖b n‖ ≤ T ^ δ) →
    ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P → (∀ t ∈ P, t ∈ Set.Icc c (c + T)) →
    ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ X, b n * E (Real.log n * (t₁ - t₂))‖ ^ 2 ≤
      10 * (T ^ ε * ((P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M)) := by
  intro ε hε
  obtain ⟨δ, hδ, T₁, hT₁⟩ := heath_brown_large_values ε hε
  refine ⟨δ, hδ, max T₁ 0, fun T hT M hM X hX b hb P c hP hc => ?_⟩
  have hT0 : 0 ≤ T := (le_max_right _ _).trans hT
  have hTT := (le_max_left _ _).trans hT
  set a₁ : ℕ → ℂ := fun n => if n ∈ X then b n else 0
  set a₂ : ℕ → ℂ := fun n => if n ∈ X ∧ 2 * M < n then b n else 0
  have ha₁ : ∀ n, ‖a₁ n‖ ≤ T ^ δ := fun n => by
    simp only [a₁]; split_ifs with h
    · exact hb n h
    · simpa using Real.rpow_nonneg hT0 δ
  have ha₂ : ∀ n, ‖a₂ n‖ ≤ T ^ δ := fun n => by
    simp only [a₂]; split_ifs with h
    · exact hb n h.1
    · simpa using Real.rpow_nonneg hT0 δ
  have H1 := hT₁ T hTT M hM a₁ ha₁ P c hP hc
  have H2 := hT₁ T hTT (2 * M) (by omega) a₂ ha₂ P c hP hc
  have key : ∀ t₁ t₂ : ℝ, ∑ n ∈ X, b n * E (Real.log n * (t₁ - t₂)) =
      ∑ n ∈ Finset.Icc M (2 * M), a₁ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I) +
      ∑ n ∈ Finset.Icc (2 * M) (2 * (2 * M)), a₂ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I) := by
    intro t₁ t₂
    rw [split_sum M X hX]
    congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      have : 1 ≤ n := hM.trans (Finset.mem_Icc.mp hn).1
      simp only [a₁]; split_ifs <;> simp only [cpow_eq n this, zero_mul]
    · refine Finset.sum_congr rfl fun n hn => ?_
      have : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
      simp only [a₂]; split_ifs <;> simp only [cpow_eq n this, zero_mul]
  simp_rw [key]
  calc _ ≤ ∑ t₁ ∈ P, ∑ t₂ ∈ P,
        (2 * ‖∑ n ∈ Finset.Icc M (2 * M), a₁ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 +
         2 * ‖∑ n ∈ Finset.Icc (2 * M) (2 * (2 * M)),
            a₂ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2) :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => norm_add_sq_le _ _
    _ = 2 * ∑ t₁ ∈ P, ∑ t₂ ∈ P,
          ‖∑ n ∈ Finset.Icc M (2 * M), a₁ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 +
        2 * ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ Finset.Icc (2 * M) (2 * (2 * M)),
            a₂ n * (n : ℂ) ^ (((t₁ - t₂ : ℝ) : ℂ) * I)‖ ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ _ := by
        have hTe : 0 ≤ T ^ ε := Real.rpow_nonneg hT0 ε
        have hTh : 0 ≤ T ^ (1 / 2 : ℝ) := Real.rpow_nonneg hT0 _
        have hP : 0 ≤ (P.card : ℝ) ^ (5 / 4 : ℝ) := Real.rpow_nonneg (by positivity) _
        have hPc : (0 : ℝ) ≤ P.card := by positivity
        have hM0 : (1 : ℝ) ≤ M := by exact_mod_cast hM
        rw [Nat.cast_mul, Nat.cast_ofNat] at H2
        have h4 : (P.card : ℝ) ^ 2 * (2 * M) + (P.card : ℝ) * (2 * M) ^ 2 +
            (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * (2 * M) ≤
            4 * ((P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
            (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
          nlinarith [mul_nonneg hP hTh, mul_nonneg (mul_nonneg hP hTh) (by linarith : (0:ℝ) ≤ M),
            mul_nonneg hPc (sq_nonneg (M:ℝ)), mul_nonneg (sq_nonneg (P.card : ℝ)) (by linarith : (0:ℝ) ≤ M)]
        have := mul_le_mul_of_nonneg_left h4 hTe
        linear_combination 2 * H1 + 2 * H2 + 2 * this

lemma eventually_const_mul_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, C * T ^ (ε / 2) ≤ T ^ ε := by
  have h := (tendsto_rpow_atTop (by linarith : 0 < ε / 2)).eventually_ge_atTop C
  filter_upwards [h, Filter.eventually_ge_atTop 0] with T hT hT0
  have : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_add' hT0 (by linarith)]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hT0 _)

theorem second_moment : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (M : ℕ), 1 ≤ M →
    ∀ X : Finset ℕ, X ⊆ Finset.Icc M (4 * M) →
    ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P → (∀ t ∈ P, t ∈ Set.Icc c (c + T)) →
    ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖Rl P (Real.log n₁ - Real.log n₂)‖ ^ 2 ≤
      T ^ ε * ((P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
  intro ε hε
  obtain ⟨δ, hδ, T₁, hT₁⟩ := hbX (ε / 2) (by linarith)
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    ((eventually_const_mul_le 10 ε hε).and (Filter.eventually_ge_atTop 1))
  refine ⟨max T₁ T₂, fun T hT M hM X hX P c hP hc => ?_⟩
  obtain ⟨hC, hT1⟩ := hT₂ T ((le_max_right _ _).trans hT)
  have h := hT₁ T ((le_max_left _ _).trans hT) M hM X hX (fun _ => 1)
    (fun n _ => by simpa using Real.one_le_rpow hT1 hδ.le) P c hP hc
  simp only [Rl_eq]
  have hid := moment_identity X P id
  simp only [id] at hid
  rw [hid]
  simp only [one_mul] at h
  have hB : 0 ≤ (P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M := by positivity
  calc _ ≤ _ := h
    _ = (10 * T ^ (ε / 2)) * ((P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * M) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hC hB

end GuthMaynard.E111.PartC
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias second_moment := GuthMaynard.E111.PartC.second_moment

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartC
open GuthMaynard GuthMaynard.E111 Complex
/-! ### Fourth moment -/
/-- `F(y) = ∑_{n ∈ X} n^{iy}`. -/
noncomputable def F (X : Finset ℕ) (y : ℝ) : ℂ := ∑ n ∈ X, E (Real.log n * y)

/-- `F'(y) = ∑_{n ∈ X} (i log n) n^{iy}`. -/
noncomputable def F' (X : Finset ℕ) (y : ℝ) : ℂ := ∑ n ∈ X, ((Real.log n : ℂ) * I) * E (Real.log n * y)

noncomputable def H (X : Finset ℕ) (y : ℝ) : ℝ := ‖F X y‖ ^ 2 + ‖F' X y‖ ^ 2

lemma continuous_E_mul (a : ℝ) : Continuous fun y : ℝ => E (a * y) := by
  unfold E; fun_prop

lemma hasDerivAt_E_mul (a y : ℝ) :
    HasDerivAt (fun y : ℝ => E (a * y)) (((a : ℂ) * I) * E (a * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (a : ℂ) * (y : ℂ) * I) ((a : ℂ) * 1 * I) y :=
    ((hasDerivAt_id y).ofReal_comp.const_mul (a : ℂ)).mul_const I
  have h2 := h1.cexp
  unfold E
  convert h2 using 1
  · funext y; push_cast; ring_nf
  · push_cast; ring

lemma hasDerivAt_F (X : Finset ℕ) (y : ℝ) : HasDerivAt (F X) (F' X y) y := by
  unfold F F'
  exact HasDerivAt.fun_sum (u := X) (fun n _ => hasDerivAt_E_mul (Real.log n) y)

lemma continuous_F (X : Finset ℕ) : Continuous (F X) := by
  unfold F; exact continuous_finsetSum _ fun n _ => continuous_E_mul _

lemma continuous_F' (X : Finset ℕ) : Continuous (F' X) := by
  unfold F'; exact continuous_finsetSum _ fun n _ => continuous_const.mul (continuous_E_mul _)

lemma continuous_H (X : Finset ℕ) : Continuous (H X) := by
  unfold H
  exact ((continuous_F X).norm.pow 2).add ((continuous_F' X).norm.pow 2)

lemma H_nonneg (X : Finset ℕ) (y : ℝ) : 0 ≤ H X y := by unfold H; positivity

/-- Gallagher step. -/
lemma gallagher (X : Finset ℕ) (y u : ℝ) (h : |y - u| ≤ 1) :
    ‖F X y‖ ^ 2 ≤ 2 * ∫ r in (-1 : ℝ)..1, H X (u + r) := by
  have hx : y ∈ Set.Icc (u - 1) (u - 1 + 2) := by
    rw [abs_le] at h; constructor <;> linarith
  have key := sq_norm_le_avg (F X) (F' X) (hasDerivAt_F X) (continuous_F' X) (u - 1) 2 two_pos
    1 one_pos y hx
  have hshift : ∫ r in (-1 : ℝ)..1, H X (u + r) = ∫ z in (u - 1)..(u - 1 + 2), H X z := by
    rw [intervalIntegral.integral_comp_add_left (H X) u]; congr 1; ring
  have hint : ∀ f : ℝ → ℝ, Continuous f →
      IntervalIntegrable f MeasureTheory.volume (u - 1) (u - 1 + 2) :=
    fun f hf => hf.intervalIntegrable _ _
  have h1 : ∫ z in (u - 1)..(u - 1 + 2), ‖F X z‖ ^ 2 ≤ ∫ z in (u - 1)..(u - 1 + 2), H X z :=
    intervalIntegral.integral_mono_on (by linarith) (hint _ ((continuous_F X).norm.pow 2))
      (hint _ (continuous_H X)) (fun z _ => by unfold H; nlinarith [sq_nonneg ‖F' X z‖])
  have h2 : ∫ z in (u - 1)..(u - 1 + 2), (1 * ‖F X z‖ ^ 2 + ‖F' X z‖ ^ 2 / 1) =
      ∫ z in (u - 1)..(u - 1 + 2), H X z := by
    congr 1; funext z; unfold H; ring
  have h0 : 0 ≤ ∫ z in (u - 1)..(u - 1 + 2), H X z :=
    intervalIntegral.integral_nonneg (by linarith) (fun z _ => H_nonneg X z)
  rw [hshift]; rw [h2] at key
  have hsplit : ∫ z in (u - 1)..(u - 1 + 2), (‖F X z‖ ^ 2 + ∫ z in (u - 1)..(u - 1 + 2), H X z) =
      (∫ z in (u - 1)..(u - 1 + 2), ‖F X z‖ ^ 2) + 2 * ∫ z in (u - 1)..(u - 1 + 2), H X z := by
    rw [intervalIntegral.integral_add (f := fun z => ‖F X z‖ ^ 2)
      (g := fun _ => ∫ z in (u - 1)..(u - 1 + 2), H X z)
      (hint _ ((continuous_F X).norm.pow 2)) intervalIntegrable_const,
      intervalIntegral.integral_const, smul_eq_mul]
    ring
  rw [hsplit] at key
  calc ‖F X y‖ ^ 2 ≤ 1 / 2 * ((∫ z in (u - 1)..(u - 1 + 2), ‖F X z‖ ^ 2) +
        2 * ∫ z in (u - 1)..(u - 1 + 2), H X z) := key
    _ ≤ 1 / 2 * ((∫ z in (u - 1)..(u - 1 + 2), H X z) +
        2 * ∫ z in (u - 1)..(u - 1 + 2), H X z) := by
        gcongr
    _ ≤ _ := by linarith

/-- Regrouping a double sum over pairs by the integer parts. -/
lemma regroup {α : Type*} [DecidableEq α] (C : Finset α) (fl : α → ℤ) (K : ℕ)
    (hK : ∀ u, (C.filter (fun p => fl p = u)).card ≤ K) (g : ℤ → ℤ → ℝ) (hg : ∀ a b, 0 ≤ g a b) :
    ∑ p ∈ C, ∑ q ∈ C, g (fl p) (fl q) ≤
      (K : ℝ) ^ 2 * ∑ u₁ ∈ C.image fl, ∑ u₂ ∈ C.image fl, g u₁ u₂ := by
  have inner : ∀ a : ℤ, ∑ q ∈ C, g a (fl q) ≤ K * ∑ u₂ ∈ C.image fl, g a u₂ := by
    intro a
    rw [Finset.sum_comp (fun b => g a b) fl, Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK b) (hg a b)
  have outer : ∑ p ∈ C, (K : ℝ) * ∑ u₂ ∈ C.image fl, g (fl p) u₂ ≤
      ∑ u₁ ∈ C.image fl, (K : ℝ) * ((K : ℝ) * ∑ u₂ ∈ C.image fl, g u₁ u₂) := by
    rw [Finset.sum_comp (fun a => (K : ℝ) * ∑ u₂ ∈ C.image fl, g a u₂) fl]
    refine Finset.sum_le_sum fun b _ => ?_
    rw [nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hK b)
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ => hg _ _))
  calc _ ≤ ∑ p ∈ C, (K : ℝ) * ∑ u₂ ∈ C.image fl, g (fl p) u₂ :=
        Finset.sum_le_sum fun p _ => inner (fl p)
    _ ≤ _ := outer
    _ = _ := by rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun _ _ => by ring

/-! ### Dyadic classes of pairs by the integer part of `t₁ + t₂` -/
noncomputable def fl (p : ℝ × ℝ) : ℤ := ⌊p.1 + p.2⌋

noncomputable def cnt (W : Finset ℝ) (u : ℤ) : ℕ := ((W ×ˢ W).filter (fun p => fl p = u)).card

noncomputable def cls (W : Finset ℝ) (p : ℝ × ℝ) : ℕ := Nat.log 2 (cnt W (fl p))

noncomputable def Cl (W : Finset ℝ) (j : ℕ) : Finset (ℝ × ℝ) :=
  (W ×ˢ W).filter (fun p => cls W p = j)

noncomputable def Ul (W : Finset ℝ) (j : ℕ) : Finset ℤ := (Cl W j).image fl

noncomputable def JJ (W : Finset ℝ) : ℕ := Nat.log 2 (W.card ^ 2)

lemma cnt_pos (W : Finset ℝ) (p : ℝ × ℝ) (hp : p ∈ W ×ˢ W) : 0 < cnt W (fl p) :=
  Finset.card_pos.mpr ⟨p, Finset.mem_filter.mpr ⟨hp, rfl⟩⟩

lemma cnt_le (W : Finset ℝ) (u : ℤ) : cnt W u ≤ W.card ^ 2 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_product, sq])

lemma fiber_eq (W : Finset ℝ) (j : ℕ) (p₀ : ℝ × ℝ) (hp : p₀ ∈ Cl W j) :
    (Cl W j).filter (fun q => fl q = fl p₀) = (W ×ˢ W).filter (fun q => fl q = fl p₀) := by
  ext q
  simp only [Cl, Finset.mem_filter]
  constructor
  · rintro ⟨⟨h1, _⟩, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩
    refine ⟨⟨h1, ?_⟩, h3⟩
    have := (Finset.mem_filter.mp hp).2
    simp only [cls] at this ⊢
    rw [h3]; exact this

lemma fiber_card_le (W : Finset ℝ) (j : ℕ) (u : ℤ) :
    ((Cl W j).filter (fun q => fl q = u)).card ≤ 2 ^ (j + 1) := by
  by_cases h : ((Cl W j).filter (fun q => fl q = u)).Nonempty
  · obtain ⟨p₀, hp⟩ := h
    rw [Finset.mem_filter] at hp
    rw [← hp.2, fiber_eq W j p₀ hp.1]
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (cnt W (fl p₀))
    have hc : Nat.log 2 (cnt W (fl p₀)) = j := (Finset.mem_filter.mp hp.1).2
    rw [hc] at this
    exact this.le
  · rw [Finset.not_nonempty_iff_eq_empty.mp h]; simp

lemma two_pow_le_cnt (W : Finset ℝ) (j : ℕ) (p₀ : ℝ × ℝ) (hp : p₀ ∈ Cl W j) :
    2 ^ j ≤ cnt W (fl p₀) := by
  have hc : Nat.log 2 (cnt W (fl p₀)) = j := (Finset.mem_filter.mp hp).2
  rw [← hc]
  exact Nat.pow_log_le_self 2 (cnt_pos W p₀ (Finset.mem_filter.mp hp).1).ne'

lemma card_U_le (W : Finset ℝ) (j : ℕ) : 2 ^ j * (Ul W j).card ≤ (Cl W j).card := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fl) (t := Ul W j)
    (fun p hp => Finset.mem_image_of_mem fl hp)]
  rw [mul_comm, ← smul_eq_mul]
  apply Finset.card_nsmul_le_sum
  intro u hu
  obtain ⟨p₀, hp₀, rfl⟩ := Finset.mem_image.mp hu
  rw [fiber_eq W j p₀ hp₀]
  exact two_pow_le_cnt W j p₀ hp₀

lemma card_C_le (W : Finset ℝ) (j : ℕ) : (Cl W j).card ≤ W.card ^ 2 :=
  (Finset.card_filter_le _ _).trans (by rw [Finset.card_product, sq])

lemma four_pow_le (W : Finset ℝ) (j : ℕ) : 4 ^ j * (Ul W j).card ≤ energy W := by
  set C := Cl W j
  have step1 : 2 ^ j * C.card ≤ ((C ×ˢ C).filter (fun x => fl x.2 = fl x.1)).card := by
    rw [Finset.card_filter, Finset.sum_product]
    rw [mul_comm, ← smul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro p hp
    rw [← Finset.card_filter, fiber_eq W j p hp]
    exact two_pow_le_cnt W j p hp
  have step2 : ((C ×ˢ C).filter (fun x => fl x.2 = fl x.1)).card ≤ energy W := by
    unfold energy
    apply Finset.card_le_card_of_injOn (fun x => (x.1.1, x.1.2, x.2.1, x.2.2))
    · intro x hx
      simp only [Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hx ⊢
      obtain ⟨⟨h1, h2⟩, h3⟩ := hx
      have m1 := (Finset.mem_filter.mp h1).1
      have m2 := (Finset.mem_filter.mp h2).1
      rw [Finset.mem_product] at m1 m2
      refine ⟨⟨m1.1, m1.2, m2.1, m2.2⟩, ?_⟩
      have := Int.abs_sub_lt_one_of_floor_eq_floor h3
      rw [abs_sub_comm] at this
      have e : x.1.1 + x.1.2 - x.2.1 - x.2.2 = x.1.1 + x.1.2 - (x.2.1 + x.2.2) := by ring
      rw [e]; exact this.le
    · intro x _ y _ h
      simp only [Prod.mk.injEq] at h
      ext <;> simp [h.1, h.2.1, h.2.2.1, h.2.2.2]
  have h4 : 4 ^ j = 2 ^ j * 2 ^ j := by rw [← mul_pow]; norm_num
  calc 4 ^ j * (Ul W j).card = 2 ^ j * (2 ^ j * (Ul W j).card) := by rw [h4, mul_assoc]
    _ ≤ 2 ^ j * C.card := Nat.mul_le_mul_left _ (card_U_le W j)
    _ ≤ _ := step1.trans step2

lemma Rl_sq (W : Finset ℝ) (τ : ℝ) : Rl W τ ^ 2 = ∑ p ∈ W ×ˢ W, E ((p.1 + p.2) * τ) := by
  rw [Rl_eq, sq, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← E_add]; congr 1; ring

lemma Rl_sq_split (W : Finset ℝ) (τ : ℝ) :
    Rl W τ ^ 2 = ∑ j ∈ Finset.range (JJ W + 1), ∑ p ∈ Cl W j, E ((p.1 + p.2) * τ) := by
  rw [Rl_sq]
  unfold Cl
  rw [Finset.sum_fiberwise_of_maps_to]
  intro p _
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (Nat.log_mono_right (cnt_le W _))

lemma norm4_le (W : Finset ℝ) (τ : ℝ) :
    ‖Rl W τ‖ ^ 4 ≤ ((JJ W + 1 : ℕ) : ℝ) *
      ∑ j ∈ Finset.range (JJ W + 1), ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * τ)‖ ^ 2 := by
  have : ‖Rl W τ‖ ^ 4 = ‖Rl W τ ^ 2‖ ^ 2 := by rw [norm_pow]; ring
  rw [this, Rl_sq_split]
  calc _ ≤ (∑ j ∈ Finset.range (JJ W + 1), ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * τ)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ _ := by
        have := sq_sum_le_card_mul_sum_sq (s := Finset.range (JJ W + 1))
          (f := fun j => ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * τ)‖)
        simpa using this

lemma card_le_of_sep (W : Finset ℝ) (a T : ℝ) (hT : 0 ≤ T) (hW : IsSeparated 1 W)
    (h : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) : (W.card : ℝ) ≤ T + 1 := by
  have hc : W.card ≤ (Finset.range (⌊T⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun t => ⌊t - a⌋₊)
    · intro t ht
      have := h t ht
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [this.2]))
    · intro t ht t' ht' he
      by_contra hne
      have h1 := hW t ht t' ht' hne
      have a1 := (h t ht).1
      have a2 := (h t' ht').1
      simp only at he
      have b1 := Nat.floor_le (by linarith : 0 ≤ t - a)
      have b2 := Nat.lt_floor_add_one (t - a)
      have b3 := Nat.floor_le (by linarith : 0 ≤ t' - a)
      have b4 := Nat.lt_floor_add_one (t' - a)
      rw [he] at b1 b2
      have : |t - t'| < 1 := by rw [abs_sub_lt_iff]; constructor <;> linarith
      linarith
  rw [Finset.card_range] at hc
  have := Nat.floor_le hT
  have : (W.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

/-! ### Heath-Brown on integer point sets, and integration -/
/-- The Heath-Brown bound at a fixed scale `T'`, for `X`. -/
def HBat (X : Finset ℕ) (M : ℕ) (T' δ ε' : ℝ) : Prop :=
  ∀ b : ℕ → ℂ, (∀ n ∈ X, ‖b n‖ ≤ T' ^ δ) → ∀ (P : Finset ℝ) (c : ℝ), IsSeparated 1 P →
    (∀ t ∈ P, t ∈ Set.Icc c (c + T')) →
    ∑ t₁ ∈ P, ∑ t₂ ∈ P, ‖∑ n ∈ X, b n * E (Real.log n * (t₁ - t₂))‖ ^ 2 ≤
      10 * (T' ^ ε' * ((P.card : ℝ) ^ 2 * M + (P.card : ℝ) * (M : ℝ) ^ 2 +
        (P.card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M))

lemma sum_image_cast (V : Finset ℤ) (f : ℝ → ℝ) :
    ∑ t ∈ V.image (fun u : ℤ => (u : ℝ)), f t = ∑ u ∈ V, f u :=
  Finset.sum_image (fun _ _ _ _ h => Int.cast_injective h)

lemma hb_int (X : Finset ℕ) (M : ℕ) (T' δ ε' : ℝ) (hHB : HBat X M T' δ ε')
    (hX1 : ∀ n ∈ X, 1 ≤ n) (hlog : ∀ n ∈ X, Real.log n ≤ T' ^ δ) (h1 : 1 ≤ T' ^ δ)
    (V : Finset ℤ) (c : ℝ) (hV : ∀ u ∈ V, (u : ℝ) ∈ Set.Icc c (c + T')) (r : ℝ) :
    ∑ u₁ ∈ V, ∑ u₂ ∈ V, H X ((u₁ : ℝ) - u₂ + r) ≤
      20 * (T' ^ ε' * ((V.card : ℝ) ^ 2 * M + (V.card : ℝ) * (M : ℝ) ^ 2 +
        (V.card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)) := by
  set P := V.image (fun u : ℤ => (u : ℝ))
  have hPc : P.card = V.card := Finset.card_image_of_injective _ Int.cast_injective
  have hsep : IsSeparated 1 P := by
    intro t ht t' ht' hne
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨u', -, rfl⟩ := Finset.mem_image.mp ht'
    have hu : u ≠ u' := fun h => hne (by rw [h])
    have := Int.one_le_abs (sub_ne_zero.mpr hu)
    rw [← Int.cast_sub, ← Int.cast_abs]; exact_mod_cast this
  have hPin : ∀ t ∈ P, t ∈ Set.Icc c (c + T') := by
    intro t ht
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp ht
    exact hV u hu
  have A := hHB (fun n => E (Real.log n * r)) (fun n _ => by rw [norm_E]; exact h1) P c hsep hPin
  have B := hHB (fun n => ((Real.log n : ℂ) * I) * E (Real.log n * r)) (fun n hn => by
      rw [norm_mul, norm_mul, norm_E, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by exact_mod_cast hX1 n hn))]
      simpa using hlog n hn) P c hsep hPin
  simp only [P, sum_image_cast, hPc] at A B
  have eF : ∀ u₁ u₂ : ℤ, F X ((u₁ : ℝ) - u₂ + r) =
      ∑ n ∈ X, E (Real.log n * r) * E (Real.log n * ((u₁ : ℝ) - u₂)) := by
    intro u₁ u₂; unfold F
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← E_add]; congr 1; ring
  have eF' : ∀ u₁ u₂ : ℤ, F' X ((u₁ : ℝ) - u₂ + r) =
      ∑ n ∈ X, ((Real.log n : ℂ) * I) * E (Real.log n * r) * E (Real.log n * ((u₁ : ℝ) - u₂)) := by
    intro u₁ u₂; unfold F'
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_assoc _ (E _) (E _), ← E_add]; congr 2; ring
  simp only [H, eF, eF', Finset.sum_add_distrib]
  linarith

lemma int_bound (X : Finset ℕ) (M : ℕ) (T' δ ε' : ℝ) (hHB : HBat X M T' δ ε')
    (hX1 : ∀ n ∈ X, 1 ≤ n) (hlog : ∀ n ∈ X, Real.log n ≤ T' ^ δ) (h1 : 1 ≤ T' ^ δ)
    (V : Finset ℤ) (c : ℝ) (hV : ∀ u ∈ V, (u : ℝ) ∈ Set.Icc c (c + T')) :
    ∑ u₁ ∈ V, ∑ u₂ ∈ V, 2 * ∫ r in (-1 : ℝ)..1, H X ((u₁ : ℝ) - u₂ + r) ≤
      80 * (T' ^ ε' * ((V.card : ℝ) ^ 2 * M + (V.card : ℝ) * (M : ℝ) ^ 2 +
        (V.card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)) := by
  have hc : ∀ u₁ u₂ : ℤ, Continuous fun r : ℝ => H X ((u₁ : ℝ) - u₂ + r) :=
    fun u₁ u₂ => (continuous_H X).comp (continuous_const.add continuous_id)
  have hswap : ∫ r in (-1 : ℝ)..1, ∑ u₁ ∈ V, ∑ u₂ ∈ V, H X ((u₁ : ℝ) - u₂ + r) =
      ∑ u₁ ∈ V, ∑ u₂ ∈ V, ∫ r in (-1 : ℝ)..1, H X ((u₁ : ℝ) - u₂ + r) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun u₁ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      intro u₂ _; exact (hc u₁ u₂).intervalIntegrable _ _
    · intro u₁ _
      exact (continuous_finsetSum _ fun u₂ _ => hc u₁ u₂).intervalIntegrable _ _
  have hmono : ∫ r in (-1 : ℝ)..1, ∑ u₁ ∈ V, ∑ u₂ ∈ V, H X ((u₁ : ℝ) - u₂ + r) ≤
      ∫ r in (-1 : ℝ)..1, 20 * (T' ^ ε' * ((V.card : ℝ) ^ 2 * M + (V.card : ℝ) * (M : ℝ) ^ 2 +
        (V.card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
    · exact (continuous_finsetSum _ fun u₁ _ =>
        continuous_finsetSum _ fun u₂ _ => hc u₁ u₂).intervalIntegrable _ _
    · exact intervalIntegrable_const
    · intro r _; exact hb_int X M T' δ ε' hHB hX1 hlog h1 V c hV r
  rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
  simp only [← Finset.mul_sum]
  rw [← hswap]
  norm_num at hmono
  linarith

/-- Bound for one dyadic class. -/
lemma class_bound (X : Finset ℕ) (M : ℕ) (T' δ ε' : ℝ) (hHB : HBat X M T' δ ε')
    (hX1 : ∀ n ∈ X, 1 ≤ n) (hlog : ∀ n ∈ X, Real.log n ≤ T' ^ δ) (h1 : 1 ≤ T' ^ δ)
    (W : Finset ℝ) (j : ℕ) (c : ℝ) (hV : ∀ u ∈ Ul W j, (u : ℝ) ∈ Set.Icc c (c + T')) :
    ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * (Real.log n₁ - Real.log n₂))‖ ^ 2 ≤
      ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 * (80 * (T' ^ ε' * (((Ul W j).card : ℝ) ^ 2 * M +
        ((Ul W j).card : ℝ) * (M : ℝ) ^ 2 +
        ((Ul W j).card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M))) := by
  rw [moment_identity X (Cl W j) (fun p => p.1 + p.2)]
  set g : ℤ → ℤ → ℝ := fun u₁ u₂ => 2 * ∫ r in (-1 : ℝ)..1, H X ((u₁ : ℝ) - u₂ + r)
  have hg : ∀ a b, 0 ≤ g a b := fun a b =>
    mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg (by norm_num)
      (fun r _ => H_nonneg X _))
  calc _ ≤ ∑ p ∈ Cl W j, ∑ q ∈ Cl W j, g (fl p) (fl q) := by
        refine Finset.sum_le_sum fun p _ => Finset.sum_le_sum fun q _ => ?_
        have := gallagher X ((p.1 + p.2) - (q.1 + q.2)) ((fl p : ℝ) - fl q) (by
          have a1 := Int.floor_le (p.1 + p.2)
          have a2 := Int.lt_floor_add_one (p.1 + p.2)
          have a3 := Int.floor_le (q.1 + q.2)
          have a4 := Int.lt_floor_add_one (q.1 + q.2)
          simp only [fl]
          rw [abs_le]; constructor <;> linarith)
        exact this
    _ ≤ ((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 * ∑ u₁ ∈ Ul W j, ∑ u₂ ∈ Ul W j, g u₁ u₂ :=
        regroup (Cl W j) fl (2 ^ (j + 1)) (fiber_card_le W j) g hg
    _ ≤ _ := by
        gcongr
        exact int_bound X M T' δ ε' hHB hX1 hlog h1 (Ul W j) c hV

/-! ### Assembly -/
lemma alg (x Uc w e M s t : ℝ) (hx : 0 < x) (hU : 0 ≤ Uc) (hw : 0 ≤ w) (he : 0 ≤ e)
    (hM : 0 ≤ M) (hs : 0 ≤ s) (hst : s ≤ 2 * t) (h1 : x * Uc ≤ w ^ 2) (h2 : x ^ 2 * Uc ≤ e) :
    x ^ 2 * (Uc ^ 2 * M + Uc * M ^ 2 + Uc ^ (5 / 4 : ℝ) * s * M) ≤
      2 * (w ^ 4 * M + M ^ 2 * e + e ^ (3 / 4 : ℝ) * w * t * M) := by
  have ha : x ^ 2 * Uc ^ 2 ≤ w ^ 4 := by
    have := pow_le_pow_left₀ (mul_nonneg hx.le hU) h1 2
    nlinarith
  have hb : x ^ 2 * Uc * M ^ 2 ≤ e * M ^ 2 := mul_le_mul_of_nonneg_right h2 (sq_nonneg M)
  have hc : x ^ 2 * Uc ^ (5 / 4 : ℝ) ≤ e ^ (3 / 4 : ℝ) * w := by
    have eq : x ^ 2 * Uc ^ (5 / 4 : ℝ) = (x ^ 2 * Uc) ^ (3 / 4 : ℝ) * (x * Uc) ^ (1 / 2 : ℝ) := by
      rw [Real.mul_rpow (sq_nonneg x) hU, Real.mul_rpow hx.le hU]
      have e1 : (x ^ 2) ^ (3 / 4 : ℝ) = x ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]; norm_num
      have e2 : x ^ (3 / 2 : ℝ) * x ^ (1 / 2 : ℝ) = x ^ 2 := by
        rw [← Real.rpow_add hx]; norm_num
      have e3 : Uc ^ (3 / 4 : ℝ) * Uc ^ (1 / 2 : ℝ) = Uc ^ (5 / 4 : ℝ) := by
        rw [← Real.rpow_add' hU (by norm_num)]; norm_num
      rw [e1, ← e2, ← e3]; ring
    have hw2 : (w ^ 2) ^ (1 / 2 : ℝ) = w := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hw]; norm_num
    rw [eq, ← hw2]
    apply mul_le_mul (Real.rpow_le_rpow (by positivity) h2 (by norm_num))
      (Real.rpow_le_rpow (by positivity) h1 (by norm_num)) (by positivity) (by positivity)
  have hc' : x ^ 2 * Uc ^ (5 / 4 : ℝ) * s * M ≤ e ^ (3 / 4 : ℝ) * w * (2 * t) * M := by
    apply mul_le_mul_of_nonneg_right _ hM
    apply mul_le_mul hc hst hs (by positivity)
  have hM2 : 0 ≤ M ^ 2 := sq_nonneg M
  nlinarith [mul_le_mul_of_nonneg_right ha hM, mul_nonneg (pow_nonneg hw 4) hM, mul_nonneg he hM2]

lemma J_le (W : Finset ℝ) (T : ℝ) (hT : 3 ≤ T) (hW : (W.card : ℝ) ≤ T + 1) :
    ((JJ W + 1 : ℕ) : ℝ) ≤ 6 * Real.log T + 1 := by
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  push_cast
  by_cases h0 : W.card = 0
  · simp [JJ, h0]; exact hlogT
  · have hp := Nat.pow_log_le_self 2 (pow_ne_zero 2 h0)
    have hp' : (2 : ℝ) ^ (JJ W) ≤ T ^ 3 := by
      have : ((2 ^ JJ W : ℕ) : ℝ) ≤ ((W.card ^ 2 : ℕ) : ℝ) := by exact_mod_cast hp
      push_cast at this
      have hc0 : (0 : ℝ) ≤ W.card := by positivity
      have : (W.card : ℝ) ^ 2 ≤ (T + 1) ^ 2 := pow_le_pow_left₀ hc0 hW 2
      nlinarith
    have hl := Real.log_le_log (by positivity) hp'
    rw [Real.log_pow, Real.log_pow] at hl
    have := Real.log_two_gt_d9
    push_cast at hl
    have hJ0 : (0 : ℝ) ≤ JJ W := by positivity
    nlinarith

theorem fourth_moment : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (M : ℕ), 1 ≤ M →
    (M : ℝ) ≤ T → ∀ X : Finset ℕ, X ⊆ Finset.Icc M (4 * M) →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖Rl W (Real.log n₁ - Real.log n₂)‖ ^ 4 ≤
      T ^ ε * ((W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * (energy W : ℝ) +
        (energy W : ℝ) ^ (3 / 4 : ℝ) * (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M) := by
  intro ε hε
  obtain ⟨δ, hδ, T₁, hT₁⟩ := hbX (ε / 4) (by linarith)
  set s := ε / 8 with hs_def
  have hs : 0 < s := by positivity
  set K : ℝ := 640 * (6 / s + 1) ^ 2
  have ev1 := eventually_const_mul_le K (ε / 2) (by linarith)
  have ev2 := eventually_const_mul_le ((2 / δ) * 4 ^ (δ / 2)) δ hδ
  obtain ⟨T₂, hT₂⟩ := Filter.eventually_atTop.mp
    (ev1.and (ev2.and (Filter.eventually_ge_atTop (max T₁ 3))))
  refine ⟨T₂, fun T hT M hM hMT X hX W a hW hWa => ?_⟩
  obtain ⟨hK, hL, hT3'⟩ := hT₂ T hT
  have hT1 : T₁ ≤ T := (le_max_left _ _).trans hT3'
  have hT3 : 3 ≤ T := (le_max_right _ _).trans hT3'
  set T' := 2 * T + 1 with hT'_def
  have hHB : HBat X M T' δ (ε / 4) := fun b hb P c hP hc =>
    hT₁ T' (by linarith) M hM X hX b hb P c hP hc
  have hX1 : ∀ n ∈ X, 1 ≤ n := fun n hn => hM.trans (Finset.mem_Icc.mp (hX hn)).1
  have hTd : T ^ δ ≤ T' ^ δ := Real.rpow_le_rpow (by linarith) (by linarith) hδ.le
  have hlog4 : Real.log (4 * T) ≤ T ^ δ := by
    have := Real.log_le_rpow_div (by linarith : (0:ℝ) ≤ 4 * T) (by linarith : 0 < δ / 2)
    rw [Real.mul_rpow (by norm_num) (by linarith)] at this
    calc _ ≤ _ := this
      _ = (2 / δ * 4 ^ (δ / 2)) * T ^ (δ / 2) := by field_simp
      _ ≤ _ := hL
  have hlog : ∀ n ∈ X, Real.log n ≤ T' ^ δ := fun n hn => by
    have hn4 : (n : ℝ) ≤ 4 * T := by
      have h4 := (Finset.mem_Icc.mp (hX hn)).2
      have : (n : ℝ) ≤ 4 * M := by exact_mod_cast h4
      linarith
    have hn1 : (0 : ℝ) < n := by exact_mod_cast hX1 n hn
    have := Real.log_le_log hn1 hn4
    linarith
  have h1 : 1 ≤ T' ^ δ := Real.one_le_rpow (by linarith) hδ.le
  have hV : ∀ j, ∀ u ∈ Ul W j, (u : ℝ) ∈ Set.Icc (2 * a - 1) (2 * a - 1 + T') := by
    intro j u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := (Finset.mem_filter.mp hp).1
    rw [Finset.mem_product] at hp'
    have b1 := hWa _ hp'.1
    have b2 := hWa _ hp'.2
    have c1 := Int.floor_le (p.1 + p.2)
    have c2 := Int.lt_floor_add_one (p.1 + p.2)
    simp only [fl, T']
    constructor <;> linarith [b1.1, b1.2, b2.1, b2.2]
  set Target := (W.card : ℝ) ^ 4 * M + (M : ℝ) ^ 2 * (energy W : ℝ) +
    (energy W : ℝ) ^ (3 / 4 : ℝ) * (W.card : ℝ) * T ^ (1 / 2 : ℝ) * M with hTarget
  have hTg : 0 ≤ Target := by positivity
  have hsq : T' ^ (1 / 2 : ℝ) ≤ 2 * T ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
    have : Real.sqrt T' ≤ Real.sqrt (4 * T) := Real.sqrt_le_sqrt (by linarith)
    rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)] at this
    exact this
  have hTe : T' ^ (ε / 4) ≤ T ^ (ε / 2) := by
    have : T' ≤ T ^ (2 : ℝ) := by rw [Real.rpow_two]; nlinarith
    calc T' ^ (ε / 4) ≤ (T ^ (2 : ℝ)) ^ (ε / 4) :=
          Real.rpow_le_rpow (by linarith) this (by linarith)
      _ = T ^ (ε / 2) := by rw [← Real.rpow_mul (by linarith)]; ring_nf
  have hclass : ∀ j, ∑ n₁ ∈ X, ∑ n₂ ∈ X,
      ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * (Real.log n₁ - Real.log n₂))‖ ^ 2 ≤
      640 * T ^ (ε / 2) * Target := by
    intro j
    refine (class_bound X M T' δ (ε / 4) hHB hX1 hlog h1 W j (2 * a - 1) (hV j)).trans ?_
    have hU1 : (2 : ℝ) ^ j * (Ul W j).card ≤ (W.card : ℝ) ^ 2 := by
      have := (card_U_le W j).trans (card_C_le W j)
      exact_mod_cast this
    have hU2 : ((2 : ℝ) ^ j) ^ 2 * (Ul W j).card ≤ (energy W : ℝ) := by
      have := four_pow_le W j
      rw [← pow_mul, mul_comm j 2, pow_mul]; norm_num
      exact_mod_cast this
    have hA := alg ((2 : ℝ) ^ j) (Ul W j).card W.card (energy W) M (T' ^ (1 / 2 : ℝ))
      (T ^ (1 / 2 : ℝ)) (by positivity) (by positivity) (by positivity) (by positivity)
      (by positivity) (by positivity) hsq hU1 hU2
    have hTe0 : 0 ≤ T' ^ (ε / 4) := Real.rpow_nonneg (by linarith) _
    have e1 : (((2 ^ (j + 1) : ℕ) : ℝ) ^ 2 * (80 * (T' ^ (ε / 4) *
        (((Ul W j).card : ℝ) ^ 2 * M + ((Ul W j).card : ℝ) * (M : ℝ) ^ 2 +
        ((Ul W j).card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)))) =
        320 * T' ^ (ε / 4) * (((2 : ℝ) ^ j) ^ 2 * (((Ul W j).card : ℝ) ^ 2 * M +
        ((Ul W j).card : ℝ) * (M : ℝ) ^ 2 +
        ((Ul W j).card : ℝ) ^ (5 / 4 : ℝ) * T' ^ (1 / 2 : ℝ) * M)) := by
      push_cast; ring
    rw [e1]
    calc _ ≤ 320 * T' ^ (ε / 4) * (2 * Target) := by gcongr
      _ ≤ 320 * T ^ (ε / 2) * (2 * Target) := by gcongr
      _ = _ := by ring
  set J1 : ℝ := ((JJ W + 1 : ℕ) : ℝ)
  have hJ1 : 0 ≤ J1 := by positivity
  have hJ : J1 ^ 2 * 640 ≤ K * T ^ (ε / 2 / 2) := by
    have hW1 := card_le_of_sep W a T (by linarith) hW hWa
    have h6 := J_le W T hT3 hW1
    have hl := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ T) hs
    have hTs : 1 ≤ T ^ s := Real.one_le_rpow (by linarith) hs.le
    have hb : J1 ≤ (6 / s + 1) * T ^ s := by
      have : 6 * (T ^ s / s) = 6 / s * T ^ s := by ring
      nlinarith
    have hb2 : J1 ^ 2 ≤ (6 / s + 1) ^ 2 * T ^ (ε / 2 / 2) := by
      have : T ^ (ε / 2 / 2) = (T ^ s) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; congr 1; simp [hs_def]; ring
      rw [this, ← mul_pow]
      exact pow_le_pow_left₀ hJ1 hb 2
    simp only [K]; nlinarith
  calc ∑ n₁ ∈ X, ∑ n₂ ∈ X, ‖Rl W (Real.log n₁ - Real.log n₂)‖ ^ 4
      ≤ ∑ n₁ ∈ X, ∑ n₂ ∈ X, J1 * ∑ j ∈ Finset.range (JJ W + 1),
          ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * (Real.log n₁ - Real.log n₂))‖ ^ 2 :=
        Finset.sum_le_sum fun _ _ => Finset.sum_le_sum fun _ _ => norm4_le W _
    _ = J1 * ∑ j ∈ Finset.range (JJ W + 1), ∑ n₁ ∈ X, ∑ n₂ ∈ X,
          ‖∑ p ∈ Cl W j, E ((p.1 + p.2) * (Real.log n₁ - Real.log n₂))‖ ^ 2 := by
        simp only [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_congr rfl fun n₁ _ => Finset.sum_comm]
        exact Finset.sum_comm
    _ ≤ J1 * ∑ j ∈ Finset.range (JJ W + 1), 640 * T ^ (ε / 2) * Target := by
        gcongr with j _
        exact hclass j
    _ = J1 ^ 2 * 640 * T ^ (ε / 2) * Target := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; simp only [J1]; ring
    _ ≤ K * T ^ (ε / 2 / 2) * T ^ (ε / 2) * Target :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hJ
          (Real.rpow_nonneg (by linarith) _)) hTg
    _ ≤ T ^ (ε / 2) * T ^ (ε / 2) * Target :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK
          (Real.rpow_nonneg (by linarith) _)) hTg
    _ = T ^ ε * Target := by
        rw [← Real.rpow_add (by linarith)]; ring_nf

end GuthMaynard.E111.PartC
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias fourth_moment := GuthMaynard.E111.PartC.fourth_moment

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartD
open GuthMaynard GuthMaynard.E111 Complex
/-! ### Exponentials -/
/-- `E x = e^{ix}`. -/
noncomputable def E (x : ℝ) : ℂ := Complex.exp ((x : ℂ) * I)

lemma E_add (x y : ℝ) : E (x + y) = E x * E y := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma conj_E (x : ℝ) : (starRingEnd ℂ) (E x) = E (-x) := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; push_cast; ring

lemma norm_E (x : ℝ) : ‖E x‖ = 1 := Complex.norm_exp_ofReal_mul_I x

lemma Rl_eq (W : Finset ℝ) (τ : ℝ) : Rl W τ = ∑ t ∈ W, E (t * τ) := rfl

lemma sq_eq_mul_conj (z : ℂ) : (((‖z‖ ^ 2 : ℝ)) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj']; push_cast; ring

lemma continuous_E_mul (a : ℝ) : Continuous fun y : ℝ => E (a * y) := by
  unfold E; fun_prop

lemma hasDerivAt_E_mul (a y : ℝ) :
    HasDerivAt (fun y : ℝ => E (a * y)) (((a : ℂ) * I) * E (a * y)) y := by
  have h1 : HasDerivAt (fun y : ℝ => (a : ℂ) * (y : ℂ) * I) ((a : ℂ) * 1 * I) y :=
    ((hasDerivAt_id y).ofReal_comp.const_mul (a : ℂ)).mul_const I
  have h2 := h1.cexp
  unfold E
  convert h2 using 1
  · funext y; push_cast; ring_nf
  · push_cast; ring

/-! ### Generic exponential sums -/
noncomputable def G {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (y : ℝ) : ℂ :=
  ∑ i ∈ S, E (φ i * y)

noncomputable def G' {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (y : ℝ) : ℂ :=
  ∑ i ∈ S, ((φ i : ℂ) * I) * E (φ i * y)

lemma hasDerivAt_G {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (y : ℝ) :
    HasDerivAt (G S φ) (G' S φ y) y := by
  unfold G G'
  exact HasDerivAt.fun_sum (u := S) (fun i _ => hasDerivAt_E_mul (φ i) y)

lemma continuous_G' {ι : Type*} (S : Finset ι) (φ : ι → ℝ) : Continuous (G' S φ) := by
  unfold G'; exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_E_mul _)

lemma continuous_G {ι : Type*} (S : Finset ι) (φ : ι → ℝ) : Continuous (G S φ) := by
  unfold G; exact continuous_finsetSum _ fun i _ => continuous_E_mul _

lemma G_shift {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (c y : ℝ) :
    ‖G S (fun i => φ i - c) y‖ = ‖G S φ y‖ := by
  have : G S (fun i => φ i - c) y = E (-c * y) * G S φ y := by
    unfold G; rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← E_add]; congr 1; ring
  rw [this, norm_mul, norm_E, one_mul]

lemma G_WW (W : Finset ℝ) (y : ℝ) : G (W ×ˢ W) (fun p => p.1 + p.2) y = Rl W y ^ 2 := by
  rw [Rl_eq, sq, Finset.sum_mul_sum]; unfold G; rw [Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← E_add]; congr 1; ring

/-! ### Mean values over `[-1, 1]` -/
noncomputable def kern (x : ℝ) : ℝ := 6 / (|((⌊x⌋ : ℤ) : ℝ)| + 1)

lemma kern_nonneg (x : ℝ) : 0 ≤ kern x := by unfold kern; positivity

lemma norm_integral_E_le (x : ℝ) : ‖∫ y in (-1 : ℝ)..1, E (x * y)‖ ≤ kern x := by
  set n := ‖∫ y in (-1 : ℝ)..1, E (x * y)‖ with hn
  have hn0 : 0 ≤ n := norm_nonneg _
  have ha : n ≤ 2 := by
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (-1 : ℝ)) (b := 1)
      (C := 1) (f := fun y => E (x * y)) (fun y _ => by rw [norm_E])
    norm_num at this; linarith
  have hb : x ≠ 0 → n * |x| ≤ 2 := by
    intro hx
    have hxI : ((x : ℂ) * I) ≠ 0 := mul_ne_zero (by exact_mod_cast hx) I_ne_zero
    have hd : ∀ y, HasDerivAt (fun y : ℝ => E (x * y) / ((x : ℂ) * I)) (E (x * y)) y := by
      intro y
      have := (hasDerivAt_E_mul x y).div_const ((x : ℂ) * I)
      rwa [mul_div_cancel_left₀ _ hxI] at this
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (-1 : ℝ)) (b := 1)
      (fun y _ => hd y) ((continuous_E_mul x).intervalIntegrable _ _)
    rw [hn, hint, ← sub_div, norm_div, norm_mul, Complex.norm_I, Complex.norm_real,
      Real.norm_eq_abs, mul_one, mul_one]
    rw [div_mul_cancel₀ _ (abs_pos.mpr hx).ne']
    calc ‖E x - E (x * -1)‖ ≤ ‖E x‖ + ‖E (x * -1)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_E, norm_E]; norm_num
  unfold kern
  rw [le_div_iff₀ (by positivity)]
  set k := ⌊x⌋
  have k1 := Int.floor_le x
  have k2 := Int.lt_floor_add_one x
  by_cases h1 : 1 ≤ k
  · have hK : (1 : ℝ) ≤ k := by exact_mod_cast h1
    have hx : 0 < x := by linarith
    have := hb hx.ne'
    rw [abs_of_pos hx] at this
    rw [abs_of_pos (by linarith : (0 : ℝ) < k)]
    nlinarith
  · by_cases h2 : k ≤ -2
    · have hK : (k : ℝ) ≤ -2 := by exact_mod_cast h2
      have hx : x < 0 := by linarith
      have := hb hx.ne
      rw [abs_of_neg hx] at this
      rw [abs_of_neg (by linarith : (k : ℝ) < 0)]
      nlinarith
    · have hK : |(k : ℝ)| ≤ 1 := by
        rw [abs_le]; constructor
        · have : -1 ≤ k := by omega
          exact_mod_cast this
        · have : k ≤ 1 := by omega
          exact_mod_cast this
      nlinarith

lemma mv {ι : Type*} (S : Finset ι) (φ : ι → ℝ) (c : ι → ℂ) (B : ℝ) (hc : ∀ i ∈ S, ‖c i‖ ≤ B) :
    ∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 ≤
      B ^ 2 * ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) := by
  have hcont : ∀ i j, Continuous fun y : ℝ => c i * (starRingEnd ℂ) (c j) * E ((φ i - φ j) * y) :=
    fun i j => continuous_const.mul (continuous_E_mul _)
  have hexp : ∀ y : ℝ, (((‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 : ℝ)) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * E ((φ i - φ j) * y) := by
    intro y
    rw [sq_eq_mul_conj, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, conj_E, show (φ i - φ j) * y = φ i * y + -(φ j * y) by ring, E_add]; ring
  have hI : ((∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, c i * (starRingEnd ℂ) (c j) * ∫ y in (-1 : ℝ)..1, E ((φ i - φ j) * y) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [hexp]
    rw [intervalIntegral.integral_finsetSum
      (fun i _ => (continuous_finsetSum _ fun j _ => hcont i j).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum (fun j _ => (hcont i j).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact intervalIntegral.integral_const_mul _ _
  set r := ∫ y in (-1 : ℝ)..1, ‖∑ i ∈ S, c i * E (φ i * y)‖ ^ 2
  have h1 : r ≤ ‖(r : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]; exact le_abs_self r
  rw [hI] at h1
  refine h1.trans ((norm_sum_le _ _).trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i hi => (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j hj => ?_
  rw [norm_mul, norm_mul, Complex.norm_conj]
  have hci := hc i hi
  have hcj := hc j hj
  have hk := norm_integral_E_le (φ i - φ j)
  have hB : 0 ≤ B := (norm_nonneg _).trans hci
  calc ‖c i‖ * ‖c j‖ * ‖∫ y in (-1 : ℝ)..1, E ((φ i - φ j) * y)‖ ≤ B * B * kern (φ i - φ j) := by
        gcongr
    _ = B ^ 2 * kern (φ i - φ j) := by ring

lemma sum_Icc_inv (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 1 / (|(k : ℝ)| + 1) ≤
      2 * ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : Finset.Icc (-((n + 1 : ℕ) : ℤ)) ((n + 1 : ℕ) : ℤ) =
        insert (-((n + 1 : ℕ) : ℤ)) (insert ((n + 1 : ℕ) : ℤ) (Finset.Icc (-(n : ℤ)) n)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [e, Finset.sum_insert (by simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega),
      Finset.sum_insert (by simp only [Finset.mem_Icc]; push_cast; omega),
      Finset.sum_range_succ _ (n + 1)]
    have h1 : |(((-((n + 1 : ℕ) : ℤ)) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_neg, abs_of_nonneg (by positivity)]
    have h2 : |((((n + 1 : ℕ) : ℤ)) : ℝ)| = (n : ℝ) + 1 := by
      push_cast; rw [abs_of_nonneg (by positivity)]
    rw [h1, h2]
    push_cast
    linarith

lemma sum_kern_Icc (n : ℕ) :
    ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1) ≤ 12 * (1 + Real.log (n + 1)) := by
  have h := sum_Icc_inv n
  have hh : ∑ j ∈ Finset.range (n + 1), 1 / ((j : ℝ) + 1) = ((harmonic (n + 1) : ℚ) : ℝ) := by
    simp [harmonic]
  have hl := harmonic_le_one_add_log (n + 1)
  rw [hh] at h
  push_cast at hl
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1)
      = 6 * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 1 / (|(k : ℝ)| + 1) := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => by ring
    _ ≤ 6 * (2 * ((harmonic (n + 1) : ℚ) : ℝ)) := by gcongr
    _ ≤ _ := by linarith

lemma ksum {ι : Type*} [DecidableEq ι] (S : Finset ι) (φ : ι → ℝ) (A R : ℝ) (hR0 : 0 ≤ R)
    (hA : ∀ k : ℤ, (((S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k)).card : ℝ) ≤ A)
    (hR : ∀ i ∈ S, ∀ j ∈ S, |φ i - φ j| ≤ R) :
    ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j) ≤ 12 * A * (1 + Real.log (R + 2)) := by
  classical
  set n := ⌈R⌉₊
  have hRn : R ≤ n := Nat.le_ceil R
  have hn1 : (n : ℝ) < R + 1 := Nat.ceil_lt_add_one hR0
  have hA0 : 0 ≤ A := (Nat.cast_nonneg _).trans (hA 0)
  have hmaps : ∀ q ∈ S ×ˢ S, ⌊φ q.1 - φ q.2⌋ ∈ Finset.Icc (-(n : ℤ)) n := by
    intro q hq
    rw [Finset.mem_product] at hq
    have := abs_le.mp (hR _ hq.1 _ hq.2)
    rw [Finset.mem_Icc]
    constructor
    · apply Int.le_floor.mpr; push_cast; linarith
    · have := Int.floor_le (φ q.1 - φ q.2)
      have : ((⌊φ q.1 - φ q.2⌋ : ℤ) : ℝ) ≤ (n : ℤ) := by push_cast; linarith
      exact_mod_cast this
  rw [← Finset.sum_product' (f := fun i j => kern (φ i - φ j))]
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc ∑ k ∈ Finset.Icc (-(n : ℤ)) n, ∑ q ∈ (S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k),
        kern (φ q.1 - φ q.2)
      = ∑ k ∈ Finset.Icc (-(n : ℤ)) n,
          (((S ×ˢ S).filter (fun q => ⌊φ q.1 - φ q.2⌋ = k)).card : ℝ) * (6 / (|(k : ℝ)| + 1)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_congr rfl (g := fun _ => 6 / (|(k : ℝ)| + 1)), Finset.sum_const,
          nsmul_eq_mul]
        intro q hq
        unfold kern
        rw [(Finset.mem_filter.mp hq).2]
    _ ≤ ∑ k ∈ Finset.Icc (-(n : ℤ)) n, A * (6 / (|(k : ℝ)| + 1)) := by
        gcongr with k _
        exact hA k
    _ = A * ∑ k ∈ Finset.Icc (-(n : ℤ)) n, 6 / (|(k : ℝ)| + 1) := by rw [Finset.mul_sum]
    _ ≤ A * (12 * (1 + Real.log (n + 1))) := by gcongr; exact sum_kern_Icc n
    _ ≤ A * (12 * (1 + Real.log (R + 2))) := by
        have := Real.log_le_log (by positivity : (0 : ℝ) < n + 1) (by linarith : (n : ℝ) + 1 ≤ R + 2)
        nlinarith
    _ = _ := by ring

/-! ### Local constancy and multiplicities -/
lemma loc (g g' : ℝ → ℂ) (hg : ∀ x, HasDerivAt g (g' x) x) (hg' : Continuous g') (T : ℝ)
    (hT : 0 < T) (x : ℝ) :
    ‖g x‖ ^ 2 ≤ ∫ y in x..(x + 1 / T), (2 * T * ‖g y‖ ^ 2 + ‖g' y‖ ^ 2 / T) := by
  have hgc : Continuous g := continuous_iff_continuousAt.2 fun x => (hg x).continuousAt
  have hL : 0 < 1 / T := by positivity
  have h := sq_norm_le_avg g g' hg hg' x (1 / T) hL T hT x ⟨le_refl _, by linarith⟩
  have i1 : IntervalIntegrable (fun s => ‖g s‖ ^ 2) MeasureTheory.volume x (x + 1 / T) :=
    (by fun_prop : Continuous fun s => ‖g s‖ ^ 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun s => ‖g' s‖ ^ 2 / T) MeasureTheory.volume x (x + 1 / T) :=
    (by fun_prop : Continuous fun s => ‖g' s‖ ^ 2 / T).intervalIntegrable _ _
  rw [intervalIntegral.integral_add i1 intervalIntegrable_const, intervalIntegral.integral_const]
    at h
  rw [intervalIntegral.integral_add (i1.const_mul _) i2] at h ⊢
  rw [intervalIntegral.integral_const_mul] at h ⊢
  simp only [add_sub_cancel_left, smul_eq_mul] at h
  have e : 1 / (1 / T) = T := by field_simp
  rw [e] at h
  set I1 := ∫ y in x..x + 1 / T, ‖g y‖ ^ 2
  set I2 := ∫ y in x..x + 1 / T, ‖g' y‖ ^ 2 / T
  have e2 : T * (I1 + 1 / T * (T * I1 + I2)) = 2 * T * I1 + I2 := by field_simp; ring
  linarith

lemma sum_int_le {κ : Type*} (P : Finset κ) (τ : κ → ℝ) (δ m : ℝ) (h : ℝ → ℝ)
    (hh : Continuous h) (h0 : ∀ y, 0 ≤ h y) (hδ : 0 ≤ δ)
    (hτ : ∀ p ∈ P, -1 ≤ τ p ∧ τ p + δ ≤ 1)
    (hm : ∀ y, (((P.filter (fun p => τ p < y ∧ y ≤ τ p + δ)).card : ℝ) ≤ m)) :
    ∑ p ∈ P, ∫ y in (τ p)..(τ p + δ), h y ≤ m * ∫ y in (-1 : ℝ)..1, h y := by
  classical
  have hint : MeasureTheory.IntegrableOn h (Set.Ioc (-1 : ℝ) 1) :=
    hh.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  have e1 : ∀ p ∈ P, ∫ y in (τ p)..(τ p + δ), h y =
      ∫ y in Set.Ioc (-1 : ℝ) 1, (Set.Ioc (τ p) (τ p + δ)).indicator h y := by
    intro p hp
    rw [intervalIntegral.integral_of_le (by linarith),
      MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    congr 1
    rw [Set.inter_eq_right.mpr]
    intro y hy
    have := hτ p hp
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [Finset.sum_congr rfl e1, ← MeasureTheory.integral_finsetSum _
    (fun p _ => hint.indicator measurableSet_Ioc)]
  rw [intervalIntegral.integral_of_le (by norm_num), ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_mono
  · exact MeasureTheory.integrable_finsetSum _ (fun p _ => hint.indicator measurableSet_Ioc)
  · exact hint.const_mul m
  · intro y
    simp only [Set.indicator_apply, Set.mem_Ioc]
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hm y) (h0 y)

lemma chain {ι κ : Type*} (S : Finset ι) (φ : ι → ℝ) (B : ℝ) (hB : ∀ i ∈ S, |φ i| ≤ B)
    (P : Finset κ) (τ : κ → ℝ) (T m : ℝ) (hT : 0 < T)
    (hτ : ∀ p ∈ P, -1 ≤ τ p ∧ τ p + 1 / T ≤ 1)
    (hm : ∀ y, (((P.filter (fun p => τ p < y ∧ y ≤ τ p + 1 / T)).card : ℝ) ≤ m)) :
    ∑ p ∈ P, ‖G S φ (τ p)‖ ^ 2 ≤
      m * ((2 * T + B ^ 2 / T) * ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j)) := by
  have hH : Continuous (fun y => 2 * T * ‖G S φ y‖ ^ 2 + ‖G' S φ y‖ ^ 2 / T) := by
    have := continuous_G S φ; have := continuous_G' S φ; fun_prop
  have h1 : ∀ p ∈ P, ‖G S φ (τ p)‖ ^ 2 ≤
      ∫ y in (τ p)..(τ p + 1 / T), (2 * T * ‖G S φ y‖ ^ 2 + ‖G' S φ y‖ ^ 2 / T) :=
    fun p _ => loc _ _ (hasDerivAt_G S φ) (continuous_G' S φ) T hT _
  have h2 := sum_int_le P τ (1 / T) m _ hH (fun y => by positivity) (by positivity) hτ hm
  have hK := mv S φ (fun _ => 1) 1 (by simp)
  have hK' := mv S φ (fun i => (φ i : ℂ) * I) B (fun i hi => by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]; exact hB i hi)
  simp only [one_mul, one_pow] at hK
  have eG : ∀ y, G S φ y = ∑ i ∈ S, E (φ i * y) := fun y => rfl
  have eG' : ∀ y, G' S φ y = ∑ i ∈ S, ((φ i : ℂ) * I) * E (φ i * y) := fun y => rfl
  have hm0 : 0 ≤ m := (Nat.cast_nonneg _).trans (hm 0)
  have i1 : IntervalIntegrable (fun y => ‖G S φ y‖ ^ 2) MeasureTheory.volume (-1 : ℝ) 1 :=
    (by have := continuous_G S φ; fun_prop : Continuous fun y => ‖G S φ y‖ ^ 2).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun y => ‖G' S φ y‖ ^ 2) MeasureTheory.volume (-1 : ℝ) 1 :=
    (by have := continuous_G' S φ; fun_prop : Continuous fun y => ‖G' S φ y‖ ^ 2).intervalIntegrable _ _
  have e : ∫ y in (-1 : ℝ)..1, (2 * T * ‖G S φ y‖ ^ 2 + ‖G' S φ y‖ ^ 2 / T) =
      2 * T * (∫ y in (-1 : ℝ)..1, ‖G S φ y‖ ^ 2) + (∫ y in (-1 : ℝ)..1, ‖G' S φ y‖ ^ 2) / T := by
    rw [intervalIntegral.integral_add (i1.const_mul _) (i2.div_const _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_div]
  simp only [← eG, ← eG'] at hK hK'
  set K := ∑ i ∈ S, ∑ j ∈ S, kern (φ i - φ j)
  calc ∑ p ∈ P, ‖G S φ (τ p)‖ ^ 2
      ≤ ∑ p ∈ P, ∫ y in (τ p)..(τ p + 1 / T), (2 * T * ‖G S φ y‖ ^ 2 + ‖G' S φ y‖ ^ 2 / T) :=
        Finset.sum_le_sum h1
    _ ≤ _ := h2
    _ ≤ m * (2 * T * K + B ^ 2 * K / T) := by
        rw [e]; gcongr
    _ = _ := by ring

/-! ### Bin counts -/
lemma bin1 (W : Finset ℝ) (hW : IsSeparated 1 W) (c : ℝ) (k : ℤ) :
    (((W ×ˢ W).filter (fun q => ⌊(q.1 - c) - (q.2 - c)⌋ = k)).card : ℝ) ≤ W.card := by
  classical
  have hle : ∀ x ∈ W, (W.filter (fun y => ⌊(x - c) - (y - c)⌋ = k)).card ≤ 1 := by
    intro x _
    apply Finset.card_le_one.mpr
    intro y hy y' hy'
    rw [Finset.mem_filter] at hy hy'
    by_contra hne
    have hs := hW y hy.1 y' hy'.1 hne
    have a1 := Int.floor_le ((x - c) - (y - c))
    have a2 := Int.lt_floor_add_one ((x - c) - (y - c))
    have b1 := Int.floor_le ((x - c) - (y' - c))
    have b2 := Int.lt_floor_add_one ((x - c) - (y' - c))
    rw [hy.2] at a1 a2; rw [hy'.2] at b1 b2
    rcases le_abs.mp hs with h | h <;> linarith
  have : ((W ×ˢ W).filter (fun q => ⌊(q.1 - c) - (q.2 - c)⌋ = k)).card ≤ W.card := by
    rw [Finset.card_filter, Finset.sum_product]
    calc ∑ x ∈ W, ∑ y ∈ W, (if ⌊(x - c) - (y - c)⌋ = k then 1 else 0)
        = ∑ x ∈ W, (W.filter (fun y => ⌊(x - c) - (y - c)⌋ = k)).card :=
          Finset.sum_congr rfl fun x _ => (Finset.card_filter _ _).symm
      _ ≤ ∑ x ∈ W, 1 := Finset.sum_le_sum hle
      _ = W.card := by simp
  exact_mod_cast this

end GuthMaynard.E111.PartD
end

section
namespace GuthMaynard.E111.PartD
open GuthMaynard GuthMaynard.E111 Complex
variable {α : Type*}
/-- `Q V g k = #{(p, q) ∈ V² : g p - g q = k}`. -/
def Qc (V : Finset α) (g : α → ℤ) (k : ℤ) : ℕ :=
  ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k)).card

def rc (V : Finset α) (g : α → ℤ) (j : ℤ) : ℕ := (V.filter (fun p => g p = j)).card

lemma Qc_eq (V : Finset α) (g : α → ℤ) (k : ℤ) :
    Qc V g k = ∑ j ∈ V.image g, rc V g j * rc V g (j - k) := by
  unfold Qc
  rw [Finset.card_filter, Finset.sum_product]
  have : ∀ p ∈ V, ∑ q ∈ V, (if g p - g q = k then 1 else 0) = rc V g (g p - k) := by
    intro p _
    rw [← Finset.card_filter]; unfold rc
    congr 1; apply Finset.filter_congr; intro q _; omega
  rw [Finset.sum_congr rfl this, Finset.sum_comp (fun j => rc V g (j - k)) g]
  rfl

lemma rc_ne_zero (V : Finset α) (g : α → ℤ) (j : ℤ) (h : rc V g j ≠ 0) : j ∈ V.image g := by
  unfold rc at h
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter] at hp
  exact Finset.mem_image.mpr ⟨p, hp.1, hp.2⟩

lemma Qc_le (V : Finset α) (g : α → ℤ) (k : ℤ) : Qc V g k ≤ Qc V g 0 := by
  rw [Qc_eq, Qc_eq]
  simp only [sub_zero]
  set J := V.image g
  have hsh : ∑ j ∈ J, rc V g (j - k) ^ 2 ≤ ∑ j ∈ J, rc V g j ^ 2 := by
    rw [← Finset.sum_image (f := fun j => rc V g j ^ 2) (s := J) (g := fun j => j - k)
      (fun a _ b _ h => by simpa using h)]
    apply Finset.sum_le_sum_of_ne_zero
    intro j _ hj
    exact rc_ne_zero V g j (by intro h0; apply hj; simp [h0])
  have h2 : ∀ j ∈ J, 2 * (rc V g j * rc V g (j - k)) ≤ rc V g j ^ 2 + rc V g (j - k) ^ 2 := by
    intro j _
    nlinarith [sq_nonneg ((rc V g j : ℤ) - rc V g (j - k))]
  have h3 : 2 * ∑ j ∈ J, rc V g j * rc V g (j - k) ≤
      ∑ j ∈ J, rc V g j ^ 2 + ∑ j ∈ J, rc V g (j - k) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]; exact Finset.sum_le_sum h2
  have h4 : ∑ j ∈ J, rc V g j * rc V g j = ∑ j ∈ J, rc V g j ^ 2 :=
    Finset.sum_congr rfl fun j _ => (sq _).symm
  omega

end GuthMaynard.E111.PartD
end

section
namespace GuthMaynard.E111.PartD
open GuthMaynard GuthMaynard.E111 Complex
lemma floor_sub_cases (x y : ℝ) (k : ℤ) (h : ⌊x - y⌋ = k) :
    ⌊x⌋ - ⌊y⌋ = k ∨ ⌊x⌋ - ⌊y⌋ = k + 1 := by
  have a1 := Int.floor_le x; have a2 := Int.lt_floor_add_one x
  have b1 := Int.floor_le y; have b2 := Int.lt_floor_add_one y
  have c1 := Int.floor_le (x - y); have c2 := Int.lt_floor_add_one (x - y)
  rw [h] at c1 c2
  have h1 : ((k : ℤ) : ℝ) - 1 < ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by push_cast; linarith
  have h2 : ((⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) < ((k + 2 : ℤ) : ℝ) := by push_cast; linarith
  have h1' : k - 1 < ⌊x⌋ - ⌊y⌋ := by exact_mod_cast h1
  have h2' : ⌊x⌋ - ⌊y⌋ < k + 2 := by exact_mod_cast h2
  omega

lemma bin2 (W : Finset ℝ) (c : ℝ) (k : ℤ) :
    ((((W ×ˢ W) ×ˢ (W ×ˢ W)).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)).card : ℝ) ≤
      2 * (energy W : ℝ) := by
  classical
  set V := W ×ˢ W with hV
  set g : ℝ × ℝ → ℤ := fun p => ⌊p.1 + p.2⌋
  have hsub : ((V ×ˢ V).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)) ⊆
      ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k)) ∪
        ((V ×ˢ V).filter (fun q => g q.1 - g q.2 = k + 1)) := by
    intro q hq
    rw [Finset.mem_filter] at hq
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    have e : (q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c) = (q.1.1 + q.1.2) - (q.2.1 + q.2.2) := by
      ring
    rw [e] at hq
    rcases floor_sub_cases _ _ k hq.2 with h | h
    · exact Or.inl ⟨hq.1, h⟩
    · exact Or.inr ⟨hq.1, h⟩
  have h1 := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hQ0 : Qc V g 0 ≤ energy W := by
    unfold Qc energy
    apply Finset.card_le_card_of_injOn (fun q => (q.1.1, q.1.2, q.2.1, q.2.2))
    · intro q hq
      simp only [hV, Finset.coe_filter, Set.mem_ofPred_eq, Finset.mem_product] at hq ⊢
      obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hq
      refine ⟨⟨h1, h2, h3, h4⟩, ?_⟩
      have hg : ⌊q.1.1 + q.1.2⌋ = ⌊q.2.1 + q.2.2⌋ := by simp only [g] at h5; omega
      have a1 := Int.floor_le (q.1.1 + q.1.2); have a2 := Int.lt_floor_add_one (q.1.1 + q.1.2)
      have b1 := Int.floor_le (q.2.1 + q.2.2); have b2 := Int.lt_floor_add_one (q.2.1 + q.2.2)
      rw [hg] at a1 a2
      rw [abs_le]; constructor <;> linarith
    · intro q _ q' _ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      exact Prod.ext (Prod.ext h1 h2) (Prod.ext h3 h4)
  have hk1 := Qc_le V g k
  have hk2 := Qc_le V g (k + 1)
  unfold Qc at hk1 hk2 hQ0
  have : ((V ×ˢ V).filter
      (fun q => ⌊(q.1.1 + q.1.2 - c) - (q.2.1 + q.2.2 - c)⌋ = k)).card ≤ 2 * energy W := by
    omega
  exact_mod_cast this

/-! ### Separation of `log n₁ - log n₂` -/
noncomputable def tau (p : ℕ × ℕ) : ℝ := Real.log p.1 - Real.log p.2

lemma sep_count {κ : Type*} (P : Finset κ) (τ : κ → ℝ) (s δ y : ℝ) (hs : 0 < s) (hδ : 0 ≤ δ)
    (hsep : ∀ i ∈ P, ∀ j ∈ P, i ≠ j → s ≤ |τ i - τ j|)
    (hin : ∀ i ∈ P, y - δ ≤ τ i ∧ τ i < y) : (P.card : ℝ) ≤ δ / s + 1 := by
  have hc : P.card ≤ (Finset.range (⌊δ / s⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun i => ⌊(τ i - (y - δ)) / s⌋₊)
    · intro i hi
      have := hin i hi
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by gcongr; linarith [this.2]))
    · intro i hi j hj he
      by_contra hne
      have h1 := hsep i hi j hj hne
      have a1 := (hin i hi).1
      have a2 := (hin j hj).1
      simp only at he
      have b1 := Nat.floor_le (div_nonneg (by linarith : 0 ≤ τ i - (y - δ)) hs.le)
      have b2 := Nat.lt_floor_add_one ((τ i - (y - δ)) / s)
      have b3 := Nat.floor_le (div_nonneg (by linarith : 0 ≤ τ j - (y - δ)) hs.le)
      have b4 := Nat.lt_floor_add_one ((τ j - (y - δ)) / s)
      rw [he] at b1 b2
      rw [le_div_iff₀ hs] at b1 b3
      rw [div_lt_iff₀ hs] at b2 b4
      have : |τ i - τ j| < s := by rw [abs_sub_lt_iff]; constructor <;> nlinarith
      linarith
  rw [Finset.card_range] at hc
  have := Nat.floor_le (div_nonneg hδ hs.le)
  have : (P.card : ℝ) ≤ (⌊δ / s⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

lemma log_sub_ge (x y M : ℝ) (hx : 0 < x) (hy : 0 < y) (hxM : x ≤ M) (hyM : y ≤ M) :
    |x - y| / M ≤ |Real.log x - Real.log y| := by
  have hM : 0 < M := lt_of_lt_of_le hx hxM
  have key : ∀ u v : ℝ, 0 < u → 0 < v → v ≤ u → u ≤ M → (u - v) / M ≤ Real.log u - Real.log v := by
    intro u v hu hv hvu huM
    have h1 := Real.one_sub_inv_le_log_of_pos (div_pos hu hv)
    rw [Real.log_div hu.ne' hv.ne', inv_div] at h1
    have h2 : (u - v) / M ≤ (u - v) / u := div_le_div_of_nonneg_left (by linarith) hu huM
    have h3 : (u - v) / u = 1 - v / u := by field_simp
    linarith
  rcases le_total y x with h | h
  · rw [abs_of_nonneg (by linarith : 0 ≤ x - y)]
    exact (key x y hx hy h hxM).trans (le_abs_self _)
  · rw [abs_sub_comm, abs_of_nonneg (by linarith : 0 ≤ y - x), abs_sub_comm]
    exact (key y x hy hx h hyM).trans (le_abs_self _)

lemma gcd_sep (N : ℕ) (p q : ℕ × ℕ)
    (hp : p ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N))
    (hq : q ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N))
    (hg : Nat.gcd p.1 p.2 = Nat.gcd q.1 q.2) (hne : p ≠ q) :
    ((Nat.gcd p.1 p.2 : ℝ) ^ 2) / (4 * (N : ℝ) ^ 2) ≤ |tau p - tau q| := by
  obtain ⟨n₁, n₂⟩ := p
  obtain ⟨m₁, m₂⟩ := q
  simp only [Finset.mem_product, Finset.mem_Ioc] at hp hq hg ⊢
  set d := Nat.gcd n₁ n₂ with hd
  have hd0 : 0 < d := Nat.gcd_pos_of_pos_left _ (by omega)
  have hdm : Nat.gcd m₁ m₂ = d := hg.symm
  -- X = n₁ m₂, Y = m₁ n₂
  have hXY : n₁ * m₂ ≠ m₁ * n₂ := by
    intro hxy
    have e1 : Nat.gcd (n₁ * m₂) (n₂ * m₂) = d * m₂ := Nat.gcd_mul_right n₁ m₂ n₂
    have e2 : Nat.gcd (m₁ * n₂) (m₂ * n₂) = d * n₂ := by rw [Nat.gcd_mul_right, hdm]
    rw [hxy, mul_comm n₂ m₂] at e1
    rw [e1] at e2
    have h2 : m₂ = n₂ := Nat.eq_of_mul_eq_mul_left hd0 e2
    subst h2
    have h1 : n₁ = m₁ := Nat.eq_of_mul_eq_mul_right (by omega) hxy
    subst h1
    exact hne rfl
  have hdX : d * d ∣ n₁ * m₂ :=
    Nat.mul_dvd_mul (Nat.gcd_dvd_left _ _) (hdm ▸ Nat.gcd_dvd_right m₁ m₂)
  have hdY : d * d ∣ m₁ * n₂ :=
    Nat.mul_dvd_mul (hdm ▸ Nat.gcd_dvd_left m₁ m₂) (Nat.gcd_dvd_right _ _)
  have hdiff : ((d : ℤ) ^ 2) ≤ |((n₁ * m₂ : ℕ) : ℤ) - ((m₁ * n₂ : ℕ) : ℤ)| := by
    have hdv : ((d : ℤ) ^ 2) ∣ ((n₁ * m₂ : ℕ) : ℤ) - ((m₁ * n₂ : ℕ) : ℤ) := by
      rw [sq]
      exact dvd_sub (by exact_mod_cast hdX) (by exact_mod_cast hdY)
    apply Int.le_of_dvd
    · apply abs_pos.mpr; intro h0; apply hXY; exact_mod_cast sub_eq_zero.mp h0
    · exact (dvd_abs _ _).mpr hdv
  have hdiffR : (d : ℝ) ^ 2 ≤ |((n₁ * m₂ : ℕ) : ℝ) - ((m₁ * n₂ : ℕ) : ℝ)| := by
    have : (((d : ℤ) ^ 2 : ℤ) : ℝ) ≤ ((|((n₁ * m₂ : ℕ) : ℤ) - ((m₁ * n₂ : ℕ) : ℤ)| : ℤ) : ℝ) := by
      exact_mod_cast hdiff
    push_cast at this ⊢
    exact this
  have hN0 : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hX0 : (0 : ℝ) < ((n₁ * m₂ : ℕ) : ℝ) := by
    have : 0 < n₁ * m₂ := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hY0 : (0 : ℝ) < ((m₁ * n₂ : ℕ) : ℝ) := by
    have : 0 < m₁ * n₂ := Nat.mul_pos (by omega) (by omega)
    exact_mod_cast this
  have hXM : ((n₁ * m₂ : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
    have : n₁ * m₂ ≤ (2 * N) * (2 * N) := Nat.mul_le_mul hp.1.2 hq.2.2
    have : ((n₁ * m₂ : ℕ) : ℝ) ≤ (((2 * N) * (2 * N) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢; nlinarith
  have hYM : ((m₁ * n₂ : ℕ) : ℝ) ≤ 4 * (N : ℝ) ^ 2 := by
    have : m₁ * n₂ ≤ (2 * N) * (2 * N) := Nat.mul_le_mul hq.1.2 hp.2.2
    have : ((m₁ * n₂ : ℕ) : ℝ) ≤ (((2 * N) * (2 * N) : ℕ) : ℝ) := by exact_mod_cast this
    push_cast at this ⊢; nlinarith
  have hl := log_sub_ge _ _ _ hX0 hY0 hXM hYM
  have etau : tau (n₁, n₂) - tau (m₁, m₂) =
      Real.log ((n₁ * m₂ : ℕ) : ℝ) - Real.log ((m₁ * n₂ : ℕ) : ℝ) := by
    unfold tau
    have : (0 : ℝ) < n₁ := by exact_mod_cast (show 0 < n₁ by omega)
    have : (0 : ℝ) < n₂ := by exact_mod_cast (show 0 < n₂ by omega)
    have : (0 : ℝ) < m₁ := by exact_mod_cast (show 0 < m₁ by omega)
    have : (0 : ℝ) < m₂ := by exact_mod_cast (show 0 < m₂ by omega)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    ring
  rw [etau]
  refine le_trans ?_ hl
  gcongr

lemma tau_bound (N : ℕ) (p : ℕ × ℕ) (hp : p ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)) :
    |tau p| ≤ 7 / 10 := by
  rw [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Ioc] at hp
  obtain ⟨⟨a1, a2⟩, ⟨b1, b2⟩⟩ := hp
  have ha : (N : ℝ) < p.1 := by exact_mod_cast a1
  have ha' : (p.1 : ℝ) ≤ 2 * N := by exact_mod_cast a2
  have hb : (N : ℝ) < p.2 := by exact_mod_cast b1
  have hb' : (p.2 : ℝ) ≤ 2 * N := by exact_mod_cast b2
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have l1 : Real.log p.1 ≤ Real.log 2 + Real.log p.2 := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have l2 : Real.log p.2 ≤ Real.log 2 + Real.log p.1 := by
    rw [← Real.log_mul (by norm_num) (by linarith)]
    exact Real.log_le_log (by linarith) (by linarith)
  have := Real.log_two_lt_d9
  unfold tau
  rw [abs_le]; constructor <;> linarith

lemma mult (N : ℕ) (hN : 1 ≤ N) (Dg T : ℝ) (hDg : 0 ≤ Dg) (hT : 0 < T) (y : ℝ) :
    ((((Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (Nat.gcd p.1 p.2 : ℝ) ≤ Dg)).filter
        (fun p => tau p < y ∧ y ≤ tau p + 1 / T)).card : ℝ) ≤ Dg + 8 * (N : ℝ) ^ 2 / T := by
  classical
  set Pr := Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N) with hPr
  set S' := (Pr.filter (fun p => (Nat.gcd p.1 p.2 : ℝ) ≤ Dg)).filter
        (fun p => tau p < y ∧ y ≤ tau p + 1 / T) with hS'
  set K := ⌊Dg⌋₊
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hmaps : ∀ p ∈ S', Nat.gcd p.1 p.2 ∈ Finset.Icc 1 K := by
    intro p hp
    simp only [hS', Finset.mem_filter, hPr, Finset.mem_product, Finset.mem_Ioc] at hp
    rw [Finset.mem_Icc]
    exact ⟨Nat.gcd_pos_of_pos_left _ (by omega), Nat.le_floor hp.1.2⟩
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  push_cast
  have hfib : ∀ d ∈ Finset.Icc 1 K, ((S'.filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ) ≤
      4 * (N : ℝ) ^ 2 / T * (1 / (d : ℝ) ^ 2) + 1 := by
    intro d hd
    have hd1 : (0 : ℝ) < d := by
      have := (Finset.mem_Icc.mp hd).1; exact_mod_cast (show 0 < d by omega)
    have hs : 0 < (d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2) := by positivity
    have := sep_count (S'.filter (fun p => Nat.gcd p.1 p.2 = d)) tau ((d : ℝ) ^ 2 / (4 * (N : ℝ) ^ 2))
      (1 / T) y hs (by positivity) (by
        intro p hp q hq hpq
        simp only [hS', Finset.mem_filter] at hp hq
        have := gcd_sep N p q hp.1.1.1 hq.1.1.1 (hp.2.trans hq.2.symm) hpq
        rw [hp.2] at this
        exact this) (by
        intro p hp
        simp only [hS', Finset.mem_filter] at hp
        exact ⟨by linarith [hp.1.2.2], hp.1.2.1⟩)
    refine this.trans (le_of_eq ?_)
    field_simp
  calc ∑ d ∈ Finset.Icc 1 K, ((S'.filter (fun p => Nat.gcd p.1 p.2 = d)).card : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 K, (4 * (N : ℝ) ^ 2 / T * (1 / (d : ℝ) ^ 2) + 1) :=
        Finset.sum_le_sum hfib
    _ = 4 * (N : ℝ) ^ 2 / T * ∑ d ∈ Finset.Icc 1 K, (1 / (d : ℝ) ^ 2) + K := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp
    _ ≤ 4 * (N : ℝ) ^ 2 / T * 2 + Dg := by
        have h2 : ∑ d ∈ Finset.Icc 1 K, (1 / (d : ℝ) ^ 2) ≤ 2 := by
          have e : Finset.Icc 1 K = Finset.Ioo 0 (K + 1) := by ext; simp; omega
          rw [e]
          have := sum_Ioo_inv_sq_le (α := ℝ) 0 (K + 1)
          simp only [one_div]
          norm_num at this ⊢
          exact this
        have h3 : (K : ℝ) ≤ Dg := Nat.floor_le hDg
        gcongr
    _ = _ := by ring

/-! ### Main bound -/
lemma eventually_const_mul_le (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, C * T ^ (ε / 2) ≤ T ^ ε := by
  have h := (tendsto_rpow_atTop (by linarith : 0 < ε / 2)).eventually_ge_atTop C
  filter_upwards [h, Filter.eventually_ge_atTop 0] with T hT hT0
  have : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_add' hT0 (by linarith)]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg hT0 _)

lemma main_bound (T : ℝ) (hT : 4 ≤ T) (N : ℕ) (hN : 1 ≤ N) (Dg : ℝ) (hDg : 0 ≤ Dg)
    (W : Finset ℝ) (a : ℝ) (hW : IsSeparated 1 W) (hWa : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) :
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (Nat.gcd p.1 p.2 : ℝ) ≤ Dg),
      ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3 ≤
      (360 * (1 + Real.log (2 * T + 2))) * (Dg * T + (N : ℝ) ^ 2) * (W.card : ℝ) ^ (1 / 2 : ℝ) *
        (energy W : ℝ) ^ (1 / 2 : ℝ) := by
  classical
  set S' := (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (Nat.gcd p.1 p.2 : ℝ) ≤ Dg) with hS'
  have hT0 : 0 < T := by linarith
  set c₀ := a + T / 2 with hc₀
  set m := Dg + 8 * (N : ℝ) ^ 2 / T with hm_def
  set L := 1 + Real.log (2 * T + 2) with hL_def
  have hτ : ∀ p ∈ S', -1 ≤ tau p ∧ tau p + 1 / T ≤ 1 := by
    intro p hp
    have h1 := tau_bound N p (Finset.mem_filter.mp hp).1
    have h2 : 1 / T ≤ 1 / 4 := by gcongr
    rw [abs_le] at h1
    constructor <;> linarith [h1.1, h1.2]
  have hm := mult N hN Dg T hDg hT0
  have hL1 : 1 + Real.log (T + 2) ≤ L := by
    have := Real.log_le_log (by linarith) (by linarith : T + 2 ≤ 2 * T + 2)
    linarith
  have hL0 : 0 ≤ 1 + Real.log (T + 2) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ T + 2); linarith
  have hE0 : (0 : ℝ) ≤ energy W := by positivity
  have hW0 : (0 : ℝ) ≤ W.card := by positivity
  have hm0 : 0 ≤ m := by positivity
  -- second moment
  have hX : ∑ p ∈ S', ‖Rl W (tau p)‖ ^ 2 ≤ m * T * (27 * (W.card : ℝ) * L) := by
    have hc := chain W (fun t => t - c₀) (T / 2) (fun t ht => by
        have := hWa t ht; rw [abs_le]; constructor <;> linarith [this.1, this.2])
      S' tau T m hT0 hτ hm
    have hk := ksum W (fun t => t - c₀) (W.card : ℝ) T hT0.le (fun k => bin1 W hW c₀ k)
      (fun i hi j hj => by
        obtain ⟨_, _⟩ := hWa i hi; obtain ⟨_, _⟩ := hWa j hj
        rw [abs_le]; constructor <;> linarith)
    have e : ∀ p, ‖Rl W (tau p)‖ = ‖G W (fun t => t - c₀) (tau p)‖ := fun p =>
      (G_shift W (fun t => t) c₀ (tau p)).symm
    simp only [e]
    refine hc.trans ?_
    have hK0 : 0 ≤ ∑ i ∈ W, ∑ j ∈ W, kern ((fun t => t - c₀) i - (fun t => t - c₀) j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => kern_nonneg _
    calc m * ((2 * T + (T / 2) ^ 2 / T) *
          ∑ i ∈ W, ∑ j ∈ W, kern ((fun t => t - c₀) i - (fun t => t - c₀) j))
        ≤ m * ((2 * T + (T / 2) ^ 2 / T) * (12 * W.card * (1 + Real.log (T + 2)))) := by
          gcongr
      _ ≤ m * ((2 * T + (T / 2) ^ 2 / T) * (12 * W.card * L)) := by gcongr
      _ = m * T * (27 * (W.card : ℝ) * L) := by field_simp; ring
  -- fourth moment
  have hY : ∑ p ∈ S', (‖Rl W (tau p)‖ ^ 2) ^ 2 ≤ m * T * (72 * (energy W : ℝ) * L) := by
    have hc := chain (W ×ˢ W) (fun q => q.1 + q.2 - 2 * c₀) T (fun q hq => by
        rw [Finset.mem_product] at hq
        obtain ⟨_, _⟩ := hWa _ hq.1; obtain ⟨_, _⟩ := hWa _ hq.2; rw [abs_le]; constructor <;> linarith)
      S' tau T m hT0 hτ hm
    have hk := ksum (W ×ˢ W) (fun q => q.1 + q.2 - 2 * c₀) (2 * (energy W : ℝ)) (2 * T)
      (by linarith) (fun k => bin2 W (2 * c₀) k)
      (fun i hi j hj => by
        rw [Finset.mem_product] at hi hj
        obtain ⟨_, _⟩ := hWa _ hi.1; obtain ⟨_, _⟩ := hWa _ hi.2
        obtain ⟨_, _⟩ := hWa _ hj.1; obtain ⟨_, _⟩ := hWa _ hj.2
        rw [abs_le]; constructor <;> linarith)
    have e : ∀ p, (‖Rl W (tau p)‖ ^ 2) ^ 2 =
        ‖G (W ×ˢ W) (fun q => q.1 + q.2 - 2 * c₀) (tau p)‖ ^ 2 := fun p => by
      rw [G_shift (W ×ˢ W) (fun q => q.1 + q.2) (2 * c₀) (tau p), G_WW, norm_pow]
    simp only [e]
    refine hc.trans ?_
    have hK0 : 0 ≤ ∑ i ∈ W ×ˢ W, ∑ j ∈ W ×ˢ W,
        kern ((fun q => q.1 + q.2 - 2 * c₀) i - (fun q => q.1 + q.2 - 2 * c₀) j) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => kern_nonneg _
    calc _ ≤ m * ((2 * T + T ^ 2 / T) * (12 * (2 * (energy W : ℝ)) * L)) := by
          gcongr
      _ = m * T * (72 * (energy W : ℝ) * L) := by field_simp; ring
  -- Cauchy–Schwarz
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt S' (fun p => ‖Rl W (tau p)‖)
    (fun p => ‖Rl W (tau p)‖ ^ 2)
  have e3 : ∀ p, ‖Rl W (tau p)‖ * ‖Rl W (tau p)‖ ^ 2 = ‖Rl W (tau p)‖ ^ 3 := fun p => by ring
  simp only [e3] at hCS
  unfold tau at hCS
  refine hCS.trans ?_
  have hmT : m * T ≤ 8 * (Dg * T + (N : ℝ) ^ 2) := by
    simp only [m]; field_simp; nlinarith [mul_nonneg hDg hT0.le, sq_nonneg (N : ℝ)]
  have hQ0 : 0 ≤ Dg * T + (N : ℝ) ^ 2 := by positivity
  have hLpos : 0 ≤ L := hL0.trans hL1
  rw [← Real.sqrt_mul (Finset.sum_nonneg fun _ _ => by positivity),
    ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have hR : 360 * L * (Dg * T + (N : ℝ) ^ 2) * √(W.card : ℝ) * √(energy W : ℝ) =
      √((360 * L * (Dg * T + (N : ℝ) ^ 2)) ^ 2 * ((W.card : ℝ) * (energy W : ℝ))) := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.sqrt_mul hW0]; ring
  rw [hR]
  apply Real.sqrt_le_sqrt
  unfold tau at hX hY
  have hXY := mul_le_mul hX hY (Finset.sum_nonneg fun _ _ => by positivity) (by positivity)
  refine hXY.trans ?_
  have hmT0 : 0 ≤ m * T := by positivity
  have hmT2 : (m * T) ^ 2 ≤ (8 * (Dg * T + (N : ℝ) ^ 2)) ^ 2 := pow_le_pow_left₀ hmT0 hmT 2
  have hwe : 0 ≤ L ^ 2 * ((W.card : ℝ) * (energy W : ℝ)) := by positivity
  calc m * T * (27 * (W.card : ℝ) * L) * (m * T * (72 * (energy W : ℝ) * L))
      = 1944 * (m * T) ^ 2 * (L ^ 2 * ((W.card : ℝ) * (energy W : ℝ))) := by ring
    _ ≤ 1944 * (8 * (Dg * T + (N : ℝ) ^ 2)) ^ 2 * (L ^ 2 * ((W.card : ℝ) * (energy W : ℝ))) := by
        gcongr
    _ ≤ _ := by
        have : 0 ≤ (Dg * T + (N : ℝ) ^ 2) ^ 2 * (L ^ 2 * ((W.card : ℝ) * (energy W : ℝ))) := by
          positivity
        nlinarith

theorem small_gcd : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ), 1 ≤ N →
    (N : ℝ) ≤ T → ∀ Dg : ℝ, 0 ≤ Dg →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (Nat.gcd p.1 p.2 : ℝ) ≤ Dg),
      ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3 ≤
      T ^ ε * (Dg * T + (N : ℝ) ^ 2) * (W.card : ℝ) ^ (1 / 2 : ℝ) *
        (energy W : ℝ) ^ (1 / 2 : ℝ) := by
  intro ε hε
  have ev := eventually_const_mul_le (360 * (1 + 4 / ε)) ε hε
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.mp (ev.and (Filter.eventually_ge_atTop 4))
  refine ⟨T₁, fun T hT N hN hNT Dg hDg W a hW hWa => ?_⟩
  obtain ⟨hC, hT4⟩ := hT₁ T hT
  have hmain := main_bound T hT4 N hN Dg hDg W a hW hWa
  refine hmain.trans ?_
  have hK : 360 * (1 + Real.log (2 * T + 2)) ≤ T ^ ε := by
    have h1 : Real.log (2 * T + 2) ≤ 2 * Real.log T := by
      rw [← Real.log_rpow (by linarith)]
      exact Real.log_le_log (by linarith) (by rw [Real.rpow_two]; nlinarith)
    have h2 := Real.log_le_rpow_div (by linarith : (0 : ℝ) ≤ T) (by linarith : 0 < ε / 2)
    have h3 : 1 ≤ T ^ (ε / 2) := Real.one_le_rpow (by linarith) (by linarith)
    have h4 : 2 * (T ^ (ε / 2) / (ε / 2)) = 4 / ε * T ^ (ε / 2) := by field_simp; ring
    have h5 : 0 ≤ 4 / ε := by positivity
    nlinarith
  have hR : 0 ≤ (Dg * T + (N : ℝ) ^ 2) * (W.card : ℝ) ^ (1 / 2 : ℝ) *
      (energy W : ℝ) ^ (1 / 2 : ℝ) := by
    have : 0 ≤ T := by linarith
    positivity
  calc _ = (360 * (1 + Real.log (2 * T + 2))) * ((Dg * T + (N : ℝ) ^ 2) *
        (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by ring
    _ ≤ T ^ ε * ((Dg * T + (N : ℝ) ^ 2) *
        (W.card : ℝ) ^ (1 / 2 : ℝ) * (energy W : ℝ) ^ (1 / 2 : ℝ)) := by gcongr
    _ = _ := by ring

end GuthMaynard.E111.PartD
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias small_gcd := GuthMaynard.E111.PartD.small_gcd

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartE
open GuthMaynard GuthMaynard.E111 Complex
/-! ### Polynomial algebra (paper p. 45), in the variables `u = w^{1/8}`, `s = T^{1/4}`, `e = E^{1/4}`. -/
lemma poly (P s u e : ℝ) (hs : 1 ≤ s) (hu : 1 ≤ u) (he : 0 ≤ e) (hsP : s ^ 3 ≤ P)
    (hE : e ^ 4 ≤ 3 * u ^ 24) (hw : u ^ 8 ≤ 2 * s ^ 4) :
    (P * u ^ 16 + s ^ 4 * u ^ 8 + u ^ 10 * s ^ 2 * P) *
      (P * u ^ 32 + s ^ 4 * e ^ 4 + e ^ 3 * u ^ 8 * s ^ 2 * P) ≤
      8 * (P * u ^ 24 + P * s * u ^ 21 + e ^ 2 * u ^ 4 * P ^ 2) ^ 2 := by
  have hs0 : 0 ≤ s := by linarith
  have hu0 : 0 ≤ u := by linarith
  have hP1 : 1 ≤ P := le_trans (one_le_pow₀ hs) hsP
  have hP0 : 0 ≤ P := by linarith
  have hu12 : 0 ≤ u ^ 12 := by positivity
  have he2 : e ^ 2 ≤ 2 * u ^ 12 := by nlinarith [sq_nonneg (e ^ 2), sq_nonneg (u ^ 12)]
  have he1 : e ≤ 2 * u ^ 6 := by nlinarith [sq_nonneg e, pow_nonneg hu0 6]
  have hus : u ^ 2 ≤ 2 * s := by
    have : (u ^ 2) ^ 4 ≤ (2 * s) ^ 4 := by nlinarith [pow_nonneg hs0 4]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp this
  have hs2P : s ^ 2 ≤ P := le_trans (pow_le_pow_right₀ hs (by norm_num)) hsP
  have hs4 : s ^ 4 ≤ P ^ 2 := by
    calc s ^ 4 ≤ s ^ 6 := pow_le_pow_right₀ hs (by norm_num)
      _ = (s ^ 3) ^ 2 := by ring
      _ ≤ P ^ 2 := by gcongr
  have hs5 : s ^ 5 ≤ P ^ 2 := by
    calc s ^ 5 ≤ s ^ 6 := pow_le_pow_right₀ hs (by norm_num)
      _ = (s ^ 3) ^ 2 := by ring
      _ ≤ P ^ 2 := by gcongr
  have he4 : e ^ 4 ≤ e ^ 2 * (2 * u ^ 12) := by
    have : e ^ 4 = e ^ 2 * e ^ 2 := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left he2 (by positivity)
  have he3 : e ^ 3 ≤ e ^ 2 * (2 * u ^ 6) := by
    have : e ^ 3 = e ^ 2 * e := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left he1 (by positivity)
  have hu810 : u ^ 8 ≤ u ^ 10 := pow_le_pow_right₀ hu (by norm_num)
  have hu2425 : u ^ 24 ≤ u ^ 25 := pow_le_pow_right₀ hu (by norm_num)
  have hu2225 : u ^ 22 ≤ u ^ 25 := pow_le_pow_right₀ hu (by norm_num)
  -- the six products
  have k2 : P * u ^ 16 * (s ^ 4 * e ^ 4) ≤ 2 * ((P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2)) := by
    calc P * u ^ 16 * (s ^ 4 * e ^ 4) ≤ P * u ^ 16 * (P ^ 2 * (e ^ 2 * (2 * u ^ 12))) := by
          gcongr
      _ = 2 * ((P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2)) := by ring
  have k3 : P * u ^ 16 * (e ^ 3 * u ^ 8 * s ^ 2 * P) ≤
      4 * ((P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2)) := by
    have h1 : u ^ 6 * s ^ 2 ≤ 2 * u ^ 4 * P := by
      calc u ^ 6 * s ^ 2 = u ^ 4 * (u ^ 2 * s ^ 2) := by ring
        _ ≤ u ^ 4 * (2 * s * s ^ 2) := by gcongr
        _ = 2 * u ^ 4 * s ^ 3 := by ring
        _ ≤ 2 * u ^ 4 * P := by gcongr
    calc P * u ^ 16 * (e ^ 3 * u ^ 8 * s ^ 2 * P)
        ≤ P * u ^ 16 * (e ^ 2 * (2 * u ^ 6) * u ^ 8 * s ^ 2 * P) := by gcongr
      _ = 2 * P ^ 2 * u ^ 24 * e ^ 2 * (u ^ 6 * s ^ 2) := by ring
      _ ≤ 2 * P ^ 2 * u ^ 24 * e ^ 2 * (2 * u ^ 4 * P) := by gcongr
      _ = 4 * ((P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2)) := by ring
  have k5 : u ^ 10 * s ^ 2 * P * (s ^ 4 * e ^ 4) ≤
      2 * ((P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2)) := by
    calc u ^ 10 * s ^ 2 * P * (s ^ 4 * e ^ 4) = u ^ 10 * s * P * (s ^ 5 * e ^ 4) := by ring
      _ ≤ u ^ 10 * s * P * (P ^ 2 * (e ^ 2 * (2 * u ^ 12))) := by gcongr
      _ = 2 * P ^ 3 * s * e ^ 2 * u ^ 22 := by ring
      _ ≤ 2 * P ^ 3 * s * e ^ 2 * u ^ 25 := by gcongr
      _ = 2 * ((P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2)) := by ring
  have k6 : u ^ 10 * s ^ 2 * P * (e ^ 3 * u ^ 8 * s ^ 2 * P) ≤
      2 * ((P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2)) := by
    calc u ^ 10 * s ^ 2 * P * (e ^ 3 * u ^ 8 * s ^ 2 * P)
        = u ^ 18 * s * s ^ 3 * P ^ 2 * e ^ 3 := by ring
      _ ≤ u ^ 18 * s * P * P ^ 2 * (e ^ 2 * (2 * u ^ 6)) := by gcongr
      _ = 2 * P ^ 3 * s * e ^ 2 * u ^ 24 := by ring
      _ ≤ 2 * P ^ 3 * s * e ^ 2 * u ^ 25 := by gcongr
      _ = 2 * ((P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2)) := by ring
  have hf2 : s ^ 4 * u ^ 8 ≤ u ^ 10 * s ^ 2 * P := by
    calc s ^ 4 * u ^ 8 = s ^ 2 * s ^ 2 * u ^ 8 := by ring
      _ ≤ s ^ 2 * P * u ^ 10 := by gcongr
      _ = _ := by ring
  have hG : 0 ≤ P * u ^ 32 + s ^ 4 * e ^ 4 + e ^ 3 * u ^ 8 * s ^ 2 * P := by positivity
  have hF := mul_le_mul_of_nonneg_right
    (by linarith : P * u ^ 16 + s ^ 4 * u ^ 8 + u ^ 10 * s ^ 2 * P ≤
      P * u ^ 16 + 2 * (u ^ 10 * s ^ 2 * P)) hG
  have a12 : 0 ≤ (P * u ^ 24) * (P * s * u ^ 21) := by positivity
  have a33 : 0 ≤ (e ^ 2 * u ^ 4 * P ^ 2) ^ 2 := by positivity
  have a13 : 0 ≤ (P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2) := by positivity
  have a23 : 0 ≤ (P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2) := by positivity
  have a11 : 0 ≤ (P * u ^ 24) ^ 2 := by positivity
  have a22 : 0 ≤ (P * s * u ^ 21) ^ 2 := by positivity
  have hexp : (P * u ^ 16 + 2 * (u ^ 10 * s ^ 2 * P)) *
      (P * u ^ 32 + s ^ 4 * e ^ 4 + e ^ 3 * u ^ 8 * s ^ 2 * P) =
      (P * u ^ 24) ^ 2 + P * u ^ 16 * (s ^ 4 * e ^ 4) + P * u ^ 16 * (e ^ 3 * u ^ 8 * s ^ 2 * P) +
      2 * (P * s * u ^ 21) ^ 2 + 2 * (u ^ 10 * s ^ 2 * P * (s ^ 4 * e ^ 4)) +
      2 * (u ^ 10 * s ^ 2 * P * (e ^ 3 * u ^ 8 * s ^ 2 * P)) := by ring
  have hsq : (P * u ^ 24 + P * s * u ^ 21 + e ^ 2 * u ^ 4 * P ^ 2) ^ 2 =
      (P * u ^ 24) ^ 2 + (P * s * u ^ 21) ^ 2 + (e ^ 2 * u ^ 4 * P ^ 2) ^ 2 +
      2 * ((P * u ^ 24) * (P * s * u ^ 21)) + 2 * ((P * u ^ 24) * (e ^ 2 * u ^ 4 * P ^ 2)) +
      2 * ((P * s * u ^ 21) * (e ^ 2 * u ^ 4 * P ^ 2)) := by ring
  rw [hexp] at hF
  rw [hsq]
  linarith

lemma rp (x : ℝ) (hx : 0 ≤ x) (q r : ℝ) (k : ℕ) (h : q = r * k) : x ^ q = (x ^ r) ^ k := by
  rw [h, Real.rpow_mul_natCast hx]

lemma rpow_alg (N T w E : ℝ) (hT : 1 ≤ T) (hw : 1 ≤ w) (hE0 : 0 ≤ E)
    (hN : T ^ (3 / 4 : ℝ) ≤ N) (hE : E ≤ 3 * w ^ 3) (hwT : w ≤ 2 * T) :
    (N * w ^ 2 + T * w + w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N) *
      (N * w ^ 4 + T * E + E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * N) ≤
      8 * (N * w ^ 3 + N * T ^ (1 / 4 : ℝ) * w ^ (21 / 8 : ℝ) +
        E ^ (1 / 2 : ℝ) * w ^ (1 / 2 : ℝ) * N ^ 2) ^ 2 := by
  have hw0 : 0 ≤ w := by linarith
  have hT0 : 0 ≤ T := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = w ^ (1 / 8 : ℝ) := ⟨_, rfl⟩
  obtain ⟨s, hs⟩ : ∃ s, s = T ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  obtain ⟨e, he⟩ : ∃ e, e = E ^ (1 / 4 : ℝ) := ⟨_, rfl⟩
  have w8 : w = u ^ 8 := by rw [hu, ← rp w hw0 1 _ _ (by norm_num), Real.rpow_one]
  have w54 : w ^ (5 / 4 : ℝ) = u ^ 10 := by rw [hu]; exact rp w hw0 _ _ _ (by norm_num)
  have w218 : w ^ (21 / 8 : ℝ) = u ^ 21 := by rw [hu]; exact rp w hw0 _ _ _ (by norm_num)
  have w12 : w ^ (1 / 2 : ℝ) = u ^ 4 := by rw [hu]; exact rp w hw0 _ _ _ (by norm_num)
  have T4 : T = s ^ 4 := by rw [hs, ← rp T hT0 1 _ _ (by norm_num), Real.rpow_one]
  have T12 : T ^ (1 / 2 : ℝ) = s ^ 2 := by rw [hs]; exact rp T hT0 _ _ _ (by norm_num)
  have T34 : T ^ (3 / 4 : ℝ) = s ^ 3 := by rw [hs]; exact rp T hT0 _ _ _ (by norm_num)
  have E4 : E = e ^ 4 := by rw [he, ← rp E hE0 1 _ _ (by norm_num), Real.rpow_one]
  have E34 : E ^ (3 / 4 : ℝ) = e ^ 3 := by rw [he]; exact rp E hE0 _ _ _ (by norm_num)
  have E12 : E ^ (1 / 2 : ℝ) = e ^ 2 := by rw [he]; exact rp E hE0 _ _ _ (by norm_num)
  have hu1 : 1 ≤ u := by rw [hu]; exact Real.one_le_rpow hw (by norm_num)
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow hT (by norm_num)
  have he0 : 0 ≤ e := by rw [he]; positivity
  have h1 : e ^ 4 ≤ 3 * u ^ 24 := by
    rw [← E4]; calc E ≤ 3 * w ^ 3 := hE
      _ = 3 * u ^ 24 := by rw [w8]; ring
  have h2 : u ^ 8 ≤ 2 * s ^ 4 := by rw [← w8, ← T4]; exact hwT
  have h3 : s ^ 3 ≤ N := by rw [← T34]; exact hN
  have := poly N s u e hs1 hu1 he0 h3 h1 h2
  rw [w54, w218, w12, T12, E34, E12, ← hs]
  rw [w8, T4, E4]
  convert this using 2 <;> ring

/-! ### Counting in 1-separated sets -/
lemma card_le_three (W : Finset ℝ) (hW : IsSeparated 1 W) (x : ℝ) :
    (W.filter fun t => |x - t| ≤ 1).card ≤ 3 := by
  have h : (W.filter fun t => |x - t| ≤ 1).card ≤ (Finset.Icc (0 : ℤ) 2).card := by
    apply Finset.card_le_card_of_injOn (fun t => ⌊t - x + 1⌋)
    · intro t ht
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht
      have := abs_le.mp ht.2
      simp only [Finset.coe_Icc, Set.mem_Icc]
      constructor
      · exact Int.floor_nonneg.mpr (by linarith)
      · exact Int.floor_le_iff.mpr (by push_cast; linarith)
    · intro t ht t' ht' he
      simp only [Finset.coe_filter, Set.mem_ofPred_eq] at ht ht'
      by_contra hne
      have hs := hW t ht.1 t' ht'.1 hne
      have a1 := Int.floor_le (t - x + 1)
      have a2 := Int.lt_floor_add_one (t - x + 1)
      have b1 := Int.floor_le (t' - x + 1)
      have b2 := Int.lt_floor_add_one (t' - x + 1)
      simp only at he
      rw [he] at a1 a2
      rcases le_abs.mp hs with hs | hs <;> linarith
  simpa using h

lemma energy_le (W : Finset ℝ) (hW : IsSeparated 1 W) : energy W ≤ 3 * W.card ^ 3 := by
  unfold energy
  rw [Finset.card_filter]
  simp_rw [Finset.sum_product]
  calc ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, ∑ t₄ ∈ W,
        (if |t₁ + t₂ - t₃ - t₄| ≤ 1 then 1 else 0)
      ≤ ∑ t₁ ∈ W, ∑ t₂ ∈ W, ∑ t₃ ∈ W, 3 := by
        gcongr with t₁ _ t₂ _ t₃ _
        rw [← Finset.card_filter]
        exact card_le_three W hW (t₁ + t₂ - t₃)
    _ = 3 * W.card ^ 3 := by simp; ring

lemma card_le_of_sep (W : Finset ℝ) (a T : ℝ) (hT : 0 ≤ T) (hW : IsSeparated 1 W)
    (h : ∀ t ∈ W, t ∈ Set.Icc a (a + T)) : (W.card : ℝ) ≤ T + 1 := by
  have hc : W.card ≤ (Finset.range (⌊T⌋₊ + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun t => ⌊t - a⌋₊)
    · intro t ht
      have := h t ht
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.floor_le_floor (by linarith [this.2]))
    · intro t ht t' ht' he
      by_contra hne
      have h1 := hW t ht t' ht' hne
      have a1 := (h t ht).1
      have a2 := (h t' ht').1
      simp only at he
      have b1 := Nat.floor_le (by linarith : 0 ≤ t - a)
      have b2 := Nat.lt_floor_add_one (t - a)
      have b3 := Nat.floor_le (by linarith : 0 ≤ t' - a)
      have b4 := Nat.lt_floor_add_one (t' - a)
      rw [he] at b1 b2
      have : |t - t'| < 1 := by rw [abs_sub_lt_iff]; constructor <;> linarith
      linarith
  rw [Finset.card_range] at hc
  have := Nat.floor_le hT
  have : (W.card : ℝ) ≤ (⌊T⌋₊ : ℝ) + 1 := by exact_mod_cast hc
  linarith

/-! ### The reduction to `X_d` -/
/-- The divisors `d ∈ (N²/T, 2N]`. -/
noncomputable def Ds (N : ℕ) (T : ℝ) : Finset ℕ :=
  (Finset.Icc 1 (2 * N)).filter (fun d => (N : ℝ) ^ 2 / T < d)

/-- `X_d = (N/d, 2N/d] ∩ ℕ`. -/
def Xd (N d : ℕ) : Finset ℕ := Finset.Ioc (N / d) (2 * N / d)

/-- `M_d = ⌊N/d⌋ + 1`. -/
def Md (N d : ℕ) : ℕ := N / d + 1

lemma Xd_sub (N d : ℕ) (hd : 1 ≤ d) : Xd N d ⊆ Finset.Icc (Md N d) (4 * Md N d) := by
  intro m hm
  simp only [Xd, Md, Finset.mem_Ioc, Finset.mem_Icc] at hm ⊢
  refine ⟨hm.1, ?_⟩
  have h1 : m * d ≤ 2 * N := (Nat.le_div_iff_mul_le (by omega)).mp hm.2
  have h2 := Nat.div_add_mod N d
  have h3 := Nat.mod_lt N (show d > 0 by omega)
  have h4 : m * d < 2 * (N / d + 1) * d := by nlinarith
  have := Nat.lt_of_mul_lt_mul_right h4
  omega

lemma Md_le (N d : ℕ) (hd1 : 1 ≤ d) (hd2 : d ≤ 2 * N) : (Md N d : ℝ) ≤ 2 * N / d := by
  have hd : (0 : ℝ) < d := by exact_mod_cast hd1
  unfold Md
  rcases le_or_gt d N with h | h
  · have a1 : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have a2 : (1 : ℝ) ≤ (N : ℝ) / d := by
      rw [le_div_iff₀ hd]; exact_mod_cast (by omega : 1 * d ≤ N)
    push_cast
    calc ((N / d : ℕ) : ℝ) + 1 ≤ (N : ℝ) / d + (N : ℝ) / d := by linarith
      _ = 2 * N / d := by ring
  · rw [Nat.div_eq_of_lt h]
    rw [le_div_iff₀ hd]
    push_cast
    exact_mod_cast (by omega : (0 + 1) * d ≤ 2 * N)

lemma sum_Md_le (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.Icc 1 (2 * N)) :
    ∑ d ∈ S, (Md N d : ℝ) ≤ 2 * N * (1 + Real.log (2 * N)) := by
  have hint : ∑ d ∈ Finset.Icc 1 (2 * N), ((d : ℝ))⁻¹ ≤ 1 + Real.log (2 * N) := by
    have := harmonic_le_one_add_log (2 * N)
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at this
    simpa using this
  calc ∑ d ∈ S, (Md N d : ℝ) ≤ ∑ d ∈ S, 2 * (N : ℝ) / d := by
        apply Finset.sum_le_sum
        intro d hd
        have := Finset.mem_Icc.mp (hS hd)
        exact Md_le N d this.1 this.2
    _ ≤ ∑ d ∈ Finset.Icc 1 (2 * N), 2 * (N : ℝ) / d :=
        Finset.sum_le_sum_of_subset_of_nonneg hS (fun _ _ _ => by positivity)
    _ = 2 * N * ∑ d ∈ Finset.Icc 1 (2 * N), ((d : ℝ))⁻¹ := by
        rw [Finset.mul_sum]; rfl
    _ ≤ 2 * N * (1 + Real.log (2 * N)) := by gcongr

lemma reduce (N : ℕ) (T : ℝ) (W : Finset ℝ) :
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (N : ℝ) ^ 2 / T < (Nat.gcd p.1 p.2 : ℝ)),
      ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3 ≤
    ∑ x ∈ (Ds N T).sigma (fun d => Xd N d ×ˢ Xd N d),
      ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 3 := by
  set Ss := (Ds N T).sigma (fun d => Xd N d ×ˢ Xd N d)
  let ψ : (Σ _ : ℕ, ℕ × ℕ) → ℕ × ℕ := fun x => (x.1 * x.2.1, x.1 * x.2.2)
  let f : ℕ × ℕ → ℝ := fun p => ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3
  have hsub : (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
      (fun p => (N : ℝ) ^ 2 / T < (Nat.gcd p.1 p.2 : ℝ)) ⊆ Ss.image ψ := by
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨h1, h2⟩, h3, h4⟩, h5⟩ := hp
    set g := Nat.gcd p.1 p.2 with hg
    have g1 : 0 < g := Nat.gcd_pos_of_pos_left _ (by omega)
    have g2 : g ≤ p.1 := Nat.gcd_le_left _ (by omega)
    have d1 : g * (p.1 / g) = p.1 := Nat.mul_div_cancel' (Nat.gcd_dvd_left _ _)
    have d2 : g * (p.2 / g) = p.2 := Nat.mul_div_cancel' (Nat.gcd_dvd_right _ _)
    rw [Finset.mem_image]
    refine ⟨⟨g, (p.1 / g, p.2 / g)⟩, ?_, ?_⟩
    · simp only [Ss, Finset.mem_sigma, Ds, Finset.mem_filter, Finset.mem_Icc, Xd,
        Finset.mem_product, Finset.mem_Ioc]
      refine ⟨⟨⟨g1, by omega⟩, h5⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
      · rw [Nat.div_lt_iff_lt_mul g1, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]; exact h1
      · rw [Nat.le_div_iff_mul_le g1, Nat.div_mul_cancel (Nat.gcd_dvd_left _ _)]; exact h2
      · rw [Nat.div_lt_iff_lt_mul g1, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]; exact h3
      · rw [Nat.le_div_iff_mul_le g1, Nat.div_mul_cancel (Nat.gcd_dvd_right _ _)]; exact h4
    · simp only [ψ, d1, d2]
  calc _ ≤ ∑ p ∈ Ss.image ψ, f p :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ ∑ x ∈ Ss, f (ψ x) := Finset.sum_image_le_of_nonneg (fun _ _ => by positivity)
    _ = _ := by
        apply Finset.sum_congr rfl
        intro x hx
        simp only [Ss, Finset.mem_sigma, Ds, Finset.mem_filter, Finset.mem_Icc, Xd,
          Finset.mem_product, Finset.mem_Ioc] at hx
        have a0 : (x.1 : ℝ) ≠ 0 := by exact_mod_cast (by omega : x.1 ≠ 0)
        have a1 : (x.2.1 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hx.2.1.1))
        have a2 : (x.2.2 : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hx.2.2.1))
        simp only [f, ψ]
        push_cast
        rw [Real.log_mul a0 a1, Real.log_mul a0 a2]
        ring_nf

/-! ### Absorbing the constant and the logarithm into `T^ε` -/
lemma absorb (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in Filter.atTop, 12 * (1 + Real.log (2 * T)) * T ^ (ε / 2) ≤ T ^ ε := by
  have hr : 0 < ε / 2 := by linarith
  have h1 := (isLittleO_log_rpow_atTop hr).bound (c := 1 / 24) (by norm_num)
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (24 * (1 + Real.log 2))
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with T hT1 hT2 hT3
  have hT0 : 0 ≤ T := by linarith
  have hp : 0 ≤ T ^ (ε / 2) := Real.rpow_nonneg hT0 _
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hp] at hT1
  have hl2 : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) (by linarith)
  have hc : 12 * (1 + Real.log (2 * T)) ≤ T ^ (ε / 2) := by rw [hl2]; linarith
  have : T ^ ε = T ^ (ε / 2) * T ^ (ε / 2) := by
    rw [← Real.rpow_add' hT0 (by linarith)]; ring_nf
  rw [this]
  exact mul_le_mul_of_nonneg_right hc hp

lemma combine (S S3 A B k L F1 F2 Φ : ℝ) (hS0 : 0 ≤ S) (hred : S ≤ S3) (hCS : S3 ^ 2 ≤ A * B)
    (hA : A ≤ k * (4 * L * F1)) (hB : B ≤ k * (4 * L * F2)) (hA0 : 0 ≤ A) (hk : 0 ≤ k)
    (hB0' : 0 ≤ B) (hL : 0 ≤ L) (hF2 : 0 ≤ F2) (hΦ : 0 ≤ Φ) (halg : F1 * F2 ≤ 8 * Φ ^ 2) :
    S ≤ 12 * L * k * Φ := by
  have hB0 : 0 ≤ k * (4 * L * F2) := by positivity
  have key : S ^ 2 ≤ (12 * L * k * Φ) ^ 2 := by
    calc S ^ 2 ≤ S3 ^ 2 := by gcongr
      _ ≤ A * B := hCS
      _ ≤ (k * (4 * L * F1)) * (k * (4 * L * F2)) := mul_le_mul hA hB hB0' (hA0.trans hA)
      _ = 16 * L ^ 2 * k ^ 2 * (F1 * F2) := by ring
      _ ≤ 16 * L ^ 2 * k ^ 2 * (8 * Φ ^ 2) := by gcongr
      _ ≤ (12 * L * k * Φ) ^ 2 := by
          nlinarith [mul_nonneg (mul_nonneg (sq_nonneg L) (sq_nonneg k)) (sq_nonneg Φ)]
  exact (pow_le_pow_iff_left₀ hS0 (by positivity) (by norm_num)).mp key

/-! ### Lemma 11.9 -/
/-- Lemma 11.9 (large gcd terms), `D = N²/T`. -/
theorem large_gcd : ∀ ε : ℝ, 0 < ε → ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
    T ^ (3 / 4 : ℝ) ≤ N → (N : ℝ) ≤ T →
    ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
    ∑ p ∈ (Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N)).filter
        (fun p => (N : ℝ) ^ 2 / T < (Nat.gcd p.1 p.2 : ℝ)),
      ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3 ≤
      T ^ ε * ((N : ℝ) * (W.card : ℝ) ^ 3 + N * T ^ (1 / 4 : ℝ) * (W.card : ℝ) ^ (21 / 8 : ℝ) +
        (energy W : ℝ) ^ (1 / 2 : ℝ) * (W.card : ℝ) ^ (1 / 2 : ℝ) * (N : ℝ) ^ 2) := by
  intro ε hε
  obtain ⟨T1, h2⟩ := second_moment (ε / 2) (by linarith)
  obtain ⟨T2, h4⟩ := fourth_moment (ε / 2) (by linarith)
  obtain ⟨T3, h3⟩ := Filter.eventually_atTop.mp (absorb ε hε)
  refine ⟨max (max T1 T2) (max T3 4), ?_⟩
  intro T hT N hN34 hNT W a hW hWa
  simp only [max_le_iff] at hT
  obtain ⟨⟨hT1, hT2⟩, hT3, hT4⟩ := hT
  have hT0 : 0 < T := by linarith
  rcases W.eq_empty_or_nonempty with hWe | hWne
  · subst hWe
    have : ∀ τ, Rl (∅ : Finset ℝ) τ = 0 := fun τ => by simp [Rl]
    simp only [this, norm_zero]
    rw [Finset.sum_eq_zero (fun _ _ => by norm_num)]
    positivity
  -- basic facts
  have hw1 : (1 : ℝ) ≤ W.card := by exact_mod_cast hWne.card_pos
  have hwT : (W.card : ℝ) ≤ 2 * T := by
    have := card_le_of_sep W a T hT0.le hW hWa; linarith
  have hE : (energy W : ℝ) ≤ 3 * (W.card : ℝ) ^ 3 := by exact_mod_cast energy_le W hW
  have hE0 : (0 : ℝ) ≤ energy W := by positivity
  have hsq : (2 : ℝ) ≤ T ^ (1 / 2 : ℝ) := by
    have h := rp T hT0.le 1 (1 / 2) 2 (by norm_num)
    rw [Real.rpow_one] at h
    nlinarith [Real.rpow_nonneg hT0.le (1 / 2 : ℝ)]
  have hN2 : (2 : ℝ) ≤ N := by
    have : T ^ (1 / 2 : ℝ) ≤ T ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
    linarith
  have hN0 : (0 : ℝ) < N := by linarith
  set L := 1 + Real.log (2 * (N : ℝ)) with hLdef
  have hL0 : 0 ≤ L := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * N); linarith
  have hLT : L ≤ 1 + Real.log (2 * T) := by
    have := Real.log_le_log (by linarith) (by linarith : 2 * (N : ℝ) ≤ 2 * T); linarith
  have hDs : Ds N T ⊆ Finset.Icc 1 (2 * N) := Finset.filter_subset _ _
  have hMd : ∀ d ∈ Ds N T, (Md N d : ℝ) ≤ 2 * T / N := by
    intro d hd
    simp only [Ds, Finset.mem_filter, Finset.mem_Icc] at hd
    have hD : 0 < (N : ℝ) ^ 2 / T := by positivity
    calc (Md N d : ℝ) ≤ 2 * N / d := Md_le N d hd.1.1 hd.1.2
      _ ≤ 2 * N / ((N : ℝ) ^ 2 / T) :=
          div_le_div_of_nonneg_left (by positivity) hD hd.2.le
      _ = 2 * T / N := by field_simp
  have hMT : ∀ d ∈ Ds N T, (Md N d : ℝ) ≤ T := by
    intro d hd
    refine (hMd d hd).trans ?_
    rw [div_le_iff₀ hN0]; nlinarith
  have hSM := sum_Md_le N (Ds N T) hDs
  have hSM2 : ∑ d ∈ Ds N T, (Md N d : ℝ) ^ 2 ≤ 4 * T * L := by
    calc ∑ d ∈ Ds N T, (Md N d : ℝ) ^ 2 ≤ ∑ d ∈ Ds N T, 2 * T / N * (Md N d : ℝ) := by
          apply Finset.sum_le_sum
          intro d hd
          rw [sq]; exact mul_le_mul_of_nonneg_right (hMd d hd) (by positivity)
      _ = 2 * T / N * ∑ d ∈ Ds N T, (Md N d : ℝ) := by rw [Finset.mul_sum]
      _ ≤ 2 * T / N * (2 * N * L) := by gcongr
      _ = 4 * T * L := by field_simp; ring
  set SM1 := ∑ d ∈ Ds N T, (Md N d : ℝ) with hSM1
  set SMM := ∑ d ∈ Ds N T, (Md N d : ℝ) ^ 2 with hSMM
  set w := (W.card : ℝ) with hw
  set E := (energy W : ℝ) with hEdef
  set Ss := (Ds N T).sigma (fun d => Xd N d ×ˢ Xd N d) with hSs
  have hSM0 : 0 ≤ SM1 := Finset.sum_nonneg (fun _ _ => by positivity)
  have hSM20 : 0 ≤ SMM := Finset.sum_nonneg (fun _ _ => by positivity)
  have hTe : 0 ≤ T ^ (ε / 2) := Real.rpow_nonneg hT0.le _
  have hc1 : 0 ≤ w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) := by positivity
  have hc2 : 0 ≤ E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) := by positivity
  -- second moment, summed over `d`
  have hA : ∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 2 ≤
      T ^ (ε / 2) * (4 * L * (N * w ^ 2 + T * w + w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * N)) := by
    calc ∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 2
        = ∑ d ∈ Ds N T, ∑ m₁ ∈ Xd N d, ∑ m₂ ∈ Xd N d,
            ‖Rl W (Real.log m₁ - Real.log m₂)‖ ^ 2 := by
          rw [hSs, Finset.sum_sigma]
          apply Finset.sum_congr rfl; intro d _; rw [Finset.sum_product]
      _ ≤ ∑ d ∈ Ds N T, T ^ (ε / 2) * (w ^ 2 * (Md N d : ℝ) + w * (Md N d : ℝ) ^ 2 +
            w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * (Md N d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hDs hd)).1
          exact h2 T hT1 (Md N d) (by simp [Md]) (Xd N d) (Xd_sub N d hd1) W a hW hWa
      _ = T ^ (ε / 2) * (w ^ 2 * SM1 + w * SMM + w ^ (5 / 4 : ℝ) * T ^ (1 / 2 : ℝ) * SM1) := by
          rw [← Finset.mul_sum]; congr 1
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hTe
          have := mul_le_mul_of_nonneg_left hSM (sq_nonneg w)
          have := mul_le_mul_of_nonneg_left hSM2 (by linarith : 0 ≤ w)
          have := mul_le_mul_of_nonneg_left hSM hc1
          nlinarith [mul_nonneg (mul_nonneg hN0.le (sq_nonneg w)) hL0,
            mul_nonneg (mul_nonneg hN0.le hc1) hL0, mul_nonneg (mul_nonneg hT0.le hL0) (by linarith : 0 ≤ w)]
  -- fourth moment, summed over `d`
  have hB : ∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 4 ≤
      T ^ (ε / 2) * (4 * L * (N * w ^ 4 + T * E + E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * N)) := by
    calc ∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 4
        = ∑ d ∈ Ds N T, ∑ m₁ ∈ Xd N d, ∑ m₂ ∈ Xd N d,
            ‖Rl W (Real.log m₁ - Real.log m₂)‖ ^ 4 := by
          rw [hSs, Finset.sum_sigma]
          apply Finset.sum_congr rfl; intro d _; rw [Finset.sum_product]
      _ ≤ ∑ d ∈ Ds N T, T ^ (ε / 2) * (w ^ 4 * (Md N d : ℝ) + E * (Md N d : ℝ) ^ 2 +
            E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * (Md N d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          have hd1 : 1 ≤ d := (Finset.mem_Icc.mp (hDs hd)).1
          have := h4 T hT2 (Md N d) (by simp [Md]) (hMT d hd) (Xd N d) (Xd_sub N d hd1) W a hW hWa
          refine this.trans (le_of_eq ?_)
          ring
      _ = T ^ (ε / 2) * (w ^ 4 * SM1 + E * SMM + E ^ (3 / 4 : ℝ) * w * T ^ (1 / 2 : ℝ) * SM1) := by
          rw [← Finset.mul_sum]; congr 1
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
          rfl
      _ ≤ _ := by
          apply mul_le_mul_of_nonneg_left _ hTe
          have := mul_le_mul_of_nonneg_left hSM (by positivity : 0 ≤ w ^ 4)
          have := mul_le_mul_of_nonneg_left hSM2 hE0
          have := mul_le_mul_of_nonneg_left hSM hc2
          nlinarith [mul_nonneg (mul_nonneg hN0.le (by positivity : 0 ≤ w ^ 4)) hL0,
            mul_nonneg (mul_nonneg hN0.le hc2) hL0, mul_nonneg (mul_nonneg hT0.le hL0) hE0]
  -- Cauchy–Schwarz
  have hCS : (∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 3) ^ 2 ≤
      (∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 2) *
        (∑ x ∈ Ss, ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 4) := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Ss
      (fun x => ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖)
      (fun x => ‖Rl W (Real.log x.2.1 - Real.log x.2.2)‖ ^ 2)
    simp only [← pow_succ', ← pow_mul] at this
    exact this
  have halg := rpow_alg N T w E (by linarith) hw1 hE0 hN34 hE hwT
  have hS1 := combine _ _ _ _ (T ^ (ε / 2)) L _ _ _ (Finset.sum_nonneg (fun _ _ => by positivity))
    (reduce N T W) hCS hA hB (Finset.sum_nonneg (fun _ _ => by positivity)) hTe
    (Finset.sum_nonneg (fun _ _ => by positivity)) hL0
    (by positivity) (by positivity) halg
  refine hS1.trans ?_
  have hc : 12 * L * T ^ (ε / 2) ≤ T ^ ε :=
    calc 12 * L * T ^ (ε / 2) ≤ 12 * (1 + Real.log (2 * T)) * T ^ (ε / 2) := by gcongr
      _ ≤ T ^ ε := h3 T hT3
  exact mul_le_mul_of_nonneg_right hc (by positivity)

end GuthMaynard.E111.PartE
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias large_gcd := GuthMaynard.E111.PartE.large_gcd

end GuthMaynard.E111
end

section
namespace GuthMaynard.E111.PartF
open GuthMaynard GuthMaynard.E111 Complex
/-- `r² ≤ a + b r` implies `r² ≤ 2a + b²`. -/
lemma quad (r a b : ℝ) (h : r ^ 2 ≤ a + b * r) : r ^ 2 ≤ 2 * a + b ^ 2 := by
  nlinarith [sq_nonneg (r - b)]

/-- The real-number assembly. -/
lemma alg (E w N s x L c τ S1 S2 y1 y4 : ℝ) (hE0 : 0 ≤ E) (hw0 : 0 ≤ w) (hN : 0 ≤ N)
    (hx : 0 ≤ x) (hL0 : 0 ≤ L) (hc0 : 0 ≤ c) (hτ : 1 ≤ τ) (hs : 0 ≤ s)
    (hk : L * x * c ≤ τ * x)
    (hE : E ≤ L * x * (S1 + S2))
    (hS1 : S1 ≤ c * (2 * N ^ 2) * w ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ))
    (hS2 : S2 ≤ c * (N * w ^ 3 + N * s * w ^ (21 / 8 : ℝ) +
      E ^ (1 / 2 : ℝ) * w ^ (1 / 2 : ℝ) * N ^ 2))
    (hy1 : y1 = x * N) (hy4 : y4 = x ^ 2 * N ^ 4) :
    E ≤ 20 * τ ^ 2 * (w * y4 + w ^ (21 / 8 : ℝ) * s * y1 + w ^ 3 * y1) := by
  set k := L * x * c with hkdef
  have hk0 : 0 ≤ k := by positivity
  set r := E ^ (1 / 2 : ℝ) with hr
  set q := w ^ (1 / 2 : ℝ) with hq
  have hr2 : r ^ 2 = E := by
    rw [hr, ← Real.sqrt_eq_rpow, Real.sq_sqrt hE0]
  have hq2 : q ^ 2 = w := by
    rw [hq, ← Real.sqrt_eq_rpow, Real.sq_sqrt hw0]
  have hr0 : 0 ≤ r := Real.rpow_nonneg hE0 _
  have hq0 : 0 ≤ q := Real.rpow_nonneg hw0 _
  set A0 := N * w ^ 3 + N * s * w ^ (21 / 8 : ℝ) with hA0
  have hA00 : 0 ≤ A0 := by positivity
  have h1 : r ^ 2 ≤ k * A0 + (3 * k * N ^ 2 * q) * r := by
    rw [hr2]
    have hLx : 0 ≤ L * x := by positivity
    calc E ≤ L * x * (S1 + S2) := hE
      _ ≤ L * x * (c * (2 * N ^ 2) * q * r + c * (A0 + r * q * N ^ 2)) := by gcongr
      _ = k * A0 + (3 * k * N ^ 2 * q) * r := by rw [hkdef]; ring
  have h2 := quad r _ _ h1
  rw [hr2] at h2
  have hτx : 0 ≤ τ * x := by positivity
  have h3 : 2 * (k * A0) ≤ 2 * (τ ^ 2 * x * A0) := by
    have : k * A0 ≤ τ * x * A0 := by gcongr
    have : τ * x * A0 ≤ τ ^ 2 * x * A0 := by
      have : τ ≤ τ ^ 2 := by nlinarith
      gcongr
    linarith
  have h4 : (3 * k * N ^ 2 * q) ^ 2 ≤ 9 * (τ * x) ^ 2 * N ^ 4 * w := by
    rw [← hq2]
    have : k ^ 2 ≤ (τ * x) ^ 2 := by gcongr
    have e : (3 * k * N ^ 2 * q) ^ 2 = 9 * k ^ 2 * N ^ 4 * q ^ 2 := by ring
    rw [e]; gcongr
  rw [hy1, hy4]
  have e2 : 2 * (τ ^ 2 * x * A0) + 9 * (τ * x) ^ 2 * N ^ 4 * w =
      τ ^ 2 * (9 * (w * (x ^ 2 * N ^ 4)) + 2 * (w ^ (21 / 8 : ℝ) * s * (x * N)) +
        2 * (w ^ 3 * (x * N))) := by rw [hA0]; ring
  have hp1 : 0 ≤ τ ^ 2 * (w * (x ^ 2 * N ^ 4)) := by positivity
  have hp2 : 0 ≤ τ ^ 2 * (w ^ (21 / 8 : ℝ) * s * (x * N)) := by positivity
  have hp3 : 0 ≤ τ ^ 2 * (w ^ 3 * (x * N)) := by positivity
  nlinarith

lemma absorb (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in Filter.atTop, 20 * (1 + Real.log (2 * T)) ^ 2 ≤ T ^ (δ / 4) := by
  have hr : 0 < δ / 8 := by linarith
  have h1 := (isLittleO_log_rpow_atTop hr).bound (c := 1 / 10) (by norm_num)
  have h2 := (tendsto_rpow_atTop hr).eventually_ge_atTop (10 * (1 + Real.log 2))
  filter_upwards [h1, h2, Filter.eventually_ge_atTop 1] with T hT1 hT2 hT3
  have hT0 : 0 ≤ T := by linarith
  have hp : 0 ≤ T ^ (δ / 8) := Real.rpow_nonneg hT0 _
  have hlog : 0 ≤ Real.log T := Real.log_nonneg hT3
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog, abs_of_nonneg hp] at hT1
  have hl2 : Real.log (2 * T) = Real.log 2 + Real.log T :=
    Real.log_mul (by norm_num) (by linarith)
  have hl20 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hc : 1 + Real.log (2 * T) ≤ T ^ (δ / 8) / 5 := by rw [hl2]; linarith
  have h0 : 0 ≤ 1 + Real.log (2 * T) := by rw [hl2]; linarith
  have : T ^ (δ / 4) = T ^ (δ / 8) * T ^ (δ / 8) := by
    rw [← Real.rpow_add' hT0 (by linarith)]; ring_nf
  rw [this]
  have := mul_le_mul hc hc h0 (by positivity)
  nlinarith

/-- Proposition 11.1, as published. -/
theorem energy_le_of_large_values_of_three_quarters_dev :
    ∀ δ : ℝ, 0 < δ → ∃ C T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T → ∀ (N : ℕ),
      (N : ℝ) ∈ Set.Icc (T ^ (3 / 4 : ℝ)) T → ∀ (σ : ℝ) (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (W : Finset ℝ) (a : ℝ), IsSeparated 1 W → (∀ t ∈ W, t ∈ Set.Icc a (a + T)) →
      (∀ t ∈ W, (N : ℝ) ^ σ ≤
        ‖∑ n ∈ Finset.Ioc N (2 * N), b n * (n : ℂ) ^ ((t : ℂ) * Complex.I)‖) →
      (energy W : ℝ) ≤ C * T ^ δ * ((W.card : ℝ) * (N : ℝ) ^ (4 - 4 * σ) +
        (W.card : ℝ) ^ (21 / 8 : ℝ) * T ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 - 2 * σ) +
        (W.card : ℝ) ^ 3 * (N : ℝ) ^ (1 - 2 * σ)) := by
  intro δ hδ
  have hε : 0 < δ / 4 := by linarith
  obtain ⟨T₁, hT₁⟩ := small_gcd (δ / 4) hε
  obtain ⟨T₂, hT₂⟩ := large_gcd (δ / 4) hε
  obtain ⟨T₃, hT₃⟩ := Filter.eventually_atTop.mp (absorb δ hδ)
  refine ⟨20, max (max T₁ T₂) (max T₃ 1), ?_⟩
  intro T hT N hNT σ b hb W a hW hWa hD
  have hT1 : T₁ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hT
  have hT2 : T₂ ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hT
  have hT3 : T₃ ≤ T := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hT4 : 1 ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  have hT0 : 0 < T := by linarith
  have hN1r : (1 : ℝ) ≤ N := le_trans (Real.one_le_rpow hT4 (by norm_num)) hNT.1
  have hN1 : 1 ≤ N := by exact_mod_cast hN1r
  have hN0 : (0 : ℝ) < N := by linarith
  -- Lemma 11.4
  have hE := energy_le_third_moment N hN1 b hb σ W hW hD
  have hprod : ∑ n₁ ∈ Finset.Ioc N (2 * N), ∑ n₂ ∈ Finset.Ioc N (2 * N),
        ‖Rl W (Real.log n₁ - Real.log n₂)‖ ^ 3 =
      ∑ p ∈ Finset.Ioc N (2 * N) ×ˢ Finset.Ioc N (2 * N),
        ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3 :=
    (Finset.sum_product _ _ (fun p : ℕ × ℕ => ‖Rl W (Real.log p.1 - Real.log p.2)‖ ^ 3)).symm
  rw [hprod, ← Finset.sum_filter_add_sum_filter_not _
      (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2 : ℝ) ≤ (N : ℝ) ^ 2 / T)] at hE
  simp only [not_le] at hE
  have hS1 := hT₁ T hT1 N hN1 hNT.2 ((N : ℝ) ^ 2 / T) (by positivity) W a hW hWa
  have hS2 := hT₂ T hT2 N hNT.1 hNT.2 W a hW hWa
  rw [div_mul_cancel₀ _ hT0.ne', show (N : ℝ) ^ 2 + (N : ℝ) ^ 2 = 2 * (N : ℝ) ^ 2 by ring]
    at hS1
  -- the logarithmic loss
  set L := 20 * (1 + Real.log (2 * N)) ^ 2 with hL
  have hlogN : Real.log (2 * N) ≤ Real.log (2 * T) :=
    Real.log_le_log (by positivity) (by linarith [hNT.2])
  have hlog0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hLT : L ≤ T ^ (δ / 4) := by
    refine le_trans ?_ (hT₃ T hT3)
    rw [hL]; gcongr
  set x := (N : ℝ) ^ (-2 * σ) with hx
  have hx0 : 0 ≤ x := by positivity
  set τ := T ^ (δ / 2) with hτ
  have hτ1 : 1 ≤ τ := Real.one_le_rpow hT4 (by linarith)
  have hτ2 : T ^ δ = τ ^ 2 := by
    rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hT0.le]; norm_num
  have hTe : T ^ (δ / 4) * T ^ (δ / 4) = τ := by
    rw [hτ, ← Real.rpow_add hT0]; ring_nf
  have hpe : 0 ≤ T ^ (δ / 4) := by positivity
  have hk : L * x * T ^ (δ / 4) ≤ τ * x := by
    rw [← hTe]
    have : L * T ^ (δ / 4) ≤ T ^ (δ / 4) * T ^ (δ / 4) := by gcongr
    nlinarith
  have hL0 : 0 ≤ L := by positivity
  have hy1 : (N : ℝ) ^ (1 - 2 * σ) = x * N := by
    rw [hx, show 1 - 2 * σ = -2 * σ + 1 by ring, Real.rpow_add hN0, Real.rpow_one]
  have hy4 : (N : ℝ) ^ (4 - 4 * σ) = x ^ 2 * (N : ℝ) ^ 4 := by
    rw [hx, show 4 - 4 * σ = (-2 * σ) * 2 + 4 by ring, Real.rpow_add hN0,
      Real.rpow_mul hN0.le]
    norm_cast
  have key := alg (energy W : ℝ) (W.card : ℝ) N (T ^ (1 / 4 : ℝ)) x L (T ^ (δ / 4)) τ _ _
    ((N : ℝ) ^ (1 - 2 * σ)) ((N : ℝ) ^ (4 - 4 * σ)) (by positivity) (by positivity)
    hN0.le hx0 hL0 hpe hτ1 (by positivity) hk hE hS1 (by linarith [hS2]) hy1 hy4
  rw [hτ2]
  linarith [key]

end GuthMaynard.E111.PartF
end

section
namespace GuthMaynard.E111
open GuthMaynard Complex
alias energy_le_of_large_values_of_three_quarters_dev := GuthMaynard.E111.PartF.energy_le_of_large_values_of_three_quarters_dev

end GuthMaynard.E111
end


theorem solution : type_of% @GuthMaynard.E111.energy_le_of_large_values_of_three_quarters_dev := @GuthMaynard.E111.energy_le_of_large_values_of_three_quarters_dev
