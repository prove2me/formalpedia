-- Prove2me | solution 1 for OAI.StandardMapEntropy.exists_critical_scale_sequence_q3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T04:59:49.641826+00:00
-- url     : https://prove2.me/submissions/92596d6d-6d95-45f7-831d-71fd00cf3c2b

import Mathlib
import Definitions.Def_StandardMapLyapunov
import Definitions.Def_OAIQ3St000

section
-- module Solutions.OAIQ3_Std.StandardMap_LocalScarcity
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace StandardMapEntropy

theorem measurePreserving_standardMap (k : ℝ) : MeasurePreserving (standardMap k) area area := by
  unfold area
  have hkick : MeasurePreserving
      (fun z : Torus => (z.1, z.2 + kick k z.1))
        ((volume : Measure Circle).prod volume) (volume.prod volume) := by
    refine (MeasurePreserving.id (volume : Measure Circle)).skew_product
      (g := fun x y : Circle => y + kick k x) ?_ ?_
    · exact measurable_snd.add ((continuous_kick k).measurable.comp measurable_fst)
    · exact Filter.Eventually.of_forall (fun x => map_add_right_eq_self volume (kick k x))
  convert (measurePreserving_add_prod (volume : Measure Circle) volume).comp hkick using 1
  funext z
  simp only [Function.comp_apply, standardMap, kick]
  congr 1
  abel

lemma recurrenceCoordinates_involutive : Function.Involutive recurrenceCoordinates := by
  intro z
  apply Prod.ext <;> simp [recurrenceCoordinates]

lemma standardMap_conjugacy (k : ℝ) (z : Torus) :
    recurrenceCoordinates (standardMap k z) =
      recurrenceMap k (recurrenceCoordinates z) := by
  apply Prod.ext <;> simp only [recurrenceCoordinates, recurrenceMap, standardMap, kick, two_smul]
  · abel
  · abel

lemma hasDerivAt_phi (k x : ℝ) : HasDerivAt (phi k) (potential k x) x := by
  have hs : HasDerivAt (fun y : ℝ => Real.sin (2 * Real.pi * y))
      (Real.cos (2 * Real.pi * x) * (2 * Real.pi)) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * Real.pi)).sin
  have hl : HasDerivAt (fun y : ℝ => 2 * y) 2 x := by
    simpa using (hasDerivAt_id x).const_mul 2
  convert! hl.add (hs.const_mul k) using 1
  unfold potential
  ring

lemma linearSolution_step (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b (n + 2) =
      v (n + 1) * linearSolution v a b (n + 1) - linearSolution v a b n := rfl

lemma linearSolution_decomposition (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b n = a * sSolution v n + b * tSolution v n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [sSolution, tSolution]
  | one => simp [sSolution, tSolution]
  | more n h₀ h₁ =>
    rw [linearSolution_step, h₀, h₁]
    dsimp only [sSolution, tSolution] at *
    rw [linearSolution_step, linearSolution_step]
    ring

theorem solution_wronskian (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    linearSolution v a b n * tSolution v (n + 1) -
      linearSolution v a b (n + 1) * tSolution v n = a := by
  induction n with
  | zero => simp [tSolution]
  | succ n ih =>
    change linearSolution v a b (n + 1) * tSolution v (n + 2) -
      linearSolution v a b (n + 2) * tSolution v (n + 1) = a
    simp only [tSolution, linearSolution_step] at *
    nlinarith only [ih]

lemma boundaryValue_vanishes (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0) :
    linearSolution v 1 (boundaryValue v j) j = 0 := by
  rw [linearSolution_decomposition]
  simp [boundaryValue, hj]

lemma boundaryValue_increment (v : ℕ → ℝ) (j : ℕ)
    (hj : tSolution v j ≠ 0) (hj₁ : tSolution v (j + 1) ≠ 0) :
    boundaryValue v (j + 1) - boundaryValue v j =
      1 / (tSolution v j * tSolution v (j + 1)) := by
  have hw := solution_wronskian v 1 0 j
  change sSolution v j * tSolution v (j + 1) -
    sSolution v (j + 1) * tSolution v j = 1 at hw
  unfold boundaryValue
  field_simp
  nlinarith only [hw]

lemma initial_from_boundary (v : ℕ → ℝ) (j : ℕ)
    (hj : tSolution v j ≠ 0) (b : ℝ) :
    b = boundaryValue v j + linearSolution v 1 b j / tSolution v j := by
  rw [linearSolution_decomposition]
  unfold boundaryValue
  field_simp
  ring

theorem boundary_expansion_exact (v : ℕ → ℝ) (j : ℕ)
    (hj : tSolution v j ≠ 0) (hj₁ : tSolution v (j + 1) ≠ 0) (b : ℝ) :
    b = boundaryValue v j + 1 / (tSolution v j * tSolution v (j + 1)) +
      linearSolution v 1 b (j + 1) / tSolution v (j + 1) := by
  rw [← boundaryValue_increment v j hj hj₁]
  simpa only [add_sub_cancel] using initial_from_boundary v (j + 1) hj₁ b

lemma liftedOrbit_step (k q₀ q₁ : ℝ) (n : ℕ) :
    liftedOrbit k q₀ q₁ (n + 2) =
      phi k (liftedOrbit k q₀ q₁ (n + 1)) - liftedOrbit k q₀ q₁ n := rfl

theorem hasDerivAt_liftedOrbit (k q₀ θ : ℝ) (n : ℕ) :
    HasDerivAt (fun x : ℝ => liftedOrbit k q₀ x n)
      (tSolution (orbitCoefficient k q₀ θ) n) θ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [tSolution] using hasDerivAt_const θ q₀
  | one =>
    convert! hasDerivAt_id θ using 1
  | more n h₀ h₁ =>
    have h := ((hasDerivAt_phi k (liftedOrbit k q₀ θ (n + 1))).comp θ h₁).sub h₀
    convert! h using 1

lemma continuous_liftedOrbit (k q₀ : ℝ) (n : ℕ) :
    Continuous (fun x : ℝ => liftedOrbit k q₀ x n) := by
  exact continuous_iff_continuousAt.mpr (fun θ => (hasDerivAt_liftedOrbit k q₀ θ n).continuousAt)

lemma dirichletSolution_boundary (v : ℕ → ℝ) (j : ℕ) (hj : tSolution v j ≠ 0) :
    dirichletSolution v j j = 0 := boundaryValue_vanishes v j hj

lemma dirichletSolution_step (v : ℕ → ℝ) (j n : ℕ) :
    dirichletSolution v j (n + 2) =
      v (n + 1) * dirichletSolution v j (n + 1) - dirichletSolution v j n := rfl

lemma dirichletSolution_right (v : ℕ → ℝ) (n : ℕ) (hn : tSolution v (n + 1) ≠ 0) :
    dirichletSolution v (n + 1) n = 1 / tSolution v (n + 1) := by
  have h := solution_wronskian v 1 (boundaryValue v (n + 1)) n
  change dirichletSolution v (n + 1) n * tSolution v (n + 1) -
    dirichletSolution v (n + 1) (n + 1) * tSolution v n = 1 at h
  rw [dirichletSolution_boundary v _ hn, zero_mul, sub_zero] at h
  exact (eq_div_iff hn).mpr h

lemma greenKernel_symm (v : ℕ → ℝ) (j a b : ℕ) :
    greenKernel v j a b = greenKernel v j b a := by
  simp only [greenKernel, min_comm, max_comm]

lemma greenKernel_zero (v : ℕ → ℝ) (j b : ℕ) : greenKernel v j 0 b = 0 := by
  simp [greenKernel, tSolution]

lemma greenKernel_boundary (v : ℕ → ℝ) (j b : ℕ)
    (hj : tSolution v j ≠ 0) (hb : b ≤ j) : greenKernel v j j b = 0 := by
  simp only [greenKernel, max_eq_left hb, dirichletSolution_boundary v j hj, mul_zero]

theorem greenKernel_jump (v : ℕ → ℝ) (j a b : ℕ) :
    v (a + 1) * greenKernel v j (a + 1) b -
      greenKernel v j a b - greenKernel v j (a + 2) b =
      if a + 1 = b then 1 else 0 := by
  rcases lt_trichotomy (a + 1) b with hab | hab | hab
  · have ha : a ≤ b := by omega
    have ha₁ : a + 1 ≤ b := by omega
    have ha₂ : a + 2 ≤ b := by omega
    simp only [greenKernel, min_eq_left ha, max_eq_right ha,
      min_eq_left ha₁, max_eq_right ha₁, min_eq_left ha₂, max_eq_right ha₂,
      ite_eq_right (ne_of_lt hab)]
    change v (a + 1) * (tSolution v (a + 1) * dirichletSolution v j b) -
      tSolution v a * dirichletSolution v j b -
      (v (a + 1) * tSolution v (a + 1) - tSolution v a) * dirichletSolution v j b = 0
    ring
  · subst b
    rw [ite_eq_left rfl]
    have ha : a ≤ a + 1 := by omega
    have ha₂ : a + 1 ≤ a + 2 := by omega
    simp only [greenKernel, min_self, max_self, min_eq_left ha, max_eq_right ha,
      min_eq_right ha₂, max_eq_left ha₂]
    have hw := solution_wronskian v 1 (boundaryValue v j) (a + 1)
    change dirichletSolution v j (a + 1) *
      (v (a + 1) * tSolution v (a + 1) - tSolution v a) -
      dirichletSolution v j (a + 2) * tSolution v (a + 1) = 1 at hw
    nlinarith only [hw]
  · have ha : b ≤ a := by omega
    have ha₁ : b ≤ a + 1 := by omega
    have ha₂ : b ≤ a + 2 := by omega
    simp only [greenKernel, min_eq_right ha, max_eq_left ha,
      min_eq_right ha₁, max_eq_left ha₁, min_eq_right ha₂, max_eq_left ha₂,
      ite_eq_right (ne_of_gt hab), dirichletSolution_step]
    ring

lemma quadratic_alternating_four (A B C β c x d : ℝ)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (h₀ : c * (A * x ^ 2 + B * x + C) + 4 * β = 0)
    (h₁ : -c * (A * (x + d) ^ 2 + B * (x + d) + C) + 4 * β = 0)
    (h₂ : c * (A * (x + 2 * d) ^ 2 + B * (x + 2 * d) + C) + 4 * β = 0)
    (h₃ : -c * (A * (x + 3 * d) ^ 2 + B * (x + 3 * d) + C) + 4 * β = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ β = 0 := by
  have hβ : β = 0 := by
    linear_combination (h₀ + 3 * h₁ + 3 * h₂ + h₃) / 32
  have hp₀ : A * x ^ 2 + B * x + C = 0 := by
    simpa only [hβ, mul_zero, add_zero, mul_eq_zero, hc, false_or] using h₀
  have hp₁ : A * (x + d) ^ 2 + B * (x + d) + C = 0 := by
    simpa only [hβ, mul_zero, add_zero, mul_eq_zero, neg_ne_zero.mpr hc, false_or] using h₁
  have hp₂ : A * (x + 2 * d) ^ 2 + B * (x + 2 * d) + C = 0 := by
    simpa only [hβ, mul_zero, add_zero, mul_eq_zero, hc, false_or] using h₂
  have hAd : A * d ^ 2 = 0 := by
    linear_combination (hp₀ - 2 * hp₁ + hp₂) / 2
  have hA : A = 0 := (mul_eq_zero.mp hAd).resolve_right (pow_ne_zero _ hd)
  have hBd : B * d = 0 := by
    rw [hA] at hp₀ hp₁
    linear_combination hp₁ - hp₀
  have hB : B = 0 := (mul_eq_zero.mp hBd).resolve_right hd
  have hC : C = 0 := by simpa only [hA, hB, zero_mul, zero_add] using hp₀
  exact ⟨hA, hB, hC, hβ⟩

lemma affine_cosine_zeros (z b : ℝ) (hb : b ≠ 0) (n : ℕ) :
    Real.cos (2 * Real.pi * (z + b * ((1 / 4 - z) / b + (n : ℝ) * (1 / (2 * b))))) = 0 ∧
    Real.sin (2 * Real.pi * (z + b * ((1 / 4 - z) / b + (n : ℝ) * (1 / (2 * b))))) =
      (-1 : ℝ) ^ n := by
  have hangle : 2 * Real.pi * (z + b * ((1 / 4 - z) / b + (n : ℝ) * (1 / (2 * b)))) =
      Real.pi / 2 + (n : ℝ) * Real.pi := by
    field_simp
    ring
  rw [hangle, Real.cos_add_nat_mul_pi, Real.sin_add_nat_mul_pi]
  simp

theorem alternating_cosine_obstruction (A B C β z b : ℝ) (hb : b ≠ 0)
    (h : ∀ x : ℝ, Real.cos (2 * Real.pi * (z + b * x)) = 0 →
      2 * Real.pi * (A * x ^ 2 + B * x + C) *
        Real.sin (2 * Real.pi * (z + b * x)) + 4 * β = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ β = 0 := by
  let x : ℝ := (1 / 4 - z) / b
  let d : ℝ := 1 / (2 * b)
  have hnodes (n : ℕ) :
      2 * Real.pi * (A * (x + (n : ℝ) * d) ^ 2 + B * (x + (n : ℝ) * d) + C) *
        (-1 : ℝ) ^ n + 4 * β = 0 := by
    have hz := affine_cosine_zeros z b hb n
    have hn := h (x + (n : ℝ) * d) hz.1
    rw [hz.2] at hn
    exact hn
  have h₀ := hnodes 0
  have h₁ := hnodes 1
  have h₂ := hnodes 2
  have h₃ := hnodes 3
  norm_num at h₀ h₁ h₂ h₃
  apply quadratic_alternating_four A B C β (2 * Real.pi) x d
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
      (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) hb))
  · exact h₀
  · nlinarith only [h₁]
  · exact h₂
  · nlinarith only [h₃]

lemma drawdown_nonneg (z : ℕ → ℝ) (c : ℝ) (n : ℕ) : 0 ≤ drawdown z c n := by
  cases n with
  | zero => rfl
  | succ n => exact le_max_left _ _

lemma drawdown_ge_drop (z : ℕ → ℝ) (c : ℝ) (j l : ℕ) (hl : l ≤ j) :
    z l - z j + c * ((j : ℝ) - (l : ℝ)) ≤ drawdown z c j := by
  induction j with
  | zero =>
    have : l = 0 := by omega
    simp [this, drawdown]
  | succ j ih =>
    by_cases hlj : l = j + 1
    · simpa [hlj] using drawdown_nonneg z c (j + 1)
    · have hl' : l ≤ j := by omega
      have hi := ih hl'
      have hm : drawdown z c j + c + z j - z (j + 1) ≤ drawdown z c (j + 1) :=
        le_max_right _ _
      push_cast
      nlinarith only [hi, hm]

lemma drawdown_pos_of_bad (z : ℕ → ℝ) (c : ℝ) (j : ℕ)
    (h : ∃ l < j, z j - z l < c * ((j : ℝ) - (l : ℝ))) :
    0 < drawdown z c j := by
  obtain ⟨l, hlj, hdrop⟩ := h
  have hg := drawdown_ge_drop z c j l hlj.le
  linarith

lemma drawdown_step_account (z : ℕ → ℝ) (c : ℝ) (n : ℕ)
    (hz : z (n + 1) - z n ≤ 1) :
    (if 0 < drawdown z c (n + 1) then 1 - c else 0) ≤
      1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1) := by
  split_ifs with hp
  · have he : drawdown z c (n + 1) = drawdown z c n + c + z n - z (n + 1) := by
      change max 0 (drawdown z c n + c + z n - z (n + 1)) = _
      apply max_eq_right
      change 0 < max 0 (drawdown z c n + c + z n - z (n + 1)) at hp
      rcases lt_max_iff.mp hp with hp | hp
      · exact False.elim ((lt_irrefl _) hp)
      · exact hp.le
    rw [he]
    linarith
  · have he : drawdown z c (n + 1) = 0 :=
      le_antisymm (not_lt.mp hp) (drawdown_nonneg z c _)
    rw [he]
    linarith [drawdown_nonneg z c n]

lemma drawdown_account_sum (z : ℕ → ℝ) (c : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      (1 - (z (n + 1) - z n) + drawdown z c n - drawdown z c (n + 1))) =
      (N : ℝ) - (z N - z 0) - drawdown z c N := by
  induction N with
  | zero => simp [drawdown]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

lemma drawdown_count (z : ℕ → ℝ) (c : ℝ) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) ≤
      (N : ℝ) - (z N - z 0) := by
  classical
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun n hn =>
    drawdown_step_account z c n (hz n (Finset.mem_range.mp hn)))
  rw [drawdown_account_sum] at hsum
  have hc :
      (((Finset.range N).filter (fun n => 0 < drawdown z c (n + 1))).card : ℝ) * (1 - c) =
      ∑ n ∈ Finset.range N, if 0 < drawdown z c (n + 1) then 1 - c else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← hc] at hsum
  linarith [drawdown_nonneg z c N]

theorem shortfall_count (z : ℕ → ℝ) (c : ℝ) (hc : c < 1) (N : ℕ)
    (hz : ∀ n < N, z (n + 1) - z n ≤ 1) :
    (((Finset.range N).filter fun n =>
      ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      ((N : ℝ) - (z N - z 0)) / (1 - c) := by
  classical
  have hsub : ((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))) ⊆
      ((Finset.range N).filter fun n => 0 < drawdown z c (n + 1)) := by
    intro n hn
    obtain ⟨hnN, hbad⟩ := Finset.mem_filter.mp hn
    exact Finset.mem_filter.mpr ⟨hnN, drawdown_pos_of_bad z c (n + 1) hbad⟩
  have hcard :
      (((Finset.range N).filter fun n =>
        ∃ l < n + 1, z (n + 1) - z l < c * ((n + 1 : ℕ) - (l : ℝ))).card : ℝ) ≤
      (((Finset.range N).filter fun n => 0 < drawdown z c (n + 1))).card :=
    Nat.cast_le.mpr (Finset.card_le_card hsub)
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  exact (mul_le_mul_of_nonneg_right hcard (sub_nonneg.mpr hc.le)).trans
    (drawdown_count z c N hz)

lemma goodExponent_pos : 0 < goodExponent := by norm_num [goodExponent]
lemma goodExponent_lt_one : goodExponent < 1 := by norm_num [goodExponent]

lemma pairMagnitude_nonneg (u : ℕ → ℝ) (j : ℕ) : 0 ≤ pairMagnitude u j :=
  (abs_nonneg _).trans (le_max_left _ _)

lemma pairMagnitude_zero (u : ℕ → ℝ) (j : ℕ) (h : pairMagnitude u j = 0) :
    u j = 0 ∧ u (j - 1) = 0 := by
  constructor
  · apply abs_nonpos_iff.mp
    exact (le_max_left _ _).trans_eq h
  · apply abs_nonpos_iff.mp
    exact (le_max_right _ _).trans_eq h

lemma pairMagnitude_normalized_pos (v : ℕ → ℝ) (b : ℝ) (j : ℕ) (hj : 1 ≤ j) :
    0 < pairMagnitude (linearSolution v 1 b) j := by
  by_contra h
  have hz := pairMagnitude_zero _ j
    (le_antisymm (not_lt.mp h) (pairMagnitude_nonneg _ _))
  have hn : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hw := solution_wronskian v 1 b (j - 1)
  rw [hn, hz.1, hz.2] at hw
  norm_num at hw

lemma pairMagnitude_t_pos (v : ℕ → ℝ) (j : ℕ) (hj : 1 ≤ j) :
    0 < pairMagnitude (tSolution v) j := by
  by_contra h
  have hz := pairMagnitude_zero _ j
    (le_antisymm (not_lt.mp h) (pairMagnitude_nonneg _ _))
  have hn : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hw := solution_wronskian v 1 0 (j - 1)
  rw [hn, hz.1, hz.2] at hw
  norm_num at hw

lemma logb_growth (M A B a : ℝ) (hM : 1 < M) (hA : 0 < A) (hB : 0 < B)
    (h : a ≤ Real.logb M B - Real.logb M A) : M ^ a * A ≤ B := by
  have hd : 0 < B / A := div_pos hB hA
  rw [← Real.logb_div (ne_of_gt hB) (ne_of_gt hA)] at h
  exact (le_div_iff₀ hA).mp ((Real.le_logb_iff_rpow_le hM hd).mp h)

lemma pairMagnitude_eq_abs_of_growth (M : ℝ) (u : ℕ → ℝ) (j : ℕ)
    (hM : 1 < M) (hprev : 0 < pairMagnitude u (j - 1))
    (hj : 0 < pairMagnitude u j)
    (hg : pairLog M u (j - 1) < pairLog M u j) : pairMagnitude u j = |u j| := by
  have hi : pairMagnitude u (j - 1) < pairMagnitude u j :=
    (Real.logb_lt_logb_iff hM hprev hj).mp hg
  have ha : |u (j - 1)| ≤ pairMagnitude u (j - 1) := le_max_left _ _
  have hs : |u (j - 1)| < pairMagnitude u j := ha.trans_lt hi
  unfold pairMagnitude at hs ⊢
  rcases lt_max_iff.mp hs with hh | hh
  · exact max_eq_left hh.le
  · exact False.elim ((lt_irrefl _) hh)

lemma GoodIndex.t_dominant {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    pairMagnitude (tSolution v) j = |tSolution v j| := by
  have hjp : 1 ≤ j - 1 := by have := hg.1; omega
  have hjlt : j - 1 < j := by have := hg.1; omega
  have hs := hg.2.1 (j - 1) hjp hjlt
  have hn : j - 1 + 1 = j := Nat.sub_add_cancel (by have := hg.1; omega)
  have hr : (j : ℝ) - ((j - 1 : ℕ) : ℝ) = 1 := by
    have hr := congrArg (fun n : ℕ => (n : ℝ)) hn
    push_cast at hr
    linarith
  rw [hr, mul_one] at hs
  apply pairMagnitude_eq_abs_of_growth M (tSolution v) j hM
    (pairMagnitude_t_pos v _ hjp) (pairMagnitude_t_pos v _ (by have := hg.1; omega))
  linarith [goodExponent_pos]

lemma GoodIndex.t_ne_zero {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) : tSolution v j ≠ 0 := by
  have hp := pairMagnitude_t_pos v j (by have := hg.1; omega)
  rw [hg.t_dominant hM] at hp
  exact abs_pos.mp hp

lemma GoodIndex.t_next_dominant {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    pairMagnitude (tSolution v) (j + 1) = |tSolution v (j + 1)| := by
  apply pairMagnitude_eq_abs_of_growth M (tSolution v) (j + 1) hM
  · simpa only [Nat.add_sub_cancel] using pairMagnitude_t_pos v j (by have := hg.1; omega)
  · exact pairMagnitude_t_pos v _ (by omega)
  · simp only [Nat.add_sub_cancel]
    have h := hg.2.2.1
    linarith [goodExponent_pos]

lemma GoodIndex.t_growth {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    M ^ goodExponent * |tSolution v j| ≤ |tSolution v (j + 1)| := by
  have h := logb_growth M _ _ goodExponent hM
    (pairMagnitude_t_pos v j (by have := hg.1; omega))
    (pairMagnitude_t_pos v (j + 1) (by omega)) hg.2.2.1
  simpa only [hg.t_dominant hM, hg.t_next_dominant hM] using h

lemma GoodIndex.t_next_ne_zero {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) : tSolution v (j + 1) ≠ 0 := by
  have hp := pairMagnitude_t_pos v (j + 1) (by omega)
  rw [hg.t_next_dominant hM] at hp
  exact abs_pos.mp hp

lemma GoodIndex.t_earlier {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) (l : ℕ) (hl : 1 ≤ l) (hlj : l < j) :
    |tSolution v l| ≤ |tSolution v j| * M ^ (-goodExponent * ((j : ℝ) - (l : ℝ))) := by
  have hp : 0 < M := lt_trans zero_lt_one hM
  have h := logb_growth M _ _ (goodExponent * ((j : ℝ) - (l : ℝ))) hM
    (pairMagnitude_t_pos v l hl) (pairMagnitude_t_pos v j (by have := hg.1; omega))
    (hg.2.1 l hl hlj)
  rw [hg.t_dominant hM] at h
  have h' : |tSolution v l| ≤ |tSolution v j| /
      M ^ (goodExponent * ((j : ℝ) - (l : ℝ))) := by
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hp _)).mpr
    calc
      |tSolution v l| * M ^ (goodExponent * ((j : ℝ) - (l : ℝ))) ≤
          pairMagnitude (tSolution v) l * M ^ (goodExponent * ((j : ℝ) - (l : ℝ))) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hp.le _)
      _ ≤ |tSolution v j| := by simpa only [mul_comm] using h
  simpa only [neg_mul, Real.rpow_neg hp.le, div_eq_mul_inv] using h'

lemma pairMagnitude_eq_prev_of_decrease (M : ℝ) (u : ℕ → ℝ) (j : ℕ)
    (hM : 1 < M) (hj : 0 < pairMagnitude u j) (hnext : 0 < pairMagnitude u (j + 1))
    (hg : pairLog M u (j + 1) < pairLog M u j) :
    pairMagnitude u j = |u (j - 1)| := by
  have hi : pairMagnitude u (j + 1) < pairMagnitude u j :=
    (Real.logb_lt_logb_iff hM hnext hj).mp hg
  have ha : |u j| ≤ pairMagnitude u (j + 1) := by
    simpa only [pairMagnitude, Nat.add_sub_cancel] using le_max_right |u (j + 1)| |u j|
  have hs : |u j| < pairMagnitude u j := ha.trans_lt hi
  unfold pairMagnitude at hs ⊢
  rcases lt_max_iff.mp hs with hh | hh
  · exact False.elim ((lt_irrefl _) hh)
  · exact max_eq_right hh.le

lemma GoodIndex.u_dominant {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    pairMagnitude (linearSolution v 1 b) j = |linearSolution v 1 b (j - 1)| := by
  apply pairMagnitude_eq_prev_of_decrease M _ j hM
    (pairMagnitude_normalized_pos v b j (by have := hg.1; omega))
    (pairMagnitude_normalized_pos v b (j + 1) (by omega))
  have h := hg.2.2.2.1
  linarith [goodExponent_pos]

lemma GoodIndex.u_next_dominant {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    pairMagnitude (linearSolution v 1 b) (j + 1) = |linearSolution v 1 b j| := by
  have h := pairMagnitude_eq_prev_of_decrease M (linearSolution v 1 b) (j + 1) hM
    (pairMagnitude_normalized_pos v b (j + 1) (by omega))
    (pairMagnitude_normalized_pos v b (j + 1 + 1) (by omega))
  apply (by simpa only [Nat.add_sub_cancel] using h)
  have hs := hg.2.2.2.2
  linarith [goodExponent_pos]

lemma GoodIndex.u_decay {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    M ^ goodExponent * |linearSolution v 1 b j| ≤ |linearSolution v 1 b (j - 1)| ∧
    M ^ goodExponent * |linearSolution v 1 b (j + 1)| ≤ |linearSolution v 1 b j| := by
  have h₁ := logb_growth M _ _ goodExponent hM
    (pairMagnitude_normalized_pos v b (j + 1) (by omega))
    (pairMagnitude_normalized_pos v b j (by have := hg.1; omega)) hg.2.2.2.1
  rw [hg.u_dominant hM, hg.u_next_dominant hM] at h₁
  have h₂ := logb_growth M _ _ goodExponent hM
    (pairMagnitude_normalized_pos v b (j + 2) (by omega))
    (pairMagnitude_normalized_pos v b (j + 1) (by omega)) hg.2.2.2.2
  rw [hg.u_next_dominant hM] at h₂
  refine ⟨h₁, ?_⟩
  calc
    M ^ goodExponent * |linearSolution v 1 b (j + 1)| ≤
        M ^ goodExponent * pairMagnitude (linearSolution v 1 b) (j + 2) := by
      apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (le_trans zero_le_one hM.le) _)
      change |linearSolution v 1 b (j + 1)| ≤ max _ |linearSolution v 1 b (j + 1)|
      exact le_max_right _ _
    _ ≤ _ := h₂

lemma GoodIndex.t_previous_growth {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 1 < M) :
    M ^ goodExponent * |tSolution v (j - 1)| ≤ |tSolution v j| := by
  have hprev : 1 ≤ j - 1 := by have := hg.1; omega
  have hlt : j - 1 < j := by have := hg.1; omega
  have hs := hg.2.1 (j - 1) hprev hlt
  have hr : (j : ℝ) - ((j - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (by have := hg.1; omega)]
    push_cast
    ring
  rw [hr, mul_one] at hs
  have h := logb_growth M _ _ goodExponent hM (pairMagnitude_t_pos v _ hprev)
    (pairMagnitude_t_pos v j (by have := hg.1; omega)) hs
  rw [hg.t_dominant hM] at h
  exact (mul_le_mul_of_nonneg_left (le_max_left _ _)
    (Real.rpow_nonneg (le_trans zero_le_one hM.le) _)).trans h

lemma goodScale_square (M : ℝ) (hM : 2 ≤ M) : 2 ≤ (M ^ goodExponent) ^ (2 : ℕ) := by
  have hm : 1 ≤ M := by linarith
  have he : (1 : ℝ) ≤ goodExponent * 2 := by norm_num [goodExponent]
  have h := Real.rpow_le_rpow_of_exponent_le hm he
  rw [Real.rpow_one, Real.rpow_mul (le_trans zero_le_one hm), Real.rpow_two] at h
  exact hM.trans h

lemma GoodIndex.u_wronskian_bound {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 2 ≤ M) :
    |linearSolution v 1 b (j - 1)| * |tSolution v j| ≤ 2 := by
  have hM₁ : 1 < M := by linarith
  let q : ℝ := M ^ goodExponent
  have hq : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hq₂ : 2 ≤ q ^ 2 := goodScale_square M hM
  have ht := hg.t_previous_growth hM₁
  have hu := (hg.u_decay hM₁).1
  have hp := mul_le_mul hu ht (by positivity) (abs_nonneg _)
  have hw := solution_wronskian v 1 b (j - 1)
  have hn : j - 1 + 1 = j := Nat.sub_add_cancel (by have := hg.1; omega)
  rw [hn] at hw
  have habs : |linearSolution v 1 b (j - 1)| * |tSolution v j| ≤
      1 + |linearSolution v 1 b j| * |tSolution v (j - 1)| := by
    rw [← abs_mul, show linearSolution v 1 b (j - 1) * tSolution v j =
      1 + linearSolution v 1 b j * tSolution v (j - 1) by linarith only [hw]]
    simpa only [abs_mul, abs_one] using
      abs_add_le (1 : ℝ) (linearSolution v 1 b j * tSolution v (j - 1))
  have hp' : q ^ 2 * (|linearSolution v 1 b j| * |tSolution v (j - 1)|) ≤
      |linearSolution v 1 b (j - 1)| * |tSolution v j| := by
    dsimp [q]
    nlinarith only [hp]
  have hs := mul_le_mul_of_nonneg_right hq₂
    (mul_nonneg (abs_nonneg (linearSolution v 1 b j)) (abs_nonneg (tSolution v (j - 1))))
  nlinarith only [habs, hp', hs]

theorem GoodIndex.boundary_expansion_error {M : ℝ} {v : ℕ → ℝ} {b : ℝ} {j : ℕ}
    (hg : GoodIndex M v b j) (hM : 2 ≤ M) :
    |b - (boundaryValue v j + 1 / (tSolution v j * tSolution v (j + 1)))| ≤
      2 / ((M ^ goodExponent) ^ (3 : ℕ) * |tSolution v j| ^ 2) := by
  have hM₁ : 1 < M := by linarith
  let q : ℝ := M ^ goodExponent
  let L : ℝ := |tSolution v j|
  have hq : 0 < q := Real.rpow_pos_of_pos (by linarith) _
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM₁)
  have ht := hg.t_growth hM₁
  have hu₁ := (hg.u_decay hM₁).1
  have hu₂ := (hg.u_decay hM₁).2
  have hb := hg.u_wronskian_bound hM
  have hu : |linearSolution v 1 b (j + 1)| ≤ 2 / (q ^ 2 * L) := by
    apply (le_div_iff₀ (by positivity)).mpr
    have hu₁' := mul_le_mul_of_nonneg_right hu₁ hL.le
    have hu₂' := mul_le_mul_of_nonneg_right hu₂ (mul_nonneg hq.le hL.le)
    dsimp [q, L] at *
    nlinarith only [hu₁', hu₂', hb]
  have he := boundary_expansion_exact v j (hg.t_ne_zero hM₁) (hg.t_next_ne_zero hM₁) b
  have hid : b - (boundaryValue v j + 1 / (tSolution v j * tSolution v (j + 1))) =
      linearSolution v 1 b (j + 1) / tSolution v (j + 1) := by linarith only [he]
  rw [hid, abs_div]
  calc
    |linearSolution v 1 b (j + 1)| / |tSolution v (j + 1)| ≤
        (2 / (q ^ 2 * L)) / (q * L) :=
      div_le_div₀ (by positivity) hu (mul_pos hq hL) ht
    _ = 2 / ((M ^ goodExponent) ^ (3 : ℕ) * |tSolution v j| ^ 2) := by
      dsimp [q, L]
      ring

lemma potential_lipschitz (k x y : ℝ) (hk : 0 ≤ k) :
    |potential k y - potential k x| ≤ (2 * Real.pi * growthBase k) * |y - x| := by
  have hK : 0 ≤ 2 * Real.pi * k := by positivity
  have hπ : 0 ≤ 2 * Real.pi := by positivity
  have hid : potential k y - potential k x =
      (2 * Real.pi * k) * (Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)) := by
    unfold potential
    ring
  rw [hid, abs_mul, abs_of_nonneg hK]
  have hdiff : |2 * Real.pi * y - 2 * Real.pi * x| = (2 * Real.pi) * |y - x| := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hπ]
  calc
    (2 * Real.pi * k) * |Real.cos (2 * Real.pi * y) - Real.cos (2 * Real.pi * x)| ≤
        (2 * Real.pi * k) * ((2 * Real.pi) * |y - x|) := by
      apply mul_le_mul_of_nonneg_left _ hK
      rw [← hdiff]
      exact Real.abs_cos_sub_cos_le _ _
    _ ≤ (2 * Real.pi * growthBase k) * |y - x| := by
      have h : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
      have h' := mul_le_mul_of_nonneg_right h (mul_nonneg hπ (abs_nonneg (y - x)))
      nlinarith only [h']

lemma abs_sub_left_of_mem_uIcc (x y z : ℝ) (hz : z ∈ uIcc x y) : |z - x| ≤ |y - x| := by
  rcases le_total x y with hxy | hyx
  · rw [uIcc_of_le hxy] at hz
    rw [abs_of_nonneg (sub_nonneg.mpr hz.1), abs_of_nonneg (sub_nonneg.mpr hxy)]
    linarith [hz.2]
  · rw [uIcc_of_ge hyx] at hz
    rw [abs_of_nonpos (sub_nonpos.mpr hz.2), abs_of_nonpos (sub_nonpos.mpr hyx)]
    linarith [hz.1]

theorem phi_quadratic_error (k x y : ℝ) (hk : 0 ≤ k) :
    |phi k y - phi k x - potential k x * (y - x)| ≤
      (2 * Real.pi * growthBase k) * |y - x| ^ 2 := by
  let f : ℝ → ℝ := fun z => phi k z - potential k x * z
  have hd : ∀ z : ℝ, HasDerivAt f (potential k z - potential k x) z := by
    intro z
    have h := (hasDerivAt_phi k z).sub ((hasDerivAt_id z).const_mul (potential k x))
    convert! h using 1
    simp
  have hC : 0 ≤ 2 * Real.pi * growthBase k := by
    have := growthBase_ge_four k hk
    positivity
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := f) (f' := fun z => potential k z - potential k x)
    (s := uIcc x y) (C := (2 * Real.pi * growthBase k) * |y - x|)
    (fun z _ => (hd z).hasDerivWithinAt)
    (fun z hz => by
      simp only [Real.norm_eq_abs]
      exact (potential_lipschitz k x z hk).trans
        (mul_le_mul_of_nonneg_left (abs_sub_left_of_mem_uIcc x y z hz) hC))
    (convex_uIcc x y) (left_mem_uIcc) (right_mem_uIcc)
  simp only [Real.norm_eq_abs, f] at h
  have he : phi k y - phi k x - potential k x * (y - x) =
      phi k y - potential k x * y - (phi k x - potential k x * x) := by ring
  rw [← he] at h
  nlinarith only [h]

lemma forcingResponse_bound (M : ℝ) (v F : ℕ → ℝ) (hM : 1 ≤ M)
    (hv : ∀ i : ℕ, |v i| + 1 ≤ M) (n : ℕ) :
    max |forcingResponse v F (n + 1)| |forcingResponse v F n| ≤ forcingBudget M F n := by
  induction n with
  | zero => simp [forcingResponse, forcingBudget]
  | succ n ih =>
    let R := max |forcingResponse v F (n + 1)| |forcingResponse v F n|
    have hR : 0 ≤ R := (abs_nonneg _).trans (le_max_left _ _)
    have h₀ : |forcingResponse v F n| ≤ R := le_max_right _ _
    have h₁ : |forcingResponse v F (n + 1)| ≤ R := le_max_left _ _
    have hnext : |forcingResponse v F (n + 2)| ≤ M * R + |F (n + 1)| := by
      change |v (n + 1) * forcingResponse v F (n + 1) - forcingResponse v F n + F (n + 1)| ≤ _
      calc
        _ ≤ |v (n + 1) * forcingResponse v F (n + 1) - forcingResponse v F n| + |F (n + 1)| :=
          abs_add_le _ _
        _ ≤ |v (n + 1)| * |forcingResponse v F (n + 1)| +
            |forcingResponse v F n| + |F (n + 1)| := by
          gcongr
          simpa only [sub_zero, zero_sub, abs_neg, abs_mul] using
            abs_sub_le (v (n + 1) * forcingResponse v F (n + 1)) (0 : ℝ) (forcingResponse v F n)
        _ ≤ (|v (n + 1)| + 1) * R + |F (n + 1)| := by
          have h := mul_le_mul_of_nonneg_left h₁ (abs_nonneg (v (n + 1)))
          nlinarith only [h, h₀]
        _ ≤ M * R + |F (n + 1)| := by
          gcongr
          exact hv _
    change max |forcingResponse v F (n + 2)| |forcingResponse v F (n + 1)| ≤
      M * forcingBudget M F n + |F (n + 1)|
    apply max_le
    · exact hnext.trans (add_le_add (mul_le_mul_of_nonneg_left ih (le_trans zero_le_one hM)) le_rfl)
    · have hinc : R ≤ M * R := by nlinarith only [hM, hR]
      exact h₁.trans (hinc.trans ((mul_le_mul_of_nonneg_left ih (le_trans zero_le_one hM)).trans
        (le_add_of_nonneg_right (abs_nonneg _))))

lemma orbitDisplacement_step (k q₀ θ δ : ℝ) (n : ℕ) :
    orbitDisplacement k q₀ θ δ (n + 2) =
      orbitCoefficient k q₀ θ (n + 1) * orbitDisplacement k q₀ θ δ (n + 1) -
        orbitDisplacement k q₀ θ δ n + orbitForcing k q₀ θ δ (n + 1) := by
  simp only [orbitDisplacement, liftedOrbit_step, orbitForcing]
  ring

lemma orbitDisplacement_representation (k q₀ θ δ : ℝ) (n : ℕ) :
    orbitDisplacement k q₀ θ δ n = δ * tSolution (orbitCoefficient k q₀ θ) n +
      forcingResponse (orbitCoefficient k q₀ θ) (orbitForcing k q₀ θ δ) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [orbitDisplacement, tSolution, forcingResponse]
  | one => simp [orbitDisplacement, tSolution, forcingResponse]
  | more n h₀ h₁ =>
    rw [orbitDisplacement_step, h₀, h₁]
    simp only [tSolution, linearSolution_step, forcingResponse]
    ring

lemma orbitForcing_bound (k q₀ θ δ : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    |orbitForcing k q₀ θ δ n| ≤
      (2 * Real.pi * growthBase k) * |orbitDisplacement k q₀ θ δ n| ^ 2 :=
  phi_quadratic_error k _ _ hk

lemma orbitDisplacement_comparison (k q₀ θ δ : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    |orbitDisplacement k q₀ θ δ (n + 1)| ≤
      |δ| * |tSolution (orbitCoefficient k q₀ θ) (n + 1)| +
        forcingBudget (growthBase k) (orbitForcing k q₀ θ δ) n := by
  have h := forcingResponse_bound (growthBase k) (orbitCoefficient k q₀ θ)
    (orbitForcing k q₀ θ δ) (by have := growthBase_ge_four k hk; linarith)
    (fun i => potential_bound k _ hk) n
  rw [orbitDisplacement_representation]
  calc
    _ ≤ |δ * tSolution (orbitCoefficient k q₀ θ) (n + 1)| +
        |forcingResponse (orbitCoefficient k q₀ θ) (orbitForcing k q₀ θ δ) (n + 1)| :=
      abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add le_rfl ((le_max_left _ _).trans h)

lemma forcing_bootstrap (M C : ℝ) (D F B : ℕ → ℝ) (j : ℕ) (hM : 0 ≤ M)
    (hB : ∀ l : ℕ, 1 ≤ l → l ≤ j → 0 ≤ B l ∧ B l ≤ 1)
    (hscale : ∀ l : ℕ, 1 ≤ l → l < j → M * (1 + 4 * C) * (B l) ^ 2 ≤ (B (l + 1)) ^ 2)
    (hsplit : ∀ l : ℕ, 1 ≤ l → l ≤ j → |D l| ≤ B l + forcingBudget M F (l - 1))
    (hforce : ∀ l : ℕ, 1 ≤ l → l < j → |D l| ≤ 2 * B l →
      |F l| ≤ 4 * C * M * (B l) ^ 2) :
    ∀ l : ℕ, 1 ≤ l → l ≤ j →
      forcingBudget M F (l - 1) ≤ (B l) ^ 2 ∧ |D l| ≤ 2 * B l := by
  have h : ∀ n : ℕ, n + 1 ≤ j →
      forcingBudget M F n ≤ (B (n + 1)) ^ 2 ∧ |D (n + 1)| ≤ 2 * B (n + 1) := by
    intro n
    induction n with
    | zero =>
      intro hj
      refine ⟨by exact sq_nonneg _, ?_⟩
      have hs := hsplit 1 (by omega) hj
      have hb := hB 1 (by omega) hj
      simp only [Nat.sub_self, forcingBudget] at hs
      linarith only [hs, hb.1]
    | succ n ih =>
      intro hj
      obtain ⟨he, hd⟩ := ih (by omega)
      have hf := hforce (n + 1) (by omega) (by omega) hd
      have hb := hB (n + 2) (by omega) (by omega)
      have he' : forcingBudget M F (n + 1) ≤ (B (n + 2)) ^ 2 := by
        change M * forcingBudget M F n + |F (n + 1)| ≤ _
        calc
          _ ≤ M * (B (n + 1)) ^ 2 + 4 * C * M * (B (n + 1)) ^ 2 :=
            add_le_add (mul_le_mul_of_nonneg_left he hM) hf
          _ = M * (1 + 4 * C) * (B (n + 1)) ^ 2 := by ring
          _ ≤ (B (n + 2)) ^ 2 := hscale (n + 1) (by omega) (by omega)
      refine ⟨he', ?_⟩
      have hs := hsplit (n + 2) (by omega) (by omega)
      change |D (n + 2)| ≤ B (n + 2) + forcingBudget M F (n + 1) at hs
      nlinarith only [hs, he', hb.1, hb.2]
  intro l hl hlj
  have heq : l - 1 + 1 = l := Nat.sub_add_cancel hl
  simpa only [heq] using h (l - 1) (by omega)

lemma power_backward_weight (r : ℝ) (j l : ℕ) (hl : l < j) :
    r ^ (j - l) = r * r ^ (j - (l + 1)) := by
  have he : j - l = (j - (l + 1)) + 1 := by omega
  rw [he, pow_succ, mul_comm]

lemma negative_power_good (M : ℝ) (hM : 1 < M) :
    0 < M ^ (-goodExponent) ∧ M ^ (-goodExponent) ≤ 1 := by
  have hp : 0 < M := lt_trans zero_lt_one hM
  rw [Real.rpow_neg hp.le]
  have hq : 1 < M ^ goodExponent := Real.one_lt_rpow hM goodExponent_pos
  constructor
  · positivity
  · exact inv_le_one_of_one_le₀ hq.le

lemma GoodIndex.rescaled_linear_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) (l : ℕ) (hl : 1 ≤ l) (hlj : l ≤ j) :
    |ξ / (|tSolution (orbitCoefficient k q₀ θ) j|)| * |tSolution (orbitCoefficient k q₀ θ) l| ≤
      (growthBase k ^ (-goodExponent)) ^ (j - l) := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0 < |tSolution (orbitCoefficient k q₀ θ) j| := abs_pos.mpr (hg.t_ne_zero hM)
  have ht : |tSolution (orbitCoefficient k q₀ θ) l| ≤
      |tSolution (orbitCoefficient k q₀ θ) j| * (growthBase k ^ (-goodExponent)) ^ (j - l) := by
    rcases lt_or_eq_of_le hlj with hlt | rfl
    · have ht := hg.t_earlier hM l hl hlt
      have hp : 0 ≤ growthBase k := le_trans zero_le_one hM.le
      rw [← Nat.cast_sub hlj, Real.rpow_mul hp, Real.rpow_natCast] at ht
      exact ht
    · simp
  rw [abs_div, abs_abs]
  calc
    |ξ| / |tSolution (orbitCoefficient k q₀ θ) j| * |tSolution (orbitCoefficient k q₀ θ) l| ≤
        1 / |tSolution (orbitCoefficient k q₀ θ) j| * |tSolution (orbitCoefficient k q₀ θ) l| := by
      gcongr
    _ ≤ _ := by
      rw [one_div, ← div_eq_inv_mul]
      exact (div_le_iff₀ hL).mpr (by simpa only [mul_comm] using ht)

theorem GoodIndex.rescaled_displacement {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hsmall : growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) (l : ℕ) (hl : l ≤ j) :
    |orbitDisplacement k q₀ θ (ξ / |tSolution (orbitCoefficient k q₀ θ) j|) l| ≤
      2 * (growthBase k ^ (-goodExponent)) ^ (j - l) := by
  let M := growthBase k
  let r := M ^ (-goodExponent)
  let δ := ξ / |tSolution (orbitCoefficient k q₀ θ) j|
  let D := orbitDisplacement k q₀ θ δ
  let F := orbitForcing k q₀ θ δ
  let B : ℕ → ℝ := fun i => r ^ (j - i)
  have hM : 1 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  have hr := negative_power_good M hM
  have hB : ∀ i : ℕ, 1 ≤ i → i ≤ j → 0 ≤ B i ∧ B i ≤ 1 := by
    intro i _ _
    exact ⟨pow_nonneg hr.1.le _, pow_le_one₀ hr.1.le hr.2⟩
  have hscale : ∀ i : ℕ, 1 ≤ i → i < j →
      M * (1 + 4 * (2 * Real.pi)) * (B i) ^ 2 ≤ (B (i + 1)) ^ 2 := by
    intro i _ hij
    have he : B i = r * B (i + 1) := power_backward_weight r j i hij
    rw [he]
    have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (B (i + 1)))
    dsimp [M, r] at *
    nlinarith only [hs]
  have hsplit : ∀ i : ℕ, 1 ≤ i → i ≤ j → |D i| ≤ B i + forcingBudget M F (i - 1) := by
    intro i hi hij
    have he : i - 1 + 1 = i := Nat.sub_add_cancel hi
    have hc := orbitDisplacement_comparison k q₀ θ δ hk (i - 1)
    rw [he] at hc
    exact hc.trans (add_le_add (hg.rescaled_linear_bound hk ξ hξ i hi hij) le_rfl)
  have hforce : ∀ i : ℕ, 1 ≤ i → i < j → |D i| ≤ 2 * B i →
      |F i| ≤ 4 * (2 * Real.pi) * M * (B i) ^ 2 := by
    intro i hi hij hd
    have hf := orbitForcing_bound k q₀ θ δ hk i
    have hs : |D i| ^ 2 ≤ (2 * B i) ^ 2 := by
      gcongr
    have hs' := mul_le_mul_of_nonneg_left hs
      (show 0 ≤ 2 * Real.pi * M by have := hM.le; positivity)
    dsimp [D, F, M] at *
    nlinarith only [hf, hs']
  by_cases hl₀ : l = 0
  · subst l
    simp only [orbitDisplacement, liftedOrbit_zero, sub_self, abs_zero, Nat.sub_zero]
    positivity
  · exact (forcing_bootstrap M (2 * Real.pi) D F B j (le_trans zero_le_one hM.le)
      hB hscale hsplit hforce l (by omega) hl).2

lemma tSolution_comparison (v w : ℕ → ℝ) (a : ℝ) (n : ℕ) :
    a * tSolution w n = a * tSolution v n +
      forcingResponse v (fun i => (w i - v i) * (a * tSolution w i)) n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [tSolution, forcingResponse]
  | one => simp [tSolution, forcingResponse]
  | more n h₀ h₁ =>
    change a * (w (n + 1) * tSolution w (n + 1) - tSolution w n) =
      a * (v (n + 1) * tSolution v (n + 1) - tSolution v n) +
        (v (n + 1) * forcingResponse v (fun i => (w i - v i) * (a * tSolution w i)) (n + 1) -
          forcingResponse v (fun i => (w i - v i) * (a * tSolution w i)) n +
            (w (n + 1) - v (n + 1)) * (a * tSolution w (n + 1)))
    linear_combination v (n + 1) * h₁ - h₀

theorem GoodIndex.rescaled_derivative {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hsmall : growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) (l : ℕ) (hl : l ≤ j) :
    |tSolution (orbitCoefficient k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) j|)) l /
      (|tSolution (orbitCoefficient k q₀ θ) j|)| ≤
      2 * (growthBase k ^ (-goodExponent)) ^ (j - l) := by
  let M := growthBase k
  let r := M ^ (-goodExponent)
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let δ := ξ / L
  let v := orbitCoefficient k q₀ θ
  let w := orbitCoefficient k q₀ (θ + δ)
  let D : ℕ → ℝ := fun i => L⁻¹ * tSolution w i
  let F : ℕ → ℝ := fun i => (w i - v i) * D i
  let B : ℕ → ℝ := fun i => r ^ (j - i)
  have hM : 1 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have hr := negative_power_good M hM
  have hB : ∀ i : ℕ, 1 ≤ i → i ≤ j → 0 ≤ B i ∧ B i ≤ 1 := by
    intro i _ _
    exact ⟨pow_nonneg hr.1.le _, pow_le_one₀ hr.1.le hr.2⟩
  have hscale : ∀ i : ℕ, 1 ≤ i → i < j →
      M * (1 + 4 * (2 * Real.pi)) * (B i) ^ 2 ≤ (B (i + 1)) ^ 2 := by
    intro i _ hij
    rw [show B i = r * B (i + 1) from power_backward_weight r j i hij]
    have hs := mul_le_mul_of_nonneg_right hsmall (sq_nonneg (B (i + 1)))
    dsimp [M, r] at *
    nlinarith only [hs]
  have hsplit : ∀ i : ℕ, 1 ≤ i → i ≤ j → |D i| ≤ B i + forcingBudget M F (i - 1) := by
    intro i hi hij
    have he : i - 1 + 1 = i := Nat.sub_add_cancel hi
    have hc := forcingResponse_bound M v F hM.le (fun i => potential_bound k _ hk) (i - 1)
    rw [he] at hc
    have ht := hg.rescaled_linear_bound hk 1 (by norm_num) i hi hij
    have hbase : |L⁻¹ * tSolution v i| ≤ B i := by
      simpa only [L, v, B, r, M, abs_mul, abs_inv, abs_abs, abs_div, abs_one, one_div] using ht
    change |L⁻¹ * tSolution w i| ≤ _
    rw [tSolution_comparison v w L⁻¹ i]
    exact (abs_add_le _ _).trans (add_le_add hbase ((le_max_left _ _).trans hc))
  have hforce : ∀ i : ℕ, 1 ≤ i → i < j → |D i| ≤ 2 * B i →
      |F i| ≤ 4 * (2 * Real.pi) * M * (B i) ^ 2 := by
    intro i _ hij hd
    have hdisp := hg.rescaled_displacement hk hsmall ξ hξ i hij.le
    have hv := potential_lipschitz k (liftedOrbit k q₀ θ i)
      (liftedOrbit k q₀ (θ + δ) i) hk
    have hv' : |w i - v i| ≤ (2 * Real.pi * M) * (2 * B i) :=
      hv.trans (mul_le_mul_of_nonneg_left hdisp (by have := hM.le; positivity))
    have hmul := mul_le_mul hv' hd (abs_nonneg (D i)) (by have := (hB i (by omega) hij.le).1; positivity)
    change |(w i - v i) * D i| ≤ _
    rw [abs_mul]
    nlinarith only [hmul]
  have hresult : |D l| ≤ 2 * B l := by
    by_cases hl₀ : l = 0
    · subst l
      simp only [D, tSolution, linearSolution_zero, mul_zero, abs_zero]
      positivity
    · exact (forcing_bootstrap M (2 * Real.pi) D F B j (le_trans zero_le_one hM.le)
        hB hscale hsplit hforce l (by omega) hl).2
  simpa only [D, L, w, δ, B, r, M, div_eq_mul_inv, mul_comm] using hresult

lemma forcingBudget_weighted (M A C r : ℝ) (F : ℕ → ℝ) (j : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hscale : (M * A + C) * r ^ 2 ≤ A)
    (hF : ∀ i : ℕ, 1 ≤ i → i < j → |F i| ≤ C * (r ^ (j - i)) ^ 2) :
    ∀ i : ℕ, 1 ≤ i → i ≤ j →
      forcingBudget M F (i - 1) ≤ A * (r ^ (j - i)) ^ 2 := by
  have hb : ∀ n : ℕ, n + 1 ≤ j → forcingBudget M F n ≤ A * (r ^ (j - (n + 1))) ^ 2 := by
    intro n
    induction n with
    | zero =>
      intro _
      exact mul_nonneg hA (sq_nonneg _)
    | succ n ih =>
      intro hj
      have he := mul_le_mul_of_nonneg_left (ih (by omega)) hM
      have hf := hF (n + 1) (by omega) (by omega)
      have hweight := power_backward_weight r j (n + 1) (by omega)
      have hs := mul_le_mul_of_nonneg_right hscale (sq_nonneg (r ^ (j - (n + 2))))
      change M * forcingBudget M F n + |F (n + 1)| ≤ _
      rw [hweight] at he hf
      nlinarith only [he, hf, hs]
  intro i hi hij
  simpa only [Nat.sub_add_cancel hi] using hb (i - 1) (by omega)

lemma tSolution_comparison_error (M : ℝ) (v w : ℕ → ℝ) (a : ℝ) (n : ℕ)
    (hM : 1 ≤ M) (hv : ∀ i : ℕ, |v i| + 1 ≤ M) :
    |a * tSolution w (n + 1) - a * tSolution v (n + 1)| ≤
      forcingBudget M (fun i => (w i - v i) * (a * tSolution w i)) n := by
  have hid : a * tSolution w (n + 1) - a * tSolution v (n + 1) =
      forcingResponse v (fun i => (w i - v i) * (a * tSolution w i)) (n + 1) := by
    linarith only [tSolution_comparison v w a (n + 1)]
  rw [hid]
  exact (le_max_left _ _).trans (forcingResponse_bound M v _ hM hv n)

lemma GoodIndex.rescaled_variation_force_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hsmall : growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) (i : ℕ) (hi : i ≤ j) :
    |(orbitCoefficient k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) j|) i -
        orbitCoefficient k q₀ θ i) *
      (|tSolution (orbitCoefficient k q₀ θ) j|⁻¹ *
        tSolution (orbitCoefficient k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) j|)) i)| ≤
      (8 * Real.pi * growthBase k) * ((growthBase k ^ (-goodExponent)) ^ (j - i)) ^ 2 := by
  have hdisp := hg.rescaled_displacement hk hsmall ξ hξ i hi
  have hder := hg.rescaled_derivative hk hsmall ξ hξ i hi
  have hv := potential_lipschitz k (liftedOrbit k q₀ θ i)
    (liftedOrbit k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) j|) i) hk
  have hM := growthBase_ge_four k hk
  have hcoeff := hv.trans (mul_le_mul_of_nonneg_left hdisp (by positivity))
  have hmul := mul_le_mul hcoeff hder (abs_nonneg _) (by positivity)
  rw [abs_mul]
  simp only [orbitCoefficient, div_eq_mul_inv, mul_comm] at hmul ⊢
  nlinarith only [hmul]

theorem GoodIndex.varied_t_lower {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hsmall : growthBase k * (1 + 8 * Real.pi) * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1 / 2)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    |tSolution (orbitCoefficient k q₀ θ) j| / 2 ≤
      |tSolution (orbitCoefficient k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) j|)) j| := by
  let M := growthBase k
  let r := M ^ (-goodExponent)
  let v := orbitCoefficient k q₀ θ
  let L := |tSolution v j|
  let w := orbitCoefficient k q₀ (θ + ξ / L)
  let F : ℕ → ℝ := fun i => (w i - v i) * (L⁻¹ * tSolution w i)
  have hM : 1 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have hj : 1 ≤ j := by have := hg.1; omega
  have he : j - 1 + 1 = j := Nat.sub_add_cancel hj
  have hsmall₁ : M * (1 + 8 * Real.pi) * r ^ 2 ≤ 1 := by linarith
  have hscale : (M * (1 / 2) + 8 * Real.pi * M) * r ^ 2 ≤ 1 / 2 := by
    have hMr : 0 ≤ M * r ^ 2 := mul_nonneg (le_trans zero_le_one hM.le) (sq_nonneg _)
    dsimp [M, r] at *
    nlinarith only [hsmall, hMr]
  have hF : ∀ i : ℕ, 1 ≤ i → i < j → |F i| ≤
      (8 * Real.pi * M) * (r ^ (j - i)) ^ 2 := by
    intro i _ hi
    exact hg.rescaled_variation_force_bound hk hsmall₁ ξ hξ i hi.le
  have hb := forcingBudget_weighted M (1 / 2) (8 * Real.pi * M) r F j
    (le_trans zero_le_one hM.le) (by norm_num) hscale hF j hj le_rfl
  simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at hb
  have hc := tSolution_comparison_error M v w L⁻¹ (j - 1) hM.le (fun i => potential_bound k _ hk)
  rw [he] at hc
  have hdiff : |L⁻¹ * tSolution w j - L⁻¹ * tSolution v j| ≤ 1 / 2 := hc.trans hb
  have hbase : |L⁻¹ * tSolution v j| = 1 := by
    rw [abs_mul, abs_inv, abs_of_pos hL]
    exact inv_mul_cancel₀ hL.ne'
  have hlow : 1 / 2 ≤ |L⁻¹ * tSolution w j| := by
    have htri := abs_sub_le (L⁻¹ * tSolution v j) (L⁻¹ * tSolution w j) 0
    rw [sub_zero, sub_zero, abs_sub_comm, hbase] at htri
    linarith only [htri, hdiff]
  rw [abs_mul, abs_inv, abs_of_pos hL, ← div_eq_inv_mul] at hlow
  exact (le_div_iff₀ hL).mp hlow |>.trans' (by dsimp [L, v]; ring_nf; rfl)

lemma hasDerivAt_potential (k x : ℝ) : HasDerivAt (potential k) (phiSecond k x) x := by
  have h := (hasDerivAt_const x (2 : ℝ)).add
    ((((hasDerivAt_id x).const_mul (2 * Real.pi)).cos).const_mul (2 * Real.pi * k))
  convert! h using 1
  simp only [id_eq]
  unfold phiSecond
  ring

lemma hasDerivAt_rescaledOrbit (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledOrbit k q₀ θ L x n) (rescaledD₁ k q₀ θ L ξ n) ξ := by
  have h := (hasDerivAt_liftedOrbit k q₀ (θ + ξ / L) n).comp ξ
    ((hasDerivAt_const ξ θ).add ((hasDerivAt_id ξ).div_const L))
  convert! h using 1
  simp [rescaledD₁, div_eq_mul_inv]

lemma rescaledD₁_step (k q₀ θ L ξ : ℝ) (n : ℕ) :
    rescaledD₁ k q₀ θ L ξ (n + 2) =
      potential k (rescaledOrbit k q₀ θ L ξ (n + 1)) * rescaledD₁ k q₀ θ L ξ (n + 1) -
        rescaledD₁ k q₀ θ L ξ n := by
  simp only [rescaledD₁, tSolution, linearSolution_step, orbitCoefficient, rescaledOrbit]
  ring

lemma hasDerivAt_rescaledD₁ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledD₁ k q₀ θ L x n) (rescaledD₂ k q₀ θ L ξ n) ξ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [rescaledD₁, rescaledD₂, tSolution, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | one => simpa [rescaledD₁, rescaledD₂, tSolution, forcingResponse] using hasDerivAt_const ξ (1 / L)
  | more n h₀ h₁ =>
    have hv := (hasDerivAt_potential k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ
      (hasDerivAt_rescaledOrbit k q₀ θ L ξ (n + 1))
    have h := (hv.mul h₁).sub h₀
    convert! h using 1
    · funext x
      exact rescaledD₁_step k q₀ θ L x n
    · simp only [rescaledD₂, forcingResponse, orbitCoefficient, rescaledOrbit, Function.comp_apply]
      ring

lemma forcingBudget_weighted_pow (M A C r : ℝ) (p : ℕ) (F : ℕ → ℝ) (j : ℕ)
    (hM : 0 ≤ M) (hA : 0 ≤ A) (hr : 0 ≤ r)
    (hscale : (M * A + C) * r ^ p ≤ A)
    (hF : ∀ i : ℕ, 1 ≤ i → i < j → |F i| ≤ C * (r ^ (j - i)) ^ p) :
    ∀ i : ℕ, 1 ≤ i → i ≤ j → forcingBudget M F (i - 1) ≤ A * (r ^ (j - i)) ^ p := by
  have hb : ∀ n : ℕ, n + 1 ≤ j → forcingBudget M F n ≤ A * (r ^ (j - (n + 1))) ^ p := by
    intro n
    induction n with
    | zero =>
      intro _
      exact mul_nonneg hA (pow_nonneg (pow_nonneg hr _) _)
    | succ n ih =>
      intro hj
      have he := mul_le_mul_of_nonneg_left (ih (by omega)) hM
      have hf := hF (n + 1) (by omega) (by omega)
      have hweight := power_backward_weight r j (n + 1) (by omega)
      have hs := mul_le_mul_of_nonneg_right hscale (pow_nonneg (pow_nonneg hr (j - (n + 2))) p)
      change M * forcingBudget M F n + |F (n + 1)| ≤ _
      rw [hweight, mul_pow] at he hf
      nlinarith only [he, hf, hs]
  intro i hi hij
  simpa only [Nat.sub_add_cancel hi] using hb (i - 1) (by omega)

lemma hasDerivAt_phiSecond (k x : ℝ) : HasDerivAt (phiSecond k) (phiThird k x) x := by
  have h := ((((hasDerivAt_id x).const_mul (2 * Real.pi)).sin).const_mul (-(2 * Real.pi) ^ 2 * k))
  convert! h using 1
  simp only [id_eq, phiThird]
  ring

lemma hasDerivAt_phiThird (k x : ℝ) : HasDerivAt (phiThird k) (phiFourth k x) x := by
  have h := ((((hasDerivAt_id x).const_mul (2 * Real.pi)).cos).const_mul (-(2 * Real.pi) ^ 3 * k))
  convert! h using 1
  simp only [id_eq, phiFourth]
  ring

lemma hasDerivAt_phiFourth (k x : ℝ) : HasDerivAt (phiFourth k) (phiFifth k x) x := by
  have h := ((((hasDerivAt_id x).const_mul (2 * Real.pi)).sin).const_mul ((2 * Real.pi) ^ 4 * k))
  convert! h using 1
  simp only [id_eq, phiFifth]
  ring

lemma hasDerivAt_rescaledD₂ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledD₂ k q₀ θ L x n) (rescaledD₃ k q₀ θ L ξ n) ξ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [rescaledD₂, rescaledD₃, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | one => simpa [rescaledD₂, rescaledD₃, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | more n h₀ h₁ =>
    have hq := hasDerivAt_rescaledOrbit k q₀ θ L ξ (n + 1)
    have hd := hasDerivAt_rescaledD₁ k q₀ θ L ξ (n + 1)
    have hv := (hasDerivAt_potential k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp := (hasDerivAt_phiSecond k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have h := ((hv.mul h₁).sub h₀).add (hp.mul (hd.pow 2))
    convert! h using 1
    simp only [rescaledD₃, forcingResponse, rescaledF₃, orbitCoefficient, rescaledOrbit,
      Function.comp_apply, Pi.pow_apply,
      Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring

lemma hasDerivAt_rescaledD₃ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledD₃ k q₀ θ L x n) (rescaledD₄ k q₀ θ L ξ n) ξ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [rescaledD₃, rescaledD₄, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | one => simpa [rescaledD₃, rescaledD₄, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | more n h₀ h₁ =>
    have hq := hasDerivAt_rescaledOrbit k q₀ θ L ξ (n + 1)
    have hd₁ := hasDerivAt_rescaledD₁ k q₀ θ L ξ (n + 1)
    have hd₂ := hasDerivAt_rescaledD₂ k q₀ θ L ξ (n + 1)
    have hv := (hasDerivAt_potential k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp₂ := (hasDerivAt_phiSecond k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp₃ := (hasDerivAt_phiThird k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have h := ((hv.mul h₁).sub h₀).add
      ((hp₃.mul (hd₁.pow 3)).add ((((hp₂.const_mul 3).mul hd₁).mul hd₂)))
    convert! h using 1
    simp only [rescaledD₄, forcingResponse, rescaledF₄, orbitCoefficient, rescaledOrbit,
      Function.comp_apply, Pi.pow_apply, Pi.mul_apply,
      Nat.reduceSub, Nat.cast_ofNat]
    ring

lemma hasDerivAt_rescaledD₄ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledD₄ k q₀ θ L x n) (rescaledD₅ k q₀ θ L ξ n) ξ := by
  induction n using Nat.twoStepInduction with
  | zero => simpa [rescaledD₄, rescaledD₅, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | one => simpa [rescaledD₄, rescaledD₅, forcingResponse] using hasDerivAt_const ξ (0 : ℝ)
  | more n h₀ h₁ =>
    have hq := hasDerivAt_rescaledOrbit k q₀ θ L ξ (n + 1)
    have hd₁ := hasDerivAt_rescaledD₁ k q₀ θ L ξ (n + 1)
    have hd₂ := hasDerivAt_rescaledD₂ k q₀ θ L ξ (n + 1)
    have hd₃ := hasDerivAt_rescaledD₃ k q₀ θ L ξ (n + 1)
    have hv := (hasDerivAt_potential k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp₂ := (hasDerivAt_phiSecond k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp₃ := (hasDerivAt_phiThird k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have hp₄ := (hasDerivAt_phiFourth k (rescaledOrbit k q₀ θ L ξ (n + 1))).comp ξ hq
    have h := ((hv.mul h₁).sub h₀).add
      ((((hp₄.mul (hd₁.pow 4)).add ((((hp₃.const_mul 6).mul (hd₁.pow 2)).mul hd₂))).add
        ((hp₂.const_mul 3).mul (hd₂.pow 2))).add (((hp₂.const_mul 4).mul hd₁).mul hd₃))
    convert! h using 1
    simp only [rescaledD₅, forcingResponse, rescaledF₅, orbitCoefficient, rescaledOrbit,
      Function.comp_apply, Pi.pow_apply, Pi.mul_apply,
      Nat.reduceSub, pow_one, Nat.cast_ofNat]
    ring

lemma derivativeMajorant_pos : 0 < derivativeMajorant := by unfold derivativeMajorant; positivity

lemma trig_amplitude_bound (k z : ℝ) (p : ℕ) (hk : 0 ≤ k) (hz : |z| ≤ 1) (hp : p ≤ 4) :
    |(2 * Real.pi) ^ (p + 1) * k * z| ≤ derivativeMajorant * growthBase k := by
  have ha : 0 ≤ 2 * Real.pi := by positivity
  have hK : 2 * Real.pi * k ≤ growthBase k := by unfold growthBase; linarith
  have hpow : (2 * Real.pi) ^ p ≤ derivativeMajorant := by
    unfold derivativeMajorant
    calc
      (2 * Real.pi) ^ p ≤ (1 + 2 * Real.pi) ^ p := by gcongr; linarith
      _ ≤ (1 + 2 * Real.pi) ^ 4 := pow_le_pow_right₀ (by linarith) hp
  rw [abs_mul, abs_mul, abs_pow, abs_of_nonneg ha, abs_of_nonneg hk]
  calc
    (2 * Real.pi) ^ (p + 1) * k * |z| ≤ (2 * Real.pi) ^ (p + 1) * k :=
      mul_le_of_le_one_right (by positivity) hz
    _ = (2 * Real.pi) ^ p * (2 * Real.pi * k) := by rw [pow_succ]; ring
    _ ≤ derivativeMajorant * growthBase k :=
      mul_le_mul hpow hK (by positivity) derivativeMajorant_pos.le

lemma uniform_phiSecond_bound (k x : ℝ) (hk : 0 ≤ k) :
    |phiSecond k x| ≤ derivativeMajorant * growthBase k := by
  simpa [phiSecond, neg_mul, abs_neg] using
    trig_amplitude_bound k (Real.sin (2 * Real.pi * x)) 1 hk (Real.abs_sin_le_one _) (by norm_num)
lemma uniform_phiThird_bound (k x : ℝ) (hk : 0 ≤ k) :
    |phiThird k x| ≤ derivativeMajorant * growthBase k := by
  simpa [phiThird, neg_mul, abs_neg] using
    trig_amplitude_bound k (Real.cos (2 * Real.pi * x)) 2 hk (Real.abs_cos_le_one _) (by norm_num)
lemma uniform_phiFourth_bound (k x : ℝ) (hk : 0 ≤ k) :
    |phiFourth k x| ≤ derivativeMajorant * growthBase k := by
  simpa [phiFourth] using
    trig_amplitude_bound k (Real.sin (2 * Real.pi * x)) 3 hk (Real.abs_sin_le_one _) (by norm_num)
lemma uniform_phiFifth_bound (k x : ℝ) (hk : 0 ≤ k) :
    |phiFifth k x| ≤ derivativeMajorant * growthBase k := by
  simpa [phiFifth] using
    trig_amplitude_bound k (Real.cos (2 * Real.pi * x)) 4 hk (Real.abs_cos_le_one _) (by norm_num)

lemma bell₃_bound (V B a b x y : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hx : |x| ≤ 2 * B) (hy : |y| ≤ B ^ 2) :
    |a * x ^ 3 + 3 * b * x * y| ≤ 14 * V * B ^ 3 := by
  calc
    |a * x ^ 3 + 3 * b * x * y| ≤ |a| * |x| ^ 3 + 3 * |b| * |x| * |y| := by
      have ht := abs_add_le (a * x ^ (3 : ℕ)) (3 * b * x * y)
      simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 3)] at ht
      exact ht
    _ ≤ V * (2 * B) ^ 3 + 3 * V * (2 * B) * B ^ 2 := by gcongr
    _ = 14 * V * B ^ 3 := by ring

lemma bell₄_bound (V B a b c x y z : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V)
    (hx : |x| ≤ 2 * B) (hy : |y| ≤ B ^ 2) (hz : |z| ≤ B ^ 3) :
    |a * x ^ 4 + 6 * b * x ^ 2 * y + 3 * c * y ^ 2 + 4 * c * x * z| ≤ 51 * V * B ^ 4 := by
  calc
    _ ≤ |a * x ^ 4| + |6 * b * x ^ 2 * y| + |3 * c * y ^ 2| + |4 * c * x * z| := by
      grw [abs_add_le, abs_add_le, abs_add_le]
    _ = |a| * |x| ^ 4 + 6 * |b| * |x| ^ 2 * |y| + 3 * |c| * |y| ^ 2 + 4 * |c| * |x| * |z| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    _ ≤ V * (2 * B) ^ 4 + 6 * V * (2 * B) ^ 2 * B ^ 2 + 3 * V * (B ^ 2) ^ 2 + 4 * V * (2 * B) * B ^ 3 := by
      gcongr
    _ = 51 * V * B ^ 4 := by ring

lemma bell₅_bound (V B a b c d x y z w : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V) (hd : |d| ≤ V)
    (hx : |x| ≤ 2 * B) (hy : |y| ≤ B ^ 2) (hz : |z| ≤ B ^ 3) (hw : |w| ≤ B ^ 4) :
    |a * x ^ 5 + 10 * b * x ^ 3 * y + 15 * c * x * y ^ 2 + 10 * c * x ^ 2 * z +
      10 * d * y * z + 5 * d * x * w| ≤ 202 * V * B ^ 5 := by
  calc
    _ ≤ |a * x ^ 5| + |10 * b * x ^ 3 * y| + |15 * c * x * y ^ 2| +
        |10 * c * x ^ 2 * z| + |10 * d * y * z| + |5 * d * x * w| := by
      grw [abs_add_le, abs_add_le, abs_add_le, abs_add_le, abs_add_le]
    _ = |a| * |x| ^ 5 + 10 * |b| * |x| ^ 3 * |y| + 15 * |c| * |x| * |y| ^ 2 +
        10 * |c| * |x| ^ 2 * |z| + 10 * |d| * |y| * |z| + 5 * |d| * |x| * |w| := by
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 15), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 5)]
    _ ≤ V * (2 * B) ^ 5 + 10 * V * (2 * B) ^ 3 * B ^ 2 + 15 * V * (2 * B) * (B ^ 2) ^ 2 +
        10 * V * (2 * B) ^ 2 * B ^ 3 + 10 * V * B ^ 2 * B ^ 3 + 5 * V * (2 * B) * B ^ 4 := by
      gcongr
    _ = 202 * V * B ^ 5 := by ring

lemma forcingResponse_fixed_order (M V r : ℝ) (p j : ℕ) (w F : ℕ → ℝ)
    (hM : 1 ≤ M) (hV : 0 ≤ V) (hr : 0 ≤ r) (hr₁ : r ≤ 1) (hp : 2 ≤ p)
    (hMr : M * r ^ 2 ≤ 1 / 2) (hw : ∀ i, |w i| + 1 ≤ M)
    (hF : ∀ i, 1 ≤ i → i < j → |F i| ≤ 256 * V * (r ^ (j - i)) ^ p)
    (l : ℕ) (hl : l ≤ j) :
    |forcingResponse w F l| ≤ (512 * V * r ^ p) * (r ^ (j - l)) ^ p := by
  have hrp : r ^ p ≤ r ^ 2 := pow_le_pow_of_le_one hr hr₁ hp
  have hMp : M * r ^ p ≤ 1 / 2 := (mul_le_mul_of_nonneg_left hrp (by linarith)).trans hMr
  have hA : 0 ≤ 512 * V * r ^ p := by positivity
  have hscale : (M * (512 * V * r ^ p) + 256 * V) * r ^ p ≤ 512 * V * r ^ p := by
    have h := mul_le_mul_of_nonneg_right hMp hA
    nlinarith only [h]
  by_cases hl₀ : l = 0
  · subst l
    simp only [forcingResponse, abs_zero]
    positivity
  · have hl₁ : 1 ≤ l := by omega
    have he : l - 1 + 1 = l := Nat.sub_add_cancel hl₁
    have hc := forcingResponse_bound M w F hM hw (l - 1)
    rw [he] at hc
    exact ((le_max_left _ _).trans hc).trans
      (forcingBudget_weighted_pow M (512 * V * r ^ p) (256 * V) r p F j
        (by linarith) hA hr hscale hF l hl₁ hl)

lemma fixed_order_coarse (V r : ℝ) (p : ℕ) (hV : 0 ≤ V) (hr : 0 ≤ r) (hr₁ : r ≤ 1)
    (hp : 2 ≤ p) (hsmall : 512 * V * r ^ 2 ≤ 1) : 512 * V * r ^ p ≤ 1 := by
  exact (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hr hr₁ hp) (by positivity)).trans hsmall

lemma rescaling_ratio_bounds (k : ℝ) (hk : 0 ≤ k) :
    0 < growthBase k ^ (-goodExponent) ∧ growthBase k ^ (-goodExponent) ≤ 1 := by
  have hM := growthBase_ge_four k hk
  exact ⟨Real.rpow_pos_of_pos (by linarith) _, Real.rpow_le_one_of_one_le_of_nonpos
    (by linarith) (by norm_num [goodExponent])⟩

lemma HigherControl.base_small {k : ℝ} (hc : HigherControl k) (hk : 0 ≤ k) :
    growthBase k * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ) ≤ 1 / 2 := by
  have hM := growthBase_ge_four k hk
  have hp : 0 ≤ 8 * Real.pi * (growthBase k * (growthBase k ^ (-goodExponent)) ^ (2 : ℕ)) := by positivity
  nlinarith only [hc.1, hp]

lemma eventually_scalar_rescaling_small (C ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ M : ℝ in Filter.atTop, C * M * (M ^ (-goodExponent)) ^ (2 : ℕ) ≤ ε := by
  have ht : Filter.Tendsto (fun M : ℝ => C * M ^ (-(2 * goodExponent - 1)))
      Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using
      (tendsto_rpow_neg_atTop (show 0 < 2 * goodExponent - 1 by norm_num [goodExponent])).const_mul C
  filter_upwards [ht.eventually (gt_mem_nhds hε), Filter.eventually_gt_atTop (0 : ℝ)] with M hsmall hM
  have hid : C * M * (M ^ (-goodExponent)) ^ (2 : ℕ) = C * M ^ (-(2 * goodExponent - 1)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    have hexp : -(2 * goodExponent - 1) = 1 + (-goodExponent) * (2 : ℝ) := by ring
    rw [hexp, Real.rpow_add hM, Real.rpow_one]
    ring_nf
  rw [hid]
  exact hsmall.le

lemma tendsto_growthBase : Filter.Tendsto growthBase Filter.atTop Filter.atTop := by
  have h : Filter.Tendsto (fun k : ℝ => (2 * Real.pi) * k) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by positivity) Filter.tendsto_id
  exact Filter.tendsto_atTop_mono (fun k => by dsimp [growthBase]; linarith) h

lemma eventually_HigherControl : ∀ᶠ k : ℝ in Filter.atTop, HigherControl k := by
  have h₁ := tendsto_growthBase.eventually (eventually_scalar_rescaling_small
    (1 + 8 * Real.pi) (1 / 2) (by norm_num))
  have h₂ := tendsto_growthBase.eventually (eventually_scalar_rescaling_small
    (512 * derivativeMajorant) 1 zero_lt_one)
  filter_upwards [h₁, h₂] with k hk₁ hk₂
  constructor
  · convert hk₁ using 1; ring
  · convert hk₂ using 1; ring

theorem GoodIndex.rescaled_high_bounds {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    let r := growthBase k ^ (-goodExponent)
    let V := derivativeMajorant * growthBase k
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    ∀ l : ℕ, l ≤ j →
      |rescaledD₂ k q₀ θ L ξ l| ≤ (512 * V * r ^ 2) * (r ^ (j - l)) ^ 2 ∧
      |rescaledD₃ k q₀ θ L ξ l| ≤ (512 * V * r ^ 3) * (r ^ (j - l)) ^ 3 ∧
      |rescaledD₄ k q₀ θ L ξ l| ≤ (512 * V * r ^ 4) * (r ^ (j - l)) ^ 4 ∧
      |rescaledD₅ k q₀ θ L ξ l| ≤ (512 * V * r ^ 5) * (r ^ (j - l)) ^ 5 := by
  dsimp only
  let M := growthBase k
  let r := M ^ (-goodExponent)
  let V := derivativeMajorant * M
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let w := orbitCoefficient k q₀ (θ + ξ / L)
  have hM : 1 ≤ M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  have hV : 0 ≤ V := mul_nonneg derivativeMajorant_pos.le (le_trans zero_le_one hM)
  have hr : 0 ≤ r := (rescaling_ratio_bounds k hk).1.le
  have hr₁ : r ≤ 1 := (rescaling_ratio_bounds k hk).2
  have hB (i : ℕ) : 0 ≤ r ^ (j - i) := pow_nonneg hr _
  have hfirst : ∀ i, i ≤ j → |rescaledD₁ k q₀ θ L ξ i| ≤ 2 * r ^ (j - i) := by
    intro i hi
    exact hg.rescaled_derivative hk (by linarith only [hc.1]) ξ hξ i hi
  have hresponse (p : ℕ) (hp : 2 ≤ p) (F : ℕ → ℝ)
      (hF : ∀ i, 1 ≤ i → i < j → |F i| ≤ 256 * V * (r ^ (j - i)) ^ p)
      (l : ℕ) (hl : l ≤ j) :
      |forcingResponse w F l| ≤ (512 * V * r ^ p) * (r ^ (j - l)) ^ p :=
    forcingResponse_fixed_order M V r p j w F hM hV hr hr₁ hp (hc.base_small hk)
      (fun _ => potential_bound k _ hk) hF l hl
  have hcoarse (p : ℕ) (hp : 2 ≤ p) (f : ℕ → ℝ)
      (hf : ∀ l, l ≤ j → |f l| ≤ (512 * V * r ^ p) * (r ^ (j - l)) ^ p)
      (l : ℕ) (hl : l ≤ j) : |f l| ≤ (r ^ (j - l)) ^ p := by
    have hc' := fixed_order_coarse V r p hV hr hr₁ hp hc.2
    exact (hf l hl).trans (by simpa only [one_mul] using
      mul_le_mul_of_nonneg_right hc' (pow_nonneg (hB l) p))
  have h₂ : ∀ l, l ≤ j → |rescaledD₂ k q₀ θ L ξ l| ≤ (512 * V * r ^ 2) * (r ^ (j - l)) ^ 2 := by
    apply hresponse 2 (by norm_num)
    intro i _ hi
    have hp := uniform_phiSecond_bound k (rescaledOrbit k q₀ θ L ξ i) hk
    have hd := hfirst i hi.le
    change |phiSecond k (rescaledOrbit k q₀ θ L ξ i) * (rescaledD₁ k q₀ θ L ξ i) ^ 2| ≤ _
    rw [abs_mul, abs_pow]
    calc
      _ ≤ V * (2 * r ^ (j - i)) ^ 2 := by gcongr
      _ ≤ 256 * V * (r ^ (j - i)) ^ 2 := by nlinarith [mul_nonneg hV (sq_nonneg (r ^ (j - i)))]
  have hc₂ := hcoarse 2 (by norm_num) _ h₂
  have h₃ : ∀ l, l ≤ j → |rescaledD₃ k q₀ θ L ξ l| ≤ (512 * V * r ^ 3) * (r ^ (j - l)) ^ 3 := by
    apply hresponse 3 (by norm_num)
    intro i _ hi
    have h := bell₃_bound V (r ^ (j - i))
      (phiThird k (rescaledOrbit k q₀ θ L ξ i)) (phiSecond k (rescaledOrbit k q₀ θ L ξ i))
      (rescaledD₁ k q₀ θ L ξ i) (rescaledD₂ k q₀ θ L ξ i) hV (hB i)
      (uniform_phiThird_bound k _ hk) (uniform_phiSecond_bound k _ hk) (hfirst i hi.le) (hc₂ i hi.le)
    exact h.trans (by nlinarith [mul_nonneg hV (pow_nonneg (hB i) 3)])
  have hc₃ := hcoarse 3 (by norm_num) _ h₃
  have h₄ : ∀ l, l ≤ j → |rescaledD₄ k q₀ θ L ξ l| ≤ (512 * V * r ^ 4) * (r ^ (j - l)) ^ 4 := by
    apply hresponse 4 (by norm_num)
    intro i _ hi
    have h := bell₄_bound V (r ^ (j - i))
      (phiFourth k (rescaledOrbit k q₀ θ L ξ i)) (phiThird k (rescaledOrbit k q₀ θ L ξ i))
      (phiSecond k (rescaledOrbit k q₀ θ L ξ i))
      (rescaledD₁ k q₀ θ L ξ i) (rescaledD₂ k q₀ θ L ξ i) (rescaledD₃ k q₀ θ L ξ i) hV (hB i)
      (uniform_phiFourth_bound k _ hk) (uniform_phiThird_bound k _ hk) (uniform_phiSecond_bound k _ hk)
      (hfirst i hi.le) (hc₂ i hi.le) (hc₃ i hi.le)
    exact h.trans (by nlinarith [mul_nonneg hV (pow_nonneg (hB i) 4)])
  have hc₄ := hcoarse 4 (by norm_num) _ h₄
  have h₅ : ∀ l, l ≤ j → |rescaledD₅ k q₀ θ L ξ l| ≤ (512 * V * r ^ 5) * (r ^ (j - l)) ^ 5 := by
    apply hresponse 5 (by norm_num)
    intro i _ hi
    have h := bell₅_bound V (r ^ (j - i))
      (phiFifth k (rescaledOrbit k q₀ θ L ξ i)) (phiFourth k (rescaledOrbit k q₀ θ L ξ i))
      (phiThird k (rescaledOrbit k q₀ θ L ξ i)) (phiSecond k (rescaledOrbit k q₀ θ L ξ i))
      (rescaledD₁ k q₀ θ L ξ i) (rescaledD₂ k q₀ θ L ξ i) (rescaledD₃ k q₀ θ L ξ i)
      (rescaledD₄ k q₀ θ L ξ i) hV (hB i)
      (uniform_phiFifth_bound k _ hk) (uniform_phiFourth_bound k _ hk)
      (uniform_phiThird_bound k _ hk) (uniform_phiSecond_bound k _ hk)
      (hfirst i hi.le) (hc₂ i hi.le) (hc₃ i hi.le) (hc₄ i hi.le)
    exact h.trans (by nlinarith [mul_nonneg hV (pow_nonneg (hB i) 5)])
  intro l hl
  exact ⟨h₂ l hl, h₃ l hl, h₄ l hl, h₅ l hl⟩

lemma recurrence_pair_backward_step (M : ℝ) (v u : ℕ → ℝ)
    (hM : 1 ≤ M) (hv : ∀ i, |v i| + 1 ≤ M)
    (hu : ∀ n, u (n + 2) = v (n + 1) * u (n + 1) - u n) (n : ℕ) :
    max |u (n + 1)| |u n| ≤ M * max |u (n + 2)| |u (n + 1)| := by
  let N := max |u (n + 2)| |u (n + 1)|
  have hN : 0 ≤ N := (abs_nonneg _).trans (le_max_left _ _)
  have h₁ : |u (n + 1)| ≤ N := le_max_right _ _
  have h₂ : |u (n + 2)| ≤ N := le_max_left _ _
  have hNM : N ≤ M * N := by nlinarith only [mul_nonneg (sub_nonneg.mpr hM) hN]
  apply max_le (h₁.trans hNM)
  have he : u n = v (n + 1) * u (n + 1) - u (n + 2) := by linarith only [hu n]
  rw [he]
  calc
    _ ≤ |v (n + 1) * u (n + 1)| + |u (n + 2)| := abs_sub _ _
    _ = |v (n + 1)| * |u (n + 1)| + |u (n + 2)| := by rw [abs_mul]
    _ ≤ (|v (n + 1)| + 1) * N := by nlinarith only [mul_le_mul_of_nonneg_left h₁ (abs_nonneg (v (n + 1))), h₂]
    _ ≤ M * N := mul_le_mul_of_nonneg_right (hv (n + 1)) hN

lemma recurrence_pair_backward (M : ℝ) (v u : ℕ → ℝ)
    (hM : 1 ≤ M) (hv : ∀ i, |v i| + 1 ≤ M)
    (hu : ∀ n, u (n + 2) = v (n + 1) * u (n + 1) - u n) (d n : ℕ) :
    max |u (n + 1)| |u n| ≤ M ^ d * max |u (n + d + 1)| |u (n + d)| := by
  induction d generalizing n with
  | zero => simp
  | succ d ih =>
    have h := mul_le_mul_of_nonneg_left (ih (n + 1)) (le_trans zero_le_one hM)
    calc
      _ ≤ M * max |u (n + 2)| |u (n + 1)| := recurrence_pair_backward_step M v u hM hv hu n
      _ ≤ M * (M ^ d * max |u (n + 1 + d + 1)| |u (n + 1 + d)|) := h
      _ = M ^ (d + 1) * max |u (n + (d + 1) + 1)| |u (n + (d + 1))| := by
        rw [pow_succ]
        have hn₁ : n + 1 + d + 1 = n + (d + 1) + 1 := by omega
        have hn₂ : n + 1 + d = n + (d + 1) := by omega
        rw [hn₁, hn₂]
        ring

lemma dirichletSolution_backward_bound (M : ℝ) (v : ℕ → ℝ) (j a : ℕ)
    (hM : 1 ≤ M) (hv : ∀ i, |v i| + 1 ≤ M) (hj : tSolution v j ≠ 0) (ha : a < j) :
    |dirichletSolution v j a| ≤ M ^ (j - a - 1) / |tSolution v j| := by
  have hj₁ : 1 ≤ j := by omega
  have he : j - 1 + 1 = j := Nat.sub_add_cancel hj₁
  have h := recurrence_pair_backward M v (dirichletSolution v j) hM hv
    (dirichletSolution_step v j) (j - a - 1) a
  have he₁ : a + (j - a - 1) + 1 = j := by omega
  have he₂ : a + (j - a - 1) = j - 1 := by omega
  rw [he₁, he₂, dirichletSolution_boundary v j hj, abs_zero] at h
  have hr := dirichletSolution_right v (j - 1) (by simpa only [he] using hj)
  rw [he] at hr
  rw [hr, abs_div, abs_one, max_eq_right (div_nonneg zero_le_one (abs_nonneg _))] at h
  exact (le_max_right _ _).trans (h.trans_eq (by simp only [div_eq_mul_inv, one_mul]))

lemma GoodIndex.varied_dirichlet_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a : ℕ) (ha : a < j) :
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    let w := orbitCoefficient k q₀ (θ + ξ / L)
    L * |dirichletSolution w j a| ≤ 2 * growthBase k ^ (j - a - 1) := by
  dsimp only
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let w := orbitCoefficient k q₀ (θ + ξ / L)
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have ht : L / 2 ≤ |tSolution w j| := hg.varied_t_lower hk hc.1 ξ hξ
  have hwpos : 0 < |tSolution w j| := lt_of_lt_of_le (by linarith) ht
  have h := dirichletSolution_backward_bound (growthBase k) w j a hM.le
    (fun _ => potential_bound k _ hk) (abs_pos.mp hwpos) ha
  have h' := (le_div_iff₀ hwpos).mp h
  have hm := mul_le_mul_of_nonneg_left ht (abs_nonneg (dirichletSolution w j a))
  nlinarith only [h', hm]

lemma GoodIndex.varied_green_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a d : ℕ) (ha : a < j) (hd : d < j) :
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    let w := orbitCoefficient k q₀ (θ + ξ / L)
    |greenKernel w j a d| ≤ 4 * growthBase k ^ (j - max a d - 1) *
      (growthBase k ^ (-goodExponent)) ^ (j - min a d) := by
  dsimp only
  let M := growthBase k
  let r := M ^ (-goodExponent)
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let w := orbitCoefficient k q₀ (θ + ξ / L)
  have hM : 1 < M := by have := growthBase_ge_four k hk; dsimp [M]; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have ht := hg.rescaled_derivative hk (by linarith only [hc.1]) ξ hξ (min a d) (by omega)
  have hu : L * |dirichletSolution w j (max a d)| ≤ 2 * M ^ (j - max a d - 1) :=
    hg.varied_dirichlet_bound hk hc ξ hξ (max a d) (max_lt ha hd)
  change |tSolution w (min a d) / L| ≤ 2 * r ^ (j - min a d) at ht
  rw [abs_div, abs_of_pos hL] at ht
  have htp := (div_le_iff₀ hL).mp ht
  have hs := mul_le_mul_of_nonneg_right htp (abs_nonneg (dirichletSolution w j (max a d)))
  have hu' := mul_le_mul_of_nonneg_left hu (show 0 ≤ 2 * r ^ (j - min a d) by
    have hr := (rescaling_ratio_bounds k hk).1; positivity)
  unfold greenKernel
  rw [abs_mul]
  nlinarith only [hs, hu']

section InverseChains
variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [HasSummableGeomSeries R]

lemma hasDerivAt_ringInverse_comp {f : ℝ → R} {f' : R} {x : ℝ}
    (hf : HasDerivAt f f' x) (hu : IsUnit (f x)) :
    HasDerivAt (fun y => Ring.inverse (f y))
      (-(Ring.inverse (f x) * f' * Ring.inverse (f x))) x := by
  obtain ⟨u, hu⟩ := hu
  have hi := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hi
  convert! hi.comp_hasDerivAt x hf using 1
  simp only [neg_apply, ContinuousLinearMap.mulLeftRight_apply, ← hu, Ring.inverse_unit]

omit [HasSummableGeomSeries R] in
lemma hasDerivAt_inverseJet₁ {G B₁ B₂ : ℝ → R} {x : ℝ}
    (hG : HasDerivAt G (inverseJet₁ (G x) (B₁ x)) x)
    (hB : HasDerivAt B₁ (B₂ x) x) :
    HasDerivAt (fun y => inverseJet₁ (G y) (B₁ y))
      (inverseJet₂ (G x) (B₁ x) (B₂ x)) x := by
  convert! ((hG.mul hB).mul hG).neg using 1
  simp only [inverseJet₁, inverseJet₂, Pi.mul_apply]
  noncomm_ring

omit [HasSummableGeomSeries R] in
lemma hasDerivAt_inverseJet₂ {G B₁ B₂ B₃ : ℝ → R} {x : ℝ}
    (hG : HasDerivAt G (inverseJet₁ (G x) (B₁ x)) x)
    (hB₁ : HasDerivAt B₁ (B₂ x) x) (hB₂ : HasDerivAt B₂ (B₃ x) x) :
    HasDerivAt (fun y => inverseJet₂ (G y) (B₁ y) (B₂ y))
      (inverseJet₃ (G x) (B₁ x) (B₂ x) (B₃ x)) x := by
  convert! (((((hasDerivAt_const x (2 : R)).mul hG).mul hB₁).mul hG).mul hB₁).mul hG |>.sub
    ((hG.mul hB₂).mul hG) using 1
  simp only [inverseJet₁, inverseJet₃, Pi.mul_apply]
  noncomm_ring

omit [HasSummableGeomSeries R] in
lemma hasDerivAt_inverseJet₃ {G B₁ B₂ B₃ B₄ : ℝ → R} {x : ℝ}
    (hG : HasDerivAt G (inverseJet₁ (G x) (B₁ x)) x)
    (hB₁ : HasDerivAt B₁ (B₂ x) x) (hB₂ : HasDerivAt B₂ (B₃ x) x)
    (hB₃ : HasDerivAt B₃ (B₄ x) x) :
    HasDerivAt (fun y => inverseJet₃ (G y) (B₁ y) (B₂ y) (B₃ y))
      (inverseJet₄ (G x) (B₁ x) (B₂ x) (B₃ x) (B₄ x)) x := by
  have h₁ := (((((((hasDerivAt_const x (6 : R)).mul hG).mul hB₁).mul hG).mul hB₁).mul hG).mul hB₁).mul hG
  have h₂ := (((((hasDerivAt_const x (3 : R)).mul hG).mul hB₂).mul hG).mul hB₁).mul hG
  have h₃ := (((((hasDerivAt_const x (3 : R)).mul hG).mul hB₁).mul hG).mul hB₂).mul hG
  have h₄ := (hG.mul hB₃).mul hG
  convert! ((h₁.neg.add h₂).add h₃).sub h₄ using 1
  simp only [inverseJet₁, inverseJet₄, Pi.mul_apply]
  noncomm_ring
end InverseChains

lemma path_variation_lower (d : ℕ → ℝ) (n r : ℕ) (hr : r ≤ n) :
    d 0 + d n - 2 * d r ≤ ∑ i ∈ Finset.range n, |d (i + 1) - d i| := by
  induction n generalizing r with
  | zero =>
    have hre : r = 0 := by omega
    subst r
    simp only [Finset.range_zero, Finset.sum_empty]
    linarith
  | succ n ih =>
    rw [Finset.sum_range_succ]
    by_cases hrn : r ≤ n
    · have h := ih r hrn
      have h' := le_abs_self (d (n + 1) - d n)
      linarith
    · have hre : r = n + 1 := by omega
      subst r
      have h := ih n le_rfl
      have h' := neg_le_abs (d (n + 1) - d n)
      linarith

lemma path_max_sum_bound (d : ℕ → ℝ) (n : ℕ) (hd : ∀ i ≤ n, 0 ≤ d i) :
    ∑ i ∈ Finset.range n, max (d i) (d (i + 1)) ≤
      2 * ∑ i ∈ Finset.range (n + 1), d i := by
  have h : ∑ i ∈ Finset.range n, max (d i) (d (i + 1)) ≤
      ∑ i ∈ Finset.range n, (d i + d (i + 1)) := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i < n := Finset.mem_range.mp hi
    exact max_le (by linarith only [hd (i + 1) (by omega)])
      (by linarith only [hd i (by omega)])
  rw [Finset.sum_add_distrib] at h
  have h₁ := Finset.sum_range_succ d n
  have h₂ := Finset.sum_range_succ' d n
  linarith only [h, h₁, h₂, hd 0 (Nat.zero_le n), hd n le_rfl]

lemma inverse_chain_exponent (n : ℕ) (d p : ℕ → ℝ)
    (hd : ∀ i ≤ n, 0 ≤ d i) (hp : ∀ i ≤ n, 1 ≤ p i)
    (hs : ∑ i ∈ Finset.range (n + 1), p i = 4) :
    -1 + d 0 + d n +
      (∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) -
        (99 / 100 : ℝ) * max (d i) (d (i + 1)))) -
      (99 / 100 : ℝ) * (∑ i ∈ Finset.range (n + 1), p i * d i) ≤
    -1 - (47 / 100 : ℝ) * (∑ i ∈ Finset.range (n + 1), p i * d i) := by
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image (Finset.range (n + 1)) d
    (Finset.nonempty_range_iff.mpr (by omega))
  have hrn : r ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hr
  have hv := path_variation_lower d n r hrn
  have hm := path_max_sum_bound d n hd
  have hdw : (∑ i ∈ Finset.range (n + 1), d i) ≤
      ∑ i ∈ Finset.range (n + 1), p i * d i := by
    apply Finset.sum_le_sum
    intro i hi
    have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    nlinarith only [mul_nonneg (sub_nonneg.mpr (hp i hi')) (hd i hi')]
  have hrw : 4 * d r ≤ ∑ i ∈ Finset.range (n + 1), p i * d i := by
    calc
      _ = ∑ i ∈ Finset.range (n + 1), p i * d r := by rw [← Finset.sum_mul, hs]
      _ ≤ _ := Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (hmin i hi)
        (le_trans zero_le_one (hp i (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)))))
  have he : (∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) -
      (99 / 100 : ℝ) * max (d i) (d (i + 1)))) =
      -(∑ i ∈ Finset.range n, |d (i + 1) - d i|) +
        (1 / 100 : ℝ) * (∑ i ∈ Finset.range n, max (d i) (d (i + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rcases le_total (d i) (d (i + 1)) with h | h
    · rw [min_eq_left h, max_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
      ring
    · rw [min_eq_right h, max_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
      ring
  rw [he]
  linarith only [hv, hm, hdw, hrw]

lemma sum_fin_predecessor {n : ℕ} (f : ℕ → ℝ) (hf : f 0 = 0) (a : Fin n) :
    (∑ i : Fin n, if a.val = i.val + 1 then f (i.val + 1) else 0) = f a.val := by
  by_cases ha : a.val = 0
  · simp [ha, hf]
  · let b : Fin n := ⟨a.val - 1, by omega⟩
    have hb : b.val + 1 = a.val := by dsimp [b]; omega
    rw [Finset.sum_eq_single b]
    · simp [hb]
    · intro i _ hi
      have hne : a.val ≠ i.val + 1 := by
        intro he
        apply hi
        apply Fin.ext
        dsimp [b]
        omega
      simp [hne]
    · simp

lemma sum_fin_successor {n : ℕ} (f : ℕ → ℝ) (hf : f (n + 1) = 0) (a : Fin n) :
    (∑ i : Fin n, if i.val = a.val + 1 then f (i.val + 1) else 0) = f (a.val + 2) := by
  by_cases ha : a.val + 1 < n
  · let b : Fin n := ⟨a.val + 1, ha⟩
    rw [Finset.sum_eq_single b]
    · simp [b, Nat.add_assoc]
    · intro i _ hi
      have hne : i.val ≠ a.val + 1 := by
        intro he
        exact hi (Fin.ext he)
      simp [hne]
    · simp
  · have he : a.val + 1 = n := by omega
    have he' : a.val + 2 = n + 1 := by omega
    rw [he', hf]
    apply Finset.sum_eq_zero
    intro i _
    have hne : i.val ≠ a.val + 1 := by omega
    simp [hne]

theorem dirichletMatrix_mul_greenMatrix (v : ℕ → ℝ) (n : ℕ)
    (ht : tSolution v (n + 1) ≠ 0) :
    dirichletMatrix v n * greenMatrix v n = 1 := by
  ext a b
  simp only [Matrix.mul_apply, dirichletMatrix, sub_mul, ite_mul, zero_mul, one_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true, greenMatrix]
  rw [sum_fin_predecessor (fun i => greenKernel v (n + 1) i (b.val + 1))
    (greenKernel_zero v (n + 1) (b.val + 1)) a]
  rw [sum_fin_successor (fun i => greenKernel v (n + 1) i (b.val + 1))
    (greenKernel_boundary v (n + 1) (b.val + 1) ht (by omega)) a]
  rw [greenKernel_jump, Matrix.one_apply]
  simp only [Nat.add_right_cancel_iff, Fin.val_inj]

lemma dirichletMatrix_isUnit (v : ℕ → ℝ) (n : ℕ) (ht : tSolution v (n + 1) ≠ 0) :
    IsUnit (dirichletMatrix v n) := by
  exact isUnit_iff_exists_inv.mpr ⟨greenMatrix v n, dirichletMatrix_mul_greenMatrix v n ht⟩

theorem dirichletMatrix_inverse (v : ℕ → ℝ) (n : ℕ) (ht : tSolution v (n + 1) ≠ 0) :
    Ring.inverse (dirichletMatrix v n) = greenMatrix v n := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact Matrix.inv_eq_right_inv (dirichletMatrix_mul_greenMatrix v n ht)

lemma hasDerivAt_rescaledPotential (k q₀ θ L ξ : ℝ) (a : ℕ) :
    HasDerivAt (fun x => potential k (rescaledOrbit k q₀ θ L x a)) (rescaledV₁ k q₀ θ L ξ a) ξ := by
  exact (hasDerivAt_potential k _).comp ξ (hasDerivAt_rescaledOrbit k q₀ θ L ξ a)

lemma hasDerivAt_rescaledV₁ (k q₀ θ L ξ : ℝ) (a : ℕ) :
    HasDerivAt (fun x => rescaledV₁ k q₀ θ L x a) (rescaledV₂ k q₀ θ L ξ a) ξ := by
  have hp := (hasDerivAt_phiSecond k _).comp ξ (hasDerivAt_rescaledOrbit k q₀ θ L ξ a)
  convert! hp.mul (hasDerivAt_rescaledD₁ k q₀ θ L ξ a) using 1
  simp only [rescaledV₂, Function.comp_apply]
  ring

lemma hasDerivAt_rescaledV₂ (k q₀ θ L ξ : ℝ) (a : ℕ) :
    HasDerivAt (fun x => rescaledV₂ k q₀ θ L x a) (rescaledV₃ k q₀ θ L ξ a) ξ := by
  have hq := hasDerivAt_rescaledOrbit k q₀ θ L ξ a
  have hd₁ := hasDerivAt_rescaledD₁ k q₀ θ L ξ a
  have hd₂ := hasDerivAt_rescaledD₂ k q₀ θ L ξ a
  have hp₂ := (hasDerivAt_phiSecond k _).comp ξ hq
  have hp₃ := (hasDerivAt_phiThird k _).comp ξ hq
  convert! (hp₃.mul (hd₁.pow 2)).add (hp₂.mul hd₂) using 1
  simp only [rescaledV₃, Function.comp_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  ring

lemma hasDerivAt_rescaledV₃ (k q₀ θ L ξ : ℝ) (a : ℕ) :
    HasDerivAt (fun x => rescaledV₃ k q₀ θ L x a) (rescaledV₄ k q₀ θ L ξ a) ξ := by
  have hq := hasDerivAt_rescaledOrbit k q₀ θ L ξ a
  have hd₁ := hasDerivAt_rescaledD₁ k q₀ θ L ξ a
  have hd₂ := hasDerivAt_rescaledD₂ k q₀ θ L ξ a
  have hd₃ := hasDerivAt_rescaledD₃ k q₀ θ L ξ a
  have hp₂ := (hasDerivAt_phiSecond k _).comp ξ hq
  have hp₃ := (hasDerivAt_phiThird k _).comp ξ hq
  have hp₄ := (hasDerivAt_phiFourth k _).comp ξ hq
  convert! ((hp₄.mul (hd₁.pow 3)).add (((hp₃.const_mul 3).mul hd₁).mul hd₂)).add
    (hp₂.mul hd₃) using 1
  simp only [rescaledV₄, Function.comp_apply, Pi.pow_apply, Pi.mul_apply, Nat.reduceSub, Nat.cast_ofNat]
  ring

lemma GoodIndex.rescaled_coarse_high_bounds {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a : ℕ) (ha : a ≤ j) :
    let r := growthBase k ^ (-goodExponent)
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    |rescaledD₂ k q₀ θ L ξ a| ≤ (r ^ (j - a)) ^ 2 ∧
    |rescaledD₃ k q₀ θ L ξ a| ≤ (r ^ (j - a)) ^ 3 ∧
    |rescaledD₄ k q₀ θ L ξ a| ≤ (r ^ (j - a)) ^ 4 ∧
    |rescaledD₅ k q₀ θ L ξ a| ≤ (r ^ (j - a)) ^ 5 := by
  dsimp only
  have hr := rescaling_ratio_bounds k hk
  have hM := growthBase_ge_four k hk
  have hV : 0 ≤ derivativeMajorant * growthBase k := by unfold derivativeMajorant; positivity
  have hs (p : ℕ) (hp : 2 ≤ p) := fixed_order_coarse (derivativeMajorant * growthBase k)
    (growthBase k ^ (-goodExponent)) p hV hr.1.le hr.2 hp hc.2
  have hh := hg.rescaled_high_bounds hk hc ξ hξ a ha
  refine ⟨hh.1.trans ?_, hh.2.1.trans ?_, hh.2.2.1.trans ?_, hh.2.2.2.trans ?_⟩
  all_goals apply mul_le_of_le_one_left (by positivity)
  · exact hs 2 (by omega)
  · exact hs 3 (by omega)
  · exact hs 4 (by omega)
  · exact hs 5 (by omega)

lemma potential_bell_bounds (V B a b c d x y z w : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B)
    (ha : |a| ≤ V) (hb : |b| ≤ V) (hc : |c| ≤ V) (hd : |d| ≤ V)
    (hx : |x| ≤ 2 * B) (hy : |y| ≤ B ^ 2) (hz : |z| ≤ B ^ 3) (hw : |w| ≤ B ^ 4) :
    |a * x| ≤ 2 * V * B ∧
    |b * x ^ 2 + a * y| ≤ 5 * V * B ^ 2 ∧
    |c * x ^ 3 + 3 * b * x * y + a * z| ≤ 15 * V * B ^ 3 ∧
    |d * x ^ 4 + 6 * c * x ^ 2 * y + 3 * b * y ^ 2 + 4 * b * x * z + a * w| ≤ 52 * V * B ^ 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      _ = |a| * |x| := abs_mul _ _
      _ ≤ V * (2 * B) := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ |b * x ^ 2| + |a * y| := abs_add_le _ _
      _ = |b| * |x| ^ 2 + |a| * |y| := by simp only [abs_mul, abs_pow]
      _ ≤ V * (2 * B) ^ 2 + V * B ^ 2 := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ |c * x ^ 3 + 3 * b * x * y| + |a * z| := abs_add_le _ _
      _ ≤ 14 * V * B ^ 3 + V * B ^ 3 := by
        apply add_le_add (bell₃_bound V B c b x y hV hB hc hb hx hy)
        rw [abs_mul]
        gcongr
      _ = _ := by ring
  · calc
      _ ≤ |d * x ^ 4 + 6 * c * x ^ 2 * y + 3 * b * y ^ 2 + 4 * b * x * z| + |a * w| := abs_add_le _ _
      _ ≤ 51 * V * B ^ 4 + V * B ^ 4 := by
        apply add_le_add (bell₄_bound V B d c b x y z hV hB hd hc hb hx hy hz)
        rw [abs_mul]
        gcongr
      _ = _ := by ring

theorem GoodIndex.rescaled_potential_bounds {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a : ℕ) (ha : a ≤ j) :
    let r := growthBase k ^ (-goodExponent)
    let V := derivativeMajorant * growthBase k
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    |rescaledV₁ k q₀ θ L ξ a| ≤ 2 * V * (r ^ (j - a)) ∧
    |rescaledV₂ k q₀ θ L ξ a| ≤ 5 * V * (r ^ (j - a)) ^ 2 ∧
    |rescaledV₃ k q₀ θ L ξ a| ≤ 15 * V * (r ^ (j - a)) ^ 3 ∧
    |rescaledV₄ k q₀ θ L ξ a| ≤ 52 * V * (r ^ (j - a)) ^ 4 := by
  dsimp only
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let q := rescaledOrbit k q₀ θ L ξ a
  have hr := rescaling_ratio_bounds k hk
  have hM := growthBase_ge_four k hk
  have hV : 0 ≤ derivativeMajorant * growthBase k := by unfold derivativeMajorant; positivity
  have hh := hg.rescaled_coarse_high_bounds hk hc ξ hξ a ha
  exact potential_bell_bounds (derivativeMajorant * growthBase k)
    ((growthBase k ^ (-goodExponent)) ^ (j - a))
    (phiSecond k q) (phiThird k q) (phiFourth k q) (phiFifth k q)
    (rescaledD₁ k q₀ θ L ξ a) (rescaledD₂ k q₀ θ L ξ a)
    (rescaledD₃ k q₀ θ L ξ a) (rescaledD₄ k q₀ θ L ξ a) hV (by positivity)
    (uniform_phiSecond_bound k q hk) (uniform_phiThird_bound k q hk)
    (uniform_phiFourth_bound k q hk) (uniform_phiFifth_bound k q hk)
    (hg.rescaled_derivative hk (by linarith only [hc.1]) ξ hξ a ha) hh.1 hh.2.1 hh.2.2.1

open scoped Matrix.Norms.Operator

lemma hasDerivAt_matrix_diagonal {n : ℕ} {v v' : ℝ → Fin n → ℝ} {x : ℝ}
    (hv : ∀ a, HasDerivAt (fun y => v y a) (v' x a) x) :
    HasDerivAt (fun y => Matrix.diagonal (v y)) (Matrix.diagonal (v' x)) x := by
  have hs := HasDerivAt.sum (u := Finset.univ)
    (fun a _ => (hv a).smul_const (Matrix.single a a (1 : ℝ)))
  convert! hs using 1
  · ext y
    simp only [Finset.sum_apply, Matrix.smul_single, smul_eq_mul, mul_one,
      Matrix.sum_single_eq_diagonal]
  · simp only [Matrix.smul_single, smul_eq_mul, mul_one, Matrix.sum_single_eq_diagonal]

lemma hasDerivAt_dirichletMatrix {n : ℕ} {v v' : ℝ → ℕ → ℝ} {x : ℝ}
    (hv : ∀ a : Fin n, HasDerivAt (fun y => v y (a.val + 1)) (v' x (a.val + 1)) x) :
    HasDerivAt (fun y => dirichletMatrix (v y) n)
      (Matrix.diagonal (fun a : Fin n => v' x (a.val + 1))) x := by
  have hd := hasDerivAt_matrix_diagonal (n := n) (v := fun y a => v y (a.val + 1))
    (v' := fun y a => v' y (a.val + 1)) hv
  convert! hd.add_const (dirichletMatrix (fun _ => 0) n) using 1
  ext y a b
  simp only [Matrix.add_apply, Matrix.diagonal_apply, dirichletMatrix]
  split_ifs <;> ring

lemma hasDerivAt_rescaledMatrix (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledMatrix k q₀ θ L x n)
      (rescaledDiagonal rescaledV₁ k q₀ θ L ξ n) ξ := by
  apply hasDerivAt_dirichletMatrix
  intro a
  exact hasDerivAt_rescaledPotential k q₀ θ L ξ (a.val + 1)

lemma hasDerivAt_rescaledDiagonal₁ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledDiagonal rescaledV₁ k q₀ θ L x n)
      (rescaledDiagonal rescaledV₂ k q₀ θ L ξ n) ξ :=
  hasDerivAt_matrix_diagonal (n := n) (x := ξ)
    (v := fun x a => rescaledV₁ k q₀ θ L x (a.val + 1))
    (v' := fun x a => rescaledV₂ k q₀ θ L x (a.val + 1))
    (fun a => hasDerivAt_rescaledV₁ k q₀ θ L ξ (a.val + 1))
lemma hasDerivAt_rescaledDiagonal₂ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledDiagonal rescaledV₂ k q₀ θ L x n)
      (rescaledDiagonal rescaledV₃ k q₀ θ L ξ n) ξ :=
  hasDerivAt_matrix_diagonal (n := n) (x := ξ)
    (v := fun x a => rescaledV₂ k q₀ θ L x (a.val + 1))
    (v' := fun x a => rescaledV₃ k q₀ θ L x (a.val + 1))
    (fun a => hasDerivAt_rescaledV₂ k q₀ θ L ξ (a.val + 1))
lemma hasDerivAt_rescaledDiagonal₃ (k q₀ θ L ξ : ℝ) (n : ℕ) :
    HasDerivAt (fun x => rescaledDiagonal rescaledV₃ k q₀ θ L x n)
      (rescaledDiagonal rescaledV₄ k q₀ θ L ξ n) ξ :=
  hasDerivAt_matrix_diagonal (n := n) (x := ξ)
    (v := fun x a => rescaledV₃ k q₀ θ L x (a.val + 1))
    (v' := fun x a => rescaledV₄ k q₀ θ L x (a.val + 1))
    (fun a => hasDerivAt_rescaledV₃ k q₀ θ L ξ (a.val + 1))

lemma hasDerivAt_rescaledInverse (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    HasDerivAt (fun x => rescaledInverse k q₀ θ L x n) (rescaledInverse₁ k q₀ θ L ξ n) ξ := by
  apply hasDerivAt_ringInverse_comp (hasDerivAt_rescaledMatrix k q₀ θ L ξ n)
  exact dirichletMatrix_isUnit _ _ ht

lemma hasDerivAt_rescaledInverse₁ (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    HasDerivAt (fun x => rescaledInverse₁ k q₀ θ L x n) (rescaledInverse₂ k q₀ θ L ξ n) ξ :=
  hasDerivAt_inverseJet₁
    (G := fun x => rescaledInverse k q₀ θ L x n)
    (B₁ := fun x => rescaledDiagonal rescaledV₁ k q₀ θ L x n)
    (B₂ := fun x => rescaledDiagonal rescaledV₂ k q₀ θ L x n)
    (hasDerivAt_rescaledInverse k q₀ θ L ξ n ht)
    (hasDerivAt_rescaledDiagonal₁ k q₀ θ L ξ n)
lemma hasDerivAt_rescaledInverse₂ (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    HasDerivAt (fun x => rescaledInverse₂ k q₀ θ L x n) (rescaledInverse₃ k q₀ θ L ξ n) ξ :=
  hasDerivAt_inverseJet₂
    (G := fun x => rescaledInverse k q₀ θ L x n)
    (B₁ := fun x => rescaledDiagonal rescaledV₁ k q₀ θ L x n)
    (B₂ := fun x => rescaledDiagonal rescaledV₂ k q₀ θ L x n)
    (B₃ := fun x => rescaledDiagonal rescaledV₃ k q₀ θ L x n)
    (hasDerivAt_rescaledInverse k q₀ θ L ξ n ht)
    (hasDerivAt_rescaledDiagonal₁ k q₀ θ L ξ n) (hasDerivAt_rescaledDiagonal₂ k q₀ θ L ξ n)
lemma hasDerivAt_rescaledInverse₃ (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    HasDerivAt (fun x => rescaledInverse₃ k q₀ θ L x n) (rescaledInverse₄ k q₀ θ L ξ n) ξ :=
  hasDerivAt_inverseJet₃
    (G := fun x => rescaledInverse k q₀ θ L x n)
    (B₁ := fun x => rescaledDiagonal rescaledV₁ k q₀ θ L x n)
    (B₂ := fun x => rescaledDiagonal rescaledV₂ k q₀ θ L x n)
    (B₃ := fun x => rescaledDiagonal rescaledV₃ k q₀ θ L x n)
    (B₄ := fun x => rescaledDiagonal rescaledV₄ k q₀ θ L x n)
    (hasDerivAt_rescaledInverse k q₀ θ L ξ n ht)
    (hasDerivAt_rescaledDiagonal₁ k q₀ θ L ξ n) (hasDerivAt_rescaledDiagonal₂ k q₀ θ L ξ n)
    (hasDerivAt_rescaledDiagonal₃ k q₀ θ L ξ n)

theorem rescaledInverse_eq_greenMatrix (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    rescaledInverse k q₀ θ L ξ n = greenMatrix (orbitCoefficient k q₀ (θ + ξ / L)) n :=
  dirichletMatrix_inverse _ _ ht

lemma geometric_positive_tail (q : ℝ) (hq : 0 ≤ q) (hq' : q ≤ 1 / 2) (n : ℕ) :
    (∑ d ∈ Finset.range n, q ^ (d + 1)) ≤ 2 * q := by
  calc
    _ = q * ∑ d ∈ Finset.range n, q ^ d := by simp only [Finset.mul_sum, pow_succ']
    _ ≤ q * ∑ d ∈ Finset.range n, (1 / 2 : ℝ) ^ d := by gcongr
    _ ≤ q * 2 := mul_le_mul_of_nonneg_left (sum_geometric_two_le n) hq
    _ = _ := mul_comm _ _

lemma weighted_geometric_sites (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1 / 2)
    (p n : ℕ) (hp : 1 ≤ p) :
    (∑ a : Fin n, z ^ (p * (n - a.val))) ≤ 2 * z ^ p := by
  have hzp : z ^ p ≤ 1 / 2 := by
    calc
      z ^ p ≤ z ^ 1 := pow_le_pow_of_le_one hz (by linarith) hp
      _ = z := pow_one z
      _ ≤ _ := hz'
  calc
    _ = ∑ a ∈ Finset.range n, (z ^ p) ^ (n - a) := by
      rw [← Fin.sum_univ_eq_sum_range]
      simp only [pow_mul]
    _ = ∑ a ∈ Finset.range n, (z ^ p) ^ (a + 1) := by
      conv_rhs => rw [← Finset.sum_range_reflect (fun a => (z ^ p) ^ (a + 1)) n]
      apply Finset.sum_congr rfl
      intro a ha
      have ha' := Finset.mem_range.mp ha
      congr 1
      omega
    _ ≤ _ := geometric_positive_tail (z ^ p) (pow_nonneg hz _) hzp n

lemma inverse_chain_site_sum (z : ℝ) (hz : 0 ≤ z) (hz' : z ≤ 1 / 2)
    (s n : ℕ) (p : Fin s → ℕ) (hp : ∀ i, 1 ≤ p i) (hs : ∑ i, p i = 4) :
    (∑ a : Fin s → Fin n, ∏ i, z ^ (p i * (n - (a i).val))) ≤ 2 ^ s * z ^ 4 := by
  rw [← Fintype.prod_sum (fun (i : Fin s) (a : Fin n) => z ^ (p i * (n - a.val)))]
  calc
    _ ≤ ∏ i, (2 * z ^ p i) := Finset.prod_le_prod
      (fun i _ => Finset.sum_nonneg (fun a _ => pow_nonneg hz _))
      (fun i _ => weighted_geometric_sites z hz hz' (p i) n (hp i))
    _ = _ := by rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, Finset.prod_pow_eq_pow_sum, hs]

lemma prod_const_rpow (M C : ℝ) (hM : 0 < M) (f : ℕ → ℝ) (n : ℕ) :
    (∏ i ∈ Finset.range n, C * M ^ f i) = C ^ n * M ^ (∑ i ∈ Finset.range n, f i) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
    ← Real.rpow_sum_of_pos hM]

lemma scalar_inverse_chain_bound (M A : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (n : ℕ) (d p v g : ℕ → ℝ) (u w : ℝ)
    (hd : ∀ i ≤ n, 0 ≤ d i) (hp : ∀ i ≤ n, 1 ≤ p i)
    (hs : ∑ i ∈ Finset.range (n + 1), p i = 4)
    (hu : |u| ≤ 2 * M ^ (d 0 - 1)) (hw : |w| ≤ 2 * M ^ (d n - 1))
    (hv : ∀ i ≤ n, |v i| ≤ A * M ^ (1 - (99 / 100 : ℝ) * p i * d i))
    (hg : ∀ i < n, |g i| ≤ 4 * M ^ (min (d i) (d (i + 1)) - 1 -
      (99 / 100 : ℝ) * max (d i) (d (i + 1)))) :
    |u * (∏ i ∈ Finset.range (n + 1), v i) * (∏ i ∈ Finset.range n, g i) * w| ≤
      (4 * A) ^ (n + 1) * M ^ (-1 - (47 / 100 : ℝ) *
        (∑ i ∈ Finset.range (n + 1), p i * d i)) := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hvp : (∏ i ∈ Finset.range (n + 1), |v i|) ≤
      ∏ i ∈ Finset.range (n + 1), A * M ^ (1 - (99 / 100 : ℝ) * p i * d i) :=
    Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => hv i (by
      have := Finset.mem_range.mp hi; omega))
  have hgp : (∏ i ∈ Finset.range n, |g i|) ≤
      ∏ i ∈ Finset.range n, 4 * M ^ (min (d i) (d (i + 1)) - 1 -
        (99 / 100 : ℝ) * max (d i) (d (i + 1))) :=
    Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i hi => hg i (Finset.mem_range.mp hi))
  have he := inverse_chain_exponent n d p hd hp hs
  calc
    _ = |u| * (∏ i ∈ Finset.range (n + 1), |v i|) *
        (∏ i ∈ Finset.range n, |g i|) * |w| := by simp only [abs_mul, Finset.abs_prod]
    _ ≤ (2 * M ^ (d 0 - 1)) *
        (∏ i ∈ Finset.range (n + 1), A * M ^ (1 - (99 / 100 : ℝ) * p i * d i)) *
        (∏ i ∈ Finset.range n, 4 * M ^ (min (d i) (d (i + 1)) - 1 -
          (99 / 100 : ℝ) * max (d i) (d (i + 1)))) * (2 * M ^ (d n - 1)) := by
      gcongr
    _ = (4 * A) ^ (n + 1) * M ^ (-1 + d 0 + d n +
        (∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) -
          (99 / 100 : ℝ) * max (d i) (d (i + 1)))) -
        (99 / 100 : ℝ) * (∑ i ∈ Finset.range (n + 1), p i * d i)) := by
      rw [prod_const_rpow M A hMp, prod_const_rpow M 4 hMp]
      have hvsum : (∑ i ∈ Finset.range (n + 1), (1 - (99 / 100 : ℝ) * p i * d i)) =
          (n + 1 : ℝ) - (99 / 100 : ℝ) * ∑ i ∈ Finset.range (n + 1), p i * d i := by
        simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        ring
      have hgsum : (∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) - 1 -
          (99 / 100 : ℝ) * max (d i) (d (i + 1)))) =
          (∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) -
            (99 / 100 : ℝ) * max (d i) (d (i + 1)))) - n := by
        have hn : (n : ℝ) = ∑ _i ∈ Finset.range n, (1 : ℝ) := by simp
        rw [hn, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [hvsum, hgsum, mul_pow, pow_succ 4 n]
      rw [show (2 * M ^ (d 0 - 1)) *
          (A ^ (n + 1) * M ^ ((n + 1 : ℝ) - 99 / 100 * ∑ i ∈ Finset.range (n + 1), p i * d i)) *
          (4 ^ n * M ^ ((∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) - 99 / 100 * max (d i) (d (i + 1)))) - n)) *
          (2 * M ^ (d n - 1)) =
          (4 ^ n * 4 * A ^ (n + 1)) *
            (M ^ (d 0 - 1) * M ^ ((n + 1 : ℝ) - 99 / 100 * ∑ i ∈ Finset.range (n + 1), p i * d i) *
            M ^ ((∑ i ∈ Finset.range n, (min (d i) (d (i + 1)) - 99 / 100 * max (d i) (d (i + 1)))) - n) *
            M ^ (d n - 1)) by ring]
      simp only [← Real.rpow_add hMp]
      congr 2
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM he) (by positivity)

lemma finTotal_sum {n : ℕ} (f : Fin n → ℝ) :
    (∑ i ∈ Finset.range n, finTotal f i) = ∑ i, f i := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [finTotal_coe]
lemma finTotal_prod {n : ℕ} (f : Fin n → ℝ) :
    (∏ i ∈ Finset.range n, finTotal f i) = ∏ i, f i := by
  rw [← Fin.prod_univ_eq_prod_range]
  simp only [finTotal_coe]

lemma finite_inverse_chain_bound (M A : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (s : ℕ) (d p v : Fin (s + 1) → ℝ) (g : Fin s → ℝ) (u w : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hp : ∀ i, 1 ≤ p i) (hs : ∑ i, p i = 4)
    (hu : |u| ≤ 2 * M ^ (d 0 - 1)) (hw : |w| ≤ 2 * M ^ (d (Fin.last s) - 1))
    (hv : ∀ i, |v i| ≤ A * M ^ (1 - (99 / 100 : ℝ) * p i * d i))
    (hg : ∀ i, |g i| ≤ 4 * M ^ (min (d i.castSucc) (d i.succ) - 1 -
      (99 / 100 : ℝ) * max (d i.castSucc) (d i.succ))) :
    |u * (∏ i, v i) * (∏ i, g i) * w| ≤ (4 * A) ^ (s + 1) *
      M ^ (-1 - (47 / 100 : ℝ) * ∑ i, p i * d i) := by
  have hz : finTotal d 0 = d 0 := by simp [finTotal]
  have hl : finTotal d s = d (Fin.last s) := by simp [finTotal, Fin.last]
  have h := scalar_inverse_chain_bound M A hM hA s (finTotal d) (finTotal p)
    (finTotal v) (finTotal g) u w
    (fun i hi => by simpa only [finTotal, dite_eq_left (by omega : i < s + 1)] using hd ⟨i, by omega⟩)
    (fun i hi => by simpa only [finTotal, dite_eq_left (by omega : i < s + 1)] using hp ⟨i, by omega⟩)
    (by rw [finTotal_sum]; exact hs) (by rwa [hz]) (by rwa [hl])
    (fun i hi => by simpa only [finTotal, dite_eq_left (by omega : i < s + 1)] using hv ⟨i, by omega⟩)
    (fun i hi => by
      simpa only [finTotal, dite_eq_left hi, dite_eq_left (by omega : i < s + 1),
        dite_eq_left (by omega : i + 1 < s + 1), Fin.castSucc_mk, Fin.succ_mk] using hg ⟨i, hi⟩)
  rw [finTotal_prod, finTotal_prod] at h
  have hsum : (∑ i ∈ Finset.range (s + 1), finTotal p i * finTotal d i) = ∑ i, p i * d i := by
    rw [← Fin.sum_univ_eq_sum_range]
    simp only [finTotal_coe]
  rwa [hsum] at h

lemma inverse_chain_rpow_factor (M : ℝ) (hM : 0 < M) (s n : ℕ)
    (p : Fin s → ℕ) (a : Fin s → Fin n) :
    M ^ (-1 - (47 / 100 : ℝ) * ∑ i, (p i : ℝ) * (n - (a i).val)) =
      M ^ (-1 : ℝ) * ∏ i, (M ^ (-(47 / 100 : ℝ))) ^ (p i * (n - (a i).val)) := by
  have hd (i : Fin s) : ((n - (a i).val : ℕ) : ℝ) = n - (a i).val :=
    Nat.cast_sub (Nat.le_of_lt (a i).isLt)
  rw [sub_eq_add_neg, Real.rpow_add hM]
  congr 1
  rw [show -(47 / 100 * ∑ i, (p i : ℝ) * (n - (a i).val)) =
      ∑ i, (-(47 / 100 : ℝ)) * ((p i : ℝ) * (n - (a i).val)) by
    rw [← Finset.mul_sum]; ring]
  rw [Real.rpow_sum_of_pos hM]
  apply Finset.prod_congr rfl
  intro i _
  rw [← Real.rpow_mul_natCast hM.le, Nat.cast_mul, hd]

lemma fourth_chain_sum_bound (M A L : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (hz : M ^ (-(47 / 100 : ℝ)) ≤ 1 / 2) (s n : ℕ)
    (p : Fin (s + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hs : ∑ i, p i = 4)
    (U : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin (s + 1) → Fin n → ℝ)
    (hU : ∀ a, |L * U a| ≤ 2 * M ^ ((n : ℝ) - a.val - 1))
    (hG : ∀ a b, |G a b| ≤ 4 * M ^
      (min ((n : ℝ) - a.val) ((n : ℝ) - b.val) - 1 -
        (99 / 100 : ℝ) * max ((n : ℝ) - a.val) ((n : ℝ) - b.val)))
    (hV : ∀ i a, |v i a| ≤ A * M ^
      (1 - (99 / 100 : ℝ) * p i * ((n : ℝ) - a.val))) :
    L ^ 2 * |∑ a : Fin (s + 1) → Fin n, boundaryChain U G s v a| ≤
      (8 * A) ^ (s + 1) * M ^ (-(72 / 25 : ℝ)) := by
  have hMp : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hterm (a : Fin (s + 1) → Fin n) :
      L ^ 2 * |boundaryChain U G s v a| ≤
        (4 * A) ^ (s + 1) * M ^ (-1 : ℝ) *
          ∏ i, (M ^ (-(47 / 100 : ℝ))) ^ (p i * (n - (a i).val)) := by
    have h := finite_inverse_chain_bound M A hM hA s
      (fun i => (n : ℝ) - (a i).val) (fun i => (p i : ℝ))
      (fun i => v i (a i)) (fun i => G (a i.castSucc) (a i.succ))
      (L * U (a 0)) (L * U (a (Fin.last s)))
      (fun i => sub_nonneg.mpr (by exact_mod_cast (a i).isLt.le))
      (fun i => by exact_mod_cast hp i) (by exact_mod_cast hs)
      (hU _) (hU _) (fun i => hV i _) (fun i => hG _ _)
    rw [inverse_chain_rpow_factor M hMp] at h
    have he : (L * U (a 0)) * (∏ i, v i (a i)) *
        (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * (L * U (a (Fin.last s))) =
        L ^ 2 * boundaryChain U G s v a := by unfold boundaryChain; ring
    rw [he, abs_mul, abs_of_nonneg (sq_nonneg L)] at h
    simpa only [mul_assoc] using h
  calc
    _ ≤ L ^ 2 * ∑ a : Fin (s + 1) → Fin n, |boundaryChain U G s v a| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (sq_nonneg L)
    _ = ∑ a : Fin (s + 1) → Fin n, L ^ 2 * |boundaryChain U G s v a| :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ a : Fin (s + 1) → Fin n, (4 * A) ^ (s + 1) * M ^ (-1 : ℝ) *
        ∏ i, (M ^ (-(47 / 100 : ℝ))) ^ (p i * (n - (a i).val)) :=
      Finset.sum_le_sum (fun a _ => hterm a)
    _ = ((4 * A) ^ (s + 1) * M ^ (-1 : ℝ)) *
        ∑ a : Fin (s + 1) → Fin n,
          ∏ i, (M ^ (-(47 / 100 : ℝ))) ^ (p i * (n - (a i).val)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((4 * A) ^ (s + 1) * M ^ (-1 : ℝ)) *
        (2 ^ (s + 1) * (M ^ (-(47 / 100 : ℝ))) ^ (4 : ℕ)) :=
      mul_le_mul_of_nonneg_left
        (inverse_chain_site_sum _ (Real.rpow_nonneg hMp.le _) hz _ _ p hp hs) (by positivity)
    _ = _ := by
      have he : (M ^ (-(47 / 100 : ℝ))) ^ (4 : ℕ) = M ^ (-(47 / 25 : ℝ)) := by
        rw [← Real.rpow_mul_natCast hMp.le]
        norm_num
      rw [he]
      calc
        _ = (8 * A) ^ (s + 1) * (M ^ (-1 : ℝ) * M ^ (-(47 / 25 : ℝ))) := by
          rw [show (8 * A) ^ (s + 1) = (4 * A) ^ (s + 1) * 2 ^ (s + 1) by
            rw [← mul_pow]; congr 1; ring]
          ring
        _ = _ := by rw [← Real.rpow_add hMp]; norm_num

lemma sum_fin_functions_cons {α : Type*} [Fintype α] (s : ℕ)
    (f : (Fin (s + 1) → α) → ℝ) :
    ∑ a, f a = ∑ a₀, ∑ a : Fin s → α, f (Fin.cons a₀ a) := by
  rw [← (Fin.consEquiv (fun _ : Fin (s + 1) => α)).sum_comp f,
    Fintype.sum_prod_type]
  rfl

lemma matrixPath_cons {n s : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin (s + 1 + 1) → Fin n → ℝ) (a₀ : Fin n) (a : Fin (s + 1) → Fin n)
    (row col : Fin n) :
    matrixPath G (s + 1) v ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n)) row col =
      G row a₀ * v 0 a₀ * matrixPath G s (fun i => v i.succ) a a₀ col := by
  have hV : (∏ i : Fin (s + 1 + 1), v i ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i)) =
      v 0 a₀ * ∏ i : Fin (s + 1), v i.succ (a i) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have hG : (∏ i : Fin (s + 1), G ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i.castSucc) ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i.succ)) =
      G a₀ (a 0) * ∏ i : Fin s, G (a i.castSucc) (a i.succ) := by
    rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.castSucc_succ, Fin.cons_zero, Fin.cons_succ]
  change G row ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) 0) * (∏ i, v i ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i)) *
      (∏ i : Fin (s + 1), G ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i.castSucc) ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) i.succ)) *
      G ((Fin.cons a₀ a : Fin (s + 1 + 1) → Fin n) (Fin.last (s + 1))) col =
    G row a₀ * v 0 a₀ * (G a₀ (a 0) * (∏ i, v i.succ (a i)) *
      (∏ i : Fin s, G (a i.castSucc) (a i.succ)) * G (a (Fin.last s)) col)
  rw [hV, hG]
  have hl : Fin.last (s + 1) = (Fin.last s).succ := rfl
  rw [hl, Fin.cons_zero, Fin.cons_succ]
  ring

lemma matrixChain_entry {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ) (row col : Fin n) :
    matrixChain G s v row col = ∑ a, matrixPath G s v a row col := by
  induction s generalizing row col with
  | zero =>
    rw [matrixChain, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rw [sum_fin_functions_cons]
    apply Finset.sum_congr rfl
    intro a₀ _
    simp [matrixPath]
  | succ s ih =>
    rw [matrixChain, Matrix.mul_apply]
    simp only [Matrix.mul_diagonal]
    rw [sum_fin_functions_cons]
    apply Finset.sum_congr rfl
    intro a₀ _
    rw [ih, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    exact (matrixPath_cons G v a₀ a row col).symm

lemma matrixChain_boundary {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (U : Fin n → ℝ) (b : Fin n) (hrow : ∀ a, G b a = U a) (hcol : ∀ a, G a b = U a)
    (s : ℕ) (v : Fin (s + 1) → Fin n → ℝ) :
    matrixChain G s v b b = ∑ a, boundaryChain U G s v a := by
  rw [matrixChain_entry]
  apply Finset.sum_congr rfl
  intro a _
  simp only [matrixPath, boundaryChain, hrow, hcol]

lemma fourth_chain_entry_bound (M A L : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (hz : M ^ (-(47 / 100 : ℝ)) ≤ 1 / 2) (s n : ℕ)
    (p : Fin (s + 1) → ℕ) (hp : ∀ i, 1 ≤ p i) (hs : ∑ i, p i = 4)
    (U : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (b : Fin n)
    (hrow : ∀ a, G b a = U a) (hcol : ∀ a, G a b = U a)
    (v : Fin (s + 1) → Fin n → ℝ)
    (hU : ∀ a, |L * U a| ≤ 2 * M ^ ((n : ℝ) - a.val - 1))
    (hG : ∀ a b, |G a b| ≤ 4 * M ^
      (min ((n : ℝ) - a.val) ((n : ℝ) - b.val) - 1 -
        (99 / 100 : ℝ) * max ((n : ℝ) - a.val) ((n : ℝ) - b.val)))
    (hV : ∀ i a, |v i a| ≤ A * M ^
      (1 - (99 / 100 : ℝ) * p i * ((n : ℝ) - a.val))) :
    L ^ 2 * |matrixChain G s v b b| ≤ (8 * A) ^ (s + 1) * M ^ (-(72 / 25 : ℝ)) := by
  rw [matrixChain_boundary G U b hrow hcol]
  exact fourth_chain_sum_bound M A L hM hA hz s n p hp hs U G v hU hG hV

lemma inverseJet₄_chains {n : ℕ} (G : Matrix (Fin n) (Fin n) ℝ)
    (v₁ v₂ v₃ v₄ : Fin n → ℝ) :
    inverseJet₄ G (Matrix.diagonal v₁) (Matrix.diagonal v₂)
      (Matrix.diagonal v₃) (Matrix.diagonal v₄) =
      (24 : ℕ) • matrixChain G 3 ![v₁, v₁, v₁, v₁] -
      (12 : ℕ) • matrixChain G 2 ![v₂, v₁, v₁] -
      (12 : ℕ) • matrixChain G 2 ![v₁, v₂, v₁] -
      (12 : ℕ) • matrixChain G 2 ![v₁, v₁, v₂] +
      (6 : ℕ) • matrixChain G 1 ![v₂, v₂] +
      (4 : ℕ) • matrixChain G 1 ![v₃, v₁] +
      (4 : ℕ) • matrixChain G 1 ![v₁, v₃] - matrixChain G 0 ![v₄] := by
  simp [inverseJet₄, matrixChain, nsmul_eq_mul, ← mul_assoc]

lemma absolute_polynomial_bound (L t C₄ C₃ C₂ C₁ a b c d e f g h : ℝ)
    (hL : 0 ≤ L)
    (ha : L * |a| ≤ C₄ * t) (hb : L * |b| ≤ C₃ * t)
    (hc : L * |c| ≤ C₃ * t) (hd : L * |d| ≤ C₃ * t)
    (he : L * |e| ≤ C₂ * t) (hf : L * |f| ≤ C₂ * t)
    (hg : L * |g| ≤ C₂ * t) (hh : L * |h| ≤ C₁ * t) :
    L * |24 * a - 12 * b - 12 * c - 12 * d + 6 * e + 4 * f + 4 * g - h| ≤
      (24 * C₄ + 36 * C₃ + 14 * C₂ + C₁) * t := by
  have habs : |24 * a - 12 * b - 12 * c - 12 * d + 6 * e + 4 * f + 4 * g - h| ≤
      24 * |a| + 12 * |b| + 12 * |c| + 12 * |d| + 6 * |e| + 4 * |f| + 4 * |g| + |h| := by
    calc
      _ ≤ |24 * a| + |12 * b| + |12 * c| + |12 * d| + |6 * e| + |4 * f| + |4 * g| + |h| := by
        have h₁ := abs_sub (24 * a) (12 * b)
        have h₂ := abs_sub (24 * a - 12 * b) (12 * c)
        have h₃ := abs_sub (24 * a - 12 * b - 12 * c) (12 * d)
        have h₄ := abs_add_le (24 * a - 12 * b - 12 * c - 12 * d) (6 * e)
        have h₅ := abs_add_le (24 * a - 12 * b - 12 * c - 12 * d + 6 * e) (4 * f)
        have h₆ := abs_add_le (24 * a - 12 * b - 12 * c - 12 * d + 6 * e + 4 * f) (4 * g)
        have h₇ := abs_sub (24 * a - 12 * b - 12 * c - 12 * d + 6 * e + 4 * f + 4 * g) h
        linarith only [h₁, h₂, h₃, h₄, h₅, h₆, h₇]
      _ = _ := by norm_num [abs_mul]
  have hm := mul_le_mul_of_nonneg_left habs hL
  nlinarith only [hm, ha, hb, hc, hd, he, hf, hg, hh]

lemma inverseJet₄_boundary_bound (M A L : ℝ) (hM : 1 ≤ M) (hA : 0 ≤ A)
    (hz : M ^ (-(47 / 100 : ℝ)) ≤ 1 / 2) (n : ℕ)
    (U : Fin n → ℝ) (G : Matrix (Fin n) (Fin n) ℝ) (b : Fin n)
    (hrow : ∀ a, G b a = U a) (hcol : ∀ a, G a b = U a)
    (v : Fin 4 → Fin n → ℝ)
    (hU : ∀ a, |L * U a| ≤ 2 * M ^ ((n : ℝ) - a.val - 1))
    (hG : ∀ a b, |G a b| ≤ 4 * M ^
      (min ((n : ℝ) - a.val) ((n : ℝ) - b.val) - 1 -
        (99 / 100 : ℝ) * max ((n : ℝ) - a.val) ((n : ℝ) - b.val)))
    (hV : ∀ i a, |v i a| ≤ A * M ^
      (1 - (99 / 100 : ℝ) * (i.val + 1) * ((n : ℝ) - a.val))) :
    L ^ 2 * |inverseJet₄ G (Matrix.diagonal (v 0)) (Matrix.diagonal (v 1))
        (Matrix.diagonal (v 2)) (Matrix.diagonal (v 3)) b b| ≤
      inverseFourthMajorant A * M ^ (-(72 / 25 : ℝ)) := by
  have H (s : ℕ) (q : Fin (s + 1) → Fin 4) (hq : ∑ i, ((q i).val + 1) = 4) :
      L ^ 2 * |matrixChain G s (fun i => v (q i)) b b| ≤
        (8 * A) ^ (s + 1) * M ^ (-(72 / 25 : ℝ)) := by
    apply fourth_chain_entry_bound M A L hM hA hz s n (fun i => (q i).val + 1)
      (fun _ => Nat.succ_le_succ (Nat.zero_le _)) hq U G b hrow hcol _ hU hG
    intro i a
    simpa only [Nat.cast_add, Nat.cast_one] using hV (q i) a
  have h₁ := H 3 ![0, 0, 0, 0] (by decide)
  have h₂ := H 2 ![1, 0, 0] (by decide)
  have h₃ := H 2 ![0, 1, 0] (by decide)
  have h₄ := H 2 ![0, 0, 1] (by decide)
  have h₅ := H 1 ![1, 1] (by decide)
  have h₆ := H 1 ![2, 0] (by decide)
  have h₇ := H 1 ![0, 2] (by decide)
  have h₈ := H 0 ![3] (by decide)
  have comp {m : ℕ} (q : Fin m → Fin 4) (w : Fin m → (Fin n → ℝ))
      (hw : ∀ i, v (q i) = w i) : (fun i => v (q i)) = w := funext hw
  rw [comp _ ![v 0, v 0, v 0, v 0] (by intro i; fin_cases i <;> rfl)] at h₁
  rw [comp _ ![v 1, v 0, v 0] (by intro i; fin_cases i <;> rfl)] at h₂
  rw [comp _ ![v 0, v 1, v 0] (by intro i; fin_cases i <;> rfl)] at h₃
  rw [comp _ ![v 0, v 0, v 1] (by intro i; fin_cases i <;> rfl)] at h₄
  rw [comp _ ![v 1, v 1] (by intro i; fin_cases i <;> rfl)] at h₅
  rw [comp _ ![v 2, v 0] (by intro i; fin_cases i <;> rfl)] at h₆
  rw [comp _ ![v 0, v 2] (by intro i; fin_cases i <;> rfl)] at h₇
  rw [comp _ ![v 3] (by intro i; fin_cases i; rfl)] at h₈
  rw [inverseJet₄_chains]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply]
  simp only [nsmul_eq_mul, Nat.cast_ofNat]
  exact absolute_polynomial_bound (L ^ 2) (M ^ (-(72 / 25 : ℝ)))
    ((8 * A) ^ 4) ((8 * A) ^ 3) ((8 * A) ^ 2) (8 * A) _ _ _ _ _ _ _ _
    (sq_nonneg _) h₁ h₂ h₃ h₄ h₅ h₆ h₇ (by simpa only [Nat.zero_add, pow_one] using h₈)

lemma decay_nat_power (M c : ℝ) (hM : 0 < M) (n p : ℕ) :
    ((M ^ (-c)) ^ n) ^ p = M ^ (-c * (p : ℝ) * (n : ℝ)) := by
  rw [← pow_mul, ← Real.rpow_mul_natCast hM.le, Nat.cast_mul]
  congr 1
  ring
lemma potential_power_identity (M A c : ℝ) (hM : 0 < M) (n p : ℕ) :
    A * M * ((M ^ (-c)) ^ n) ^ p = A * M ^ (1 - c * (p : ℝ) * (n : ℝ)) := by
  rw [decay_nat_power M c hM]
  rw [show 1 - c * (p : ℝ) * (n : ℝ) = 1 + (-c * (p : ℝ) * (n : ℝ)) by ring,
    Real.rpow_add hM, Real.rpow_one, mul_assoc]
lemma natural_distance_power (M : ℝ) (n a : ℕ) (ha : a < n) :
    M ^ (n - a - 1) = M ^ ((n : ℝ) - a - 1) := by
  rw [← Real.rpow_natCast, Nat.cast_sub (by omega : 1 ≤ n - a),
    Nat.cast_sub (Nat.le_of_lt ha), Nat.cast_one]
lemma successive_distance_power (M : ℝ) (n a : ℕ) (ha : a < n) :
    M ^ (n + 1 - (a + 1) - 1) = M ^ ((n : ℝ) - a - 1) := by
  rw [Nat.add_sub_add_right]
  exact natural_distance_power M n a ha
lemma green_power_identity (M c : ℝ) (hM : 0 < M) (n a b : ℕ) (ha : a < n) (hb : b < n) :
    M ^ (n + 1 - max (a + 1) (b + 1) - 1) *
      (M ^ (-c)) ^ (n + 1 - min (a + 1) (b + 1)) =
    M ^ (min ((n : ℝ) - a) ((n : ℝ) - b) - 1 -
      c * max ((n : ℝ) - a) ((n : ℝ) - b)) := by
  rcases le_total a b with h | h
  · have hab : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [max_eq_right (Nat.add_le_add_right h 1), min_eq_left (Nat.add_le_add_right h 1),
      successive_distance_power M n b hb, Nat.add_sub_add_right,
      ← Real.rpow_mul_natCast hM.le, Nat.cast_sub ha.le,
      ← Real.rpow_add hM, min_eq_right (by linarith : (n : ℝ) - b ≤ n - a),
      max_eq_left (by linarith : (n : ℝ) - b ≤ n - a)]
    congr 1
    ring
  · have hab : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [max_eq_left (Nat.add_le_add_right h 1), min_eq_right (Nat.add_le_add_right h 1),
      successive_distance_power M n a ha, Nat.add_sub_add_right,
      ← Real.rpow_mul_natCast hM.le, Nat.cast_sub hb.le,
      ← Real.rpow_add hM, min_eq_left (by linarith : (n : ℝ) - a ≤ n - b),
      max_eq_right (by linarith : (n : ℝ) - a ≤ n - b)]
    congr 1
    ring

lemma GoodIndex.varied_dirichlet_real_bound {k q₀ θ b : ℝ} {n : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b (n + 1)) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a : Fin n) :
    let L := |tSolution (orbitCoefficient k q₀ θ) (n + 1)|
    let w := orbitCoefficient k q₀ (θ + ξ / L)
    |L * dirichletSolution w (n + 1) (a.val + 1)| ≤
      2 * growthBase k ^ ((n : ℝ) - a.val - 1) := by
  dsimp only
  rw [abs_mul, abs_abs]
  have h := hg.varied_dirichlet_bound hk hc ξ hξ (a.val + 1) (by omega)
  simpa only [successive_distance_power _ _ _ a.isLt] using h

lemma GoodIndex.varied_green_real_bound {k q₀ θ b : ℝ} {n : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b (n + 1)) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (a d : Fin n) :
    let L := |tSolution (orbitCoefficient k q₀ θ) (n + 1)|
    let w := orbitCoefficient k q₀ (θ + ξ / L)
    |greenMatrix w n a d| ≤ 4 * growthBase k ^
      (min ((n : ℝ) - a.val) ((n : ℝ) - d.val) - 1 -
        (99 / 100 : ℝ) * max ((n : ℝ) - a.val) ((n : ℝ) - d.val)) := by
  dsimp only
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have h := hg.varied_green_bound hk hc ξ hξ (a.val + 1) (d.val + 1) (by omega) (by omega)
  dsimp only at h
  rw [mul_assoc, green_power_identity (growthBase k) goodExponent hM n a.val d.val a.isLt d.isLt] at h
  simpa only [greenMatrix, goodExponent] using h

lemma inflate_potential_bound (x C A M c : ℝ) (d p : ℕ) (hM : 0 < M)
    (hA : 0 ≤ A) (hC : C ≤ 52)
    (hx : |x| ≤ C * (A * M) * ((M ^ (-c)) ^ d) ^ p) :
    |x| ≤ (52 * A) * M ^ (1 - c * (p : ℝ) * (d : ℝ)) := by
  calc
    _ ≤ C * (A * M) * ((M ^ (-c)) ^ d) ^ p := hx
    _ ≤ 52 * (A * M) * ((M ^ (-c)) ^ d) ^ p := by gcongr
    _ = _ := by rw [← mul_assoc, potential_power_identity M (52 * A) c hM d p]

lemma GoodIndex.rescaled_potential_real_bound {k q₀ θ b : ℝ} {n : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b (n + 1)) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (i : Fin 4) (a : Fin n) :
    let L := |tSolution (orbitCoefficient k q₀ θ) (n + 1)|
    |rescaledPotentialJets k q₀ θ L ξ n i a| ≤
      (52 * derivativeMajorant) * growthBase k ^
        (1 - (99 / 100 : ℝ) * (i.val + 1) * ((n : ℝ) - a.val)) := by
  dsimp only
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hA : 0 ≤ derivativeMajorant := by unfold derivativeMajorant; positivity
  have h := hg.rescaled_potential_bounds hk hc ξ hξ (a.val + 1) (by omega)
  have hd : ((n + 1 - (a.val + 1) : ℕ) : ℝ) = (n : ℝ) - a.val := by
    rw [Nat.add_sub_add_right, Nat.cast_sub a.isLt.le]
  have H (x C : ℝ) (p : ℕ) (hC : C ≤ 52)
      (hx : |x| ≤ C * (derivativeMajorant * growthBase k) *
        ((growthBase k ^ (-goodExponent)) ^ (n + 1 - (a.val + 1))) ^ p) :
      |x| ≤ (52 * derivativeMajorant) * growthBase k ^
        (1 - (99 / 100 : ℝ) * (p : ℝ) * ((n : ℝ) - a.val)) := by
    have hh := inflate_potential_bound x C derivativeMajorant (growthBase k) goodExponent
      (n + 1 - (a.val + 1)) p hM hA hC hx
    simpa only [hd, goodExponent] using hh
  fin_cases i
  · simpa [rescaledPotentialJets, show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num] using H _ 2 1 (by norm_num) (by simpa only [pow_one] using h.1)
  · simpa [rescaledPotentialJets, show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num] using H _ 5 2 (by norm_num) h.2.1
  · simpa [rescaledPotentialJets, show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num] using H _ 15 3 (by norm_num) h.2.2.1
  · simpa [rescaledPotentialJets, show (1 : ℝ) + 1 = 2 by norm_num, show (2 : ℝ) + 1 = 3 by norm_num, show (3 : ℝ) + 1 = 4 by norm_num] using H _ 52 4 le_rfl h.2.2.2

lemma greenMatrix_first_row {n : ℕ} (v : ℕ → ℝ) (a : Fin (n + 1)) :
    greenMatrix v (n + 1) 0 a = dirichletSolution v (n + 2) (a.val + 1) := by
  simp only [greenMatrix, greenKernel, Fin.val_zero, zero_add,
    min_eq_left (by omega : 1 ≤ a.val + 1), max_eq_right (by omega : 1 ≤ a.val + 1),
    tSolution, linearSolution, one_mul]

lemma greenMatrix_first_col {n : ℕ} (v : ℕ → ℝ) (a : Fin (n + 1)) :
    greenMatrix v (n + 1) a 0 = dirichletSolution v (n + 2) (a.val + 1) := by
  change greenKernel _ _ _ _ = _
  rw [greenKernel_symm]
  exact greenMatrix_first_row v a

theorem GoodIndex.rescaled_inverse_fourth_bound {k q₀ θ b : ℝ} {n : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b (n + 2)) (hk : 0 ≤ k)
    (hc : HigherControl k) (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    let L := |tSolution (orbitCoefficient k q₀ θ) (n + 2)|
    L ^ 2 * |rescaledInverse₄ k q₀ θ L ξ (n + 1) 0 0| ≤
      inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(72 / 25 : ℝ)) := by
  dsimp only
  let L := |tSolution (orbitCoefficient k q₀ θ) (n + 2)|
  let w := orbitCoefficient k q₀ (θ + ξ / L)
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have ht : tSolution w (n + 2) ≠ 0 := by
    have hh : L / 2 ≤ |tSolution w (n + 2)| := hg.varied_t_lower hk hc.1 ξ hξ
    exact abs_pos.mp (by linarith)
  have he := rescaledInverse_eq_greenMatrix k q₀ θ L ξ (n + 1) ht
  unfold rescaledInverse₄
  rw [he]
  exact inverseJet₄_boundary_bound (growthBase k) (52 * derivativeMajorant) L hM.le
    (by unfold derivativeMajorant; positivity) hz (n + 1)
    (fun a => dirichletSolution w (n + 2) (a.val + 1)) (greenMatrix w (n + 1)) 0
    (greenMatrix_first_row w) (greenMatrix_first_col w) (rescaledPotentialJets k q₀ θ L ξ (n + 1))
    (hg.varied_dirichlet_real_bound hk hc ξ hξ) (hg.varied_green_real_bound hk hc ξ hξ)
    (hg.rescaled_potential_real_bound hk hc ξ hξ)

lemma continuous_linearSolution {v : ℝ → ℕ → ℝ} (hv : ∀ n, Continuous (fun x => v x n))
    (a b : ℝ) (n : ℕ) : Continuous (fun x => linearSolution (v x) a b n) := by
  induction n using Nat.twoStepInduction with
  | zero => exact continuous_const
  | one => exact continuous_const
  | more n h₀ h₁ => exact ((hv (n + 1)).mul h₁).sub h₀

lemma continuous_orbitCoefficient (k q₀ : ℝ) (n : ℕ) :
    Continuous (fun x => orbitCoefficient k q₀ x n) := by
  exact (continuous_iff_continuousAt.mpr (fun z => (hasDerivAt_potential k z).continuousAt)).comp
    (continuous_liftedOrbit k q₀ n)

lemma continuous_rescaled_tSolution (k q₀ θ L : ℝ) (j : ℕ) :
    Continuous (fun ξ => tSolution (orbitCoefficient k q₀ (θ + ξ / L)) j) := by
  exact (continuous_linearSolution (continuous_orbitCoefficient k q₀) 0 1 j).comp
    (continuous_const.add (continuous_id.div_const L))

lemma iteratedDeriv_of_jets (s : Set ℝ) (hs : IsOpen s) (f : ℕ → ℝ → ℝ) (n : ℕ)
    (hd : ∀ i < n, ∀ x ∈ s, HasDerivAt (f i) (f (i + 1) x) x) :
    ∀ i ≤ n, ∀ x ∈ s, iteratedDeriv i (f 0) x = f i x := by
  intro i
  induction i with
  | zero => intros; rfl
  | succ i ih =>
    intro hi x hx
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv i (f 0) =ᶠ[nhds x] f i := by
      filter_upwards [hs.eventually_mem hx] with y hy
      exact ih (by omega) y hy
    rw [he.deriv_eq]
    exact (hd i (by omega) x hx).deriv

lemma hasDerivAt_matrix_entry {n : ℕ} {f : ℝ → Matrix (Fin n) (Fin n) ℝ}
    {f' : Matrix (Fin n) (Fin n) ℝ} {x : ℝ} (hf : HasDerivAt f f' x) (a b : Fin n) :
    HasDerivAt (fun y => f y a b) (f' a b) x := by
  exact (matrixEntryCLM n a b).hasFDerivAt.comp_hasDerivAt x hf

lemma iteratedDeriv_rescaledInverse_entry (k q₀ θ L ξ : ℝ) (n : ℕ) (a b : Fin n)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 1) ≠ 0) :
    iteratedDeriv 4 (fun x => rescaledInverse k q₀ θ L x n a b) ξ =
      rescaledInverse₄ k q₀ θ L ξ n a b := by
  let g : ℕ → ℝ → ℝ := fun i => match i with
    | 0 => fun x => rescaledInverse k q₀ θ L x n a b
    | 1 => fun x => rescaledInverse₁ k q₀ θ L x n a b
    | 2 => fun x => rescaledInverse₂ k q₀ θ L x n a b
    | 3 => fun x => rescaledInverse₃ k q₀ θ L x n a b
    | _ => fun x => rescaledInverse₄ k q₀ θ L x n a b
  let s : Set ℝ := {x | tSolution (orbitCoefficient k q₀ (θ + x / L)) (n + 1) ≠ 0}
  have hs : IsOpen s := isOpen_ne.preimage (continuous_rescaled_tSolution k q₀ θ L (n + 1))
  have hd : ∀ i < 4, ∀ x ∈ s, HasDerivAt (g i) (g (i + 1) x) x := by
    intro i hi x hx
    interval_cases i
    · exact hasDerivAt_matrix_entry (hasDerivAt_rescaledInverse k q₀ θ L x n hx) a b
    · exact hasDerivAt_matrix_entry (hasDerivAt_rescaledInverse₁ k q₀ θ L x n hx) a b
    · exact hasDerivAt_matrix_entry (hasDerivAt_rescaledInverse₂ k q₀ θ L x n hx) a b
    · exact hasDerivAt_matrix_entry (hasDerivAt_rescaledInverse₃ k q₀ θ L x n hx) a b
  exact iteratedDeriv_of_jets s hs g 4 hd 4 le_rfl ξ ht

lemma rescaledInverse_boundary (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 2) ≠ 0) :
    rescaledInverse k q₀ θ L ξ (n + 1) 0 0 =
      boundaryValue (orbitCoefficient k q₀ (θ + ξ / L)) (n + 2) := by
  rw [rescaledInverse_eq_greenMatrix _ _ _ _ _ _ ht, greenMatrix_first_row]
  rfl

lemma iteratedDeriv_boundaryValue (k q₀ θ L ξ : ℝ) (n : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) (n + 2) ≠ 0) :
    iteratedDeriv 4 (fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) (n + 2)) ξ =
      rescaledInverse₄ k q₀ θ L ξ (n + 1) 0 0 := by
  have he : (fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) (n + 2))
      =ᶠ[nhds ξ] (fun x => rescaledInverse k q₀ θ L x (n + 1) 0 0) := by
    filter_upwards [(continuous_rescaled_tSolution k q₀ θ L (n + 2)).continuousAt.eventually_ne ht]
      with x hx
    exact (rescaledInverse_boundary k q₀ θ L x n hx).symm
  rw [he.iteratedDeriv_eq 4]
  exact iteratedDeriv_rescaledInverse_entry k q₀ θ L ξ (n + 1) 0 0 ht

theorem GoodIndex.boundary_fourth_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    L ^ 2 * |iteratedDeriv 4 (fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) j) ξ| ≤
      inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(14 / 5 : ℝ)) := by
  dsimp only
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hA : 0 ≤ inverseFourthMajorant (52 * derivativeMajorant) := by
    unfold inverseFourthMajorant derivativeMajorant; positivity
  rcases j with _ | j
  · simp [boundaryValue, sSolution, tSolution, linearSolution]
    positivity
  rcases j with _ | n
  · simp [boundaryValue, sSolution, tSolution, linearSolution]
    positivity
  have hL := abs_pos.mpr (hg.t_ne_zero hM)
  have ht : tSolution (orbitCoefficient k q₀ (θ + ξ / |tSolution (orbitCoefficient k q₀ θ) (n + 2)|))
      (n + 2) ≠ 0 := by
    apply abs_pos.mp
    have hh := hg.varied_t_lower hk hc.1 ξ hξ
    linarith
  rw [iteratedDeriv_boundaryValue _ _ _ _ _ _ ht]
  exact (hg.rescaled_inverse_fourth_bound hk hc hz ξ hξ).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hM.le (by norm_num)) hA)

lemma eventually_chain_ratio_small :
    ∀ᶠ k : ℝ in Filter.atTop, growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2 := by
  have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 47 / 100 by norm_num)).comp tendsto_growthBase
  exact (h.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / 2 by norm_num))).mono (fun _ h => h.le)

lemma hasDerivAt_scalarReciprocalJet {d : ℕ → ℝ → ℝ} {x : ℝ}
    (hd : ∀ i < 4, HasDerivAt (d i) (d (i + 1) x) x) (h₀ : d 0 x ≠ 0)
    (i : ℕ) (hi : i < 4) :
    HasDerivAt (fun y => scalarReciprocalJet i (fun p => d p y))
      (scalarReciprocalJet (i + 1) (fun p => d p x)) x := by
  have hG : HasDerivAt (fun y => (d 0 y)⁻¹) (inverseJet₁ (d 0 x)⁻¹ (d 1 x)) x := by
    convert! (hd 0 (by omega)).inv h₀ using 1
    simp only [inverseJet₁, div_eq_mul_inv]
    ring
  interval_cases i
  · exact hG
  · exact hasDerivAt_inverseJet₁ hG (hd 1 (by omega))
  · exact hasDerivAt_inverseJet₂ hG (hd 1 (by omega)) (hd 2 (by omega))
  · exact hasDerivAt_inverseJet₃ hG (hd 1 (by omega)) (hd 2 (by omega)) (hd 3 (by omega))

lemma hasDerivAt_scalarProductJet {n d : ℕ → ℝ → ℝ} {x : ℝ}
    (hn : ∀ i < 4, HasDerivAt (n i) (n (i + 1) x) x)
    (hd : ∀ i < 4, HasDerivAt (d i) (d (i + 1) x) x) (i : ℕ) (hi : i < 4) :
    HasDerivAt (fun y => scalarProductJet i (fun p => n p y) (fun p => d p y))
      (scalarProductJet (i + 1) (fun p => n p x) (fun p => d p x)) x := by
  have hn₀ := hn 0 (by omega); have hn₁ := hn 1 (by omega)
  have hn₂ := hn 2 (by omega); have hn₃ := hn 3 (by omega)
  have hd₀ := hd 0 (by omega); have hd₁ := hd 1 (by omega)
  have hd₂ := hd 2 (by omega); have hd₃ := hd 3 (by omega)
  interval_cases i
  · exact hn₀.mul hd₀
  · convert! (hn₁.mul hd₀).add (hn₀.mul hd₁) using 1
    simp only [scalarProductJet, Nat.reduceAdd]
    ring
  · convert! ((hn₂.mul hd₀).add ((hn₁.const_mul 2).mul hd₁)).add (hn₀.mul hd₂)
      using 1
    simp only [scalarProductJet, Nat.reduceAdd]
    ring
  · convert! (((hn₃.mul hd₀).add ((hn₂.const_mul 3).mul hd₁)).add
      ((hn₁.const_mul 3).mul hd₂)).add (hn₀.mul hd₃)
      using 1
    simp only [scalarProductJet, Nat.reduceAdd]
    ring

lemma scalarReciprocalJet_bound (d : ℕ → ℝ) (hd₀ : 1 / 2 ≤ |d 0|)
    (hd : ∀ i, 1 ≤ i → i ≤ 4 → |d i| ≤ 2) (i : ℕ) (hi : i ≤ 4) :
    |scalarReciprocalJet i d| ≤ 20000 := by
  have hG : |(d 0)⁻¹| ≤ 2 := by
    rw [abs_inv, inv_le_iff_one_le_mul₀ (by linarith : 0 < |d 0|)]
    linarith
  have h₁ := hd 1 (by omega) (by omega)
  have h₂ := hd 2 (by omega) (by omega)
  have h₃ := hd 3 (by omega) (by omega)
  have h₄ := hd 4 (by omega) (by omega)
  interval_cases i
  · exact hG.trans (by norm_num)
  · simp only [scalarReciprocalJet, inverseJet₁, abs_neg, abs_mul]
    calc
      |(d 0)⁻¹| * |d 1| * |(d 0)⁻¹| ≤ 2 * 2 * 2 := by gcongr
      _ ≤ 20000 := by norm_num
  · simp only [scalarReciprocalJet, inverseJet₂]
    calc
      _ ≤ |2 * (d 0)⁻¹ * d 1 * (d 0)⁻¹ * d 1 * (d 0)⁻¹| + |(d 0)⁻¹ * d 2 * (d 0)⁻¹| := abs_sub _ _
      _ ≤ 2 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        gcongr
      _ ≤ 20000 := by norm_num
  · simp only [scalarReciprocalJet, inverseJet₃]
    calc
      _ ≤ |6 * (d 0)⁻¹ * d 1 * (d 0)⁻¹ * d 1 * (d 0)⁻¹ * d 1 * (d 0)⁻¹| +
          |3 * (d 0)⁻¹ * d 2 * (d 0)⁻¹ * d 1 * (d 0)⁻¹| +
          |3 * (d 0)⁻¹ * d 1 * (d 0)⁻¹ * d 2 * (d 0)⁻¹| + |(d 0)⁻¹ * d 3 * (d 0)⁻¹| := by
        grw [abs_sub, abs_add_le, abs_add_le]; rw [abs_neg]
      _ ≤ 6 * 2 * 2 * 2 * 2 * 2 * 2 * 2 + 3 * 2 * 2 * 2 * 2 * 2 +
          3 * 2 * 2 * 2 * 2 * 2 + 2 * 2 * 2 := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
          abs_of_pos (by norm_num : (0 : ℝ) < 3)]
        gcongr
      _ ≤ 20000 := by norm_num
  · have he : inverseJet₄ (d 0)⁻¹ (d 1) (d 2) (d 3) (d 4) =
        24 * ((d 0)⁻¹)^5 * (d 1)^4 - 36 * ((d 0)⁻¹)^4 * (d 1)^2 * d 2 +
        6 * ((d 0)⁻¹)^3 * (d 2)^2 + 8 * ((d 0)⁻¹)^3 * d 1 * d 3 - ((d 0)⁻¹)^2 * d 4 := by
      unfold inverseJet₄; ring
    simp only [scalarReciprocalJet]
    rw [he]
    calc
      _ ≤ |24 * ((d 0)⁻¹)^5 * (d 1)^4| + |36 * ((d 0)⁻¹)^4 * (d 1)^2 * d 2| +
        |6 * ((d 0)⁻¹)^3 * (d 2)^2| + |8 * ((d 0)⁻¹)^3 * d 1 * d 3| + |((d 0)⁻¹)^2 * d 4| := by
        grw [abs_sub, abs_add_le, abs_add_le, abs_sub]
      _ ≤ 24 * 2^5 * 2^4 + 36 * 2^4 * 2^2 * 2 + 6 * 2^3 * 2^2 +
        8 * 2^3 * 2 * 2 + 2^2 * 2 := by
        simp only [abs_mul, abs_pow, abs_of_pos (by norm_num : (0 : ℝ) < 24),
          abs_of_pos (by norm_num : (0 : ℝ) < 36), abs_of_pos (by norm_num : (0 : ℝ) < 6),
          abs_of_pos (by norm_num : (0 : ℝ) < 8)]
        gcongr
      _ ≤ 20000 := by norm_num

lemma scalarProductJet_bound (n d : ℕ → ℝ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hn : ∀ i ≤ 4, |n i| ≤ B) (hd : ∀ i ≤ 4, |d i| ≤ C) (i : ℕ) (hi : i ≤ 4) :
    |scalarProductJet i n d| ≤ 16 * B * C := by
  have h₀ := hn 0 (by omega); have h₁ := hn 1 (by omega); have h₂ := hn 2 (by omega)
  have h₃ := hn 3 (by omega); have h₄ := hn 4 (by omega)
  have g₀ := hd 0 (by omega); have g₁ := hd 1 (by omega); have g₂ := hd 2 (by omega)
  have g₃ := hd 3 (by omega); have g₄ := hd 4 (by omega)
  interval_cases i <;> simp only [scalarProductJet]
  · rw [abs_mul]
    exact (mul_le_mul h₀ g₀ (abs_nonneg _) hB).trans (by nlinarith [mul_nonneg hB hC])
  · calc
      _ ≤ |n 1 * d 0| + |n 0 * d 1| := abs_add_le _ _
      _ ≤ B * C + B * C := by simp only [abs_mul]; gcongr
      _ ≤ 16 * B * C := by nlinarith [mul_nonneg hB hC]
  · calc
      _ ≤ |n 2 * d 0| + |2 * n 1 * d 1| + |n 0 * d 2| := by grw [abs_add_le, abs_add_le]
      _ ≤ B * C + 2 * B * C + B * C := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; gcongr
      _ ≤ 16 * B * C := by nlinarith [mul_nonneg hB hC]
  · calc
      _ ≤ |n 3 * d 0| + |3 * n 2 * d 1| + |3 * n 1 * d 2| + |n 0 * d 3| := by
        grw [abs_add_le, abs_add_le, abs_add_le]
      _ ≤ B * C + 3 * B * C + 3 * B * C + B * C := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]; gcongr
      _ ≤ 16 * B * C := by nlinarith [mul_nonneg hB hC]
  · calc
      _ ≤ |n 4 * d 0| + |4 * n 3 * d 1| + |6 * n 2 * d 2| + |4 * n 1 * d 3| + |n 0 * d 4| := by
        grw [abs_add_le, abs_add_le, abs_add_le, abs_add_le]
      _ ≤ B * C + 4 * B * C + 6 * B * C + 4 * B * C + B * C := by
        simp only [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4),
          abs_of_pos (by norm_num : (0 : ℝ) < 6)]; gcongr
      _ = 16 * B * C := by ring

lemma hasDerivAt_rescaledTJet (k q₀ θ L ξ : ℝ) (l p : ℕ) (hp : p < 4) :
    HasDerivAt (fun x => rescaledTJet p k q₀ θ L x l) (rescaledTJet (p + 1) k q₀ θ L ξ l) ξ := by
  interval_cases p
  · exact hasDerivAt_rescaledD₁ k q₀ θ L ξ l
  · exact hasDerivAt_rescaledD₂ k q₀ θ L ξ l
  · exact hasDerivAt_rescaledD₃ k q₀ θ L ξ l
  · exact hasDerivAt_rescaledD₄ k q₀ θ L ξ l

lemma GoodIndex.rescaledTJet_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (l : ℕ) (hl : l ≤ j)
    (p : ℕ) (hp : p ≤ 4) :
    |rescaledTJet p k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| ξ l| ≤
      2 * (growthBase k ^ (-goodExponent)) ^ (j - l) := by
  let r := growthBase k ^ (-goodExponent)
  let V := derivativeMajorant * growthBase k
  have hr : 0 ≤ r := (rescaling_ratio_bounds k hk).1.le
  have hr₁ : r ≤ 1 := (rescaling_ratio_bounds k hk).2
  have hV : 0 ≤ V := mul_nonneg derivativeMajorant_pos.le
    (by have := growthBase_ge_four k hk; linarith)
  have hB : 0 ≤ r ^ (j - l) := pow_nonneg hr _
  have hB₁ : r ^ (j - l) ≤ 1 := pow_le_one₀ hr hr₁
  have hcoarse (i : ℕ) (hi : 2 ≤ i) (z : ℝ)
      (hz : |z| ≤ (512 * V * r ^ i) * (r ^ (j - l)) ^ i) : |z| ≤ 2 * r ^ (j - l) := by
    have hc' := fixed_order_coarse V r i hV hr hr₁ hi hc.2
    have hp' : (r ^ (j - l)) ^ i ≤ r ^ (j - l) := by
      simpa only [pow_one] using pow_le_pow_of_le_one hB hB₁ (show 1 ≤ i by omega)
    calc
      |z| ≤ (512 * V * r ^ i) * (r ^ (j - l)) ^ i := hz
      _ ≤ 1 * r ^ (j - l) := mul_le_mul hc' hp' (pow_nonneg hB _) zero_le_one
      _ ≤ 2 * r ^ (j - l) := by linarith
  have hh := hg.rescaled_high_bounds hk hc ξ hξ l hl
  interval_cases p
  · exact hg.rescaled_derivative hk (by linarith only [hc.1]) ξ hξ l hl
  · exact hcoarse 2 (by omega) _ hh.1
  · exact hcoarse 3 (by omega) _ hh.2.1
  · exact hcoarse 4 (by omega) _ hh.2.2.1
  · exact hcoarse 5 (by omega) _ hh.2.2.2

lemma GoodIndex.rescaledD₁_terminal_lower {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    1 / 2 ≤ |rescaledD₁ k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| ξ j| := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL := abs_pos.mpr (hg.t_ne_zero hM)
  have ht := hg.varied_t_lower hk hc.1 ξ hξ
  rw [rescaledD₁, abs_div, abs_abs, le_div_iff₀ hL]
  linarith

lemma terminalQuotient_eq (k q₀ θ L ξ : ℝ) (j : ℕ) (hL : L ≠ 0) :
    terminalQuotient k q₀ θ L ξ j =
      rescaledTJet 0 k q₀ θ L ξ (j - 1) * scalarReciprocalJet 0 (fun p => rescaledTJet p k q₀ θ L ξ j) := by
  simp only [terminalQuotient, rescaledTJet, scalarReciprocalJet, rescaledD₁]
  rw [← div_eq_mul_inv, div_div_div_cancel_right₀ hL]

lemma iteratedDeriv_terminalQuotient (k q₀ θ L ξ : ℝ) (j p : ℕ) (hp : p ≤ 4)
    (hL : L ≠ 0) (ht : rescaledD₁ k q₀ θ L ξ j ≠ 0) :
    iteratedDeriv p (fun x => terminalQuotient k q₀ θ L x j) ξ =
      scalarProductJet p (fun i => rescaledTJet i k q₀ θ L ξ (j - 1))
        (fun i => scalarReciprocalJet i (fun v => rescaledTJet v k q₀ θ L ξ j)) := by
  let s : Set ℝ := {x | rescaledD₁ k q₀ θ L x j ≠ 0}
  have hs : IsOpen s := isOpen_ne.preimage (continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_rescaledD₁ k q₀ θ L x j).continuousAt))
  let g : ℕ → ℝ → ℝ := fun i x =>
    scalarProductJet i (fun v => rescaledTJet v k q₀ θ L x (j - 1))
      (fun v => scalarReciprocalJet v (fun u => rescaledTJet u k q₀ θ L x j))
  have hg : ∀ i < 4, ∀ x ∈ s, HasDerivAt (g i) (g (i + 1) x) x := by
    intro i hi x hx
    exact hasDerivAt_scalarProductJet
      (fun v hv => hasDerivAt_rescaledTJet k q₀ θ L x (j - 1) v hv)
      (fun v hv => hasDerivAt_scalarReciprocalJet
        (fun u hu => hasDerivAt_rescaledTJet k q₀ θ L x j u hu) hx v hv) i hi
  have he : (fun x => terminalQuotient k q₀ θ L x j) = g 0 :=
    funext (fun x => terminalQuotient_eq k q₀ θ L x j hL)
  rw [he]
  exact iteratedDeriv_of_jets s hs g 4 hg p hp ξ ht

theorem GoodIndex.quotient_derivatives {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (ξ : ℝ) (hξ : |ξ| ≤ 1) (p : ℕ) (hp : p ≤ 4) :
    |iteratedDeriv p (fun x => terminalQuotient k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| x j) ξ| ≤
      640000 * growthBase k ^ (-goodExponent) := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL := abs_pos.mpr (hg.t_ne_zero hM)
  have ht := hg.rescaledD₁_terminal_lower hk hc ξ hξ
  have ht₀ : rescaledD₁ k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| ξ j ≠ 0 := by
    apply abs_pos.mp; linarith
  rw [iteratedDeriv_terminalQuotient _ _ _ _ _ _ _ hp hL.ne' ht₀]
  have hn : ∀ i ≤ 4, |rescaledTJet i k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| ξ (j - 1)| ≤
      2 * growthBase k ^ (-goodExponent) := by
    intro i hi
    have hh := hg.rescaledTJet_bound hk hc ξ hξ (j - 1) (by omega) i hi
    have he : j - (j - 1) = 1 := by have := hg.1; omega
    simpa only [he, pow_one] using hh
  have hd : ∀ i ≤ 4, |rescaledTJet i k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| ξ j| ≤ 2 := by
    intro i hi
    simpa only [Nat.sub_self, pow_zero, mul_one] using hg.rescaledTJet_bound hk hc ξ hξ j le_rfl i hi
  have hr := (rescaling_ratio_bounds k hk).1.le
  have h := scalarProductJet_bound _ _ (2 * growthBase k ^ (-goodExponent)) 20000
    (by positivity) (by norm_num) hn (fun i hi => scalarReciprocalJet_bound _ ht
      (fun v _ hv => hd v hv) i hi) p hp
  convert h using 1
  ring

lemma analytic_zeros_finite {f : ℝ → ℝ} (hf : AnalyticOnNhd ℝ f univ)
    (hn : ∃ x, f x ≠ 0) {K : Set ℝ} (hK : IsCompact K) :
    {x ∈ K | f x = 0}.Finite := by
  rcases hf.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_univ with hz | hz
  · obtain ⟨x, hx⟩ := hn
    exact False.elim (hx (hz (mem_univ x)))
  · have hh := hK.finite_sdiff_of_mem_codiscreteWithin
      (Filter.codiscreteWithin_mono (subset_univ K) hz)
    convert hh using 1
    ext x
    simp

lemma analytic_eq_of_positive_measure {f g : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f univ) (hg : AnalyticOnNhd ℝ g univ)
    {K S : Set ℝ} (hK : IsCompact K) (hSK : S ⊆ K)
    (hm : volume S ≠ 0) (he : EqOn f g S) : f = g := by
  by_contra hn
  have hx : ∃ x, (f - g) x ≠ 0 := by
    simpa only [Pi.sub_apply, sub_ne_zero] using Function.ne_iff.mp hn
  have hz := analytic_zeros_finite (hf.sub hg) hx hK
  have hsub : S ⊆ {x ∈ K | (f - g) x = 0} := by
    intro x hx
    exact ⟨hSK hx, sub_eq_zero.mpr (he hx)⟩
  exact hm (measure_mono_null hsub (hz.measure_zero volume))

lemma analytic_affine_cosine (z b : ℝ) :
    AnalyticOnNhd ℝ (fun h => Real.cos (2 * Real.pi * (z + b * h))) univ := by
  intro x _
  exact (Real.analyticAt_cos).comp
    (analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))

lemma analytic_affine_sine (z b : ℝ) :
    AnalyticOnNhd ℝ (fun h => Real.sin (2 * Real.pi * (z + b * h))) univ := by
  intro x _
  exact (Real.analyticAt_sin).comp
    (analyticAt_const.mul (analyticAt_const.add (analyticAt_const.mul analyticAt_id)))

lemma polynomial_reciprocal_affine_obstruction (p : Polynomial ℝ) (a b : ℝ) (hb : b ≠ 0) :
    ¬ ∀ h : ℝ, p.eval h * (a + b * h) = 1 := by
  intro he
  have h := he (-a / b)
  have hr : a + b * (-a / b) = 0 := by field_simp; ring
  rw [hr, mul_zero] at h
  norm_num at h

lemma cosine_zero_sine_nonzero {x : ℝ} (hx : Real.cos x = 0) : Real.sin x ≠ 0 := by
  have h := Real.cos_sq_add_sin_sq x
  rw [hx] at h
  intro hs
  rw [hs] at h
  norm_num at h

lemma cosine_root_spacing (a r : ℝ) (hr : r ≠ 0) (hle : |r| ≤ 1)
    (hroots : ∀ x : ℝ, Real.cos (2 * Real.pi * x) = 0 →
      Real.cos (2 * Real.pi * (a + r * x)) = 0) : |r| = 1 := by
  have h₀ := hroots (1 / 4) (by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two])
  have h₁ := hroots (3 / 4) (by
    rw [show 2 * Real.pi * (3 / 4) = Real.pi / 2 + Real.pi by ring,
      Real.cos_add_pi, Real.cos_pi_div_two, neg_zero])
  have hang : 2 * Real.pi * (a + r * (3 / 4)) =
      2 * Real.pi * (a + r * (1 / 4)) + Real.pi * r := by ring
  rw [hang, Real.cos_add, h₀, zero_mul, zero_sub] at h₁
  have hs : Real.sin (Real.pi * r) = 0 :=
    (mul_eq_zero.mp (neg_eq_zero.mp h₁)).resolve_left (cosine_zero_sine_nonzero h₀)
  by_contra he
  have hlt : |r| < 1 := lt_of_le_of_ne hle he
  have hb := abs_lt.mp hlt
  have hz := (Real.sin_eq_zero_iff_of_lt_of_lt (by nlinarith [Real.pi_pos])
    (by nlinarith [Real.pi_pos])).mp hs
  exact hr ((mul_eq_zero.mp hz).resolve_left Real.pi_ne_zero)

lemma cosine_roots_same_frequency (a r : ℝ) (hr : |r| = 1)
    (hroot : Real.cos (2 * Real.pi * (a + r * (1 / 4))) = 0) :
    (Real.cos (2 * Real.pi * a)) ^ 2 = 1 ∧
    ∀ x : ℝ, Real.cos (2 * Real.pi * (a + r * x)) =
      Real.cos (2 * Real.pi * a) * Real.cos (2 * Real.pi * x) := by
  have hor : r = 1 ∨ r = -1 := (abs_eq (by norm_num)).mp hr
  have hs : Real.sin (2 * Real.pi * a) = 0 := by
    rcases hor with hr | hr
    · rw [hr, show 2 * Real.pi * (a + 1 * (1 / 4)) =
        2 * Real.pi * a + Real.pi / 2 by ring, Real.cos_add_pi_div_two] at hroot
      exact neg_eq_zero.mp hroot
    · rw [hr, show 2 * Real.pi * (a + -1 * (1 / 4)) =
        2 * Real.pi * a - Real.pi / 2 by ring, Real.cos_sub_pi_div_two] at hroot
      exact hroot
  constructor
  · simpa only [hs, zero_pow (by decide : 2 ≠ 0), add_zero] using
      Real.cos_sq_add_sin_sq (2 * Real.pi * a)
  · intro x
    rcases hor with hr | hr
    · rw [hr, show 2 * Real.pi * (a + 1 * x) =
        2 * Real.pi * a + 2 * Real.pi * x by ring, Real.cos_add, hs]
      ring
    · rw [hr, show 2 * Real.pi * (a + -1 * x) =
        2 * Real.pi * a - 2 * Real.pi * x by ring, Real.cos_sub, hs]
      ring

lemma two_secants_polynomial_limit (p : Polynomial ℝ) (a r A B : ℝ)
    (hr : r ≠ 0) (hle : |r| ≤ 1) (hA : 0 < A) (hB : 0 < B)
    (hid : ∀ x : ℝ,
      p.eval x * Real.cos (2 * Real.pi * x) * Real.cos (2 * Real.pi * (a + r * x)) =
        A * Real.cos (2 * Real.pi * (a + r * x)) + B * Real.cos (2 * Real.pi * x)) :
    |r| = 1 ∧ A = B ∧
      ∀ x : ℝ, Real.cos (2 * Real.pi * (a + r * x)) = -Real.cos (2 * Real.pi * x) := by
  have hroots : ∀ x : ℝ, Real.cos (2 * Real.pi * x) = 0 →
      Real.cos (2 * Real.pi * (a + r * x)) = 0 := by
    intro x hx
    have h := hid x
    rw [hx] at h
    have hz : A * Real.cos (2 * Real.pi * (a + r * x)) = 0 := by nlinarith only [h]
    exact (mul_eq_zero.mp hz).resolve_left hA.ne'
  have hfreq := cosine_root_spacing a r hr hle hroots
  have hquarter : Real.cos (2 * Real.pi * (1 / 4)) = 0 := by
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.cos_pi_div_two]
  obtain ⟨hsq, hprop⟩ := cosine_roots_same_frequency a r hfreq (hroots _ hquarter)
  let c := Real.cos (2 * Real.pi * a)
  have hc₁ : HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x)) (-2 * Real.pi) (1 / 4) := by
    convert! ((hasDerivAt_id (1 / 4 : ℝ)).const_mul (2 * Real.pi)).cos using 1
    dsimp only [id_eq]
    rw [show 2 * Real.pi * (1 / 4) = Real.pi / 2 by ring, Real.sin_pi_div_two]
    ring
  have hc₂ : HasDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * (a + r * x)))
      (c * (-2 * Real.pi)) (1 / 4) := by
    convert! hc₁.const_mul c using 1
    exact funext hprop
  have hleft := ((p.hasDerivAt (1 / 4)).mul hc₁).mul hc₂
  have hright := (hc₂.const_mul A).add (hc₁.const_mul B)
  have heq := hleft.unique (hright.congr_of_eventuallyEq (Filter.Eventually.of_forall (fun x => hid x)))
  simp only [Pi.mul_apply, hquarter, hroots _ hquarter, mul_zero, zero_mul, zero_add] at heq
  have hlin : A * c + B = 0 := by
    have hh : (A * c + B) * (-2 * Real.pi) = 0 := by nlinarith only [heq]
    exact (mul_eq_zero.mp hh).resolve_right (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hc : c = -1 := by
    change c ^ 2 = 1 at hsq
    have hs : c = 1 ∨ c = -1 := (sq_eq_one_iff).mp hsq
    rcases hs with hs | hs
    · rw [hs] at hlin
      linarith
    · exact hs
  refine ⟨hfreq, ?_, ?_⟩
  · rw [hc] at hlin
    linarith
  · intro x
    rw [hprop]
    change c * _ = _
    rw [hc, neg_one_mul]

lemma opposite_limit_obstruction (p : Polynomial ℝ) (A B C β z b : ℝ) (hb : b ≠ 0)
    (hN : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ β ≠ 0) :
    ∃ h, oppositeLimitDifference p A B C β z b h ≠ 0 := by
  by_contra hn
  push Not at hn
  have hz := alternating_cosine_obstruction A B C β z b hb (fun x hx => by
    have he := hn x
    simp only [oppositeLimitDifference, hx, zero_pow (by decide : 2 ≠ 0), mul_zero,
      zero_sub] at he
    linarith)
  rcases hN with hA | hB | hC | hβ
  · exact hA hz.1
  · exact hB hz.2.1
  · exact hC hz.2.2.1
  · exact hβ hz.2.2.2

lemma polynomial_quartic_obstruction (p : Polynomial ℝ) (hp : p.natDegree ≤ 3) :
    ¬ ∀ x : ℝ, p.eval x = x ^ 4 := by
  intro he
  have hpoly : p = Polynomial.X ^ 4 := Polynomial.funext (by simpa using he)
  rw [hpoly] at hp
  norm_num at hp

lemma taylorPolynomialAtZero_eval (f : ℝ → ℝ) (n : ℕ) (x : ℝ) :
    (taylorPolynomialAtZero f n).eval x =
      ∑ i ∈ Finset.range (n + 1), iteratedDeriv i f 0 / (i.factorial : ℝ) * x ^ i := by
  simp only [taylorPolynomialAtZero, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma taylorPolynomialAtZero_degree (f : ℝ → ℝ) (n : ℕ) :
    (taylorPolynomialAtZero f n).natDegree ≤ n := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ (Finset.mem_range.mp hi))

lemma taylorPolynomialAtZero_eval_eq (f : ℝ → ℝ) (n : ℕ) {s : Set ℝ}
    (hs : UniqueDiffOn ℝ s) (h₀ : (0 : ℝ) ∈ s) (hf : AnalyticAt ℝ f 0) (x : ℝ) :
    (taylorPolynomialAtZero f n).eval x = taylorWithinEval f n s 0 x := by
  induction n with
  | zero => simp [taylorPolynomialAtZero, iteratedDeriv_zero]
  | succ n ih =>
    rw [taylorWithinEval_succ, ← ih, taylorPolynomialAtZero_eval,
      Finset.sum_range_succ, taylorPolynomialAtZero_eval]
    rw [iteratedDerivWithin_eq_iteratedDeriv hs hf.contDiffAt h₀]
    simp only [sub_zero, smul_eq_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    ring

lemma taylorPolynomialAtZero_eval_zero (f : ℝ → ℝ) (n : ℕ) :
    (taylorPolynomialAtZero f n).eval 0 = f 0 := by
  rw [taylorPolynomialAtZero_eval, Finset.sum_eq_single 0]
  · simp
  · intro i _ hi
    simp [zero_pow hi]
  · simp

lemma analytic_taylor_remainder_bound {f : ℝ → ℝ} (n : ℕ)
    (hf : AnalyticOnNhd ℝ f (Icc (-1) 1)) {C : ℝ} (_hC : 0 ≤ C)
    (hb : ∀ x ∈ Icc (-1) 1, |iteratedDeriv (n + 1) f x| ≤ C)
    {x : ℝ} (hx : |x| ≤ 1) :
    |f x - (taylorPolynomialAtZero f n).eval x| ≤
      C * |x| ^ (n + 1) / ((n + 1).factorial : ℝ) := by
  by_cases hzero : x = 0
  · subst x
    simp [taylorPolynomialAtZero_eval_zero]
  have hseg : uIcc (0 : ℝ) x ⊆ Icc (-1) 1 := by
    rw [uIcc]
    exact Icc_subset_Icc (le_min (by norm_num) (abs_le.mp hx).1)
      (max_le (by norm_num) (abs_le.mp hx).2)
  have han := hf.mono hseg
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := n)
    (Ne.symm hzero) han.contDiffOn_of_completeSpace
  have hpol := taylorPolynomialAtZero_eval_eq f n (uniqueDiffOn_uIcc (Ne.symm hzero))
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 x) (hf 0 (by norm_num)) x
  rw [hpol, he, abs_div, abs_mul, abs_pow, sub_zero, Nat.abs_cast]
  gcongr
  exact hb y (hseg (⟨hy.1.le, hy.2.le⟩))

lemma analytic_liftedOrbit (k q₀ : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun x => liftedOrbit k q₀ x n) univ := by
  induction n using Nat.twoStepInduction with
  | zero => exact analyticOnNhd_const
  | one => exact analyticOnNhd_id
  | more n h₀ h₁ =>
    intro x hx
    exact ((analyticAt_const.mul (h₁ x hx)).add
      (analyticAt_const.mul (Real.analyticAt_sin.comp
        (analyticAt_const.mul (h₁ x hx))))).sub (h₀ x hx)

lemma analytic_orbitCoefficient (k q₀ : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun x => orbitCoefficient k q₀ x n) univ := by
  intro x hx
  exact analyticAt_const.add (analyticAt_const.mul (Real.analyticAt_cos.comp
    (analyticAt_const.mul (analytic_liftedOrbit k q₀ n x hx))))

lemma analytic_linearSolution {v : ℝ → ℕ → ℝ}
    (hv : ∀ n, AnalyticOnNhd ℝ (fun x => v x n) univ) (a b : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun x => linearSolution (v x) a b n) univ := by
  induction n using Nat.twoStepInduction with
  | zero => exact analyticOnNhd_const
  | one => exact analyticOnNhd_const
  | more n h₀ h₁ => exact ((hv (n + 1)).mul h₁).sub h₀

lemma analytic_rescaledOrbit (k q₀ θ L : ℝ) (n : ℕ) :
    AnalyticOnNhd ℝ (fun x => rescaledOrbit k q₀ θ L x n) univ := by
  intro x _
  exact (analytic_liftedOrbit k q₀ n _ (mem_univ _)).comp
    (analyticAt_const.add (analyticAt_id.div_const))

lemma analyticAt_boundaryValue (k q₀ θ L ξ : ℝ) (j : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + ξ / L)) j ≠ 0) :
    AnalyticAt ℝ (fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) j) ξ := by
  have ha : AnalyticAt ℝ (fun x : ℝ => θ + x / L) ξ :=
    analyticAt_const.add (analyticAt_id.div_const)
  exact (((analytic_linearSolution (analytic_orbitCoefficient k q₀) 1 0 j _
    (mem_univ _)).comp ha).neg).div
      ((analytic_linearSolution (analytic_orbitCoefficient k q₀) 0 1 j _
        (mem_univ _)).comp ha) ht

lemma iteratedDeriv_rescaledOrbit (k q₀ θ L ξ : ℝ) (n p : ℕ) (hp : p ≤ 4) :
    iteratedDeriv (p + 1) (fun x => rescaledOrbit k q₀ θ L x n) ξ =
      rescaledTJet p k q₀ θ L ξ n := by
  induction p generalizing ξ with
  | zero => simpa only [Nat.zero_add, iteratedDeriv_one, rescaledTJet] using
      (hasDerivAt_rescaledOrbit k q₀ θ L ξ n).deriv
  | succ p ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv (p + 1) (fun x => rescaledOrbit k q₀ θ L x n) =
        (fun x => rescaledTJet p k q₀ θ L x n) := by
      funext x
      exact ih x (by omega)
    rw [he]
    exact (hasDerivAt_rescaledTJet k q₀ θ L ξ n p (by omega)).deriv

lemma GoodIndex.boundary_taylor_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (ξ : ℝ) (hξ : |ξ| ≤ 1) :
    let L := |tSolution (orbitCoefficient k q₀ θ) j|
    let f := fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) j
    L ^ 2 * |f ξ - (taylorPolynomialAtZero f 3).eval ξ| ≤
      inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(14 / 5 : ℝ)) *
        |ξ| ^ 4 / 24 := by
  dsimp only
  let L := |tSolution (orbitCoefficient k q₀ θ) j|
  let f := fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / L)) j
  let C := inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(14 / 5 : ℝ))
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0 < L := abs_pos.mpr (hg.t_ne_zero hM)
  have hC : 0 ≤ C := by
    dsimp [C]
    apply mul_nonneg
    · unfold inverseFourthMajorant derivativeMajorant; positivity
    · positivity
  have han : AnalyticOnNhd ℝ f (Icc (-1) 1) := by
    intro x hx
    apply analyticAt_boundaryValue
    apply abs_pos.mp
    have hh := hg.varied_t_lower hk hc.1 x (abs_le.mpr hx)
    change 0 < L at hL
    linarith
  have hb : ∀ x ∈ Icc (-1) 1, |iteratedDeriv (3 + 1) f x| ≤ C / L ^ 2 := by
    intro x hx
    apply (le_div_iff₀ (sq_pos_of_pos hL)).mpr
    have hh := hg.boundary_fourth_bound hk hc hz x (abs_le.mpr hx)
    change L ^ 2 * |iteratedDeriv 4 f x| ≤ C at hh
    nlinarith only [hh]
  have ht := analytic_taylor_remainder_bound 3 han (div_nonneg hC (sq_nonneg L)) hb hξ
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.reduceMul, Nat.cast_ofNat] at ht
  have hh := mul_le_mul_of_nonneg_left ht (sq_nonneg L)
  change L ^ 2 * |f ξ - (taylorPolynomialAtZero f 3).eval ξ| ≤ C * |ξ| ^ 4 / 24
  calc
    L ^ 2 * |f ξ - (taylorPolynomialAtZero f 3).eval ξ| ≤
        L ^ 2 * (C / L ^ 2 * |ξ| ^ 4 / 24) := hh
    _ = C * |ξ| ^ 4 / 24 := by field_simp [ne_of_gt hL]

open Filter
open scoped Topology

lemma vandermonde_continuous (d : ℕ) :
    Continuous (fun x : Fin d → ℝ => Matrix.vandermonde x) := by
  unfold Matrix.vandermonde
  fun_prop

lemma coefficientPolynomial_eval {d : ℕ} (c : Fin d → ℝ) (x : ℝ) :
    (coefficientPolynomial c).eval x = ∑ i : Fin d, c i * x ^ i.val := by
  simp only [coefficientPolynomial, Polynomial.eval_finsetSum, Polynomial.eval_monomial]

lemma coefficientPolynomial_reconstruct {d : ℕ} (p : Polynomial ℝ) (hp : p.natDegree < d) :
    coefficientPolynomial (fun i : Fin d => p.coeff i) = p := by
  unfold coefficientPolynomial
  rw [show (∑ i : Fin d, Polynomial.monomial i.val (p.coeff i.val)) =
      ∑ i ∈ Finset.range d, Polynomial.monomial i (p.coeff i) by
    exact Fin.sum_univ_eq_sum_range (fun i => Polynomial.monomial i (p.coeff i)) d]
  exact (p.as_sum_range' d hp).symm

lemma coefficientPolynomial_degree {d : ℕ} (c : Fin (d + 1) → ℝ) :
    (coefficientPolynomial c).natDegree ≤ d := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.le_of_lt_succ i.isLt)

lemma coefficientPolynomial_vandermonde {d : ℕ} (c x : Fin d → ℝ) :
    (Matrix.vandermonde x).mulVec c = fun i => (coefficientPolynomial c).eval (x i) := by
  ext i
  simp only [coefficientPolynomial_eval, Matrix.mulVec, dotProduct, Matrix.vandermonde_apply]
  exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

lemma continuous_coefficientPolynomial_eval (d : ℕ) :
    Continuous (fun q : (Fin d → ℝ) × ℝ => (coefficientPolynomial q.1).eval q.2) := by
  simp only [coefficientPolynomial_eval]
  fun_prop

open Metric

lemma compact_sets_subsequence (K : ℕ → TopologicalSpace.NonemptyCompacts ℝ)
    (hK : ∀ n, (K n : Set ℝ) ⊆ Icc (-1) 1) :
    ∃ F : TopologicalSpace.NonemptyCompacts ℝ, (F : Set ℝ) ⊆ Icc (-1) 1 ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (K ∘ φ) atTop (nhds F) := by
  exact (TopologicalSpace.NonemptyCompacts.isCompact_subsets_of_isCompact
    (isCompact_Icc : IsCompact (Icc (-1 : ℝ) 1))).tendsto_subseq hK

lemma neighborhoods_null_limit (K : ℕ → TopologicalSpace.NonemptyCompacts ℝ)
    (F : TopologicalSpace.NonemptyCompacts ℝ) (hK : Tendsto K atTop (nhds F))
    (hF : volume (F : Set ℝ) = 0) (δ : ℕ → ℝ) (hδ : Tendsto δ atTop (nhds 0)) :
    Tendsto (fun n => volume {x : ℝ | ∃ y ∈ (K n : Set ℝ), dist x y < δ n}) atTop (nhds 0) := by
  have hD : Tendsto (fun n => dist (K n) F) atTop (nhds 0) := by
    simpa only [dist_self] using hK.dist (tendsto_const_nhds (x := F))
  have hm := (tendsto_measure_cthickening_of_isCompact (μ := volume) F.isCompact).comp
    (by simpa only [zero_add] using hδ.add hD)
  simp only [hF] at hm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hm
  · intro n
    exact bot_le
  · intro n
    apply measure_mono
    rintro x ⟨y, hy, hxy⟩
    obtain ⟨z, hz, hdist⟩ := F.isCompact.exists_infDist_eq_dist F.nonempty y
    have hfinite : hausdorffEDist (K n : Set ℝ) (F : Set ℝ) ≠ ⊤ :=
      hausdorffEDist_ne_top_of_nonempty_of_bounded (K n).nonempty F.nonempty
        (K n).isCompact.isBounded F.isCompact.isBounded
    have hh := infDist_le_hausdorffDist_of_mem hy hfinite
    rw [hdist, ← Metric.NonemptyCompacts.dist_eq] at hh
    exact mem_cthickening_of_dist_le x z _ _ hz
      ((dist_triangle x y z).trans (add_le_add hxy.le hh))

lemma successful_points_approximation (S : ℕ → Set ℝ)
    (K : ℕ → TopologicalSpace.NonemptyCompacts ℝ)
    (F : TopologicalSpace.NonemptyCompacts ℝ)
    (hcl : ∀ n, closure (S n) = (K n : Set ℝ))
    (hK : Tendsto K atTop (nhds F)) {x : ℝ} (hx : x ∈ (F : Set ℝ)) :
    ∃ y : ℕ → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y atTop (nhds x) := by
  classical
  have hnon (n : ℕ) : (S n).Nonempty := by
    apply closure_nonempty_iff.mp
    rw [hcl n]
    exact (K n).nonempty
  have hv (n : ℕ) : ∃ y ∈ S n, dist x y < infDist x (S n) + 1 / ((n : ℝ) + 1) := by
    apply (infDist_lt_iff (hnon n)).mp
    linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  choose y hy hd using hv
  refine ⟨y, hy, ?_⟩
  have hdist : Tendsto (fun n => infDist x (S n)) atTop (nhds 0) := by
    have hh := ((Metric.lipschitz_infDist_set x).continuous.tendsto F).comp hK
    simp only [infDist_zero_of_mem hx] at hh
    have he : (fun n => infDist x (S n)) = fun n => infDist x (K n : Set ℝ) := by
      funext n
      rw [← infDist_closure, hcl n]
    rwa [he]
  have hlim : Tendsto (fun n => dist (y n) x) atTop (nhds 0) := by
    apply squeeze_zero (fun n => dist_nonneg) (fun n => ?_)
      (by simpa using hdist.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
    rw [dist_comm]
    simpa only [one_div] using (hd n).le
  exact tendsto_iff_dist_tendsto_zero.mpr hlim

lemma CommonGood.scale_pos {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k) :
    0 < matchedScale k q₀ θ jm jp := by
  obtain ⟨b, hm, _⟩ := hg
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  exact (abs_pos.mpr (hm.t_ne_zero hM)).trans_le (le_max_left _ _)

lemma CommonGood.boundary_sum_error {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k) :
    |potential k q₀ -
      (boundaryValue (orbitCoefficient k q₀ θ) jm +
       boundaryValue (orbitCoefficient k q₀ (phi k q₀ - θ)) jp +
       1 / (tSolution (orbitCoefficient k q₀ θ) jm *
         tSolution (orbitCoefficient k q₀ θ) (jm + 1)) +
       1 / (tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp *
         tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) (jp + 1)))| ≤
      2 / ((growthBase k ^ goodExponent) ^ (3 : ℕ) *
        |tSolution (orbitCoefficient k q₀ θ) jm| ^ 2) +
      2 / ((growthBase k ^ goodExponent) ^ (3 : ℕ) *
        |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp| ^ 2) := by
  obtain ⟨b, hm, hp⟩ := hg
  have hM : 2 ≤ growthBase k := (by norm_num : (2 : ℝ) ≤ 4).trans (growthBase_ge_four k hk)
  have e₁ := hm.boundary_expansion_error hM
  have e₂ := hp.boundary_expansion_error hM
  calc
    _ = |(b - (boundaryValue (orbitCoefficient k q₀ θ) jm +
        1 / (tSolution (orbitCoefficient k q₀ θ) jm *
          tSolution (orbitCoefficient k q₀ θ) (jm + 1)))) +
        ((potential k q₀ - b) - (boundaryValue (orbitCoefficient k q₀ (phi k q₀ - θ)) jp +
        1 / (tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp *
          tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) (jp + 1))))| := by congr 1; ring
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add e₁ e₂)

lemma matched_log_ratio {M A B : ℝ} (hM : 1 < M) (hA : 0 < A) (hB : 0 < B)
    (h : |Real.logb M A - Real.logb M B| ≤ 3 / 5) :
    M ^ (-(3 / 5 : ℝ)) * max A B ≤ min A B := by
  have ha := abs_le.mp h
  have h₁ := logb_growth M A B (-(3 / 5)) hM hA hB (by linarith)
  have h₂ := logb_growth M B A (-(3 / 5)) hM hB hA (by linarith)
  rcases le_total A B with hAB | hBA
  · simpa only [max_eq_right hAB, min_eq_left hAB] using h₂
  · simpa only [max_eq_left hBA, min_eq_right hBA] using h₁

lemma CommonGood.scale_ratio {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k)
    (hl : MatchedLogs k q₀ θ jm jp) :
    growthBase k ^ (-(3 / 5 : ℝ)) * matchedScale k q₀ θ jm jp ≤
      min |tSolution (orbitCoefficient k q₀ θ) jm|
        |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp| := by
  obtain ⟨b, hm, hp⟩ := hg
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  unfold MatchedLogs pairLog at hl
  rw [hm.t_dominant hM, hp.t_dominant hM] at hl
  exact matched_log_ratio hM (abs_pos.mpr (hm.t_ne_zero hM))
    (abs_pos.mpr (hp.t_ne_zero hM)) hl

lemma cubic_scale_remainder {L l C e a h : ℝ}
    (hL : 0 < L) (hl : 0 < l) (hlL : l ≤ L) (hC : 0 ≤ C)
    (_he : 0 ≤ e) (ha : |a| = l / L) (hh : |h| ≤ 1)
    (hb : l ^ 2 * e ≤ C * |a * h| ^ 4 / 24) :
    L ^ 2 * e ≤ C / 24 := by
  have hr : 0 ≤ l / L := div_nonneg hl.le hL.le
  have hr₁ : l / L ≤ 1 := (div_le_one hL).mpr hlL
  have hp : (l / L) ^ 2 ≤ 1 := pow_le_one₀ hr hr₁
  have hhp : |h| ^ 4 ≤ 1 := pow_le_one₀ (abs_nonneg _) hh
  have hb' : l ^ 2 * e ≤ C * (l / L) ^ 4 / 24 := by
    rw [abs_mul, mul_pow, ha] at hb
    exact hb.trans (by nlinarith [mul_nonneg hC (pow_nonneg hr 4)])
  have hs := mul_le_mul_of_nonneg_left hb' (show 0 ≤ L ^ 2 / l ^ 2 by positivity)
  have hid₁ : L ^ 2 / l ^ 2 * (l ^ 2 * e) = L ^ 2 * e := by field_simp
  have hid₂ : L ^ 2 / l ^ 2 * (C * (l / L) ^ 4 / 24) = C / 24 * (l / L) ^ 2 := by
    field_simp
  rw [hid₁, hid₂] at hs
  exact hs.trans (by nlinarith)

lemma scaledTaylorPolynomial_degree (f : ℝ → ℝ) (a : ℝ) :
    (scaledTaylorPolynomial f a).natDegree ≤ 3 := by
  have hd : (Polynomial.C a * Polynomial.X : Polynomial ℝ).natDegree ≤ 1 :=
    (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  exact (Polynomial.natDegree_comp_le).trans
    ((Nat.mul_le_mul (taylorPolynomialAtZero_degree f 3) hd).trans (by norm_num))

lemma scaledTaylorPolynomial_eval (f : ℝ → ℝ) (a h : ℝ) :
    (scaledTaylorPolynomial f a).eval h = (taylorPolynomialAtZero f 3).eval (a * h) := by
  simp [scaledTaylorPolynomial]

lemma GoodIndex.scaled_boundary_taylor_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (L a h : ℝ) (hL : 0 < L)
    (hlL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    (ha : |a| = |tSolution (orbitCoefficient k q₀ θ) j| / L) (hh : |h| ≤ 1) :
    let l := |tSolution (orbitCoefficient k q₀ θ) j|
    let f := fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / l)) j
    L ^ 2 * |f (a * h) - (scaledTaylorPolynomial f a).eval h| ≤
      inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(14 / 5 : ℝ)) / 24 := by
  dsimp only
  rw [scaledTaylorPolynomial_eval]
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hl := abs_pos.mpr (hg.t_ne_zero hM)
  have ha₁ : |a| ≤ 1 := by rw [ha]; exact (div_le_one hL).mpr hlL
  apply cubic_scale_remainder hL hl hlL (by
    unfold inverseFourthMajorant derivativeMajorant; positivity) (abs_nonneg _) ha hh
  exact hg.boundary_taylor_bound hk hc hz (a * h) (by
    rw [abs_mul]; exact (mul_le_of_le_one_left (abs_nonneg _) ha₁).trans hh)

lemma potential_reciprocal_identity (k Q L t s u : ℝ) (hk : 0 < k)
    (hL : L ≠ 0) (ht : t ≠ 0) (hu : u ≠ 0) (he : u = potential k Q * t - s) :
    (2 * Real.pi * k) * L ^ 2 / (t * u) =
      1 / ((t / L) ^ 2 * (Real.cos (2 * Real.pi * Q) + (2 - s / t) / (2 * Real.pi * k))) := by
  have hK : 2 * Real.pi * k ≠ 0 := by positivity
  have hd : Real.cos (2 * Real.pi * Q) + (2 - s / t) / (2 * Real.pi * k) =
      u / ((2 * Real.pi * k) * t) := by
    rw [he]
    unfold potential
    field_simp
    ring
  rw [hd]
  field_simp

lemma CommonGood.cubic_boundary_bound {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k) (hc : HigherControl k)
    (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 3 ∧ ∀ h : ℝ, |h| ≤ 1 →
      let L := matchedScale k q₀ θ jm jp
      |(2 * Real.pi * k) * L ^ 2 *
        (potential k q₀ - boundaryValue (orbitCoefficient k q₀ (θ + h / L)) jm -
          boundaryValue (orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))) jp) - P.eval h| ≤
        (2 * Real.pi * k) * inverseFourthMajorant (52 * derivativeMajorant) *
          growthBase k ^ (-(14 / 5 : ℝ)) / 12 := by
  obtain ⟨b, hm, hp⟩ := hg
  let L := matchedScale k q₀ θ jm jp
  let lm := |tSolution (orbitCoefficient k q₀ θ) jm|
  let lp := |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp|
  let fm := fun x => boundaryValue (orbitCoefficient k q₀ (θ + x / lm)) jm
  let fp := fun x => boundaryValue (orbitCoefficient k q₀ (phi k q₀ - θ + x / lp)) jp
  let Pm := scaledTaylorPolynomial fm (lm / L)
  let Pp := scaledTaylorPolynomial fp (-lp / L)
  let K := 2 * Real.pi * k
  let C := inverseFourthMajorant (52 * derivativeMajorant) * growthBase k ^ (-(14 / 5 : ℝ))
  refine ⟨Polynomial.C (K * L ^ 2) * (Polynomial.C (potential k q₀) - Pm - Pp), ?_, ?_⟩
  · apply (Polynomial.natDegree_C_mul_le _ _).trans
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le _ (scaledTaylorPolynomial_degree fp (-lp / L))
    apply (Polynomial.natDegree_sub_le _ _).trans
    exact max_le (by simp) (scaledTaylorPolynomial_degree fm (lm / L))
  intro h hh
  have hL : 0 < L := CommonGood.scale_pos ⟨b, hm, hp⟩ hk
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hlm : 0 < lm := abs_pos.mpr (hm.t_ne_zero hM)
  have hlp : 0 < lp := abs_pos.mpr (hp.t_ne_zero hM)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have em := hm.scaled_boundary_taylor_bound hk hc hz L (lm / L) h hL
    (le_max_left _ _) (abs_of_nonneg (by positivity)) hh
  have ep := hp.scaled_boundary_taylor_bound hk hc hz L (-lp / L) h hL
    (le_max_right _ _) (by rw [abs_div, abs_neg, abs_of_pos hlp, abs_of_pos hL]) hh
  have h₁ : θ + (lm / L * h) / lm = θ + h / L := by field_simp
  have h₂ : phi k q₀ - θ + (-lp / L * h) / lp = phi k q₀ - (θ + h / L) := by
    field_simp
    ring
  change L ^ 2 * |fm (lm / L * h) - Pm.eval h| ≤ C / 24 at em
  change L ^ 2 * |fp (-lp / L * h) - Pp.eval h| ≤ C / 24 at ep
  have hev₁ : fm (lm / L * h) = boundaryValue (orbitCoefficient k q₀ (θ + h / L)) jm := by
    dsimp only [fm]; rw [h₁]
  have hev₂ : fp (-lp / L * h) =
      boundaryValue (orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))) jp := by
    dsimp only [fp]; rw [h₂]
  dsimp only at ⊢
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
  have hR : (2 * Real.pi * k) * inverseFourthMajorant (52 * derivativeMajorant) *
      growthBase k ^ (-(14 / 5 : ℝ)) / 12 = K * C / 12 := by dsimp [K, C]; ring
  rw [hR]
  change |K * L ^ 2 * (potential k q₀ - _ - _) -
    K * L ^ 2 * (potential k q₀ - Pm.eval h - Pp.eval h)| ≤ K * C / 12
  rw [← hev₁, ← hev₂]
  have hid : K * L ^ 2 * (potential k q₀ - fm (lm / L * h) - fp (-lp / L * h)) -
      K * L ^ 2 * (potential k q₀ - Pm.eval h - Pp.eval h) =
      -(K * L ^ 2) * ((fm (lm / L * h) - Pm.eval h) +
        (fp (-lp / L * h) - Pp.eval h)) := by ring
  rw [hid, abs_mul, abs_neg, abs_of_nonneg (mul_nonneg hK (sq_nonneg _))]
  calc
    _ ≤ K * L ^ 2 * (|fm (lm / L * h) - Pm.eval h| +
        |fp (-lp / L * h) - Pp.eval h|) :=
      mul_le_mul_of_nonneg_left (abs_add_le _ _) (mul_nonneg hK (sq_nonneg _))
    _ ≤ K * C / 12 := by nlinarith [mul_le_mul_of_nonneg_left em hK,
      mul_le_mul_of_nonneg_left ep hK]

lemma scaled_positive_reciprocal_bound {K L q r t : ℝ}
    (hK : 0 ≤ K) (hL : 0 < L) (hq : 0 < q) (hr : 0 < r)
    (ht : r * L / 2 ≤ |t|) :
    K * L ^ 2 * (2 / (q ^ 3 * |t| ^ 2)) ≤ 8 * K / (q ^ 3 * r ^ 2) := by
  have htp : 0 < |t| := (by positivity : 0 < r * L / 2).trans_le ht
  have hh : L / |t| ≤ 2 / r := by
    apply (div_le_div_iff₀ htp hr).mpr
    nlinarith only [ht]
  have hs : (L / |t|) ^ 2 ≤ (2 / r) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hh 2
  calc
    _ = (2 * K / q ^ 3) * (L / |t|) ^ 2 := by field_simp
    _ ≤ (2 * K / q ^ 3) * (2 / r) ^ 2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by field_simp; ring

lemma fourth_error_power (M : ℝ) (hM : 0 < M) :
    M * M ^ (-(14 / 5 : ℝ)) = M ^ (-(9 / 5 : ℝ)) := by
  rw [show -(9 / 5 : ℝ) = 1 + -(14 / 5 : ℝ) by norm_num,
    Real.rpow_add hM, Real.rpow_one]

lemma matched_error_power (M : ℝ) (hM : 0 < M) :
    M / ((M ^ goodExponent) ^ (3 : ℕ) * (M ^ (-(3 / 5 : ℝ))) ^ (2 : ℕ)) =
      M ^ (-(77 / 100 : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le,
    ← Real.rpow_natCast, ← Real.rpow_mul hM.le, ← Real.rpow_add hM]
  conv_lhs => lhs; rw [← Real.rpow_one M]
  rw [← Real.rpow_sub hM]
  norm_num [goodExponent]

lemma CommonGood.cubic_successful_bound {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k) (hc : HigherControl k)
    (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (hl : MatchedLogs k q₀ θ jm jp) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 3 ∧ ∀ h ∈ localSuccessfulSet k q₀ θ jm jp,
      let L := matchedScale k q₀ θ jm jp
      let v₁ := orbitCoefficient k q₀ (θ + h / L)
      let v₂ := orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))
      |P.eval h - ((2 * Real.pi * k) * L ^ 2 / (tSolution v₁ jm * tSolution v₁ (jm + 1)) +
        (2 * Real.pi * k) * L ^ 2 / (tSolution v₂ jp * tSolution v₂ (jp + 1)))| ≤
        inverseFourthMajorant (52 * derivativeMajorant) / 12 *
          growthBase k ^ (-(9 / 5 : ℝ)) + 16 * growthBase k ^ (-(77 / 100 : ℝ)) := by
  obtain ⟨P, hP, hPb⟩ := hg.cubic_boundary_bound hk hc hz
  refine ⟨P, hP, ?_⟩
  intro h hh
  obtain ⟨hhI, hgh⟩ := hh
  have hh₁ : |h| ≤ 1 := abs_le.mpr hhI
  let M := growthBase k
  let K := 2 * Real.pi * k
  let L := matchedScale k q₀ θ jm jp
  let lm := |tSolution (orbitCoefficient k q₀ θ) jm|
  let lp := |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp|
  let vm := orbitCoefficient k q₀ (θ + h / L)
  let vp := orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))
  let r := M ^ (-(3 / 5 : ℝ))
  let q := M ^ goodExponent
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hM₁ : 1 < M := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKM : K ≤ M := by dsimp [K, M, growthBase]; linarith
  have hL : 0 < L := hg.scale_pos hk
  have hr : 0 < r := Real.rpow_pos_of_pos hM _
  have hq : 0 < q := Real.rpow_pos_of_pos hM _
  have hmin := hg.scale_ratio hk hl
  change r * L ≤ min lm lp at hmin
  obtain ⟨b, hgm, hgp⟩ := hg
  have hlm : 0 < lm := abs_pos.mpr (hgm.t_ne_zero hM₁)
  have hlp : 0 < lp := abs_pos.mpr (hgp.t_ne_zero hM₁)
  have hascale : |lm / L * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hlm.le hL.le)]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hL).mpr (le_max_left _ _))).trans hh₁
  have hbscale : |-lp / L * h| ≤ 1 := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hlp, abs_of_pos hL]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hL).mpr (le_max_right _ _))).trans hh₁
  have hm := hgm.varied_t_lower hk hc.1 (lm / L * h) hascale
  have hp := hgp.varied_t_lower hk hc.1 (-lp / L * h) hbscale
  have hi₁ : θ + (lm / L * h) / lm = θ + h / L := by field_simp
  have hi₂ : phi k q₀ - θ + (-lp / L * h) / lp = phi k q₀ - (θ + h / L) := by
    field_simp
    ring
  change lm / 2 ≤ |tSolution (orbitCoefficient k q₀ (θ + (lm / L * h) / lm)) jm| at hm
  rw [hi₁] at hm
  change lp / 2 ≤ |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ + (-lp / L * h) / lp)) jp| at hp
  rw [hi₂] at hp
  have ht₁ : r * L / 2 ≤ |tSolution vm jm| := by
    have hh := hmin.trans (min_le_left _ _)
    change lm / 2 ≤ |tSolution vm jm| at hm
    linarith
  have ht₂ : r * L / 2 ≤ |tSolution vp jp| := by
    have hh := hmin.trans (min_le_right _ _)
    change lp / 2 ≤ |tSolution vp jp| at hp
    linarith
  have e₁ := scaled_positive_reciprocal_bound hK hL hq hr ht₁
  have e₂ := scaled_positive_reciprocal_bound hK hL hq hr ht₂
  have he := hgh.boundary_sum_error hk
  change |potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
    1 / (tSolution vm jm * tSolution vm (jm + 1)) +
    1 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤
      2 / (q ^ 3 * |tSolution vm jm| ^ 2) + 2 / (q ^ 3 * |tSolution vp jp| ^ 2) at he
  have hexp : K * L ^ 2 * |potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤
      16 * M ^ (-(77 / 100 : ℝ)) := by
    calc
      _ ≤ K * L ^ 2 * (2 / (q ^ 3 * |tSolution vm jm| ^ 2) +
          2 / (q ^ 3 * |tSolution vp jp| ^ 2)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hK (sq_nonneg _))
      _ = K * L ^ 2 * (2 / (q ^ 3 * |tSolution vm jm| ^ 2)) +
          K * L ^ 2 * (2 / (q ^ 3 * |tSolution vp jp| ^ 2)) := by ring
      _ ≤ 8 * K / (q ^ 3 * r ^ 2) + 8 * K / (q ^ 3 * r ^ 2) := add_le_add e₁ e₂
      _ = 16 * K / (q ^ 3 * r ^ 2) := by ring
      _ ≤ 16 * M / (q ^ 3 * r ^ 2) := by gcongr
      _ = _ := by rw [mul_div_assoc, matched_error_power M hM]
  have htay := hPb h hh₁
  change |K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp) - P.eval h| ≤
    K * inverseFourthMajorant (52 * derivativeMajorant) * M ^ (-(14 / 5 : ℝ)) / 12 at htay
  have hC : 0 ≤ inverseFourthMajorant (52 * derivativeMajorant) := by
    unfold inverseFourthMajorant derivativeMajorant; positivity
  have htay' : |K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp) - P.eval h| ≤
      inverseFourthMajorant (52 * derivativeMajorant) / 12 * M ^ (-(9 / 5 : ℝ)) := by
    apply htay.trans
    calc
      _ ≤ M * inverseFourthMajorant (52 * derivativeMajorant) * M ^ (-(14 / 5 : ℝ)) / 12 := by gcongr
      _ = _ := by rw [show M * inverseFourthMajorant (52 * derivativeMajorant) *
          M ^ (-(14 / 5 : ℝ)) / 12 = inverseFourthMajorant (52 * derivativeMajorant) / 12 *
          (M * M ^ (-(14 / 5 : ℝ))) by ring, fourth_error_power M hM]
  dsimp only
  change |P.eval h - (K * L ^ 2 / (tSolution vm jm * tSolution vm (jm + 1)) +
    K * L ^ 2 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤ _
  have htri := abs_add_le
    (P.eval h - K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp))
    (K * L ^ 2 * (potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))))
  rw [abs_mul, abs_of_nonneg (mul_nonneg hK (sq_nonneg _))] at htri
  have hid : (P.eval h - K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp)) +
      K * L ^ 2 * (potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))) =
      P.eval h - (K * L ^ 2 / (tSolution vm jm * tSolution vm (jm + 1)) +
      K * L ^ 2 / (tSolution vp jp * tSolution vp (jp + 1))) := by ring
  rw [hid] at htri
  apply htri.trans
  apply add_le_add _ hexp
  simpa only [abs_sub_comm] using htay'

lemma localReciprocalTerm_eq {k q₀ θ L h b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ (θ + h / L)) b j)
    (hk : 0 < k) (hL : L ≠ 0) :
    localReciprocalTerm k q₀ θ L h j = (2 * Real.pi * k) * L ^ 2 /
      (tSolution (orbitCoefficient k q₀ (θ + h / L)) j *
       tSolution (orbitCoefficient k q₀ (θ + h / L)) (j + 1)) := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk.le; linarith
  have hj : j - 1 + 1 = j := Nat.sub_add_cancel (by have := hg.1; omega)
  apply (potential_reciprocal_identity k _ L _ _ _ hk hL
    (hg.t_ne_zero hM) (hg.t_next_ne_zero hM) _).symm
  simpa only [show j - 1 + 2 = j + 1 by omega, hj, tSolution, orbitCoefficient] using
    linearSolution_step (orbitCoefficient k q₀ (θ + h / L)) 0 1 (j - 1)

theorem CommonGood.cubic_reciprocal_relation {k q₀ θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 < k) (hc : HigherControl k)
    (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (hl : MatchedLogs k q₀ θ jm jp) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 3 ∧ ∀ h ∈ localSuccessfulSet k q₀ θ jm jp,
      let L := matchedScale k q₀ θ jm jp
      |P.eval h - (localReciprocalTerm k q₀ θ L h jm +
        localReciprocalTerm k q₀ (phi k q₀ - θ) L (-h) jp)| ≤
        inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
          16 * growthBase k ^ (-(77 / 100 : ℝ)) := by
  obtain ⟨P, hP, hPb⟩ := hg.cubic_successful_bound hk.le hc hz hl
  refine ⟨P, hP, ?_⟩
  intro h hh
  have hL := (hg.scale_pos hk.le).ne'
  obtain ⟨b, hm, hp⟩ := hh.2
  have hi : phi k q₀ - θ + -h / matchedScale k q₀ θ jm jp =
      phi k q₀ - (θ + h / matchedScale k q₀ θ jm jp) := by ring
  have hp' : GoodIndex (growthBase k)
      (orbitCoefficient k q₀ (phi k q₀ - θ + -h / matchedScale k q₀ θ jm jp))
      (potential k q₀ - b) jp := by simpa only [hi] using hp
  dsimp only
  rw [localReciprocalTerm_eq hm hk hL, localReciprocalTerm_eq hp' hk hL, hi]
  exact hPb h hh

lemma tendsto_cubic_relation_error :
    Tendsto (fun k : ℝ =>
      inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
        16 * growthBase k ^ (-(77 / 100 : ℝ))) atTop (nhds 0) := by
  have h₁ := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 9 / 5 by norm_num)).comp tendsto_growthBase
  have h₂ := (tendsto_rpow_neg_atTop (show (0 : ℝ) < 77 / 100 by norm_num)).comp tendsto_growthBase
  convert! (h₁.const_mul (inverseFourthMajorant (52 * derivativeMajorant) / 12)).add (h₂.const_mul 16) using 1 ; simp only [mul_zero, zero_add]

lemma reciprocal_fourth_normalized (r S S₀ S₁ S₁₀ S₂ S₃ S₄ : ℝ)
    (hr : r ≠ 0) (hS : S ≠ 0) (h₀ : S₀ ≠ 0) (h₁ : S₁₀ ≠ 0) :
    ((1 / r ^ 2) * (24 * S₁ ^ 4 / S ^ 5 - 36 * S₁ ^ 2 * S₂ / S ^ 4 +
      (6 * S₂ ^ 2 + 8 * S₁ * S₃) / S ^ 3 - S₄ / S ^ 2)) /
        (S₁₀ ^ 4 / (r ^ 2 * S₀ ^ 5)) =
      24 * (S₁ / S₁₀) ^ 4 / (S / S₀) ^ 5 -
      36 * (S₁ / S₁₀) ^ 2 * (S₀ * S₂ / S₁₀ ^ 2) / (S / S₀) ^ 4 +
      (6 * (S₀ * S₂ / S₁₀ ^ 2) ^ 2 +
        8 * (S₁ / S₁₀) * (S₀ ^ 2 * S₃ / S₁₀ ^ 3)) / (S / S₀) ^ 3 -
      (S₀ ^ 3 * S₄ / S₁₀ ^ 4) / (S / S₀) ^ 2 := by
  field_simp

lemma rescaledOrbit_change_scale (k q₀ θ L l h : ℝ) (j : ℕ) (hl : l ≠ 0) :
    rescaledOrbit k q₀ θ L h j = rescaledOrbit k q₀ θ l ((l / L) * h) j := by
  unfold rescaledOrbit
  congr 2
  field_simp

lemma iteratedDeriv_rescaledOrbit_change_scale (k q₀ θ L l h : ℝ) (j p : ℕ)
    (hl : l ≠ 0) :
    iteratedDeriv p (fun x => rescaledOrbit k q₀ θ L x j) h =
      (l / L) ^ p * iteratedDeriv p (fun x => rescaledOrbit k q₀ θ l x j) ((l / L) * h) := by
  have hf : (fun x => rescaledOrbit k q₀ θ L x j) =
      (fun x => rescaledOrbit k q₀ θ l ((l / L) * x) j) := by
    funext x
    exact rescaledOrbit_change_scale k q₀ θ L l x j hl
  rw [hf, iteratedDeriv_comp_const_mul (analytic_rescaledOrbit k q₀ θ l j).contDiff]

lemma GoodIndex.terminal_derivative_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : 2 ≤ p) (hp' : p ≤ 5) :
    |iteratedDeriv p (fun x => rescaledOrbit k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| x j) h| ≤
      512 * derivativeMajorant * growthBase k * (growthBase k ^ (-goodExponent)) ^ p := by
  have hb := hg.rescaled_high_bounds hk hc h hh j le_rfl
  simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at hb
  interval_cases p
  · simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 1 (by omega),
      rescaledTJet, mul_assoc] using hb.1
  · simpa only [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 2 (by omega),
      rescaledTJet, mul_assoc] using hb.2.1
  · simpa only [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 3 (by omega),
      rescaledTJet, mul_assoc] using hb.2.2.1
  · simpa only [show (5 : ℕ) = 4 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 4 (by omega),
      rescaledTJet, mul_assoc] using hb.2.2.2

lemma scaled_rpow_bound (M a C : ℝ) (p : ℕ) (hM : 0 < M) :
    a ^ p * (C * M * (M ^ (-goodExponent)) ^ p) =
      C * a ^ p * M ^ (1 - (p : ℝ) * goodExponent) := by
  have hpow : (M ^ (-goodExponent)) ^ p = M ^ (-goodExponent * (p : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
  rw [hpow]
  rw [show 1 - (p : ℝ) * goodExponent = 1 + -goodExponent * (p : ℝ) by ring,
    Real.rpow_add hM, Real.rpow_one]
  ring

lemma GoodIndex.matched_phase_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : 2 ≤ p) (hp' : p ≤ 5) :
    |iteratedDeriv p (fun x => rescaledOrbit k q₀ θ L x j) h| ≤
      (512 * derivativeMajorant) * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p *
        growthBase k ^ (1 - (p : ℝ) * goodExponent) := by
  let l := |tSolution (orbitCoefficient k q₀ θ) j|
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hl : 0 < l := abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := hl.trans_le hL
  have ha : 0 ≤ l / L := div_nonneg hl.le hL'.le
  have ha' : l / L ≤ 1 := (div_le_one hL').mpr hL
  rw [iteratedDeriv_rescaledOrbit_change_scale k q₀ θ L l h j p hl.ne']
  rw [abs_mul, abs_pow, abs_of_nonneg ha]
  have hc' : |(l / L) * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [abs_nonneg h]
  have hb := hg.terminal_derivative_bound hk hc hc' hp hp'
  calc
    _ ≤ (l / L) ^ p * (512 * derivativeMajorant * growthBase k *
        (growthBase k ^ (-goodExponent)) ^ p) := mul_le_mul_of_nonneg_left hb (pow_nonneg ha _)
    _ = _ := scaled_rpow_bound _ _ _ _ hM

lemma taylorPolynomialAtZero_two_eval (f : ℝ → ℝ) (x : ℝ) :
    (taylorPolynomialAtZero f 2).eval x =
      f 0 + deriv f 0 * x + iteratedDeriv 2 f 0 / 2 * x ^ 2 := by
  simp [taylorPolynomialAtZero_eval, Finset.sum_range_succ, iteratedDeriv_zero,
    iteratedDeriv_one]

lemma taylorPolynomialAtZero_one_eval (f : ℝ → ℝ) (x : ℝ) :
    (taylorPolynomialAtZero f 1).eval x = f 0 + deriv f 0 * x := by
  simp [taylorPolynomialAtZero_eval, Finset.sum_range_succ, iteratedDeriv_zero,
    iteratedDeriv_one]

lemma analytic_quadratic_taylor_C1 {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc (-1) 1)) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y ∈ Icc (-1) 1, |iteratedDeriv 3 f y| ≤ C)
    {x : ℝ} (hx : |x| ≤ 1) :
    |f x - (f 0 + deriv f 0 * x + iteratedDeriv 2 f 0 / 2 * x ^ 2)| ≤ C / 6 ∧
    |deriv f x - (deriv f 0 + iteratedDeriv 2 f 0 * x)| ≤ C / 2 := by
  constructor
  · have hh := analytic_taylor_remainder_bound 2 hf hC hb hx
    rw [taylorPolynomialAtZero_two_eval] at hh
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at hh
    exact hh.trans (by nlinarith [pow_le_one₀ (abs_nonneg x) hx (n := 3)])
  · have hd : ∀ y ∈ Icc (-1) 1, |iteratedDeriv 2 (deriv f) y| ≤ C := by
      simpa only [← iteratedDeriv_succ'] using hb
    have hh := analytic_taylor_remainder_bound 1 hf.deriv hC hd hx
    rw [taylorPolynomialAtZero_one_eval] at hh
    have he : deriv (deriv f) 0 = iteratedDeriv 2 f 0 := by rw [iteratedDeriv_succ, iteratedDeriv_one]
    rw [he] at hh
    norm_num only [Nat.reduceAdd, Nat.factorial, Nat.cast_ofNat] at hh
    exact hh.trans (by nlinarith [pow_le_one₀ (abs_nonneg x) hx (n := 2)])

lemma GoodIndex.matched_phase_initial_derivative {k q₀ θ L : ℝ} {j : ℕ} :
    deriv (fun x => rescaledOrbit k q₀ θ L x j) 0 =
      tSolution (orbitCoefficient k q₀ θ) j / L := by
  rw [(hasDerivAt_rescaledOrbit k q₀ θ L 0 j).deriv]
  simp only [rescaledD₁, zero_div, add_zero]

lemma iteratedDeriv_comp_scale (n : ℕ) (f : ℝ → ℝ) (a : ℝ) :
    iteratedDeriv n (fun x => f (a * x)) =
      (fun x => a ^ n * iteratedDeriv n f (a * x)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext x
    rw [deriv_const_mul_field, deriv_comp_mul_left]
    simp only [smul_eq_mul, iteratedDeriv_succ, pow_succ]
    ring

lemma terminalQuotient_change_scale (k q₀ θ L l h : ℝ) (j : ℕ) (hl : l ≠ 0) :
    terminalQuotient k q₀ θ L h j = terminalQuotient k q₀ θ l ((l / L) * h) j := by
  unfold terminalQuotient
  have he : θ + (l / L * h) / l = θ + h / L := by field_simp
  rw [he]

lemma iteratedDeriv_terminalQuotient_change_scale (k q₀ θ L l h : ℝ) (j p : ℕ)
    (hl : l ≠ 0) :
    iteratedDeriv p (fun x => terminalQuotient k q₀ θ L x j) h =
      (l / L) ^ p * iteratedDeriv p (fun x => terminalQuotient k q₀ θ l x j) ((l / L) * h) := by
  have hf : (fun x => terminalQuotient k q₀ θ L x j) =
      (fun x => terminalQuotient k q₀ θ l ((l / L) * x) j) := by
    funext x
    exact terminalQuotient_change_scale k q₀ θ L l x j hl
  rw [hf]
  exact congrFun (iteratedDeriv_comp_scale p (fun x => terminalQuotient k q₀ θ l x j) (l / L)) h

lemma GoodIndex.matched_quotient_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (fun x => terminalQuotient k q₀ θ L x j) h| ≤
      640000 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p * growthBase k ^ (-goodExponent) := by
  let l := |tSolution (orbitCoefficient k q₀ θ) j|
  have hl : 0 < l := abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := hl.trans_le hL
  have ha : 0 ≤ l / L := div_nonneg hl.le hL'.le
  have ha' : l / L ≤ 1 := (div_le_one hL').mpr hL
  rw [iteratedDeriv_terminalQuotient_change_scale k q₀ θ L l h j p hl.ne']
  rw [abs_mul, abs_pow, abs_of_nonneg ha]
  have hc' : |(l / L) * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [abs_nonneg h]
  have hb := hg.quotient_derivatives hk hc _ hc' p hp
  calc
    _ ≤ (l / L) ^ p * (640000 * growthBase k ^ (-goodExponent)) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ha _)
    _ = _ := by ring

lemma analyticAt_terminalQuotient (k q₀ θ L h : ℝ) (j : ℕ)
    (ht : tSolution (orbitCoefficient k q₀ (θ + h / L)) j ≠ 0) :
    AnalyticAt ℝ (fun x => terminalQuotient k q₀ θ L x j) h := by
  have ha : AnalyticAt ℝ (fun x : ℝ => θ + x / L) h :=
    analyticAt_const.add (analyticAt_id.div_const)
  exact (((analytic_linearSolution (analytic_orbitCoefficient k q₀) 0 1 (j - 1) _
    (mem_univ _)).comp ha)).div
      ((analytic_linearSolution (analytic_orbitCoefficient k q₀) 0 1 j _
        (mem_univ _)).comp ha) ht

lemma GoodIndex.analytic_matched_quotient {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L) :
    AnalyticOnNhd ℝ (fun x => terminalQuotient k q₀ θ L x j) (Icc (-1) 1) := by
  intro h hh
  let l := |tSolution (orbitCoefficient k q₀ θ) j|
  have hl : 0 < l := abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := hl.trans_le hL
  have hs : |l / L * h| ≤ 1 := by
    rw [abs_mul, abs_of_pos (div_pos hl hL')]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hL').mpr hL)).trans (abs_le.mpr hh)
  have ht := hg.varied_t_lower hk hc.1 (l / L * h) hs
  have he : θ + (l / L * h) / l = θ + h / L := by field_simp
  rw [he] at ht
  apply analyticAt_terminalQuotient
  apply abs_pos.mp
  exact (half_pos hl).trans_le ht

lemma CommonGood.cubic_successful_bound_ratio {k q₀ θ r : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 ≤ k) (hc : HigherControl k)
    (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (hr : 0 < r)
    (hmin : r * matchedScale k q₀ θ jm jp ≤
      min |tSolution (orbitCoefficient k q₀ θ) jm|
        |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp|) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 3 ∧ ∀ h ∈ localSuccessfulSet k q₀ θ jm jp,
      let L := matchedScale k q₀ θ jm jp
      let v₁ := orbitCoefficient k q₀ (θ + h / L)
      let v₂ := orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))
      |P.eval h - ((2 * Real.pi * k) * L ^ 2 / (tSolution v₁ jm * tSolution v₁ (jm + 1)) +
        (2 * Real.pi * k) * L ^ 2 / (tSolution v₂ jp * tSolution v₂ (jp + 1)))| ≤
        inverseFourthMajorant (52 * derivativeMajorant) / 12 *
          growthBase k ^ (-(9 / 5 : ℝ)) + 16 / r ^ 2 * growthBase k ^ (1 - 3 * goodExponent) := by
  obtain ⟨P, hP, hPb⟩ := hg.cubic_boundary_bound hk hc hz
  refine ⟨P, hP, ?_⟩
  intro h hh
  obtain ⟨hhI, hgh⟩ := hh
  have hh₁ : |h| ≤ 1 := abs_le.mpr hhI
  let M := growthBase k
  let K := 2 * Real.pi * k
  let L := matchedScale k q₀ θ jm jp
  let lm := |tSolution (orbitCoefficient k q₀ θ) jm|
  let lp := |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp|
  let vm := orbitCoefficient k q₀ (θ + h / L)
  let vp := orbitCoefficient k q₀ (phi k q₀ - (θ + h / L))
  let q := M ^ goodExponent
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hM₁ : 1 < M := lt_of_lt_of_le (by norm_num) (growthBase_ge_four k hk)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hKM : K ≤ M := by dsimp [K, M, growthBase]; linarith
  have hL : 0 < L := hg.scale_pos hk
  have hq : 0 < q := Real.rpow_pos_of_pos hM _
  change r * L ≤ min lm lp at hmin
  obtain ⟨b, hgm, hgp⟩ := hg
  have hlm : 0 < lm := abs_pos.mpr (hgm.t_ne_zero hM₁)
  have hlp : 0 < lp := abs_pos.mpr (hgp.t_ne_zero hM₁)
  have hascale : |lm / L * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (div_nonneg hlm.le hL.le)]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hL).mpr (le_max_left _ _))).trans hh₁
  have hbscale : |-lp / L * h| ≤ 1 := by
    rw [abs_mul, abs_div, abs_neg, abs_of_pos hlp, abs_of_pos hL]
    exact (mul_le_of_le_one_left (abs_nonneg _) ((div_le_one hL).mpr (le_max_right _ _))).trans hh₁
  have hm := hgm.varied_t_lower hk hc.1 (lm / L * h) hascale
  have hp := hgp.varied_t_lower hk hc.1 (-lp / L * h) hbscale
  have hi₁ : θ + (lm / L * h) / lm = θ + h / L := by field_simp
  have hi₂ : phi k q₀ - θ + (-lp / L * h) / lp = phi k q₀ - (θ + h / L) := by
    field_simp
    ring
  change lm / 2 ≤ |tSolution (orbitCoefficient k q₀ (θ + (lm / L * h) / lm)) jm| at hm
  rw [hi₁] at hm
  change lp / 2 ≤ |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ + (-lp / L * h) / lp)) jp| at hp
  rw [hi₂] at hp
  have ht₁ : r * L / 2 ≤ |tSolution vm jm| := by
    have hh := hmin.trans (min_le_left _ _)
    change lm / 2 ≤ |tSolution vm jm| at hm
    linarith
  have ht₂ : r * L / 2 ≤ |tSolution vp jp| := by
    have hh := hmin.trans (min_le_right _ _)
    change lp / 2 ≤ |tSolution vp jp| at hp
    linarith
  have e₁ := scaled_positive_reciprocal_bound hK hL hq hr ht₁
  have e₂ := scaled_positive_reciprocal_bound hK hL hq hr ht₂
  have he := hgh.boundary_sum_error hk
  change |potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
    1 / (tSolution vm jm * tSolution vm (jm + 1)) +
    1 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤
      2 / (q ^ 3 * |tSolution vm jm| ^ 2) + 2 / (q ^ 3 * |tSolution vp jp| ^ 2) at he
  have hexp : K * L ^ 2 * |potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤
      16 / r ^ 2 * M ^ (1 - 3 * goodExponent) := by
    calc
      _ ≤ K * L ^ 2 * (2 / (q ^ 3 * |tSolution vm jm| ^ 2) +
          2 / (q ^ 3 * |tSolution vp jp| ^ 2)) :=
        mul_le_mul_of_nonneg_left he (mul_nonneg hK (sq_nonneg _))
      _ = K * L ^ 2 * (2 / (q ^ 3 * |tSolution vm jm| ^ 2)) +
          K * L ^ 2 * (2 / (q ^ 3 * |tSolution vp jp| ^ 2)) := by ring
      _ ≤ 8 * K / (q ^ 3 * r ^ 2) + 8 * K / (q ^ 3 * r ^ 2) := add_le_add e₁ e₂
      _ = 16 * K / (q ^ 3 * r ^ 2) := by ring
      _ ≤ 16 * M / (q ^ 3 * r ^ 2) := by gcongr
      _ = _ := by
        have hp : q ^ 3 = M ^ (3 * goodExponent) := by
          dsimp [q]
          rw [← Real.rpow_natCast, ← Real.rpow_mul hM.le]
          congr 1
          ring
        rw [hp, Real.rpow_sub hM, Real.rpow_one]
        ring
  have htay := hPb h hh₁
  change |K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp) - P.eval h| ≤
    K * inverseFourthMajorant (52 * derivativeMajorant) * M ^ (-(14 / 5 : ℝ)) / 12 at htay
  have hC : 0 ≤ inverseFourthMajorant (52 * derivativeMajorant) := by
    unfold inverseFourthMajorant derivativeMajorant; positivity
  have htay' : |K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp) - P.eval h| ≤
      inverseFourthMajorant (52 * derivativeMajorant) / 12 * M ^ (-(9 / 5 : ℝ)) := by
    apply htay.trans
    calc
      _ ≤ M * inverseFourthMajorant (52 * derivativeMajorant) * M ^ (-(14 / 5 : ℝ)) / 12 := by gcongr
      _ = _ := by rw [show M * inverseFourthMajorant (52 * derivativeMajorant) *
          M ^ (-(14 / 5 : ℝ)) / 12 = inverseFourthMajorant (52 * derivativeMajorant) / 12 *
          (M * M ^ (-(14 / 5 : ℝ))) by ring, fourth_error_power M hM]
  dsimp only
  change |P.eval h - (K * L ^ 2 / (tSolution vm jm * tSolution vm (jm + 1)) +
    K * L ^ 2 / (tSolution vp jp * tSolution vp (jp + 1)))| ≤ _
  have htri := abs_add_le
    (P.eval h - K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp))
    (K * L ^ 2 * (potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))))
  rw [abs_mul, abs_of_nonneg (mul_nonneg hK (sq_nonneg _))] at htri
  have hid : (P.eval h - K * L ^ 2 * (potential k q₀ - boundaryValue vm jm - boundaryValue vp jp)) +
      K * L ^ 2 * (potential k q₀ - (boundaryValue vm jm + boundaryValue vp jp +
      1 / (tSolution vm jm * tSolution vm (jm + 1)) +
      1 / (tSolution vp jp * tSolution vp (jp + 1)))) =
      P.eval h - (K * L ^ 2 / (tSolution vm jm * tSolution vm (jm + 1)) +
      K * L ^ 2 / (tSolution vp jp * tSolution vp (jp + 1))) := by ring
  rw [hid] at htri
  apply htri.trans
  apply add_le_add _ hexp
  simpa only [abs_sub_comm] using htay'

theorem CommonGood.cubic_reciprocal_relation_ratio {k q₀ θ r : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q₀ θ jm jp) (hk : 0 < k) (hc : HigherControl k)
    (hz : growthBase k ^ (-(47 / 100 : ℝ)) ≤ 1 / 2)
    (hr : 0 < r)
    (hmin : r * matchedScale k q₀ θ jm jp ≤
      min |tSolution (orbitCoefficient k q₀ θ) jm|
        |tSolution (orbitCoefficient k q₀ (phi k q₀ - θ)) jp|) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ 3 ∧ ∀ h ∈ localSuccessfulSet k q₀ θ jm jp,
      let L := matchedScale k q₀ θ jm jp
      |P.eval h - (localReciprocalTerm k q₀ θ L h jm +
        localReciprocalTerm k q₀ (phi k q₀ - θ) L (-h) jp)| ≤
        inverseFourthMajorant (52 * derivativeMajorant) / 12 * growthBase k ^ (-(9 / 5 : ℝ)) +
          16 / r ^ 2 * growthBase k ^ (1 - 3 * goodExponent) := by
  obtain ⟨P, hP, hPb⟩ := hg.cubic_successful_bound_ratio hk.le hc hz hr hmin
  refine ⟨P, hP, ?_⟩
  intro h hh
  have hL := (hg.scale_pos hk.le).ne'
  obtain ⟨b, hm, hp⟩ := hh.2
  have hi : phi k q₀ - θ + -h / matchedScale k q₀ θ jm jp =
      phi k q₀ - (θ + h / matchedScale k q₀ θ jm jp) := by ring
  have hp' : GoodIndex (growthBase k)
      (orbitCoefficient k q₀ (phi k q₀ - θ + -h / matchedScale k q₀ θ jm jp))
      (potential k q₀ - b) jp := by simpa only [hi] using hp
  dsimp only
  rw [localReciprocalTerm_eq hm hk hL, localReciprocalTerm_eq hp' hk hL, hi]
  exact hPb h hh

section

lemma iteratedDeriv_product_bound {f g : ℝ → ℝ} {x A B r : ℝ} {n : ℕ}
    (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hA : 0 ≤ A) (_hB : 0 ≤ B) (hr : 0 ≤ r)
    (hb : ∀ i ≤ n, |iteratedDeriv i f x| ≤ A * r ^ i)
    (hc : ∀ i ≤ n, |iteratedDeriv i g x| ≤ B * r ^ i) :
    |iteratedDeriv n (fun y => f y * g y) x| ≤ 2 ^ n * A * B * r ^ n := by
  rw [iteratedDeriv_fun_mul hf hg]
  calc
    _ ≤ ∑ i ∈ Finset.range (n + 1), |(n.choose i : ℝ) * iteratedDeriv i f x * iteratedDeriv (n-i) g x| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * (A * B * r ^ n) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' : i ≤ n := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hi
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
      calc
        _ ≤ (n.choose i : ℝ) * (A * r ^ i) * (B * r ^ (n-i)) := by
          gcongr
          · exact hb i hi'
          · exact hc (n-i) (Nat.sub_le _ _)
        _ = _ := by rw [show (n.choose i : ℝ) * (A * r ^ i) * (B * r ^ (n-i)) =
            (n.choose i : ℝ) * (A * B * (r ^ i * r ^ (n-i))) by ring,
            ← pow_add, Nat.add_sub_of_le hi']
    _ = 2 ^ n * A * B * r ^ n := by
      rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]
      ring

lemma iteratedDeriv_product_bound_four {f g : ℝ → ℝ} {x A B r : ℝ} {n : ℕ}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hr : 0 ≤ r) (hn : n ≤ 4)
    (hb : ∀ i ≤ n, |iteratedDeriv i f x| ≤ A * r ^ i)
    (hc : ∀ i ≤ n, |iteratedDeriv i g x| ≤ B * r ^ i) :
    |iteratedDeriv n (fun y => f y * g y) x| ≤ 16 * A * B * r ^ n := by
  apply (iteratedDeriv_product_bound hf.contDiffAt hg.contDiffAt hA hB hr hb hc).trans
  have hpow : (2 : ℝ) ^ n ≤ 16 := by
    calc
      _ ≤ (2 : ℝ) ^ 4 := pow_le_pow_right₀ (by norm_num) hn
      _ = 16 := by norm_num
  gcongr

lemma GoodIndex.terminal_coarse_derivative_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : 2 ≤ p) (hp' : p ≤ 5) :
    |iteratedDeriv p (fun x => rescaledOrbit k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| x j) h| ≤ 1 := by
  have hb := hg.rescaled_coarse_high_bounds hk hc h hh j le_rfl
  simp only [Nat.sub_self, pow_zero, one_pow] at hb
  interval_cases p
  · simpa only [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 1 (by omega), rescaledTJet] using hb.1
  · simpa only [show (3 : ℕ) = 2 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 2 (by omega), rescaledTJet] using hb.2.1
  · simpa only [show (4 : ℕ) = 3 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 3 (by omega), rescaledTJet] using hb.2.2.1
  · simpa only [show (5 : ℕ) = 4 + 1 from rfl, iteratedDeriv_rescaledOrbit k q₀ θ _ h j 4 (by omega), rescaledTJet] using hb.2.2.2

lemma GoodIndex.matched_phase_coarse_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : 1 ≤ p) (hp' : p ≤ 5) :
    |iteratedDeriv p (fun x => rescaledOrbit k q₀ θ L x j) h| ≤
      2 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p := by
  let l := |tSolution (orbitCoefficient k q₀ θ) j|
  have hl : 0 < l := abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := hl.trans_le hL
  have ha : 0 ≤ l / L := div_nonneg hl.le hL'.le
  have ha' : l / L ≤ 1 := (div_le_one hL').mpr hL
  rw [iteratedDeriv_rescaledOrbit_change_scale k q₀ θ L l h j p hl.ne']
  rw [abs_mul, abs_pow, abs_of_nonneg ha]
  have hc' : |(l / L) * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [abs_nonneg h]
  have hb : |iteratedDeriv p (fun x => rescaledOrbit k q₀ θ l x j) (l/L*h)| ≤ 2 := by
    rcases eq_or_lt_of_le hp with hp₁ | hp₁
    · subst p
      rw [iteratedDeriv_one, (hasDerivAt_rescaledOrbit k q₀ θ l _ j).deriv]
      have hb := hg.rescaled_derivative hk (by linarith only [hc.1]) _ hc' j le_rfl
      simpa only [Nat.sub_self, pow_zero, mul_one, rescaledD₁, l] using hb
    · exact (hg.terminal_coarse_derivative_bound hk hc hc' (by omega) hp').trans (by norm_num)
  calc
    _ ≤ (l / L) ^ p * 2 := mul_le_mul_of_nonneg_left hb (pow_nonneg ha _)
    _ = _ := by ring

lemma iteratedDeriv_rescaledPotential (k q₀ θ L h : ℝ) (j p : ℕ) (hp : p ≤ 4) :
    iteratedDeriv p (fun x => potential k (rescaledOrbit k q₀ θ L x j)) h =
      rescaledPotentialJet p k q₀ θ L h j := by
  apply iteratedDeriv_of_jets univ isOpen_univ (fun p h => rescaledPotentialJet p k q₀ θ L h j) 4 _ p hp h (mem_univ _)
  intro i hi x _
  interval_cases i
  · exact hasDerivAt_rescaledPotential k q₀ θ L x j
  · exact hasDerivAt_rescaledV₁ k q₀ θ L x j
  · exact hasDerivAt_rescaledV₂ k q₀ θ L x j
  · exact hasDerivAt_rescaledV₃ k q₀ θ L x j

lemma analytic_rescaledPotential (k q₀ θ L : ℝ) (j : ℕ) :
    AnalyticOnNhd ℝ (fun x => potential k (rescaledOrbit k q₀ θ L x j)) univ := by
  intro x _
  unfold potential
  exact analyticAt_const.add (analyticAt_const.mul
    (Real.analyticAt_cos.comp (analyticAt_const.mul (analytic_rescaledOrbit k q₀ θ L j x (mem_univ _)))))

lemma GoodIndex.terminal_potential_derivative_bound {k q₀ θ b : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (fun x => potential k (rescaledOrbit k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| x j)) h| ≤
      (1 + 52 * derivativeMajorant) * growthBase k := by
  have hb := hg.rescaled_potential_bounds hk hc h hh j le_rfl
  simp only [Nat.sub_self, pow_zero, one_pow, mul_one] at hb
  have hM : 0 ≤ growthBase k := by linarith [growthBase_ge_four k hk]
  have hD := derivativeMajorant_pos.le
  rw [iteratedDeriv_rescaledPotential k q₀ θ _ h j p hp]
  interval_cases p
  · change |potential k _| ≤ _
    have := potential_bound k (rescaledOrbit k q₀ θ |tSolution (orbitCoefficient k q₀ θ) j| h j) hk
    nlinarith
  · change |rescaledV₁ k q₀ θ _ h j| ≤ _
    nlinarith [hb.1]
  · change |rescaledV₂ k q₀ θ _ h j| ≤ _
    nlinarith [hb.2.1]
  · change |rescaledV₃ k q₀ θ _ h j| ≤ _
    nlinarith [hb.2.2.1]
  · change |rescaledV₄ k q₀ θ _ h j| ≤ _
    nlinarith [hb.2.2.2]

lemma GoodIndex.matched_potential_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (fun x => potential k (rescaledOrbit k q₀ θ L x j)) h| ≤
      (1 + 52 * derivativeMajorant) * growthBase k * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p := by
  let l := |tSolution (orbitCoefficient k q₀ θ) j|
  have hl : 0 < l := abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := hl.trans_le hL
  have ha : 0 ≤ l / L := div_nonneg hl.le hL'.le
  have ha' : l / L ≤ 1 := (div_le_one hL').mpr hL
  have hf : (fun x => potential k (rescaledOrbit k q₀ θ L x j)) =
      fun x => potential k (rescaledOrbit k q₀ θ l ((l/L)*x) j) := by
    funext x
    rw [rescaledOrbit_change_scale k q₀ θ L l x j hl.ne']
  rw [hf]
  have he := congrFun (iteratedDeriv_comp_scale p (fun x => potential k (rescaledOrbit k q₀ θ l x j)) (l/L)) h
  rw [he, abs_mul, abs_pow, abs_of_nonneg ha]
  have hc' : |(l / L) * h| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg ha]
    nlinarith [abs_nonneg h]
  have hb := hg.terminal_potential_derivative_bound hk hc hc' hp
  calc
    _ ≤ (l/L)^p * ((1 + 52 * derivativeMajorant) * growthBase k) :=
      mul_le_mul_of_nonneg_left hb (pow_nonneg ha _)
    _ = _ := by ring

lemma shiftedCosine_eq (k q₀ θ L : ℝ) (j : ℕ) (h : ℝ) (hk : k ≠ 0) :
    shiftedCosine k q₀ θ L j h = Real.cos (2 * Real.pi * rescaledOrbit k q₀ θ L h j) +
      (2 - terminalQuotient k q₀ θ L h j) / (2 * Real.pi * k) := by
  unfold shiftedCosine potential
  field_simp
  ring

lemma analytic_normalizedSlope (k q₀ θ L : ℝ) (j : ℕ) :
    AnalyticOnNhd ℝ (normalizedSlope k q₀ θ L j) univ :=
  (analytic_rescaledOrbit k q₀ θ L j).deriv.div_const

lemma GoodIndex.normalizedSlope_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (normalizedSlope k q₀ θ L j) h| ≤
      2 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p := by
  let r := |tSolution (orbitCoefficient k q₀ θ) j| / L
  have ht : 0 < |tSolution (orbitCoefficient k q₀ θ) j| :=
    abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk]))
  have hL' : 0 < L := ht.trans_le hL
  have hr : 0 < r := div_pos ht hL'
  change |iteratedDeriv p (fun h => deriv (fun x => rescaledOrbit k q₀ θ L x j) h / r) h| ≤ 2 * r ^ p
  rw [iteratedDeriv_div_const, ← iteratedDeriv_succ', abs_div, abs_of_pos hr]
  rw [div_le_iff₀ hr]
  have hb := hg.matched_phase_coarse_derivative_bound hk hc hL hh (p := p+1) (by omega) (by omega)
  simpa only [pow_succ, mul_assoc] using hb

lemma GoodIndex.analytic_shiftedCosine {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 0 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L) :
    AnalyticOnNhd ℝ (shiftedCosine k q₀ θ L j) (Icc (-1) 1) :=
  (((analytic_rescaledPotential k q₀ θ L j).mono (subset_univ _)).sub
    (hg.analytic_matched_quotient hk hc hL)).div_const

lemma GoodIndex.shiftedCosine_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 1 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (shiftedCosine k q₀ θ L j) h| ≤
      (640002 + 104 * derivativeMajorant) * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p := by
  have hk₀ : 0 ≤ k := by linarith
  have hK : 0 < 2 * Real.pi * k := by positivity
  have hK₁ : 1 ≤ 2 * Real.pi * k := by nlinarith [Real.pi_gt_three]
  have hKM : growthBase k ≤ 2 * (2 * Real.pi * k) := by
    unfold growthBase
    nlinarith [Real.pi_gt_three]
  have hm := rescaling_ratio_bounds k hk₀
  have hD := derivativeMajorant_pos.le
  have ht : 0 < |tSolution (orbitCoefficient k q₀ θ) j| :=
    abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk₀]))
  have hL' : 0 < L := ht.trans_le hL
  have hr : 0 ≤ |tSolution (orbitCoefficient k q₀ θ) j| / L := (div_pos ht hL').le
  unfold shiftedCosine
  rw [iteratedDeriv_div_const,
    iteratedDeriv_fun_sub (analytic_rescaledPotential k q₀ θ L j h (mem_univ _)).contDiffAt
      (hg.analytic_matched_quotient hk₀ hc hL h (abs_le.mp hh)).contDiffAt,
    abs_div, abs_of_pos hK]
  apply (div_le_div_of_nonneg_right (abs_sub _ _) hK.le).trans
  have hp₁ := hg.matched_potential_derivative_bound hk₀ hc hL hh hp
  have hp₂ := hg.matched_quotient_derivative_bound hk₀ hc hL hh hp
  rw [div_le_iff₀ hK]
  calc
    _ ≤ (1 + 52 * derivativeMajorant) * growthBase k *
          (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p +
        640000 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p * growthBase k ^ (-goodExponent) := add_le_add hp₁ hp₂
    _ ≤ (1 + 52 * derivativeMajorant) * (2 * (2 * Real.pi * k)) *
          (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p +
        640000 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p * (2 * Real.pi * k) := by
      gcongr
      exact hm.2.trans hK₁
    _ = _ := by ring

lemma GoodIndex.slowDenominator_derivative_bound {k q₀ θ b L : ℝ} {j : ℕ}
    (hg : GoodIndex (growthBase k) (orbitCoefficient k q₀ θ) b j) (hk : 1 ≤ k)
    (hc : HigherControl k) (hL : |tSolution (orbitCoefficient k q₀ θ) j| ≤ L)
    {h : ℝ} (hh : |h| ≤ 1) {p : ℕ} (hp : p ≤ 4) :
    |iteratedDeriv p (slowDenominator k q₀ θ L j) h| ≤
      (1024 * (640002 + 104 * derivativeMajorant)) * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ p := by
  have hk₀ : 0 ≤ k := by linarith
  have ht : 0 < |tSolution (orbitCoefficient k q₀ θ) j| :=
    abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four k hk₀]))
  have hr : 0 ≤ |tSolution (orbitCoefficient k q₀ θ) j| / L :=
    (div_pos ht (ht.trans_le hL)).le
  have ha := analytic_normalizedSlope k q₀ θ L j h (mem_univ _)
  have hb := hg.analytic_shiftedCosine hk₀ hc hL h (abs_le.mp hh)
  have ha' : ∀ i ≤ p, |iteratedDeriv i (fun x => normalizedSlope k q₀ θ L j x *
      normalizedSlope k q₀ θ L j x) h| ≤ 64 * (|tSolution (orbitCoefficient k q₀ θ) j| / L) ^ i := by
    intro i hi
    convert iteratedDeriv_product_bound_four ha ha (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (0 : ℝ) ≤ 2) hr
      (hi.trans hp) (fun a ha => hg.normalizedSlope_derivative_bound hk₀ hc hL hh ((ha.trans hi).trans hp))
      (fun a ha => hg.normalizedSlope_derivative_bound hk₀ hc hL hh ((ha.trans hi).trans hp)) using 1 ; ring
  unfold slowDenominator
  simp only [pow_two]
  have hC : 0 ≤ 640002 + 104 * derivativeMajorant := by have := derivativeMajorant_pos; positivity
  convert iteratedDeriv_product_bound_four (ha.mul ha) hb (by norm_num : (0 : ℝ) ≤ 64) hC hr hp ha'
    (fun i hi => hg.shiftedCosine_derivative_bound hk hc hL hh (hi.trans hp)) using 1 ; congr 2 ; norm_num

end

section

lemma hasDerivAt_slowDenominatorModel {Q E : ℝ → ℝ} {K r x b d e : ℝ}
    (hQ : HasDerivAt Q b x) (hd : HasDerivAt (deriv Q) d x) (hE : HasDerivAt E e x) :
    HasDerivAt (slowDenominatorModel Q E K r)
      (2 * (b / r) * (d / r) * (Real.cos (2 * Real.pi * Q x) + (2 - E x) / K) +
        (b / r) ^ 2 * (-2 * Real.pi * Real.sin (2 * Real.pi * Q x) * b - e / K)) x := by
  have hc := ((hQ.const_mul (2 * Real.pi)).cos).add ((hE.const_sub 2).div_const K)
  convert! ((hd.div_const r).pow 2).mul hc using 1
  simp only [Pi.pow_apply, Pi.add_apply, hQ.deriv, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  ring

lemma slowDenominatorModel_value {Q E : ℝ → ℝ} {K r x : ℝ}
    (hr : 0 < r) (hb : |deriv Q x| = r) :
    slowDenominatorModel Q E K r x = Real.cos (2 * Real.pi * Q x) + (2 - E x) / K := by
  have hs : (deriv Q x / r) ^ 2 = 1 := by
    have hab : |deriv Q x / r| = 1 := by rw [abs_div, hb, abs_of_pos hr, div_self hr.ne']
    nlinarith [sq_abs (deriv Q x / r)]
  simp only [slowDenominatorModel, hs, one_mul]

lemma abs_sin_close_one (x : ℝ) : abs (abs (Real.sin x) - 1) ≤ (Real.cos x) ^ 2 := by
  have hs := Real.abs_sin_le_one x
  rw [abs_of_nonpos (sub_nonpos.mpr hs)]
  have h := Real.sin_sq_add_cos_sq x
  nlinarith [abs_nonneg (Real.sin x), sq_abs (Real.sin x)]

lemma slowDenominatorModel_slope_bound {Q E : ℝ → ℝ} {K r x b d e : ℝ}
    (hr : 0 < r) (hK : 0 < K) (hb : |b| = r)
    (hQ : HasDerivAt Q b x) (hd : HasDerivAt (deriv Q) d x) (hE : HasDerivAt E e x) :
    abs (abs (deriv (slowDenominatorModel Q E K r) x) / r - 2 * Real.pi) ≤
      2 * (|d| / r ^ 2) * |slowDenominatorModel Q E K r x| + |e| / (K * r) +
        2 * Real.pi * (Real.cos (2 * Real.pi * Q x)) ^ 2 := by
  let s := Real.sin (2 * Real.pi * Q x)
  let W := slowDenominatorModel Q E K r x
  have hv : W = Real.cos (2 * Real.pi * Q x) + (2 - E x) / K :=
    slowDenominatorModel_value hr (by rwa [hQ.deriv])
  have hb' : (b / r) ^ 2 = 1 := by
    have hab : |b/r| = 1 := by rw [abs_div, hb, abs_of_pos hr, div_self hr.ne']
    nlinarith [sq_abs (b/r)]
  have heq : deriv (slowDenominatorModel Q E K r) x / r =
      (2 * b * d * W / r ^ 3 - e / (K * r)) + (-2 * Real.pi * s * (b / r)) := by
    rw [(hasDerivAt_slowDenominatorModel hQ hd hE).deriv, hb', ← hv]
    dsimp [s]
    field_simp
    ring
  have hmain : |-2 * Real.pi * s * (b / r)| = 2 * Real.pi * |s| := by
    rw [abs_mul, abs_mul, abs_mul, abs_div, hb, abs_of_pos hr, div_self hr.ne', mul_one,
      abs_of_pos Real.pi_pos]
    norm_num
  rw [show abs (deriv (slowDenominatorModel Q E K r) x) / r =
    abs (deriv (slowDenominatorModel Q E K r) x / r) by rw [abs_div, abs_of_pos hr]]
  rw [heq]
  calc
    _ ≤ abs (abs ((2 * b * d * W / r ^ 3 - e / (K * r)) + (-2 * Real.pi * s * (b / r))) -
        abs (-2 * Real.pi * s * (b / r))) + abs (abs (-2 * Real.pi * s * (b / r)) - 2 * Real.pi) :=
      abs_sub_le _ _ _
    _ ≤ |2 * b * d * W / r ^ 3 - e / (K * r)| + abs (abs (-2 * Real.pi * s * (b / r)) - 2 * Real.pi) := by
      apply add_le_add _ le_rfl
      convert abs_abs_sub_abs_le_abs_sub
        ((2 * b * d * W / r ^ 3 - e / (K * r)) + (-2 * Real.pi * s * (b / r))) (-2 * Real.pi * s * (b / r)) using 1 ; congr 1 ; ring
    _ ≤ |2 * b * d * W / r ^ 3| + |e / (K*r)| + 2 * Real.pi * abs (abs s - 1) := by
      rw [hmain, show 2 * Real.pi * |s| - 2 * Real.pi = 2 * Real.pi * (|s| - 1) by ring,
        abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
      gcongr
      exact abs_sub _ _
    _ ≤ |2 * b * d * W / r ^ 3| + |e / (K*r)| + 2 * Real.pi * (Real.cos (2 * Real.pi * Q x)) ^ 2 := by
      gcongr
      exact abs_sin_close_one _
    _ = _ := by
      rw [abs_div, abs_mul, abs_mul, abs_mul, abs_pow, abs_of_pos hr, hb,
        abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_div, abs_of_pos (mul_pos hK hr)]
      dsimp [W]
      field_simp

lemma tendsto_slow_nonzero_slope {ι : Type*} {l : Filter ι} (Q E : ι → ℝ → ℝ) (K r : ι → ℝ)
    (hK : ∀ n, 0 < K n) (hr : ∀ n, 0 < r n)
    (hQ : ∀ n, DifferentiableAt ℝ (Q n) 0)
    (hd : ∀ n, DifferentiableAt ℝ (deriv (Q n)) 0)
    (hE : ∀ n, DifferentiableAt ℝ (E n) 0)
    (hb : ∀ n, |deriv (Q n) 0| = r n)
    (hW : Tendsto (fun n => slowDenominatorModel (Q n) (E n) (K n) (r n) 0) l (nhds 0))
    (hc : Tendsto (fun n => |deriv (deriv (Q n)) 0| / (r n) ^ 2) l (nhds 0))
    (he : Tendsto (fun n => |deriv (E n) 0| / (K n * r n)) l (nhds 0))
    (hs : Tendsto (fun n => (2 - E n 0) / K n) l (nhds 0)) :
    Tendsto (fun n => |deriv (slowDenominatorModel (Q n) (E n) (K n) (r n)) 0| / r n)
      l (nhds (2 * Real.pi)) := by
  have hcos : Tendsto (fun n => Real.cos (2 * Real.pi * Q n 0)) l (nhds 0) := by
    convert hW.sub hs using 1
    · funext n
      rw [slowDenominatorModel_value (hr n) (hb n)]
      ring
    · ring_nf
  have hright : Tendsto (fun n => 2 * (|deriv (deriv (Q n)) 0| / r n ^ 2) *
      |slowDenominatorModel (Q n) (E n) (K n) (r n) 0| +
      |deriv (E n) 0| / (K n * r n) + 2 * Real.pi * (Real.cos (2 * Real.pi * Q n 0)) ^ 2)
      l (nhds 0) := by
    convert ((hc.const_mul 2).mul hW.abs).add he |>.add ((hcos.pow 2).const_mul (2 * Real.pi)) using 1 ; norm_num
  have hh : Tendsto (fun n => |deriv (slowDenominatorModel (Q n) (E n) (K n) (r n)) 0| / r n - 2 * Real.pi)
      l (nhds 0) := by
    apply squeeze_zero_norm' _ hright
    filter_upwards [] with n
    simpa only [Real.norm_eq_abs] using slowDenominatorModel_slope_bound (hr n) (hK n) (hb n)
      (hQ n).hasDerivAt (hd n).hasDerivAt (hE n).hasDerivAt
  simpa using hh.add_const (2 * Real.pi)

end

section
variable {ι : Type*} {l : Filter ι} [filterNonempty : l.NeBot]

omit [l.NeBot] in
lemma coefficients_tendsto_of_values_filter {d : ℕ}
    (x : ι → Fin d → ℝ) (c : ι → Fin d → ℝ) (x₀ y : Fin d → ℝ)
    (hx : Tendsto x l (nhds x₀)) (hi : Function.Injective x₀)
    (hy : Tendsto (fun n => (Matrix.vandermonde (x n)).mulVec (c n)) l (nhds y)) :
    Tendsto c l (nhds ((Matrix.vandermonde x₀)⁻¹.mulVec y)) := by
  let V := fun n => Matrix.vandermonde (x n)
  let A := Matrix.vandermonde x₀
  have hdet : A.det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hi
  have hV : Tendsto V l (nhds A) := (vandermonde_continuous d).continuousAt.tendsto.comp hx
  have hInv : Tendsto (fun n => (V n)⁻¹) l (nhds A⁻¹) := by
    have hh : ContinuousAt Ring.inverse A.det := by
      have he : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
      rw [he]
      exact continuousAt_inv₀ hdet
    exact (continuousAt_matrix_inv A hh).tendsto.comp hV
  have hdetN : ∀ᶠ n in l, (V n).det ≠ 0 :=
    (continuous_id.matrix_det.continuousAt.tendsto.comp hV).eventually_ne hdet
  have hcomp : Continuous (fun q : Matrix (Fin d) (Fin d) ℝ × (Fin d → ℝ) =>
      q.1.mulVec q.2) := continuous_fst.matrix_mulVec continuous_snd
  have hlim := hcomp.continuousAt.tendsto.comp (hInv.prodMk_nhds hy)
  apply hlim.congr'
  filter_upwards [hdetN] with n hn
  dsimp only [V] at hn
  dsimp only [V]
  change (Matrix.vandermonde (x n))⁻¹.mulVec ((Matrix.vandermonde (x n)).mulVec (c n)) = c n
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hn),
    Matrix.one_mulVec]

lemma polynomial_extraction_filter {d : ℕ} (S : ι → Set ℝ) (F : Set ℝ)
    (hF : F.Infinite) (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree < d + 1)
    (g : ℝ → ℝ)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, ∀ y : ι → ℝ, (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l (nhds (g x))) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧ ∀ x ∈ F, P.eval x = g x := by
  classical
  let z : Fin (d + 1) → ℝ := fun i => (hF.natEmbedding F i.val).val
  have hz : ∀ i, z i ∈ F := fun i => (hF.natEmbedding F i.val).property
  have hi : Function.Injective z := by
    intro i j hij
    exact Fin.ext ((hF.natEmbedding F).injective (Subtype.ext hij))
  choose y hy hyn using fun i => happrox (z i) (hz i)
  let c : ι → Fin (d + 1) → ℝ := fun n i => (p n).coeff i
  have hrec (n : ι) : coefficientPolynomial (c n) = p n :=
    coefficientPolynomial_reconstruct _ (hp n)
  have hyvec : Tendsto (fun n i => y i n) l (nhds z) :=
    tendsto_pi_nhds.mpr hyn
  have hv : Tendsto (fun n => (Matrix.vandermonde (fun i => y i n)).mulVec (c n)) l
      (nhds (fun i => g (z i))) := by
    simp_rw [coefficientPolynomial_vandermonde, hrec]
    exact tendsto_pi_nhds.mpr (fun i => hvalues (z i) (hz i) (y i) (hy i) (hyn i))
  have hc := coefficients_tendsto_of_values_filter (fun n i => y i n) c z (fun i => g (z i)) hyvec hi hv
  let c₀ := (Matrix.vandermonde z)⁻¹.mulVec (fun i => g (z i))
  refine ⟨coefficientPolynomial c₀, coefficientPolynomial_degree c₀, ?_⟩
  intro x hx
  obtain ⟨v, hv, hvlim⟩ := happrox x hx
  have hlim := (continuous_coefficientPolynomial_eval (d + 1)).continuousAt.tendsto.comp
    (hc.prodMk_nhds hvlim)
  have hlim' : Tendsto (fun n => (p n).eval (v n)) l
      (nhds ((coefficientPolynomial c₀).eval x)) := by
    change Tendsto (fun n => (coefficientPolynomial (c n)).eval (v n)) l
      (nhds ((coefficientPolynomial c₀).eval x)) at hlim
    simpa only [hrec] using hlim
  exact tendsto_nhds_unique hlim' (hvalues x hx v hv hvlim)

open Metric

omit [l.NeBot] in
lemma HasStrictDerivAt.moving_quotient_limit_filter {f : ℝ → ℝ} {x df d : ℝ}
    (hf : HasStrictDerivAt f df x) (u v ε : ι → ℝ)
    (hu : Tendsto u l (nhds x)) (hv : Tendsto v l (nhds x))
    (hε : ∀ᶠ n in l, ε n ≠ 0)
    (hd : Tendsto (fun n => (u n - v n) / ε n) l (nhds d)) :
    Tendsto (fun n => (f (u n) - f (v n)) / ε n) l (nhds (df * d)) := by
  have hsmall := hf.hasStrictFDerivAt.isLittleO.comp_tendsto (hu.prodMk_nhds hv)
  have hlarge : (fun n => u n - v n) =O[l] ε :=
    Asymptotics.isBigO_of_div_tendsto_nhds
      (hε.mono (fun n hn he => (hn he).elim)) d hd
  have hh := (hsmall.trans_isBigO hlarge).tendsto_div_nhds_zero
  have he : Tendsto (fun n => (f (u n) - f (v n) - df * (u n - v n)) / ε n)
      l (nhds 0) := by
    simpa only [Function.comp_def, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_comm] using hh
  have hs := he.add (hd.const_mul df)
  simp only [zero_add] at hs
  convert! hs using 1
  funext n
  ring

omit [l.NeBot] in
lemma tendsto_product_difference_quotient_filter (a b c d ε : ι → ℝ) (x y A B : ℝ)
    (_ha : Tendsto a l (nhds x)) (hc : Tendsto c l (nhds y))
    (hA : Tendsto (fun n => (a n - b n) / ε n) l (nhds A))
    (hB : Tendsto (fun n => (c n - d n) / ε n) l (nhds B))
    (hb : Tendsto b l (nhds x)) :
    Tendsto (fun n => (a n * c n - b n * d n) / ε n) l (nhds (A * y + x * B)) := by
  have hh := (hA.mul hc).add (hb.mul hB)
  convert! hh using 1
  funext n
  ring

omit filterNonempty in
lemma opposite_reciprocal_limit_filter [l.NeBot] (x₁ x₂ y₁ y₂ δ₁ δ₂ ε : ι → ℝ)
    (z b p dp β : ℝ) (hb : b ≠ 0) (hc : Real.cos (2 * Real.pi * z) ≠ 0)
    (hx₁ : Tendsto x₁ l (nhds z)) (hx₂ : Tendsto x₂ l (nhds z))
    (hy₁ : Tendsto y₁ l (nhds b)) (hy₂ : Tendsto y₂ l (nhds b))
    (hδ₁ : Tendsto δ₁ l (nhds 0)) (hδ₂ : Tendsto δ₂ l (nhds 0))
    (hε : ∀ᶠ n in l, ε n ≠ 0)
    (hp : Tendsto (fun n => (x₂ n - x₁ n) / ε n) l (nhds p))
    (hdp : Tendsto (fun n => (y₂ n - y₁ n) / ε n) l (nhds dp))
    (hs₁ : Tendsto (fun n => δ₁ n / ε n) l (nhds (2 * β)))
    (hs₂ : Tendsto (fun n => δ₂ n / ε n) l (nhds (2 * β))) :
    Tendsto (fun n =>
      (1 / (y₁ n ^ 2 * (Real.cos (2 * Real.pi * x₁ n) + δ₁ n)) +
       1 / (y₂ n ^ 2 * (-Real.cos (2 * Real.pi * x₂ n) + δ₂ n))) / ε n)
      l (nhds ((2 / b * dp * Real.cos (2 * Real.pi * z) -
        2 * Real.pi * p * Real.sin (2 * Real.pi * z) - 4 * β) /
        (b ^ 2 * Real.cos (2 * Real.pi * z) ^ 2))) := by
  let c := Real.cos (2 * Real.pi * z)
  let s := Real.sin (2 * Real.pi * z)
  have hcos : HasStrictDerivAt (fun x : ℝ => Real.cos (2 * Real.pi * x))
      (-2 * Real.pi * s) z := by
    convert! ((hasStrictDerivAt_id z).const_mul (2 * Real.pi)).cos using 1
    dsimp [s]
    ring
  have hcd := HasStrictDerivAt.moving_quotient_limit_filter hcos x₂ x₁ ε hx₂ hx₁ hε hp
  have hc₁ : Tendsto (fun n => Real.cos (2 * Real.pi * x₁ n)) l (nhds c) :=
    Real.continuous_cos.continuousAt.tendsto.comp (hx₁.const_mul (2 * Real.pi))
  have hc₂ : Tendsto (fun n => Real.cos (2 * Real.pi * x₂ n)) l (nhds c) :=
    Real.continuous_cos.continuousAt.tendsto.comp (hx₂.const_mul (2 * Real.pi))
  have hyd : Tendsto (fun n => (y₂ n ^ 2 - y₁ n ^ 2) / ε n) l (nhds (2 * b * dp)) := by
    have hh := (hy₂.add hy₁).mul hdp
    convert! hh using 1
    · funext n; ring
    · ring_nf
  have hprod := tendsto_product_difference_quotient_filter
    (fun n => y₂ n ^ 2) (fun n => y₁ n ^ 2)
    (fun n => Real.cos (2 * Real.pi * x₂ n)) (fun n => Real.cos (2 * Real.pi * x₁ n)) ε
    (b ^ 2) c (2 * b * dp) ((-2 * Real.pi * s) * p)
    (hy₂.pow 2) hc₂ hyd hcd (hy₁.pow 2)
  have hnum : Tendsto (fun n =>
      (y₂ n ^ 2 * (-Real.cos (2 * Real.pi * x₂ n) + δ₂ n) +
       y₁ n ^ 2 * (Real.cos (2 * Real.pi * x₁ n) + δ₁ n)) / ε n) l
      (nhds (-(2 * b * dp * c + b ^ 2 * ((-2 * Real.pi * s) * p)) +
        b ^ 2 * (2 * β) + b ^ 2 * (2 * β))) := by
    have hh := (hprod.neg.add ((hy₂.pow 2).mul hs₂)).add ((hy₁.pow 2).mul hs₁)
    convert! hh using 1
    funext n
    ring
  let a := fun n => y₁ n ^ 2 * (Real.cos (2 * Real.pi * x₁ n) + δ₁ n)
  let d := fun n => y₂ n ^ 2 * (-Real.cos (2 * Real.pi * x₂ n) + δ₂ n)
  have halim : Tendsto a l (nhds (b ^ 2 * c)) := by
    simpa only [add_zero] using (hy₁.pow 2).mul (hc₁.add hδ₁)
  have hdlim : Tendsto d l (nhds (b ^ 2 * -c)) := by
    simpa only [add_zero] using (hy₂.pow 2).mul (hc₂.neg.add hδ₂)
  have haN : b ^ 2 * c ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) hc
  have hdN : b ^ 2 * -c ≠ 0 := mul_ne_zero (pow_ne_zero _ hb) (neg_ne_zero.mpr hc)
  have hlim := hnum.div (halim.mul hdlim) (mul_ne_zero haN hdN)
  have hre : ∀ᶠ n in l, a n ≠ 0 ∧ d n ≠ 0 :=
    (halim.eventually_ne haN).and (hdlim.eventually_ne hdN)
  have heq : (fun n =>
      (1 / a n + 1 / d n) / ε n) =ᶠ[l]
      (fun n => ((d n + a n) / ε n) / (a n * d n)) := by
    filter_upwards [hre] with n hn
    field_simp [hn.1, hn.2]
  have hfinal := hlim.congr' heq.symm
  convert! hfinal using 1
  dsimp [c, s]
  field_simp [hb, hc]
  ring_nf

omit [l.NeBot] in
lemma tendsto_reciprocal_fourth_normalized_filter (r S S₀ S₁ S₁₀ S₂ S₃ S₄ : ι → ℝ)
    (hn : ∀ᶠ n in l, r n ≠ 0 ∧ S n ≠ 0 ∧ S₀ n ≠ 0 ∧ S₁₀ n ≠ 0)
    (hS : Tendsto (fun n => S n / S₀ n) l (nhds 1))
    (h₁ : Tendsto (fun n => S₁ n / S₁₀ n) l (nhds 1))
    (h₂ : Tendsto (fun n => S₀ n * S₂ n / S₁₀ n ^ 2) l (nhds 0))
    (h₃ : Tendsto (fun n => S₀ n ^ 2 * S₃ n / S₁₀ n ^ 3) l (nhds 0))
    (h₄ : Tendsto (fun n => S₀ n ^ 3 * S₄ n / S₁₀ n ^ 4) l (nhds 0)) :
    Tendsto (fun n => ((1 / r n ^ 2) * (24 * S₁ n ^ 4 / S n ^ 5 -
      36 * S₁ n ^ 2 * S₂ n / S n ^ 4 + (6 * S₂ n ^ 2 + 8 * S₁ n * S₃ n) / S n ^ 3 -
      S₄ n / S n ^ 2)) / (S₁₀ n ^ 4 / (r n ^ 2 * S₀ n ^ 5))) l (nhds 24) := by
  have hh := (((h₁.pow 4).const_mul 24).div (hS.pow 5) (by norm_num)).sub
    ((((h₁.pow 2).const_mul 36).mul h₂).div (hS.pow 4) (by norm_num))
  have hh' := (hh.add ((((h₂.pow 2).const_mul 6).add ((h₁.const_mul 8).mul h₃)).div
    (hS.pow 3) (by norm_num))).sub (h₄.div (hS.pow 2) (by norm_num))
  norm_num only [one_pow, mul_one, mul_zero, zero_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_add, add_zero, zero_div, div_one, sub_zero] at hh'
  apply hh'.congr'
  filter_upwards [hn] with n hh
  exact (reciprocal_fourth_normalized _ _ _ _ _ _ _ _ hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).symm

lemma polynomial_extraction_analytic_ratio_filter {d : ℕ}
    (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F) (hm : volume F ≠ 0)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree < d + 1)
    (num den : ℝ → ℝ) (hn : AnalyticOnNhd ℝ num univ)
    (hd : AnalyticOnNhd ℝ den univ) (hdn : ∃ x, den x ≠ 0)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, den x ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l (nhds (num x / den x))) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧ ∀ x : ℝ, P.eval x * den x = num x := by
  let G : Set ℝ := {x ∈ F | den x ≠ 0}
  have hz := analytic_zeros_finite hd hdn hF
  have hG : volume G ≠ 0 := by
    intro hzero
    apply hm
    apply measure_mono_null (t := G ∪ {x ∈ F | den x = 0}) _
      (measure_union_null hzero (hz.measure_zero volume))
    intro x hx
    by_cases h : den x = 0
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, h⟩
  have hi : G.Infinite := by
    intro hh
    exact hG (hh.measure_zero volume)
  obtain ⟨P, hP, he⟩ := polynomial_extraction_filter S G hi p hp (fun x => num x / den x)
    (fun x hx => happrox x hx.1)
    (fun x hx y hy hyr => hvalues x hx.1 hx.2 y hy hyr)
  refine ⟨P, hP, ?_⟩
  have hid := analytic_eq_of_positive_measure
    ((AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) P).mul hd) hn hF
    (show G ⊆ F from fun _ hx => hx.1) hG (fun x hx => by
      rw [he x hx, div_mul_cancel₀ _ hx.2])
  exact fun x => congrFun hid x

omit [l.NeBot] in
lemma successful_polynomial_values_tendsto_filter (S : ι → Set ℝ)
    (p : ι → Polynomial ℝ) (f : ι → ℝ → ℝ) (e : ι → ℝ)
    (he : Tendsto e l (nhds 0))
    (hb : ∀ᶠ n in l, ∀ x ∈ S n, |(p n).eval x - f n x| ≤ e n)
    (x : ι → ℝ) (hx : ∀ n, x n ∈ S n) {z : ℝ}
    (hf : Tendsto (fun n => f n (x n)) l (nhds z)) :
    Tendsto (fun n => (p n).eval (x n)) l (nhds z) := by
  have hh : Tendsto (fun n => (p n).eval (x n) - f n (x n)) l (nhds 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hb] with n hn
    simpa only [Real.norm_eq_abs] using hn (x n) (hx n)
  simpa only [zero_add, sub_add_cancel] using hh.add hf

lemma secant_quartic_limit_null_filter (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (z b a : ℝ) (hb : b ≠ 0)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l
        (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)) + a * x ^ 4))) :
    volume F = 0 := by
  by_contra hm
  let c := fun x => Real.cos (2 * Real.pi * (z + b * x))
  have hc := analytic_affine_cosine z b
  have hn : AnalyticOnNhd ℝ (fun x => 1 + a * x ^ 4 * c x) univ :=
    analyticOnNhd_const.add ((analyticOnNhd_const.mul (analyticOnNhd_id.pow 4)).mul hc)
  have hcn : ∃ x, c x ≠ 0 := by
    refine ⟨-z / b, ?_⟩
    have h : z + b * (-z / b) = 0 := by field_simp; ring
    simp [c, h]
  obtain ⟨P, _, hid⟩ := polynomial_extraction_analytic_ratio_filter S F hF hm p
    (fun n => Nat.lt_succ_of_le (hp n)) (fun x => 1 + a * x ^ 4 * c x) c hn hc hcn
    happrox (fun x hx hcx y hy hyr => by
      have hh := hvalues x hx hcx y hy hyr
      have hr : (1 + a * x ^ 4 * c x) / c x = 1 / c x + a * x ^ 4 := by
        field_simp
      rw [hr]
      exact hh)
  have ht := hid ((1 / 4 - z) / b)
  have hz : c ((1 / 4 - z) / b) = 0 := by
    have h : 2 * Real.pi * (z + b * ((1 / 4 - z) / b)) = Real.pi / 2 := by
      field_simp; ring
    dsimp [c]
    rw [h, Real.cos_pi_div_two]
  rw [hz, mul_zero, mul_zero, add_zero] at ht
  norm_num at ht

end

lemma analyticAt_iteratedDeriv {f : ℝ → ℝ} {x : ℝ} (hf : AnalyticAt ℝ f x) (p : ℕ) :
    AnalyticAt ℝ (iteratedDeriv p f) x := by
  induction p with
  | zero => simpa only [iteratedDeriv_zero] using hf
  | succ p ih => simpa only [iteratedDeriv_succ] using ih.deriv

lemma analytic_derivative_variation {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc (-1) 1)) (p : ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ y ∈ Icc (-1) 1, |iteratedDeriv (p + 1) f y| ≤ C)
    {x : ℝ} (hx : |x| ≤ 1) :
    |iteratedDeriv p f x - iteratedDeriv p f 0| ≤ C := by
  have hh := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le
    (f := iteratedDeriv p f)
    (fun y hy => (analyticAt_iteratedDeriv (hf y hy) p).differentiableAt)
    (fun y hy => by simpa only [Real.norm_eq_abs, ← iteratedDeriv_succ] using hb y hy)
    (by norm_num : (0 : ℝ) ∈ Icc (-1) 1) (abs_le.mp hx)
  simp only [Real.norm_eq_abs, sub_zero] at hh
  exact hh.trans (mul_le_of_le_one_right hC hx)

lemma analytic_cubic_lagrange {f : ℝ → ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc (-1) 1)) {x : ℝ} (hx : |x| ≤ 1) :
    ∃ y ∈ Icc (-1 : ℝ) 1,
      f x - (taylorPolynomialAtZero f 3).eval x = iteratedDeriv 4 f y * x ^ 4 / 24 := by
  by_cases hz : x = 0
  · subst x
    exact ⟨0, by norm_num, by simp [taylorPolynomialAtZero_eval_zero]⟩
  have hs : uIcc (0 : ℝ) x ⊆ Icc (-1) 1 := by
    rw [uIcc]
    exact Icc_subset_Icc (le_min (by norm_num) (abs_le.mp hx).1)
      (max_le (by norm_num) (abs_le.mp hx).2)
  obtain ⟨y, hy, he⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := 3)
    (Ne.symm hz) (hf.mono hs).contDiffOn_of_completeSpace
  refine ⟨y, hs ⟨hy.1.le, hy.2.le⟩, ?_⟩
  have hp := taylorPolynomialAtZero_eval_eq f 3 (uniqueDiffOn_uIcc (Ne.symm hz))
    (left_mem_uIcc : (0 : ℝ) ∈ uIcc 0 x) (hf 0 (by norm_num)) x
  rw [hp, he]
  norm_num

lemma tendsto_cubic_remainder_of_fourth {ι : Type*} {l : Filter ι}
    (f : ι → ℝ → ℝ) (a x : ι → ℝ) (A x₀ : ℝ)
    (hf : ∀ᶠ n in l, AnalyticOnNhd ℝ (f n) (Icc (-1) 1))
    (hx : ∀ n, |x n| ≤ 1) (hx0 : Tendsto x l (nhds x₀))
    (hd : ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) →
      Tendsto (fun n => iteratedDeriv 4 (f n) (y n) / a n) l (nhds A)) :
    Tendsto (fun n => (f n (x n) - (taylorPolynomialAtZero (f n) 3).eval (x n)) / a n)
      l (nhds (A * x₀ ^ 4 / 24)) := by
  classical
  have he : ∀ n, AnalyticOnNhd ℝ (f n) (Icc (-1) 1) →
      ∃ y ∈ Icc (-1 : ℝ) 1,
        f n (x n) - (taylorPolynomialAtZero (f n) 3).eval (x n) =
          iteratedDeriv 4 (f n) y * x n ^ 4 / 24 :=
    fun n hn => analytic_cubic_lagrange hn (hx n)
  let y := fun n => if hn : AnalyticOnNhd ℝ (f n) (Icc (-1) 1) then (he n hn).choose else 0
  have hy : ∀ n, |y n| ≤ 1 := by
    intro n
    dsimp [y]
    split_ifs with hn
    · exact abs_le.mpr (he n hn).choose_spec.1
    · norm_num
  have hl := ((hd y hy).mul (hx0.pow 4)).div_const 24
  apply hl.congr'
  filter_upwards [hf] with n hn
  have hh := (he n hn).choose_spec.2
  have hy' : y n = (he n hn).choose := dite_eq_left hn
  calc
    iteratedDeriv 4 (f n) (y n) / a n * x n ^ 4 / 24 =
        (iteratedDeriv 4 (f n) (y n) * x n ^ 4 / 24) / a n := by ring
    _ = (f n (x n) - (taylorPolynomialAtZero (f n) 3).eval (x n)) / a n := by
      exact congrArg (fun z => z / a n) (by simpa only [hy'] using hh.symm)

lemma analytic_iteratedDeriv_inverse {f : ℝ → ℝ} {x : ℝ}
    (hf : AnalyticAt ℝ f x) (hx : f x ≠ 0) (p : ℕ) (hp : p ≤ 4) :
    iteratedDeriv p (fun y => (f y)⁻¹) x =
      scalarReciprocalJet p (fun i => iteratedDeriv i f x) := by
  let s : Set ℝ := {y | AnalyticAt ℝ f y ∧ f y ≠ 0}
  have hs : IsOpen s := by
    apply isOpen_iff_mem_nhds.mpr
    intro y hy
    filter_upwards [hy.1.eventually_analyticAt, hy.1.continuousAt.eventually_ne hy.2] with z hz hn
    exact ⟨hz, hn⟩
  have hh := iteratedDeriv_of_jets s hs
    (fun i y => scalarReciprocalJet i (fun j => iteratedDeriv j f y)) 4
    (fun i hi y hy => hasDerivAt_scalarReciprocalJet
      (fun a ha => by
        have hd := ((analyticAt_iteratedDeriv hy.1 a).differentiableAt).hasDerivAt
        simpa only [iteratedDeriv_succ] using hd)
      (by simpa only [iteratedDeriv_zero] using hy.2) i hi) p hp x ⟨hf, hx⟩
  simpa only [scalarReciprocalJet, iteratedDeriv_zero] using hh

lemma analytic_reciprocal_fourth {f : ℝ → ℝ} {x r : ℝ}
    (hf : AnalyticAt ℝ f x) (hx : f x ≠ 0) :
    iteratedDeriv 4 (fun y => 1 / (r ^ 2 * f y)) x =
      (1 / r ^ 2) * (24 * (deriv f x) ^ 4 / (f x) ^ 5 -
        36 * (deriv f x) ^ 2 * iteratedDeriv 2 f x / (f x) ^ 4 +
        (6 * (iteratedDeriv 2 f x) ^ 2 + 8 * deriv f x * iteratedDeriv 3 f x) / (f x) ^ 3 -
        iteratedDeriv 4 f x / (f x) ^ 2) := by
  have he : (fun y => 1 / (r ^ 2 * f y)) = (fun y => (1 / r ^ 2) * (f y)⁻¹) := by
    funext y
    simp [div_eq_mul_inv, mul_comm]
  rw [he, iteratedDeriv_const_mul_field, analytic_iteratedDeriv_inverse hf hx 4 (by omega)]
  simp only [scalarReciprocalJet, inverseJet₄, iteratedDeriv_zero, iteratedDeriv_one,
    div_eq_mul_inv]
  ring

lemma ultrafilter_bounded_limit {ι : Type*} (U : Ultrafilter ι) (f : ι → ℝ)
    {a b : ℝ} (hf : ∀ᶠ n in (U : Filter ι), f n ∈ Icc a b) :
    ∃ x ∈ Icc a b, Tendsto f U (nhds x) := by
  obtain ⟨x, hx, hlim⟩ := (isCompact_Icc : IsCompact (Icc a b)).ultrafilter_le_nhds'
    (U.map f) hf
  exact ⟨x, hx, hlim⟩

section
variable {ι : Type*} {l : Filter ι} [l.NeBot]
lemma polynomial_extraction_analytic_ratio_avoiding {d : ℕ}
    (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F) (hm : volume F ≠ 0)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree < d + 1)
    (num den avoid : ℝ → ℝ) (hn : AnalyticOnNhd ℝ num univ)
    (hd : AnalyticOnNhd ℝ den univ) (ha : AnalyticOnNhd ℝ avoid univ)
    (hdn : ∃ x, den x ≠ 0) (han : ∃ x, avoid x ≠ 0)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, den x ≠ 0 → avoid x ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l (nhds (num x / den x))) :
    ∃ P : Polynomial ℝ, P.natDegree ≤ d ∧ ∀ x : ℝ, P.eval x * den x = num x := by
  have hz := analytic_zeros_finite hd hdn hF
  have hw := analytic_zeros_finite ha han hF
  have hpos : volume {x ∈ F | den x ≠ 0 ∧ avoid x ≠ 0} ≠ 0 := by
    intro he
    apply hm
    apply measure_mono_null (t := {x ∈ F | den x ≠ 0 ∧ avoid x ≠ 0} ∪
      ({x ∈ F | den x = 0} ∪ {x ∈ F | avoid x = 0})) _
      (measure_union_null he (measure_union_null (hz.measure_zero volume) (hw.measure_zero volume)))
    intro x hx
    by_cases hd0 : den x = 0
    · exact Or.inr (Or.inl ⟨hx, hd0⟩)
    by_cases ha0 : avoid x = 0
    · exact Or.inr (Or.inr ⟨hx, ha0⟩)
    exact Or.inl ⟨hx, hd0, ha0⟩
  have hprod : ∃ x, den x * avoid x ≠ 0 := by
    obtain ⟨x, hx, hd0, ha0⟩ := nonempty_of_measure_ne_zero hpos
    exact ⟨x, mul_ne_zero hd0 ha0⟩
  obtain ⟨P, hP, hid⟩ := polynomial_extraction_analytic_ratio_filter S F hF hm p hp
    (fun x => num x * avoid x) (fun x => den x * avoid x) (hn.mul ha) (hd.mul ha)
    hprod happrox (fun x hx hh y hy hyr => by
      obtain ⟨hdx, hax⟩ := mul_ne_zero_iff.mp hh
      simpa only [mul_div_mul_right _ _ hax] using hvalues x hx hdx hax y hy hyr)
  refine ⟨P, hP, ?_⟩
  have he := analytic_eq_of_positive_measure
    ((AnalyticOnNhd.eval_polynomial (𝕜 := ℝ) P).mul hd) hn hF
    (show {x ∈ F | den x ≠ 0 ∧ avoid x ≠ 0} ⊆ F from fun _ hx => hx.1)
    hpos (fun x hx => by
      have hh := hid x
      rw [← mul_assoc] at hh
      exact mul_right_cancel₀ hx.2.2 hh)
  exact fun x => congrFun he x

lemma affine_reciprocal_limit_null_avoiding (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (a b : ℝ) (hb : b ≠ 0) (avoid : ℝ → ℝ)
    (ha : AnalyticOnNhd ℝ avoid univ) (han : ∃ x, avoid x ≠ 0)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, a + b * x ≠ 0 → avoid x ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l (nhds (1 / (a + b * x)))) :
    volume F = 0 := by
  by_contra hm
  have hdn : ∃ x, a + b * x ≠ 0 := by
    refine ⟨(1 - a) / b, ?_⟩
    have he : a + b * ((1 - a) / b) = 1 := by field_simp; ring
    rw [he]
    norm_num
  obtain ⟨P, _, hid⟩ := polynomial_extraction_analytic_ratio_avoiding S F hF hm p
    (fun n => Nat.lt_succ_of_le (hp n)) (fun _ => 1) (fun x => a + b * x)
    avoid analyticOnNhd_const (analyticOnNhd_const.add (analyticOnNhd_const.mul analyticOnNhd_id))
    ha hdn han happrox hvalues
  exact polynomial_reciprocal_affine_obstruction P a b hb hid

lemma quartic_limit_null_avoiding (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (avoid : ℝ → ℝ) (ha : AnalyticOnNhd ℝ avoid univ) (han : ∃ x, avoid x ≠ 0)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hvalues : ∀ x ∈ F, avoid x ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l (nhds (x ^ 4))) :
    volume F = 0 := by
  by_contra hm
  obtain ⟨P, hP, hid⟩ := polynomial_extraction_analytic_ratio_avoiding S F hF hm p
    (fun n => Nat.lt_succ_of_le (hp n)) (fun x => x ^ 4) (fun _ => 1)
    avoid (analyticOnNhd_id.pow 4) analyticOnNhd_const ha ⟨0, by norm_num⟩ han happrox
    (fun x hx _ hh y hy hyr => by simpa only [div_one] using hvalues x hx hh y hy hyr)
  apply polynomial_quartic_obstruction P hP
  exact fun x => by simpa only [mul_one] using hid x
end

lemma ultrafilter_scaled_limit {ι : Type*} (U : Ultrafilter ι) (f r : ι → ℝ)
    (p : ℕ) (C : ℝ) (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hb : ∀ᶠ n in (U : Filter ι), |f n| ≤ C * r n ^ p) :
    ∃ a ∈ Icc (-C) C, Tendsto (fun n => f n / r n ^ p) U (nhds a) := by
  apply ultrafilter_bounded_limit U
  filter_upwards [hr, hb] with n hn hb
  apply abs_le.mp
  rw [abs_div, abs_of_pos (pow_pos hn _), div_le_iff₀ (pow_pos hn _)]
  exact hb

lemma ultrafilter_real_alternative {ι : Type*} (U : Ultrafilter ι) (f : ι → ℝ) :
    (∃ a : ℝ, Tendsto f U (nhds a)) ∨
      (Tendsto (fun n => 1 / f n) U (nhds 0) ∧ ∀ᶠ n in (U : Filter ι), f n ≠ 0) := by
  by_cases hb : ∃ C : ℝ, ∀ᶠ n in (U : Filter ι), |f n| ≤ C
  · obtain ⟨C, hC⟩ := hb
    obtain ⟨a, _, ha⟩ := ultrafilter_bounded_limit U f (hC.mono fun _ hh => abs_le.mp hh)
    exact Or.inl ⟨a, ha⟩
  right
  have hh : ∀ C : ℝ, ∀ᶠ n in (U : Filter ι), C < |f n| := by
    intro C
    have hn : ¬∀ᶠ n in (U : Filter ι), |f n| ≤ C := fun h => hb ⟨C, h⟩
    simpa only [not_le] using (U.eventually_not.mpr hn)
  refine ⟨?_, (hh 0).mono fun n hn => abs_pos.mp hn⟩
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hh (1 / ε)] with n hn
  rw [Real.dist_eq, sub_zero, abs_div, abs_one]
  have hp : 0 < |f n| := lt_trans (one_div_pos.mpr hε) hn
  exact (div_lt_iff₀ hp).mpr (by simpa only [mul_comm] using (div_lt_iff₀ hε).mp hn)

lemma reciprocal_fourth_scaled_identity (r S a b c d : ℝ) (hr : r ≠ 0) :
    (1 / r ^ 2) * (24 * a ^ 4 / S ^ 5 - 36 * a ^ 2 * b / S ^ 4 +
      (6 * b ^ 2 + 8 * a * c) / S ^ 3 - d / S ^ 2) =
    r ^ 2 * (24 * (a / r) ^ 4 / S ^ 5 -
      36 * (a / r) ^ 2 * (b / r ^ 2) / S ^ 4 +
      (6 * (b / r ^ 2) ^ 2 + 8 * (a / r) * (c / r ^ 3)) / S ^ 3 -
      (d / r ^ 4) / S ^ 2) := by
  by_cases hs : S = 0
  · simp [hs]
  field_simp

lemma slow_reciprocal_fourth_vanishes {ι : Type*} (U : Ultrafilter ι)
    (S : ι → ℝ → ℝ) (r y : ι → ℝ) (C s : ℝ)
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hr0 : Tendsto r U (nhds 0)) (hs : s ≠ 0)
    (hy : ∀ n, |y n| ≤ 1)
    (hf : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hb : ∀ᶠ n in (U : Filter ι), ∀ p ∈ Icc 1 4, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv p (S n) x| ≤ C * r n ^ p)
    (hS : Tendsto (fun n => S n (y n)) U (nhds s)) :
    Tendsto (fun n => iteratedDeriv 4 (fun x => 1 / (r n ^ 2 * S n x)) (y n))
      U (nhds 0) := by
  have hd : ∀ p ∈ Icc 1 4, ∃ a ∈ Icc (-C) C,
      Tendsto (fun n => iteratedDeriv p (S n) (y n) / r n ^ p) U (nhds a) := by
    intro p hp
    apply ultrafilter_scaled_limit U _ r p C hr
    filter_upwards [hb] with n hn
    exact hn p hp (y n) (abs_le.mp (hy n))
  obtain ⟨a, _, ha⟩ := hd 1 (by norm_num)
  obtain ⟨b, _, hb⟩ := hd 2 (by norm_num)
  obtain ⟨c, _, hc⟩ := hd 3 (by norm_num)
  obtain ⟨d, _, hd⟩ := hd 4 (by norm_num)
  simp only [iteratedDeriv_one, pow_one] at ha
  have hlim := (hr0.pow 2).mul
    (((((ha.pow 4).const_mul 24).div (hS.pow 5) (pow_ne_zero _ hs)).sub
      ((((ha.pow 2).const_mul 36).mul hb).div (hS.pow 4) (pow_ne_zero _ hs))).add
        ((((hb.pow 2).const_mul 6).add ((ha.const_mul 8).mul hc)).div (hS.pow 3)
          (pow_ne_zero _ hs)) |>.sub (hd.div (hS.pow 2) (pow_ne_zero _ hs)))
  convert! hlim.congr' ?_ using 1
  · norm_num
  · filter_upwards [hf, hr, hS.eventually_ne hs] with n hf hr hs
    rw [analytic_reciprocal_fourth (hf _ (abs_le.mp (hy n))) hs]
    exact (reciprocal_fourth_scaled_identity _ _ _ _ _ _ hr.ne').symm

section
variable {ι : Type*} (U : Ultrafilter ι) (S : ι → ℝ → ℝ) (r : ι → ℝ) (C : ℝ)

lemma slow_no_zeros (hC : 0 ≤ C)
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hf : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hb : ∀ᶠ n in (U : Filter ι), ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 1 (S n) x| ≤ C * r n)
    (hS : ∀ᶠ n in (U : Filter ι), S n 0 ≠ 0)
    (hw : Tendsto (fun n => r n / |S n 0|) U (nhds 0)) :
    ∀ᶠ n in (U : Filter ι), ∀ x ∈ Icc (-1 : ℝ) 1, S n x ≠ 0 := by
  have hl := hw.const_mul C
  rw [mul_zero] at hl
  filter_upwards [hf, hb, hr, hS, hl.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
    with n hf hb hr hS hh
  have hsmall : C * r n < |S n 0| := by
    rw [← mul_div_assoc, div_lt_iff₀ (abs_pos.mpr hS)] at hh
    simpa only [one_mul] using hh
  intro x hx hn
  have hv := analytic_derivative_variation hf 0 (mul_nonneg hC hr.le) hb (abs_le.mpr hx)
  simp only [iteratedDeriv_zero, hn, zero_sub, abs_neg] at hv
  exact (not_lt_of_ge hv) hsmall

lemma slow_relative_value (hC : 0 ≤ C) (y : ι → ℝ) (hy : ∀ n, |y n| ≤ 1)
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hf : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hb : ∀ᶠ n in (U : Filter ι), ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 1 (S n) x| ≤ C * r n)
    (hS : ∀ᶠ n in (U : Filter ι), S n 0 ≠ 0)
    (hw : Tendsto (fun n => r n / |S n 0|) U (nhds 0)) :
    Tendsto (fun n => S n (y n) / S n 0) U (nhds 1) := by
  have hv : ∀ᶠ n in (U : Filter ι), |S n (y n) - S n 0| ≤ C * r n ^ 1 := by
    filter_upwards [hf, hb, hr] with n hf hb hr
    simpa only [iteratedDeriv_zero, pow_one] using
      analytic_derivative_variation hf 0 (mul_nonneg hC hr.le) hb (hy n)
  obtain ⟨a, _, ha⟩ := ultrafilter_scaled_limit U _ r 1 C hr hv
  simp only [pow_one] at ha
  have hw' : Tendsto (fun n => r n / S n 0) U (nhds 0) := by
    apply squeeze_zero_norm' _ hw
    filter_upwards [hr] with n hr
    simp only [Real.norm_eq_abs, abs_div, abs_of_pos hr, le_refl]
  have hlim := (ha.mul hw').add_const 1
  simp only [mul_zero, zero_add] at hlim
  apply hlim.congr'
  filter_upwards [hr, hS] with n hr hs
  field_simp
  ring

lemma slow_relative_fourth (hC : 0 ≤ C) (y : ι → ℝ) (hy : ∀ n, |y n| ≤ 1)
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hr0 : Tendsto r U (nhds 0))
    (hf : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hb : ∀ᶠ n in (U : Filter ι), ∀ p ∈ Icc 1 4, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv p (S n) x| ≤ C * r n ^ p)
    (hS : ∀ᶠ n in (U : Filter ι), S n 0 ≠ 0)
    (hS0 : Tendsto (fun n => S n 0) U (nhds 0))
    (hw : Tendsto (fun n => r n / |S n 0|) U (nhds 0))
    (hd : Tendsto (fun n => |deriv (S n) 0| / r n) U (nhds (2 * Real.pi))) :
    Tendsto (fun n => iteratedDeriv 4 (fun x => 1 / (r n ^ 2 * S n x)) (y n) /
      ((deriv (S n) 0) ^ 4 / (r n ^ 2 * S n 0 ^ 5))) U (nhds 24) := by
  have hb1 : ∀ᶠ n in (U : Filter ι), ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 1 (S n) x| ≤ C * r n := by
    filter_upwards [hb] with n hn x hx
    simpa only [pow_one] using hn 1 (by norm_num) x hx
  have hrel := slow_relative_value U S r C hC y hy hr hf hb1 hS hw
  have hzn := slow_no_zeros U S r C hC hr hf hb1 hS hw
  obtain ⟨b, _, hb0⟩ := ultrafilter_scaled_limit U (fun n => deriv (S n) 0) r 1 C hr (by
    filter_upwards [hb1] with n hn
    simpa only [pow_one, iteratedDeriv_one] using hn 0 (by norm_num))
  simp only [pow_one] at hb0
  have hab : |b| = 2 * Real.pi := by
    apply tendsto_nhds_unique (hb0.abs) ?_
    apply hd.congr'
    filter_upwards [hr] with n hr
    simp only [abs_div, abs_of_pos hr]
  have hbn : b ≠ 0 := by intro hh; simp only [hh, abs_zero] at hab; linarith [Real.pi_pos]
  have hdn : ∀ᶠ n in (U : Filter ι), deriv (S n) 0 ≠ 0 :=
    (hb0.eventually_ne hbn).mono fun n hn => fun hz => hn (by simp [hz])
  obtain ⟨a, _, ha⟩ := ultrafilter_scaled_limit U (fun n => deriv (S n) (y n) - deriv (S n) 0)
    r 2 C hr (by
      filter_upwards [hf, hb, hr] with n hf hb hr
      have hh := analytic_derivative_variation hf 1 (mul_nonneg hC (sq_nonneg _))
        (hb 2 (by norm_num)) (hy n)
      simpa only [iteratedDeriv_one] using hh)
  have hrel1 : Tendsto (fun n => deriv (S n) (y n) / deriv (S n) 0) U (nhds 1) := by
    have hl := ((ha.mul hr0).div hb0 hbn).add_const 1
    simp only [mul_zero, zero_div, zero_add] at hl
    apply hl.congr'
    filter_upwards [hr, hdn] with n hr hn
    simp only [Pi.div_apply]
    field_simp [hr.ne', hn]
    ring
  have hhigh : ∀ p ∈ Icc 2 4,
      Tendsto (fun n => (S n 0) ^ (p-1) * iteratedDeriv p (S n) (y n) /
        (deriv (S n) 0) ^ p) U (nhds 0) := by
    intro p hp
    have hp' : 2 ≤ p := hp.1
    obtain ⟨a, _, ha⟩ := ultrafilter_scaled_limit U (fun n => iteratedDeriv p (S n) (y n))
      r p C hr (by
        filter_upwards [hb] with n hb
        exact hb p ⟨by omega, hp.2⟩ (y n) (abs_le.mp (hy n)))
    have hl := ((hS0.pow (p-1)).mul ha).div (hb0.pow p) (pow_ne_zero _ hbn)
    simp only [zero_pow (by omega : p-1 ≠ 0), zero_mul, zero_div] at hl
    apply hl.congr'
    filter_upwards [hr, hdn] with n hr hn
    simp only [Pi.div_apply, div_pow]
    field_simp [hr.ne', hn]
  have hlim := tendsto_reciprocal_fourth_normalized_filter r (fun n => S n (y n))
    (fun n => S n 0) (fun n => deriv (S n) (y n)) (fun n => deriv (S n) 0)
    (fun n => iteratedDeriv 2 (S n) (y n)) (fun n => iteratedDeriv 3 (S n) (y n))
    (fun n => iteratedDeriv 4 (S n) (y n))
    (by filter_upwards [hr, hzn, hS, hdn] with n hr hn hs hd
        exact ⟨hr.ne', hn _ (abs_le.mp (hy n)), hs, hd⟩)
    hrel hrel1 (by simpa only [Nat.reduceSub, pow_one] using hhigh 2 (by norm_num))
    (by simpa only [Nat.reduceSub] using hhigh 3 (by norm_num))
    (by simpa only [Nat.reduceSub] using hhigh 4 (by norm_num))
  apply hlim.congr'
  filter_upwards [hf, hzn] with n hf hn
  exact (congrArg (fun t => t / ((deriv (S n) 0) ^ 4 / (r n ^ 2 * S n 0 ^ 5)))
    (analytic_reciprocal_fourth (hf _ (abs_le.mp (hy n))) (hn _ (abs_le.mp (hy n))))).symm
end

section
variable {ι : Type*} {l : Filter ι} [l.NeBot]

lemma analytic_affine_cosine_nonzero (z b : ℝ) (hb : b ≠ 0) :
    ∃ x, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 := by
  refine ⟨-z / b, ?_⟩
  have h : z + b * (-z / b) = 0 := by field_simp; ring
  simp [h]

lemma cubic_fast_quartic_null (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (f g : ι → ℝ → ℝ) (e : ι → ℝ) (z b a : ℝ) (hb : b ≠ 0)
    (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y l (nhds x))
    (he : Tendsto e l (nhds 0))
    (hpval : ∀ᶠ n in l, ∀ x ∈ A n, |(p n).eval x - (f n x + g n x)| ≤ e n)
    (hf : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ A n) → Tendsto y l (nhds x) →
      Tendsto (fun n => f n (y n)) l (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)))))
    (hg : ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y l (nhds x) →
      Tendsto (fun n => g n (y n) - (taylorPolynomialAtZero (g n) 3).eval (y n)) l
        (nhds (a * x ^ 4))) :
    volume F = 0 := by
  let P := fun n => p n - taylorPolynomialAtZero (g n) 3
  apply secant_quartic_limit_null_filter A F hF P
    (fun n => (Polynomial.natDegree_sub_le _ _).trans (max_le (hp n) (taylorPolynomialAtZero_degree _ _))) z b a hb happrox
  intro x hx hcx y hy hyr
  have hgy := hg x y (fun n => abs_le.mpr (hA n (hy n))) hyr
  have hfy := hf x hx hcx y hy hyr
  refine successful_polynomial_values_tendsto_filter A P (fun n x => f n x +
    (g n x - (taylorPolynomialAtZero (g n) 3).eval x)) e he ?_ y hy (hfy.add hgy)
  filter_upwards [hpval] with n hn x hx
  convert hn x hx using 1
  simp only [P, Polynomial.eval_sub]
  congr 1
  ring

lemma cubic_pure_quartic_null (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (f g : ι → ℝ → ℝ) (e a : ι → ℝ) (z b : ℝ) (hb : b ≠ 0)
    (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y l (nhds x))
    (he : Tendsto e l (nhds 0))
    (hpval : ∀ᶠ n in l, ∀ x ∈ A n, |(p n).eval x - (f n x + g n x)| ≤ e n)
    (hf : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ A n) → Tendsto y l (nhds x) →
      Tendsto (fun n => f n (y n)) l (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)))))
    (ha : Tendsto (fun n => 1 / a n) l (nhds 0))
    (hg : ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y l (nhds x) →
      Tendsto (fun n => (g n (y n) - (taylorPolynomialAtZero (g n) 3).eval (y n)) / a n) l
        (nhds (x ^ 4))) :
    volume F = 0 := by
  let P := fun n => Polynomial.C (1 / a n) * (p n - taylorPolynomialAtZero (g n) 3)
  have hdeg : ∀ n, (P n).natDegree ≤ 3 := by
    intro n
    apply (Polynomial.natDegree_C_mul_le _ _).trans
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le (hp n) (taylorPolynomialAtZero_degree _ _))
  apply quartic_limit_null_avoiding A F hF P hdeg
    (fun x => Real.cos (2 * Real.pi * (z + b * x))) (analytic_affine_cosine z b)
    (analytic_affine_cosine_nonzero z b hb) happrox
  intro x hx hcx y hy hyr
  have hfy := (hf x hx hcx y hy hyr).mul ha
  rw [mul_zero] at hfy
  have hgy := hg x y (fun n => abs_le.mpr (hA n (hy n))) hyr
  have herr : Tendsto (fun n => ((p n).eval (y n) - (f n (y n) + g n (y n))) / a n) l (nhds 0) := by
    have h0 : Tendsto (fun n => (p n).eval (y n) - (f n (y n) + g n (y n))) l (nhds 0) := by
      apply squeeze_zero_norm' _ he
      filter_upwards [hpval] with n hn
      simpa only [Real.norm_eq_abs] using hn (y n) (hy n)
    simpa only [zero_mul, div_eq_mul_inv, one_div, one_mul] using h0.mul ha
  have hh := (herr.add hfy).add hgy
  rw [zero_add, zero_add] at hh
  apply hh.congr'
  exact Filter.Eventually.of_forall fun n => by
    simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub]
    ring
end

section
variable {ι : Type*} (U : Ultrafilter ι)

lemma slow_almost_constant_scarcity (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (f S : ι → ℝ → ℝ) (r e : ι → ℝ) (z b C : ℝ) (hb : b ≠ 0) (hC : 0 ≤ C)
    (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y U (nhds x))
    (he : Tendsto e U (nhds 0))
    (hpval : ∀ᶠ n in (U : Filter ι), ∀ x ∈ A n,
      |(p n).eval x - (f n x + 1 / (r n ^ 2 * S n x))| ≤ e n)
    (hf : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ A n) → Tendsto y U (nhds x) →
      Tendsto (fun n => f n (y n)) U (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)))))
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hr0 : Tendsto r U (nhds 0))
    (hS : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hbound : ∀ᶠ n in (U : Filter ι), ∀ i ∈ Icc 0 4, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv i (S n) x| ≤ C * r n ^ i)
    (hS0 : ∀ᶠ n in (U : Filter ι), S n 0 ≠ 0)
    (hw : Tendsto (fun n => r n / |S n 0|) U (nhds 0))
    (hslope : Tendsto (fun n => S n 0) U (nhds 0) →
      Tendsto (fun n => |deriv (S n) 0| / r n) U (nhds (2 * Real.pi))) :
    volume F = 0 := by
  let g := fun n x => 1 / (r n ^ 2 * S n x)
  have hbound' : ∀ᶠ n in (U : Filter ι), ∀ i ∈ Icc 1 4, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv i (S n) x| ≤ C * r n ^ i := by
    filter_upwards [hbound] with n hn i hi x hx
    exact hn i ⟨Nat.zero_le _, hi.2⟩ x hx
  have hbound1 : ∀ᶠ n in (U : Filter ι), ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 1 (S n) x| ≤ C * r n := by
    filter_upwards [hbound'] with n hn x hx
    simpa only [pow_one] using hn 1 (by norm_num) x hx
  have hzn := slow_no_zeros U S r C hC hr hS hbound1 hS0 hw
  have hg : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (g n) (Icc (-1) 1) := by
    filter_upwards [hS, hr, hzn] with n hs hr hz
    intro x hx
    exact analyticAt_const.div ((analyticAt_const.mul (hs x hx))) (mul_ne_zero (pow_ne_zero _ hr.ne') (hz x hx))
  obtain ⟨s, _, hs⟩ := ultrafilter_bounded_limit U (fun n => S n 0) (by
    filter_upwards [hbound] with n hn
    have hh := hn 0 (by norm_num) 0 (by norm_num)
    exact abs_le.mp (by simpa only [iteratedDeriv_zero, pow_zero, mul_one] using hh))
  by_cases hs0 : s = 0
  · subst s
    let a := fun n => (deriv (S n) 0) ^ 4 / (r n ^ 2 * S n 0 ^ 5)
    have hd := hslope hs
    have haN : ∀ᶠ n in (U : Filter ι), a n ≠ 0 := by
      filter_upwards [hr, hS0, hd.eventually_ne (by positivity : (2 * Real.pi : ℝ) ≠ 0)] with n hr hs hd
      have hdN : deriv (S n) 0 ≠ 0 := by
        intro hz
        exact hd (by simp [hz])
      exact div_ne_zero (pow_ne_zero _ hdN) (mul_ne_zero (pow_ne_zero _ hr.ne') (pow_ne_zero _ hs))
    have hrem : ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y U (nhds x) →
        Tendsto (fun n => (g n (y n) - (taylorPolynomialAtZero (g n) 3).eval (y n)) / a n)
          U (nhds (x ^ 4)) := by
      intro x y hy hyr
      have hh := tendsto_cubic_remainder_of_fourth g a y 24 x hg hy hyr
        (fun v hv => slow_relative_fourth U S r C hC v hv hr hr0 hS hbound' hS0 hs hw hd)
      convert hh using 1 ; ring_nf
    rcases ultrafilter_real_alternative U a with ⟨a₀, ha₀⟩ | ⟨ha₀, _⟩
    · apply cubic_fast_quartic_null A F hF p hp f g e z b a₀ hb hA happrox he hpval hf
      intro x y hy hyr
      have hh := (hrem x y hy hyr).mul ha₀
      have hlim : Tendsto (fun n => g n (y n) - (taylorPolynomialAtZero (g n) 3).eval (y n)) U
          (nhds (x ^ 4 * a₀)) := by
        apply hh.congr'
        filter_upwards [haN] with n hn
        exact div_mul_cancel₀ _ hn
      simpa only [mul_comm] using hlim
    · exact cubic_pure_quartic_null A F hF p hp f g e a z b hb hA happrox he hpval hf ha₀ hrem
  · apply cubic_fast_quartic_null A F hF p hp f g e z b 0 hb hA happrox he hpval hf
    intro x y hy hyr
    have hder : ∀ v : ι → ℝ, (∀ n, |v n| ≤ 1) →
        Tendsto (fun n => iteratedDeriv 4 (g n) (v n)) U (nhds 0) := by
      intro v hv
      have hrel := slow_relative_value U S r C hC v hv hr hS hbound1 hS0 hw
      have hvS : Tendsto (fun n => S n (v n)) U (nhds s) := by
        have hh := hrel.mul hs
        rw [one_mul] at hh
        apply hh.congr'
        filter_upwards [hS0] with n hn
        exact div_mul_cancel₀ _ hn
      exact slow_reciprocal_fourth_vanishes U S r v C s hr hr0 hs0 hv hS hbound' hvS
    have hh := tendsto_cubic_remainder_of_fourth g (fun _ => 1) y 0 x hg hy hyr
      (fun v hv => by simpa only [div_one] using hder v hv)
    simpa only [div_one, zero_mul, zero_div] using hh
end

lemma analytic_linear_remainder_bound {f : ℝ → ℝ} {C : ℝ}
    (hf : AnalyticOnNhd ℝ f (Icc (-1) 1)) (hC : 0 ≤ C)
    (hb : ∀ y ∈ Icc (-1) 1, |iteratedDeriv 2 f y| ≤ C)
    {x : ℝ} (hx : |x| ≤ 1) : |f x - f 0 - deriv f 0 * x| ≤ C := by
  let g := fun x => f x - f 0 - deriv f 0 * x
  have hg : AnalyticOnNhd ℝ g (Icc (-1) 1) :=
    (hf.sub analyticOnNhd_const).sub (analyticOnNhd_const.mul analyticOnNhd_id)
  have hd (y : ℝ) (hy : y ∈ Icc (-1 : ℝ) 1) :
      HasDerivAt g (deriv f y - deriv f 0) y := by
    convert! (((hf y hy).differentiableAt.hasDerivAt).sub_const (f 0)).sub
      ((hasDerivAt_id y).const_mul (deriv f 0)) using 1 ; simp
  have hh := analytic_derivative_variation hg 0 hC (fun y hy => by
    rw [iteratedDeriv_one, (hd y hy).deriv]
    simpa only [iteratedDeriv_one] using analytic_derivative_variation hf 1 hC hb (abs_le.mpr hy)) hx
  simpa only [iteratedDeriv_zero, g, mul_zero, sub_self, sub_zero] using hh

section
variable {ι : Type*} (U : Ultrafilter ι)
lemma slow_affine_limit (S : ι → ℝ → ℝ) (r w : ι → ℝ) (C lam : ℝ)
    (hC : 0 ≤ C) (hlam : 0 < lam)
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n ∧ r n ≤ w n ∧ |S n 0| ≤ w n)
    (hr0 : Tendsto r U (nhds 0))
    (hl : Tendsto (fun n => r n / w n) U (nhds lam))
    (hS : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hbound : ∀ᶠ n in (U : Filter ι), ∀ i ∈ Icc 1 2, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv i (S n) x| ≤ C * r n ^ i)
    (hslope : Tendsto (fun n => S n 0) U (nhds 0) →
      Tendsto (fun n => |deriv (S n) 0| / r n) U (nhds (2 * Real.pi))) :
    ∃ α β : ℝ, β ≠ 0 ∧ Tendsto w U (nhds 0) ∧
      ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y U (nhds x) →
      Tendsto (fun n => S n (y n) / w n) U (nhds (α + β * x)) := by
  have hw : ∀ᶠ n in (U : Filter ι), 0 < w n := hr.mono fun _ hn => hn.1.trans_le hn.2.1
  have hw0 : Tendsto w U (nhds 0) := by
    have hh := hr0.div hl hlam.ne'
    rw [zero_div] at hh
    apply hh.congr'
    filter_upwards [hr] with n hn
    simp only [Pi.div_apply]
    field_simp [hn.1.ne', (hn.1.trans_le hn.2.1).ne']
  have hS0 : Tendsto (fun n => S n 0) U (nhds 0) := by
    apply squeeze_zero_norm' _ hw0
    exact hr.mono fun _ hn => by simpa only [Real.norm_eq_abs] using hn.2.2
  obtain ⟨α, _, hα⟩ := ultrafilter_scaled_limit U (fun n => S n 0) w 1 1 hw (by
    filter_upwards [hr] with n hn
    simpa only [pow_one, one_mul] using hn.2.2)
  obtain ⟨β, _, hβ⟩ := ultrafilter_scaled_limit U (fun n => deriv (S n) 0) w 1 C hw (by
    filter_upwards [hr, hbound] with n hn hb
    have hh := hb 1 (by norm_num) 0 (by norm_num)
    simp only [iteratedDeriv_one, pow_one] at hh ⊢
    exact hh.trans (mul_le_mul_of_nonneg_left hn.2.1 hC))
  simp only [pow_one] at hα hβ
  have hβabs : |β| = 2 * Real.pi * lam := by
    apply tendsto_nhds_unique hβ.abs
    have hh := (hslope hS0).mul hl
    apply hh.congr'
    filter_upwards [hr] with n hn
    rw [abs_div, abs_of_pos (hn.1.trans_le hn.2.1)]
    field_simp [hn.1.ne']
  have hβne : β ≠ 0 := by
    intro he
    simp only [he, abs_zero] at hβabs
    have : 0 < 2 * Real.pi * lam := by positivity
    linarith
  refine ⟨α, β, hβne, hw0, ?_⟩
  intro x y hy hyr
  obtain ⟨a, _, ha⟩ := ultrafilter_scaled_limit U
    (fun n => S n (y n) - S n 0 - deriv (S n) 0 * y n) r 2 C
    (hr.mono fun _ hn => hn.1) (by
      filter_upwards [hS, hbound] with n hs hb
      exact analytic_linear_remainder_bound hs (mul_nonneg hC (sq_nonneg _))
        (hb 2 (by norm_num)) (hy n))
  have herr := (ha.mul hr0).mul hl
  simp only [mul_zero, zero_mul] at herr
  have hh := herr.add (hα.add (hβ.mul hyr))
  rw [zero_add] at hh
  apply hh.congr'
  filter_upwards [hr] with n hn
  field_simp [hn.1.ne', (hn.1.trans_le hn.2.1).ne']
  ring

lemma slow_affine_scarcity (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (f S : ι → ℝ → ℝ) (r w e : ι → ℝ) (z b C lam : ℝ)
    (hb : b ≠ 0) (hC : 0 ≤ C) (hlam : 0 < lam)
    (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y U (nhds x))
    (he : Tendsto e U (nhds 0))
    (hpval : ∀ᶠ n in (U : Filter ι), ∀ x ∈ A n,
      |(p n).eval x - (f n x + 1 / (r n ^ 2 * S n x))| ≤ e n)
    (hf : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ A n) → Tendsto y U (nhds x) →
      Tendsto (fun n => f n (y n)) U (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)))))
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n ∧ r n ≤ w n ∧ |S n 0| ≤ w n)
    (hr0 : Tendsto r U (nhds 0))
    (hl : Tendsto (fun n => r n / w n) U (nhds lam))
    (hS : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hbound : ∀ᶠ n in (U : Filter ι), ∀ i ∈ Icc 1 2, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv i (S n) x| ≤ C * r n ^ i)
    (hslope : Tendsto (fun n => S n 0) U (nhds 0) →
      Tendsto (fun n => |deriv (S n) 0| / r n) U (nhds (2 * Real.pi))) :
    volume F = 0 := by
  obtain ⟨α, β, hβ, hw0, hlim⟩ := slow_affine_limit U S r w C lam hC hlam hr hr0 hl hS hbound hslope
  let P := fun n => Polynomial.C (r n ^ 2 * w n) * p n
  have hdeg : ∀ n, (P n).natDegree ≤ 3 :=
    fun n => (Polynomial.natDegree_C_mul_le _ _).trans (hp n)
  apply affine_reciprocal_limit_null_avoiding A F hF P hdeg α β hβ
    (fun x => Real.cos (2 * Real.pi * (z + b * x))) (analytic_affine_cosine z b)
    (analytic_affine_cosine_nonzero z b hb) happrox
  intro x hx hαβ hcos y hy hyr
  have hsy := hlim x y (fun n => abs_le.mpr (hA n (hy n))) hyr
  have hscale := (hr0.pow 2).mul hw0
  simp only [mul_zero] at hscale
  have herr : Tendsto (fun n => (p n).eval (y n) -
      (f n (y n) + 1 / (r n ^ 2 * S n (y n)))) U (nhds 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hpval] with n hn
    simpa only [Real.norm_eq_abs] using hn (y n) (hy n)
  have hh := (hscale.mul (herr.add (hf x hx hcos y hy hyr))).add ((tendsto_const_nhds (x := (1 : ℝ))).div hsy hαβ)
  simp only [zero_mul, zero_add] at hh
  apply hh.congr'
  filter_upwards [hr, hsy.eventually_ne hαβ] with n hn hsn
  have hsN : S n (y n) ≠ 0 := by intro hz; apply hsn; simp [hz]
  simp only [P, Polynomial.eval_mul, Polynomial.eval_C, Pi.div_apply]
  field_simp [hn.1.ne', (hn.1.trans_le hn.2.1).ne', hsN]
  ring
end

variable {ι : Type*} (U : Ultrafilter ι)

lemma vanishing_slope_scarcity (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (f S : ι → ℝ → ℝ) (r e : ι → ℝ) (z b C : ℝ) (hb : b ≠ 0) (hC : 0 ≤ C)
    (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y U (nhds x))
    (he : Tendsto e U (nhds 0))
    (hpval : ∀ᶠ n in (U : Filter ι), ∀ x ∈ A n,
      |(p n).eval x - (f n x + 1 / (r n ^ 2 * S n x))| ≤ e n)
    (hf : ∀ x ∈ F, Real.cos (2 * Real.pi * (z + b * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ A n) → Tendsto y U (nhds x) →
      Tendsto (fun n => f n (y n)) U (nhds (1 / Real.cos (2 * Real.pi * (z + b * x)))))
    (hr : ∀ᶠ n in (U : Filter ι), 0 < r n)
    (hr0 : Tendsto r U (nhds 0))
    (hS : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (S n) (Icc (-1) 1))
    (hbound : ∀ᶠ n in (U : Filter ι), ∀ i ∈ Icc 0 4, ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv i (S n) x| ≤ C * r n ^ i)
    (hslope : Tendsto (fun n => S n 0) U (nhds 0) →
      Tendsto (fun n => |deriv (S n) 0| / r n) U (nhds (2 * Real.pi))) :
    volume F = 0 := by
  let w := fun n => max |S n 0| (r n)
  have hw : ∀ᶠ n in (U : Filter ι), 0 < w n :=
    hr.mono fun _ hn => hn.trans_le (le_max_right _ _)
  obtain ⟨lam, hlam, hl⟩ := ultrafilter_bounded_limit U (fun n => r n / w n) (by
    filter_upwards [hr, hw] with n hn hw
    have hp := (div_pos hn hw).le
    have hu : r n / w n ≤ 1 := (div_le_one hw).mpr (le_max_right _ _)
    exact ⟨(by linarith : (-1 : ℝ) ≤ r n / w n), hu⟩)
  have hlam0 : 0 ≤ lam := ge_of_tendsto hl (hr.and hw |>.mono fun _ hn => (div_pos hn.1 hn.2).le)
  by_cases hlamz : lam = 0
  · subst lam
    have heq : ∀ᶠ n in (U : Filter ι), w n = |S n 0| ∧ S n 0 ≠ 0 := by
      filter_upwards [hr, hw, hl.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
        with n hn hw hl
      have hlt : r n < w n := (div_lt_one hw).mp hl
      have he : w n = |S n 0| := by
        dsimp [w] at hlt ⊢
        exact max_eq_left (le_of_lt ((lt_max_iff.mp hlt).resolve_right (lt_irrefl _)))
      refine ⟨he, abs_pos.mp ?_⟩
      rw [← he]
      exact hw
    have hS0 := heq.mono fun _ hn => hn.2
    have hl' : Tendsto (fun n => r n / |S n 0|) U (nhds 0) := by
      apply hl.congr'
      exact heq.mono fun n hn => by change r n / w n = r n / |S n 0|; rw [hn.1]
    exact slow_almost_constant_scarcity U A F hF p hp f S r e z b C hb hC hA happrox
      he hpval hf hr hr0 hS hbound hS0 hl' hslope
  · apply slow_affine_scarcity U A F hF p hp f S r w e z b C lam hb hC
      (lt_of_le_of_ne hlam0 (Ne.symm hlamz)) hA happrox he hpval hf
      (hr.mono fun n hn => ⟨hn, le_max_right _ _, le_max_left _ _⟩) hr0 hl hS _ hslope
    filter_upwards [hbound] with n hn i hi x hx
    exact hn i ⟨Nat.zero_le _, le_trans hi.2 (by norm_num)⟩ x hx

end StandardMapEntropy
open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma two_secants_affine_polynomial_limit (p : Polynomial ℝ) (z₁ z₂ b₁ b₂ A B : ℝ)
    (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hle : |b₂| ≤ |b₁|) (hA : 0 < A) (hB : 0 < B)
    (hid : ∀ x : ℝ,
      p.eval x * Real.cos (2 * Real.pi * (z₁ + b₁ * x)) *
        Real.cos (2 * Real.pi * (z₂ + b₂ * x)) =
      A * Real.cos (2 * Real.pi * (z₂ + b₂ * x)) +
      B * Real.cos (2 * Real.pi * (z₁ + b₁ * x))) :
    |b₂| = |b₁| ∧ A = B ∧ ∀ x : ℝ,
      Real.cos (2 * Real.pi * (z₂ + b₂ * x)) = -Real.cos (2 * Real.pi * (z₁ + b₁ * x)) := by
  let q := p.comp ((Polynomial.X - Polynomial.C z₁) * Polynomial.C (1 / b₁))
  let a := z₂ - b₂ * z₁ / b₁
  let r := b₂ / b₁
  have hr : r ≠ 0 := div_ne_zero hb₂ hb₁
  have hle' : |r| ≤ 1 := by
    dsimp [r]
    rw [abs_div, div_le_one (abs_pos.mpr hb₁)]
    exact hle
  have hh : ∀ x : ℝ,
      q.eval x * Real.cos (2 * Real.pi * x) * Real.cos (2 * Real.pi * (a + r * x)) =
      A * Real.cos (2 * Real.pi * (a + r * x)) + B * Real.cos (2 * Real.pi * x) := by
    intro x
    have h₁ : z₁ + b₁ * ((x - z₁) / b₁) = x := by field_simp; ring
    have h₂ : z₂ + b₂ * ((x - z₁) / b₁) = a + r * x := by dsimp [a, r]; ring
    simpa only [q, Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, ← div_eq_mul_one_div, h₁, h₂] using hid ((x - z₁) / b₁)
  obtain ⟨hmag, hAB, hcos⟩ := two_secants_polynomial_limit q a r A B hr hle' hA hB hh
  refine ⟨?_, hAB, ?_⟩
  · change |b₂ / b₁| = 1 at hmag
    rw [abs_div, div_eq_one_iff_eq (abs_ne_zero.mpr hb₁)] at hmag
    exact hmag
  · intro x
    have he : a + r * (z₁ + b₁ * x) = z₂ + b₂ * x := by
      dsimp [a, r]
      field_simp
      ring
    simpa only [he] using hcos (z₁ + b₁ * x)

lemma analytic_cosine_product_nonzero (z₁ z₂ b₁ b₂ : ℝ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) :
    ∃ x : ℝ, Real.cos (2 * Real.pi * (z₁ + b₁ * x)) *
      Real.cos (2 * Real.pi * (z₂ + b₂ * x)) ≠ 0 := by
  have h₁ : ∃ x : ℝ, Real.cos (2 * Real.pi * (z₁ + b₁ * x)) ≠ 0 := by
    refine ⟨-z₁ / b₁, ?_⟩
    have he : z₁ + b₁ * (-z₁ / b₁) = 0 := by field_simp; ring
    simp [he]
  have h₂ : ∃ x : ℝ, Real.cos (2 * Real.pi * (z₂ + b₂ * x)) ≠ 0 := by
    refine ⟨-z₂ / b₂, ?_⟩
    have he : z₂ + b₂ * (-z₂ / b₂) = 0 := by field_simp; ring
    simp [he]
  have hz₁ := analytic_zeros_finite (analytic_affine_cosine z₁ b₁) h₁ (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  have hz₂ := analytic_zeros_finite (analytic_affine_cosine z₂ b₂) h₂ (isCompact_Icc (a := (-1 : ℝ)) (b := 1))
  by_contra hn
  push Not at hn
  have hs : Icc (-1 : ℝ) 1 ⊆ {x ∈ Icc (-1 : ℝ) 1 | Real.cos (2 * Real.pi * (z₁ + b₁ * x)) = 0} ∪
      {x ∈ Icc (-1 : ℝ) 1 | Real.cos (2 * Real.pi * (z₂ + b₂ * x)) = 0} := by
    intro x hx
    rcases mul_eq_zero.mp (hn x) with h | h
    · exact Or.inl ⟨hx, h⟩
    · exact Or.inr ⟨hx, h⟩
  have hm := measure_mono_null hs (measure_union_null (hz₁.measure_zero volume) (hz₂.measure_zero volume))
  norm_num at hm

section
variable {ι : Type*} {l : Filter ι} [l.NeBot]
lemma two_secants_limit_classification (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (hm : volume F ≠ 0) (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (z₁ z₂ b₁ b₂ A B : ℝ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (hle : |b₂| ≤ |b₁|) (hA : 0 < A) (hB : 0 < B)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hlim : ∀ x ∈ F,
      Real.cos (2 * Real.pi * (z₁ + b₁ * x)) ≠ 0 →
      Real.cos (2 * Real.pi * (z₂ + b₂ * x)) ≠ 0 → ∀ y : ι → ℝ,
      (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => (p n).eval (y n)) l
        (nhds (A / Real.cos (2 * Real.pi * (z₁ + b₁ * x)) +
          B / Real.cos (2 * Real.pi * (z₂ + b₂ * x))))) :
    |b₂| = |b₁| ∧ A = B ∧ ∀ x : ℝ,
      Real.cos (2 * Real.pi * (z₂ + b₂ * x)) = -Real.cos (2 * Real.pi * (z₁ + b₁ * x)) := by
  let c₁ := fun x => Real.cos (2 * Real.pi * (z₁ + b₁ * x))
  let c₂ := fun x => Real.cos (2 * Real.pi * (z₂ + b₂ * x))
  obtain ⟨P, _, hP⟩ := polynomial_extraction_analytic_ratio_filter S F hF hm p
    (d := 3) (fun n => by have := hp n; omega)
    (fun x => A * c₂ x + B * c₁ x) (fun x => c₁ x * c₂ x)
    ((analyticOnNhd_const.mul (analytic_affine_cosine z₂ b₂)).add
      (analyticOnNhd_const.mul (analytic_affine_cosine z₁ b₁)))
    ((analytic_affine_cosine z₁ b₁).mul (analytic_affine_cosine z₂ b₂))
    (analytic_cosine_product_nonzero z₁ z₂ b₁ b₂ hb₁ hb₂) happrox (by
      intro x hx hn y hy hyr
      have hc₁ : c₁ x ≠ 0 := (mul_ne_zero_iff.mp hn).1
      have hc₂ : c₂ x ≠ 0 := (mul_ne_zero_iff.mp hn).2
      have hh := hlim x hx hc₁ hc₂ y hy hyr
      have he : (A * c₂ x + B * c₁ x) / (c₁ x * c₂ x) = A / c₁ x + B / c₂ x := by
        field_simp
      rw [he]
      exact hh)
  apply two_secants_affine_polynomial_limit P z₁ z₂ b₁ b₂ A B hb₁ hb₂ hle hA hB
  intro x
  simpa only [mul_assoc, c₁, c₂] using hP x
end
section
variable {ι : Type*} {l : Filter ι} [l.NeBot]
lemma opposite_cubic_scarcity (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (Q₁ Q₂ D₁ D₂ δ₁ δ₂ : ι → ℝ → ℝ) (ell e : ι → ℝ)
    (A B C β z b : ℝ) (hb : b ≠ 0) (hN : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ β ≠ 0)
    (hell : ∀ᶠ n in l, ell n ≠ 0) (he : Tendsto (fun n => e n / |ell n|) l (nhds 0))
    (hpval : ∀ᶠ n in l, ∀ x ∈ S n,
      |(p n).eval x - (1 / (D₁ n x ^ 2 * (Real.cos (2 * Real.pi * Q₁ n x) + δ₁ n x)) +
       1 / (D₂ n x ^ 2 * (-Real.cos (2 * Real.pi * Q₂ n x) + δ₂ n x)))| ≤ e n)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y l (nhds x))
    (hlim : ∀ x ∈ F, ∀ y : ι → ℝ, (∀ n, y n ∈ S n) → Tendsto y l (nhds x) →
      Tendsto (fun n => Q₁ n (y n)) l (nhds (z + b * x)) ∧
      Tendsto (fun n => Q₂ n (y n)) l (nhds (z + b * x)) ∧
      Tendsto (fun n => D₁ n (y n)) l (nhds b) ∧
      Tendsto (fun n => D₂ n (y n)) l (nhds b) ∧
      Tendsto (fun n => δ₁ n (y n)) l (nhds 0) ∧
      Tendsto (fun n => δ₂ n (y n)) l (nhds 0) ∧
      Tendsto (fun n => (Q₂ n (y n) - Q₁ n (y n)) / ell n) l (nhds (A * x ^ 2 + B * x + C)) ∧
      Tendsto (fun n => (D₂ n (y n) - D₁ n (y n)) / ell n) l (nhds (2 * A * x + B)) ∧
      Tendsto (fun n => δ₁ n (y n) / ell n) l (nhds (2 * β)) ∧
      Tendsto (fun n => δ₂ n (y n) / ell n) l (nhds (2 * β))) :
    volume F = 0 := by
  by_contra hm
  let P : ι → Polynomial ℝ := fun n => Polynomial.C (1 / ell n) * p n
  let c := fun x => Real.cos (2 * Real.pi * (z + b * x))
  let s := fun x => Real.sin (2 * Real.pi * (z + b * x))
  let num := fun x => 2 / b * (2 * A * x + B) * c x -
    2 * Real.pi * (A * x ^ 2 + B * x + C) * s x - 4 * β
  let den := fun x => b ^ 2 * c x ^ 2
  have hn : AnalyticOnNhd ℝ num univ := by
    apply ((analyticOnNhd_const.mul ((analyticOnNhd_const.mul analyticOnNhd_id).add
      analyticOnNhd_const) |>.mul (analytic_affine_cosine z b)).sub ?_).sub analyticOnNhd_const
    exact (analyticOnNhd_const.mul (((analyticOnNhd_const.mul (analyticOnNhd_id.pow 2)).add
      (analyticOnNhd_const.mul analyticOnNhd_id)).add analyticOnNhd_const)).mul (analytic_affine_sine z b)
  have hd : AnalyticOnNhd ℝ den univ := analyticOnNhd_const.mul ((analytic_affine_cosine z b).pow 2)
  have hdn : ∃ x, den x ≠ 0 := by
    refine ⟨-z / b, ?_⟩
    have hh : z + b * (-z / b) = 0 := by field_simp; ring
    simpa [den, c, hh] using pow_ne_zero 2 hb
  obtain ⟨R, _, hR⟩ := polynomial_extraction_analytic_ratio_filter S F hF hm P
    (d := 3) (fun n => by
      change (Polynomial.C (1 / ell n) * p n).natDegree < 4
      have := (Polynomial.natDegree_C_mul_le (1 / ell n) (p n)).trans (hp n)
      omega)
    num den hn hd hdn happrox (by
      intro x hx hden y hy hyr
      have hc : c x ≠ 0 := by
        intro he
        apply hden
        simp [den, he]
      obtain ⟨hQ₁, hQ₂, hD₁, hD₂, hδ₁, hδ₂, hq, hdq, hs₁, hs₂⟩ := hlim x hx y hy hyr
      have hh := opposite_reciprocal_limit_filter
        (fun n => Q₁ n (y n)) (fun n => Q₂ n (y n)) (fun n => D₁ n (y n)) (fun n => D₂ n (y n))
        (fun n => δ₁ n (y n)) (fun n => δ₂ n (y n)) ell (z + b * x) b
        (A * x ^ 2 + B * x + C) (2 * A * x + B) β hb hc
        hQ₁ hQ₂ hD₁ hD₂ hδ₁ hδ₂ hell hq hdq hs₁ hs₂
      apply successful_polynomial_values_tendsto_filter S P
        (fun n x => (1 / (D₁ n x ^ 2 * (Real.cos (2 * Real.pi * Q₁ n x) + δ₁ n x)) +
          1 / (D₂ n x ^ 2 * (-Real.cos (2 * Real.pi * Q₂ n x) + δ₂ n x))) / ell n)
        (fun n => e n / |ell n|) he _ y hy hh
      filter_upwards [hpval] with n hn x hx
      simpa only [P, Polynomial.eval_mul, Polynomial.eval_C, mul_comm (1 / ell n),
        ← div_eq_mul_one_div, ← sub_div, abs_div] using
        div_le_div_of_nonneg_right (hn x hx) (abs_nonneg (ell n)))
  obtain ⟨x, hx⟩ := opposite_limit_obstruction R A B C β z b hb hN
  apply hx
  dsimp [oppositeLimitDifference]
  have hh := hR x
  dsimp [den, num, c, s] at hh
  nlinarith only [hh]
end

lemma coefficientScale_bounds {ι : Type*} (a b c d : ι → ℝ) (n : ι) :
    |a n| ≤ coefficientScale a b c d n ∧ |b n| ≤ coefficientScale a b c d n ∧
    |c n| ≤ coefficientScale a b c d n ∧ d n ≤ coefficientScale a b c d n := by
  dsimp [coefficientScale]
  exact ⟨(le_max_left _ _).trans (le_max_left _ _),
    (le_max_right _ _).trans (le_max_left _ _),
    (le_max_left _ _).trans (le_max_right _ _),
    (le_max_right _ _).trans (le_max_right _ _)⟩

lemma coefficientScale_tendsto {ι : Type*} {l : Filter ι} (a b c d : ι → ℝ)
    (ha : Tendsto a l (nhds 0)) (hb : Tendsto b l (nhds 0))
    (hc : Tendsto c l (nhds 0)) (hd : Tendsto d l (nhds 0)) :
    Tendsto (coefficientScale a b c d) l (nhds 0) := by
  unfold coefficientScale
  simpa only [abs_zero, max_self] using (ha.abs.max hb.abs).max (hc.abs.max hd)

lemma coefficientScale_extract {ι : Type*} (U : Ultrafilter ι) (a b c d : ι → ℝ)
    (hd : ∀ᶠ n in (U : Filter ι), 0 < d n) :
    ∃ A B C β : ℝ, (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ β ≠ 0) ∧
      Tendsto (fun n => a n / coefficientScale a b c d n) U (nhds A) ∧
      Tendsto (fun n => b n / coefficientScale a b c d n) U (nhds B) ∧
      Tendsto (fun n => c n / coefficientScale a b c d n) U (nhds C) ∧
      Tendsto (fun n => d n / coefficientScale a b c d n) U (nhds β) := by
  let ell := coefficientScale a b c d
  have he : ∀ᶠ n in (U : Filter ι), 0 < ell n :=
    hd.mono fun n hn => hn.trans_le (coefficientScale_bounds a b c d n).2.2.2
  have H (f : ι → ℝ) (hf : ∀ᶠ n in (U : Filter ι), |f n| ≤ ell n) :
      ∃ A, Tendsto (fun n => f n / ell n) U (nhds A) := by
    obtain ⟨A, _, hA⟩ := ultrafilter_scaled_limit U f ell 1 1 he (by
      simpa only [pow_one, one_mul] using hf)
    exact ⟨A, by simpa only [pow_one] using hA⟩
  obtain ⟨A, hA⟩ := H a (Eventually.of_forall fun n => (coefficientScale_bounds a b c d n).1)
  obtain ⟨B, hB⟩ := H b (Eventually.of_forall fun n => (coefficientScale_bounds a b c d n).2.1)
  obtain ⟨C, hC⟩ := H c (Eventually.of_forall fun n => (coefficientScale_bounds a b c d n).2.2.1)
  obtain ⟨β, hβ⟩ := H d (hd.mono fun n hn => by
    rw [abs_of_pos hn]; exact (coefficientScale_bounds a b c d n).2.2.2)
  refine ⟨A, B, C, β, ?_, hA, hB, hC, hβ⟩
  have hm := (hA.abs.max hB.abs).max (hC.abs.max hβ)
  have hm' : Tendsto (fun _ : ι => (1 : ℝ)) U (nhds (max (max |A| |B|) (max |C| β))) := by
    apply hm.congr'
    filter_upwards [he] with n hn
    simp only [abs_div, abs_of_pos hn]
    rw [max_div_div_right hn.le, max_div_div_right hn.le, max_div_div_right hn.le]
    exact div_self hn.ne'
  have hmax : max (max |A| |B|) (max |C| β) = 1 := tendsto_nhds_unique hm' tendsto_const_nhds
  by_contra hn
  push Not at hn
  rcases hn with ⟨rfl, rfl, rfl, rfl⟩
  norm_num at hmax

lemma error_tendsto_div_larger {ι : Type*} {l : Filter ι} (e d ell : ι → ℝ)
    (hd : ∀ᶠ n in l, 0 < d n ∧ d n ≤ ell n)
    (he : Tendsto (fun n => e n / d n) l (nhds 0)) :
    Tendsto (fun n => e n / ell n) l (nhds 0) := by
  apply squeeze_zero_norm' _ (by simpa only [abs_zero] using he.abs)
  filter_upwards [hd] with n hn
  rw [Real.norm_eq_abs, abs_div, abs_div, abs_of_pos hn.1, abs_of_pos (hn.1.trans_le hn.2)]
  exact div_le_div_of_nonneg_left (abs_nonneg _) hn.1 hn.2

lemma quadratic_normalization_limit {ι : Type*} (U : Ultrafilter ι)
    (q : ι → ℝ → ℝ) (d e : ι → ℝ)
    (hd : ∀ᶠ n in (U : Filter ι), 0 < d n) (hd0 : Tendsto d U (nhds 0))
    (he : Tendsto (fun n => e n / d n) U (nhds 0))
    (hq : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (q n) (Icc (-1) 1))
    (hb : ∀ᶠ n in (U : Filter ι), 0 ≤ e n ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |iteratedDeriv 3 (q n) x| ≤ e n)
    (hc0 : Tendsto (fun n => q n 0) U (nhds 0))
    (hc1 : Tendsto (fun n => deriv (q n) 0) U (nhds 0))
    (hc2 : Tendsto (fun n => iteratedDeriv 2 (q n) 0) U (nhds 0)) :
    ∃ ell : ι → ℝ, ∃ A B C β : ℝ,
      (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ β ≠ 0) ∧
      (∀ᶠ n in (U : Filter ι), 0 < ell n ∧ d n ≤ ell n) ∧
      Tendsto ell U (nhds 0) ∧ Tendsto (fun n => d n / ell n) U (nhds β) ∧
      ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y U (nhds x) →
      Tendsto (fun n => q n (y n) / ell n) U (nhds (A * x ^ 2 + B * x + C)) ∧
      Tendsto (fun n => deriv (q n) (y n) / ell n) U (nhds (2 * A * x + B)) := by
  let a := fun n => iteratedDeriv 2 (q n) 0 / 2
  let b := fun n => deriv (q n) 0
  let c := fun n => q n 0
  let ell := coefficientScale a b c d
  have ha0 : Tendsto a U (nhds 0) := by simpa only [zero_div] using hc2.div_const 2
  have hell := coefficientScale_tendsto a b c d ha0 hc1 hc0 hd0
  obtain ⟨A, B, C, β, hN, hA, hB, hC, hβ⟩ := coefficientScale_extract U a b c d hd
  have hde : ∀ᶠ n in (U : Filter ι), 0 < d n ∧ d n ≤ ell n :=
    hd.mono fun n hn => ⟨hn, (coefficientScale_bounds a b c d n).2.2.2⟩
  have he' := error_tendsto_div_larger e d ell hde he
  refine ⟨ell, A, B, C, β, hN, hde.mono (fun n hn => ⟨hn.1.trans_le hn.2, hn.2⟩), hell, hβ, ?_⟩
  intro x y hy hyr
  have hrem : ∀ᶠ n in (U : Filter ι),
      |q n (y n) - (c n + b n * y n + a n * y n ^ 2)| ≤ e n / 6 ∧
      |deriv (q n) (y n) - (b n + 2 * a n * y n)| ≤ e n / 2 := by
    filter_upwards [hq, hb] with n hn hb
    have hh := analytic_quadratic_taylor_C1 hn hb.1 hb.2 (hy n)
    dsimp [a, b, c]
    convert hh using 1 ; ring_nf
  have E (f : ι → ℝ) (t : ℝ) (ht : 0 ≤ t)
      (hf : ∀ᶠ n in (U : Filter ι), |f n| ≤ e n / t) :
      Tendsto (fun n => f n / ell n) U (nhds 0) := by
    apply squeeze_zero_norm' _ (show Tendsto (fun n => (e n / ell n) / t) U (nhds 0) by
      simpa only [zero_div] using he'.div_const t)
    filter_upwards [hde, hf] with n hn hh
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (hn.1.trans_le hn.2)]
    calc |f n| / ell n ≤ (e n / t) / ell n := div_le_div_of_nonneg_right hh (hn.1.trans_le hn.2).le
         _ = _ := by ring
  have hqrem := E (fun n => q n (y n) - (c n + b n * y n + a n * y n ^ 2)) 6 (by norm_num)
    (hrem.mono fun _ hn => hn.1)
  have hdrem := E (fun n => deriv (q n) (y n) - (b n + 2 * a n * y n)) 2 (by norm_num)
    (hrem.mono fun _ hn => hn.2)
  constructor
  · have hh := hqrem.add ((hC.add (hB.mul hyr)).add (hA.mul (hyr.pow 2)))
    convert! hh using 1
    · funext n; ring
    · ring_nf
  · have hh := hdrem.add (hB.add ((hA.const_mul 2).mul hyr))
    convert! hh using 1
    · funext n; ring
    · ring_nf
section
variable {ι : Type*} {l : Filter ι}
lemma phase_moving_limit (Q : ι → ℝ → ℝ) (e : ι → ℝ) (z b : ℝ)
    (hQ : ∀ᶠ n in l, AnalyticOnNhd ℝ (Q n) (Icc (-1) 1))
    (hb : ∀ᶠ n in l, 0 ≤ e n ∧ ∀ x ∈ Icc (-1 : ℝ) 1, |iteratedDeriv 2 (Q n) x| ≤ e n)
    (he : Tendsto e l (nhds 0)) (hz : Tendsto (fun n => Q n 0) l (nhds z))
    (hd : Tendsto (fun n => deriv (Q n) 0) l (nhds b))
    (x : ℝ) (y : ι → ℝ) (hy : ∀ n, |y n| ≤ 1) (hyr : Tendsto y l (nhds x)) :
    Tendsto (fun n => Q n (y n)) l (nhds (z + b * x)) ∧
    Tendsto (fun n => deriv (Q n) (y n)) l (nhds b) := by
  have hq : Tendsto (fun n => Q n (y n) - Q n 0 - deriv (Q n) 0 * y n) l (nhds 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hQ, hb] with n hn hb
    simpa only [Real.norm_eq_abs] using analytic_linear_remainder_bound hn hb.1 hb.2 (hy n)
  have hd' : Tendsto (fun n => deriv (Q n) (y n) - deriv (Q n) 0) l (nhds 0) := by
    apply squeeze_zero_norm' _ he
    filter_upwards [hQ, hb] with n hn hb
    simpa only [Real.norm_eq_abs, iteratedDeriv_one] using
      analytic_derivative_variation hn 1 hb.1 hb.2 (hy n)
  constructor
  · convert! hq.add (hz.add (hd.mul hyr)) using 1
    · funext n; ring
    · ring_nf
  · simpa only [sub_add_cancel, zero_add] using hd'.add hd
end

lemma centerPhase_zero_bounds (Q : ℝ → ℝ) : centerPhase Q 0 ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact sub_nonneg.mpr (Int.floor_le _)
  · exact (Int.fract_lt_one (Q 0)).le

lemma centerPhase_cos (Q : ℝ → ℝ) (x : ℝ) :
    Real.cos (2 * Real.pi * centerPhase Q x) = Real.cos (2 * Real.pi * Q x) := by
  have he : 2 * Real.pi * centerPhase Q x = 2 * Real.pi * Q x - (⌊Q 0⌋ : ℝ) * (2 * Real.pi) := by
    dsimp [centerPhase]; ring
  rw [he, Real.cos_sub_int_mul_two_pi]

lemma analytic_centerPhase {Q : ℝ → ℝ} {s : Set ℝ} (hQ : AnalyticOnNhd ℝ Q s) :
    AnalyticOnNhd ℝ (centerPhase Q) s := hQ.sub analyticOnNhd_const

lemma centerPhase_iteratedDeriv (Q : ℝ → ℝ) {i : ℕ} (hi : 1 ≤ i) :
    iteratedDeriv i (centerPhase Q) = iteratedDeriv i Q := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [show 1 + j = j + 1 by omega, iteratedDeriv_succ']
  have hd : deriv (centerPhase Q) = deriv Q := by
    funext x
    exact deriv_sub_const _
  rw [hd, ← iteratedDeriv_succ']

lemma opposite_phase_change (z₁ z₂ b₁ b₂ : ℝ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0)
    (hmag : |b₂| = |b₁|)
    (hopp : ∀ x, Real.cos (2 * Real.pi * (z₂ + b₂ * x)) = -Real.cos (2 * Real.pi * (z₁ + b₁ * x))) :
    (b₁ / b₂) ^ 2 = 1 ∧ ∀ u, Real.cos (2 * Real.pi * u) =
      -Real.cos (2 * Real.pi * (z₁ + (b₁ / b₂) * (u - z₂))) := by
  constructor
  · have hh : |b₁ / b₂| = 1 := by rw [abs_div, hmag, div_self (abs_ne_zero.mpr hb₁)]
    nlinarith [sq_abs (b₁ / b₂)]
  · intro u
    have he : z₂ + b₂ * ((u - z₂) / b₂) = u := by field_simp; ring
    have he' : z₁ + b₁ * ((u - z₂) / b₂) = z₁ + (b₁ / b₂) * (u - z₂) := by ring
    simpa only [he, he'] using hopp ((u - z₂) / b₂)

lemma phaseReciprocal_tendsto {ι : Type*} {l : Filter ι}
    (Q E : ι → ℝ → ℝ) (d y : ι → ℝ) (z b : ℝ) (hb : b ≠ 0)
    (hc : Real.cos (2 * Real.pi * z) ≠ 0)
    (hq : Tendsto (fun n => Q n (y n)) l (nhds z))
    (hdq : Tendsto (fun n => deriv (Q n) (y n)) l (nhds b))
    (hE : Tendsto (fun n => E n (y n)) l (nhds 0))
    (hd : Tendsto d l (nhds 0)) :
    Tendsto (fun n => phaseReciprocal (Q n) (E n) (d n) (y n)) l
      (nhds (1 / (b ^ 2 * Real.cos (2 * Real.pi * z)))) := by
  have hs := ((tendsto_const_nhds (x := (2 : ℝ))).sub hE).mul hd
  have hcos := Real.continuous_cos.continuousAt.tendsto.comp (hq.const_mul (2 * Real.pi))
  have H := (tendsto_const_nhds (x := (1 : ℝ))).div ((hdq.pow 2).mul (hcos.add hs))
      (by simpa only [sub_zero, mul_zero, add_zero] using mul_ne_zero (pow_ne_zero 2 hb) hc)
  convert! H using 1 ; simp only [sub_zero, mul_zero, add_zero]

lemma positive_slope_scarcity {ι : Type*} (U : Ultrafilter ι)
    (S : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F)
    (p : ι → Polynomial ℝ) (hp : ∀ n, (p n).natDegree ≤ 3)
    (Q₁ Q₂ E₁ E₂ : ι → ℝ → ℝ) (d e t : ι → ℝ)
    (z₁ z₂ b₁ b₂ : ℝ) (hb₁ : b₁ ≠ 0) (hb₂ : b₂ ≠ 0) (hle : |b₂| ≤ |b₁|)
    (hS : ∀ n, S n ⊆ Icc (-1 : ℝ) 1)
    (hd : ∀ᶠ n in (U : Filter ι), 0 < d n) (hd0 : Tendsto d U (nhds 0))
    (he : Tendsto (fun n => e n / d n) U (nhds 0))
    (ht : Tendsto (fun n => t n / d n) U (nhds 0))
    (hQ : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (Q₁ n) (Icc (-1) 1) ∧
      AnalyticOnNhd ℝ (Q₂ n) (Icc (-1) 1))
    (hc₁ : Tendsto (fun n => iteratedDeriv 2 (Q₁ n) 0) U (nhds 0))
    (hc₂ : Tendsto (fun n => iteratedDeriv 2 (Q₂ n) 0) U (nhds 0))
    (hthird : ∀ᶠ n in (U : Filter ι), 0 ≤ t n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 3 (Q₁ n) x| ≤ t n ∧ |iteratedDeriv 3 (Q₂ n) x| ≤ t n)
    (hphase : ∀ x : ℝ, ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) → Tendsto y U (nhds x) →
      Tendsto (fun n => Q₁ n (y n)) U (nhds (z₁ + b₁ * x)) ∧
      Tendsto (fun n => Q₂ n (y n)) U (nhds (z₂ + b₂ * x)) ∧
      Tendsto (fun n => deriv (Q₁ n) (y n)) U (nhds b₁) ∧
      Tendsto (fun n => deriv (Q₂ n) (y n)) U (nhds b₂))
    (hE : ∀ y : ι → ℝ, (∀ n, |y n| ≤ 1) →
      Tendsto (fun n => E₁ n (y n)) U (nhds 0) ∧ Tendsto (fun n => E₂ n (y n)) U (nhds 0))
    (hpval : ∀ᶠ n in (U : Filter ι), ∀ x ∈ S n,
      |(p n).eval x - (phaseReciprocal (Q₁ n) (E₁ n) (d n) x +
        phaseReciprocal (Q₂ n) (E₂ n) (d n) x)| ≤ e n)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ S n) ∧ Tendsto y U (nhds x)) :
    volume F = 0 := by
  by_contra hm
  have he0 : Tendsto e U (nhds 0) := by
    have hh := he.mul hd0
    rw [zero_mul] at hh
    apply hh.congr'
    filter_upwards [hd] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  obtain ⟨hmag, _, hopp⟩ := two_secants_limit_classification S F hF hm p hp z₁ z₂ b₁ b₂
    (1 / b₁ ^ 2) (1 / b₂ ^ 2) hb₁ hb₂ hle (by positivity) (by positivity) happrox (by
      intro x hx hcos₁ hcos₂ y hy hyr
      have hyy : ∀ n, |y n| ≤ 1 := fun n => abs_le.mpr (hS n (hy n))
      obtain ⟨h₁, h₂, hd₁, hd₂⟩ := hphase x y hyy hyr
      obtain ⟨hE₁, hE₂⟩ := hE y hyy
      have hh := (phaseReciprocal_tendsto Q₁ E₁ d y (z₁ + b₁ * x) b₁ hb₁ hcos₁ h₁ hd₁ hE₁ hd0).add
        (phaseReciprocal_tendsto Q₂ E₂ d y (z₂ + b₂ * x) b₂ hb₂ hcos₂ h₂ hd₂ hE₂ hd0)
      have heq : 1 / (b₁ ^ 2 * Real.cos (2 * Real.pi * (z₁ + b₁ * x))) +
          1 / (b₂ ^ 2 * Real.cos (2 * Real.pi * (z₂ + b₂ * x))) =
          (1 / b₁ ^ 2) / Real.cos (2 * Real.pi * (z₁ + b₁ * x)) +
          (1 / b₂ ^ 2) / Real.cos (2 * Real.pi * (z₂ + b₂ * x)) := by ring
      rw [heq] at hh
      exact successful_polynomial_values_tendsto_filter S p _ e he0 hpval y hy hh)
  let η := b₁ / b₂
  obtain ⟨hηsq, hηcos⟩ := opposite_phase_change z₁ z₂ b₁ b₂ hb₁ hb₂ hmag hopp
  have hηabs : |η| = 1 := by dsimp [η]; rw [abs_div, hmag, div_self (abs_ne_zero.mpr hb₁)]
  have hηb : η * b₂ = b₁ := div_mul_cancel₀ _ hb₂
  let R := fun n x => z₁ - η * z₂ + η * Q₂ n x
  let q := fun n x => z₁ - η * z₂ + (η * Q₂ n x - Q₁ n x)
  have hRder (n : ι) (x : ℝ) : deriv (R n) x = η * deriv (Q₂ n) x := by
    dsimp [R]
    rw [deriv_const_add, deriv_const_mul_field]
  have hqi : ∀ᶠ n in (U : Filter ι), ∀ i : ℕ, 0 < i → ∀ x ∈ Icc (-1 : ℝ) 1,
      iteratedDeriv i (q n) x = η * iteratedDeriv i (Q₂ n) x - iteratedDeriv i (Q₁ n) x := by
    filter_upwards [hQ] with n hn i hi x hx
    dsimp [q]
    rw [iteratedDeriv_const_add hi]
    have hm : AnalyticAt ℝ (fun u => η * Q₂ n u) x := analyticAt_const.mul (hn.2 x hx)
    rw [iteratedDeriv_fun_sub hm.contDiffAt ((hn.1 x hx).contDiffAt)]
    rw [iteratedDeriv_const_mul_field]
  have hq : ∀ᶠ n in (U : Filter ι), AnalyticOnNhd ℝ (q n) (Icc (-1) 1) :=
    hQ.mono fun n hn => analyticOnNhd_const.add ((analyticOnNhd_const.mul hn.2).sub hn.1)
  have hqb : ∀ᶠ n in (U : Filter ι), 0 ≤ 2 * t n ∧ ∀ x ∈ Icc (-1 : ℝ) 1,
      |iteratedDeriv 3 (q n) x| ≤ 2 * t n := by
    filter_upwards [hthird, hqi] with n hn hi
    refine ⟨mul_nonneg (by norm_num) hn.1, fun x hx => ?_⟩
    rw [hi 3 (by norm_num) x hx]
    exact (abs_sub _ _).trans (by rw [abs_mul, hηabs, one_mul]; linarith [(hn.2 x hx).1, (hn.2 x hx).2])
  obtain ⟨h₁₀, h₂₀, hd₁₀, hd₂₀⟩ := hphase 0 (fun _ => 0) (fun _ => by norm_num) tendsto_const_nhds
  simp only [mul_zero, add_zero] at h₁₀ h₂₀
  have hq0 : Tendsto (fun n => q n 0) U (nhds 0) := by
    convert! (tendsto_const_nhds (x := z₁ - η * z₂)).add ((h₂₀.const_mul η).sub h₁₀) using 1 ; ring_nf
  have hq1 : Tendsto (fun n => deriv (q n) 0) U (nhds 0) := by
    have hh := (hd₂₀.const_mul η).sub hd₁₀
    rw [hηb, sub_self] at hh
    apply hh.congr'
    filter_upwards [hqi] with n hn
    simpa only [iteratedDeriv_one] using (hn 1 (by norm_num) 0 (by norm_num)).symm
  have hq2 : Tendsto (fun n => iteratedDeriv 2 (q n) 0) U (nhds 0) := by
    have hh := (hc₂.const_mul η).sub hc₁
    rw [mul_zero, sub_self] at hh
    exact hh.congr' (hqi.mono fun n hn => (hn 2 (by norm_num) 0 (by norm_num)).symm)
  obtain ⟨ell, A, B, C, β, hN, hell, hell0, hβ, hnorm⟩ := quadratic_normalization_limit U q d
    (fun n => 2 * t n) hd hd0 (by simpa only [mul_div_assoc, mul_zero] using ht.const_mul 2)
    hq hqb hq0 hq1 hq2
  apply hm
  refine opposite_cubic_scarcity S F hF p hp Q₁ R (fun n => deriv (Q₁ n)) (fun n => deriv (R n))
    (fun n x => (2 - E₁ n x) * d n) (fun n x => (2 - E₂ n x) * d n) ell e A B C β z₁ b₁ hb₁ hN
    (hell.mono fun _ hn => hn.1.ne') ?_ ?_ happrox ?_
  · have hh := error_tendsto_div_larger e d ell (hd.and hell |>.mono fun _ hn => ⟨hn.1, hn.2.2⟩) he
    apply hh.congr'
    exact hell.mono fun n hn => by simp only [abs_of_pos hn.1]
  · filter_upwards [hpval] with n hn x hx
    convert hn x hx using 1
    dsimp only [phaseReciprocal]
    rw [hRder, mul_pow, hηsq, one_mul]
    have hc : Real.cos (2 * Real.pi * Q₂ n x) = -Real.cos (2 * Real.pi * R n x) := by
      convert hηcos (Q₂ n x) using 2 ; dsimp [R, η] ; ring_nf
    rw [← hc]
  · intro x hx y hy hyr
    have hyy : ∀ n, |y n| ≤ 1 := fun n => abs_le.mpr (hS n (hy n))
    obtain ⟨h₁, h₂, hd₁, hd₂⟩ := hphase x y hyy hyr
    obtain ⟨hE₁, hE₂⟩ := hE y hyy
    obtain ⟨hq', hdq'⟩ := hnorm x y hyy hyr
    have hR : Tendsto (fun n => R n (y n)) U (nhds (z₁ + b₁ * x)) := by
      convert! (tendsto_const_nhds (x := z₁ - η * z₂)).add (h₂.const_mul η) using 1
      rw [mul_add, ← mul_assoc, hηb]; ring_nf
    have hdR : Tendsto (fun n => deriv (R n) (y n)) U (nhds b₁) := by
      simpa only [hηb, hRder] using hd₂.const_mul η
    have hδ₁ := (tendsto_const_nhds (x := (2 : ℝ))).sub hE₁ |>.mul hd0
    have hδ₂ := (tendsto_const_nhds (x := (2 : ℝ))).sub hE₂ |>.mul hd0
    simp only [sub_zero, mul_zero] at hδ₁ hδ₂
    have hs₁ := (tendsto_const_nhds (x := (2 : ℝ))).sub hE₁ |>.mul hβ
    have hs₂ := (tendsto_const_nhds (x := (2 : ℝ))).sub hE₂ |>.mul hβ
    simp only [sub_zero] at hs₁ hs₂
    refine ⟨h₁, hR, hd₁, hdR, hδ₁, hδ₂, ?_, ?_, ?_, ?_⟩
    · convert! hq' using 1
      funext n; dsimp [q, R]; ring
    · apply hdq'.congr'
      filter_upwards [hqi] with n hn
      rw [show deriv (q n) (y n) = η * deriv (Q₂ n) (y n) - deriv (Q₁ n) (y n) by
        simpa only [iteratedDeriv_one] using hn 1 (by norm_num) (y n) (abs_le.mp (hyy n)), hRder]
    · simpa only [mul_div_assoc] using hs₁
    · simpa only [mul_div_assoc] using hs₂

namespace RescaledPath

lemma Admissible.size_pos {P : RescaledPath} (hP : P.Admissible) : 0 < P.size := by
  obtain ⟨b,hg⟩ := hP.2.2.2.2
  exact abs_pos.mpr (hg.t_ne_zero (by linarith [growthBase_ge_four P.k (by linarith [hP.1])]))
lemma Admissible.scale_pos {P : RescaledPath} (hP : P.Admissible) : 0 < P.L := hP.size_pos.trans_le hP.2.2.2.1
lemma Admissible.ratio_bounds {P : RescaledPath} (hP : P.Admissible) : 0 < P.ratio ∧ P.ratio ≤ 1 :=
  ⟨div_pos hP.size_pos hP.scale_pos, (div_le_one hP.scale_pos).mpr hP.2.2.2.1⟩
lemma phase_iteratedDeriv (P : RescaledPath) {i : ℕ} (hi : 1 ≤ i) (x : ℝ) :
    iteratedDeriv i P.phase x = P.sign ^ i *
      iteratedDeriv i (fun h => rescaledOrbit P.k P.q₀ P.θ P.L h P.j) (P.sign * x) := by
  rw [phase, centerPhase_iteratedDeriv _ hi,
    iteratedDeriv_comp_scale i (fun h => rescaledOrbit P.k P.q₀ P.θ P.L h P.j) P.sign]
lemma analytic_phase (P : RescaledPath) : AnalyticOnNhd ℝ P.phase univ :=
  analytic_centerPhase ((analytic_rescaledOrbit P.k P.q₀ P.θ P.L P.j).comp
    (analyticOnNhd_const.mul analyticOnNhd_id) (fun _ _ => mem_univ _))
lemma phase_zero_bounds (P : RescaledPath) : P.phase 0 ∈ Icc (0 : ℝ) 1 := centerPhase_zero_bounds _
lemma phase_deriv_zero (P : RescaledPath) : deriv P.phase 0 =
    P.sign * tSolution (orbitCoefficient P.k P.q₀ P.θ) P.j / P.L := by
  rw [← iteratedDeriv_one, phase_iteratedDeriv P (by norm_num)]
  simp only [pow_one, mul_zero, iteratedDeriv_one, GoodIndex.matched_phase_initial_derivative]
  ring
lemma Admissible.abs_phase_deriv_zero {P : RescaledPath} (hP : P.Admissible) :
    |deriv P.phase 0| = P.ratio := by
  rw [phase_deriv_zero, abs_div, abs_mul, hP.2.2.1, one_mul, abs_of_pos hP.scale_pos]
  rfl
lemma Admissible.phase_derivative_bound {P : RescaledPath} (hP : P.Admissible)
    {x : ℝ} (hx : |x| ≤ 1) {i : ℕ} (hi : 2 ≤ i) (hi' : i ≤ 5) :
    |iteratedDeriv i P.phase x| ≤ 512 * derivativeMajorant * P.ratio ^ i *
      growthBase P.k ^ (1 - (i : ℝ) * goodExponent) := by
  obtain ⟨b,hg⟩ := hP.2.2.2.2
  rw [phase_iteratedDeriv _ (by omega), abs_mul, abs_pow, hP.2.2.1, one_pow, one_mul]
  exact hg.matched_phase_derivative_bound (by linarith [hP.1]) hP.2.1 hP.2.2.2.1
    (by simpa only [abs_mul, hP.2.2.1, one_mul] using hx) hi hi'
lemma Admissible.phase_derivative_bound_coarse {P : RescaledPath} (hP : P.Admissible)
    {x : ℝ} (hx : |x| ≤ 1) {i : ℕ} (hi : 2 ≤ i) (hi' : i ≤ 5) :
    |iteratedDeriv i P.phase x| ≤ 512 * derivativeMajorant *
      growthBase P.k ^ (1 - (i : ℝ) * goodExponent) := by
  apply (hP.phase_derivative_bound hx hi hi').trans
  have hr := pow_le_one₀ hP.ratio_bounds.1.le hP.ratio_bounds.2 (n := i)
  have hM : 0 ≤ growthBase P.k ^ (1 - (i : ℝ) * goodExponent) := Real.rpow_nonneg (by linarith [growthBase_ge_four P.k (by linarith [hP.1])]) _
  have := derivativeMajorant_pos
  calc
    _ ≤ (512 * derivativeMajorant) * 1 * growthBase P.k ^ (1 - (i : ℝ) * goodExponent) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hr (by positivity)) hM
    _ = _ := by ring
lemma Admissible.analytic_quotient {P : RescaledPath} (hP : P.Admissible) :
    AnalyticOnNhd ℝ P.quotient (Icc (-1) 1) := by
  obtain ⟨b,hg⟩ := hP.2.2.2.2
  exact (hg.analytic_matched_quotient (by linarith [hP.1]) hP.2.1 hP.2.2.2.1).comp
    (analyticOnNhd_const.mul analyticOnNhd_id) (fun x hx => by
      apply abs_le.mp
      simpa only [abs_mul, hP.2.2.1, one_mul] using abs_le.mpr hx)
lemma Admissible.quotient_derivative_bound {P : RescaledPath} (hP : P.Admissible)
    {x : ℝ} (hx : |x| ≤ 1) {i : ℕ} (hi : i ≤ 4) :
    |iteratedDeriv i P.quotient x| ≤ 640000 * P.ratio ^ i * growthBase P.k ^ (-goodExponent) := by
  obtain ⟨b,hg⟩ := hP.2.2.2.2
  change |iteratedDeriv i (fun x => terminalQuotient P.k P.q₀ P.θ P.L (P.sign*x) P.j) x| ≤ _
  rw [iteratedDeriv_comp_scale i (fun h => terminalQuotient P.k P.q₀ P.θ P.L h P.j) P.sign, abs_mul, abs_pow, hP.2.2.1, one_pow, one_mul]
  exact hg.matched_quotient_derivative_bound (by linarith [hP.1]) hP.2.1 hP.2.2.2.1
    (by simpa only [abs_mul, hP.2.2.1, one_mul] using hx) hi
lemma Admissible.denominator_model {P : RescaledPath} (hP : P.Admissible) :
    P.denominator = slowDenominatorModel P.phase P.quotient (2 * Real.pi * P.k) P.ratio := by
  funext x
  have hd : deriv P.phase x = P.sign * deriv (fun h => rescaledOrbit P.k P.q₀ P.θ P.L h P.j) (P.sign*x) := by
    simpa only [iteratedDeriv_one, pow_one] using phase_iteratedDeriv P (i := 1) (by norm_num) x
  have hs : P.sign ^ 2 = 1 := by nlinarith [sq_abs P.sign, hP.2.2.1]
  change _ = (deriv P.phase x / P.ratio) ^ 2 * (Real.cos (2 * Real.pi * P.phase x) + (2 - P.quotient x) / (2 * Real.pi * P.k))
  rw [hd]
  simp only [mul_div_assoc, mul_pow, hs, one_mul, phase, centerPhase_cos]
  simp only [denominator, slowDenominator, normalizedSlope, shiftedCosine_eq _ _ _ _ _ _
    (show P.k ≠ 0 by linarith [hP.1]), ratio, size, quotient]
lemma Admissible.analytic_denominator {P : RescaledPath} (hP : P.Admissible) :
    AnalyticOnNhd ℝ P.denominator (Icc (-1) 1) := by
  rw [hP.denominator_model]
  have hc : AnalyticOnNhd ℝ (fun x => Real.cos (2 * Real.pi * P.phase x)) (Icc (-1) 1) :=
    fun x _ => Real.analyticAt_cos.comp (analyticAt_const.mul (P.analytic_phase x (mem_univ _)))
  exact ((P.analytic_phase.deriv.mono (subset_univ _)).div_const.pow 2).mul
    (hc.add ((analyticOnNhd_const.sub hP.analytic_quotient).div_const))
lemma Admissible.denominator_derivative_bound {P : RescaledPath} (hP : P.Admissible)
    {x : ℝ} (hx : |x| ≤ 1) {i : ℕ} (hi : i ≤ 4) :
    |iteratedDeriv i P.denominator x| ≤ (1024 * (640002 + 104 * derivativeMajorant)) * P.ratio ^ i := by
  obtain ⟨b,hg⟩ := hP.2.2.2.2
  change |iteratedDeriv i (fun x => slowDenominator P.k P.q₀ P.θ P.L P.j (P.sign*x)) x| ≤ _
  rw [iteratedDeriv_comp_scale i (slowDenominator P.k P.q₀ P.θ P.L P.j) P.sign, abs_mul, abs_pow, hP.2.2.1, one_pow, one_mul]
  exact hg.slowDenominator_derivative_bound hP.1 hP.2.1 hP.2.2.2.1
    (by simpa only [abs_mul, hP.2.2.1, one_mul] using hx) hi
end RescaledPath
section
variable {ι : Type*} {l : Filter ι}
lemma power_times_parameter_tendsto (k : ι → ℝ) (hk : Tendsto k l atTop) (a C : ℝ)
    (ha : a + 1 < 0) :
    Tendsto (fun n => C * growthBase (k n) ^ a * (2 * Real.pi * k n)) l (nhds 0) := by
  have hM := tendsto_growthBase.comp hk
  have h₁ : Tendsto (fun n => growthBase (k n) ^ (a+1)) l (nhds 0) := by
    simpa only [neg_neg, Function.comp_def] using (tendsto_rpow_neg_atTop (neg_pos.mpr ha)).comp hM
  have h₂ : Tendsto (fun n => growthBase (k n) ^ a) l (nhds 0) := by
    have ha' : a < 0 := by linarith
    simpa only [neg_neg, Function.comp_def] using (tendsto_rpow_neg_atTop (neg_pos.mpr ha')).comp hM
  have ht := (h₁.sub (h₂.mul_const 4)).const_mul C
  simp only [zero_mul, sub_self, mul_zero] at ht
  apply ht.congr'
  filter_upwards [hk.eventually (eventually_ge_atTop (0 : ℝ))] with n hn
  have hm : 0 < growthBase (k n) := by linarith [growthBase_ge_four (k n) hn]
  rw [Real.rpow_add hm, Real.rpow_one]
  unfold growthBase
  ring

namespace RescaledPath
lemma parameter_inverse_tendsto (P : ι → RescaledPath) (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => 1 / (2 * Real.pi * (P n).k)) l (nhds 0) := by
  simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp (hk.const_mul_atTop (by positivity : 0 < 2 * Real.pi))
lemma curvature_bound_tendsto (P : ι → RescaledPath) (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => 512 * derivativeMajorant * growthBase (P n).k ^ (1 - 2 * goodExponent)) l (nhds 0) := by
  have hh := (tendsto_rpow_neg_atTop (show 0 < 2*goodExponent-1 by norm_num [goodExponent])).comp (tendsto_growthBase.comp hk)
  convert! hh.const_mul (512 * derivativeMajorant) using 1
  · ext n; dsimp only [Function.comp_def]; congr 1; ring_nf
  · simp only [mul_zero]
lemma quotient_bound_tendsto (P : ι → RescaledPath) (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => 640000 * growthBase (P n).k ^ (-goodExponent)) l (nhds 0) := by
  simpa only [mul_zero, Function.comp_def] using ((tendsto_rpow_neg_atTop goodExponent_pos).comp (tendsto_growthBase.comp hk)).const_mul 640000
lemma quotient_moving_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) (y : ι → ℝ) (hy : ∀ n, |y n| ≤ 1) :
    Tendsto (fun n => (P n).quotient (y n)) l (nhds 0) := by
  apply squeeze_zero_norm' _ (quotient_bound_tendsto P hk)
  exact Eventually.of_forall fun n => by
    simpa only [Real.norm_eq_abs, iteratedDeriv_zero, pow_zero, mul_one] using
      (hP n).quotient_derivative_bound (hy n) (i := 0) (by norm_num)
lemma phase_moving_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) (z b : ℝ)
    (hz : Tendsto (fun n => (P n).phase 0) l (nhds z))
    (hb : Tendsto (fun n => deriv (P n).phase 0) l (nhds b))
    (x : ℝ) (y : ι → ℝ) (hy : ∀ n, |y n| ≤ 1) (hyr : Tendsto y l (nhds x)) :
    Tendsto (fun n => (P n).phase (y n)) l (nhds (z+b*x)) ∧
    Tendsto (fun n => deriv (P n).phase (y n)) l (nhds b) := by
  apply phase_moving_limit (fun n => (P n).phase)
    (fun n => 512 * derivativeMajorant * growthBase (P n).k ^ (1 - 2 * goodExponent)) z b
    (Eventually.of_forall fun n => (P n).analytic_phase.mono (subset_univ _)) _
    (curvature_bound_tendsto P hk) hz hb x y hy hyr
  exact Eventually.of_forall fun n => ⟨by
    have := derivativeMajorant_pos
    have hm := growthBase_ge_four (P n).k (show 0 ≤ (P n).k by linarith [(hP n).1])
    positivity, fun x hx => (hP n).phase_derivative_bound_coarse (abs_le.mpr hx) (by norm_num) (by norm_num)⟩
lemma curvature_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => iteratedDeriv 2 (P n).phase 0) l (nhds 0) := by
  apply squeeze_zero_norm' _ (curvature_bound_tendsto P hk)
  exact Eventually.of_forall fun n => by
    convert! (hP n).phase_derivative_bound_coarse (x := 0) (by norm_num) (i := 2) (by norm_num) (by norm_num) using 1
lemma scaled_curvature_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => |deriv (deriv (P n).phase) 0| / (P n).ratio ^ 2) l (nhds 0) := by
  apply squeeze_zero' (Eventually.of_forall fun n => div_nonneg (abs_nonneg _) (sq_nonneg _)) _
    (curvature_bound_tendsto P hk)
  exact Eventually.of_forall fun n => by
    have hb := (hP n).phase_derivative_bound (x := 0) (by norm_num) (i := 2) (by norm_num) (by norm_num)
    rw [div_le_iff₀ (sq_pos_of_pos (hP n).ratio_bounds.1)]
    convert! hb using 1
    · rw [show 2 = 1+1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    · push_cast; ring
lemma scaled_quotient_derivative_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => |deriv (P n).quotient 0| / ((2 * Real.pi * (P n).k) * (P n).ratio)) l (nhds 0) := by
  have hlim := (quotient_bound_tendsto P hk).mul (parameter_inverse_tendsto P hk)
  rw [mul_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun n => by
    apply div_nonneg (abs_nonneg _)
    have hp := (hP n).ratio_bounds.1
    have hk := (hP n).1
    positivity) _ hlim
  exact Eventually.of_forall fun n => by
    have hkp : 0 < 2 * Real.pi * (P n).k := by have := (hP n).1; positivity
    have hr := (hP n).ratio_bounds.1
    rw [div_le_iff₀ (mul_pos hkp hr)]
    have hb := (hP n).quotient_derivative_bound (x := 0) (by norm_num) (i := 1) (by norm_num)
    simp only [iteratedDeriv_one, pow_one] at hb
    convert! hb using 1
    field_simp [ne_of_gt (show 0 < (P n).k by linarith [(hP n).1])]

lemma shifted_tendsto (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop) :
    Tendsto (fun n => (2 - (P n).quotient 0) / (2 * Real.pi * (P n).k)) l (nhds 0) := by
  have he := quotient_moving_tendsto P hP hk (fun _ => 0) (fun _ => by norm_num)
  have hh := ((tendsto_const_nhds (x := (2 : ℝ))).sub he).mul (parameter_inverse_tendsto P hk)
  convert! hh using 1
  · ext n; ring
  · simp only [mul_zero]
lemma denominator_nonzero_slope (P : ι → RescaledPath) (hP : ∀ n, (P n).Admissible)
    (hk : Tendsto (fun n => (P n).k) l atTop)
    (hW : Tendsto (fun n => (P n).denominator 0) l (nhds 0)) :
    Tendsto (fun n => |deriv (P n).denominator 0| / (P n).ratio) l (nhds (2*Real.pi)) := by
  convert tendsto_slow_nonzero_slope (fun n => (P n).phase) (fun n => (P n).quotient)
    (fun n => 2 * Real.pi * (P n).k) (fun n => (P n).ratio)
    (fun n => by have := (hP n).1; positivity) (fun n => (hP n).ratio_bounds.1)
    (fun n => ((P n).analytic_phase 0 (mem_univ _)).differentiableAt)
    (fun n => ((P n).analytic_phase.deriv 0 (mem_univ _)).differentiableAt)
    (fun n => ((hP n).analytic_quotient 0 (by norm_num)).differentiableAt)
    (fun n => (hP n).abs_phase_deriv_zero) _ (scaled_curvature_tendsto P hP hk)
    (scaled_quotient_derivative_tendsto P hP hk) (shifted_tendsto P hP hk) using 1
  · funext n; rw [(hP n).denominator_model]
  · simpa only [← (hP _).denominator_model] using hW
end RescaledPath
end
namespace RescaledPath
lemma Admissible.reciprocal_denominator {P : RescaledPath} (hP : P.Admissible) (x : ℝ) :
    phaseReciprocal P.phase P.quotient (1 / (2 * Real.pi * P.k)) x =
      1 / (P.ratio ^ 2 * P.denominator x) := by
  rw [hP.denominator_model]
  unfold phaseReciprocal slowDenominatorModel
  congr 1
  have hr := hP.ratio_bounds.1.ne'
  field_simp [hr]

lemma Admissible.reciprocal_eq {P : RescaledPath} (hP : P.Admissible) (x : ℝ) :
    phaseReciprocal P.phase P.quotient (1 / (2 * Real.pi * P.k)) x =
      localReciprocalTerm P.k P.q₀ P.θ P.L (P.sign * x) P.j := by
  have hs : P.sign ^ 2 = 1 := by nlinarith [sq_abs P.sign, hP.2.2.1]
  have hd : deriv P.phase x = P.sign * rescaledD₁ P.k P.q₀ P.θ P.L (P.sign*x) P.j := by
    rw [← iteratedDeriv_one, phase_iteratedDeriv _ (by norm_num)]
    rw [iteratedDeriv_one, pow_one, (hasDerivAt_rescaledOrbit _ _ _ _ _ _).deriv]
  unfold phaseReciprocal localReciprocalTerm
  rw [hd, mul_pow, hs, one_mul]
  simp only [phase, centerPhase_cos, rescaledOrbit, quotient]
  congr 1
  ring
end RescaledPath

lemma fine_cubic_error_tendsto {ι : Type*} {l : Filter ι} (k r : ι → ℝ)
    (hk : Tendsto k l atTop) {a : ℝ} (ha : a ≠ 0) (hr : Tendsto r l (nhds a)) :
    Tendsto (fun n => cubicFineError (k n) (r n) / (1 / (2 * Real.pi * k n))) l (nhds 0) := by
  have ht := power_times_parameter_tendsto k hk (1-3*goodExponent) 1 (by norm_num [goodExponent])
  simp only [one_mul] at ht
  have hs := power_times_parameter_tendsto k hk (-(9/5))
    (inverseFourthMajorant (52 * derivativeMajorant) / 12) (by norm_num)
  have hcoeff := (tendsto_const_nhds (x := (16 : ℝ))).div (hr.pow 2) (pow_ne_zero _ ha)
  convert! hs.add (hcoeff.mul ht) using 1
  · ext n
    simp only [cubicFineError, one_div, div_inv_eq_mul, Pi.div_apply]
    ring
  · simp only [mul_zero, add_zero]

lemma paired_paths_scarcity {ι : Type*} (U : Ultrafilter ι)
    (P₁ P₂ : ι → RescaledPath) (h₁ : ∀ n, (P₁ n).Admissible) (h₂ : ∀ n, (P₂ n).Admissible)
    (hK : ∀ n, (P₂ n).k = (P₁ n).k) (hfast : ∀ n, (P₁ n).ratio = 1)
    (hk : Tendsto (fun n => (P₁ n).k) U atTop)
    (A : ι → Set ℝ) (F : Set ℝ) (hF : IsCompact F) (hA : ∀ n, A n ⊆ Icc (-1 : ℝ) 1)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ A n) ∧ Tendsto y U (nhds x))
    (p₀ p₁ : ι → Polynomial ℝ) (hp₀ : ∀ n, (p₀ n).natDegree ≤ 3) (hp₁ : ∀ n, (p₁ n).natDegree ≤ 3)
    (hval₀ : ∀ᶠ n in (U : Filter ι), ∀ x ∈ A n,
      |(p₀ n).eval x - (phaseReciprocal (P₁ n).phase (P₁ n).quotient (1/(2*Real.pi*(P₁ n).k)) x +
      phaseReciprocal (P₂ n).phase (P₂ n).quotient (1/(2*Real.pi*(P₁ n).k)) x)| ≤ cubicError (P₁ n).k)
    (hval₁ : ∀ᶠ n in (U : Filter ι), ∀ x ∈ A n,
      |(p₁ n).eval x - (phaseReciprocal (P₁ n).phase (P₁ n).quotient (1/(2*Real.pi*(P₁ n).k)) x +
      phaseReciprocal (P₂ n).phase (P₂ n).quotient (1/(2*Real.pi*(P₁ n).k)) x)| ≤ cubicFineError (P₁ n).k (P₂ n).ratio) :
    volume F = 0 := by
  have hk₂ : Tendsto (fun n => (P₂ n).k) U atTop := hk.congr (fun n => (hK n).symm)
  obtain ⟨z₁,_,hz₁⟩ := ultrafilter_bounded_limit U (fun n => (P₁ n).phase 0)
    (Eventually.of_forall fun n => (P₁ n).phase_zero_bounds)
  obtain ⟨z₂,_,hz₂⟩ := ultrafilter_bounded_limit U (fun n => (P₂ n).phase 0)
    (Eventually.of_forall fun n => (P₂ n).phase_zero_bounds)
  obtain ⟨b₁,hb₁,hdb₁⟩ := ultrafilter_bounded_limit U (fun n => deriv (P₁ n).phase 0)
    (Eventually.of_forall fun n => abs_le.mp ((h₁ n).abs_phase_deriv_zero.le.trans (h₁ n).ratio_bounds.2))
  obtain ⟨b₂,hb₂,hdb₂⟩ := ultrafilter_bounded_limit U (fun n => deriv (P₂ n).phase 0)
    (Eventually.of_forall fun n => abs_le.mp ((h₂ n).abs_phase_deriv_zero.le.trans (h₂ n).ratio_bounds.2))
  have hbabs : |b₁| = 1 := by
    apply tendsto_nhds_unique hdb₁.abs
    convert tendsto_const_nhds (x := (1:ℝ)) using 1
    ext n
    exact (h₁ n).abs_phase_deriv_zero.trans (hfast n)
  have hbne : b₁ ≠ 0 := by intro hz; simp [hz] at hbabs
  have hr₂ : Tendsto (fun n => (P₂ n).ratio) U (nhds |b₂|) := by
    convert hdb₂.abs using 1
    ext n
    exact (h₂ n).abs_phase_deriv_zero.symm
  have hphase₁ := RescaledPath.phase_moving_tendsto P₁ h₁ hk z₁ b₁ hz₁ hdb₁
  have hphase₂ := RescaledPath.phase_moving_tendsto P₂ h₂ hk₂ z₂ b₂ hz₂ hdb₂
  by_cases hbz : b₂ = 0
  · have hrs : Tendsto (fun n => (P₂ n).ratio) U (nhds 0) := by simpa only [hbz, abs_zero] using hr₂
    apply vanishing_slope_scarcity U A F hF p₀ hp₀
      (fun n => phaseReciprocal (P₁ n).phase (P₁ n).quotient (1/(2*Real.pi*(P₁ n).k)))
      (fun n => (P₂ n).denominator) (fun n => (P₂ n).ratio) (fun n => cubicError (P₁ n).k)
      z₁ b₁ (1024 * (640002 + 104 * derivativeMajorant)) hbne (by
        have := derivativeMajorant_pos; positivity) hA happrox
      (tendsto_cubic_relation_error.comp hk) _ _
      (Eventually.of_forall fun n => (h₂ n).ratio_bounds.1) hrs
      (Eventually.of_forall fun n => (h₂ n).analytic_denominator) _
      (RescaledPath.denominator_nonzero_slope P₂ h₂ hk₂)
    · filter_upwards [hval₀] with n hn x hx
      simpa only [← (h₂ n).reciprocal_denominator x, hK n] using hn x hx
    · intro x hx hc y hy hyr
      have hyy : ∀ n, |y n| ≤ 1 := fun n => abs_le.mpr (hA n (hy n))
      obtain ⟨hq,hd⟩ := hphase₁ x y hyy hyr
      have hh := phaseReciprocal_tendsto (fun n => (P₁ n).phase) (fun n => (P₁ n).quotient)
        (fun n => 1/(2*Real.pi*(P₁ n).k)) y (z₁+b₁*x) b₁ hbne hc hq hd
        (RescaledPath.quotient_moving_tendsto P₁ h₁ hk y hyy) (RescaledPath.parameter_inverse_tendsto P₁ hk)
      simpa only [show b₁ ^ 2 = 1 by nlinarith [sq_abs b₁], one_mul] using hh
    · exact Eventually.of_forall fun n i hi x hx => (h₂ n).denominator_derivative_bound (abs_le.mpr hx) hi.2
  · apply positive_slope_scarcity U A F hF p₁ hp₁
      (fun n => (P₁ n).phase) (fun n => (P₂ n).phase)
      (fun n => (P₁ n).quotient) (fun n => (P₂ n).quotient)
      (fun n => 1/(2*Real.pi*(P₁ n).k)) (fun n => cubicFineError (P₁ n).k (P₂ n).ratio)
      (fun n => 512 * derivativeMajorant * growthBase (P₁ n).k ^ (1-3*goodExponent))
      z₁ z₂ b₁ b₂ hbne hbz (by rw [hbabs]; exact abs_le.mpr hb₂) hA
      (Eventually.of_forall fun n => by have := (h₁ n).1; positivity)
      (RescaledPath.parameter_inverse_tendsto P₁ hk)
      (fine_cubic_error_tendsto _ _ hk (abs_ne_zero.mpr hbz) hr₂) _
      (Eventually.of_forall fun n => ⟨(P₁ n).analytic_phase.mono (subset_univ _), (P₂ n).analytic_phase.mono (subset_univ _)⟩)
      (RescaledPath.curvature_tendsto P₁ h₁ hk) (RescaledPath.curvature_tendsto P₂ h₂ hk₂) _ _ _ hval₁ happrox
    · simpa only [one_div, div_inv_eq_mul] using power_times_parameter_tendsto (fun n => (P₁ n).k) hk
        (1-3*goodExponent) (512*derivativeMajorant) (by norm_num [goodExponent])
    · exact Eventually.of_forall fun n => ⟨by
        have := derivativeMajorant_pos
        have := growthBase_ge_four (P₁ n).k (by linarith [(h₁ n).1]); positivity,
        fun x hx => ⟨by convert! (h₁ n).phase_derivative_bound_coarse (abs_le.mpr hx) (i:=3) (by norm_num) (by norm_num) using 1,
        by convert! (h₂ n).phase_derivative_bound_coarse (abs_le.mpr hx) (i:=3) (by norm_num) (by norm_num) using 1 ; rw [hK n] ; norm_num only [Nat.cast_ofNat]⟩⟩
    · intro x y hy hyr
      exact ⟨(hphase₁ x y hy hyr).1, (hphase₂ x y hy hyr).1, (hphase₁ x y hy hyr).2, (hphase₂ x y hy hyr).2⟩
    · intro y hy
      exact ⟨RescaledPath.quotient_moving_tendsto P₁ h₁ hk y hy, RescaledPath.quotient_moving_tendsto P₂ h₂ hk₂ y hy⟩
namespace LocalConfiguration
lemma Valid.left_admissible {C : LocalConfiguration} (h : C.Valid) : C.left.Admissible := by
  refine ⟨h.1, h.2.1, by norm_num [left], ?_, ?_⟩
  · exact le_max_left _ _
  · obtain ⟨b, hm, hp⟩ := h.2.2.2.1
    exact ⟨b,hm⟩
lemma Valid.right_admissible {C : LocalConfiguration} (h : C.Valid) : C.right.Admissible := by
  refine ⟨h.1, h.2.1, by norm_num [right], ?_, ?_⟩
  · exact le_max_right _ _
  · obtain ⟨b, hm, hp⟩ := h.2.2.2.1
    exact ⟨potential C.k C.q₀ - b,hp⟩
lemma Valid.fast_admissible {C : LocalConfiguration} (h : C.Valid) : C.fast.Admissible := by
  unfold fast; split <;> first | exact h.left_admissible | exact h.right_admissible
lemma Valid.slow_admissible {C : LocalConfiguration} (h : C.Valid) : C.slow.Admissible := by
  unfold slow; split <;> first | exact h.left_admissible | exact h.right_admissible
lemma fast_parameter (C : LocalConfiguration) : C.fast.k = C.k := by unfold fast; split <;> rfl
lemma slow_parameter (C : LocalConfiguration) : C.slow.k = C.k := by unfold slow; split <;> rfl
lemma Valid.scale_pos {C : LocalConfiguration} (h : C.Valid) : 0 < C.scale := h.2.2.2.1.scale_pos (by linarith [h.1])
lemma Valid.fast_ratio {C : LocalConfiguration} (h : C.Valid) : C.fast.ratio = 1 := by
  have hm : C.scale = max C.left.size C.right.size := rfl
  unfold fast
  split
  · rename_i hc
    change C.left.size / C.scale = 1
    rw [hm, max_eq_left hc, div_self h.left_admissible.size_pos.ne']
  · rename_i hc
    change C.right.size / C.scale = 1
    rw [hm, max_eq_right (le_of_not_ge hc), div_self h.right_admissible.size_pos.ne']
lemma Valid.slow_min {C : LocalConfiguration} (h : C.Valid) :
    C.slow.ratio * C.scale = min C.left.size C.right.size := by
  unfold slow
  split
  · rename_i hc
    change C.right.size / C.scale * C.scale = _
    rw [div_mul_cancel₀ _ h.scale_pos.ne', min_eq_right hc]
  · rename_i hc
    change C.left.size / C.scale * C.scale = _
    rw [div_mul_cancel₀ _ h.scale_pos.ne', min_eq_left (le_of_not_ge hc)]
lemma Valid.reciprocalSum {C : LocalConfiguration} (h : C.Valid) (x : ℝ) :
    C.reciprocalSum x = phaseReciprocal C.fast.phase C.fast.quotient (1/(2*Real.pi*C.k)) x +
      phaseReciprocal C.slow.phase C.slow.quotient (1/(2*Real.pi*C.k)) x := by
  have hl := h.left_admissible.reciprocal_eq x
  have hr := h.right_admissible.reciprocal_eq x
  simp only [left, right, one_mul, neg_one_mul] at hl hr
  unfold fast slow
  split <;> dsimp only [left, right] <;> rw [hl, hr]
  · rfl
  · exact add_comm _ _
lemma Valid.cubic_relation {C : LocalConfiguration} (h : C.Valid) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ 3 ∧ ∀ x ∈ C.successful,
      |p.eval x - C.reciprocalSum x| ≤ cubicError C.k :=
  h.2.2.2.1.cubic_reciprocal_relation (by linarith [h.1]) h.2.1 h.2.2.1 h.2.2.2.2
lemma Valid.fine_cubic_relation {C : LocalConfiguration} (h : C.Valid) :
    ∃ p : Polynomial ℝ, p.natDegree ≤ 3 ∧ ∀ x ∈ C.successful,
      |p.eval x - C.reciprocalSum x| ≤ cubicFineError C.k C.slow.ratio := by
  apply h.2.2.2.1.cubic_reciprocal_relation_ratio (by linarith [h.1]) h.2.1 h.2.2.1 h.slow_admissible.ratio_bounds.1
  exact h.slow_min.le
lemma successful_subset (C : LocalConfiguration) : C.successful ⊆ Icc (-1 : ℝ) 1 := fun _ hx => hx.1
lemma successful_nonempty {C : LocalConfiguration} (h : C.Valid) : C.successful.Nonempty := by
  refine ⟨0, by norm_num, ?_⟩
  simpa only [zero_div, add_zero] using h.2.2.2.1
lemma limit_null {ι : Type*} (U : Ultrafilter ι)
    (C : ι → LocalConfiguration) (hC : ∀ n, (C n).Valid)
    (hk : Tendsto (fun n => (C n).k) U atTop)
    (F : Set ℝ) (hF : IsCompact F)
    (happrox : ∀ x ∈ F, ∃ y : ι → ℝ, (∀ n, y n ∈ (C n).successful) ∧ Tendsto y U (nhds x)) :
    volume F = 0 := by
  choose p₀ hp₀ hval₀ using fun n => (hC n).cubic_relation
  choose p₁ hp₁ hval₁ using fun n => (hC n).fine_cubic_relation
  apply paired_paths_scarcity U (fun n => (C n).fast) (fun n => (C n).slow)
    (fun n => (hC n).fast_admissible) (fun n => (hC n).slow_admissible)
    (fun n => by rw [slow_parameter, fast_parameter]) (fun n => (hC n).fast_ratio)
    (by simpa only [fast_parameter] using hk)
    (fun n => (C n).successful) F hF (fun n => (C n).successful_subset) happrox p₀ p₁ hp₀ hp₁
  · exact Eventually.of_forall fun n x hx => by
      simpa only [fast_parameter, ← (hC n).reciprocalSum x] using hval₀ n x hx
  · exact Eventually.of_forall fun n x hx => by
      simpa only [fast_parameter, ← (hC n).reciprocalSum x] using hval₁ n x hx
end LocalConfiguration
end StandardMapEntropy
open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
namespace LocalConfiguration
lemma uniform_thick_scarcity (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ k₀ : ℝ, ∀ C : LocalConfiguration, C.Valid → k₀ ≤ C.k →
      volume {x : ℝ | ∃ y ∈ C.successful, dist x y < δ} ≤ ENNReal.ofReal η := by
  classical
  by_contra hf
  push Not at hf
  have hex (n : ℕ) := hf (1 / ((n : ℝ)+1)) (by positivity) (n : ℝ)
  choose C hC hk hbad using hex
  let K : ℕ → TopologicalSpace.NonemptyCompacts ℝ := fun n =>
    ⟨⟨closure (C n).successful,
      isCompact_Icc.of_isClosed_subset isClosed_closure
        (closure_minimal (C n).successful_subset isClosed_Icc)⟩,
      (successful_nonempty (hC n)).closure⟩
  have hKbound : ∀ n, (K n : Set ℝ) ⊆ Icc (-1 : ℝ) 1 := fun n =>
    closure_minimal (C n).successful_subset isClosed_Icc
  obtain ⟨F,hF,φ,hφ,hconv⟩ := compact_sets_subsequence K hKbound
  have hparam : Tendsto (fun n => (C n).k) atTop atTop :=
    tendsto_atTop_mono hk tendsto_natCast_atTop_atTop
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  have hnull : volume (F : Set ℝ) = 0 := by
    apply limit_null U (C ∘ φ) (fun n => hC (φ n)) ((hparam.comp hφ.tendsto_atTop).mono_left hU)
      (F : Set ℝ) F.isCompact
    intro x hx
    obtain ⟨y, hy, hylim⟩ := successful_points_approximation (fun n => (C (φ n)).successful)
      (K ∘ φ) F (fun _ => rfl) hconv hx
    exact ⟨y,hy,hylim.mono_left hU⟩
  have hlim := neighborhoods_null_limit (K ∘ φ) F hconv hnull (fun n => 1/((φ n : ℝ)+1))
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
  have hle : ENNReal.ofReal η ≤ 0 := ge_of_tendsto hlim (Eventually.of_forall fun n => by
    apply (hbad (φ n)).le.trans
    apply measure_mono
    rintro x ⟨y,hy,hxy⟩
    exact ⟨y,subset_closure hy,hxy⟩)
  exact (ENNReal.ofReal_pos.mpr hη).not_ge hle
end LocalConfiguration

theorem local_scarcity : LocalScarcityObligation := by
  intro η hη
  obtain ⟨δ,hδ,k₀,hscarce⟩ := LocalConfiguration.uniform_thick_scarcity η hη
  obtain ⟨B,hB⟩ := (eventually_HigherControl.and eventually_chain_ratio_small).exists_forall_of_atTop
  let K₀ := max 1 (max k₀ B)
  refine ⟨δ,hδ,growthBase K₀,?_⟩
  intro k hk hM q₀ θ jm jp hg hl
  have hk₀ : K₀ ≤ k := by
    unfold growthBase at hM
    nlinarith [Real.pi_pos]
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk₀
  have hkk : k₀ ≤ k := (le_max_left _ _).trans ((le_max_right _ _).trans hk₀)
  have hkB : B ≤ k := (le_max_right _ _).trans ((le_max_right _ _).trans hk₀)
  let C : LocalConfiguration := ⟨k,q₀,θ,jm,jp⟩
  exact hscarce C ⟨hk1,(hB k hkB).1,(hB k hkB).2,hg,hl⟩ hkk
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PlaneGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma abs_dot_le_norm_mul (z w : ℂ) : |dot z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have h0 := sq_nonneg (wedge z w)
  have hs : (dot z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma abs_wedge_le_norm_mul (z w : ℂ) : |wedge z w| ≤ ‖z‖*‖w‖ := by
  have h := dot_wedge_sq z w
  have hs : (wedge z w)^2 ≤ (‖z‖*‖w‖)^2 := by nlinarith [sq_nonneg (dot z w)]
  exact (abs_le_of_sq_le_sq hs (mul_nonneg (norm_nonneg z) (norm_nonneg w)))
lemma wedge_add_left (z w a : ℂ) : wedge (z+w) a = wedge z a + wedge w a := by
  simp [wedge]; ring
lemma wedge_smul_left (t : ℝ) (z w : ℂ) : wedge (t • z) w = t*wedge z w := by
  simp [wedge]; ring
lemma wedge_swap (z w : ℂ) : wedge z w = -wedge w z := by dsimp [wedge]; ring
lemma wedge_sine_triangle (a b c : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hc : ‖c‖=1) :
    |wedge a c| ≤ |wedge a b|+|wedge b c| := by
  have he : wedge a c = dot b a * wedge b c + wedge b a * wedge (quarterTurn b) c := by
    conv_lhs => rw [unit_expansion b a hb]
    rw [wedge_add_left, wedge_smul_left, wedge_smul_left]
  rw [he]
  calc
    _ ≤ |dot b a| * |wedge b c|+|wedge b a| * |wedge (quarterTurn b) c| := by
      simpa only [abs_mul] using abs_add_le (dot b a * wedge b c) (wedge b a * wedge (quarterTurn b) c)
    _ ≤ |wedge b c|+|wedge b a| := by
      have h1 : |dot b a|≤1 := by simpa [ha,hb] using abs_dot_le_norm_mul b a
      have h2 : |wedge (quarterTurn b) c|≤1 := by simpa [norm_quarterTurn,hb,hc] using abs_wedge_le_norm_mul (quarterTurn b) c
      nlinarith [abs_nonneg (wedge b c), abs_nonneg (wedge b a)]
    _ = _ := by rw [wedge_swap b a, abs_neg]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PlaneTransfer
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma dot_quarterTurn_right (a z : ℂ) : dot a (quarterTurn z) = -wedge a z := by
  simp [dot,wedge,quarterTurn]; ring
lemma PlaneAreaPreserving.norm_le_product {A B C : ℂ →L[ℝ] ℂ}
    (_hB : PlaneAreaPreserving B) (hBC : ∀ z, C (B z)=A z) : ‖A‖≤‖C‖*‖B‖ := by
  have he : A=C.comp B := by ext z; exact (hBC z).symm
  rw [he]
  exact C.opNorm_comp_le B
lemma expanded_projection_bound {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A‖*|dot a z| ≤ ‖A z‖ := by
  have hs := h.norm_map_sq a ha hA z
  have hnon := mul_nonneg (sq_nonneg (wedge a z)) (sq_nonneg (‖A‖⁻¹))
  have hsq : (‖A‖*|dot a z|)^2≤‖A z‖^2 := by nlinarith [sq_abs (dot a z)]
  exact (sq_le_sq₀ (mul_nonneg (norm_nonneg A) (abs_nonneg _)) (norm_nonneg _)).mp hsq
lemma two_singular_upper {A : ℂ →L[ℝ] ℂ} (h : PlaneAreaPreserving A)
    (a : ℂ) (ha : ‖a‖=1) (hA : ‖A a‖=‖A‖) (z : ℂ) :
    ‖A z‖ ≤ ‖A‖*|dot a z| + ‖A‖⁻¹*|wedge a z| := by
  have hd := orthogonal_image_of_max A a ha hA
  have hs := h.norm_map_sq a ha hA (quarterTurn a)
  rw [dot_quarterTurn,wedge_quarterTurn,ha] at hs
  have hb : ‖A (quarterTurn a)‖=‖A‖⁻¹ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  conv_lhs => rw [unit_expansion a z ha]
  rw [map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(dot a z : ℝ) • A a‖+‖(wedge a z : ℝ) • A (quarterTurn a)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hA,hb]; ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TransferCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma transferStepInv_area (v : ℝ) : PlaneAreaPreserving (transferStepInv v) := by
  intro z w; simp [wedge]; ring
lemma transferProduct_pair (v : ℕ → ℝ) (a b : ℝ) (n : ℕ) :
    transferProduct v n ⟨b,a⟩ = ⟨linearSolution v a b (n+1),linearSolution v a b n⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ContinuousLinearMap.comp_apply,ih]
    apply Complex.ext <;> simp only [transferStep_re,transferStep_im,linearSolution_step]
lemma transferProductInv_area (v : ℕ → ℝ) (n : ℕ) : PlaneAreaPreserving (transferProductInv v n) := by
  induction n with
  | zero => intro z w; rfl
  | succ n ih => exact ih.comp (transferStepInv_area _)
lemma transferProduct_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProduct v n (transferProductInv v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,ih,transferStep_inv]
lemma transferProductInv_inverse (v : ℕ → ℝ) (n : ℕ) (z : ℂ) :
    transferProductInv v n (transferProduct v n z)=z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [transferProduct, transferProductInv,ContinuousLinearMap.comp_apply,transferStepInv_inv,ih]
lemma transferProduct_norm_inverse (v : ℕ → ℝ) (n : ℕ) :
    ‖transferProduct v n‖=‖transferProductInv v n‖ :=
  (transferProduct_area v n).norm_inverse (transferProductInv_area v n)
    (transferProduct_inverse v n) (transferProductInv_inverse v n)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_LiftDynamics
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftIter_add (k : ℝ) (i j : ℤ) (z : ℝ × ℝ) :
    liftIter k (i+j) z=liftIter k i (liftIter k j z) := by
  simp only [liftIter,zpow_add,Equiv.Perm.coe_mul,Function.comp_apply]
lemma liftIter_nat (k : ℝ) (n : ℕ) (z : ℝ × ℝ) :
    liftIter k n z=(liftedOrbit k z.2 z.1 (n+1),liftedOrbit k z.2 z.1 n) := by
  induction n with
  | zero => simp [liftIter,liftedOrbit]
  | succ n ih =>
    rw [Nat.cast_add,Nat.cast_one,add_comm,liftIter_add,ih]
    simp only [liftIter,zpow_one]
    change (phi k (liftedOrbit k z.2 z.1 (n+1))-liftedOrbit k z.2 z.1 n,
      liftedOrbit k z.2 z.1 (n+1))=_
    rfl
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SegmentObservations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter Metric
open scoped Topology
namespace StandardMapEntropy
lemma liftSegmentTransfer_eq (k : ℝ) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) :
    liftSegmentTransfer k z a n=transferProduct
      (orbitCoefficient k (liftIter k a z).2 (liftIter k a z).1) n := by
  unfold liftSegmentTransfer
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [transferProduct,ih]
    congr 2
    unfold liftSegmentCoefficient orbitCoefficient
    rw [show a+((n+1:ℕ):ℤ)-1=(n:ℤ)+a by push_cast; ring,liftIter_add,liftIter_nat]
lemma liftShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : ℝ × ℝ) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    liftShortfall k z a n ∈ Icc 0 1 := by
  have hM : 1 < growthBase k := by have := growthBase_ge_four k hk; linarith
  have hp : 0 < Real.log (growthBase k) := Real.log_pos hM
  have hnp : (0:ℝ) < n := Nat.cast_pos.mpr hn
  obtain ⟨hlo,hhi⟩ := liftSegmentTransfer_norm_bounds k hk z a n
  have hlog0 : 0 ≤ Real.log ‖liftSegmentTransfer k z a n‖ := Real.log_nonneg hlo
  have hlog1 : Real.log ‖liftSegmentTransfer k z a n‖ ≤ (n:ℝ)*Real.log (growthBase k) := by
    rw [← Real.log_pow]
    exact Real.log_le_log (by linarith) hhi
  unfold liftShortfall
  constructor
  · have := (div_le_one (mul_pos hnp hp)).mpr hlog1; linarith
  · have := div_nonneg hlog0 (mul_pos hnp hp).le; linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusDynamics
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma measurePreserving_torusStep (k : ℝ) : MeasurePreserving (torusStep k) area area := by
  have hh := measurePreserving_recurrenceCoordinates.comp
    ((measurePreserving_standardMap k).comp measurePreserving_recurrenceCoordinates)
  convert hh using 1
  funext z
  simp only [Function.comp_apply,standardMap_conjugacy,torusStep_apply]
  rw [recurrenceCoordinates_involutive z]
lemma measurePreserving_torusStep_symm (k : ℝ) : MeasurePreserving (torusStep k).symm area area :=
  (measurePreserving_torusStep k).symm (torusStep_measurableEquiv k)
lemma measurePreserving_torusIter (k : ℝ) (i : ℤ) : MeasurePreserving (torusIter k i) area area := by
  cases i with
  | ofNat n =>
      change MeasurePreserving (torusIter k (n : ℤ)) area area
      simpa only [torusIter,zpow_natCast,Equiv.Perm.coe_pow] using (measurePreserving_torusStep k).iterate n
  | negSucc n => simpa only [torusIter,zpow_negSucc,← inv_pow,Equiv.Perm.inv_def,Equiv.Perm.coe_pow] using
      (measurePreserving_torusStep_symm k).iterate (n+1)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_TorusObservations
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_torusShortfall (k : ℝ) (hk : 0 ≤ k) (a : ℤ) (n : ℕ) :
    Continuous (fun z => torusShortfall k z a n) := by
  apply continuous_const.sub
  apply Continuous.div_const
  exact (continuous_torusSegmentTransfer k a n).norm.log
    (fun z => by have := (torusSegmentTransfer_norm_bounds k hk z a n).1; linarith)
lemma torusShortfall_mem (k : ℝ) (hk : 0 ≤ k) (z : Torus) (a : ℤ) (n : ℕ) (hn : 0 < n) :
    torusShortfall k z a n ∈ Icc 0 1 := by
  obtain ⟨w,rfl⟩ := liftProjection_surjective z
  rw [torusShortfall_lift]
  exact liftShortfall_mem k hk w a n hn
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CocycleAlgebra
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transferProduct_concat (v : ℕ → ℝ) (m n : ℕ) :
    transferProduct v (m+n)=(transferProduct (fun i => v (m+i)) n).comp (transferProduct v m) := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
    rw [show m+(n+1)=(m+n)+1 by omega,transferProduct,ih,transferProduct]
    simp only [ContinuousLinearMap.comp_assoc,Nat.add_assoc]
lemma torusSegmentCoefficient_shift (k : ℝ) (z : Torus) (a : ℤ) (m : ℕ) :
    (fun i => torusSegmentCoefficient k z a (m+i))=torusSegmentCoefficient k z (a+(m:ℤ)) := by
  funext i
  unfold torusSegmentCoefficient
  congr 3
  push_cast
  ring
lemma torusSegmentTransfer_concat (k : ℝ) (z : Torus) (a : ℤ) (m n : ℕ) :
    torusSegmentTransfer k z a (m+n)=
      (torusSegmentTransfer k z (a+(m:ℤ)) n).comp (torusSegmentTransfer k z a m) := by
  unfold torusSegmentTransfer
  rw [transferProduct_concat,torusSegmentCoefficient_shift]
lemma torusIter_neg_swap (k : ℝ) (n : ℕ) (z : Torus) :
    torusIter k (-(n:ℤ)) z=(torusIter k (n:ℤ) z.swap).swap := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show ((n+1:ℕ):ℤ)=1+(n:ℤ) by omega,show -(1+(n:ℤ))=(-1)+(-(n:ℤ)) by ring,
      torusIter_add,torusIter_add,ih]
    simp only [torusIter,zpow_neg_one,zpow_one,Equiv.Perm.inv_def,torusStep_symm_apply,torusStep_apply,
      recurrenceMap,Prod.fst_swap,Prod.snd_swap,Prod.swap_prod_mk]
lemma torus_backward_pair_coordinate (k : ℝ) (z : Torus) (n : ℕ) :
    (torusIter k (-(n:ℤ)-1) z).1=(torusIter k (n:ℤ) z.swap).1 := by
  rw [show -(n:ℤ)-1=(-1)+(-(n:ℤ)) by ring,torusIter_add,torusIter_neg_swap]
  rfl
lemma torusSegmentTransfer_reverse_identity (k : ℝ) (z : Torus) (n : ℕ) (u : ℂ) :
    torusSegmentTransfer k z (-(n:ℤ)) n
      (planeSwap (torusSegmentTransfer k z.swap 0 n (planeSwap u)))=u := by
  induction n generalizing u with
  | zero => simp [torusSegmentTransfer,transferProduct]
  | succ n ih =>
    have hc : torusSegmentTransfer k z (-((n+1:ℕ):ℤ)) (n+1)=
        (torusSegmentTransfer k z (-(n:ℤ)) n).comp
          (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)) := by
      rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
      congr 1
      · congr 1; push_cast; ring
      · simp only [torusSegmentTransfer,transferProduct,ContinuousLinearMap.comp_id,
          torusSegmentCoefficient]
        exact congrArg (fun t : ℤ => transferStep (torusPotential k (torusIter k t z).1)) (by omega)
    rw [hc]
    change torusSegmentTransfer k z (-(n:ℤ)) n
      (transferStep (torusPotential k (torusIter k (-(n:ℤ)-1) z).1)
        (planeSwap (transferStep (torusSegmentCoefficient k z.swap 0 (n+1))
          (torusSegmentTransfer k z.swap 0 n (planeSwap u)))))=u
    have hcoef : torusSegmentCoefficient k z.swap 0 (n+1)=
        torusPotential k (torusIter k (-(n:ℤ)-1) z).1 := by
      unfold torusSegmentCoefficient
      rw [show (0:ℤ)+((n+1:ℕ):ℤ)-1=(n:ℤ) by omega,torus_backward_pair_coordinate]
    rw [hcoef]
    have he (v : ℝ) (w : ℂ) : transferStep v (planeSwap (transferStep v w))=planeSwap w := by
      apply Complex.ext <;> simp
    rw [he]
    exact ih u
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FourPoint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma PlaneAreaPreserving.injective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Injective A := by
  intro x y hxy
  have hh:=hA.norm_lower (x-y)
  rw [map_sub,hxy,sub_self,norm_zero,mul_zero] at hh
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hh (norm_nonneg _)))
lemma PlaneAreaPreserving.surjective {A : ℂ →L[ℝ] ℂ} (hA : PlaneAreaPreserving A) :
    Function.Surjective A := LinearMap.surjective_of_injective (f := A.toLinearMap) hA.injective

lemma transfer_angle_bounds {A B C : ℂ →L[ℝ] ℂ}
    (hA : PlaneAreaPreserving A) (hB : PlaneAreaPreserving B) (hC : PlaneAreaPreserving C)
    (he : ∀ z, C (B z)=A z)
    (a b : ℂ) (ha : ‖a‖=1) (hb : ‖b‖=1) (hAa : ‖A a‖=‖A‖) (hBb : ‖B b‖=‖B‖) :
    max |wedge a b| (max (‖A‖⁻¹^2) (‖B‖⁻¹^2)) ≤ ‖C‖/(‖A‖*‖B‖) ∧
    ‖C‖/(‖A‖*‖B‖) ≤ |wedge a b|+‖A‖⁻¹^2+‖B‖⁻¹^2 := by
  have hDA : 1 ≤ ‖A‖ := hA.singular_pair.choose_spec.2.2.2.2
  have hDB : 1 ≤ ‖B‖ := hB.singular_pair.choose_spec.2.2.2.2
  have hAp : 0 < ‖A‖ := by linarith
  have hBp : 0 < ‖B‖ := by linarith
  have hbperp : ‖B (quarterTurn b)‖=‖B‖⁻¹ := by
    have hs:=hB.norm_map_sq b hb hBb (quarterTurn b)
    rw [dot_quarterTurn,wedge_quarterTurn,hb] at hs
    apply (sq_eq_sq₀ (norm_nonneg _) (inv_nonneg.mpr (norm_nonneg _))).mp
    simpa using hs
  have angle : ‖A‖*|wedge a b| ≤ ‖C‖*‖B‖⁻¹ := by
    have hh:=expanded_projection_bound hA a ha hAa (quarterTurn b)
    rw [dot_quarterTurn_right,abs_neg,← he] at hh
    exact hh.trans (by simpa [hbperp] using C.le_opNorm (B (quarterTurn b)))
  have normAB : ‖A‖ ≤ ‖C‖*‖B‖ := hB.norm_le_product he
  have normBA : ‖B‖ ≤ ‖C‖*‖A‖ := by
    apply B.opNorm_le_bound (by positivity)
    intro z
    have hh:=hC.norm_lower (B z)
    rw [he] at hh
    calc
      _ ≤ ‖C‖*‖A z‖ := hh
      _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (A.le_opNorm z) (norm_nonneg C)
  have upper : ‖C‖ ≤ ‖A‖/‖B‖+‖A‖*‖B‖*|wedge a b|+‖B‖/‖A‖ := by
    apply C.opNorm_le_bound (by positivity)
    intro z
    obtain ⟨y,rfl⟩:=hB.surjective z
    rw [he]
    have hdot : |dot b y| ≤ ‖B y‖/‖B‖ := by
      apply (le_div_iff₀ hBp).mpr
      simpa [mul_comm] using expanded_projection_bound hB b hb hBb y
    have hwedge : |wedge b y| ≤ ‖B‖*‖B y‖ := by
      have hh : |wedge b y| ≤ ‖y‖ := by simpa only [hb,one_mul] using abs_wedge_le_norm_mul b y
      exact hh.trans (hB.norm_lower y)
    have hwb : |wedge a (quarterTurn b)| ≤ 1 := by
      simpa [ha,hb,norm_quarterTurn] using abs_wedge_le_norm_mul a (quarterTurn b)
    have hAperp : ‖A (quarterTurn b)‖ ≤ ‖A‖*|wedge a b|+‖A‖⁻¹ := by
      have hh:=two_singular_upper hA a ha hAa (quarterTurn b)
      rw [dot_quarterTurn_right,abs_neg] at hh
      exact hh.trans (add_le_add_right (by simpa using mul_le_mul_of_nonneg_left hwb (inv_nonneg.mpr (norm_nonneg A))) _)
    calc
      ‖A y‖ = ‖dot b y • A b+wedge b y • A (quarterTurn b)‖ := by
        conv_lhs => rw [unit_expansion b y hb]
        rw [map_add,map_smul,map_smul]
      _ ≤ |dot b y| *‖A b‖+|wedge b y| *‖A (quarterTurn b)‖ := by
        simpa only [norm_smul,Real.norm_eq_abs] using norm_add_le (dot b y • A b) (wedge b y • A (quarterTurn b))
      _ ≤ (‖B y‖/‖B‖)*‖A‖+(‖B‖*‖B y‖)*(‖A‖*|wedge a b|+‖A‖⁻¹) := by
        gcongr
        simpa [hb] using A.le_opNorm b
      _ = _ := by ring
  constructor
  · apply max_le
    · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
      have hh:=mul_le_mul_of_nonneg_right angle hBp.le
      simp only [mul_assoc,inv_mul_cancel₀ hBp.ne',mul_one] at hh
      nlinarith only [hh]
    · apply max_le
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hAp).mp
        calc
          _ = ‖B‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normBA
      · apply (le_div_iff₀ (mul_pos hAp hBp)).mpr
        apply (mul_le_mul_iff_right₀ hBp).mp
        calc
          _ = ‖A‖ := by field_simp [hAp.ne',hBp.ne']
          _ ≤ _ := by simpa only [mul_comm] using normAB
  · apply (div_le_iff₀ (mul_pos hAp hBp)).mpr
    calc
      _ ≤ _ := upper
      _ = _ := by field_simp [hAp.ne',hBp.ne']; ring

lemma normalized_transfer_fourpoint {ι : Type*}
    (A : ι → (ℂ →L[ℝ] ℂ)) (T : ι → ι → (ℂ →L[ℝ] ℂ))
    (hA : ∀ i, PlaneAreaPreserving (A i)) (hT : ∀ i j, PlaneAreaPreserving (T i j))
    (hcomp : ∀ i j z, T i j (A j z)=A i z) (j l p : ι) :
    ‖T j p‖/(‖A j‖*‖A p‖) ≤
      6*max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by
  choose a ha hnorm horth hperp hD using fun i => (hA i).singular_pair
  have hs (i q : ι) := transfer_angle_bounds (hA i) (hA q) (hT i q)
    (hcomp i q) (a i) (a q) (ha i) (ha q) (hnorm i) (hnorm q)
  have hjl:=hs j l
  have hlp:=hs l p
  have hjp:=hs j p
  have hangle:=wedge_sine_triangle (a j) (a l) (a p) (ha j) (ha l) (ha p)
  have hj : ‖A j‖⁻¹^2 ≤ ‖T j l‖/(‖A j‖*‖A l‖) :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hjl.1)
  have hp : ‖A p‖⁻¹^2 ≤ ‖T l p‖/(‖A l‖*‖A p‖) :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlp.1)
  have ha1 : |wedge (a j) (a l)| ≤ ‖T j l‖/(‖A j‖*‖A l‖) := (le_max_left _ _).trans hjl.1
  have ha2 : |wedge (a l) (a p)| ≤ ‖T l p‖/(‖A l‖*‖A p‖) := (le_max_left _ _).trans hlp.1
  have hm1 := le_max_left (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hm2 := le_max_right (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖))
  have hnon : 0 ≤ max (‖T j l‖/(‖A j‖*‖A l‖)) (‖T l p‖/(‖A l‖*‖A p‖)) := by positivity
  linarith [hjp.2]
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ProductDistances
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma transfer_distance_fourpoint (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    productDistance k z j p-productDistance k z i j-productDistance k z i p ≤
      max (productDistance k z j l-productDistance k z i j-productDistance k z i l)
        (productDistance k z l p-productDistance k z i l-productDistance k z i p)+
        Real.log 6/Real.log (growthBase k) := by
  let A := fun j => (torusTransfer k z i j).toContinuousLinearMap
  let T := fun j p => (torusTransfer k z p j).toContinuousLinearMap
  let R := fun j p => ‖T j p‖/(‖A j‖*‖A p‖)
  have hR : ∀ j p, 0<R j p := fun j p => div_pos (torusTransfer_norm_pos k z p j)
    (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p))
  have hc := normalized_transfer_fourpoint A T (fun j => torusTransfer_area k z i j)
    (fun j p => torusTransfer_area k z p j) (fun j p u => torusTransfer_comp k z i p j u) j l p
  change R j p≤6*max (R j l) (R l p) at hc
  have he (j p : ℤ) : Real.log (R j p)/Real.log (growthBase k)=
      productDistance k z j p-productDistance k z i j-productDistance k z i p := by
    dsimp only [R,A,T]
    rw [Real.log_div (torusTransfer_norm_pos k z p j).ne'
      (mul_pos (torusTransfer_norm_pos k z i j) (torusTransfer_norm_pos k z i p)).ne',
      Real.log_mul (torusTransfer_norm_pos k z i j).ne' (torusTransfer_norm_pos k z i p).ne',
      torusTransfer_norm_symm k z p j]
    unfold productDistance; ring
  have hm : Real.log (max (R j l) (R l p))=max (Real.log (R j l)) (Real.log (R l p)) := by
    rcases le_total (R j l) (R l p) with h | h
    · rw [max_eq_right h,max_eq_right (Real.log_le_log (hR j l) h)]
    · rw [max_eq_left h,max_eq_left (Real.log_le_log (hR l p) h)]
  have hlog := Real.log_le_log (hR j p) hc
  rw [Real.log_mul (by norm_num : (6:ℝ)≠0) (lt_of_lt_of_le (hR j l) (le_max_left _ _)).ne',hm] at hlog
  have hd := div_le_div_of_nonneg_right hlog (log_growthBase_pos k hk).le
  rw [add_div,← max_div_div_right (log_growthBase_pos k hk).le,he,he,he] at hd
  linarith
lemma log_six_div_growth_le_three (k : ℝ) (hk : 0≤k) : Real.log 6/Real.log (growthBase k)≤3 := by
  apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
  have hh := Real.log_le_log (by norm_num : (0:ℝ)<6)
    (show (6:ℝ)≤growthBase k^3 by
      have hp := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤4) (growthBase_ge_four k hk) 3
      norm_num at hp ⊢; linarith)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

lemma productDistance_tree (k : ℝ) (hk : 0≤k) (z : Torus) (i j l p : ℤ) :
    min (productDistance k z i j+productDistance k z i l-productDistance k z j l)
        (productDistance k z i l+productDistance k z i p-productDistance k z l p)-3 ≤
      productDistance k z i j+productDistance k z i p-productDistance k z j p := by
  have hh := transfer_distance_fourpoint k hk z i j l p
  have he := log_six_div_growth_le_three k hk
  rcases le_total (productDistance k z i j+productDistance k z i l-productDistance k z j l)
      (productDistance k z i l+productDistance k z i p-productDistance k z l p) with h | h
  · rw [min_eq_left h]
    rw [max_eq_left (by linarith)] at hh
    linarith
  · rw [min_eq_right h]
    rw [max_eq_right (by linarith)] at hh
    linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ScaleTruncation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy

lemma min_tree_chain {a b c x y e : ℝ} (he : 0≤e)
    (hx : min a b-e≤x) (hy : min x c-e≤y) : min a (min b c)-2*e≤y := by
  have ha : min a (min b c)≤a := min_le_left _ _
  have hb : min a (min b c)≤b := (min_le_right _ _).trans (min_le_left _ _)
  have hc : min a (min b c)≤c := (min_le_right _ _).trans (min_le_right _ _)
  have h1 : min a (min b c)-e≤x := by have := le_min ha hb; linarith
  have h2 : min a (min b c)-e≤ min x c := le_min h1 (by linarith)
  linarith
lemma productDistance_cut_wings (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let D := (n:ℝ)-min (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
    (s:ℝ)-D≤productDistance k z i (i-(s:ℤ)) ∧
      (s:ℝ)-D≤productDistance k z i (i+(s:ℤ)) := by
  dsimp only
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  have hL := productDistance_triangle k hk z i (i-(s:ℤ)) (i-(n:ℤ))
  have hR := productDistance_triangle k hk z i (i+(s:ℤ)) (i+(n:ℤ))
  have bL := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
  have bR := productDistance_le k hk z (i+(s:ℤ)) (i+(n:ℤ))
  simp only [Int.cast_add,Int.cast_sub,Int.cast_natCast] at bL bR
  rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at bL
  rw [show (i:ℝ)+n-((i:ℝ)+s)=(n:ℝ)-s by ring,abs_of_nonneg (by linarith)] at bR
  have hminL := min_le_left (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  have hminR := min_le_right (productDistance k z i (i-(n:ℤ))) (productDistance k z i (i+(n:ℤ)))
  constructor <;> linarith
lemma productDistance_truncation (k : ℝ) (hk : 0≤k) (z : Torus) (i : ℤ)
    (n s : ℕ) (hsn : s≤n) :
    let g := productDistance k z
    let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
    let loss := g i (i-(n:ℤ))+g i (i+(n:ℤ))-g (i-(n:ℤ)) (i+(n:ℤ))
    min loss (2*(s:ℝ)-2*D)-6≤g i (i-(s:ℤ))+g i (i+(s:ℤ))-g (i-(s:ℤ)) (i+(s:ℤ)) := by
  let g := productDistance k z
  let D := (n:ℝ)-min (g i (i-(n:ℤ))) (g i (i+(n:ℤ)))
  let B := fun u v => g i u+g i v-g u v
  change min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D)-6≤B (i-(s:ℤ)) (i+(s:ℤ))
  have ht (u v w : ℤ) : min (B u v) (B v w)-3≤B u w := productDistance_tree k hk z i u v w
  have hns : (s:ℝ)≤n := by exact_mod_cast hsn
  obtain ⟨hcL,hcR⟩ := productDistance_cut_wings k hk z i n s hsn
  have hwL : (n:ℝ)-D≤g i (i-(n:ℤ)) := by
    dsimp only [D]; have := min_le_left (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hwR : (n:ℝ)-D≤g i (i+(n:ℤ)) := by
    dsimp only [D]; have := min_le_right (g i (i-(n:ℤ))) (g i (i+(n:ℤ))); linarith
  have hbL : g (i-(s:ℤ)) (i-(n:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i-(s:ℤ)) (i-(n:ℤ))
    simp only [Int.cast_sub,Int.cast_natCast] at hh
    rw [show (i:ℝ)-n-((i:ℝ)-s)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hbR : g (i+(n:ℤ)) (i+(s:ℤ))≤(n:ℝ)-s := by
    have hh := productDistance_le k hk z (i+(n:ℤ)) (i+(s:ℤ))
    simp only [Int.cast_add,Int.cast_natCast] at hh
    rw [show (i:ℝ)+s-((i:ℝ)+n)=(s:ℝ)-n by ring,abs_of_nonpos (by linarith)] at hh
    linarith
  have hBL : 2*(s:ℝ)-2*D≤B (i-(s:ℤ)) (i-(n:ℤ)) := by
    change (s:ℝ)-D≤g i (i-(s:ℤ)) at hcL
    dsimp only [B]; linarith
  have hBR : 2*(s:ℝ)-2*D≤B (i+(n:ℤ)) (i+(s:ℤ)) := by
    change (s:ℝ)-D≤g i (i+(s:ℤ)) at hcR
    dsimp only [B]; linarith
  have hh := min_tree_chain (by norm_num : (0:ℝ)≤3)
    (ht (i-(s:ℤ)) (i-(n:ℤ)) (i+(n:ℤ)))
    (ht (i-(s:ℤ)) (i+(n:ℤ)) (i+(s:ℤ)))
  have hmin : min (B (i-(n:ℤ)) (i+(n:ℤ))) (2*(s:ℝ)-2*D) ≤
      min (B (i-(s:ℤ)) (i-(n:ℤ))) (min (B (i-(n:ℤ)) (i+(n:ℤ))) (B (i+(n:ℤ)) (i+(s:ℤ)))) := by
    exact le_min ((min_le_right _ _).trans hBL)
      (le_min (min_le_left _ _) ((min_le_right _ _).trans hBR))
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_GoodCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pairMagnitude_step_bounds (M : ℝ) (v : ℕ → ℝ) (a b : ℝ) (j : ℕ)
    (hj : 1≤j) (hv : |v j|+1≤M) :
    pairMagnitude (linearSolution v a b) (j+1) ≤ M*pairMagnitude (linearSolution v a b) j ∧
    pairMagnitude (linearSolution v a b) j ≤ M*pairMagnitude (linearSolution v a b) (j+1) := by
  let u:=linearSolution v a b
  have hstep : u (j+1)=v j*u j-u (j-1) := by
    have h:=linearSolution_step v a b (j-1)
    have hidx : j-1+2=j+1 := by omega
    simpa [u,Nat.sub_add_cancel hj,hidx] using h
  have hb := abs_sub (v j*u j) (u (j-1))
  rw [abs_mul] at hb
  have hinv : u (j-1)=v j*u j-u (j+1) := by linarith [hstep]
  have hb' := abs_sub (v j*u j) (u (j+1))
  rw [abs_mul] at hb'
  have hM : 1≤M := by linarith [abs_nonneg (v j)]
  have huj : |u j|≤pairMagnitude u j := le_max_left _ _
  have hup : |u (j-1)|≤pairMagnitude u j := le_max_right _ _
  have hun : |u (j+1)|≤pairMagnitude u (j+1) := le_max_left _ _
  have huj' : |u j|≤pairMagnitude u (j+1) := by simp [pairMagnitude]
  constructor
  · apply max_le
    · change |u (j+1)|≤M*pairMagnitude u j
      rw [hstep]
      calc
        _ ≤ |v j| *|u j|+|u (j-1)| := hb
        _ ≤ (|v j|+1)*pairMagnitude u j := by nlinarith [mul_le_mul_of_nonneg_left huj (abs_nonneg (v j))]
        _ ≤ _ := mul_le_mul_of_nonneg_right hv (pairMagnitude_nonneg _ _)
    · change |u (j+1-1)|≤M*pairMagnitude u j
      simp only [Nat.add_sub_cancel]
      exact huj.trans (le_mul_of_one_le_left (pairMagnitude_nonneg _ _) hM)
  · apply max_le
    · exact huj'.trans (le_mul_of_one_le_left (pairMagnitude_nonneg _ _) hM)
    · change |u (j-1)| ≤ M*pairMagnitude u (j+1)
      rw [hinv]
      calc
        _ ≤ |v j| *|u j|+|u (j+1)| := hb'
        _ ≤ (|v j|+1)*pairMagnitude u (j+1) := by nlinarith [mul_le_mul_of_nonneg_left huj' (abs_nonneg (v j))]
        _ ≤ _ := mul_le_mul_of_nonneg_right hv (pairMagnitude_nonneg _ _)
lemma pairLog_step_abs (M : ℝ) (v : ℕ → ℝ) (a b : ℝ) (j : ℕ)
    (hM : 1<M) (hj : 1≤j) (hv : |v j|+1≤M)
    (hp : 0<pairMagnitude (linearSolution v a b) j)
    (hn : 0<pairMagnitude (linearSolution v a b) (j+1)) :
    |pairLog M (linearSolution v a b) (j+1)-pairLog M (linearSolution v a b) j|≤1 := by
  have hh:=pairMagnitude_step_bounds M v a b j hj hv
  have hm : 0<M := lt_trans zero_lt_one hM
  have hlog : Real.logb M M=1 := by simp [Real.logb,ne_of_gt (Real.log_pos hM)]
  have hi := (Real.logb_le_logb hM hn (mul_pos hm hp)).mpr hh.1
  have hi' := (Real.logb_le_logb hM hp (mul_pos hm hn)).mpr hh.2
  rw [Real.logb_mul (ne_of_gt hm) (ne_of_gt hp),hlog] at hi
  rw [Real.logb_mul (ne_of_gt hm) (ne_of_gt hn),hlog] at hi'
  exact abs_le.mpr ⟨by dsimp [pairLog]; linarith,by dsimp [pairLog]; linarith⟩

lemma shortfall_count_subset (z : ℕ → ℝ) (c : ℝ) (hc : c<1) (N q : ℕ)
    (hN : 1≤N) (hz : ∀ j, 1≤j → j<N → z (j+1)-z j≤1)
    (S : Finset ℕ) (hS : ∀ j∈S, 2≤j+q ∧ j+q≤N ∧
      ∃ l, 1≤l ∧ l<j+q ∧ z (j+q)-z l<c*((j+q : ℕ)-(l : ℝ))) :
    (S.card : ℝ) ≤ ((N : ℝ)-1-(z N-z 1))/(1-c) := by
  classical
  let B := (Finset.range (N-1)).filter fun n => ∃ l<n+1,
    z (n+1+1)-z (l+1)<c*((n+1 : ℕ)-(l : ℝ))
  have hcard : S.card≤B.card := by
    apply Finset.card_le_card_of_injOn (fun j => j+q-2)
    · intro j hj
      obtain ⟨h2,hN',l,hl,hlj,hbad⟩ := hS j hj
      dsimp only
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_range.mpr (by omega),l-1,by omega,?_⟩
      have hjq : j+q-2+1+1=j+q := by omega
      have hjq' : (j+q-2+1 : ℕ)=(j+q)-1 := by omega
      rw [hjq,Nat.sub_add_cancel hl]
      have e : ((j+q-2+1 : ℕ):ℝ)-((l-1 : ℕ):ℝ)=((j+q : ℕ):ℝ)-(l : ℝ) := by
        rw [hjq', Nat.cast_sub (by omega : 1≤j+q), Nat.cast_sub hl]
        norm_num
      rw [e]
      exact hbad
    · intro i hi j hj he
      dsimp only at he
      have hi':= (hS i hi).1
      have hj':= (hS j hj).1
      omega
  have hb := shortfall_count (fun j => z (j+1)) c hc (N-1) (fun n hn => hz (n+1) (by omega) (by omega))
  have hNeq : N-1+1=N := Nat.sub_add_cancel hN
  simp only [hNeq,zero_add] at hb
  have hNr : ((N-1 : ℕ):ℝ)=(N:ℝ)-1 := by rw [Nat.cast_sub hN]; norm_num
  rw [hNr] at hb
  exact (Nat.cast_le.mpr hcard).trans hb

lemma good_failures_count (τ σ : ℕ → ℝ) (c : ℝ) (hc : c<1) (N : ℕ) (hN : 2≤N)
    (hτ : ∀ j, 1≤j → j<N → τ (j+1)-τ j≤1)
    (hσ : ∀ j, 1≤j → j<N → σ (j+1)-σ j≤1) :
    (((Finset.Icc (2:ℕ) (N-2)).filter fun j => ¬
      ((∀ l : ℕ, 1≤l → l<j → c*((j : ℝ)-(l : ℝ))≤τ j-τ l) ∧
       c≤τ (j+1)-τ j ∧ c≤σ (j+1)-σ j ∧ c≤σ (j+2)-σ (j+1))).card : ℝ) ≤
      2*(((N : ℝ)-1-(τ N-τ 1))+((N : ℝ)-1-(σ N-σ 1)))/(1-c) := by
  classical
  let S:=Finset.Icc (2:ℕ) (N-2)
  let P0 := fun j : ℕ => ∃ l : ℕ, 1≤l ∧ l<j ∧ τ j-τ l<c*((j : ℝ)-(l : ℝ))
  let P1 := fun j => τ (j+1)-τ j<c
  let P2 := fun j => σ (j+1)-σ j<c
  let P3 := fun j => σ (j+2)-σ (j+1)<c
  have h0:=shortfall_count_subset τ c hc N 0 (by omega) hτ (S.filter P0) (by
    intro j hj
    obtain ⟨hj,hp⟩:=Finset.mem_filter.mp hj
    obtain ⟨hj2,hjN⟩:=Finset.mem_Icc.mp hj
    exact ⟨by omega,by omega,by simpa [P0] using hp⟩)
  have inc (z : ℕ → ℝ) (q : ℕ) (hq : q=1 ∨ q=2)
      (hz : ∀ j, 1≤j → j<N → z (j+1)-z j≤1) :
      ((S.filter fun j => z (j+q)-z (j+q-1)<c).card : ℝ) ≤
        ((N : ℝ)-1-(z N-z 1))/(1-c) := by
    apply shortfall_count_subset z c hc N q (by omega) hz
    intro j hj
    obtain ⟨hj,hp⟩:=Finset.mem_filter.mp hj
    obtain ⟨hj2,hjN⟩:=Finset.mem_Icc.mp hj
    refine ⟨by omega,by omega,j+q-1,by omega,by omega,?_⟩
    have he : ((j+q : ℕ):ℝ)-((j+q-1 : ℕ):ℝ)=1 := by
      rw [Nat.cast_sub (by omega : 1≤j+q)]; simp
    rw [he, mul_one]
    exact hp
  have h1 : ((S.filter P1).card : ℝ)≤((N:ℝ)-1-(τ N-τ 1))/(1-c) := by
    simpa [P1] using inc τ 1 (Or.inl rfl) hτ
  have h2 : ((S.filter P2).card : ℝ)≤((N:ℝ)-1-(σ N-σ 1))/(1-c) := by
    simpa [P2] using inc σ 1 (Or.inl rfl) hσ
  have h3 : ((S.filter P3).card : ℝ)≤((N:ℝ)-1-(σ N-σ 1))/(1-c) := by
    simpa [P3] using inc σ 2 (Or.inr rfl) hσ
  have he : (S.filter fun j => ¬
      ((∀ l : ℕ, 1≤l → l<j → c*((j : ℝ)-(l : ℝ))≤τ j-τ l) ∧
       c≤τ (j+1)-τ j ∧ c≤σ (j+1)-σ j ∧ c≤σ (j+2)-σ (j+1))) =
      ((S.filter P0) ∪ (S.filter P1)) ∪ ((S.filter P2) ∪ (S.filter P3)) := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_union,P0,P1,P2,P3]
    simp only [not_and_or, not_forall, not_le, exists_prop]
    simp only [and_or_left,or_assoc]
  rw [he]
  have hh := Finset.card_union_le ((S.filter P0) ∪ (S.filter P1)) ((S.filter P2) ∪ (S.filter P3))
  have hh' := Finset.card_union_le (S.filter P0) (S.filter P1)
  have hh'' := Finset.card_union_le (S.filter P2) (S.filter P3)
  have hcard : (((S.filter P0) ∪ (S.filter P1) ∪ ((S.filter P2) ∪ (S.filter P3))).card : ℝ)≤
      (S.filter P0).card+(S.filter P1).card+(S.filter P2).card+(S.filter P3).card := by exact_mod_cast (by omega : _)
  calc
    _ ≤ _ := hcard
    _ ≤ 2*(((N : ℝ)-1-(τ N-τ 1))+((N : ℝ)-1-(σ N-σ 1)))/(1-c) := by
      calc
        _ ≤ ((N:ℝ)-1-(τ N-τ 1))/(1-c)+((N:ℝ)-1-(τ N-τ 1))/(1-c)+
            ((N:ℝ)-1-(σ N-σ 1))/(1-c)+((N:ℝ)-1-(σ N-σ 1))/(1-c) := by linarith
        _ = _ := by ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MatchingCore
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma half_unit_crossing (τ : ℕ → ℝ) (N : ℕ) (a : ℝ)
    (hτ : ∀ j, 1≤j → j<N → τ (j+1)-τ j≤1)
    (h1 : τ 1=0) (ha : 1<a) (hN1 : 1≤N) (hN : a≤τ N) :
    ∃ k, 2≤k ∧ k≤N ∧ |τ k-a|≤1/2 := by
  have hex : ∃ k : ℕ, 1≤k ∧ a≤τ k := ⟨N,hN1,hN⟩
  let k := Nat.find hex
  have hk : 1≤k ∧ a≤τ k := Nat.find_spec hex
  have hkle : k≤N := Nat.find_min' hex ⟨hN1,hN⟩
  have hk2 : 2≤k := by
    by_contra hn
    have he : k=1 := by omega
    rw [he,h1] at hk
    linarith
  have hprev : τ (k-1)<a := by
    have hf := Nat.find_min hex (by omega : k-1<k)
    exact lt_of_not_ge (fun h => hf ⟨by omega,h⟩)
  have hstep := hτ (k-1) (by omega) (by omega)
  rw [Nat.sub_add_cancel (by omega : 1≤k)] at hstep
  have hk3 : 3≤k := by
    by_contra hn
    have he : k=2 := by omega
    rw [he] at hstep
    norm_num [h1] at hstep
    have := hk.2
    rw [he] at this
    linarith
  by_cases hnear : τ k-a≤1/2
  · exact ⟨k,hk2,hkle,abs_le.mpr ⟨by linarith [hk.2],hnear⟩⟩
  · exact ⟨k-1,by omega,by omega,abs_le.mpr ⟨by linarith,by linarith⟩⟩
lemma separated_fiber_card (S : Finset ℕ) (τ : ℕ → ℝ) (a c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-a|≤1/2) : S.card≤2 := by
  classical
  by_cases hS : S.Nonempty
  · let m := S.min' hS
    have hm : m∈S := S.min'_mem hS
    have hsub : S⊆Finset.Icc m (m+1) := by
      intro j hj
      have hjm : m≤j := S.min'_le _ hj
      refine Finset.mem_Icc.mpr ⟨hjm,?_⟩
      by_contra hf
      have hd : (m:ℝ)+2≤(j:ℝ) := by exact_mod_cast (by omega : m+2≤j)
      have hs := hsep m hm j hj (by omega)
      have hmi := (abs_le.mp (hclose m hm)).1
      have hji := (abs_le.mp (hclose j hj)).2
      nlinarith
    have hh := Finset.card_le_card hsub
    simp only [Nat.card_Icc] at hh
    omega
  · simp [Finset.not_nonempty_iff_eq_empty.mp hS]

lemma discard_bad_matches (S B : Finset ℕ) (τ ρ : ℕ → ℝ) (f : ℕ → ℕ) (c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-ρ (f i)|≤1/2) :
    (S.filter fun i => f i∈B).card≤2*B.card := by
  classical
  have hfiber (b : ℕ) : ((S.filter fun i => f i∈B).filter fun i => f i=b).card≤2 := by
    apply separated_fiber_card _ τ (ρ b) c hc
    · intro i hi j hj hij
      exact hsep i (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
        j (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1 hij
    · intro i hi
      obtain ⟨hi,he⟩ := Finset.mem_filter.mp hi
      simpa only [he] using hclose i (Finset.mem_filter.mp hi).1
  have he := Finset.card_eq_sum_card_fiberwise (f := f) (s := S.filter fun i => f i∈B)
    (t := B) (fun i hi => (Finset.mem_filter.mp hi).2)
  rw [he]
  calc
    _ ≤ ∑ _b∈B, 2 := Finset.sum_le_sum fun b _ => hfiber b
    _ = _ := by simp [mul_comm]

lemma spaced_matched_subset (S : Finset ℕ) (τ ρ : ℕ → ℝ) (f : ℕ → ℕ) (c : ℝ)
    (hc : 1/2<c)
    (hsep : ∀ i∈S, ∀ j∈S, i<j → c*((j:ℝ)-(i:ℝ))≤τ j-τ i)
    (hclose : ∀ i∈S, |τ i-ρ (f i)|≤1/2)
    (horder : ∀ i∈S, ∀ j∈S, f j≤f i → ρ (f j)≤ρ (f i)) :
    ∃ T : Finset ℕ, T⊆S ∧ S.card/3≤T.card ∧
      ∀ i∈T, ∀ j∈T, i<j → f i<f j := by
  classical
  obtain ⟨r,hr,hcard⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
    (s := S) (t := Finset.range 3) (f := fun i => i%3)
    (fun i _ => Finset.mem_range.mpr (Nat.mod_lt i (by omega)))
    (by simp) (by simpa using Nat.mul_div_le S.card 3)
  let T:=S.filter fun i => i%3=r
  refine ⟨T,Finset.filter_subset _ _,hcard,?_⟩
  intro i hi j hj hij
  obtain ⟨hi,hir⟩ := Finset.mem_filter.mp hi
  obtain ⟨hj,hjr⟩ := Finset.mem_filter.mp hj
  have hd : i+3≤j := by omega
  have hdr : (i:ℝ)+3≤(j:ℝ) := by exact_mod_cast hd
  have hs := hsep i hi j hj hij
  have hi' := (abs_le.mp (hclose i hi)).1
  have hj' := (abs_le.mp (hclose j hj)).2
  by_contra hf
  have hm := horder i hi j hj (by omega)
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ManyGood
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pairMagnitude_wronskian (v : ℕ → ℝ) (b : ℝ) (N : ℕ) (hN : 1≤N) :
    1 ≤ 2*pairMagnitude (linearSolution v 1 b) N*pairMagnitude (tSolution v) N := by
  let u:=linearSolution v 1 b
  let t:=tSolution v
  have hw := solution_wronskian v 1 b (N-1)
  rw [Nat.sub_add_cancel hN] at hw
  have habs : |u (N-1)*t N-u N*t (N-1)|=1 := by rw [hw]; norm_num
  have h1 : |u (N-1)|≤pairMagnitude u N := le_max_right _ _
  have h2 : |u N|≤pairMagnitude u N := le_max_left _ _
  have h3 : |t N|≤pairMagnitude t N := le_max_left _ _
  have h4 : |t (N-1)|≤pairMagnitude t N := le_max_right _ _
  calc
    1 = |u (N-1)*t N-u N*t (N-1)| := habs.symm
    _ ≤ |u (N-1)| *|t N|+|u N| *|t (N-1)| := by simpa only [abs_mul] using abs_sub (u (N-1)*t N) (u N*t (N-1))
    _ ≤ pairMagnitude u N*pairMagnitude t N+pairMagnitude u N*pairMagnitude t N :=
      add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (pairMagnitude_nonneg _ _))
        (mul_le_mul h2 h4 (abs_nonneg _) (pairMagnitude_nonneg _ _))
    _ = _ := by dsimp [u,t]; ring
lemma pairLog_t_one (v : ℕ → ℝ) (M : ℝ) : pairLog M (tSolution v) 1=0 := by
  simp [pairLog,pairMagnitude,tSolution]
lemma pairLog_normalized_one_nonneg (v : ℕ → ℝ) (b M : ℝ) (hM : 1<M) :
    0≤pairLog M (linearSolution v 1 b) 1 := by
  apply Real.logb_nonneg hM
  simp [pairMagnitude]
lemma goodIndex_failure_bound (v : ℕ → ℝ) (b M : ℝ) (N : ℕ) (hN : 2≤N)
    (hM : 1<M) (hv : ∀ j, 1≤j → j<N → |v j|+1≤M) :
    ((badIndices M v b N).card : ℝ) ≤
      2*(((N:ℝ)-1-pairLog M (tSolution v) N)+
      ((N:ℝ)-1+pairLog M (linearSolution v 1 b) N-pairLog M (linearSolution v 1 b) 1))/(1-goodExponent) := by
  classical
  have ht (j : ℕ) (hj : 1≤j) (hjN : j<N) :=
    pairLog_step_abs M v 0 1 j hM hj (hv j hj hjN)
      (pairMagnitude_t_pos v j hj) (pairMagnitude_t_pos v (j+1) (by omega))
  have hu (j : ℕ) (hj : 1≤j) (hjN : j<N) :=
    pairLog_step_abs M v 1 b j hM hj (hv j hj hjN)
      (pairMagnitude_normalized_pos v b j hj) (pairMagnitude_normalized_pos v b (j+1) (by omega))
  have hh:=good_failures_count (pairLog M (tSolution v)) (fun j => -pairLog M (linearSolution v 1 b) j)
    goodExponent goodExponent_lt_one N hN
    (fun j hj hjN => (abs_le.mp (ht j hj hjN)).2)
    (fun j hj hjN => by have := (abs_le.mp (hu j hj hjN)).1; linarith)
  have he : (Finset.Icc (2:ℕ) (N-2)).filter (fun j => ¬GoodIndex M v b j) =
      (Finset.Icc (2:ℕ) (N-2)).filter (fun j => ¬
        ((∀ l : ℕ, 1≤l → l<j → goodExponent*((j:ℝ)-(l:ℝ))≤pairLog M (tSolution v) j-pairLog M (tSolution v) l) ∧
        goodExponent≤pairLog M (tSolution v) (j+1)-pairLog M (tSolution v) j ∧
        goodExponent≤ -pairLog M (linearSolution v 1 b) (j+1)-(-pairLog M (linearSolution v 1 b) j) ∧
        goodExponent≤ -pairLog M (linearSolution v 1 b) (j+2)-(-pairLog M (linearSolution v 1 b) (j+1)))) := by
    apply Finset.filter_congr
    intro j hj
    have hj2 := (Finset.mem_Icc.mp hj).1
    simp only [GoodIndex,hj2,true_and,neg_sub_neg]
  unfold badIndices
  rw [he]
  convert hh using 1
  rw [pairLog_t_one]
  ring
lemma small_endpoint_log_bounds (v : ℕ → ℝ) (b M E : ℝ) (N : ℕ)
    (hM : 1<M) (hN : 1≤N) (hE : 0<E)
    (hb : pairMagnitude (linearSolution v 1 b) N≤E) :
    -Real.logb M 2-Real.logb M E≤pairLog M (tSolution v) N ∧
    pairLog M (linearSolution v 1 b) N≤Real.logb M E := by
  have hu:=pairMagnitude_normalized_pos v b N hN
  have ht:=pairMagnitude_t_pos v N hN
  have hp : 1≤2*E*pairMagnitude (tSolution v) N := by
    have hh:=pairMagnitude_wronskian v b N hN
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) ht.le)
  have hlog := (Real.logb_le_logb hM (by norm_num : (0:ℝ)<1) (by positivity : 0<2*E*pairMagnitude (tSolution v) N)).mpr hp
  rw [Real.logb_one,Real.logb_mul (by positivity : (2*E:ℝ)≠0) (ne_of_gt ht),
    Real.logb_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hE)] at hlog
  exact ⟨by dsimp [pairLog]; linarith,(Real.logb_le_logb hM hu hE).mpr hb⟩

lemma many_good_small_endpoint (v : ℕ → ℝ) (b M s : ℝ) (N : ℕ) (hN : 2≤N)
    (hM : 1<M) (hv : ∀ j, 1≤j → j<N → |v j|+1≤M)
    (hb : pairMagnitude (linearSolution v 1 b) N≤3*M^(-s)) :
    ((badIndices M v b N).card : ℝ) ≤
      (4*((N:ℝ)-1-s)+2*Real.logb M 2+4*Real.logb M 3)/(1-goodExponent) := by
  have hm : 0<M := lt_trans zero_lt_one hM
  have hh:=goodIndex_failure_bound v b M N hN hM hv
  have he : Real.logb M (3*M^(-s))=Real.logb M 3-s := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hm _)), Real.logb_rpow hm (ne_of_gt hM)]
    ring
  obtain ⟨ht,hu⟩:=small_endpoint_log_bounds v b M (3*M^(-s)) N hM (by omega) (by positivity) hb
  rw [he] at ht hu
  have hu1:=pairLog_normalized_one_nonneg v b M hM
  apply hh.trans
  apply (div_le_div_iff_of_pos_right (by linarith [goodExponent_lt_one] : 0<1-goodExponent)).mpr
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MatchingAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma matching_subset (S B : Finset ℕ) (τ ρ : ℕ → ℝ) (N : ℕ) (c : ℝ)
    (hc : 1/2 < c) (hN : 2 ≤ N)
    (hρ : ∀ j, 1 ≤ j → j < N → ρ (j+1)-ρ j ≤ 1) (hρ1 : ρ 1=0)
    (hrange : ∀ j ∈ S, 1 < τ j ∧ τ j ≤ ρ N)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i < j → c*((j:ℝ)-(i:ℝ)) ≤ τ j-τ i)
    (hgood : ∀ i, 2 ≤ i → i ≤ N → i ∉ B → ∀ j, 2 ≤ j → j < i →
      c*((i:ℝ)-(j:ℝ)) ≤ ρ i-ρ j) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), T ⊆ S ∧ S.card ≤ 3*T.card+2*B.card+2 ∧
      (∀ i ∈ T, 2 ≤ f i ∧ f i ≤ N ∧ f i ∉ B ∧ |τ i-ρ (f i)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  classical
  have hex : ∀ i ∈ S, ∃ k, 2 ≤ k ∧ k ≤ N ∧ |τ i-ρ k| ≤ 1/2 := by
    intro i hi
    obtain ⟨k,hk2,hkN,hk⟩:=half_unit_crossing ρ N (τ i) hρ hρ1 (hrange i hi).1 (by omega) (hrange i hi).2
    exact ⟨k,hk2,hkN,by simpa only [abs_sub_comm] using hk⟩
  have hex' : ∀ i, ∃ k, i ∈ S → 2 ≤ k ∧ k ≤ N ∧ |τ i-ρ k| ≤ 1/2 := by
    intro i
    by_cases hi : i ∈ S
    · obtain ⟨k,hk⟩:=hex i hi
      exact ⟨k,fun _ => hk⟩
    · exact ⟨0,fun h => False.elim (hi h)⟩
  choose f hf using hex'
  let R := S.filter fun i => f i ∉ B
  have hR : R ⊆ S := Finset.filter_subset _ _
  have hloss := discard_bad_matches S B τ ρ f c hc hsep (fun i hi => (hf i hi).2.2)
  have hcard := Finset.card_filter_add_card_filter_not (s := S) (fun i => f i ∈ B)
  have horder : ∀ i ∈ R, ∀ j ∈ R, f j ≤ f i → ρ (f j) ≤ ρ (f i) := by
    intro i hi j hj hij
    by_cases he : f j=f i
    · simp [he]
    · have hi' := hf i (hR hi)
      have hj' := hf j (hR hj)
      have hh:=hgood (f i) hi'.1 hi'.2.1 (Finset.mem_filter.mp hi).2
        (f j) hj'.1 (lt_of_le_of_ne hij he)
      have hd : (f j:ℝ) ≤ (f i:ℝ) := by exact_mod_cast hij
      nlinarith
  obtain ⟨T,hTR,hT,hord⟩:=spaced_matched_subset R τ ρ f c hc
    (fun i hi j hj hij => hsep i (hR hi) j (hR hj) hij)
    (fun i hi => (hf i (hR hi)).2.2) horder
  refine ⟨T,f,hTR.trans hR,?_,?_,hord⟩
  · have hdiv : R.card ≤ 3*(R.card/3)+2 := by omega
    dsimp [R] at hT hdiv
    omega
  · intro i hi
    have hi' := hTR hi
    have hh := hf i (hR hi')
    exact ⟨hh.1,hh.2.1,(Finset.mem_filter.mp hi').2,hh.2.2⟩

lemma log_path_bounds (τ : ℕ → ℝ) (N : ℕ)
    (hstep : ∀ i, 1 ≤ i → i < N → τ (i+1)-τ i ≤ 1) (h1 : τ 1=0) :
    ∀ j, 1 ≤ j → j ≤ N → τ N-((N:ℝ)-(j:ℝ)) ≤ τ j ∧ τ j ≤ (j:ℝ)-1 := by
  have hinc : ∀ a b : ℕ, 1 ≤ a → a ≤ b → b ≤ N → τ b-τ a ≤ (b:ℝ)-(a:ℝ) := by
    intro a b ha hab hb
    induction b,hab using Nat.le_induction with
    | base => simp
    | succ b hab ih =>
      have ih' := ih (by omega)
      have hs := hstep b (by omega) (by omega)
      push_cast
      linarith
  intro j hj hjN
  have hleft:=hinc j N hj hjN le_rfl
  have hright:=hinc 1 j (by omega) hj hjN
  rw [h1] at hright
  norm_num at hright
  exact ⟨by linarith,by linarith⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MatchingQuantitative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma matching_of_shortfalls (M : ℝ) (vp vm : ℕ → ℝ) (bp bm : ℝ)
    (n Np Nm : ℕ) (hn : 1000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1)
    (hNm : n ≤ Nm ∧ Nm ≤ n+1) (hM : 1 < M)
    (hvp : ∀ j, 1 ≤ j → j < Np → |vp j|+1 ≤ M)
    (hvm : ∀ j, 1 ≤ j → j < Nm → |vm j|+1 ≤ M)
    (hshortp : (Np:ℝ)-1-pairLog M (tSolution vp) Np ≤ (n:ℝ)/1000)
    (hshortm : (Nm:ℝ)-1-pairLog M (tSolution vm) Nm ≤ (n:ℝ)/1000)
    (hbadp : (badIndices M vp bp Np).card ≤ n/1000)
    (hbadm : (badIndices M vm bm Nm).card ≤ n/1000) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), n/100 ≤ T.card ∧
      (∀ j ∈ T, 2 ≤ j ∧ j ≤ Np-2 ∧ GoodIndex M vp bp j ∧
        2 ≤ f j ∧ f j ≤ Nm-2 ∧ GoodIndex M vm bm (f j) ∧
        |pairLog M (tSolution vp) j-pairLog M (tSolution vm) (f j)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  classical
  let τ:=pairLog M (tSolution vp)
  let ρ:=pairLog M (tSolution vm)
  have hτstep (j : ℕ) (hj : 1 ≤ j) (hjN : j < Np) : τ (j+1)-τ j ≤ 1 :=
    (abs_le.mp (pairLog_step_abs M vp 0 1 j hM hj (hvp j hj hjN)
      (pairMagnitude_t_pos vp j hj) (pairMagnitude_t_pos vp (j+1) (by omega)))).2
  have hρstep (j : ℕ) (hj : 1 ≤ j) (hjN : j < Nm) : ρ (j+1)-ρ j ≤ 1 :=
    (abs_le.mp (pairLog_step_abs M vm 0 1 j hM hj (hvm j hj hjN)
      (pairMagnitude_t_pos vm j hj) (pairMagnitude_t_pos vm (j+1) (by omega)))).2
  have hτ1 : τ 1=0 := pairLog_t_one vp M
  have hρ1 : ρ 1=0 := pairLog_t_one vm M
  let I:=Finset.Icc (n/3) (n/2)
  let S:=I.filter fun j => GoodIndex M vp bp j
  let B:=badIndices M vm bm Nm
  have hI (j : ℕ) (hj : j ∈ I) : 2 ≤ j ∧ j ≤ Np-2 := by
    have hh:=Finset.mem_Icc.mp hj
    omega
  have hS (j : ℕ) (hj : j ∈ S) : j ∈ I ∧ GoodIndex M vp bp j := Finset.mem_filter.mp hj
  have hcard : n/2+1-n/3 ≤ S.card+n/1000 := by
    have hbad : (I.filter fun j => ¬GoodIndex M vp bp j).card ≤ (badIndices M vp bp Np).card := by
      apply Finset.card_le_card
      intro j hj
      obtain ⟨hj,hg⟩:=Finset.mem_filter.mp hj
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr (hI j hj),hg⟩
    have hh:=Finset.card_filter_add_card_filter_not (s := I) (fun j => GoodIndex M vp bp j)
    have hIc : I.card=n/2+1-n/3 := by simp [I,Nat.card_Icc]
    dsimp [S]
    omega
  have hnR : (1000:ℝ) ≤ n := by exact_mod_cast hn
  have hrange : ∀ j ∈ S, 1 < τ j ∧ τ j ≤ ρ (Nm-2) := by
    intro j hj
    have hjI:=Finset.mem_Icc.mp (hS j hj).1
    have hjbd:=hI j (hS j hj).1
    have hh:=log_path_bounds τ Np hτstep hτ1 j (by omega) (by omega)
    have hm:=log_path_bounds ρ Nm hρstep hρ1 (Nm-2) (by omega) (by omega)
    have hjlo : (n:ℝ)/3-1 ≤ j := by
      have hnat : n ≤ 3*j+2 := by omega
      have hreal : (n:ℝ) ≤ 3*(j:ℝ)+2 := by exact_mod_cast hnat
      linarith
    have hjhi : (j:ℝ) ≤ (n:ℝ)/2 := by
      have hnat : 2*j ≤ n := by omega
      have hreal : 2*(j:ℝ) ≤ n := by exact_mod_cast hnat
      linarith
    have hNmR : (n:ℝ) ≤ Nm := by exact_mod_cast hNm.1
    have he : ((Nm-2:ℕ):ℝ)=(Nm:ℝ)-2 := by rw [Nat.cast_sub (by omega)]; norm_num
    rw [he] at hm
    dsimp [τ,ρ] at *
    exact ⟨by linarith,by linarith⟩
  obtain ⟨T,f,hTS,hct,hmatch,hord⟩:=matching_subset S B τ ρ (Nm-2) goodExponent
    (by norm_num [goodExponent]) (by omega)
    (fun j hj hjN => hρstep j hj (by omega)) hρ1 hrange
    (by
      intro i hi j hj hij
      exact (hS j hj).2.2.1 i (by have := (hS i hi).2.1; omega) hij)
    (by
      intro i hi hiN hinB j hj hji
      have hgood : GoodIndex M vm bm i := by
        by_contra hnot
        exact hinB (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hi,hiN⟩,hnot⟩)
      exact hgood.2.1 j (by omega) hji)
  refine ⟨T,f,?_,?_,hord⟩
  · dsimp [B] at hct
    omega
  · intro j hj
    have hp:=hS j (hTS hj)
    have hb:=hI j hp.1
    have hm:=hmatch j hj
    refine ⟨hb.1,hb.2,hp.2,hm.1,hm.2.1,?_,hm.2.2.2⟩
    by_contra hnot
    exact hm.2.2.1 (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm.1,hm.2.1⟩,hnot⟩)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_EndpointMatching
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma endpoint_shortfall_bounds (M : ℝ) (v : ℕ → ℝ) (b : ℝ) (n N : ℕ)
    (hn : 10000000 ≤ n) (hN : n ≤ N ∧ N ≤ n+1) (hM : 6 ≤ M)
    (hv : ∀ j, 1 ≤ j → j < N → |v j|+1 ≤ M)
    (hb : pairMagnitude (linearSolution v 1 b) N ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    (N:ℝ)-1-pairLog M (tSolution v) N ≤ (n:ℝ)/1000 ∧
      (badIndices M v b N).card ≤ n/1000 := by
  have hm : 1 < M := by linarith
  have hm0 : 0 < M := by linarith
  have hlog2 : Real.logb M 2 ≤ 1 := by
    rw [← Real.logb_self_eq_one hm]
    exact (Real.logb_le_logb hm (by norm_num) hm0).mpr (by linarith)
  have hlog3 : Real.logb M 3 ≤ 1 := by
    rw [← Real.logb_self_eq_one hm]
    exact (Real.logb_le_logb hm (by norm_num) hm0).mpr (by linarith)
  have hnR : (10000000:ℝ) ≤ n := by exact_mod_cast hn
  have hNR : (N:ℝ) ≤ (n:ℝ)+1 := by exact_mod_cast hN.2
  have ht:=small_endpoint_log_bounds v b M (3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) N hm (by omega) (by positivity) hb
  have he : Real.logb M (3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) =
      Real.logb M 3-(1-3/100000000:ℝ)*(n:ℝ) := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hm0 _)),Real.logb_rpow hm0 hm.ne']
    ring
  rw [he] at ht
  have hg:=many_good_small_endpoint v b M ((1-3/100000000:ℝ)*(n:ℝ)) N (by omega) hm hv hb
  norm_num [goodExponent] at hg
  constructor
  · linarith [ht.1]
  · have htin : ((badIndices M v b N).card:ℝ) ≤ (n:ℝ)/1000-1 := by linarith
    have he' : (n:ℝ)/1000-1 < (↑(n/1000):ℝ)+1 := by
      have hnn : n ≤ 1000*(n/1000)+999 := by omega
      have hnnR : (n:ℝ) ≤ 1000*(↑(n/1000):ℝ)+999 := by exact_mod_cast hnn
      linarith
    have hlt : (badIndices M v b N).card < n/1000+1 := by exact_mod_cast htin.trans_lt he'
    omega
lemma matching_small_endpoints (M : ℝ) (vp vm : ℕ → ℝ) (bp bm : ℝ)
    (n Np Nm : ℕ) (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1)
    (hNm : n ≤ Nm ∧ Nm ≤ n+1) (hM : 6 ≤ M)
    (hvp : ∀ j, 1 ≤ j → j < Np → |vp j|+1 ≤ M)
    (hvm : ∀ j, 1 ≤ j → j < Nm → |vm j|+1 ≤ M)
    (hbp : pairMagnitude (linearSolution vp 1 bp) Np ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ))))
    (hbm : pairMagnitude (linearSolution vm 1 bm) Nm ≤ 3*M^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    ∃ (T : Finset ℕ) (f : ℕ → ℕ), n/100 ≤ T.card ∧
      (∀ j ∈ T, 2 ≤ j ∧ j ≤ Np-2 ∧ GoodIndex M vp bp j ∧
        2 ≤ f j ∧ f j ≤ Nm-2 ∧ GoodIndex M vm bm (f j) ∧
        |pairLog M (tSolution vp) j-pairLog M (tSolution vm) (f j)| ≤ 1/2) ∧
      (∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) := by
  have hp:=endpoint_shortfall_bounds M vp bp n Np hn hNp hM hvp hbp
  have hm:=endpoint_shortfall_bounds M vm bm n Nm hn hNm hM hvm hbm
  exact matching_of_shortfalls M vp vm bp bm n Np Nm (by omega) hNp hNm (by linarith)
    hvp hvm hp.1 hm.1 hp.2 hm.2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CoverContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy

lemma covering_contraction {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (F : Set X)
    (r s : X → ℝ) (R : ℝ) (η : ℝ≥0∞)
    (hr : ∀ x∈F, 0<r x ∧ r x≤R)
    (hlocal : ∀ b∈F,
      μ (⋃ a∈F, ⋃ (_ : (ball a (r a) ∩ ball b (r b)).Nonempty ∧ r a≤2*r b), ball a (s a)) ≤
        η*μ (ball b (r b))) :
    μ (⋃ a∈F, ball a (s a)) ≤ η*μ (⋃ a∈F, ball a (r a)) := by
  obtain ⟨U,hUF,hdisj,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement
    (fun x => ball x (r x)) F r 2 (by norm_num)
    (fun x hx => (hr x hx).1.le) R (fun x hx => (hr x hx).2)
    (fun x hx => ⟨x,mem_ball_self (hr x hx).1⟩)
  have hcount : U.Countable := hdisj.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x,mem_ball_self (hr x (hUF hx)).1⟩)
  let G := fun b => ⋃ a∈F, ⋃ (_ : (ball a (r a) ∩ ball b (r b)).Nonempty ∧ r a≤2*r b), ball a (s a)
  have hsub : (⋃ a∈F, ball a (s a)) ⊆ ⋃ b∈U, G b := by
    intro x hx
    obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
    obtain ⟨b,hb,hab,hrab⟩ := hcover a ha
    exact mem_iUnion₂.mpr ⟨b,hb,mem_iUnion₂.mpr ⟨a,ha,mem_iUnion.mpr ⟨⟨hab,hrab⟩,hx⟩⟩⟩
  calc
    _ ≤ μ (⋃ b∈U, G b) := measure_mono hsub
    _ ≤ ∑' b : U, μ (G b) := measure_biUnion_le μ hcount G
    _ ≤ ∑' b : U, η*μ (ball b (r b)) := ENNReal.tsum_le_tsum fun b => hlocal b (hUF b.property)
    _ = η*μ (⋃ b∈U, ball b (r b)) := by
      rw [ENNReal.tsum_mul_left,measure_biUnion hcount hdisj (fun _ _ => measurableSet_ball)]
    _ ≤ _ := by
      gcongr
      exact iUnion_subset fun hb => subset_iUnion_of_subset (hUF hb) Subset.rfl

lemma covering_contraction_of_distance {X : Type*} [MetricSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (F : Set X)
    (r s : X → ℝ) (R : ℝ) (η : ℝ≥0∞)
    (hr : ∀ x∈F, 0<r x ∧ r x≤R)
    (hlocal : ∀ b∈F,
      μ (⋃ a∈F, ⋃ (_ : dist a b<3*r b ∧ r a≤2*r b), ball a (s a)) ≤
        η*μ (ball b (r b))) :
    μ (⋃ a∈F, ball a (s a)) ≤ η*μ (⋃ a∈F, ball a (r a)) := by
  apply covering_contraction μ F r s R η hr
  intro b hb
  apply le_trans (measure_mono ?_) (hlocal b hb)
  intro x hx
  obtain ⟨a,ha,hx⟩ := mem_iUnion₂.mp hx
  obtain ⟨⟨hab,hrab⟩,hx⟩ := mem_iUnion.mp hx
  have hd := dist_lt_add_of_nonempty_ball_inter_ball hab
  exact mem_iUnion₂.mpr ⟨a,ha,mem_iUnion.mpr ⟨⟨by linarith,hrab⟩,hx⟩⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_RealScarcityCover
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma volume_preimage_rescale (L b : ℝ) (hL : 0 < L) (S : Set ℝ) :
    volume ((fun x => (x-b)*L) ⁻¹' S)=ENNReal.ofReal (1/L)*volume S := by
  have he : (fun x => (x-b)*L) ⁻¹' S =
      (fun x => x+(-b)) ⁻¹' ((fun x => L*x) ⁻¹' S) := by
    ext x
    simp only [mem_preimage]
    simp [sub_eq_add_neg,mul_comm]
  rw [he,measure_preimage_add_right,Real.volume_preimage_mul_left (ne_of_gt hL)]
  simp [abs_of_pos (inv_pos.mpr hL),one_div]
lemma CommonGood.matchedScale_pos {k q θ : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q θ jm jp) (hM : 1 < growthBase k) :
    0 < matchedScale k q θ jm jp := by
  obtain ⟨b,hm,hp⟩:=hg
  exact (abs_pos.mpr (hm.t_ne_zero hM)).trans_le (le_max_left _ _)

lemma local_group_scarcity (k q : ℝ) (jm jp : ℕ) (F : Set ℝ)
    (s : ℝ → ℝ) (η η' ε : ℝ)
    (hM : 1 < growthBase k) (hη : 0 ≤ η) (hε0 : 0 ≤ ε) (hε : ε/5 < η')
    (hg : ∀ a ∈ F, CommonGood k q a jm jp)
    (hsmall : ∀ a ∈ F, s a ≤ ε/(10*matchedScale k q a jm jp))
    (hscarce : ∀ b ∈ F,
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    ∀ b ∈ F,
      volume (⋃ a ∈ F, ⋃ (_ : dist a b < 3/(10*matchedScale k q b jm jp) ∧
        1/(10*matchedScale k q a jm jp) ≤ 2/(10*matchedScale k q b jm jp)), ball a (s a))  ≤
      ENNReal.ofReal (5*η)*volume (ball b (1/(10*matchedScale k q b jm jp))) := by
  intro b hb
  let L:=matchedScale k q b jm jp
  have hL : 0 < L := (hg b hb).matchedScale_pos hM
  let S := {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'}
  have hsub : (⋃ a ∈ F, ⋃ (_ : dist a b < 3/(10*L) ∧
      1/(10*matchedScale k q a jm jp) ≤ 2/(10*L)), ball a (s a))  ⊆
      (fun x => (x-b)*L) ⁻¹' S := by
    intro x hx
    obtain ⟨a,ha,hx⟩:=mem_iUnion₂.mp hx
    obtain ⟨⟨hd,hr⟩,hx⟩:=mem_iUnion.mp hx
    have hLa : 0 < matchedScale k q a jm jp := (hg a ha).matchedScale_pos hM
    have hs : s a < η'/L := by
      have hrad : s a ≤ ε*(2/(10*L)) := by
        calc
          _  ≤  ε/(10*matchedScale k q a jm jp) := hsmall a ha
          _ = ε*(1/(10*matchedScale k q a jm jp)) := by ring
          _  ≤  _ := mul_le_mul_of_nonneg_left hr hε0
      have hlt : ε*(2/(10*L)) < η'/L := by
        field_simp
        nlinarith
      exact hrad.trans_lt hlt
    refine ⟨(a-b)*L,?_,?_⟩
    · constructor
      · have hd' : |a-b| *L < 3/10 := by
          rw [Real.dist_eq] at hd
          have := (lt_div_iff₀ (by positivity : 0 < 10*L)).mp hd
          nlinarith
        have habs : |(a-b)*L| < 3/10 := by simpa only [abs_mul,abs_of_pos hL] using hd'
        exact abs_le.mp (habs.le.trans (by norm_num : (3/10:ℝ) ≤ 1))
      · have he : b+((a-b)*L)/matchedScale k q b jm jp=a := by
          dsimp [L] at hL
          field_simp
          ring
        rw [he]
        exact hg a ha
    · have hx' : |x-a| < η'/L := by
        have := mem_ball.mp hx
        rw [Real.dist_eq] at this
        exact this.trans hs
      rw [Real.dist_eq]
      have he : (x-b)*L-(a-b)*L=(x-a)*L := by ring
      rw [he,abs_mul,abs_of_pos hL]
      exact (lt_div_iff₀ hL).mp hx'
  calc
    _  ≤  volume ((fun x => (x-b)*L) ⁻¹' S) := measure_mono hsub
    _ = ENNReal.ofReal (1/L)*volume S := volume_preimage_rescale L b hL S
    _  ≤  ENNReal.ofReal (1/L)*ENNReal.ofReal η := by
      gcongr
      exact hscarce b hb
    _ = _ := by
      rw [Real.volume_ball,← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
      congr 1
      dsimp [L]
      ring
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PatternDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma CommonGood.scale_ge_one {k q a : ℝ} {jm jp : ℕ}
    (hg : CommonGood k q a jm jp) (hM : 1 < growthBase k) :
    1 ≤ matchedScale k q a jm jp := by
  obtain ⟨b,hm,hp⟩:=hg
  have hh:=hm.t_earlier hM 1 le_rfl (by have :=hm.1; omega)
  have ht : tSolution (orbitCoefficient k q a) 1=1 := linearSolution_one _ _ _
  rw [ht,abs_one,Nat.cast_one] at hh
  have hr : growthBase k ^ (-goodExponent*((jm:ℝ)-1)) ≤ 1 := by
    apply Real.rpow_le_one_of_one_le_of_nonpos hM.le
    have hj : (2:ℝ) ≤ jm := by exact_mod_cast hm.1
    nlinarith [goodExponent_pos]
  have hpos := abs_nonneg (tSolution (orbitCoefficient k q a) jm)
  exact (hh.trans (by nlinarith)).trans (le_max_left _ _)
lemma CommonGood.scale_mono_factor {k q a : ℝ} {jm jp lm lp : ℕ}
    (hg : CommonGood k q a jm jp) (hl : CommonGood k q a lm lp)
    (hmj : jm < lm) (hpj : jp < lp) (hM : 1 < growthBase k) :
    matchedScale k q a jm jp ≤ matchedScale k q a lm lp * growthBase k ^ (-goodExponent) := by
  obtain ⟨b,hm,hp⟩:=hg
  obtain ⟨d,hlm,hlp⟩:=hl
  have hbase := lt_trans zero_lt_one hM
  have hpow (j l : ℕ) (hjl : j < l) :
      growthBase k ^ (-goodExponent*((l:ℝ)-(j:ℝ))) ≤ growthBase k ^ (-goodExponent) := by
    apply Real.rpow_le_rpow_of_exponent_le hM.le
    have hh : (j:ℝ)+1 ≤ l := by exact_mod_cast hjl
    nlinarith [goodExponent_pos]
  apply max_le
  · calc
      _ ≤ |tSolution (orbitCoefficient k q a) lm| *growthBase k ^ (-goodExponent*((lm:ℝ)-(jm:ℝ))) :=
        hlm.t_earlier hM jm (by have :=hm.1; omega) hmj
      _ ≤ matchedScale k q a lm lp*growthBase k ^ (-goodExponent) := by
        exact mul_le_mul (le_max_left _ _) (hpow jm lm hmj) (Real.rpow_nonneg hbase.le _) ((abs_nonneg _).trans (le_max_left _ _))
  · calc
      _ ≤ |tSolution (orbitCoefficient k q (phi k q-a)) lp| *growthBase k ^ (-goodExponent*((lp:ℝ)-(jp:ℝ))) :=
        hlp.t_earlier hM jp (by have :=hp.1; omega) hpj
      _ ≤ matchedScale k q a lm lp*growthBase k ^ (-goodExponent) := by
        exact mul_le_mul (le_max_right _ _) (hpow jp lp hpj) (Real.rpow_nonneg hbase.le _) ((abs_nonneg _).trans (le_max_left _ _))

lemma pattern_decay (k q η η' : ℝ) (jm jp : ℕ → ℕ) (r : ℕ) (F : Set ℝ)
    (hr : 1 ≤ r) (hM : 1 < growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hF : F ⊆ Icc 0 1)
    (hgood : ∀ a ∈ F, ∀ i, i < r → CommonGood k q a (jm i) (jp i))
    (hmono : ∀ i, i+1 < r → jm i < jm (i+1) ∧ jp i < jp (i+1))
    (hscarce : ∀ i, i < r → ∀ b ∈ F,
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b (jm i) (jp i), dist x y < η'} ≤ ENNReal.ofReal η) :
    volume F ≤ ENNReal.ofReal (5*η)^(r-1)*3 := by
  let L := fun i a => matchedScale k q a (jm i) (jp i)
  let radius := fun i a => 1/(10*L i a)
  let V := fun i => ⋃ a ∈ F, ball a (radius i a)
  have hL (i : ℕ) (hi : i < r) (a : ℝ) (ha : a ∈ F) : 1 ≤ L i a :=
    (hgood a ha i hi).scale_ge_one hM
  have hrad (i : ℕ) (hi : i < r) (a : ℝ) (ha : a ∈ F) : 0 < radius i a ∧ radius i a ≤ 1/10 := by
    have hh:=hL i hi a ha
    dsimp [radius]
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 10*L i a)).mpr
      linarith
  have hVF (i : ℕ) (hi : i < r) : F ⊆ V i := by
    intro a ha
    exact mem_iUnion₂.mpr ⟨a,ha,mem_ball_self (hrad i hi a ha).1⟩
  have hstep (i : ℕ) (hi : i+1 < r) : volume (V (i+1)) ≤ ENNReal.ofReal (5*η)*volume (V i) := by
    apply covering_contraction_of_distance volume F (radius i) (radius (i+1)) (1/10)
      (ENNReal.ofReal (5*η)) (hrad i (by omega))
    have hrec (a : ℝ) (ha : a ∈ F) : radius (i+1) a ≤ growthBase k ^ (-goodExponent)/(10*L i a) := by
      have hh := (hgood a ha i (by omega)).scale_mono_factor (hgood a ha (i+1) hi)
        (hmono i hi).1 (hmono i hi).2 hM
      have hpos : 0 < L i a := lt_of_lt_of_le zero_lt_one (hL i (by omega) a ha)
      have hpos' : 0 < L (i+1) a := lt_of_lt_of_le zero_lt_one (hL (i+1) hi a ha)
      dsimp [radius]
      apply (div_le_div_iff₀ (by positivity : 0 < 10*L (i+1) a) (by positivity : 0 < 10*L i a)).mpr
      dsimp [L] at *
      nlinarith
    have hh:=local_group_scarcity k q (jm i) (jp i) F (radius (i+1)) η η'
      (growthBase k ^ (-goodExponent)) hM hη (Real.rpow_nonneg (by linarith : 0 ≤ growthBase k) _) hsmall
      (fun a ha => hgood a ha i (by omega)) hrec (hscarce i (by omega))
    simpa only [radius,L,mul_one_div] using hh
  have hV0 : volume (V 0) ≤ 3 := by
    calc
      _ ≤ volume (Ioo (-1:ℝ) 2) := measure_mono (by
        intro x hx
        obtain ⟨a,ha,hx⟩:=mem_iUnion₂.mp hx
        have hh:=mem_ball.mp hx
        rw [Real.dist_eq] at hh
        have ha':=hF ha
        change 0 ≤ a ∧ a ≤ 1 at ha'
        have hh':=abs_lt.mp (hh.trans_le (hrad 0 (by omega) a ha).2)
        exact ⟨by linarith,by linarith⟩)
      _ = 3 := by norm_num
  have hbound (i : ℕ) (hi : i < r) : volume (V i) ≤ ENNReal.ofReal (5*η)^i*3 := by
    induction i with
    | zero => simpa using hV0
    | succ i ih =>
      calc
        _ ≤ ENNReal.ofReal (5*η)*volume (V i) := hstep i hi
        _ ≤ ENNReal.ofReal (5*η)*(ENNReal.ofReal (5*η)^i*3) := by gcongr; exact ih (by omega)
        _ = _ := by rw [pow_succ]; ring
  exact (measure_mono (hVF (r-1) (by omega))).trans (hbound (r-1) (by omega))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_PatternCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma card_increasing_maps_le (N r : ℕ) : Fintype.card (Fin r ↪o Fin N) ≤ 2^N := by
  classical
  let image : (Fin r ↪o Fin N) → Finset (Fin N) := fun f => Finset.univ.image f
  have hi : Function.Injective image := by
    intro f g hfg
    apply DFunLike.ext
    intro i
    have hh : Set.range f=Set.range g := by
      have hc:=congrArg (fun S : Finset (Fin N) => (S:Set (Fin N))) hfg
      simpa [image] using hc
    exact congrFun ((f.strictMono.range_inj g.strictMono).mp hh) i
  have hh:=Fintype.card_le_of_injective image hi
  simpa using hh

lemma card_pair_patterns_le (N r : ℕ) :
    Fintype.card ((Fin r ↪o Fin N) × (Fin r ↪o Fin N)) ≤ 4^N := by
  have hh:=Nat.mul_le_mul (card_increasing_maps_le N r) (card_increasing_maps_le N r)
  rw [Fintype.card_prod]
  convert hh using 1
  rw [← mul_pow]
  norm_num
lemma finite_pattern_union_bound {ι : Type*} [Fintype ι]
    (F : ι → Set ℝ) (A : ℝ≥0∞) (N : ℕ)
    (hcard : Fintype.card ι ≤ N) (hF : ∀ i, volume (F i) ≤ A) :
    volume (⋃ i, F i) ≤ N*A := by
  classical
  calc
    _ ≤ ∑ i, volume (F i) := measure_iUnion_fintype_le _ _
    _ ≤ ∑ i : ι, A := Finset.sum_le_sum fun i hi => hF i
    _ = (Fintype.card ι : ℝ≥0∞)*A := by simp [nsmul_eq_mul]
    _ ≤ _ := by gcongr

lemma increasing_pattern_union_decay (k q η η' : ℝ) (N r : ℕ)
    (hr : 1 ≤ r) (hM : 1 < growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hscarce : ∀ jm jp b, CommonGood k q b jm jp → MatchedLogs k q b jm jp →
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin r ↪o Fin N),
      ∀ i : Fin r, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} ≤
      (4^N:ℝ≥0∞)*(ENNReal.ofReal (5*η)^(r-1)*3) := by
  classical
  let F := fun P : (Fin r ↪o Fin N) × (Fin r ↪o Fin N) =>
    {a : ℝ | a ∈ Icc 0 1 ∧ ∀ i : Fin r, CommonGood k q a (P.1 i) (P.2 i) ∧ MatchedLogs k q a (P.1 i) (P.2 i)}
  have hsub : {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin r ↪o Fin N),
      ∀ i : Fin r, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} ⊆ ⋃ P, F P := by
    rintro a ⟨ha,fm,fp,hp⟩
    exact mem_iUnion.mpr ⟨⟨fm,fp⟩,ha,hp⟩
  apply (measure_mono hsub).trans
  have hh:=finite_pattern_union_bound F (ENNReal.ofReal (5*η)^(r-1)*3) (4^N)
    (card_pair_patterns_le N r) ?_
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  intro P
  let fm : ℕ → ℕ := fun i => if h : i < r then (P.1 ⟨i,h⟩ : ℕ) else 0
  let fp : ℕ → ℕ := fun i => if h : i < r then (P.2 ⟨i,h⟩ : ℕ) else 0
  apply pattern_decay k q η η' fm fp r (F P) hr hM hη hsmall (fun a ha => ha.1)
  · intro a ha i hi
    simpa only [fm,fp,dite_eq_left hi] using (ha.2 ⟨i,hi⟩).1
  · intro i hi
    have hi' : i < r := by omega
    simp only [fm,fp,dite_eq_left hi,dite_eq_left hi']
    change ((P.1 ⟨i,hi'⟩ : ℕ) < (P.1 ⟨i+1,hi⟩ : ℕ)) ∧
      ((P.2 ⟨i,hi'⟩ : ℕ) < (P.2 ⟨i+1,hi⟩ : ℕ))
    exact
      And.intro (P.1.strictMono (show (⟨i,hi'⟩:Fin r) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self i))
        (P.2.strictMono (show (⟨i,hi'⟩:Fin r) < ⟨i+1,hi⟩ by exact Nat.lt_succ_self i))
  · intro i hi b hb
    simpa only [fm,fp,dite_eq_left hi] using hscarce (P.1 ⟨i,hi⟩) (P.2 ⟨i,hi⟩) b
      (hb.2 ⟨i,hi⟩).1 (hb.2 ⟨i,hi⟩).2
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_SliceCancellation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma ordered_subpattern (T : Finset ℕ) (f : ℕ → ℕ) (N r : ℕ) (P : ℕ → ℕ → Prop)
    (hr : r ≤ T.card) (hb : ∀ j ∈ T, j < N ∧ f j < N ∧ P j (f j))
    (hord : ∀ i ∈ T, ∀ j ∈ T, i < j → f i < f j) :
    ∃ (e₁ e₂ : Fin r ↪o Fin N), ∀ i, P (e₁ i) (e₂ i) := by
  classical
  let g : Fin r → ℕ := fun i => T.orderEmbOfFin rfl (Fin.castLE hr i)
  have hgmem (i : Fin r) : g i ∈ T := T.orderEmbOfFin_mem rfl _
  have hgmono : StrictMono g := fun i j hij => (T.orderEmbOfFin rfl).strictMono hij
  let e₁ : Fin r → Fin N := fun i => ⟨g i,(hb _ (hgmem i)).1⟩
  let e₂ : Fin r → Fin N := fun i => ⟨f (g i),(hb _ (hgmem i)).2.1⟩
  have hm₁ : StrictMono e₁ := fun i j hij => hgmono hij
  have hm₂ : StrictMono e₂ := fun i j hij => hord _ (hgmem i) _ (hgmem j) (hgmono hij)
  exact ⟨OrderEmbedding.ofStrictMono e₁ hm₁,OrderEmbedding.ofStrictMono e₂ hm₂,
    fun i => (hb _ (hgmem i)).2.2⟩

lemma small_endpoints_pattern (k q a : ℝ) (n Np Nm : ℕ)
    (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1) (hNm : n ≤ Nm ∧ Nm ≤ n+1)
    (hk : 0 ≤ k) (hM : 6 ≤ growthBase k)
    (hb : ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) :
    ∃ (fm fp : Fin (n/100) ↪o Fin (n+2)), ∀ i,
      CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i) := by
  obtain ⟨b,hm,hp⟩:=hb
  obtain ⟨T,f,hcard,hT,hord⟩:=matching_small_endpoints (growthBase k)
    (orbitCoefficient k q a) (orbitCoefficient k q (phi k q-a)) b (potential k q-b)
    n Nm Np hn hNm hNp hM
    (fun j _ _ => potential_bound k _ hk)
    (fun j _ _ => potential_bound k _ hk) hm hp
  apply ordered_subpattern T f (n+2) (n/100)
    (fun jm jp => CommonGood k q a jm jp ∧ MatchedLogs k q a jm jp) hcard ?_ hord
  intro j hj
  have hh:=hT j hj
  refine ⟨by omega,by omega,⟨⟨b,hh.2.2.1,hh.2.2.2.2.2.1⟩,?_⟩⟩
  dsimp [MatchedLogs]
  linarith [hh.2.2.2.2.2.2]

lemma small_endpoints_slice_bound (k q η η' : ℝ) (n Np Nm : ℕ)
    (hn : 10000000 ≤ n) (hNp : n ≤ Np ∧ Np ≤ n+1) (hNm : n ≤ Nm ∧ Nm ≤ n+1)
    (hk : 0 ≤ k) (hM : 6 ≤ growthBase k) (hη : 0 ≤ η)
    (hsmall : growthBase k ^ (-goodExponent)/5 < η')
    (hscarce : ∀ jm jp b, CommonGood k q b jm jp → MatchedLogs k q b jm jp →
      volume {x : ℝ | ∃ y ∈ localSuccessfulSet k q b jm jp, dist x y < η'} ≤ ENNReal.ofReal η) :
    volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
        3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤
      (4^(n+2):ℝ≥0∞)*(ENNReal.ofReal (5*η)^(n/100-1)*3) := by
  apply (measure_mono (show _ ⊆ {a : ℝ | a ∈ Icc 0 1 ∧ ∃ (fm fp : Fin (n/100) ↪o Fin (n+2)),
      ∀ i, CommonGood k q a (fm i) (fp i) ∧ MatchedLogs k q a (fm i) (fp i)} from ?_)).trans
  · exact increasing_pattern_union_decay k q η η' (n+2) (n/100) (by omega) (by linarith) hη hsmall hscarce
  · rintro a ⟨ha,hb⟩
    exact ⟨ha,small_endpoints_pattern k q a n Np Nm hn hNp hNm hk hM hb⟩
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationScalar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pattern_power_bound (n : ℕ) (hn : 1000 ≤ n) :
    (4:ℝ)^(n+2)*(((1/4:ℝ)^400)^(n/100-1)*3) ≤ (1/4:ℝ)^n := by
  have hexp : 2*n+4 ≤ 400*(n/100-1) := by omega
  rw [← pow_mul]
  calc
    _ ≤ (4:ℝ)^(n+2)*((1/4:ℝ)^(2*n+4)*3) := by
      apply mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ (by norm_num)) (by positivity)
      exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hexp
    _ = (1/4:ℝ)^n*(3/16) := by
      have he : 2*n+4= n+(n+4) := by omega
      rw [he,pow_add,pow_add,pow_add]
      simp only [one_div_pow]
      field_simp
      ; ring
    _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 1/4) n]
lemma pattern_ennreal_bound (n : ℕ) (hn : 1000 ≤ n) :
    (4^(n+2):ℝ≥0∞)*(ENNReal.ofReal ((1/4:ℝ)^400)^(n/100-1)*3) ≤
      ENNReal.ofReal ((1/4:ℝ)^n) := by
  have hh := ENNReal.ofReal_le_ofReal (pattern_power_bound n hn)
  simpa only [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4^(n+2)),
    ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ ((1/4:ℝ)^400)^(n/100-1)),
    ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 4),
    ENNReal.ofReal_pow (by positivity : (0:ℝ) ≤ (1/4:ℝ)^400),ENNReal.ofReal_ofNat] using hh

theorem eventually_small_endpoints_slice :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ q : ℝ, ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
        pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) ∧
        pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤
          3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  let η : ℝ := (1/4:ℝ)^400/5
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨η',hη',Mη,hscarce⟩:=local_scarcity η hη
  have hlim : Tendsto (fun M : ℝ => M^(-goodExponent)/5) atTop (nhds 0) := by
    simpa using (tendsto_rpow_neg_atTop goodExponent_pos).div_const 5
  obtain ⟨MM,hMM⟩:=eventually_atTop.mp (hlim.eventually (gt_mem_nhds hη'))
  refine ⟨max 6 (max Mη MM),?_⟩
  intro k hk hM q n Np Nm hn hNp hNm
  have hm6 : 6 ≤ growthBase k := (le_max_left _ _).trans hM
  have hmη : Mη ≤ growthBase k := (le_max_left _ _).trans ((le_max_right _ _).trans hM)
  have hmmm : MM ≤ growthBase k := (le_max_right _ _).trans ((le_max_right _ _).trans hM)
  have hs :=small_endpoints_slice_bound k q η η' n Np Nm hn hNp hNm hk.le hm6 hη.le
    (hMM _ hmmm) (fun jm jp b hgood hmatch => hscarce k hk hmη q b jm jp hgood hmatch)
  have he : 5*η=(1/4:ℝ)^400 := by dsimp only [η]; exact mul_div_cancel₀ _ (by norm_num : (5:ℝ) ≠ 0)
  rw [he] at hs
  exact hs.trans (pattern_ennreal_bound n (by omega))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationVector
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma torus_reverse_operator (k : ℝ) (z : Torus) (n : ℕ) :
    (planeSwap.comp (torusSegmentTransfer k z.swap 0 n)).comp planeSwap=
      transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n := by
  ext u
  apply (show Function.Injective (torusSegmentTransfer k z (-(n:ℤ)) n) from fun x y hxy => by
    have := congrArg (transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n) hxy
    simpa only [torusSegmentTransfer,transferProductInv_inverse] using this)
  exact (torusSegmentTransfer_reverse_identity k z n u).trans (transferProduct_inverse _ _ _).symm
lemma small_vector_of_cancellation (M : ℝ) (hM : 1 < M) (δ : ℝ) (hδ : 0 ≤ δ)
    (A B : ℂ →L[ℝ] ℂ) (hA : PlaneAreaPreserving A) (n : ℕ)
    (ha : M^((1-δ)*(n:ℝ)) ≤ ‖A‖) (hab : ‖B‖ ≤ M^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧ ‖A u‖ ≤ M^(-((1-2*δ)*(n:ℝ))) ∧
      ‖B (A u)‖ ≤ M^(-((1-2*δ)*(n:ℝ))) := by
  obtain ⟨a,ha1,_,_,hsmall,hAn⟩ := hA.singular_pair
  have hMp : 0 < M := by linarith
  have hneg : ‖A (quarterTurn a)‖ ≤ M^(-((1-δ)*(n:ℝ))) := by
    rw [hsmall,Real.rpow_neg hMp.le]
    exact (inv_le_inv₀ (by linarith : 0 < ‖A‖) (Real.rpow_pos_of_pos hMp _)).mpr ha
  refine ⟨quarterTurn a,by simpa [norm_quarterTurn] using ha1,?_,?_⟩
  · exact hneg.trans (Real.rpow_le_rpow_of_exponent_le hM.le (by nlinarith [Nat.cast_nonneg (α:=ℝ) n]))
  · calc
      _ ≤ ‖B‖*‖A (quarterTurn a)‖ := B.le_opNorm _
      _ ≤ M^(δ*(n:ℝ))*M^(-((1-δ)*(n:ℝ))) := mul_le_mul hab hneg (norm_nonneg _) (Real.rpow_nonneg hMp.le _)
      _ = _ := by rw [← Real.rpow_add hMp]; congr 1; ring
lemma torus_cancellation_vector (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (z : Torus)
    (hback : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖torusSegmentTransfer k z (-(n:ℤ)) n‖)
    (hfull : ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖ ≤ growthBase k^(δ*(n:ℝ))) :
    ∃ u : ℂ, ‖u‖=1 ∧
      ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) ∧
      ‖torusSegmentTransfer k z 0 n u‖ ≤ growthBase k^(-((1-2*δ)*(n:ℝ))) := by
  let A := transferProductInv (torusSegmentCoefficient k z (-(n:ℤ))) n
  let B := torusSegmentTransfer k z (-(n:ℤ)) (n+n)
  have hM : 1 < growthBase k := by linarith [growthBase_ge_four k hk]
  have ha : growthBase k^((1-δ)*(n:ℝ)) ≤ ‖A‖ := by
    dsimp only [A]
    rw [← transferProduct_norm_inverse]
    exact hback
  obtain ⟨u,hu,hum,hup⟩ := small_vector_of_cancellation (growthBase k) hM δ hδ A B
    (transferProductInv_area _ _) n ha hfull
  refine ⟨u,hu,?_,?_⟩
  · dsimp only [A] at hum
    rw [← torus_reverse_operator,ContinuousLinearMap.comp_apply,ContinuousLinearMap.comp_apply,norm_planeSwap] at hum
    exact hum
  · have he : B (A u)=torusSegmentTransfer k z 0 n u := by
      dsimp only [A,B]
      rw [torusSegmentTransfer_concat,neg_add_cancel,ContinuousLinearMap.comp_apply]
      simp only [torusSegmentTransfer,transferProduct_inverse]
    rwa [he] at hup
lemma torusSegmentTransfer_first (k : ℝ) (z : Torus) (n : ℕ) :
    torusSegmentTransfer k z 0 (n+1)=
      (torusSegmentTransfer k (torusStep k z) 0 n).comp (transferStep (torusPotential k z.1)) := by
  rw [show n+1=1+n by omega,torusSegmentTransfer_concat]
  change (torusSegmentTransfer k z 1 n).comp (torusSegmentTransfer k z 0 1)=_
  have hs : torusSegmentTransfer k (torusStep k z) 0 n=torusSegmentTransfer k z 1 n := by
    exact torusSegmentTransfer_shift k z 0 1 n
  rw [hs]
  simp only [torusSegmentTransfer,transferProduct,torusSegmentCoefficient,zero_add,Nat.cast_one,
    sub_self,torusIter_zero,ContinuousLinearMap.comp_id]
lemma torusStep_swap_prev (k : ℝ) (z : Torus) :
    torusStep k z.swap=((torusStep k).symm z).swap := rfl
lemma torusPotential_bound (k : ℝ) (hk : 0 ≤ k) (x : Circle) : |torusPotential k x|+1 ≤ growthBase k := by
  obtain ⟨t,rfl⟩ := Quotient.mk_surjective x
  exact potential_bound k t hk
lemma max_unit_coordinate (u : ℂ) (hu : ‖u‖=1) : 1/2 ≤ max |u.re| |u.im| := by
  have hs : u.re^2+u.im^2=1 := by simpa only [Complex.sq_norm,Complex.normSq_apply,hu,one_pow,pow_two,one_mul] using (Complex.sq_norm u).symm
  by_contra h
  have hr : |u.re| < 1/2 := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge h)
  have hi : |u.im| < 1/2 := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge h)
  nlinarith [sq_abs u.re,sq_abs u.im,abs_nonneg u.re,abs_nonneg u.im]
lemma normalized_endpoint_norm (A : ℂ →L[ℝ] ℂ) (u : ℂ) (a R : ℝ)
    (ha : 1/2 ≤ |a|) (hR : 0 ≤ R) (h : ‖A u‖ ≤ R) : ‖A (a⁻¹ • u)‖ ≤ 2*R := by
  rw [map_smul,norm_smul,Real.norm_eq_abs,abs_inv]
  have hap : 0 < |a| := by linarith
  have hai : |a|⁻¹ ≤ 2 := (inv_le_iff_one_le_mul₀ hap).mpr (by linarith)
  exact (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (abs_nonneg a))).trans
    (mul_le_mul_of_nonneg_right hai hR)
lemma torus_small_normalize (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 1 ≤ n) (R : ℝ) (hR : 0 ≤ R)
    (z : Torus) (u : ℂ) (hu : ‖u‖=1)
    (hm : ‖torusSegmentTransfer k z.swap 0 n (planeSwap u)‖ ≤ R)
    (hp : ‖torusSegmentTransfer k z 0 n u‖ ≤ R) :
    torusSmallEndpoints k n (n+1) (2*R) z ∨
      torusSmallEndpoints k (n+1) n (2*R) ((torusStep k).symm z) := by
  have hM : 1 ≤ growthBase k := by linarith [growthBase_ge_four k hk]
  have hcoord := max_unit_coordinate u hu
  by_cases hdom : |u.im| ≤ |u.re|
  · left
    have hure : 1/2 ≤ |u.re| := by simpa only [max_eq_left hdom] using hcoord
    have hur0 : u.re ≠ 0 := by intro hh; simp [hh] at hure; norm_num at hure
    have hb : |u.im/u.re| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.re|)).mpr hdom
    refine ⟨u.im/u.re,⟨?_,?_⟩,?_,?_⟩
    · linarith [(abs_le.mp hb).1]
    · linarith [(abs_le.mp hb).2]
    · have he : (u.re⁻¹ : ℝ) • planeSwap u=⟨u.im/u.re,1⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [Nat.add_sub_cancel,he] using normalized_endpoint_norm
        (torusSegmentTransfer k z.swap 0 n) (planeSwap u) u.re R hure hR hm
    · have he : (u.re⁻¹ : ℝ) • u=⟨1,u.im/u.re⟩ := by
        apply Complex.ext <;> simp [div_eq_mul_inv,hur0,mul_comm]
      simpa only [he] using normalized_endpoint_norm (torusSegmentTransfer k z 0 n) u u.re R hure hR hp
  · right
    have himdom : |u.re| ≤ |u.im| := le_of_lt (lt_of_not_ge hdom)
    have him : 1/2 ≤ |u.im| := by simpa only [max_eq_right himdom] using hcoord
    have hi0 : u.im ≠ 0 := by intro hh; simp [hh] at him; norm_num at him
    let p := torusPotential k z.2
    let w := transferStepInv p u
    have hwp : torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1) w=torusSegmentTransfer k z 0 n u := by
      rw [torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,Equiv.apply_symm_apply]
      change torusSegmentTransfer k z 0 n (transferStep p (transferStepInv p u))=_
      rw [transferStep_inv]
    have hwm : torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1) (planeSwap w)=
        torusSegmentTransfer k z.swap 0 n (planeSwap u) := by
      conv_rhs => rw [← Nat.sub_add_cancel hn,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,torusStep_swap_prev]
      congr 1
    have hwre : w.re=u.im := rfl
    have hbr : |w.im/u.im| ≤ growthBase k := by
      have hd : |u.re/u.im| ≤ 1 := by rw [abs_div]; exact (div_le_one (by linarith : 0 < |u.im|)).mpr himdom
      have he : w.im/u.im=p-u.re/u.im := by change (p*u.im-u.re)/u.im=_; field_simp
      rw [he]
      exact (abs_sub _ _).trans ((add_le_add_right hd _).trans (torusPotential_bound k hk z.2))
    refine ⟨w.im/u.im,⟨(abs_le.mp hbr).1,(abs_le.mp hbr).2⟩,?_,?_⟩
    · have he : (u.im⁻¹ : ℝ) • planeSwap w=⟨w.im/u.im,1⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k (((torusStep k).symm z).swap) 0 (n-1))
        (planeSwap w) u.im R him hR (by rw [hwm]; exact hm)
      simpa only [he] using hb
    · have he : (u.im⁻¹ : ℝ) • w=⟨1,w.im/u.im⟩ := by
        apply Complex.ext <;> simp [hwre,div_eq_mul_inv,hi0,mul_comm]
      have hb := normalized_endpoint_norm (torusSegmentTransfer k ((torusStep k).symm z) 0 (n+1))
        w u.im R him hR (by rw [hwp]; exact hp)
      simpa only [he] using hb
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationArea
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma continuous_complex_mk {α : Type*} [TopologicalSpace α] (f g : α → ℝ)
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun x => (⟨f x,g x⟩:ℂ)) :=
  Complex.equivRealProdCLM.symm.continuous.comp (hf.prodMk hg)
lemma isClosed_torusSmallEndpoints (k : ℝ) (Np Nm : ℕ) (R : ℝ) :
    IsClosed {z : Torus | torusSmallEndpoints k Np Nm R z} := by
  let S : Set (Torus × ℝ) := {p | p.2 ∈ Icc (-growthBase k) (growthBase k) ∧
    ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖ ≤ R ∧
    ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖ ≤ R}
  have h1 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1.swap 0 (Nm-1) ⟨p.2,1⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 (Nm-1)).comp (continuous_swap.comp continuous_fst)).clm_apply
      (continuous_complex_mk _ _ continuous_snd continuous_const)).norm
  have h2 : Continuous (fun p : Torus × ℝ =>
      ‖torusSegmentTransfer k p.1 0 Np ⟨1,p.2⟩‖) := by
    exact (((continuous_torusSegmentTransfer k 0 Np).comp continuous_fst).clm_apply
      (continuous_complex_mk _ _ continuous_const continuous_snd)).norm
  have hS : IsCompact S := by
    have hc := (isCompact_univ : IsCompact (univ : Set Torus)).prod
      (isCompact_Icc : IsCompact (Icc (-growthBase k) (growthBase k)))
    convert hc.inter_right ((isClosed_le h1 (continuous_const (y:=R))).inter (isClosed_le h2 (continuous_const (y:=R)))) using 1
    ext p
    simp only [S,mem_inter_iff,mem_prod,mem_univ,true_and,mem_ofPred_eq]
  have he : {z : Torus | torusSmallEndpoints k Np Nm R z}=Prod.fst '' S := by
    ext z
    constructor
    · rintro ⟨b,hb,hm,hp⟩
      exact ⟨(z,b),⟨hb,hm,hp⟩,rfl⟩
    · rintro ⟨⟨w,b⟩,hs,hw⟩
      subst z
      exact ⟨b,hs⟩
  rw [he]
  exact (hS.image continuous_fst).isClosed
lemma scalar_pairMagnitude_le_norm (v : ℕ → ℝ) (b : ℝ) (N : ℕ) (hN : 1 ≤ N) :
    pairMagnitude (linearSolution v 1 b) N ≤ ‖transferProduct v (N-1) ⟨b,1⟩‖ := by
  rw [transferProduct_pair,Nat.sub_add_cancel hN]
  exact max_le (Complex.abs_re_le_norm ⟨_,_⟩) (Complex.abs_im_le_norm ⟨_,_⟩)
lemma torusSmallEndpoints_lift_sub (k q a R : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (h : torusSmallEndpoints k Np Nm R (liftProjection (q,a))) :
    ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R := by
  obtain ⟨b,_,hm,hp⟩ := h
  refine ⟨b,?_,?_⟩
  · have he : torusSegmentTransfer k (liftProjection (q,a)).swap 0 (Nm-1)=
        transferProduct (orbitCoefficient k q a) (Nm-1) := by
      change torusSegmentTransfer k (liftProjection (a,q)) 0 (Nm-1)=_
      rw [torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
    rw [he] at hm
    exact (scalar_pairMagnitude_le_norm _ b Nm hNm).trans hm
  · have he : torusSegmentTransfer k (liftProjection (q,a)) 0 Np ⟨1,b⟩=
        transferProduct (orbitCoefficient k q (phi k q-a)) (Np-1) ⟨potential k q-b,1⟩ := by
      conv_lhs => rw [← Nat.sub_add_cancel hNp,torusSegmentTransfer_first,ContinuousLinearMap.comp_apply,
        ← liftProjection_step,torusSegmentTransfer_lift,liftSegmentTransfer_eq,liftIter_zero]
      simp only [liftStep_apply]
      congr 1
      apply Complex.ext <;> simp [liftProjection,torusPotential_coe]
    rw [he] at hp
    exact (scalar_pairMagnitude_le_norm _ _ Np hNp).trans hp
lemma area_small_endpoints_of_slices (k : ℝ) (Np Nm : ℕ) (hNp : 1 ≤ Np) (hNm : 1 ≤ Nm)
    (R : ℝ) (K : ℝ≥0∞)
    (hs : ∀ q : ℝ, volume {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
      pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
      pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} ≤ K) :
    area {z | torusSmallEndpoints k Np Nm R z} ≤ K := by
  let E := {z | torusSmallEndpoints k Np Nm R z}
  have hE : MeasurableSet E := (isClosed_torusSmallEndpoints k Np Nm R).measurableSet
  have hproj : Measurable liftProjection :=
    (((AddCircle.continuous_mk' (1:ℝ)).comp continuous_fst).prodMk
      ((AddCircle.continuous_mk' (1:ℝ)).comp continuous_snd)).measurable
  have hmp := (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ)).prod
    (AddCircle.measurePreserving_mk (1:ℝ) (0:ℝ))
  have hm : ((volume.restrict (Ioc (0:ℝ) 1)).prod (volume.restrict (Ioc (0:ℝ) 1)))
      (liftProjection ⁻¹' E)=area E := by
    convert! hmp.measure_preimage hE.nullMeasurableSet using 1
    simp only [zero_add]; rfl
  rw [← hm,Measure.prod_apply (hE.preimage hproj)]
  calc
    _ ≤ ∫⁻ _q : ℝ, K ∂(volume.restrict (Ioc (0:ℝ) 1)) := by
      apply lintegral_mono
      intro q
      change (volume.restrict (Ioc (0:ℝ) 1)) (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ≤ K
      have hmsec : MeasurableSet (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) := by
        exact (hE.preimage hproj).preimage (measurable_const.prodMk measurable_id)
      rw [Measure.restrict_apply hmsec]
      apply (measure_mono (show (Prod.mk q ⁻¹' (liftProjection ⁻¹' E)) ∩ Ioc 0 1 ⊆
          {a : ℝ | a ∈ Icc 0 1 ∧ ∃ b : ℝ,
            pairMagnitude (linearSolution (orbitCoefficient k q a) 1 b) Nm ≤ R ∧
            pairMagnitude (linearSolution (orbitCoefficient k q (phi k q-a)) 1 (potential k q-b)) Np ≤ R} from ?_)).trans (hs q)
      intro a ha
      exact ⟨⟨ha.2.1.le,ha.2.2⟩,torusSmallEndpoints_lift_sub k q a R Np Nm hNp hNm ha.1⟩
    _ = K := by simp
lemma eventually_small_endpoints_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0 < k → M₀ ≤ growthBase k →
      ∀ n Np Nm : ℕ, 10000000 ≤ n → n ≤ Np ∧ Np ≤ n+1 → n ≤ Nm ∧ Nm ≤ n+1 →
      area {z | torusSmallEndpoints k Np Nm
        (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ≤ ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_slice
  refine ⟨M₀,?_⟩
  intro k hk hMk n Np Nm hn hNp hNm
  exact area_small_endpoints_of_slices k Np Nm (by omega) (by omega) _ _
    (fun q => hM k hk hMk q n Np Nm hn hNp hNm)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CancellationTheorem
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma isClosed_torusCancellation (k : ℝ) (n : ℕ) : IsClosed {z | torusCancellation k n z} :=
  (isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
    ((isClosed_le continuous_const (continuous_torusSegmentTransfer k _ _).norm).inter
      (isClosed_le (continuous_torusSegmentTransfer k _ _).norm continuous_const))
lemma torusSmallEndpoints_mono (k : ℝ) (Np Nm : ℕ) {R S : ℝ} (hRS : R≤S) (z : Torus)
    (h : torusSmallEndpoints k Np Nm R z) : torusSmallEndpoints k Np Nm S z := by
  obtain ⟨b,hb,hm,hp⟩ := h
  exact ⟨b,hb,hm.trans hRS,hp.trans hRS⟩
lemma torusCancellation_sub_small (k : ℝ) (hk : 0≤k) (n : ℕ) (hn : 1≤n) :
    {z | torusCancellation k n z} ⊆
      {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} ∪
      ((torusStep k).symm ⁻¹' {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z}) := by
  intro z hz
  obtain ⟨u,hu,hm,hp⟩ := torus_cancellation_vector k hk n (1/100000000) (by norm_num) z hz.1 hz.2.2
  have hM : 1≤growthBase k := by linarith [growthBase_ge_four k hk]
  have hR : 0≤growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) := Real.rpow_nonneg (by linarith) _
  have hRS : 2*growthBase k^(-((1-2*(1/100000000:ℝ))*(n:ℝ))) ≤
      3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ))) := by
    have hh := Real.rpow_le_rpow_of_exponent_le hM
      (show -((1-2*(1/100000000:ℝ))*(n:ℝ)) ≤ -((1-3/100000000:ℝ)*(n:ℝ)) by
        nlinarith [Nat.cast_nonneg (α:=ℝ) n])
    nlinarith [Real.rpow_nonneg (show 0≤growthBase k by linarith) (-((1-3/100000000:ℝ)*(n:ℝ)))]
  rcases torus_small_normalize k hk n hn _ hR z u hu hm hp with h|h
  · exact Or.inl (torusSmallEndpoints_mono _ _ _ hRS _ h)
  · exact Or.inr (torusSmallEndpoints_mono _ _ _ hRS _ h)
lemma eventually_cancellation_area_large :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ, 10000000≤n →
      area {z | torusCancellation k n z} ≤ 2*ENNReal.ofReal ((1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_small_endpoints_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  have hp := hM k hk hMk n n (n+1) hn ⟨le_rfl,by omega⟩ ⟨by omega,le_rfl⟩
  have hm := hM k hk hMk n (n+1) n hn ⟨by omega,le_rfl⟩ ⟨le_rfl,by omega⟩
  have hmp : MeasurePreserving (torusStep k).symm area area := measurePreserving_torusStep_symm k
  calc
    _ ≤ _ := measure_mono (torusCancellation_sub_small k hk.le n (by omega))
    _ ≤ _ := measure_union_le _ _
    _ = area {z | torusSmallEndpoints k n (n+1) (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} +
        area {z | torusSmallEndpoints k (n+1) n (3*growthBase k^(-((1-3/100000000:ℝ)*(n:ℝ)))) z} := by
      rw [hmp.measure_preimage (isClosed_torusSmallEndpoints _ _ _ _).measurableSet.nullMeasurableSet]
    _ ≤ _ := by rw [two_mul]; exact add_le_add hp hm
lemma cancellationConstant_pos : 0<cancellationConstant := by unfold cancellationConstant; positivity
lemma eventually_cancellation_area :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀≤growthBase k → ∀ n : ℕ,
      area {z | torusCancellation k n z} ≤ ENNReal.ofReal (cancellationConstant*(1/4:ℝ)^n) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area_large
  refine ⟨M₀,?_⟩
  intro k hk hMk n
  by_cases hn : 10000000≤n
  · apply (hM k hk hMk n hn).trans
    have hc : 2≤cancellationConstant := by
      have hp : (1:ℝ)≤4^10000000 := one_le_pow₀ (by norm_num)
      simpa only [mul_one,cancellationConstant] using mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤2)
    rw [ENNReal.ofReal_mul cancellationConstant_pos.le]
    exact mul_le_mul_of_nonneg_right (by simpa using ENNReal.ofReal_le_ofReal hc) bot_le
  · have hprob : area {z | torusCancellation k n z}≤1 := by
      calc
        _≤area univ := measure_mono (subset_univ _)
        _=1 := measure_univ
    apply hprob.trans
    have he : (4:ℝ)^n*(1/4:ℝ)^n=1 := by rw [← mul_pow]; norm_num
    have hp := pow_le_pow_right₀ (show (1:ℝ)≤4 by norm_num) (show n≤10000000 by omega)
    have hc : 1≤cancellationConstant*(1/4:ℝ)^n := by
      have hh := mul_le_mul_of_nonneg_right hp (show 0≤(1/4:ℝ)^n by positivity)
      rw [he] at hh
      have h2 := mul_le_mul_of_nonneg_right (show (1:ℝ)≤2 by norm_num)
        (show 0≤(4:ℝ)^10000000*(1/4:ℝ)^n by positivity)
      simpa only [one_mul,cancellationConstant,mul_assoc] using hh.trans (by simpa only [one_mul] using h2)
    simpa using ENNReal.ofReal_le_ofReal hc
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_DoublingPointwise
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma wingDefect_nonneg (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) : 0 ≤ wingDefect k z n := by
  have hh := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast] at hh
  have hm := min_le_right (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ))
  unfold wingDefect; linarith
lemma cancellationLoss_bounds (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    0 ≤ cancellationLoss k z n ∧ cancellationLoss k z n ≤ 2*(n:ℝ) := by
  have htri := productDistance_triangle k hk z (-(n:ℤ)) 0 (n:ℤ)
  rw [productDistance_symm k z (-(n:ℤ)) 0] at htri
  have hL := productDistance_le k hk z 0 (-(n:ℤ))
  have hR := productDistance_le k hk z 0 (n:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hL hR
  have hn := productDistance_nonneg k hk z (-(n:ℤ)) (n:ℤ)
  unfold cancellationLoss
  constructor  <;> linarith
lemma torusCancellation_iff_distance (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    torusCancellation k n z ↔
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (-(n:ℤ)) ∧
      (1-1/100000000:ℝ)*(n:ℝ) ≤ productDistance k z 0 (n:ℤ) ∧
      productDistance k z (-(n:ℤ)) (n:ℤ) ≤ (1/100000000:ℝ)*(n:ℝ) := by
  have hM : 0 < growthBase k := lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (growthBase_ge_four k hk)
  have hp a m : 0 < ‖torusSegmentTransfer k z a m‖ := lt_of_lt_of_le zero_lt_one (torusSegmentTransfer_norm_bounds k hk z a m).1
  rw [productDistance_symm k z 0 (-(n:ℤ))]
  have h1 : productDistance k z (-(n:ℤ)) 0=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) n‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) n using 1  ; simp
  have h2 : productDistance k z 0 (n:ℤ)=Real.log ‖torusSegmentTransfer k z 0 n‖/Real.log (growthBase k) := by
    simpa using productDistance_forward k z 0 n
  have h3 : productDistance k z (-(n:ℤ)) (n:ℤ)=Real.log ‖torusSegmentTransfer k z (-(n:ℤ)) (n+n)‖/Real.log (growthBase k) := by
    convert productDistance_forward k z (-(n:ℤ)) (n+n) using 1  ; push_cast  ; ring_nf
  rw [h1,h2,h3]
  simp only [torusCancellation,Real.rpow_le_iff_le_log hM (hp _ _),Real.le_rpow_iff_log_le (hp _ _) hM,
    le_div_iff₀ (log_growthBase_pos k hk),div_le_iff₀ (log_growthBase_pos k hk)]
lemma large_loss_implies_cancellation (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ)
    (hl : 10000000000*(1+wingDefect k z n) < cancellationLoss k z n) :
    let s := ⌊cancellationLoss k z n/2⌋₊
    1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z := by
  let s := ⌊cancellationLoss k z n/2⌋₊
  change 1  ≤  s ∧ s  ≤  n ∧ cancellationLoss k z n < 2*(s:ℝ)+2 ∧ torusCancellation k s z
  have hD := wingDefect_nonneg k hk z n
  obtain ⟨hl0,hln⟩ := cancellationLoss_bounds k hk z n
  have hfloor : (s:ℝ) ≤ cancellationLoss k z n/2 := Nat.floor_le (by linarith)
  have hfloor' : cancellationLoss k z n/2 < (s:ℝ)+1 := Nat.lt_floor_add_one _
  have hs1 : 1  ≤  s := by
    have hs : (1:ℝ) ≤ s := by linarith
    exact_mod_cast hs
  have hsn : s  ≤  n := by
    have hs : (s:ℝ) ≤ n := by linarith
    exact_mod_cast hs
  have hsmall : 2*wingDefect k z n+6 ≤ (1/100000000:ℝ)*(s:ℝ) := by linarith
  refine ⟨hs1,hsn,by linarith,?_⟩
  rw [torusCancellation_iff_distance k hk z s]
  obtain ⟨hL,hR⟩ := productDistance_cut_wings k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hL hR
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (-(s:ℤ)) at hL
  change (s:ℝ)-wingDefect k z n ≤ productDistance k z 0 (s:ℤ) at hR
  have hcut := productDistance_truncation k hk z 0 n s hsn
  simp only [zero_sub,zero_add] at hcut
  change min (cancellationLoss k z n) (2*(s:ℝ)-2*wingDefect k z n)-6 ≤ cancellationLoss k z s at hcut
  rw [min_eq_right (by linarith)] at hcut
  have hLs := productDistance_le k hk z 0 (-(s:ℤ))
  have hRs := productDistance_le k hk z 0 (s:ℤ)
  simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hLs hRs
  unfold cancellationLoss at hcut
  exact ⟨by linarith,by linarith,by linarith⟩
lemma cancellationLoss_pointwise_bound (k : ℝ) (hk : 0 ≤ k) (z : Torus) (n : ℕ) :
    cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+
      ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) := by
  by_cases hl : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)
  · apply hl.trans
    have hh : 0 ≤ ∑ s∈Finset.range (n+1), (if torusCancellation k s z then 2*(s:ℝ)+2 else 0) :=
      Finset.sum_nonneg fun s hs => by split_ifs  <;> positivity
    linarith
  · obtain ⟨hs1,hsn,hls,hcan⟩ := large_loss_implies_cancellation k hk z n (lt_of_not_ge hl)
    let s := ⌊cancellationLoss k z n/2⌋₊
    have hsum := Finset.single_le_sum (f:=fun s : ℕ => if torusCancellation k s z then 2*(s:ℝ)+2 else 0)
      (fun i hi => by split_ifs  <;> positivity) (show s∈Finset.range (n+1) by simpa only [Finset.mem_range] using Nat.lt_succ_of_le hsn)
    rw [ite_eq_left hcan] at hsum
    have hD := wingDefect_nonneg k hk z n
    linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MeanDeficit
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma integral_torusIter (k : ℝ) (a : ℤ) (f : Torus → ℝ) :
    (∫ z, f (torusIter k a z) ∂area)=∫ z, f z ∂area :=
  (measurePreserving_torusIter k a).integral_comp (torusIterMeasurableEquiv k a).measurableEmbedding f
lemma integrable_productDistance (k : ℝ) (hk : 0 ≤ k) (i j : ℤ) :
    Integrable (fun z => productDistance k z i j) area :=
  (continuous_productDistance k hk i j).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
lemma continuous_wingDefect (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => wingDefect k z n) :=
  continuous_const.sub ((continuous_productDistance k hk 0 (-(n:ℤ))).min (continuous_productDistance k hk 0 (n:ℤ)))
lemma continuous_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : Continuous (fun z => cancellationLoss k z n) :=
  ((continuous_productDistance k hk 0 (-(n:ℤ))).add (continuous_productDistance k hk 0 (n:ℤ))).sub
    (continuous_productDistance k hk (-(n:ℤ)) (n:ℤ))
lemma integral_productDistance_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) :
    0 ≤ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ∧ (∫ z, productDistance k z 0 (n:ℤ) ∂area) ≤ (n:ℝ) := by
  refine ⟨integral_nonneg (fun z => productDistance_nonneg k hk z 0 (n:ℤ)),?_⟩
  have hh := integral_mono (integrable_productDistance k hk 0 (n:ℤ)) (integrable_const (n:ℝ)) (fun z => by simpa using productDistance_le k hk z 0 (n:ℤ))
  simpa only [Int.cast_natCast,Int.cast_zero,sub_zero,Nat.abs_cast,integral_const,Measure.real,measure_univ,ENNReal.toReal_one,one_smul] using hh
lemma meanDeficit_bounds (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) : 0 ≤ meanDeficit k n ∧ meanDeficit k n ≤ 1 := by
  obtain ⟨h0,h1⟩ := integral_productDistance_bounds k hk n
  have hnp : (0:ℝ)<n := by exact_mod_cast hn
  have hdiv : (∫ z, productDistance k z 0 (n:ℤ) ∂area)/(n:ℝ) ≤ 1 := (div_le_one hnp).mpr h1
  have hdiv0 := div_nonneg h0 hnp.le
  unfold meanDeficit; constructor <;> linarith
lemma integral_distance_shift (k : ℝ) (i j a : ℤ) :
    (∫ z,productDistance k z (i+a) (j+a) ∂area)=∫ z,productDistance k z i j ∂area := by
  calc
    _ = ∫ z,productDistance k (torusIter k a z) i j ∂area := by simp only [productDistance_shift]
    _ = _ := by convert! integral_torusIter k a (fun z => productDistance k z i j) using 1
lemma integral_wing_left (k : ℝ) (n : ℕ) :
    (∫ z, productDistance k z 0 (-(n:ℤ)) ∂area)=∫ z, productDistance k z 0 (n:ℤ) ∂area := by
  simp_rw [productDistance_symm k _ 0 (-(n:ℤ))]
  convert integral_distance_shift k 0 (n:ℤ) (-(n:ℤ)) using 1 ; simp
lemma integral_wingDefect_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,wingDefect k z n ∂area) ≤ 2*(n:ℝ)*meanDeficit k n := by
  have hbd (z : Torus) : wingDefect k z n ≤ ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) := by
    have hl := productDistance_le k hk z 0 (-(n:ℤ))
    have hr := productDistance_le k hk z 0 (n:ℤ)
    simp only [Int.cast_neg,Int.cast_natCast,Int.cast_zero,sub_zero,abs_neg,Nat.abs_cast] at hl hr
    unfold wingDefect
    rcases le_total (productDistance k z 0 (-(n:ℤ))) (productDistance k z 0 (n:ℤ)) with h | h
    · rw [min_eq_left h]; linarith
    · rw [min_eq_right h]; linarith
  have hL := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (-(n:ℤ)))
  have hR := (integrable_const (n:ℝ)).sub (integrable_productDistance k hk 0 (n:ℤ))
  have hh := integral_mono ((continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (hL.add hR) hbd
  simp only [Pi.add_apply,Pi.sub_apply] at hh
  have hsum : (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ)))+((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area)=
      (∫ z, ((n:ℝ)-productDistance k z 0 (-(n:ℤ))) ∂area)+(∫ z, ((n:ℝ)-productDistance k z 0 (n:ℤ)) ∂area) := by
    convert! integral_add hL hR using 1
  have hsub (i : ℤ) : (∫ z, ((n:ℝ)-productDistance k z 0 i) ∂area)=(n:ℝ)-(∫ z,productDistance k z 0 i ∂area) := by
    calc
      _ = (∫ _z : Torus, (n:ℝ) ∂area)-(∫ z,productDistance k z 0 i ∂area) := by
        convert! integral_sub (integrable_const (n:ℝ)) (integrable_productDistance k hk 0 i) using 1
      _ = _ := by simp
  rw [hsum,hsub,hsub,integral_wing_left] at hh
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  unfold meanDeficit
  field_simp [hn0] at *
  nlinarith
lemma integral_cancellationLoss (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    (∫ z,cancellationLoss k z n ∂area)=2*(n:ℝ)*(meanDeficit k (n+n)-meanDeficit k n) := by
  have hL := integrable_productDistance k hk 0 (-(n:ℤ))
  have hR := integrable_productDistance k hk 0 (n:ℤ)
  have hT := integrable_productDistance k hk (-(n:ℤ)) (n:ℤ)
  have ht : (∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area)=∫ z,productDistance k z 0 ((n+n:ℕ):ℤ) ∂area := by
    convert integral_distance_shift k 0 ((n+n:ℕ):ℤ) (-(n:ℤ)) using 1 ; push_cast ; ring_nf
  have hsum : (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ)) ∂area)+(∫ z,productDistance k z 0 (n:ℤ) ∂area) := by
    convert! integral_add hL hR using 1
  have hsub : (∫ z,cancellationLoss k z n ∂area)=
      (∫ z,productDistance k z 0 (-(n:ℤ))+productDistance k z 0 (n:ℤ) ∂area)-(∫ z,productDistance k z (-(n:ℤ)) (n:ℤ) ∂area) := by
    convert! integral_sub (hL.add hR) hT using 1
  rw [hsub,hsum,integral_wing_left,ht]
  unfold meanDeficit
  have hn0 : (n:ℝ)≠0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp [hn0]; ring
lemma meanDeficit_doubling_mono (k : ℝ) (hk : 0 ≤ k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n ≤ meanDeficit k (n+n) := by
  have hh : 0 ≤ ∫ z,cancellationLoss k z n ∂area := integral_nonneg fun z => (cancellationLoss_bounds k hk z n).1
  rw [integral_cancellationLoss k hk n hn] at hh
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MeanCancellation
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma cancellation_weight_sum (N : ℕ) :
    ∑ s∈Finset.range N, (2*(s:ℝ)+2)*(1/4:ℝ)^s ≤ 4 := by
  have hb (s : ℕ) : (s:ℝ)+1 ≤ (2:ℝ)^s := by
    induction s with
    | zero => norm_num
    | succ s ih => rw [pow_succ]; push_cast; nlinarith
  calc
    _ ≤ ∑ s∈Finset.range N, 2*(1/2:ℝ)^s := Finset.sum_le_sum fun s hs => by
      have hh := mul_le_mul_of_nonneg_right (hb s) (show 0 ≤ (1/4:ℝ)^s by positivity)
      rw [← mul_pow] at hh
      norm_num at hh
      nlinarith
    _ = 2*∑ s∈Finset.range N, (1/2:ℝ)^s := by rw [Finset.mul_sum]
    _ ≤ 4 := by
      have hh := sum_geometric_two_le N
      norm_num only [one_div] at *
      linarith
lemma cancellationWeight_eq_indicator (k : ℝ) (s : ℕ) :
    cancellationWeight k s={z | torusCancellation k s z}.indicator (fun _ => 2*(s:ℝ)+2) := by
  funext z
  simp only [cancellationWeight,Set.indicator_apply,Set.mem_ofPred_eq]
lemma integrable_cancellationWeight (k : ℝ) (s : ℕ) : Integrable (cancellationWeight k s) area := by
  rw [cancellationWeight_eq_indicator]
  exact (integrable_const _).indicator (isClosed_torusCancellation k s).measurableSet
lemma integral_cancellationWeight (k : ℝ) (s : ℕ) :
    (∫ z,cancellationWeight k s z ∂area)=(2*(s:ℝ)+2)*area.real {z | torusCancellation k s z} := by
  rw [cancellationWeight_eq_indicator,integral_indicator (isClosed_torusCancellation k s).measurableSet]
  simp [mul_comm]
lemma integral_cancellationWeight_le (k : ℝ) (C : ℝ) (hC : 0 ≤ C) (s : ℕ)
    (hc : area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationWeight k s z ∂area) ≤ C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) := by
  rw [integral_cancellationWeight]
  have hr : area.real {z | torusCancellation k s z} ≤ C*(1/4:ℝ)^s := by
    have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hc
    rwa [ENNReal.toReal_ofReal (by positivity)] at hh
  have hh := mul_le_mul_of_nonneg_left hr (show 0 ≤ 2*(s:ℝ)+2 by positivity)
  nlinarith
lemma integral_cancellationLoss_le (k : ℝ) (hk : 0 ≤ k) (n : ℕ)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ s : ℕ, area {z | torusCancellation k s z} ≤ ENNReal.ofReal (C*(1/4:ℝ)^s)) :
    (∫ z,cancellationLoss k z n ∂area) ≤
      10000000000*(1+∫ z,wingDefect k z n ∂area)+4*C := by
  have hD : Integrable (fun z => wingDefect k z n) area :=
    (continuous_wingDefect k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hl : Integrable (fun z => cancellationLoss k z n) area :=
    (continuous_cancellationLoss k hk n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hw : Integrable (fun z => ∑ s∈Finset.range (n+1), cancellationWeight k s z) area :=
    integrable_finsetSum _ (fun s hs => integrable_cancellationWeight k s)
  have ht : Integrable (fun z => 10000000000*(1+wingDefect k z n)) area :=
    ((integrable_const 1).add hD).const_mul _
  have hb (z : Torus) : cancellationLoss k z n ≤ 10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z :=
    cancellationLoss_pointwise_bound k hk z n
  have hh := integral_mono hl (ht.add hw) hb
  have hsum : (∫ z,10000000000*(1+wingDefect k z n)+∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=
      (∫ z,10000000000*(1+wingDefect k z n) ∂area)+(∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area) := by
    convert! integral_add ht hw using 1
  have hDint : (∫ z,10000000000*(1+wingDefect k z n) ∂area)=10000000000*(1+∫ z,wingDefect k z n ∂area) := by
    rw [integral_const_mul]
    have he : (∫ z,1+wingDefect k z n ∂area)=1+∫ z,wingDefect k z n ∂area := by
      calc
        _ = (∫ _z : Torus,(1:ℝ) ∂area)+(∫ z,wingDefect k z n ∂area) := by
          convert! integral_add (integrable_const (1:ℝ)) hD using 1
        _ = _ := by simp
    rw [he]
  have hwint : (∫ z,∑ s∈Finset.range (n+1),cancellationWeight k s z ∂area)=∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area := by
    convert! integral_finsetSum (Finset.range (n+1)) (fun s hs => integrable_cancellationWeight k s) using 1
  simp only [Pi.add_apply] at hh
  rw [hsum,hDint,hwint] at hh
  have hsumbd : (∑ s∈Finset.range (n+1),∫ z,cancellationWeight k s z ∂area) ≤ 4*C := by
    calc
      _ ≤ ∑ s∈Finset.range (n+1),C*((2*(s:ℝ)+2)*(1/4:ℝ)^s) :=
        Finset.sum_le_sum fun s hs => integral_cancellationWeight_le k C hC s (hc s)
      _ = C*∑ s∈Finset.range (n+1),(2*(s:ℝ)+2)*(1/4:ℝ)^s := by rw [Finset.mul_sum]
      _ ≤ 4*C := by nlinarith [mul_le_mul_of_nonneg_left (cancellation_weight_sum (n+1)) hC]
  linarith
lemma doublingConstant_pos : 0<doublingConstant := by
  unfold doublingConstant; nlinarith [cancellationConstant_pos]
lemma eventually_meanDeficit_doubling :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0<k → M₀ ≤ growthBase k → ∀ n : ℕ, 0<n →
      meanDeficit k n ≤ meanDeficit k (n+n) ∧
      meanDeficit k (n+n) ≤ doublingConstant*meanDeficit k n+doublingConstant/(n:ℝ) := by
  obtain ⟨M₀,hM⟩ := eventually_cancellation_area
  refine ⟨M₀,?_⟩
  intro k hk hMk n hn
  refine ⟨meanDeficit_doubling_mono k hk.le n hn,?_⟩
  have hb := integral_cancellationLoss_le k hk.le n cancellationConstant cancellationConstant_pos.le (hM k hk hMk)
  have hD := integral_wingDefect_le k hk.le n hn
  rw [integral_cancellationLoss k hk.le n hn] at hb
  have he := (meanDeficit_bounds k hk.le n hn).1
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hc := cancellationConstant_pos
  unfold doublingConstant
  have hn0 : (0:ℝ)<n := by positivity
  apply (mul_le_mul_iff_right₀ hn0).mp
  rw [mul_add,mul_div_cancel₀ _ hn0.ne']
  have hx : 0 ≤ cancellationConstant*meanDeficit k n*(n:ℝ) := by positivity
  nlinarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_MeanGrowth
attribute [-instance] _root_.OAI.StandardMapEntropy.circleVolumeNullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma meanLoss_nonneg (k : ℝ) (hk : 0 ≤ k) (n : ℕ) : 0 ≤ meanLoss k n :=
  sub_nonneg.mpr (integral_productDistance_bounds k hk n).2
lemma meanLoss_eq (k : ℝ) (n : ℕ) : meanLoss k n=(n:ℝ)*meanDeficit k n := by
  cases n with
  | zero => simp [meanLoss,meanDeficit]
  | succ n => unfold meanLoss meanDeficit; field_simp
lemma meanLoss_superadditive (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) :
    meanLoss k n+meanLoss k m ≤ meanLoss k (n+m) := by
  have hi := integral_mono (integrable_productDistance k hk 0 ((n+m:ℕ):ℤ))
    ((integrable_productDistance k hk 0 (n:ℤ)).add (integrable_productDistance k hk (n:ℤ) ((n+m:ℕ):ℤ)))
    (fun z => productDistance_triangle k hk z 0 (n:ℤ) ((n+m:ℕ):ℤ))
  have he : (∫ z,productDistance k z 0 (n:ℤ)+productDistance k z (n:ℤ) ((n+m:ℕ):ℤ) ∂area)=
      (∫ z,productDistance k z 0 (n:ℤ) ∂area)+(∫ z,productDistance k z 0 (m:ℤ) ∂area) := by
    rw [integral_add (integrable_productDistance k hk 0 _) (integrable_productDistance k hk _ _)]
    congr 1
    simpa only [zero_add,add_zero,Nat.cast_add,add_comm] using integral_distance_shift k 0 (m:ℤ) (n:ℤ)
  simp only [Pi.add_apply] at hi
  rw [he] at hi
  unfold meanLoss
  simp only [Nat.cast_add] at hi ⊢
  linarith
lemma meanLoss_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (meanLoss k) := by
  intro n m hnm
  have hh := meanLoss_superadditive k hk n (m-n)
  rw [Nat.add_sub_of_le hnm] at hh
  linarith [meanLoss_nonneg k hk (m-n)]
lemma meanDeficit_comparison (k : ℝ) (hk : 0 ≤ k) (n m : ℕ) (hnm : n ≤ m) :
    (n:ℝ)*meanDeficit k n ≤ (m:ℝ)*meanDeficit k m := by
  simpa only [← meanLoss_eq] using meanLoss_mono k hk hnm
lemma meanDeficit_pow_mono (k : ℝ) (hk : 0 ≤ k) : Monotone (fun j : ℕ => meanDeficit k (2^j)) := by
  apply monotone_nat_of_le_succ
  intro j
  have hh := meanDeficit_doubling_mono k hk (2^j) (by positivity)
  simpa only [pow_succ,Nat.mul_two] using hh
lemma first_dyadic_crossing (k θ C : ℝ) (hk : 0 ≤ k) (hC : 0 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      (∀ j, j < q → meanDeficit k (2^j) ≤ θ) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) := by
  let q := Nat.find hex
  have hq : θ < meanDeficit k (2^q) := Nat.find_spec hex
  have hprev (j : ℕ) (hj : j < q) : meanDeficit k (2^j) ≤ θ :=
    le_of_not_gt (Nat.find_min hex hj)
  have hpq : p < q := by
    by_contra h
    have hle := meanDeficit_pow_mono k hk (show q ≤ p by omega)
    linarith
  refine ⟨q,hpq,hq,hprev,?_⟩
  have hq0 : 0 < q := by omega
  have hm := hdouble (2^(q-1)) (by positivity)
  have he : 2^(q-1)+2^(q-1)=2^q := by
    rw [← Nat.mul_two,← pow_succ]
    congr 1; omega
  rw [he] at hm
  have hθ := mul_le_mul_of_nonneg_left (hprev (q-1) (by omega)) hC
  have hpow : ((2^p:ℕ):ℝ) ≤ ((2^(q-1):ℕ):ℝ) := by
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (show p ≤ q-1 by omega)
  have hd : C/((2^(q-1):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
    div_le_div_of_nonneg_left hC (by positivity) hpow
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CosineNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace StandardMapEntropy
lemma countable_cosine_zero : Set.Countable {x : Circle | cosine x=0} := by
  apply (Set.countable_range (fun m : ℤ => (((2*(m:ℝ)+1)/4:ℝ) : Circle))).mono
  intro x hx
  obtain ⟨r,rfl⟩ := (QuotientAddGroup.mk_surjective (s := AddSubgroup.zmultiples (1:ℝ))) x
  change Real.cos (2*Real.pi*r)=0 at hx
  obtain ⟨m,hm⟩ := Real.cos_eq_zero_iff.mp hx
  refine ⟨m,?_⟩
  have he : r=(2*(m:ℝ)+1)/4 := by
    have hp := Real.pi_pos
    nlinarith
  rw [he]
lemma volume_cosine_zero : volume {x : Circle | cosine x=0}=0 := countable_cosine_zero.measure_zero volume
lemma cosine_small_measure (η : ℝ) (hη : 0<η) :
    ∃ δ : ℝ, 0<δ ∧ δ≤1 ∧ volume {x : Circle | |cosine x|≤δ}<ENNReal.ofReal η := by
  let E : ℕ → Set Circle := fun n => {x | |cosine x|≤1/((n:ℝ)+1)}
  have hm : Antitone E := by
    intro i j hij x hx
    change |cosine x|≤1/((i:ℝ)+1)
    change |cosine x|≤1/((j:ℝ)+1) at hx
    exact hx.trans (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hij 1))
  have he : (⋂ n,E n)={x : Circle | cosine x=0} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,E]
    constructor
    · intro hx
      apply abs_eq_zero.mp
      by_contra hn
      have hp : 0 < |cosine x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
      obtain ⟨n,hn⟩ := exists_nat_one_div_lt hp
      exact (not_lt_of_ge (hx n)) hn
    · intro hx n; simp [hx]; positivity
  have ht := tendsto_measure_iInter_atTop
    (μ := (volume : Measure Circle)) (s := E)
    (fun n => ((isClosed_le continuous_cosine.abs continuous_const).measurableSet.nullMeasurableSet)) hm
    ⟨0,measure_ne_top _ _⟩
  rw [he,volume_cosine_zero] at ht
  have hh : ∀ᶠ n : ℕ in atTop, volume (E n)<ENNReal.ofReal η :=
    ht.eventually (gt_mem_nhds (ENNReal.ofReal_pos.mpr hη))
  obtain ⟨n,hn⟩ := hh.exists
  refine ⟨1/((n:ℝ)+1),by positivity,?_,hn⟩
  exact (div_le_one (by positivity)).mpr (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_ConeGrowth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open Set Filter
open scoped Topology
namespace StandardMapEntropy
lemma transferStep_cone (v : ℝ) (B : ℝ) (hB : 2 ≤ B) (hv : B ≤ |v|) (z : ℂ)
    (hz : |z.im| ≤ |z.re|) :
    (B-1)*|z.re| ≤ |(transferStep v z).re| ∧ |(transferStep v z).im| ≤ |(transferStep v z).re| := by
  have htri := abs_sub_abs_le_abs_sub (v*z.re) z.im
  rw [abs_mul] at htri
  have hm := mul_le_mul_of_nonneg_right hv (abs_nonneg z.re)
  simp only [transferStep_re,transferStep_im]
  constructor <;> nlinarith [abs_nonneg z.re]
lemma transferProduct_cone (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) :
    (B-1)^n ≤ |(transferProduct v n 1).re| ∧ |(transferProduct v n 1).im| ≤ |(transferProduct v n 1).re| := by
  induction n with
  | zero => simp [transferProduct]
  | succ n ih =>
      obtain ⟨hg,hc⟩ := ih (fun i hi hin => hv i hi (by omega))
      obtain ⟨h1,h2⟩ := transferStep_cone (v (n+1)) B hB (hv _ (by omega) le_rfl) (transferProduct v n 1) hc
      simp only [transferProduct,ContinuousLinearMap.comp_apply]
      refine ⟨?_,h2⟩
      rw [pow_succ]
      have hh := mul_le_mul_of_nonneg_left hg (show 0 ≤ B-1 by linarith)
      nlinarith
lemma transferProduct_norm_lower_of_coefficients (v : ℕ → ℝ) (B : ℝ) (hB : 2 ≤ B) (n : ℕ)
    (hv : ∀ i, 1 ≤ i → i ≤ n → B ≤ |v i|) : (B-1)^n ≤ ‖transferProduct v n‖ := by
  calc
    _  ≤  |(transferProduct v n 1).re| := (transferProduct_cone v B hB n hv).1
    _  ≤  ‖transferProduct v n 1‖ := Complex.abs_re_le_norm _
    _  ≤  ‖transferProduct v n‖ := by simpa using (transferProduct v n).le_opNorm (1:ℂ)
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_FixedDeficit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma integrable_cosineBad (δ : ℝ) : Integrable (cosineBad δ) volume :=
  (integrable_const _).indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet
lemma integral_cosineBad (δ : ℝ) : (∫ x,cosineBad δ x ∂volume)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  unfold cosineBad
  rw [integral_indicator (isClosed_le continuous_cosine.abs continuous_const).measurableSet]
  simp [Measure.real]
lemma circleFst_preserving : MeasurePreserving (Prod.fst : Torus → Circle) area volume :=
  measurePreserving_fst
lemma bad_time_integrable (k δ : ℝ) (i : ℤ) :
    Integrable (fun z => cosineBad δ (torusIter k i z).1) area :=
  (circleFst_preserving.comp (measurePreserving_torusIter k i)).integrable_comp_of_integrable (integrable_cosineBad δ)
lemma bad_time_integral (k δ : ℝ) (i : ℤ) :
    (∫ z,cosineBad δ (torusIter k i z).1 ∂area)=(volume {x : Circle | |cosine x|≤δ}).toReal := by
  calc
    _ = ∫ z,cosineBad δ z.1 ∂area := by
      convert! integral_torusIter k i (fun z => cosineBad δ z.1) using 1
    _ = _ := by rw [area,integral_fun_fst,integral_cosineBad]; simp
lemma potential_large_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (x : Circle) (hx : δ≤|cosine x|) :
    growthBase k*δ/2≤|torusPotential k x| := by
  have hK : 0≤2*Real.pi*k := by positivity
  have ht := abs_sub_abs_le_abs_sub ((2*Real.pi*k)*cosine x) (-2)
  rw [abs_mul,abs_of_nonneg hK] at ht
  have hm := mul_le_mul_of_nonneg_left hx hK
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  unfold torusPotential
  have hg : growthBase k=2*Real.pi*k+4 := rfl
  have he : (2*Real.pi*k)*cosine x-(-2)=2+(2*Real.pi*k)*cosine x := by ring
  rw [he] at ht
  norm_num at ht
  nlinarith
lemma shortfall_small_of_cosine (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus)
    (hgood : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k) := by
  have hMd : 12≤growthBase k*δ := (div_le_iff₀ hδ0).mp hM
  have hMp : 0<growthBase k := by have := growthBase_ge_four k hk; linarith
  have hL : 0<Real.log (growthBase k) := log_growthBase_pos k hk
  have hg := transferProduct_norm_lower_of_coefficients (torusSegmentCoefficient k z 0)
    (growthBase k*δ/2) (by linarith) n (by
      intro i hi hin
      have hidx : (0:ℤ)+(i:ℤ)-1=((i-1:ℕ):ℤ) := by omega
      unfold torusSegmentCoefficient
      rw [hidx]
      exact potential_large_of_cosine k δ hk hδ0 hδ1 hM _ (hgood (i-1) (Finset.mem_range.mpr (by omega))))
  have hlower : (growthBase k*(δ/4))^n≤‖torusSegmentTransfer k z 0 n‖ := by
    apply (pow_le_pow_left₀ (by positivity : 0≤growthBase k*(δ/4)) (by nlinarith : growthBase k*(δ/4)≤growthBase k*δ/2-1) n).trans hg
  have hl := Real.log_le_log (show 0<(growthBase k*(δ/4))^n by positivity) hlower
  rw [Real.log_pow,Real.log_mul hMp.ne' (by positivity : δ/4≠0)] at hl
  have hnpos : (0:ℝ)<n := by exact_mod_cast hn
  unfold torusShortfall
  apply (le_div_iff₀ hL).mpr
  have he : (1-Real.log ‖torusSegmentTransfer k z 0 n‖/((n:ℝ)*Real.log (growthBase k)))*Real.log (growthBase k)=
      Real.log (growthBase k)-Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := by field_simp
  rw [he]
  have hnd : Real.log (growthBase k)+Real.log (δ/4)≤Real.log ‖torusSegmentTransfer k z 0 n‖/(n:ℝ) := (le_div_iff₀ hnpos).mpr (by nlinarith [hl])
  nlinarith
lemma fixed_shortfall_pointwise (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) (z : Torus) :
    torusShortfall k z 0 n≤-Real.log (δ/4)/Real.log (growthBase k)+
      ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 := by
  have h0 (i : ℕ) : 0≤cosineBad δ (torusIter k (i:ℤ) z).1 := by
    exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
  by_cases hg : ∀ i∈Finset.range n, δ≤|cosine (torusIter k (i:ℤ) z).1|
  · exact (shortfall_small_of_cosine k δ hk hδ0 hδ1 hM n hn z hg).trans (le_add_of_nonneg_right (Finset.sum_nonneg (fun i hi => h0 i)))
  · push Not at hg
    obtain ⟨i,hi,hbad⟩ := hg
    have h1 : cosineBad δ (torusIter k (i:ℤ) z).1=1 := by
      simp [cosineBad,le_of_lt hbad]
    have hs := Finset.single_le_sum (fun j _ => h0 j) hi
    rw [h1] at hs
    have hr : 0≤-Real.log (δ/4)/Real.log (growthBase k) :=
      div_nonneg (neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))) (log_growthBase_pos k hk).le
    have hsf := (torusShortfall_mem k hk z 0 n hn).2
    linarith
lemma meanDeficit_eq_integral_shortfall (k : ℝ) (hk : 0≤k) (n : ℕ) :
    meanDeficit k n=∫ z,torusShortfall k z 0 n ∂area := by
  have he (z : Torus) : torusShortfall k z 0 n=1-productDistance k z 0 (n:ℤ)/(n:ℝ) := by
    have hh := productDistance_forward k z 0 n
    simp only [zero_add] at hh
    rw [hh]
    unfold torusShortfall
    ring
  simp_rw [he]
  rw [integral_sub (integrable_const _) ((integrable_productDistance k hk 0 _).div_const _),integral_div]
  simp [meanDeficit]
lemma meanDeficit_fixed_bound (k δ : ℝ) (hk : 0≤k) (hδ0 : 0<δ) (hδ1 : δ≤1)
    (hM : 12/δ≤growthBase k) (n : ℕ) (hn : 0<n) :
    meanDeficit k n≤-Real.log (δ/4)/Real.log (growthBase k)+
      (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
  rw [meanDeficit_eq_integral_shortfall k hk n]
  have hi : Integrable (fun z => torusShortfall k z 0 n) area :=
    (continuous_torusShortfall k hk 0 n).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hs : Integrable (fun z => ∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1) area :=
    integrable_finsetSum _ (fun i hi => bad_time_integrable k δ (i:ℤ))
  have hb := integral_mono hi ((integrable_const _).add hs) (fixed_shortfall_pointwise k δ hk hδ0 hδ1 hM n hn)
  have he : (∫ z,-Real.log (δ/4)/Real.log (growthBase k)+∑ i∈Finset.range n,cosineBad δ (torusIter k (i:ℤ) z).1 ∂area)=
      -Real.log (δ/4)/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal := by
    rw [integral_add (integrable_const _) hs]
    have he := integral_finsetSum (Finset.range n) (fun (i : ℕ) _ => bad_time_integrable k δ (i:ℤ))
    rw [he]
    simp [bad_time_integral]
  exact he ▸ hb
lemma meanDeficit_fixed_small (n : ℕ) (hn : 0<n) (ε : ℝ) (hε : 0<ε) :
    ∃ M₀ : ℝ, ∀ k : ℝ, 0≤k → M₀≤growthBase k → meanDeficit k n≤ε := by
  have hn' : (0:ℝ)<n := by exact_mod_cast hn
  obtain ⟨δ,hδ0,hδ1,hδm⟩ := cosine_small_measure (ε/(2*(n:ℝ))) (by positivity)
  let C := -Real.log (δ/4)
  have hC : 0≤C := neg_nonneg.mpr (Real.log_nonpos (by linarith) (by linarith))
  refine ⟨max (12/δ) (Real.exp (2*C/ε+1)),?_⟩
  intro k hk hM
  have hMd : 12/δ≤growthBase k := (le_max_left _ _).trans hM
  have hMe : Real.exp (2*C/ε+1)≤growthBase k := (le_max_right _ _).trans hM
  have hlog := Real.log_le_log (Real.exp_pos _) hMe
  rw [Real.log_exp] at hlog
  have hr : C/Real.log (growthBase k)≤ε/2 := by
    apply (div_le_iff₀ (log_growthBase_pos k hk)).mpr
    have hm := mul_le_mul_of_nonneg_left hlog (show 0≤ε/2 by positivity)
    have he : (ε/2)*(2*C/ε+1)=C+ε/2 := by field_simp
    rw [he] at hm
    linarith
  have hv := ENNReal.toReal_lt_of_lt_ofReal hδm
  have hnv : (n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal<ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*(n:ℝ) by positivity)).mp hv
    nlinarith
  have hb := meanDeficit_fixed_bound k δ hk hδ0 hδ1 hMd n hn
  change meanDeficit k n≤C/Real.log (growthBase k)+(n:ℝ)*(volume {x : Circle | |cosine x|≤δ}).toReal at hb
  linarith
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalScales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter
open scoped ENNReal Topology Classical
namespace StandardMapEntropy
lemma exists_dyadic_ceiling (n : ℕ) (hn : 0 < n) : ∃ q : ℕ, n ≤ 2^q ∧ 2^q < 2*n := by
  have hx : ∃ q : ℕ, n ≤ 2^q := ⟨n,by
    have hh := (Nat.lt_two_pow_self (n := n))
    omega⟩
  let q := Nat.find hx
  have hl : n ≤ 2^q := Nat.find_spec hx
  refine ⟨q,hl,?_⟩
  by_cases hq : q=0
  · simp only [hq,pow_zero]; omega
  · have hp : 2^(q-1) < n := lt_of_not_ge (Nat.find_min hx (show q-1 < q by omega))
    have he : 2^q=2^(q-1)*2 := by rw [← pow_succ]; congr 1; omega
    rw [he]; omega
lemma positive_deficit_dyadic (k η : ℝ) (hk : 0 ≤ k) (hη : 0 < η)
    (hex : ∃ n : ℕ, 0 < n ∧ η ≤ meanDeficit k n) :
    ∃ q : ℕ, η/2 < meanDeficit k (2^q) := by
  obtain ⟨n,hn,hnη⟩ := hex
  obtain ⟨q,hq,hq2⟩ := exists_dyadic_ceiling n hn
  have hh := meanDeficit_comparison k hk n (2^q) hq
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hqR : ((2^q:ℕ):ℝ) < 2*(n:ℝ) := by exact_mod_cast hq2
  have hp : (0:ℝ) < (2^q:ℕ) := by positivity
  have he : 0 ≤ meanDeficit k (2^q) := (meanDeficit_bounds k hk _ (by positivity)).1
  refine ⟨q,?_⟩
  nlinarith
lemma meanDeficit_iterated_doubling (k C : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p m : ℕ) :
    meanDeficit k (2^(p+m)) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by
  have hp : (0:ℝ) < (2^p:ℕ) := by positivity
  have he0 := (meanDeficit_bounds k hk (2^p) (by positivity)).1
  induction m with
  | zero => simp only [Nat.add_zero,pow_zero,one_mul]; linarith [one_div_nonneg.mpr hp.le]
  | succ m ih =>
    have hh := hdouble (2^(p+m)) (by positivity)
    rw [show 2^(p+(m+1))=2^(p+m)+2^(p+m) by rw [show p+(m+1)=(p+m)+1 by omega,pow_succ,Nat.mul_two]]
    have hpM : ((2^p:ℕ):ℝ) ≤ ((2^(p+m):ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : p ≤ p+m)
    have hd : C/((2^(p+m):ℕ):ℝ) ≤ C/((2^p:ℕ):ℝ) :=
      div_le_div_of_nonneg_left (by linarith) hp hpM
    have hpow : (1:ℝ) ≤ (2*C)^m := one_le_pow₀ (by linarith)
    have ht := mul_le_mul_of_nonneg_left ih (by linarith : 0 ≤ C)
    rw [pow_succ]
    have hz : 0 ≤ 1/((2^p:ℕ):ℝ) := by positivity
    have hB : 1/((2^p:ℕ):ℝ) ≤ (2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)) := by nlinarith
    have hhB := mul_le_mul_of_nonneg_left hB (by linarith : 0 ≤ C)
    calc
      _ ≤ C*meanDeficit k (2^(p+m))+C/((2^(p+m):ℕ):ℝ) := hh
      _ ≤ C*((2*C)^m*(meanDeficit k (2^p)+1/((2^p:ℕ):ℝ)))+C/((2^p:ℕ):ℝ) := add_le_add ht hd
      _ ≤ _ := by simp only [div_eq_mul_inv] at hhB ⊢; nlinarith

lemma critical_scale_finite (k C θ : ℝ) (hk : 0 ≤ k) (hC : 1 ≤ C)
    (hdouble : ∀ n : ℕ, 0 < n → meanDeficit k (n+n) ≤ C*meanDeficit k n+C/(n:ℝ))
    (p : ℕ) (hp : meanDeficit k (2^p) ≤ θ^2) (hθ : 0 < θ) (hθ1 : θ < 1)
    (hex : ∃ q : ℕ, θ < meanDeficit k (2^q)) :
    ∃ q : ℕ, p < q ∧ θ < meanDeficit k (2^q) ∧
      meanDeficit k (2^q) ≤ C*θ+C/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m)) ≤ (2*C)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m)) ≤ (2*C)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨q,hpq,hq,hprev,hup⟩ := first_dyadic_crossing k θ C hk (by linarith) hdouble p (by nlinarith) hex
  refine ⟨q,hpq,hq,hup,?_,?_⟩
  · intro m
    exact (meanDeficit_iterated_doubling k C hk hC hdouble p m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
  · intro m
    have hpqR : ((2^p:ℕ):ℝ) ≤ ((2^q:ℕ):ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2) hpq.le
    have hd : 1/((2^q:ℕ):ℝ) ≤ 1/((2^p:ℕ):ℝ) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hpqR
    exact (meanDeficit_iterated_doubling k C hk hC hdouble q m).trans
      (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
end StandardMapEntropy

end OAI
end

section
-- module Solutions.OAIQ3_Std.StandardMap_CriticalSequence
attribute [-instance] _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayMulti _root_.OAI.StandardMapEntropy.CriticalScaleSequence.instRegularNonAffineArrayTerminal _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_dilate_local _root_.OAI.StandardMapEntropy.CriticalScaleSequence.multi_terminal_local
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Filter Set
open scoped Topology Classical
namespace StandardMapEntropy
lemma doublingConstant_ge_one : 1 ≤ doublingConstant := by
  unfold doublingConstant
  linarith [cancellationConstant_pos]

lemma choose_critical_parameter (η θ : ℝ) (hη : 0<η) (hθ : 0<θ) (hθ1 : θ<1)
    (hθη : θ<η/2) (p : ℕ) (R : ℝ)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) :
    ∃ k : ℝ, ∃ q : ℕ, 0<k ∧ R≤k ∧ p<q ∧ meanDeficit k (2^p)≤θ^2 ∧
      θ < meanDeficit k (2^q) ∧ meanDeficit k (2^q)≤doublingConstant*θ+doublingConstant/((2^p:ℕ):ℝ) ∧
      (∀ m : ℕ, meanDeficit k (2^(p+m))≤(2*doublingConstant)^m*(θ^2+1/((2^p:ℕ):ℝ))) ∧
      (∀ m : ℕ, meanDeficit k (2^(q+m))≤(2*doublingConstant)^m*(meanDeficit k (2^q)+1/((2^p:ℕ):ℝ))) := by
  obtain ⟨M₀,hM₀⟩ := eventually_meanDeficit_doubling
  obtain ⟨M₁,hM₁⟩ := meanDeficit_fixed_small (2^p) (by positivity) (θ^2) (sq_pos_of_pos hθ)
  let A := max M₀ M₁
  obtain ⟨k,hk,hbadk⟩ := hbad (max (max R 1) ((A-4)/(2*Real.pi)))
  have hk0 : 0<k := lt_of_lt_of_le (by norm_num) ((le_max_right R 1).trans ((le_max_left _ _).trans hk))
  have hkR : R≤k := (le_max_left R 1).trans ((le_max_left _ _).trans hk)
  have hKA : A≤growthBase k := by
    have hh := (le_max_right (max R 1) ((A-4)/(2*Real.pi))).trans hk
    have hpi : 0<2*Real.pi := by positivity
    have he := (div_le_iff₀ hpi).mp hh
    unfold growthBase
    nlinarith
  have hsmall := hM₁ k hk0.le ((le_max_right M₀ M₁).trans hKA)
  have hdouble := fun n hn => (hM₀ k hk0 ((le_max_left M₀ M₁).trans hKA) n hn).2
  have hex : ∃ q : ℕ, θ < meanDeficit k (2^q) := by
    obtain ⟨q,hq⟩ := positive_deficit_dyadic k η hk0.le hη hbadk
    exact ⟨q,hθη.trans hq⟩
  obtain ⟨q,hpq,hq,hup,hlo,hhi⟩ := critical_scale_finite k doublingConstant θ hk0.le doublingConstant_ge_one hdouble p hsmall hθ hθ1 hex
  exact ⟨k,q,hk0,hkR,hpq,hsmall,hq,hup,hlo,hhi⟩

lemma criticalTheta_pos (r i : ℕ) : 0 < criticalTheta r i := by unfold criticalTheta; positivity
lemma criticalTheta_lt_one (r i : ℕ) : criticalTheta r i < 1 := by
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
lemma criticalTheta_square (r i : ℕ) :
    1/((2^(criticalLowerExponent r i):ℕ):ℝ)=(criticalTheta r i)^2 := by
  unfold criticalLowerExponent criticalTheta
  push_cast
  simp only [div_pow,one_pow,← pow_mul]
  rw [Nat.mul_comm 2]
lemma exists_critical_scale_sequence_q3_oai (η : ℝ) (hη : 0<η)
    (hbad : ∀ K : ℝ, ∃ k : ℝ, K≤k ∧ BadGrowth η k) : Nonempty CriticalScaleSequence := by
  obtain ⟨r,hr⟩ := exists_pow_lt_of_lt_one (show 0<η/2 by positivity) (by norm_num : (1/2:ℝ)<1)
  have htη (i : ℕ) : criticalTheta r i < η/2 := by
    apply lt_of_le_of_lt _ hr
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  have hx (i : ℕ) := choose_critical_parameter η (criticalTheta r i) hη (criticalTheta_pos r i)
    (criticalTheta_lt_one r i) (htη i) (criticalLowerExponent r i) (i:ℝ) hbad
  choose k q hk hkR hpq hsmall hq hqU hlo hhi using hx
  refine ⟨⟨r,k,q,hk,hkR,hpq,hq,?_,?_,?_⟩⟩
  · intro i
    have hh := hqU i
    rw [show doublingConstant/((2^(criticalLowerExponent r i):ℕ):ℝ)=
      doublingConstant*(1/((2^(criticalLowerExponent r i):ℕ):ℝ)) by ring,criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have hmul := mul_le_mul_of_nonneg_left (show (criticalTheta r i)^2 ≤ criticalTheta r i by nlinarith) doublingConstant_pos.le
    nlinarith
  · intro i m
    have hh := hlo i m
    rw [criticalTheta_square] at hh
    nlinarith
  · intro i m
    have hh := hhi i m
    rw [criticalTheta_square] at hh
    have ht := criticalTheta_pos r i
    have ht1 := criticalTheta_lt_one r i
    have ht2 : (criticalTheta r i)^2 ≤ meanDeficit (k i) (2^(q i)) := by nlinarith [hq i]
    have hp : 0 ≤ (2*doublingConstant)^m := pow_nonneg (mul_nonneg (by norm_num) doublingConstant_pos.le) _
    nlinarith [mul_le_mul_of_nonneg_left ht2 hp]
end StandardMapEntropy

end OAI
end

theorem solution : type_of% @OAI.StandardMapEntropy.exists_critical_scale_sequence_q3_oai := @OAI.StandardMapEntropy.exists_critical_scale_sequence_q3_oai
