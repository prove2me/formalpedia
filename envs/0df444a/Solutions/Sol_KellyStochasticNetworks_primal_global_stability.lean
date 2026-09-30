-- Prove2me | solution 1 for KellyStochasticNetworks.primal_global_stability
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-27T01:33:11.523356+00:00
-- url     : https://prove2.me/submissions/c6994247-56ef-457f-af0f-adf32517effa

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_KellyStochasticNetworks_Congestion

namespace KellyStochasticNetworks

lemma pr_P_convex (q : ℝ → ℝ) (hq : Continuous q) (hmono : Monotone q) :
    ConvexOn ℝ Set.univ (fun u => ∫ s in (0:ℝ)..u, q s) := by
  have hd : ∀ u, HasDerivAt (fun u => ∫ s in (0:ℝ)..u, q s) (q u) u :=
    fun u => (hq.integral_hasStrictDerivAt 0 u).hasDerivAt
  have hderiv : deriv (fun u => ∫ s in (0:ℝ)..u, q s) = q := funext fun u => (hd u).deriv
  refine Monotone.convexOn_univ_of_deriv (fun u => (hd u).differentiableAt) ?_
  rw [hderiv]; exact hmono

theorem pr_strictConcave {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) :
    StrictConcaveOn ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} (primalUtility A w p) := by
  have hconv : Convex ℝ {x : Fin R → ℝ | ∀ r, 0 < x r} := by
    intro x hx y hy a b ha hb hab r
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rcases ha.eq_or_lt with rfl | ha'
    · rw [zero_add] at hab; subst hab
      have := hy r; simp only [zero_mul, zero_add, one_mul]; exact this
    · have := mul_pos ha' (hx r); have := mul_nonneg hb (hy r).le; linarith
  refine ⟨hconv, fun x hx y hy hxy a b ha hb hab => ?_⟩
  obtain ⟨r0, hr0⟩ := Function.ne_iff.mp hxy
  have hP := fun j => pr_P_convex (p j) (hp j) (hpmono j)
  unfold primalUtility
  simp only [smul_eq_mul]
  have h1 : a * ∑ r, w r * Real.log (x r) + b * ∑ r, w r * Real.log (y r) <
      ∑ r, w r * Real.log ((a • x + b • y) r) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro r _
      have := strictConcaveOn_log_Ioi.concaveOn.2 (hx r) (hy r) ha.le hb.le hab
      simp only [smul_eq_mul] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have m := mul_le_mul_of_nonneg_left this (hw r).le
      have e : w r * (a * Real.log (x r) + b * Real.log (y r)) =
          a * (w r * Real.log (x r)) + b * (w r * Real.log (y r)) := by ring
      linarith
    · refine ⟨r0, Finset.mem_univ _, ?_⟩
      have := strictConcaveOn_log_Ioi.2 (hx r0) (hy r0) hr0 ha hb hab
      simp only [smul_eq_mul] at this
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have m := mul_lt_mul_of_pos_left this (hw r0)
      have e : w r0 * (a * Real.log (x r0) + b * Real.log (y r0)) =
          a * (w r0 * Real.log (x r0)) + b * (w r0 * Real.log (y r0)) := by ring
      linarith
  have h2 : (∑ j, (∫ s in (0:ℝ)..(linkFlow A (a • x + b • y) j), p j s)) ≤
      a * (∑ j, (∫ s in (0:ℝ)..(linkFlow A x j), p j s)) +
        b * (∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) := by
    have e : a * (∑ j, (∫ s in (0:ℝ)..(linkFlow A x j), p j s)) +
        b * (∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) =
        ∑ j, (a * (∫ s in (0:ℝ)..(linkFlow A x j), p j s) +
          b * (∫ s in (0:ℝ)..(linkFlow A y j), p j s)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    rw [e]
    refine Finset.sum_le_sum fun j _ => ?_
    have hL : linkFlow A (a • x + b • y) j = a * linkFlow A x j + b * linkFlow A y j := by
      simp only [linkFlow, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring
    rw [hL]
    have := (hP j).2 (Set.mem_univ (linkFlow A x j)) (Set.mem_univ (linkFlow A y j)) ha.le hb.le hab
    simpa only [smul_eq_mul] using this
  linarith

theorem pr_lyapunov_deriv {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j))
    (x : ℝ → Fin R → ℝ) (t : ℝ) (hpos : ∀ r, 0 < x t r)
    (hode : ∀ r, HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    HasDerivAt (fun s => primalUtility A w p (x s))
        (∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2) t
      ∧ 0 ≤ ∑ r, (κ r / x t r)
          * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by
  set D : Fin R → ℝ := fun r => primalDrift A w κ p (x t) r with hD
  have h1 : HasDerivAt (fun s => ∑ r, w r * Real.log (x s r))
      (∑ r, w r * (D r / x t r)) t :=
    HasDerivAt.fun_sum fun r _ => ((hode r).log (hpos r).ne').const_mul (w r)
  have hL : ∀ j, HasDerivAt (fun s => linkFlow A (x s) j) (∑ r, A j r * D r) t :=
    fun j => HasDerivAt.fun_sum fun r _ => (hode r).const_mul (A j r)
  have h2 : HasDerivAt (fun s => ∑ j, ∫ y in (0:ℝ)..(linkFlow A (x s) j), p j y)
      (∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r) t := by
    apply HasDerivAt.fun_sum
    intro j _
    have hF := ((hp j).integral_hasStrictDerivAt 0 (linkFlow A (x t) j)).hasDerivAt
    exact hF.comp t (hL j)
  have h := h1.sub h2
  have hval : (∑ r, w r * (D r / x t r)) - ∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r =
      ∑ r, (κ r / x t r) * (w r - x t r * ∑ j, A j r * p j (linkFlow A (x t) j)) ^ 2 := by
    have e1 : ∑ j, p j (linkFlow A (x t) j) * ∑ r, A j r * D r =
        ∑ r, D r * ∑ j, A j r * p j (linkFlow A (x t) j) := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun j _ => by ring
    rw [e1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun r _ => ?_
    have hx0 := (hpos r).ne'
    simp only [hD, primalDrift]
    field_simp
  refine ⟨?_, ?_⟩
  · rw [← hval]
    unfold primalUtility
    exact h
  · exact Finset.sum_nonneg fun r _ =>
      mul_nonneg (div_nonneg (hκ r).le (hpos r).le) (sq_nonneg _)

lemma pg_P_tangent (q : ℝ → ℝ) (hq : Continuous q) (hmono : Monotone q) (a b : ℝ) :
    q a * (b - a) ≤ (∫ s in (0:ℝ)..b, q s) - ∫ s in (0:ℝ)..a, q s := by
  rw [intervalIntegral.integral_interval_sub_left (hq.intervalIntegrable 0 b)
    (hq.intervalIntegrable 0 a)]
  rcases le_total a b with hab | hba
  · have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hab intervalIntegrable_const
      (hq.intervalIntegrable a b) (fun s hs => hmono hs.1)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    linarith
  · have := intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hba (hq.intervalIntegrable b a)
      intervalIntegrable_const (fun s hs => hmono hs.2)
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    rw [intervalIntegral.integral_symm b a]
    linarith

lemma pg_max_of_eq {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ) (p : Fin J → ℝ → ℝ)
    (hw : ∀ r, 0 < w r) (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j))
    (y0 : Fin R → ℝ) (hy0 : ∀ r, 0 < y0 r)
    (heq : ∀ r, w r = y0 r * ∑ j, A j r * p j (linkFlow A y0 j)) :
    ∀ y : Fin R → ℝ, (∀ r, 0 < y r) → primalUtility A w p y ≤ primalUtility A w p y0 := by
  intro y hy
  unfold primalUtility
  have hlog : ∀ r, w r * Real.log (y r) ≤
      w r * Real.log (y0 r) + w r * ((y r - y0 r) / y0 r) := by
    intro r
    have hq : 0 < y r / y0 r := div_pos (hy r) (hy0 r)
    have hl := Real.log_le_sub_one_of_pos hq
    rw [Real.log_div (hy r).ne' (hy0 r).ne'] at hl
    have e : y r / y0 r - 1 = (y r - y0 r) / y0 r := by field_simp [(hy0 r).ne']
    rw [e] at hl
    have := mul_le_mul_of_nonneg_left hl (hw r).le
    nlinarith
  have hP : ∀ j, p j (linkFlow A y0 j) * (linkFlow A y j - linkFlow A y0 j) ≤
      (∫ s in (0:ℝ)..(linkFlow A y j), p j s) - ∫ s in (0:ℝ)..(linkFlow A y0 j), p j s :=
    fun j => pg_P_tangent (p j) (hp j) (hpmono j) _ _
  have hkey : ∑ r, w r * ((y r - y0 r) / y0 r) =
      ∑ j, p j (linkFlow A y0 j) * (linkFlow A y j - linkFlow A y0 j) := by
    have h1 : ∀ r, w r * ((y r - y0 r) / y0 r) =
        ∑ j, (y r - y0 r) * (A j r * p j (linkFlow A y0 j)) := by
      intro r; rw [heq r, ← Finset.mul_sum]; field_simp [(hy0 r).ne']
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show linkFlow A y j - linkFlow A y0 j = ∑ r, A j r * (y r - y0 r) by
      simp only [linkFlow, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun r _ => by ring, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring
  have h1 := Finset.sum_le_sum fun r (_ : r ∈ Finset.univ) => hlog r
  have h2 := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hP j
  rw [Finset.sum_add_distrib] at h1
  rw [Finset.sum_sub_distrib] at h2
  linarith

lemma pg_box {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ) (p : Fin J → ℝ → ℝ)
    (hA : ∀ j r, A j r = 0 ∨ A j r = 1) (hw : ∀ r, 0 < w r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j)) (hpnn : ∀ j y, 0 ≤ p j y)
    (hpne : ∀ j, ∃ y, p j y ≠ 0) (hroute : ∀ r, ∃ j, A j r = 1) (hR : 0 < R) (c0 : ℝ) :
    ∃ lo hi : Fin R → ℝ, (∀ r, 0 < lo r) ∧ ∀ y : Fin R → ℝ, (∀ r, 0 < y r) →
      c0 ≤ primalUtility A w p y → ∀ r, lo r ≤ y r ∧ y r ≤ hi r := by
  choose jr hjr using hroute
  have hA0 : ∀ j r, 0 ≤ A j r := fun j r => by rcases hA j r with h | h <;> rw [h]; norm_num
  have hlin : ∀ j, ∃ cj : ℝ, 0 < cj ∧ ∃ dj : ℝ, ∀ u, cj * u + dj ≤ ∫ s in (0:ℝ)..u, p j s := by
    intro j
    obtain ⟨u0, hu0⟩ := hpne j
    have hc : 0 < p j u0 := lt_of_le_of_ne (hpnn j u0) (Ne.symm hu0)
    refine ⟨p j u0, hc, (∫ s in (0:ℝ)..u0, p j s) - p j u0 * u0, fun u => ?_⟩
    have := pg_P_tangent (p j) (hp j) (hpmono j) u0 u
    linarith
  choose cj hcj dj hdj using hlin
  have hPnn : ∀ j u, 0 ≤ u → 0 ≤ ∫ s in (0:ℝ)..u, p j s := fun j u hu =>
    intervalIntegral.integral_nonneg hu (fun s _ => hpnn j s)
  have hRpos : (0:ℝ) < R := by exact_mod_cast hR
  set a : Fin R → ℝ := fun r => cj (jr r) / R with ha
  set D : ℝ := (∑ r, dj (jr r)) / R with hD
  have hapos : ∀ r, 0 < a r := fun r => div_pos (hcj _) hRpos
  have hU : ∀ y : Fin R → ℝ, (∀ r, 0 < y r) →
      primalUtility A w p y ≤ ∑ r, (w r * Real.log (y r) - a r * y r) - D := by
    intro y hy
    have hL : ∀ j, 0 ≤ linkFlow A y j := fun j =>
      Finset.sum_nonneg fun r _ => mul_nonneg (hA0 j r) (hy r).le
    have hLr : ∀ r, y r ≤ linkFlow A y (jr r) := by
      intro r
      have h1 : A (jr r) r * y r = y r := by rw [hjr r, one_mul]
      calc y r = A (jr r) r * y r := h1.symm
        _ ≤ ∑ r', A (jr r) r' * y r' :=
          Finset.single_le_sum (f := fun r' => A (jr r) r' * y r')
            (fun r' _ => mul_nonneg (hA0 _ _) (hy r').le) (Finset.mem_univ r)
    have hPen : ∀ r, cj (jr r) * y r + dj (jr r) ≤
        ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) := by
      intro r
      calc cj (jr r) * y r + dj (jr r) ≤ cj (jr r) * linkFlow A y (jr r) + dj (jr r) := by
            have := mul_le_mul_of_nonneg_left (hLr r) (hcj (jr r)).le
            linarith
        _ ≤ ∫ s in (0:ℝ)..(linkFlow A y (jr r)), p (jr r) s := hdj _ _
        _ ≤ ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) :=
          Finset.single_le_sum (f := fun j => ∫ s in (0:ℝ)..(linkFlow A y j), p j s)
            (fun j _ => hPnn j _ (hL j)) (Finset.mem_univ _)
    have hsum : ∑ r, (cj (jr r) * y r + dj (jr r)) ≤
        (R:ℝ) * ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) := by
      calc ∑ r, (cj (jr r) * y r + dj (jr r)) ≤
            ∑ _r : Fin R, ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) :=
            Finset.sum_le_sum fun r _ => hPen r
        _ = (R:ℝ) * ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have e1 : ∑ r, (w r * Real.log (y r) - a r * y r) =
        ∑ r, w r * Real.log (y r) - ∑ r, a r * y r := by
      rw [Finset.sum_sub_distrib]
    have e2 : ∑ r, a r * y r + D = (∑ r, (cj (jr r) * y r + dj (jr r))) / R := by
      rw [Finset.sum_add_distrib, add_div, Finset.sum_div, hD]
      congr 1
      exact Finset.sum_congr rfl fun r _ => by simp only [ha]; ring
    have h3 : (∑ r, (cj (jr r) * y r + dj (jr r))) / R ≤
        ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) := by
      rw [div_le_iff₀ hRpos]; linarith
    show (∑ r, w r * Real.log (y r)) - ∑ j, (∫ s in (0:ℝ)..(linkFlow A y j), p j s) ≤ _
    linarith
  set K : Fin R → ℝ := fun r => 2 * w r / a r with hK
  have hKpos : ∀ r, 0 < K r := fun r => div_pos (by linarith [hw r]) (hapos r)
  set Bd : Fin R → ℝ := fun r => w r * Real.log (K r) - w r with hBd
  have hh : ∀ r (u : ℝ), 0 < u → w r * Real.log u - a r * u ≤ Bd r - a r / 2 * u := by
    intro r u hu
    have hl := Real.log_le_sub_one_of_pos (div_pos hu (hKpos r))
    rw [Real.log_div hu.ne' (hKpos r).ne'] at hl
    have hwK : w r * (u / K r) = a r / 2 * u := by
      simp only [hK]; field_simp [(hapos r).ne', (hw r).ne']
    have := mul_le_mul_of_nonneg_left hl (hw r).le
    have e2 : w r * (u / K r - 1) = a r / 2 * u - w r := by rw [mul_sub, mul_one, hwK]
    simp only [hBd]
    nlinarith
  set Btot := ∑ r, |Bd r| with hBtot
  set m := c0 + D - Btot with hm
  refine ⟨fun r => Real.exp (m / w r), fun r => 2 * (Btot - m) / a r, fun r => Real.exp_pos _, ?_⟩
  intro y hy hc r
  have hUy := hU y hy
  have hother : ∑ s, (w s * Real.log (y s) - a s * y s) ≤
      (w r * Real.log (y r) - a r * y r) + Btot := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ r)]
    have : ∑ s ∈ Finset.univ.erase r, (w s * Real.log (y s) - a s * y s) ≤ Btot := by
      calc ∑ s ∈ Finset.univ.erase r, (w s * Real.log (y s) - a s * y s)
          ≤ ∑ s ∈ Finset.univ.erase r, |Bd s| := Finset.sum_le_sum fun s _ => by
            have := hh s (y s) (hy s)
            have := le_abs_self (Bd s)
            have := mul_pos (hapos s) (hy s)
            linarith
        _ ≤ Btot := Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            (fun s _ _ => abs_nonneg _)
    linarith
  have hr_ge : m ≤ w r * Real.log (y r) - a r * y r := by linarith
  have hBr : Bd r ≤ Btot := by
    calc Bd r ≤ |Bd r| := le_abs_self _
      _ ≤ Btot := Finset.single_le_sum (f := fun s => |Bd s|) (fun s _ => abs_nonneg _)
          (Finset.mem_univ r)
  constructor
  · have h1 : m ≤ w r * Real.log (y r) := by nlinarith [mul_pos (hapos r) (hy r)]
    have h2 : m / w r ≤ Real.log (y r) := by rw [div_le_iff₀ (hw r)]; linarith
    calc Real.exp (m / w r) ≤ Real.exp (Real.log (y r)) := Real.exp_le_exp.mpr h2
      _ = y r := Real.exp_log (hy r)
  · have := hh r (y r) (hy r)
    show y r ≤ 2 * (Btot - m) / a r
    rw [le_div_iff₀ (hapos r)]
    nlinarith

lemma pg_U_cont {J R : ℕ} (A : Fin J → Fin R → ℝ) (w : Fin R → ℝ) (p : Fin J → ℝ → ℝ)
    (hp : ∀ j, Continuous (p j)) :
    ContinuousOn (primalUtility A w p) {y : Fin R → ℝ | ∀ r, 0 < y r} := by
  have hP : ∀ j, Continuous (fun u => ∫ s in (0:ℝ)..u, p j s) := fun j =>
    continuous_iff_continuousAt.mpr fun u =>
      ((hp j).integral_hasStrictDerivAt 0 u).hasDerivAt.continuousAt
  have hL : ∀ j, Continuous (fun y : Fin R → ℝ => linkFlow A y j) := fun j =>
    continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_apply r)
  show ContinuousOn (fun y : Fin R → ℝ => (∑ r, w r * Real.log (y r)) -
    ∑ j, ∫ s in (0:ℝ)..(linkFlow A y j), p j s) _
  apply ContinuousOn.sub
  · apply continuousOn_finsetSum
    intro r _
    exact continuousOn_const.mul ((continuous_apply r).continuousOn.log fun y hy => (hy r).ne')
  · exact (continuous_finsetSum _ fun j _ => (hP j).comp (hL j)).continuousOn

lemma pg_G_cont {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ) (p : Fin J → ℝ → ℝ)
    (hp : ∀ j, Continuous (p j)) :
    ContinuousOn (fun y : Fin R → ℝ => ∑ r, (κ r / y r)
      * (w r - y r * ∑ j, A j r * p j (linkFlow A y j)) ^ 2) {y : Fin R → ℝ | ∀ r, 0 < y r} := by
  have hL : ∀ j, Continuous (fun y : Fin R → ℝ => linkFlow A y j) := fun j =>
    continuous_finsetSum _ fun r _ => continuous_const.mul (continuous_apply r)
  have hS : ∀ r, Continuous (fun y : Fin R → ℝ => ∑ j, A j r * p j (linkFlow A y j)) := fun r =>
    continuous_finsetSum _ fun j _ => continuous_const.mul ((hp j).comp (hL j))
  apply continuousOn_finsetSum
  intro r _
  apply ContinuousOn.mul
  · exact continuousOn_const.div (continuous_apply r).continuousOn fun y hy => (hy r).ne'
  · exact ((continuous_const.sub ((continuous_apply r).mul (hS r))).pow 2).continuousOn

theorem pg_main {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hw : ∀ r, 0 < w r) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j))
    (hpnn : ∀ j y, 0 ≤ p j y) (hpne : ∀ j, ∃ y, p j y ≠ 0)
    (xbar : Fin R → ℝ) (hbarpos : ∀ r, 0 < xbar r)
    (hbar : ∀ r, w r = xbar r * ∑ j, A j r * p j (linkFlow A xbar j))
    (x : ℝ → Fin R → ℝ) (hxpos : ∀ t, 0 ≤ t → ∀ r, 0 < x t r)
    (hode : ∀ t, 0 ≤ t → ∀ r,
      HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    IsMaxOn (primalUtility A w p) {y : Fin R → ℝ | ∀ r, 0 < y r} xbar
      ∧ Filter.Tendsto x Filter.atTop (nhds xbar) := by
  set U := primalUtility A w p with hUdef
  have hmax : ∀ y : Fin R → ℝ, (∀ r, 0 < y r) → U y ≤ U xbar :=
    pg_max_of_eq A w p hw hp hpmono xbar hbarpos hbar
  refine ⟨fun y hy => hmax y hy, ?_⟩
  rcases Nat.eq_zero_or_pos R with hR0 | hRpos
  · subst hR0
    have hx : x = fun _ => xbar := funext fun t => funext fun r => r.elim0
    rw [hx]; exact tendsto_const_nhds
  have hroute : ∀ r, ∃ j, A j r = 1 := by
    intro r
    by_contra hcon
    push Not at hcon
    have h0 : ∀ j, A j r = 0 := fun j => (hA j r).resolve_right (hcon j)
    have := hbar r
    simp only [h0, zero_mul, Finset.sum_const_zero, mul_zero] at this
    linarith [hw r]
  -- uniqueness of the maximizer
  have hsc := pr_strictConcave A w p hw hp hpmono
  have huniq : ∀ y : Fin R → ℝ, (∀ r, 0 < y r) → U xbar ≤ U y → y = xbar := by
    intro y hy hle
    by_contra hne
    have h := hsc.2 hy hbarpos hne (by norm_num : (0:ℝ) < 1 / 2) (by norm_num : (0:ℝ) < 1 / 2)
      (by norm_num)
    have hmid : ∀ r, 0 < ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • xbar) r := by
      intro r
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      have := hy r; have := hbarpos r; positivity
    have := hmax _ hmid
    simp only [smul_eq_mul] at h
    linarith
  -- the Lyapunov derivative
  set G : (Fin R → ℝ) → ℝ := fun y => ∑ r, (κ r / y r)
      * (w r - y r * ∑ j, A j r * p j (linkFlow A y j)) ^ 2 with hGdef
  have hGnn : ∀ y : Fin R → ℝ, (∀ r, 0 < y r) → 0 ≤ G y := fun y hy =>
    Finset.sum_nonneg fun r _ => mul_nonneg (div_nonneg (hκ r).le (hy r).le) (sq_nonneg _)
  have hG0 : ∀ y : Fin R → ℝ, (∀ r, 0 < y r) → G y = 0 → y = xbar := by
    intro y hy h0
    have hterm : ∀ r, w r = y r * ∑ j, A j r * p j (linkFlow A y j) := by
      intro r
      have hnn : ∀ r ∈ Finset.univ, 0 ≤ (κ r / y r)
          * (w r - y r * ∑ j, A j r * p j (linkFlow A y j)) ^ 2 :=
        fun r _ => mul_nonneg (div_nonneg (hκ r).le (hy r).le) (sq_nonneg _)
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0 r (Finset.mem_univ r)
      have hk : κ r / y r ≠ 0 := (div_pos (hκ r) (hy r)).ne'
      have h2 := (mul_eq_zero.mp h1).resolve_left hk
      have h3 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp h2
      linarith
    exact huniq y hy (pg_max_of_eq A w p hw hp hpmono y hy hterm xbar hbarpos)
  set V : ℝ → ℝ := fun t => U (x t) with hVdef
  have hVd : ∀ t, 0 ≤ t → HasDerivAt V (G (x t)) t := fun t ht =>
    (pr_lyapunov_deriv A w κ p hκ hp x t (hxpos t ht) (hode t ht)).1
  have hVmono : MonotoneOn V (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    · exact fun t ht => (hVd t ht).continuousAt.continuousWithinAt
    · rw [interior_Ici]
      exact fun t ht => (hVd t (le_of_lt ht)).differentiableAt.differentiableWithinAt
    · rw [interior_Ici]
      intro t ht
      rw [(hVd t (le_of_lt ht)).deriv]
      exact hGnn _ (hxpos t (le_of_lt ht))
  have hVlin : ∀ δ : ℝ, (∀ t, 0 ≤ t → δ ≤ G (x t)) → ∀ t, 0 ≤ t → V 0 + δ * t ≤ V t := by
    intro δ hδ t ht
    have hW : MonotoneOn (fun s => V s - δ * s) (Set.Ici 0) := by
      apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
      · exact fun s hs =>
          ((hVd s hs).sub ((hasDerivAt_id' s).const_mul δ)).continuousAt.continuousWithinAt
      · rw [interior_Ici]
        exact fun s hs => ((hVd s (le_of_lt hs)).sub
          ((hasDerivAt_id' s).const_mul δ)).differentiableAt.differentiableWithinAt
      · rw [interior_Ici]
        intro s hs
        have hd : HasDerivAt (fun s => V s - δ * s) (G (x s) - δ * 1) s :=
          (hVd s (le_of_lt hs)).sub ((hasDerivAt_id' s).const_mul δ)
        rw [hd.deriv]
        linarith [hδ s (le_of_lt hs)]
    have := hW (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    simp only [mul_zero, sub_zero] at this
    linarith
  -- compact box containing the trajectory
  obtain ⟨lo, hi, hlo, hbox⟩ :=
    pg_box A w p hA hw hp hpmono hpnn hpne hroute hRpos (V 0)
  set B : Set (Fin R → ℝ) := Set.univ.pi (fun r => Set.Icc (lo r) (hi r)) with hB
  have hBc : IsCompact B := isCompact_univ_pi fun r => isCompact_Icc
  have hBpos : ∀ y ∈ B, ∀ r, 0 < y r := fun y hy r =>
    lt_of_lt_of_le (hlo r) (hy r (Set.mem_univ r)).1
  have hUc : ContinuousOn U B := (pg_U_cont A w p hp).mono fun y hy => hBpos y hy
  have hGc : ContinuousOn G B := (pg_G_cont A w κ p hp).mono fun y hy => hBpos y hy
  have hxB : ∀ t, 0 ≤ t → x t ∈ B ∧ V 0 ≤ U (x t) := by
    intro t ht
    have hVt : V 0 ≤ V t := hVmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
    exact ⟨fun r _ => hbox (x t) (hxpos t ht) hVt r, hVt⟩
  have hclosed : ∀ T : Set ℝ, IsClosed T → IsCompact (B ∩ U ⁻¹' T) := fun T hT =>
    hBc.of_isClosed_subset (hUc.preimage_isClosed_of_isClosed hBc.isClosed hT)
      Set.inter_subset_left
  have hV0 : V 0 ≤ U xbar := hmax _ (hxpos 0 le_rfl)
  -- Step A: the Lyapunov function approaches its maximum
  have hstepA : ∀ η > 0, ∃ T, 0 ≤ T ∧ U xbar - η < V T := by
    intro η hη
    by_contra hcon
    push Not at hcon
    set K := B ∩ U ⁻¹' Set.Icc (V 0) (U xbar - η) with hK
    have hKc : IsCompact K := hclosed _ isClosed_Icc
    have hmemK : ∀ t, 0 ≤ t → x t ∈ K := fun t ht =>
      ⟨(hxB t ht).1, (hxB t ht).2, hcon t ht⟩
    obtain ⟨y0, hy0K, hy0min⟩ := hKc.exists_isMinOn ⟨x 0, hmemK 0 le_rfl⟩
      (hGc.mono Set.inter_subset_left)
    have hy0pos := hBpos y0 hy0K.1
    have hδ : 0 < G y0 := by
      rcases (hGnn y0 hy0pos).lt_or_eq with h | h
      · exact h
      · exfalso
        have h1 := hG0 y0 hy0pos h.symm
        have h2 : U y0 ≤ U xbar - η := hy0K.2.2
        rw [h1] at h2; linarith
    have hlin := hVlin (G y0) (fun t ht => hy0min (hmemK t ht))
    set t1 := (U xbar - V 0) / G y0 + 1 with ht1def
    have ht1 : 0 ≤ t1 := by
      have : 0 ≤ (U xbar - V 0) / G y0 := div_nonneg (by linarith) hδ.le
      linarith
    have h1 := hlin t1 ht1
    have h2 := hcon t1 ht1
    have e : G y0 * t1 = (U xbar - V 0) + G y0 := by
      rw [ht1def]; field_simp
    linarith
  -- Step B: convergence of the trajectory
  rw [Metric.tendsto_atTop]
  intro ε hε
  set Kε := (B ∩ U ⁻¹' Set.Ici (V 0)) ∩ {y | ε ≤ dist y xbar} with hKε
  have hKεc : IsCompact Kε := (hclosed _ isClosed_Ici).inter_right
    (isClosed_le continuous_const (continuous_id.dist continuous_const))
  rcases Kε.eq_empty_or_nonempty with hemp | hne
  · refine ⟨0, fun t ht => ?_⟩
    by_contra hcon
    push Not at hcon
    have hmem : x t ∈ Kε := ⟨⟨(hxB t ht).1, (hxB t ht).2⟩, hcon⟩
    rw [hemp] at hmem
    exact hmem
  · obtain ⟨y1, hy1K, hy1max⟩ := hKεc.exists_isMaxOn hne (hUc.mono fun y hy => hy.1.1)
    have hy1pos := hBpos y1 hy1K.1.1
    have hlt : U y1 < U xbar := by
      by_contra hcon
      push Not at hcon
      have h1 := huniq y1 hy1pos hcon
      have h2 : ε ≤ dist y1 xbar := hy1K.2
      rw [h1, dist_self] at h2
      linarith
    obtain ⟨T, hT0, hT⟩ := hstepA (U xbar - U y1) (by linarith)
    refine ⟨T, fun t ht => ?_⟩
    have ht0 : 0 ≤ t := le_trans hT0 ht
    have hVT : V T ≤ V t := hVmono (Set.mem_Ici.mpr hT0) (Set.mem_Ici.mpr ht0) ht
    by_contra hcon
    push Not at hcon
    have hmem : x t ∈ Kε := ⟨⟨(hxB t ht0).1, (hxB t ht0).2⟩, hcon⟩
    have h1 : U (x t) ≤ U y1 := hy1max hmem
    have h2 : V t = U (x t) := rfl
    linarith

end KellyStochasticNetworks

open KellyStochasticNetworks

theorem solution {J R : ℕ} (A : Fin J → Fin R → ℝ) (w κ : Fin R → ℝ)
    (p : Fin J → ℝ → ℝ) (hA : ∀ j r, A j r = 0 ∨ A j r = 1)
    (hw : ∀ r, 0 < w r) (hκ : ∀ r, 0 < κ r)
    (hp : ∀ j, Continuous (p j)) (hpmono : ∀ j, Monotone (p j))
    (hpnn : ∀ j y, 0 ≤ p j y) (hpne : ∀ j, ∃ y, p j y ≠ 0)
    (xbar : Fin R → ℝ) (hbarpos : ∀ r, 0 < xbar r)
    (hbar : ∀ r, w r = xbar r * ∑ j, A j r * p j (linkFlow A xbar j))
    (x : ℝ → Fin R → ℝ) (hxpos : ∀ t, 0 ≤ t → ∀ r, 0 < x t r)
    (hode : ∀ t, 0 ≤ t → ∀ r,
      HasDerivAt (fun s => x s r) (primalDrift A w κ p (x t) r) t) :
    IsMaxOn (primalUtility A w p) {y : Fin R → ℝ | ∀ r, 0 < y r} xbar
      ∧ Filter.Tendsto x Filter.atTop (nhds xbar) := by
  exact pg_main A w κ p hA hw hκ hp hpmono hpnn hpne xbar hbarpos hbar x hxpos hode
