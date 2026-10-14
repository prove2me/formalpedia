-- Prove2me | solution 1 for ModernOnlineLearning.Adaptive.theorem_4_30
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:59:34.908973+00:00
-- url     : https://prove2.me/submissions/563e5567-cee5-4230-9c7d-70670d804440

import Mathlib
import Definitions.Def_ModernOnlineLearning_Adaptive_Defs

namespace RRAux_ModernOnlineLearning_Adaptive_theorem_4_30

open ModernOnlineLearning.Adaptive

theorem proj_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : Set E) (hv : Convex ℝ V) (y p u : E) (hu : u ∈ V)
    (hp : OnlineConvexOpt.FirstOrder.IsMetricProjection V y p) :
    ‖p - u‖ ^ 2 ≤ ‖y - u‖ ^ 2 := by
  obtain ⟨hpV, hmin⟩ := hp
  have hinner : inner ℝ (y - p) (u - p) ≤ 0 := by
    have : ‖y - p‖ = ⨅ w : V, ‖y - w‖ := by
      have : Nonempty V := ⟨⟨p, hpV⟩⟩
      apply le_antisymm
      · exact le_ciInf fun w => by simpa [dist_eq_norm] using hmin w w.2
      · have hbdd : BddBelow (Set.range fun w : V => ‖y - (w : E)‖) :=
          ⟨0, by rintro _ ⟨w, rfl⟩; exact norm_nonneg _⟩
        exact ciInf_le hbdd ⟨p, hpV⟩
    exact (norm_eq_iInf_iff_real_inner_le_zero hv hpV).1 this u hu
  have e : y - u = (y - p) + (p - u) := by abel
  rw [e, @norm_add_sq_real]
  have h3 : inner ℝ (y - p) (p - u) = - inner ℝ (y - p) (u - p) := by
    rw [← inner_neg_right, neg_sub]
  nlinarith [sq_nonneg ‖y - p‖]

theorem step_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (x g u p : E) (η : ℝ) (hη : 0 < η)
    (h : ‖p - u‖ ^ 2 ≤ ‖x - η • g - u‖ ^ 2) :
    inner ℝ g (x - u) ≤ (‖x - u‖ ^ 2 - ‖p - u‖ ^ 2) / (2 * η) + η / 2 * ‖g‖ ^ 2 := by
  have e : x - η • g - u = (x - u) - η • g := by abel
  rw [e, norm_sub_sq_real (x - u) (η • g), inner_smul_right, norm_smul, Real.norm_eq_abs,
    abs_of_pos hη, real_inner_comm] at h
  rw [div_add' _ _ _ (by positivity), le_div_iff₀ (by positivity)]
  nlinarith

theorem scal (A Gt n2 D : ℝ) (hG : 0 < Gt) (hD : 0 < D) :
    A / (2 * (Real.sqrt 2 * D / (2 * Real.sqrt Gt))) +
      Real.sqrt 2 * D / (2 * Real.sqrt Gt) / 2 * n2 =
    Real.sqrt Gt / (Real.sqrt 2 * D) * A + D / (2 * Real.sqrt 2) * (n2 / Real.sqrt Gt) := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hsG : 0 < Real.sqrt Gt := Real.sqrt_pos.mpr hG
  field_simp
  linear_combination (D ^ 2 * n2) * h2

theorem cum_bound (a c : ℕ → ℝ) (D2 : ℝ) :
    ∀ T : ℕ, 1 ≤ T → (∀ t ∈ Finset.Icc 1 T, a t ≤ D2) → (∀ t ∈ Finset.Icc 1 T, 0 ≤ c t) →
    (∀ t ∈ Finset.Icc 1 (T - 1), c t ≤ c (t + 1)) →
    ∑ t ∈ Finset.Icc 1 T, c t * (a t - a (t + 1)) ≤ c T * D2 - c T * a (T + 1) := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro ha hc _
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have := ha 1 (by simp)
    have hp := hc 1 (by simp)
    nlinarith
  | succ n hn ih =>
    intro ha hc hm
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (fun t ht => ha t (by simp at ht ⊢; omega))
      (fun t ht => hc t (by simp at ht ⊢; omega))
      (fun t ht => hm t (by simp at ht ⊢; omega))
    have h3 : c n ≤ c (n + 1) := hm n (by simp; omega)
    have h4 : a (n + 1) ≤ D2 := ha (n + 1) (by simp)
    nlinarith

theorem ada_sum (y : ℕ → ℝ) (hy : ∀ t, 0 ≤ y t) :
    ∀ T : ℕ, ∑ t ∈ Finset.Icc 1 T, y t / Real.sqrt (∑ i ∈ Finset.Icc 1 t, y i) ≤
      2 * Real.sqrt (∑ i ∈ Finset.Icc 1 T, y i) := by
  intro T
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Icc_succ_top (by omega)]
    set G := ∑ i ∈ Finset.Icc 1 n, y i
    have hG : 0 ≤ G := Finset.sum_nonneg fun i _ => hy i
    have hyn := hy (n + 1)
    have key : y (n + 1) / Real.sqrt (G + y (n + 1)) ≤
        2 * Real.sqrt (G + y (n + 1)) - 2 * Real.sqrt G := by
      rcases eq_or_lt_of_le (add_nonneg hG hyn) with h0 | h0
      · have hy0 : y (n + 1) = 0 := by linarith
        have hG0 : G = 0 := by linarith
        rw [hy0, hG0]; simp
      · have hs := Real.sqrt_pos.mpr h0
        have h1 : Real.sqrt (G + y (n + 1)) ^ 2 = G + y (n + 1) := Real.sq_sqrt h0.le
        have h2 : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG
        have h3 : Real.sqrt G ≤ Real.sqrt (G + y (n + 1)) := Real.sqrt_le_sqrt (by linarith)
        have h4 : 0 ≤ Real.sqrt G := Real.sqrt_nonneg _
        rw [div_le_iff₀ hs]
        nlinarith
    linarith

theorem final (R c L D s : ℝ) (hD : 0 < D) (hs : 0 ≤ s) (hL : 0 ≤ L) (hc : 0 ≤ c)
    (h1 : R ≤ Real.sqrt 2 * D * Real.sqrt c) (h2 : c ≤ 2 * s * (R + L)) :
    R ≤ 4 * s * D ^ 2 + 2 * D * Real.sqrt (s * L) := by
  set w := 2 * D * Real.sqrt (s * L) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw2 : w ^ 2 = 4 * D ^ 2 * (s * L) := by
    rw [hw, mul_pow, Real.sq_sqrt (by positivity)]; ring
  by_contra hlt
  push Not at hlt
  have hR : 0 < R := lt_of_le_of_lt (by positivity) hlt
  have hsq : R ^ 2 ≤ 2 * D ^ 2 * c := by
    have := pow_le_pow_left₀ hR.le h1 2
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hc] at this
    linarith
  have hsD : 0 ≤ s * D ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ 2 * D ^ 2)]

theorem scal2 (Gs D : ℝ) (hD : 0 < D) :
    Gs / (Real.sqrt 2 * D) * D ^ 2 + D / (2 * Real.sqrt 2) * (2 * Gs) =
      Real.sqrt 2 * D * Gs := by
  have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  field_simp
  linear_combination (-Gs) * h2

end RRAux_ModernOnlineLearning_Adaptive_theorem_4_30

open ModernOnlineLearning.Adaptive in
-- Orabona, Theorem 4.30
theorem solution {d : ℕ} (V : Set (Vec d)) (ℓ : ℕ → Vec d → ℝ)
    (D s : ℝ) (T : ℕ) (x g : ℕ → Vec d)
    (hT : 1 ≤ T) (hs : 0 ≤ s) (hVne : V.Nonempty)
    (hVclosed : IsClosed V) (hVconv : Convex ℝ V)
    (hdiam : ∀ a ∈ V, ∀ b ∈ V, ‖a - b‖ ≤ D)
    (hconv : ∀ t ∈ Finset.Icc 1 T, ConvexOn ℝ Set.univ (ℓ t))
    (hnonneg : ∀ t ∈ Finset.Icc 1 T, ∀ z : Vec d, 0 ≤ ℓ t z)
    (hself : ∀ t ∈ Finset.Icc 1 T, IsSelfBounded V s (ℓ t))
    (hrun : IsAdaptiveOSDRun V ℓ D T x g) :
    ∀ u ∈ V, regret ℓ x u T ≤
      4 * s * D ^ 2 + 2 * D *
        Real.sqrt (s * (∑ t ∈ Finset.Icc 1 T, ℓ t u)) := by
  intro u hu
  obtain ⟨_, _, _, hD, _, hx1, hstep⟩ := hrun
  have hxV : ∀ t ∈ Finset.Icc 1 T, x t ∈ V := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨h1, h2⟩ := ht
    induction t, h1 using Nat.le_induction with
    | base => exact hx1
    | succ n hn ih =>
      have hn' := hstep n (by simp; omega)
      by_cases hg0 : g n = 0
      · rw [hn'.2.2.1 hg0]; exact ih (by omega)
      · exact (hn'.2.2.2 hg0).1
  set G : ℕ → ℝ := fun t => gradientEnergy g t with hGdef
  set c : ℕ → ℝ := fun t => Real.sqrt (G t) / (Real.sqrt 2 * D) with hc
  set a : ℕ → ℝ := fun t => ‖x t - u‖ ^ 2 with ha
  set b : ℕ → ℝ := fun t => D / (2 * Real.sqrt 2) * (‖g t‖ ^ 2 / Real.sqrt (G t)) with hb
  have hround : ∀ t ∈ Finset.Icc 1 T, ℓ t (x t) - ℓ t u ≤ c t * (a t - a (t + 1)) + b t := by
    intro t ht
    obtain ⟨_, hsub, hzero, hproj⟩ := hstep t ht
    have h1 : ℓ t (x t) - ℓ t u ≤ inner ℝ (g t) (x t - u) := by
      have := hsub u
      have e : inner ℝ (g t) (u - x t) = - inner ℝ (g t) (x t - u) := by
        rw [← inner_neg_right, neg_sub]
      linarith
    by_cases hg0 : g t = 0
    · have hx := hzero hg0
      simp only [ha, hb, hx, hg0, inner_zero_left, norm_zero, sub_self, mul_zero] at h1 ⊢
      simp at h1 ⊢
      linarith
    · have hgpos : 0 < ‖g t‖ ^ 2 := by positivity
      have hGt : 0 < G t := by
        simp only [hGdef, gradientEnergy]
        exact lt_of_lt_of_le hgpos (Finset.single_le_sum (f := fun i => ‖g i‖ ^ 2)
          (fun i _ => sq_nonneg _) (by simp at ht ⊢; omega))
      have hη : 0 < adaptiveStep D g t := by
        unfold adaptiveStep
        have : 0 < Real.sqrt (gradientEnergy g t) := Real.sqrt_pos.mpr hGt
        positivity
      have h2 := RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.proj_le V hVconv _ _ u hu
        (hproj hg0)
      have h3 := RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.step_ineq (x t) (g t) u
        (x (t + 1)) _ hη h2
      unfold adaptiveStep at h3
      rw [RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.scal _ _ _ _ hGt hD] at h3
      simp only [hc, ha, hb]
      linarith
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib] at hsum
  have hGmono : ∀ t, G t ≤ G (t + 1) := by
    intro t
    simp only [hGdef, gradientEnergy]
    rw [Finset.sum_Icc_succ_top (by omega)]
    linarith [sq_nonneg ‖g (t + 1)‖]
  have hcum := RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.cum_bound a c (D ^ 2) T hT
    (fun t ht => pow_le_pow_left₀ (norm_nonneg _) (hdiam _ (hxV t ht) u hu) 2)
    (fun t _ => by simp only [hc]; positivity)
    (fun t _ => by
      simp only [hc]
      apply div_le_div_of_nonneg_right (Real.sqrt_le_sqrt (hGmono t)) (by positivity))
  have hada := RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.ada_sum (fun t => ‖g t‖ ^ 2)
    (fun t => sq_nonneg _) T
  have hbsum : ∑ t ∈ Finset.Icc 1 T, b t ≤ D / (2 * Real.sqrt 2) * (2 * Real.sqrt (G T)) := by
    simp only [hb, ← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [hGdef, gradientEnergy] using hada
  have haT : 0 ≤ c T * a (T + 1) := by simp only [hc, ha]; positivity
  have hRle : regret ℓ x u T ≤ Real.sqrt 2 * D * Real.sqrt (G T) := by
    unfold regret
    rw [← RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.scal2 (Real.sqrt (G T)) D hD]
    simp only [hc] at hcum ⊢
    linarith
  -- self-bounding
  have hGself : G T ≤ 2 * s * (regret ℓ x u T + ∑ t ∈ Finset.Icc 1 T, ℓ t u) := by
    have : regret ℓ x u T + ∑ t ∈ Finset.Icc 1 T, ℓ t u = ∑ t ∈ Finset.Icc 1 T, ℓ t (x t) := by
      unfold regret; rw [Finset.sum_sub_distrib]; ring
    rw [this, Finset.mul_sum]
    simp only [hGdef, gradientEnergy]
    apply Finset.sum_le_sum
    intro t ht
    obtain ⟨_, _, hsb⟩ := hself t ht
    have h1 := hsb (x t) (hxV t ht) (g t) (hstep t ht).2.1
    have h2 : 0 ≤ sInf (Set.range (ℓ t)) :=
      Real.sInf_nonneg (by rintro _ ⟨z, rfl⟩; exact hnonneg t ht z)
    nlinarith
  have hL : 0 ≤ ∑ t ∈ Finset.Icc 1 T, ℓ t u :=
    Finset.sum_nonneg fun t ht => hnonneg t ht u
  have hG0 : 0 ≤ G T := by
    simp only [hGdef, gradientEnergy]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact RRAux_ModernOnlineLearning_Adaptive_theorem_4_30.final _ _ _ D s hD hs hL hG0 hRle hGself

#print axioms solution
