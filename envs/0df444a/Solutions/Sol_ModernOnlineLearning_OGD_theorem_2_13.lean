-- Prove2me | solution 1 for ModernOnlineLearning.OGD.theorem_2_13
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:01:22.159979+00:00
-- url     : https://prove2.me/submissions/5b2af9f5-bc7c-4304-abfa-1c21c7947a5d

import Mathlib
import Definitions.Def_ModernOnlineLearning_OGD_Defs

namespace RRAux_ModernOnlineLearning_OGD_theorem_2_13

theorem grad_ineq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (V : Set E) (hv : Convex ℝ V) (f : E → ℝ) (C : Set E) (hVC : V ⊆ C) (hf : ConvexOn ℝ C f)
    (x u g : E) (hx : x ∈ V) (hu : u ∈ V) (hg : HasGradientAt f g x) :
    f x - f u ≤ inner ℝ g (x - u) := by
  have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (f ∘ AffineMap.lineMap (k := ℝ) x u) := by
    refine (hf.comp_affineMap (AffineMap.lineMap (k := ℝ) x u)).subset ?_ (convex_Icc 0 1)
    intro s hs
    simp only [Set.mem_preimage]
    apply hVC
    rw [AffineMap.lineMap_apply_module']
    have := hv hu hx hs.1 (sub_nonneg.mpr hs.2) (by ring : s + (1 - s) = 1)
    convert this using 1
    rw [smul_sub, sub_smul, one_smul]; abel
  have hd : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x u) (inner ℝ g (u - x)) 0 := by
    have h1 := hg.hasFDerivAt
    rw [← AffineMap.lineMap_apply_zero x u (k := ℝ)] at h1
    have := h1.comp_hasDerivAt (0:ℝ) (AffineMap.hasDerivAt_lineMap (a := x) (b := u))
    simpa using this
  have := hφ.le_slope_of_hasDerivAt (x := 0) (y := 1) (by simp) (by simp) one_pos hd
  rw [slope_def_field] at this
  simp at this
  have h2 : inner ℝ g (x - u) = - inner ℝ g (u - x) := by
    rw [← inner_neg_right, neg_sub]
  linarith

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

theorem sum_bound (a η : ℕ → ℝ) (D2 : ℝ) :
    ∀ T : ℕ, 1 ≤ T → (∀ t ∈ Finset.Icc 1 T, a t ≤ D2) → (∀ t ∈ Finset.Icc 1 T, 0 < η t) →
    (∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t) →
    ∑ t ∈ Finset.Icc 1 T, (a t - a (t + 1)) / (2 * η t) ≤ D2 / (2 * η T) - a (T + 1) / (2 * η T) := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro ha hη _
    simp only [Finset.Icc_self, Finset.sum_singleton]
    have := ha 1 (by simp)
    have hp := hη 1 (by simp)
    have : a 1 / (2 * η 1) ≤ D2 / (2 * η 1) := div_le_div_of_nonneg_right this (by positivity)
    rw [sub_div]
    linarith
  | succ n hn ih =>
    intro ha hη hm
    rw [Finset.sum_Icc_succ_top (by omega)]
    have ih' := ih (fun t ht => ha t (by simp at ht ⊢; omega))
      (fun t ht => hη t (by simp at ht ⊢; omega))
      (fun t ht => hm t (by simp at ht ⊢; omega))
    have h1 : 0 < η n := hη n (by simp; omega)
    have h2 : 0 < η (n + 1) := hη (n + 1) (by simp)
    have h3 : η (n + 1) ≤ η n := hm n (by simp; omega)
    have h4 : a (n + 1) ≤ D2 := ha (n + 1) (by simp)
    have key : (D2 - a (n + 1)) / (2 * η n) ≤ (D2 - a (n + 1)) / (2 * η (n + 1)) := by
      apply div_le_div_of_nonneg_left (by linarith) (by positivity) (by linarith)
    have e1 : D2 / (2 * η n) - a (n + 1) / (2 * η n) = (D2 - a (n + 1)) / (2 * η n) := by ring
    have e2 : (a (n + 1) - a (n + 1 + 1)) / (2 * η (n + 1)) + (D2 - a (n + 1)) / (2 * η (n + 1))
        = D2 / (2 * η (n + 1)) - a (n + 1 + 1) / (2 * η (n + 1)) := by ring
    linarith

end RRAux_ModernOnlineLearning_OGD_theorem_2_13

open ModernOnlineLearning.OGD in
-- Orabona, Theorem 2.13
theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (hb : Bornology.IsBounded V)
    (loss : ℕ → E → ℝ) (η : ℕ → ℝ) (x g : ℕ → E) (T : ℕ)
    (hT : 1 ≤ T) (u : E) (hu : u ∈ V)
    (hloss : ∀ t ∈ Finset.Icc 1 T,
      ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U (loss t) ∧ DifferentiableOn ℝ (loss t) U)
    (hη : ∀ t ∈ Finset.Icc 1 T, 0 < η t)
    (hmono : ∀ t ∈ Finset.Icc 1 (T - 1), η (t + 1) ≤ η t)
    (hrun : IsOGDRun V loss η x g T) :
    regret loss x u T ≤
      Metric.diam V ^ 2 / (2 * η T) +
        ∑ t ∈ Finset.Icc 1 T, (η t / 2) * ‖g t‖ ^ 2 -
          ‖x (T + 1) - u‖ ^ 2 / (2 * η T) := by
  obtain ⟨_, _, _, hx1, hstep⟩ := hrun
  -- all iterates up to T lie in V
  have hxV : ∀ t ∈ Finset.Icc 1 T, x t ∈ V := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨h1, h2⟩ := ht
    induction t, h1 using Nat.le_induction with
    | base => exact hx1
    | succ n hn _ => exact ((hstep n (by simp; omega)).2.2.2.2).1
  have hround : ∀ t ∈ Finset.Icc 1 T, loss t (x t) - loss t u ≤
      (‖x t - u‖ ^ 2 - ‖x (t + 1) - u‖ ^ 2) / (2 * η t) + η t / 2 * ‖g t‖ ^ 2 := by
    intro t ht
    obtain ⟨hηt, ⟨C, _, hVC, hconv⟩, _, hgrad, hproj⟩ := hstep t ht
    have h1 := RRAux_ModernOnlineLearning_OGD_theorem_2_13.grad_ineq V hv (loss t) C hVC hconv
      (x t) u (g t) (hxV t ht) hu hgrad
    have h2 := RRAux_ModernOnlineLearning_OGD_theorem_2_13.proj_le V hv _ _ u hu hproj
    have h3 := RRAux_ModernOnlineLearning_OGD_theorem_2_13.step_ineq (x t) (g t) u (x (t + 1))
      (η t) hηt h2
    linarith
  have hsum := Finset.sum_le_sum hround
  rw [Finset.sum_add_distrib] at hsum
  have hb2 := RRAux_ModernOnlineLearning_OGD_theorem_2_13.sum_bound (fun t => ‖x t - u‖ ^ 2) η
    (Metric.diam V ^ 2) T hT
    (fun t ht => by
      have := Metric.dist_le_diam_of_mem hb (hxV t ht) hu
      rw [dist_eq_norm] at this
      exact pow_le_pow_left₀ (norm_nonneg _) this 2) hη hmono
  unfold regret
  linarith

#print axioms solution
