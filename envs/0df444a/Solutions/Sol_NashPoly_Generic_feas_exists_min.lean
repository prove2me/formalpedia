-- Prove2me | solution 1 for NashPoly.Generic.feas_exists_min
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-01T02:23:32.015877+00:00
-- url     : https://prove2.me/submissions/220f5daa-8cfe-47de-9877-9d578d6e2572

import Mathlib
import Definitions.Def_NashPoly_Generic_MultiplierExpr

open MvPolynomial Matrix NashPoly.Generic

namespace SolFemAux

theorem quad_lower {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    (Θ : Matrix ι ι ℝ) (hΘ : Θ.PosDef) :
    ∃ μ > 0, ∀ v : ι → ℝ, μ * ‖v‖ ^ 2 ≤ v ⬝ᵥ Θ *ᵥ v := by
  have hcont : Continuous fun v : ι → ℝ => v ⬝ᵥ Θ *ᵥ v := by
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨i0⟩ := ‹Nonempty ι›
  have hne : (Metric.sphere (0 : ι → ℝ) 1).Nonempty :=
    ⟨Pi.single i0 1, by simp [Pi.norm_single]⟩
  obtain ⟨w, hw, hmin⟩ := (isCompact_sphere (0 : ι → ℝ) 1).exists_isMinOn hne hcont.continuousOn
  have hw0 : w ≠ 0 := by
    intro h; rw [h] at hw; simp at hw
  have hpos : 0 < w ⬝ᵥ Θ *ᵥ w := by
    simpa using hΘ.dotProduct_mulVec_pos hw0
  refine ⟨_, hpos, fun v => ?_⟩
  by_cases hv : v = 0
  · subst hv; simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hs : ‖v‖⁻¹ • v ∈ Metric.sphere (0 : ι → ℝ) 1 := by
    simp [norm_smul, hnv.ne']
  have := hmin hs
  simp only [Set.mem_ofPred_eq] at this
  have key : (‖v‖⁻¹ • v) ⬝ᵥ Θ *ᵥ (‖v‖⁻¹ • v) = ‖v‖⁻¹ ^ 2 * (v ⬝ᵥ Θ *ᵥ v) := by
    rw [mulVec_smul, smul_dotProduct, dotProduct_smul]; simp [smul_eq_mul]; ring
  rw [key] at this
  have h2 : 0 < ‖v‖ ^ 2 := by positivity
  calc (w ⬝ᵥ Θ *ᵥ w) * ‖v‖ ^ 2 ≤ (‖v‖⁻¹ ^ 2 * (v ⬝ᵥ Θ *ᵥ v)) * ‖v‖ ^ 2 :=
        mul_le_mul_of_nonneg_right this h2.le
    _ = v ⬝ᵥ Θ *ᵥ v := by field_simp

variable {N : ℕ} {n m : Fin N → ℕ}

theorem cont_blk (i : Fin N) : Continuous fun x : Var n → ℝ => blk x i :=
  continuous_pi fun k => continuous_apply _

theorem cont_repl (i : Fin N) (v : Fin (n i) → ℝ) :
    Continuous fun x : Var n → ℝ => repl x i v := by
  refine continuous_pi fun w => ?_
  rcases w with ⟨j, k⟩
  by_cases h : j = i
  · subst h; simp [repl]; exact continuous_const
  · simp only [repl, Function.update_of_ne h]; exact continuous_apply _

theorem cont_evalblk (i : Fin N) (p : MvPolynomial (Fin (n i)) ℝ) :
    Continuous fun x : Var n → ℝ => eval (blk x i) p :=
  (continuous_eval p).comp (cont_blk i)

theorem cont_gradf (P : NEP N n m) (i : Fin N) (k : Fin (n i)) :
    Continuous fun x => P.gradf i x k := continuous_eval _

theorem cont_gradg (P : NEP N n m) (i : Fin N) (j : Fin (m i)) (k : Fin (n i)) :
    Continuous fun x => P.gradg i j x k := cont_evalblk i _

theorem cont_lam (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (i : Fin N) (j : Fin (m i)) : Continuous fun x => P.lam H i x j := by
  unfold NEP.lam
  refine continuous_finsetSum _ fun r _ => (cont_evalblk i _).mul ?_
  rcases r with k | k
  · exact cont_gradf P i k
  · exact continuous_const

theorem closed_feas (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ)) : IsClosed (P.Feas H K) := by
  unfold NEP.Feas NEP.GSet
  simp only [Set.ofPred_forall, Set.ofPred_and]
  refine IsClosed.inter (isClosed_iInter fun i => ?_) (isClosed_iInter fun i => isClosed_iInter
    fun v => isClosed_iInter fun _ => isClosed_le (continuous_eval _)
      ((continuous_eval _).comp (cont_repl i v)))
  refine IsClosed.inter (isClosed_iInter fun k => isClosed_eq ?_ continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq (cont_evalblk i _) continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_eq ((cont_lam P H i j).mul (cont_evalblk i _)) continuous_const)
    (IsClosed.inter (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (cont_evalblk i _))
    (isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le continuous_const (cont_lam P H i j)))))
  exact (cont_gradf P i k).sub (continuous_finsetSum _ fun j _ =>
    (cont_lam P H i j).mul (cont_gradg P i j k))

end SolFemAux

open SolFemAux in
theorem solution {N : ℕ} {n m : Fin N → ℕ} (P : NEP N n m)
    (H : (i : Fin N) → Matrix (Fin (m i)) (Fin (n i) ⊕ Fin (m i)) (MvPolynomial (Fin (n i)) ℝ))
    (K : (i : Fin N) → Set (Fin (n i) → ℝ))
    (Θ : Matrix (Option (Var n)) (Option (Var n)) ℝ) (hΘ : Θ.PosDef)
    (hne : (P.Feas H K).Nonempty) :
    ∃ u ∈ P.Feas H K, IsMinOn (theta Θ) (P.Feas H K) u := by
  classical
  obtain ⟨μ, hμ, hq⟩ := quad_lower Θ hΘ
  have hct : Continuous (theta Θ : (Var n → ℝ) → ℝ) := by
    have : Continuous (xbar1 : (Var n → ℝ) → Option (Var n) → ℝ) := by
      refine continuous_pi fun o => ?_
      cases o with
      | none => exact continuous_const
      | some w => exact continuous_apply w
    unfold theta
    simp only [dotProduct, mulVec]
    fun_prop
  obtain ⟨x0, hx0⟩ := hne
  set S := P.Feas H K ∩ {x | theta Θ x ≤ theta Θ x0} with hS
  have hSc : IsCompact S := by
    refine Metric.isCompact_of_isClosed_isBounded
      ((closed_feas P H K).inter (isClosed_le hct continuous_const)) ?_
    rw [Metric.isBounded_iff_subset_closedBall 0]
    refine ⟨Real.sqrt (theta Θ x0 / μ), fun x hx => ?_⟩
    rw [Metric.mem_closedBall, dist_zero_right]
    have h1 : ‖x‖ ≤ ‖xbar1 x‖ := by
      refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun w => ?_
      have := norm_le_pi_norm (xbar1 x) (some w)
      simpa [xbar1] using this
    have h2 : μ * ‖xbar1 x‖ ^ 2 ≤ theta Θ x0 := (hq _).trans hx.2
    apply Real.le_sqrt_of_sq_le
    rw [le_div_iff₀ hμ]
    have h3 : ‖x‖ ^ 2 ≤ ‖xbar1 x‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    nlinarith [mul_le_mul_of_nonneg_left h3 hμ.le]
  obtain ⟨u, hu, hmin⟩ := hSc.exists_isMinOn ⟨x0, hx0, show theta Θ x0 ≤ theta Θ x0 from le_refl _⟩ hct.continuousOn
  refine ⟨u, hu.1, fun x hx => ?_⟩
  by_cases h : theta Θ x ≤ theta Θ x0
  · exact hmin ⟨hx, h⟩
  · push Not at h
    show theta Θ u ≤ theta Θ x
    exact (hu.2).trans h.le
