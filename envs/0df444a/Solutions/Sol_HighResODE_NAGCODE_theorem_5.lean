-- Prove2me | solution 1 for HighResODE.NAGCODE.theorem_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T22:11:26.004621+00:00
-- url     : https://prove2.me/submissions/77ed978f-ccaf-4b2a-9c17-c48b078181a8

import Mathlib
import Definitions.Def_HighResODE_NAGCODE_Setting

namespace RRAux_HighResODE_NAGCODE_theorem_5

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_diff (f : F → ℝ) (hf : ContDiff ℝ 2 f) : Differentiable ℝ (gradient f) := by
  have h1 : ContDiff ℝ 1 (fderiv ℝ f) := hf.fderiv_right (by norm_num)
  have h2 : Differentiable ℝ (fderiv ℝ f) := h1.differentiable (by norm_num)
  have : gradient f = fun x => (InnerProductSpace.toDual ℝ F).symm (fderiv ℝ f x) := rfl
  rw [this]
  exact (InnerProductSpace.toDual ℝ F).symm.toContinuousLinearEquiv.differentiable.comp h2

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem descent (f : F → ℝ) (L : ℝ) (hd : Differentiable ℝ f)
    (hlip : ∀ x y, ‖gradient f x - gradient f y‖ ≤ L * ‖x - y‖) (x y : F) :
    f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + L / 2 * ‖y - x‖ ^ 2 := by
  set w := y - x with hw
  set ψ : ℝ → ℝ := fun t => f (x + t • w) - t * ⟪gradient f x, w⟫_ℝ - L / 2 * t ^ 2 * ‖w‖ ^ 2
    with hψ
  have hder : ∀ t, HasDerivAt ψ (⟪gradient f (x + t • w), w⟫_ℝ - ⟪gradient f x, w⟫_ℝ
      - L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
    intro t
    have hl : HasDerivAt (fun t : ℝ => x + t • w) w t := by
      simpa using ((hasDerivAt_id t).smul_const w).const_add x
    have hc := (hd (x + t • w)).hasFDerivAt.comp_hasDerivAt t hl
    rw [grad_inner f] at hc
    have h2 : HasDerivAt (fun t : ℝ => t * ⟪gradient f x, w⟫_ℝ) ⟪gradient f x, w⟫_ℝ t := by
      simpa using (hasDerivAt_id t).mul_const ⟪gradient f x, w⟫_ℝ
    have h3 : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖w‖ ^ 2) (L / 2 * (2 * t) * ‖w‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖w‖ ^ 2)
      simpa using this
    exact (hc.sub h2).sub h3
  have hanti : AntitoneOn ψ (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro t _; exact (hder t).continuousAt.continuousWithinAt
    · intro t _; exact (hder t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      rw [(hder t).deriv]
      have h1 := real_inner_le_norm (gradient f (x + t • w) - gradient f x) w
      have h2 := hlip (x + t • w) x
      have e : x + t • w - x = t • w := by abel
      rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at h2
      rw [inner_sub_left] at h1
      have h3 := mul_le_mul_of_nonneg_right h2 (norm_nonneg w)
      nlinarith
  have := hanti (show (0:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 le_rfl)
    (show (1:ℝ) ∈ Set.Ici 0 from Set.mem_Ici.2 zero_le_one) zero_le_one
  simp only [hψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul] at this
  have e : x + w = y := by rw [hw]; abel
  rw [e] at this
  norm_num at this
  rw [grad_inner f] at this
  linarith

theorem key3 (v x g : F) (u σ δ : ℝ) (hu : 0 ≤ u) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hG : δ ≤ ⟪g, x⟫_ℝ) :
    (1 * (u + σ / 2) + u * 1) * δ + u * (u + σ / 2) * ⟪g, v⟫_ℝ
      + 1 / 2 * (2 * ⟪u • v + (2:ℝ) • x + (u * σ) • g, -(u + σ / 2) • g⟫_ℝ)
      ≤ -(σ * u ^ 2 * ‖g‖ ^ 2) := by
  simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real,
    real_inner_self_eq_norm_sq]
  rw [real_inner_comm g v, real_inner_comm g x]
  have h1 : (u + σ / 2) * δ ≤ (u + σ / 2) * ⟪x, g⟫_ℝ := by
    rw [real_inner_comm] at hG
    exact mul_le_mul_of_nonneg_left hG (by positivity)
  have h2 : 0 ≤ σ * δ := mul_nonneg hσ hδ
  have h3 : 0 ≤ u * σ ^ 2 * ‖g‖ ^ 2 := by positivity
  nlinarith

end RRAux_HighResODE_NAGCODE_theorem_5

open scoped InnerProductSpace
open RRAux_HighResODE_NAGCODE_theorem_5

open HighResODE.NAGCODE in
theorem solution {n : ℕ} (f : HighResODE.NAGSC.E n → ℝ) (L s : ℝ) (hf : IsF2 f L) (xs : HighResODE.NAGSC.E n)
    (hmin : ∀ z : HighResODE.NAGSC.E n, f xs ≤ f z) (hs : 0 < s) (x0 : HighResODE.NAGSC.E n) (X V : ℝ → HighResODE.NAGSC.E n)
    (hsol : IsNAGCODE f s x0 X V) :
    ∀ t : ℝ, t0 s < t →
      (⨅ u : Set.Icc (t0 s) t, ‖gradient f (X u)‖ ^ 2)
        ≤ (12 + 9 * s * L) * ‖x0 - xs‖ ^ 2 / (2 * Real.sqrt s * (t ^ 3 - (t0 s) ^ 3)) := by
  intro t ht
  obtain ⟨hX0, hV0, hXd, hVd⟩ := hsol
  have hL := hf.L_pos
  have hdiff := hf.differentiable
  have hconv := hf.convex
  have hlip := hf.lipschitz_gradient
  have hgd := grad_diff f hf.contDiff
  have hg0 : gradient f xs = 0 := by
    have hlm : IsLocalMin f xs := Filter.Eventually.of_forall hmin
    unfold gradient
    rw [hlm.fderiv_eq_zero, map_zero]
  have hσ : 0 < Real.sqrt s := Real.sqrt_pos.2 hs
  have ht0 : t0 s = 3 * Real.sqrt s / 2 := rfl
  have ht0p : 0 < t0 s := by rw [ht0]; positivity
  set m := ⨅ u : Set.Icc (t0 s) t, ‖gradient f (X u)‖ ^ 2 with hm
  have hmle : ∀ w, t0 s ≤ w → w ≤ t → m ≤ ‖gradient f (X w)‖ ^ 2 := by
    intro w hw1 hw2
    have hbdd : BddBelow (Set.range fun u : Set.Icc (t0 s) t => ‖gradient f (X u)‖ ^ 2) :=
      ⟨0, by rintro _ ⟨u, rfl⟩; positivity⟩
    exact ciInf_le hbdd ⟨w, hw1, hw2⟩
  -- derivative of the Lyapunov function
  have hderiv : ∀ u, t0 s ≤ u → HasDerivWithinAt (lyap f s xs X V)
      ((1 * (u + Real.sqrt s / 2) + u * 1) * (f (X u) - f xs)
        + u * (u + Real.sqrt s / 2) * ⟪gradient f (X u), V u⟫_ℝ
        + 1 / 2 * (2 * ⟪u • V u + (2:ℝ) • (X u - xs) + (u * Real.sqrt s) • gradient f (X u),
            -(u + Real.sqrt s / 2) • gradient f (X u)⟫_ℝ)) (Set.Ici (t0 s)) u := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ht0p hu
    have hX := hXd u hu
    have hV := hVd u hu
    have h1 : HasDerivWithinAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ (Set.Ici (t0 s)) u := by
      have := (hdiff (X u)).hasFDerivAt.comp_hasDerivWithinAt u hX
      rw [grad_inner f] at this
      exact this
    have hg : HasDerivWithinAt (fun w => gradient f (X w))
          (fderiv ℝ (gradient f) (X u) (V u)) (Set.Ici (t0 s)) u :=
        (hgd (X u)).hasFDerivAt.comp_hasDerivWithinAt u hX
    have hW := (((hasDerivWithinAt_id u (Set.Ici (t0 s))).smul hV).add
      ((hX.sub_const xs).const_smul (2:ℝ))).add
      (((hasDerivWithinAt_id u (Set.Ici (t0 s))).mul_const (Real.sqrt s)).smul hg)
    have hW2 : HasDerivWithinAt
        (fun w => w • V w + (2:ℝ) • (X w - xs) + (w * Real.sqrt s) • gradient f (X w)) _ _ u := hW
    have hW3 : HasDerivWithinAt
        (fun w => w • V w + (2:ℝ) • (X w - xs) + (w * Real.sqrt s) • gradient f (X w))
        (-(u + Real.sqrt s / 2) • gradient f (X u)) (Set.Ici (t0 s)) u := by
      refine hW2.congr_deriv ?_
      simp only [id, smul_sub, smul_smul, one_mul, one_smul]
      have e1 : u * -(3 / u) = -3 := by field_simp
      have e2 : u * (1 + 3 * Real.sqrt s / (2 * u)) = u + 3 * Real.sqrt s / 2 := by field_simp
      rw [e1, e2]
      module
    have hc : HasDerivWithinAt (fun w : ℝ => w * (w + Real.sqrt s / 2))
        (1 * (u + Real.sqrt s / 2) + u * 1) (Set.Ici (t0 s)) u :=
      (hasDerivWithinAt_id u _).mul ((hasDerivWithinAt_id u _).add_const _)
    exact (hc.mul (h1.sub_const (f xs))).add ((hW3.norm_sq).const_mul (1 / 2))
  have hDle : ∀ u, t0 s ≤ u → (1 * (u + Real.sqrt s / 2) + u * 1) * (f (X u) - f xs)
        + u * (u + Real.sqrt s / 2) * ⟪gradient f (X u), V u⟫_ℝ
        + 1 / 2 * (2 * ⟪u • V u + (2:ℝ) • (X u - xs) + (u * Real.sqrt s) • gradient f (X u),
            -(u + Real.sqrt s / 2) • gradient f (X u)⟫_ℝ)
        ≤ -(Real.sqrt s * u ^ 2 * ‖gradient f (X u)‖ ^ 2) := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le ht0p hu
    have hG : f (X u) - f xs ≤ ⟪gradient f (X u), X u - xs⟫_ℝ := by
      have := hconv (X u) xs
      rw [← neg_sub (X u) xs, inner_neg_right] at this
      linarith
    exact key3 (V u) (X u - xs) (gradient f (X u)) u (Real.sqrt s) _ hu0.le hσ.le
      (sub_nonneg.2 (hmin _)) hG
  -- the auxiliary function G(w) = E(w) + σ m w³ / 3 is antitone on [t0, t]
  have hanti : AntitoneOn (fun w => lyap f s xs X V w + Real.sqrt s * m * w ^ 3 / 3)
      (Set.Icc (t0 s) t) := by
    have hGd : ∀ u, t0 s ≤ u → HasDerivWithinAt
        (fun w => lyap f s xs X V w + Real.sqrt s * m * w ^ 3 / 3)
        (((1 * (u + Real.sqrt s / 2) + u * 1) * (f (X u) - f xs)
        + u * (u + Real.sqrt s / 2) * ⟪gradient f (X u), V u⟫_ℝ
        + 1 / 2 * (2 * ⟪u • V u + (2:ℝ) • (X u - xs) + (u * Real.sqrt s) • gradient f (X u),
            -(u + Real.sqrt s / 2) • gradient f (X u)⟫_ℝ))
          + Real.sqrt s * m * (3 * u ^ 2) / 3) (Set.Ici (t0 s)) u := by
      intro u hu
      have := ((hasDerivAt_pow 3 u).const_mul (Real.sqrt s * m)).div_const 3
      simp only [Nat.cast_ofNat] at this
      have h3 : HasDerivWithinAt (fun w => Real.sqrt s * m * w ^ 3 / 3)
          (Real.sqrt s * m * (3 * u ^ (3 - 1)) / 3) (Set.Ici (t0 s)) u := this.hasDerivWithinAt
      norm_num at h3
      exact (hderiv u hu).add h3
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
    · intro u hu
      exact ((hGd u hu.1).continuousWithinAt).mono Set.Icc_subset_Ici_self
    · intro u hu
      rw [interior_Icc] at hu
      exact ((hGd u hu.1.le).hasDerivAt (Ici_mem_nhds hu.1)).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Icc] at hu
      rw [((hGd u hu.1.le).hasDerivAt (Ici_mem_nhds hu.1)).deriv]
      have h1 := hDle u hu.1.le
      have h2 := hmle u hu.1.le hu.2.le
      have h3 : Real.sqrt s * u ^ 2 * m ≤ Real.sqrt s * u ^ 2 * ‖gradient f (X u)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by positivity)
      nlinarith
  have hGt := hanti (Set.left_mem_Icc.2 ht.le) (Set.right_mem_Icc.2 ht.le) ht.le
  simp only at hGt
  -- E(t) ≥ 0
  have hEt : 0 ≤ lyap f s xs X V t := by
    unfold lyap
    have : 0 ≤ t * (t + Real.sqrt s / 2) * (f (X t) - f xs) := by
      have := sub_nonneg.2 (hmin (X t))
      have : 0 < t := ht0p.trans ht
      positivity
    positivity
  -- E(t0) bound
  have hE0 : lyap f s xs X V (t0 s) ≤ (2 + 3 / 2 * (s * L)) * ‖x0 - xs‖ ^ 2 := by
    unfold lyap
    rw [hX0, hV0]
    have e : t0 s • -Real.sqrt s • gradient f x0 + (2:ℝ) • (x0 - xs)
        + (t0 s * Real.sqrt s) • gradient f x0 = (2:ℝ) • (x0 - xs) := by
      module
    rw [e, norm_smul, mul_pow]
    have e2 : t0 s * (t0 s + Real.sqrt s / 2) = 3 * s := by
      rw [ht0]; ring_nf; rw [Real.sq_sqrt hs.le]
    rw [e2]
    have hδ : f x0 - f xs ≤ L / 2 * ‖x0 - xs‖ ^ 2 := by
      have := descent f L hdiff hlip xs x0
      rw [hg0, inner_zero_left] at this
      linarith
    have : 3 * s * (f x0 - f xs) ≤ 3 * s * (L / 2 * ‖x0 - xs‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hδ (by positivity)
    norm_num
    nlinarith
  have hT : 0 < t ^ 3 - t0 s ^ 3 := by
    have : t0 s ^ 3 < t ^ 3 := pow_lt_pow_left₀ ht ht0p.le (by norm_num)
    linarith
  rw [le_div_iff₀ (by positivity)]
  have key : Real.sqrt s * m * (t ^ 3 - t0 s ^ 3) ≤ 3 * ((2 + 3 / 2 * (s * L)) * ‖x0 - xs‖ ^ 2) := by
    nlinarith
  nlinarith

#print axioms solution
