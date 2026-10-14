-- Prove2me | solution 1 for NesterovODE.Rate.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:09:27.466412+00:00
-- url     : https://prove2.me/submissions/08bde886-e249-4b55-8102-27689f4f4884

import Mathlib
import Definitions.Def_NesterovODE_Rate_Setting

namespace RRAux_NesterovODE_Rate_theorem_3

open scoped InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

theorem grad_inner (f : F → ℝ) (x v : F) :
    fderiv ℝ f x v = ⟪gradient f x, v⟫_ℝ := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply.symm

theorem conv_grad (f : F → ℝ) (hc : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) (x y : F) :
    f x + ⟪gradient f x, y - x⟫_ℝ ≤ f y := by
  have hg : ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap (k := ℝ) x y) := by
    have := hc.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
    simpa using this
  have hl : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
  have hfx : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • (y - x)) := by
    simpa using (hd x).hasFDerivAt
  have hcomp := hfx.comp_hasDerivAt (0:ℝ) hl
  have e : (f ∘ AffineMap.lineMap (k := ℝ) x y) = fun t : ℝ => f (x + t • (y - x)) := by
    funext t; simp [AffineMap.lineMap_apply, add_comm]
  have hd' : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) ⟪gradient f x, y - x⟫_ℝ 0 := by
    rw [e, ← grad_inner f]; exact hcomp
  have := hg.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd'
  rw [slope_def_field, e] at this
  have e1 : x + (1:ℝ) • (y - x) = y := by rw [one_smul]; abel
  simp only [e1, zero_smul, add_zero, sub_zero, div_one] at this
  linarith

theorem key (g w v : F) (t δ : ℝ) (h : 0 < t) (hG : δ ≤ ⟪g, w⟫_ℝ) :
    2 * t * δ + t ^ 2 * ⟪g, v⟫_ℝ
      + 2 * (2 * ⟪w + (t / 2) • v, v + (1 / 2 : ℝ) • v + (t / 2) • (-(3 / t) • v - g)⟫_ℝ)
      ≤ 0 := by
  have e : v + (1 / 2 : ℝ) • v + (t / 2) • (-(3 / t) • v - g) = -(t / 2) • g := by
    rw [smul_sub, smul_smul]
    have : t / 2 * -(3 / t) = -(3 / 2) := by field_simp
    rw [this]; module
  rw [e]
  simp only [inner_add_left, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm g w, real_inner_comm g v]
  have : t * δ ≤ t * ⟪w, g⟫_ℝ := by
    rw [real_inner_comm] at hG; exact mul_le_mul_of_nonneg_left hG h.le
  nlinarith

end RRAux_NesterovODE_Rate_theorem_3

open scoped InnerProductSpace
open RRAux_NesterovODE_Rate_theorem_3

open NesterovODE.Rate in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsFinfty f)
    (x₀ xstar : EuclideanSpace ℝ (Fin n)) (hxstar : ∀ y, f xstar ≤ f y)
    (X V : ℝ → EuclideanSpace ℝ (Fin n)) (hX : IsSolution f 3 x₀ X V) :
    ∀ t : ℝ, 0 < t → f (X t) - f xstar ≤ 2 * ‖x₀ - xstar‖ ^ 2 / t ^ 2 := by
  intro t ht
  obtain ⟨L, _, hconv, hC1, _⟩ := hf
  have hd : Differentiable ℝ f := hC1.differentiable (by norm_num)
  obtain ⟨hX0, hV0, hXd0, hVc0, hode⟩ := hX
  set E : ℝ → ℝ := fun u => u ^ 2 * (f (X u) - f xstar) + 2 * ‖X u + (u / 2) • V u - xstar‖ ^ 2
    with hE
  have hder : ∀ u, 0 < u → HasDerivAt E
      (2 * u * (f (X u) - f xstar) + u ^ 2 * ⟪gradient f (X u), V u⟫_ℝ
        + 2 * (2 * ⟪X u + (u / 2) • V u - xstar,
            V u + (1 / 2 : ℝ) • V u + (u / 2) • (-(3 / u) • V u - gradient f (X u))⟫_ℝ)) u := by
    intro u hu
    obtain ⟨hXu, hVu⟩ := hode u hu
    have h1 : HasDerivAt (fun w => f (X w)) ⟪gradient f (X u), V u⟫_ℝ u := by
      have := (hd (X u)).hasFDerivAt.comp_hasDerivAt u hXu
      rw [grad_inner f] at this
      exact this
    have hp : HasDerivAt (fun w : ℝ => w ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have hW : HasDerivAt (fun w => X w + (w / 2) • V w - xstar)
        (V u + (1 / 2 : ℝ) • V u + (u / 2) • (-(3 / u) • V u - gradient f (X u))) u := by
      have hh : HasDerivAt (fun w : ℝ => w / 2) (1 / 2) u := by
        simpa using (hasDerivAt_id u).div_const 2
      have := (hXu.add (hh.smul hVu)).sub_const xstar
      refine this.congr_deriv ?_
      abel
    exact (hp.mul (h1.sub_const (f xstar))).add ((hW.norm_sq).const_mul 2)
  have hDle : ∀ u, 0 < u →
      2 * u * (f (X u) - f xstar) + u ^ 2 * ⟪gradient f (X u), V u⟫_ℝ
        + 2 * (2 * ⟪X u + (u / 2) • V u - xstar,
            V u + (1 / 2 : ℝ) • V u + (u / 2) • (-(3 / u) • V u - gradient f (X u))⟫_ℝ) ≤ 0 := by
    intro u hu
    have hG : f (X u) - f xstar ≤ ⟪gradient f (X u), X u - xstar⟫_ℝ := by
      have := conv_grad f hconv hd (X u) xstar
      rw [← neg_sub (X u) xstar, inner_neg_right] at this
      linarith
    have := key (gradient f (X u)) (X u - xstar) (V u) u _ hu hG
    have e : X u + (u / 2) • V u - xstar = X u - xstar + (u / 2) • V u := by abel
    rw [e]; exact this
  -- continuity of E at 0 within Ici 0
  have hc0 : ContinuousWithinAt E (Set.Ici 0) 0 := by
    have hXc : ContinuousWithinAt X (Set.Ici 0) 0 := hXd0.continuousWithinAt
    have hfX : ContinuousWithinAt (fun w => f (X w)) (Set.Ici 0) 0 :=
      (hd.continuous.continuousAt (x := X 0)).comp_continuousWithinAt hXc
    have hid : ContinuousWithinAt (fun w : ℝ => w) (Set.Ici 0) 0 := continuousWithinAt_id
    have hn : ContinuousWithinAt (fun w => ‖X w + (w / 2) • V w - xstar‖ ^ 2) (Set.Ici 0) 0 :=
      (((hXc.add ((hid.div_const 2).smul hVc0)).sub continuousWithinAt_const).norm.pow 2)
    exact ((hid.pow 2).mul (hfX.sub continuousWithinAt_const)).add
      (continuousWithinAt_const.mul hn)
  have hanti : AntitoneOn E (Set.Ici 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
    · intro u hu
      rcases (Set.mem_Ici.1 hu).eq_or_lt with h | h
      · subst h; exact hc0
      · exact (hder u h).continuousAt.continuousWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      exact (hder u hu).differentiableAt.differentiableWithinAt
    · intro u hu
      rw [interior_Ici] at hu
      rw [(hder u hu).deriv]
      exact hDle u hu
  have hEt := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 ht.le) ht.le
  have hE0 : E 0 = 2 * ‖x₀ - xstar‖ ^ 2 := by
    simp [hE, hX0, hV0]
  rw [hE0] at hEt
  have hEge : t ^ 2 * (f (X t) - f xstar) ≤ E t := by
    simp only [hE]; nlinarith [sq_nonneg ‖X t + (t / 2) • V t - xstar‖]
  rw [le_div_iff₀ (by positivity)]
  linarith

#print axioms solution
