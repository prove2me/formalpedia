-- Prove2me | solution 1 for NonconvexDRS.ADMM.theorem_5_5
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-10T21:06:08.157253+00:00
-- url     : https://prove2.me/submissions/2f7c8411-7eda-4490-8211-6d7d312c7017

import Mathlib
import Definitions.Def_NonconvexSplitting_Shared_LimitingSubdiff
import Definitions.Def_NonconvexDRS_ADMM_Setting

open NonconvexSplitting.Shared
open Filter Topology
open scoped InnerProductSpace

namespace RRAux_NonconvexDRS_ADMM_theorem_5_5

open NonconvexSplitting.Shared NonconvexDRS.ADMM

lemma shift (a b : EReal) (r1 r2 : ℝ) :
    a + (r1 : EReal) ≤ b + (r2 : EReal) ↔ a + ((r1 - r2 : ℝ) : EReal) ≤ b := by
  constructor
  · intro h
    calc a + ((r1 - r2 : ℝ) : EReal) = (a + (r1 : EReal)) + ((-r2 : ℝ) : EReal) := by
          rw [add_assoc, ← EReal.coe_add, sub_eq_add_neg]
      _ ≤ (b + (r2 : EReal)) + ((-r2 : ℝ) : EReal) := add_le_add_left h _
      _ = b := by rw [add_assoc, ← EReal.coe_add, add_neg_cancel, EReal.coe_zero, add_zero]
  · intro h
    calc a + (r1 : EReal) = (a + ((r1 - r2 : ℝ) : EReal)) + (r2 : EReal) := by
          rw [add_assoc, ← EReal.coe_add, sub_add_cancel]
      _ ≤ b + (r2 : EReal) := add_le_add_left h _

lemma real_aux (K ε t : ℝ) (hK : 0 ≤ K) (hε : 0 < ε) (ht0 : 0 ≤ t) (ht : t * (K + 1) < ε) :
    K * t ^ 2 ≤ ε * t := by nlinarith

lemma regsub {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (F : X → EReal) (x0 q : X) (K : ℝ) (hK : 0 ≤ K) (hfin : F x0 ≠ ⊤)
    (h : ∀ x', F x0 + ((-(⟪q, x' - x0⟫_ℝ + K * ‖x' - x0‖ ^ 2) : ℝ) : EReal) ≤ F x') :
    IsRegularSubgrad F x0 (-q) := by
  refine ⟨hfin, fun ε hε => ?_⟩
  have hδ : 0 < ε / (K + 1) := by positivity
  filter_upwards [Metric.ball_mem_nhds x0 hδ] with x' hx'
  rw [Metric.mem_ball, dist_eq_norm, lt_div_iff₀ (by linarith)] at hx'
  refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _) (h x')
  rw [inner_neg_left]
  have := real_aux K ε ‖x' - x0‖ hK hε (norm_nonneg _) hx'
  linarith

lemma Q {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] (β : ℝ) (c r d : P) :
    (⟪c, r⟫_ℝ + β / 2 * ‖r‖ ^ 2) - (⟪c, r + d⟫_ℝ + β / 2 * ‖r + d‖ ^ 2)
      = -(⟪c + β • r, d⟫_ℝ + β / 2 * ‖d‖ ^ 2) := by
  rw [norm_add_sq_real, inner_add_right, inner_add_left, real_inner_smul_left]
  ring

lemma R {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P] (β : ℝ) (hβ : 0 < β)
    (u0 s0 w q : P) (h : u0 - s0 = (1 / β) • q) :
    ‖u0 - s0‖ ^ 2 / (2 * (1 / β)) - ‖w - s0‖ ^ 2 / (2 * (1 / β))
      = -(⟪q, w - u0⟫_ℝ + β / 2 * ‖w - u0‖ ^ 2) := by
  have e : w - s0 = (w - u0) + (1 / β) • q := by rw [← h]; abel
  rw [e, h, norm_add_sq_real, norm_smul, inner_smul_right, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / β), real_inner_comm]
  field_simp
  ring

lemma ne_top_of {a b : EReal} (r1 r2 : ℝ) (h : a + (r1 : EReal) ≤ b + (r2 : EReal))
    (hb : b ≠ ⊤) : a ≠ ⊤ := by
  intro ha
  rw [ha, EReal.top_add_coe, top_le_iff] at h
  exact EReal.add_ne_top hb (EReal.coe_ne_top _) h

lemma sq_le_opnorm {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (A : E →L[ℝ] F) (d : E) :
    ‖A d‖ ^ 2 ≤ ‖A‖ ^ 2 * ‖d‖ ^ 2 := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (A.le_opNorm d) 2

end RRAux_NonconvexDRS_ADMM_theorem_5_5

open NonconvexDRS.ADMM in
theorem solution {m n p : ℕ} (f : EuclideanSpace ℝ (Fin m) → EReal)
    (g : EuclideanSpace ℝ (Fin n) → EReal) (hf : NonconvexDRS.Tight.IsProper f) (hg : NonconvexDRS.Tight.IsProper g)
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin p))
    (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin p)) (b : EuclideanSpace ℝ (Fin p))
    (β lam : ℝ) (hβ : 0 < β) (hlam : 0 < lam) (hsolv : SubproblemsSolvable f g A B b β)
    (x xp : EuclideanSpace ℝ (Fin m)) (y yp : EuclideanSpace ℝ (Fin p))
    (z zp : EuclideanSpace ℝ (Fin n))
    (hstep : IsADMMStep f g A B b β lam x y z xp yp zp) :
    let s := A x - (1 / β) • y
    let u := A x
    let v := b - B z
    let sp := A xp - (1 / β) • yp
    let up := A xp
    let vp := b - B zp
    (sp = s + lam • (v - u) ∧
      up ∈ NonconvexDRS.Tight.proxSet (imageFn A f) (1 / β) sp ∧
      vp ∈ NonconvexDRS.Tight.proxSet (fun t => imageFn B g (b - t)) (1 / β) ((2 : ℝ) • up - sp)) ∧
    imageFn A f up = f xp ∧
    imageFn B g (b - vp) = g zp ∧
    IsRegularSubgrad (imageFn A f) up (-yp) ∧
    IsRegularSubgrad f xp (-(ContinuousLinearMap.adjoint A yp)) ∧
    ∃ w, IsRegularSubgrad g zp w ∧
      ‖-(ContinuousLinearMap.adjoint B yp) - w‖ ≤ β * ‖B‖ * ‖A xp + B zp - b‖ := by
  open RRAux_NonconvexDRS_ADMM_theorem_5_5 in
  intro s u v sp up vp
  obtain ⟨hx, hyp, hz⟩ := hstep
  generalize hyh : y - (β * (1 - lam)) • (A x + B z - b) = yh at hx hyp
  -- f xp, g zp finite
  have hfxp : f xp ≠ ⊤ := by
    obtain ⟨x0, hx0⟩ := hf.2
    exact ne_top_of _ _ (hx x0) hx0
  have hgzp : g zp ≠ ⊤ := by
    obtain ⟨z0, hz0⟩ := hg.2
    exact ne_top_of _ _ (hz z0) hz0
  -- basic inequalities
  have hx' : ∀ x', f xp + ((-(⟪yp, A (x' - xp)⟫_ℝ + β / 2 * ‖A (x' - xp)‖ ^ 2) : ℝ) : EReal)
      ≤ f x' := by
    intro x'
    have h := (shift _ _ _ _).1 (hx x')
    have e : A x' + B z - b = (A xp + B z - b) + A (x' - xp) := by rw [map_sub]; abel
    rw [e, Q, ← hyp] at h
    exact h
  set q2 := yp + β • (A xp + B zp - b) with hq2
  have hz' : ∀ z', g zp + ((-(⟪q2, B (z' - zp)⟫_ℝ + β / 2 * ‖B (z' - zp)‖ ^ 2) : ℝ) : EReal)
      ≤ g z' := by
    intro z'
    have h := (shift _ _ _ _).1 (hz z')
    have e : A xp + B z' - b = (A xp + B zp - b) + B (z' - zp) := by rw [map_sub]; abel
    rw [e, Q] at h
    exact h
  -- (i)
  have hi : imageFn A f up = f xp := by
    show (⨅ (x' : EuclideanSpace ℝ (Fin m)) (_ : A x' = A xp), f x') = f xp
    apply le_antisymm (iInf₂_le (f := fun x' (_ : A x' = A xp) => f x') xp rfl)
    refine le_iInf₂ fun x' hx'' => ?_
    have h := hx' x'
    rw [map_sub, hx'', sub_self] at h
    simpa using h
  -- (ii)
  have hii : imageFn B g (b - vp) = g zp := by
    have e : b - vp = B zp := by simp [vp]
    rw [e]
    show (⨅ (z' : EuclideanSpace ℝ (Fin n)) (_ : B z' = B zp), g z') = g zp
    apply le_antisymm (iInf₂_le (f := fun z' (_ : B z' = B zp) => g z') zp rfl)
    refine le_iInf₂ fun z' hz'' => ?_
    have h := hz' z'
    rw [map_sub, hz'', sub_self] at h
    simpa using h
  have H3 : ∀ w, imageFn A f up + ((-(⟪yp, w - up⟫_ℝ + β / 2 * ‖w - up‖ ^ 2) : ℝ) : EReal)
      ≤ imageFn A f w := by
    intro w
    rw [hi]
    refine le_iInf₂ fun x' hx'' => ?_
    have h := hx' x'
    rwa [map_sub, hx''] at h
  have H5 : ∀ w, imageFn B g (b - vp) +
      ((-(⟪-q2, w - vp⟫_ℝ + β / 2 * ‖w - vp‖ ^ 2) : ℝ) : EReal) ≤ imageFn B g (b - w) := by
    intro w
    rw [hii]
    refine le_iInf₂ fun z' hz'' => ?_
    have e : w - vp = -(B (z' - zp)) := by
      rw [map_sub, hz'']; simp only [vp]; abel
    have h := hz' z'
    rwa [e, inner_neg_neg, norm_neg]
  refine ⟨⟨?_, ?_, ?_⟩, hi, hii, ?_, ?_, ?_⟩
  · -- sp identity
    simp only [sp, s, v, u]
    rw [hyp, ← hyh]
    have h1 : (1 / β) * (β * (1 - lam)) = 1 - lam := by field_simp
    have h2 : (1 / β) * β = 1 := by field_simp
    rw [smul_add, smul_sub, smul_smul, smul_smul, h1, h2, one_smul]
    module
  · intro w
    refine (shift _ _ _ _).2 (le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) _)
      (H3 w))
    exact R β hβ up sp w yp (by simp [up, sp])
  · intro w
    have h := H5 w
    refine (shift _ _ _ _).2 (le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 (le_of_eq ?_)) _)
      h)
    refine R β hβ vp _ w (-q2) ?_
    have h2 : (1 / β) * β = 1 := by field_simp
    simp only [vp, up, sp, hq2, smul_neg, smul_add, smul_smul, h2, one_smul]
    module
  · exact regsub _ up yp (β / 2) (by positivity) (by rw [hi]; exact hfxp) H3
  · refine regsub _ xp _ (β / 2 * ‖A‖ ^ 2) (by positivity) hfxp fun x' => ?_
    refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _) (hx' x')
    rw [ContinuousLinearMap.adjoint_inner_left]
    have := sq_le_opnorm A (x' - xp)
    have hb : 0 ≤ β / 2 := by positivity
    nlinarith
  · refine ⟨-(ContinuousLinearMap.adjoint B q2), ?_, ?_⟩
    · refine regsub _ zp _ (β / 2 * ‖B‖ ^ 2) (by positivity) hgzp fun z' => ?_
      refine le_trans (add_le_add_right (EReal.coe_le_coe_iff.2 ?_) _) (hz' z')
      rw [ContinuousLinearMap.adjoint_inner_left]
      have := sq_le_opnorm B (z' - zp)
      have hb : 0 ≤ β / 2 := by positivity
      nlinarith
    · have e : -(ContinuousLinearMap.adjoint B yp) - -(ContinuousLinearMap.adjoint B q2)
          = ContinuousLinearMap.adjoint B (β • (A xp + B zp - b)) := by
        rw [hq2, map_add]; abel
      rw [e]
      refine le_trans (ContinuousLinearMap.le_opNorm _ _) ?_
      rw [LinearIsometryEquiv.norm_map, norm_smul, Real.norm_eq_abs, abs_of_pos hβ, mul_assoc]
      exact le_of_eq (by ring)

#print axioms solution
