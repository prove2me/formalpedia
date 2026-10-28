-- Prove2me | solution 1 for LagrangeRank.Debias.eq_A_1
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:03:22.476964+00:00
-- url     : https://prove2.me/submissions/86d89e6e-f7e4-4085-9fc4-0daf39d398aa

import Mathlib
import Definitions.Def_LagrangeRank_Debias_Setting

open Matrix

open LagrangeRank.Debias in
theorem solution {d : ℕ} (L f : (Fin d → ℝ) → ℝ) (OmHat OmStar : Matrix (Fin d) (Fin d) ℝ)
    (thetaHat thetaStar : Fin d → ℝ) (hfeas : f thetaHat = 0) :
    Sum.elim (estThetaD L f OmHat thetaHat - thetaStar)
        (fun _ => lam (thetaBlock OmHat (grad f thetaHat)) (grad L thetaHat) (f thetaHat))
      = thetaBlock OmStar (grad f thetaStar) *ᵥ
            Sum.elim (-grad L thetaStar) (fun _ => -f thetaStar)
        + remJ1 (thetaBlock OmHat (grad f thetaHat)) (thetaBlock OmStar (grad f thetaStar))
            (grad L) (hess L thetaHat) f (grad f) thetaHat thetaStar
        + remJ2 (thetaBlock OmStar (grad f thetaStar))
            (grad L) (hess L thetaHat) f (grad f) thetaHat thetaStar
        + remJ3 (thetaBlock OmHat (grad f thetaHat))
            (borderedHessian (hess L thetaHat) (grad f thetaHat)) thetaHat thetaStar := by
  unfold remJ1 remJ2 remJ3
  set Th := thetaBlock OmHat (grad f thetaHat) with hTh
  set Ts := thetaBlock OmStar (grad f thetaStar) with hTs
  set H := hess L thetaHat with hH
  set g := grad f thetaHat with hg
  set δ := thetaHat - thetaStar with hδ
  set v : Fin d ⊕ Unit → ℝ := Sum.elim (-grad L thetaHat + H *ᵥ δ) (fun _ => -f thetaHat + g ⬝ᵥ δ)
    with hv
  set us : Fin d ⊕ Unit → ℝ := Sum.elim (-grad L thetaStar) (fun _ => -f thetaStar) with hus
  set w : Fin d ⊕ Unit → ℝ := Sum.elim (grad L thetaStar - grad L thetaHat + H *ᵥ δ)
    (fun _ => f thetaStar - f thetaHat + g ⬝ᵥ δ) with hw
  set z : Fin d ⊕ Unit → ℝ := Sum.elim δ (fun _ => (0 : ℝ)) with hz
  set u : Fin d ⊕ Unit → ℝ := Sum.elim (-grad L thetaHat) (fun _ => -f thetaHat) with hu
  have hvw : us + w = v := by
    funext p
    cases p with
    | inl j => simp only [hus, hw, hv, Pi.add_apply, Sum.elim_inl, Pi.neg_apply, Pi.sub_apply]; ring
    | inr q => simp only [hus, hw, hv, Pi.add_apply, Sum.elim_inr]; ring
  have hSz : borderedHessian H g *ᵥ z = Sum.elim (H *ᵥ δ) (fun _ => g ⬝ᵥ δ) := by
    funext p
    cases p with
    | inl j =>
      simp [borderedHessian, hz, fromBlocks_mulVec, Function.comp_def, mulVec, dotProduct]
    | inr q =>
      simp [borderedHessian, hz, fromBlocks_mulVec, Function.comp_def, mulVec, dotProduct]
  have hvu : v - Sum.elim (H *ᵥ δ) (fun _ => g ⬝ᵥ δ) = u := by
    funext p
    cases p with
    | inl j => simp only [hv, hu, Pi.sub_apply, Sum.elim_inl, Pi.add_apply]; ring
    | inr q => simp only [hv, hu, Pi.sub_apply, Sum.elim_inr]; ring
  have e1 : Ts *ᵥ us + Ts *ᵥ w = Ts *ᵥ v := by rw [← mulVec_add, hvw]
  have e2 : Th *ᵥ v - Th *ᵥ (borderedHessian H g *ᵥ z) = Th *ᵥ u := by
    rw [← mulVec_sub, hSz, hvu]
  have hR : Ts *ᵥ us + (Th - Ts) *ᵥ v + Ts *ᵥ w + (1 - Th * borderedHessian H g) *ᵥ z
      = Th *ᵥ u + z := by
    rw [sub_mulVec, sub_mulVec, one_mulVec, ← mulVec_mulVec]
    linear_combination (norm := module) e1 + e2
  rw [hR]
  funext p
  cases p with
  | inl j =>
    simp only [Sum.elim_inl, Pi.add_apply, Pi.sub_apply, hz, hδ, estThetaD, debiased, hu, ← hTh,
      ← hg]
    simp only [mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, hfeas,
      neg_zero, mul_zero, Finset.sum_const_zero, add_zero, toBlocks₁₁, of_apply, Pi.neg_apply,
      mul_neg, Finset.sum_neg_distrib]
    ring
  | inr q =>
    simp only [Sum.elim_inr, Pi.add_apply, hz, add_zero, lam, hu, ← hTh, ← hg]
