-- Prove2me | solution 1 for NestedSA.NASA.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:35:37.737986+00:00
-- url     : https://prove2.me/submissions/fe92c697-68de-40d1-90e6-858af9194f60

import Definitions.Def_NestedSA_NASA_Model
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

open NestedSA.NASA

namespace D24Composite

lemma gradient_difference_norm {k : ℕ} (h : EuclideanSpace ℝ (Fin k) → ℝ)
    (x y : EuclideanSpace ℝ (Fin k)) :
    ‖gradient h x - gradient h y‖ = ‖fderiv ℝ h x - fderiv ℝ h y‖ := by
  simp only [gradient, ← map_sub, LinearIsometryEquiv.norm_map]

end D24Composite

theorem solution {n m : ℕ} (f : EuclideanSpace ℝ (Fin m) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)) (Lf Lg Ldf Ldg : ℝ)
    (hA2 : Assumption2 f g Lf Lg Ldf Ldg) (x x' : EuclideanSpace ℝ (Fin n)) :
    ‖gradF f g x - gradF f g x'‖ ≤ LgradF Lf Lg Ldf Ldg * ‖x - x'‖ := by
  have hfl : LipschitzWith ⟨Lf, hA2.Lf_nonneg⟩ f := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro u v
    change ‖f u - f v‖ ≤ Lf * ‖u - v‖
    simpa only [Real.norm_eq_abs] using hA2.lip_f u v
  have hgl : LipschitzWith ⟨Lg, hA2.Lg_nonneg⟩ g :=
    lipschitzWith_iff_norm_sub_le.mpr hA2.lip_g
  have hfn (u : EuclideanSpace ℝ (Fin m)) : ‖fderiv ℝ f u‖ ≤ Lf :=
    norm_fderiv_le_of_lipschitz ℝ hfl
  have hgn (u : EuclideanSpace ℝ (Fin n)) : ‖fderiv ℝ g u‖ ≤ Lg :=
    norm_fderiv_le_of_lipschitz ℝ hgl
  have hfd := hA2.contDiff_f.differentiable (by norm_num)
  have hgd := hA2.contDiff_g.differentiable (by norm_num)
  have hchain (z : EuclideanSpace ℝ (Fin n)) :
      fderiv ℝ (fun y => f (g y)) z = (fderiv ℝ f (g z)).comp (fderiv ℝ g z) :=
    fderiv_comp z (hfd (g z)) (hgd z)
  have hsplit :
      (fderiv ℝ f (g x)).comp (fderiv ℝ g x) -
        (fderiv ℝ f (g x')).comp (fderiv ℝ g x') =
      (fderiv ℝ f (g x) - fderiv ℝ f (g x')).comp (fderiv ℝ g x) +
        (fderiv ℝ f (g x')).comp (fderiv ℝ g x - fderiv ℝ g x') := by
    ext z
    simp
  have hdf : ‖fderiv ℝ f (g x) - fderiv ℝ f (g x')‖ ≤ Ldf * Lg * ‖x - x'‖ := by
    rw [← D24Composite.gradient_difference_norm]
    exact (hA2.lip_gradf (g x) (g x')).trans
      (by simpa only [mul_assoc] using
        mul_le_mul_of_nonneg_left (hA2.lip_g x x') hA2.Ldf_nonneg)
  unfold gradF
  rw [D24Composite.gradient_difference_norm, hchain, hchain, hsplit]
  calc
    _ ≤ ‖(fderiv ℝ f (g x) - fderiv ℝ f (g x')).comp (fderiv ℝ g x)‖ +
          ‖(fderiv ℝ f (g x')).comp (fderiv ℝ g x - fderiv ℝ g x')‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ f (g x) - fderiv ℝ f (g x')‖ * ‖fderiv ℝ g x‖ +
          ‖fderiv ℝ f (g x')‖ * ‖fderiv ℝ g x - fderiv ℝ g x'‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _) (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ (Ldf * Lg * ‖x - x'‖) * Lg + Lf * (Ldg * ‖x - x'‖) := by
      apply add_le_add
      · exact mul_le_mul hdf (hgn x) (norm_nonneg _)
          (mul_nonneg (mul_nonneg hA2.Ldf_nonneg hA2.Lg_nonneg) (norm_nonneg _))
      · exact mul_le_mul (hfn (g x')) (hA2.lip_fderivg x x') (norm_nonneg _) hA2.Lf_nonneg
    _ = LgradF Lf Lg Ldf Ldg * ‖x - x'‖ := by unfold LgradF; ring

#print axioms solution
