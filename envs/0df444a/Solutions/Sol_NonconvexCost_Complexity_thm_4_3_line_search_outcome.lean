-- Prove2me | solution 1 for NonconvexCost.Complexity.thm_4_3_line_search_outcome
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-29T09:30:52.406312+00:00
-- url     : https://prove2.me/submissions/65e86cbc-6c37-4090-bc62-82dfd68570d8

import Mathlib
import Definitions.Def_NonconvexCost_Complexity_Setting
import Definitions.Def_NonconvexCost_Complexity_Algorithm
open Set
open scoped RealInnerProductSpace
namespace Queelius.NonsmoothLine
open NonconvexCost.Complexity
lemma point_distance {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (δ : ℝ) (x g : X) (hg : g ≠ 0) (t : ℝ) :
    ‖lsPoint δ x g t-x‖ = |t-δ| := by
  have hn : ‖g‖ ≠ 0 := norm_ne_zero_iff.mpr hg
  simp [lsPoint,norm_smul,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg g)),hn]
lemma oracle_mem {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ : ℝ) (x g : X) (hg : g ≠ 0) (t : ℝ) (ht : t ∈ Icc 0 δ) :
    G (lsPoint δ x g t) (‖g‖⁻¹ • g) ∈ goldstein G δ x := by
  apply subset_convexHull ℝ
  refine ⟨lsPoint δ x g t,‖g‖⁻¹ • g,?_,rfl⟩
  rw [point_distance δ x g hg t,abs_of_nonpos (sub_nonpos.mpr ht.2)]
  linarith [ht.1]
lemma oracle_angle {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (G : X → X → X) (δ ε : ℝ) (hε : 0 < ε) (x g : X) (hg : ε < ‖g‖)
    (t : ℝ) (ht : lsDeriv G δ ε x g t < 0) :
    ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),g⟫ < ‖g‖^2/2 := by
  have hn : 0 < ‖g‖ := lt_trans hε hg
  unfold lsDeriv at ht
  rw [inner_smul_right] at ht
  have ha : ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g),g⟫ / ‖g‖ < ε/2 := by
    simpa only [div_eq_mul_inv,mul_comm] using sub_neg.mp ht
  have hb := (div_lt_iff₀ hn).mp ha
  nlinarith [mul_pos (sub_pos.mpr hg) hn]
end Queelius.NonsmoothLine
namespace NonconvexCost.Complexity
 theorem _root_.solution {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    (f : X → ℝ) (G : X → X → X) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) (x g : X)
    (hg : ε < ‖g‖) (hdec : f x - f (lsPoint δ x g 0) < δ * ε / 3) :
    (lsFun f δ ε x g δ - lsFun f δ ε x g 0) / (δ - 0) < -(ε / 6) ∧
      ∀ t ∈ Icc (0 : ℝ) δ, lsDeriv G δ ε x g t < 0 →
        G (lsPoint δ x g t) (‖g‖⁻¹ • g) ∈ goldstein G δ x ∧
          ⟪G (lsPoint δ x g t) (‖g‖⁻¹ • g), g⟫ < ‖g‖ ^ 2 / 2 := by
  constructor
  · rw [sub_zero,div_lt_iff₀ hδ]
    unfold lsFun
    simp only [lsPoint,sub_self,zero_smul,add_zero,mul_zero,zero_div,sub_zero] at *
    linarith
  · intro t ht hd
    have hn : g ≠ 0 := norm_pos_iff.mp (lt_trans hε hg)
    exact ⟨Queelius.NonsmoothLine.oracle_mem G δ x g hn t ht,
      Queelius.NonsmoothLine.oracle_angle G δ ε hε x g hg t hd⟩
end NonconvexCost.Complexity
