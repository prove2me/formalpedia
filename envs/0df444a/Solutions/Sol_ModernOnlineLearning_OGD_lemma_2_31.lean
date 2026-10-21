-- Prove2me | solution 1 for ModernOnlineLearning.OGD.lemma_2_31
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T15:16:37.696583+00:00
-- url     : https://prove2.me/submissions/030dd697-809a-4697-88d2-a2affaaa505e

import Theorems.Thm_ModernOnlineLearning_OGD_proposition_2_11
import Definitions.Def_ModernOnlineLearning_OGD_Defs

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (loss : E → ℝ) (x xn g u : E) (η : ℝ)
    (hx : x ∈ V) (hu : u ∈ V) (hη : 0 < η)
    (hg : ModernOnlineLearning.OGD.IsSubgradientOn V loss x g)
    (hxn : OnlineConvexOpt.FirstOrder.IsMetricProjection V (x - η • g) xn) :
    η * (loss x - loss u) ≤ η * inner ℝ g (x - u) ∧
      η * inner ℝ g (x - u) ≤
        (1 / 2 : ℝ) * ‖x - u‖ ^ 2 - (1 / 2 : ℝ) * ‖xn - u‖ ^ 2 +
          (η ^ 2 / 2) * ‖g‖ ^ 2 := by
  constructor
  · have hs := hg u hu
    apply mul_le_mul_of_nonneg_left _ hη.le
    simp only [inner_sub_right] at hs ⊢
    linarith
  · have hp := ModernOnlineLearning.OGD.proposition_2_11 V hV hc hv (x - η • g) xn u hxn hu
    have hsq : ‖xn - u‖ ^ 2 ≤ ‖x - η • g - u‖ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hp 2
    have heq : x - η • g - u = (x - u) - η • g := by abel
    rw [heq, norm_sub_sq_real (x - u) (η • g), real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hη, real_inner_comm g (x - u)] at hsq
    nlinarith
