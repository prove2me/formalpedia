-- Prove2me | solution 1 for ModernOnlineLearning.OGD.lemma_2_12
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-20T15:14:56.206856+00:00
-- url     : https://prove2.me/submissions/c1b50459-6d51-4b23-aefb-9217dbc918b9

import Theorems.Thm_ModernOnlineLearning_OGD_proposition_2_11

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (V : Set E) (hV : V.Nonempty) (hc : IsClosed V)
    (hv : Convex ℝ V) (loss : E → ℝ) (x xn g u : E) (η : ℝ)
    (hx : x ∈ V) (hu : u ∈ V) (hη : 0 < η)
    (hopen : ∃ U : Set E, IsOpen U ∧ V ⊆ U ∧ ConvexOn ℝ U loss ∧ DifferentiableOn ℝ loss U)
    (hg : HasGradientAt loss g x)
    (hxn : OnlineConvexOpt.FirstOrder.IsMetricProjection V (x - η • g) xn) :
    η * (loss x - loss u) ≤ η * inner ℝ g (x - u) ∧
      η * inner ℝ g (x - u) ≤
        (1 / 2 : ℝ) * ‖x - u‖ ^ 2 - (1 / 2 : ℝ) * ‖xn - u‖ ^ 2 +
          (η ^ 2 / 2) * ‖g‖ ^ 2 := by
  constructor
  · obtain ⟨U, hU, hVU, hf, hd⟩ := hopen
    let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x u
    have hline : ConvexOn ℝ (L ⁻¹' U) (loss ∘ L) := hf.comp_affineMap L
    have hx0 : (0 : ℝ) ∈ L ⁻¹' U := by simpa [L] using hVU hx
    have hu1 : (1 : ℝ) ∈ L ⁻¹' U := by simpa [L] using hVU hu
    have hfd : HasFDerivAt loss (InnerProductSpace.toDual ℝ E g) (L 0) := by
      simpa [L] using hg.hasFDerivAt
    have hld : HasDerivAt (loss ∘ L) (inner ℝ g (u - x)) 0 := by
      simpa [L] using hfd.comp_hasDerivAt 0 (AffineMap.hasDerivAt_lineMap (a := x) (b := u) (x := (0 : ℝ)))
    have hbound := hline.le_slope_of_hasDerivAt hx0 hu1 (by norm_num) hld
    have hs : inner ℝ g (u - x) ≤ loss u - loss x := by
      simpa [slope_def_field, L] using hbound
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
