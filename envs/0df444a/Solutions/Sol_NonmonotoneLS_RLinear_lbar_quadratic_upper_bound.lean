-- Prove2me | solution 1 for NonmonotoneLS.RLinear.lbar_quadratic_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T07:24:42.05835+00:00
-- url     : https://prove2.me/submissions/5ce42688-a2fc-4a69-b2ef-1067cdbff299

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_RLinear_Run
import Definitions.Def_NonmonotoneLS_RLinear_Regions
import Definitions.Def_NonmonotoneLS_RLinear_Constants
import Theorems.Thm_NonmonotoneLS_RLinear_step_segment_mem_Lbar

open scoped InnerProductSpace NNReal
open Filter

namespace NonmonotoneLS.RLinear

/-- Descent/smoothness estimate on the trial segment: if `x k ∈ 𝓛`, `0 ≤ s ≤ μ` and `∇f` is
`L`-Lipschitz on `𝓛̄`, then `f (x k + s • d k) ≤ f (x k) + s ⟨∇f (x k), d k⟩ + (L/2) s² ‖d k‖²`. -/
theorem _root_.solution {n : ℕ} (p : Shared.Params)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f)
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (k : ℕ) (s : ℝ)
    (hx : x k ∈ levelSet f (x 0)) (hs0 : 0 ≤ s) (hsμ : s ≤ p.μ)
    (L : ℝ≥0) (hLip : LipschitzOnWith L (gradient f) (Lbar p f x d)) :
    f (x k + s • d k) ≤ f (x k) + s * ⟪gradient f (x k), d k⟫_ℝ
      + (L : ℝ) / 2 * s ^ 2 * ‖d k‖ ^ 2 := by
  let v := s • d k
  let g : ℝ → ℝ := fun t => f (x k + t • v) - f (x k) -
    t * ⟪gradient f (x k), v⟫_ℝ - (L : ℝ) / 2 * t ^ 2 * ‖v‖ ^ 2
  have hf' := hf.differentiable (by norm_num)
  have hd (t : ℝ) : HasDerivAt g
      (⟪gradient f (x k + t • v), v⟫_ℝ - ⟪gradient f (x k), v⟫_ℝ -
        (L : ℝ) * t * ‖v‖ ^ 2) t := by
    have hline : HasDerivAt (fun t : ℝ => x k + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add (x k)
    have hcomp := (hf' (x k + t • v)).hasFDerivAt.comp_hasDerivAt t hline
    have hcomp' : HasDerivAt (fun t : ℝ => f (x k + t • v))
        ⟪gradient f (x k + t • v), v⟫_ℝ t := by
      rw [← (hf' (x k + t • v)).hasGradientAt.fderiv_apply]
      exact hcomp
    convert ((hcomp'.sub_const (f (x k))).sub
      ((hasDerivAt_id t).mul_const ⟪gradient f (x k), v⟫_ℝ)).sub
      ((((hasDerivAt_id t).pow 2).const_mul ((L : ℝ) / 2)).mul_const (‖v‖ ^ 2)) using 1 <;> try rfl
    all_goals simp only [id_eq]; ring
  have hbase : x k ∈ Lbar p f x d := by
    simpa using step_segment_mem_Lbar p f x d k s 0 hx hs0 hsμ (by norm_num) (by norm_num)
  have hn (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      ⟪gradient f (x k + t • v), v⟫_ℝ - ⟪gradient f (x k), v⟫_ℝ -
        (L : ℝ) * t * ‖v‖ ^ 2 ≤ 0 := by
    have hmem : x k + t • v ∈ Lbar p f x d :=
      step_segment_mem_Lbar p f x d k s t hx hs0 hsμ ht.1 ht.2
    have hlip := hLip.norm_sub_le hmem hbase
    have hnorm : ‖gradient f (x k + t • v) - gradient f (x k)‖ ≤
        (L : ℝ) * t * ‖v‖ := by
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_assoc] using hlip
    have hinner := real_inner_le_norm (gradient f (x k + t • v) - gradient f (x k)) v
    rw [inner_sub_left] at hinner
    have := mul_le_mul_of_nonneg_right hnorm (norm_nonneg v)
    nlinarith
  have hg : Differentiable ℝ g := fun t => (hd t).differentiableAt
  have hanti : AntitoneOn g (Set.Icc (0 : ℝ) 1) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc _ _) hg.continuous.continuousOn
      hg.differentiableOn
    intro t ht
    rw [(hd t).deriv]
    exact hn t (interior_subset ht)
  have hbound := hanti (by simp : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≤ 1)
  dsimp [g, v] at hbound
  simp only [one_smul, zero_smul, add_zero, zero_mul, one_mul, zero_pow,
    one_pow, mul_one, sub_self, sub_zero, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg hs0] at hbound
  nlinarith

end NonmonotoneLS.RLinear