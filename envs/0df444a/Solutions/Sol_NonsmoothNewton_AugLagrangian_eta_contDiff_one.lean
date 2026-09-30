-- Prove2me | solution 1 for NonsmoothNewton.AugLagrangian.eta_contDiff_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T08:40:38.372318+00:00
-- url     : https://prove2.me/submissions/8e6dfcf2-1f63-42a1-84e0-2ef864027300

import Mathlib
import Definitions.Def_NonsmoothNewton_Shared_clarkeJac
import Definitions.Def_NonsmoothNewton_AugLagrangian_SemismoothAt
import Definitions.Def_NonsmoothNewton_AugLagrangian_augLagrangian

open scoped Topology
open Filter Set

namespace NonsmoothNewton.AugLagrangian

/-- `eta r g = -(1/(2r)) * s^2 + (1/(2r)) * (max 0 (s + r*g x))^2`.

On the branch `0 ≤ s + r*g x` the positive part is the identity, expanding to
`s*g x + (r/2)(g x)^2`; on the other it vanishes, leaving `-(1/(2r)) s^2`. -/
private theorem eta_eq_sq {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) :
    eta r g = fun z : EuclideanSpace ℝ (Fin n) × ℝ =>
      -(1 / (2 * r)) * z.2 ^ 2 + (1 / (2 * r)) * (max 0 (z.2 + r * g z.1)) ^ 2 := by
  funext z
  show phi r (g z.1) z.2 = _
  have hz : phi r (g z.1) z.2
      = if 0 ≤ z.2 + r * g z.1 then z.2 * g z.1 + r / 2 * g z.1 ^ 2
        else -(1 / (2 * r)) * z.2 ^ 2 := by
    unfold phi
    by_cases hs : 0 ≤ z.2 + r * g z.1 <;> simp [hs]
  by_cases h : 0 ≤ z.2 + r * g z.1
  · rw [hz, if_pos h, show (max 0 (z.2 + r * g z.1)) = z.2 + r * g z.1 from
        by simpa [max_comm] using max_eq_left h]
    field_simp
    ring
  · rw [hz, if_neg h, show (max 0 (z.2 + r * g z.1)) = 0 from
        by simpa [max_comm] using max_eq_right (le_of_not_ge h)]
    ring

/-- `t ↦ (max 0 t) ^ 2` is `C¹` with derivative `t ↦ 2 * max 0 t`.

`max 0 t` is not differentiable at `0`, so no product rule through it is used.
Off zero, eventual agreement transfers the derivative of `t ^ 2` (for
`t₀ > 0`) or of the constant `0` (for `t₀ < 0`), changing only the function.
At `t₀ = 0`, `hasDerivAt_iff_tendsto` reduces matters to
`‖s‖⁻¹ * (max 0 s) ^ 2 → 0`; this is non-negative and, by
`(max 0 s) ^ 2 ≤ s ^ 2`, at most `|s|`, so `squeeze_zero` applies. -/
private theorem sq_pospart_contDiff : ContDiff ℝ 1 (fun t : ℝ => (max 0 t) ^ 2) := by
  have hsq : ∀ s : ℝ, (max 0 s) ^ 2 ≤ s ^ 2 := by
    intro s
    by_cases hs : 0 ≤ s
    · have hmax : max 0 s = s := by simpa [max_comm] using max_eq_left hs
      simpa [hmax]
    · rw [show (max 0 s) = 0 from
          by simpa [max_comm] using max_eq_right (le_of_not_ge hs)]
      simpa using sq_nonneg s
  have hderiv : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (max 0 s) ^ 2) (2 * max 0 t) t := by
    intro t
    by_cases ht : 0 < t
    · -- A positive point: eventual agreement with the smooth `t ^ 2`.
      have hopen : Set.Ioi (0 : ℝ) ∈ 𝓝 t := isOpen_Ioi.mem_nhds ht
      have hnear : (fun s : ℝ => (max 0 s) ^ 2) =ᶠ[𝓝 t] fun s : ℝ => s ^ 2 := by
        filter_upwards [hopen] with s hs
        have hs' : 0 < s :=
          (show 0 < s from (mem_Ioi.mp hs))
        have hmax : max 0 s = s := by
          simpa [max_comm] using max_eq_left hs'.le
        simp [hmax]
      have h := ((hasDerivAt_id t).pow 2).congr_of_eventuallyEq hnear
      -- `HasDerivAt.pow` reports `(2 : ℝ) * id t ^ (2 - 1) * id 1`; change only
      -- the derivative value, with `congr_deriv` rather than `rw`.
      refine h.congr_deriv ?_
      have hmax : max 0 t = t := by simpa [max_comm] using max_eq_left ht.le
      simp only [id_eq, smul_eq_mul, one_mul, hmax]
      norm_num
    · -- A non-positive point: the derivative is the constant `0`.
      have hzero : max 0 t = 0 := by
        simpa [max_comm] using max_eq_right (le_of_not_gt ht)
      by_cases ht0 : t = 0
      · -- The touch point, via the `tendsto` characterisation of `HasDerivAt`.
        subst ht0
        refine (hasDerivAt_iff_tendsto (𝕜 := ℝ)).2 ?_
        -- The remainder is `‖s‖⁻¹ * ‖(max 0 s) ^ 2 - 0 - s * 0‖`, i.e. uniformly
        -- `‖s‖⁻¹ * (max 0 s) ^ 2`.
        have hsimple : Tendsto (fun s : ℝ => ‖s‖⁻¹ * (max 0 s) ^ 2) (𝓝 (0 : ℝ)) (𝓝 0) := by
          have habs : Tendsto (fun s : ℝ => |s|) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
            simpa using (_root_.continuous_abs.continuousAt : ContinuousAt (|·|) (0 : ℝ)).tendsto
          refine squeeze_zero (f := fun s : ℝ => ‖s‖⁻¹ * (max 0 s) ^ 2) (g := fun s : ℝ => |s|)
            (fun s => mul_nonneg (inv_nonneg.mpr (norm_nonneg s)) (sq_nonneg (max 0 s)))
            (fun s => ?_) habs
          rcases eq_or_ne s 0 with hs | hs
          · simp [hs]
          · have hspos : 0 < |s| := abs_pos.mpr hs
            have hq : (max 0 s) ^ 2 ≤ |s| * |s| := by
              rw [← Real.norm_eq_abs]; simpa [sq] using hsq s
            simpa only [Real.norm_eq_abs] using (inv_mul_le_iff₀ hspos).2 hq
        refine hsimple.congr' (Eventually.of_forall fun s => ?_)
        show ‖s‖⁻¹ * (max 0 s) ^ 2
            = ‖s - (0 : ℝ)‖⁻¹ *
              ‖(fun x : ℝ => (max 0 x) ^ 2) s - (fun x : ℝ => (max 0 x) ^ 2) 0
                - (s - 0) • (2 * max 0 0)‖
        have hzero0 : (max 0 (0 : ℝ)) ^ 2 = (0 : ℝ) := by simp
        have hzero1 : (2 * max 0 (0 : ℝ)) = (0 : ℝ) := by simp
        rw [show (fun x : ℝ => (max 0 x) ^ 2) 0 = 0 by simp [hzero0],
          hzero1, smul_eq_mul, mul_zero, sub_zero, sub_zero]
        have hb : (fun x : ℝ => (max 0 x) ^ 2) s = (max 0 s) ^ 2 := rfl
        rw [hb]
        have hs : 0 ≤ (max 0 s) ^ 2 := sq_nonneg _
        simp only [Real.norm_eq_abs, sub_zero, abs_of_nonneg hs]
      · -- A strictly negative point: eventual agreement with the constant `0`.
        have hlt : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
        have hopen : Set.Iio (0 : ℝ) ∈ 𝓝 t := isOpen_Iio.mem_nhds hlt
        have hnear : (fun s : ℝ => (max 0 s) ^ 2) =ᶠ[𝓝 t] fun _ : ℝ => (0 : ℝ) := by
          filter_upwards [hopen] with s hs
          have hs' : s < 0 :=
            (show s < 0 from (mem_Iio.mp hs))
          have hmax : max 0 s = 0 := by
            simpa [max_comm] using max_eq_right hs'.le
          simp [hmax]
        have h := (hasDerivAt_zero (x := t)).congr_of_eventuallyEq hnear
        refine h.congr_deriv ?_
        simp [hzero, max_eq_right (le_of_not_gt ht)]
  refine contDiff_one_iff_deriv.mpr ⟨?_, ?_⟩
  · exact fun t => (hderiv t).differentiableAt
  · rw [deriv_eq hderiv]
    exact continuous_const.mul (continuous_const.max continuous_id)

/-- The squared positive part of a `C¹` function is `C¹`. -/
private theorem sq_max_contDiff {n : ℕ}
    (u : EuclideanSpace ℝ (Fin n) × ℝ → ℝ) (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (max 0 (u z)) ^ 2) :=
  sq_pospart_contDiff.comp hu

end NonsmoothNewton.AugLagrangian

open NonsmoothNewton.AugLagrangian

theorem solution {n : ℕ} (r : ℝ) (hr : 0 < r)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ContDiff ℝ 1 g) :
    ContDiff ℝ 1 (eta r g) := by
  have hu : ContDiff ℝ 1 (fun z : EuclideanSpace ℝ (Fin n) × ℝ => z.2 + r * g z.1) := by
    fun_prop
  have hsq : ContDiff ℝ 1
      (fun z : EuclideanSpace ℝ (Fin n) × ℝ => (max 0 (z.2 + r * g z.1)) ^ 2) :=
    sq_max_contDiff _ hu
  rw [eta_eq_sq r hr g]
  fun_prop
