-- Prove2me | solution 1 for MultivarScores.L2Rule.divergence_eq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:14:20.639002+00:00
-- url     : https://prove2.me/submissions/50849f15-1c9a-4da8-89d6-e596e3266331

import Mathlib
import Definitions.Def_MultivarScores_L2Rule_Setting

set_option autoImplicit false
open MeasureTheory MultivarScores.L2Rule

theorem X_S_eq {d : ℕ} (P : Measure (E d)) (w h : E d → ℝ) (y : E d)
    (h_sq_smooth : Integrable (fun z => smooth P w z ^ 2 * h z))
    (h_sq_w : Integrable (fun z => w (z - y) ^ 2 * h z))
    (h_cross : Integrable (fun z => smooth P w z * w (z - y) * h z)) :
    S P w h y = S' P w h y + ∫ z, w (z - y) ^ 2 * h z := by
  unfold S S'
  have hfun : (fun z => (smooth P w z - w (z - y)) ^ 2 * h z) =
      fun z => (smooth P w z ^ 2 * h z - 2 * (smooth P w z * w (z - y) * h z)) +
        w (z - y) ^ 2 * h z := by
    funext z; ring
  have i2 : Integrable (fun z => 2 * (smooth P w z * w (z - y) * h z)) := h_cross.const_mul 2
  have i1 : Integrable (fun z => smooth P w z ^ 2 * h z - 2 * (smooth P w z * w (z - y) * h z)) :=
    h_sq_smooth.sub i2
  rw [hfun, integral_add i1 h_sq_w, integral_sub h_sq_smooth i2, integral_const_mul]

theorem X_cross {d : ℕ} (PY : Measure (E d)) [IsProbabilityMeasure PY]
    (g w h : E d → ℝ)
    (hint : Integrable (fun p : E d × E d => g p.2 * w (p.2 - p.1) * h p.2) (PY.prod volume)) :
    ∫ s, (∫ z, g z * w (z - s) * h z) ∂PY = ∫ z, g z * smooth PY w z * h z := by
  have hswap := integral_integral_swap (μ := PY) (ν := (volume : Measure (E d)))
    (f := fun s z => g z * w (z - s) * h z) hint
  rw [hswap]
  congr 1
  funext z
  unfold smooth
  rw [← integral_const_mul, ← integral_mul_const]

theorem solution {d : ℕ} (w h : E d → ℝ) (𝒱 : Set (Measure (E d)))
    (hA : Assumption1 w h 𝒱) (PX PY : Measure (E d)) (hPX : PX ∈ 𝒱) (hPY : PY ∈ 𝒱) :
    (∫ y, S PX w h y ∂PY) - (∫ y, S PY w h y ∂PY) = L2div PX PY w h ∧
      0 ≤ L2div PX PY w h := by
  haveI := hA.isProb PY hPY
  haveI := hA.isProb PX hPX
  have hsm : ∀ (P : Measure (E d)) [IsProbabilityMeasure P], Measurable (smooth P w) := by
    intro P _
    have : Measurable (fun p : E d × E d => w (p.1 - p.2)) :=
      hA.measurable_w.comp (measurable_fst.sub measurable_snd)
    exact (this.stronglyMeasurable.integral_prod_right').measurable
  have key : ∀ P ∈ 𝒱, ∫ y, S P w h y ∂PY =
      (∫ z, smooth P w z ^ 2 * h z) - 2 * (∫ z, smooth P w z * smooth PY w z * h z)
        + ∫ y, (∫ z, w (z - y) ^ 2 * h z) ∂PY := by
    intro P hP
    haveI := hA.isProb P hP
    have e1 : ∀ y, S P w h y = ((∫ z, smooth P w z ^ 2 * h z) -
        2 * ∫ z, smooth P w z * w (z - y) * h z) + ∫ z, w (z - y) ^ 2 * h z := fun y =>
      X_S_eq P w h y (hA.sq_smooth P hP) (hA.sq_w y) (hA.cross P hP y)
    have iC : Integrable (fun y => ∫ z, smooth P w z * w (z - y) * h z) PY :=
      (hA.cross_prod P hP PY hPY).integral_prod_left
    have iW : Integrable (fun y => ∫ z, w (z - y) ^ 2 * h z) PY :=
      (hA.sq_w_prod PY hPY).integral_prod_left
    have iC2 : Integrable (fun y => 2 * ∫ z, smooth P w z * w (z - y) * h z) PY := iC.const_mul 2
    have iK : Integrable (fun _ : E d => ∫ z, smooth P w z ^ 2 * h z) PY := integrable_const _
    have iD : Integrable (fun y => (∫ z, smooth P w z ^ 2 * h z) -
        2 * ∫ z, smooth P w z * w (z - y) * h z) PY := iK.sub iC2
    have hfun : (fun y => S P w h y) = fun y => ((∫ z, smooth P w z ^ 2 * h z) -
        2 * ∫ z, smooth P w z * w (z - y) * h z) + ∫ z, w (z - y) ^ 2 * h z := funext e1
    rw [hfun, integral_add iD iW, integral_sub iK iC2, integral_const_mul,
      X_cross PY (smooth P w) w h (hA.cross_prod P hP PY hPY)]
    simp
  have hXY : Integrable (fun z => smooth PX w z * smooth PY w z * h z) := by
    have hb : Integrable (fun z => smooth PX w z ^ 2 * h z + smooth PY w z ^ 2 * h z) :=
      (hA.sq_smooth PX hPX).add (hA.sq_smooth PY hPY)
    refine hb.mono' ?_ ?_
    · exact (((hsm PX).mul (hsm PY)).mul hA.measurable_h).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      have hh := hA.h_nonneg z
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hh]
      have : |smooth PX w z * smooth PY w z| ≤ smooth PX w z ^ 2 + smooth PY w z ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (smooth PX w z + smooth PY w z),
          sq_nonneg (smooth PX w z - smooth PY w z)]
      nlinarith [mul_le_mul_of_nonneg_right this hh]
  have hL : L2div PX PY w h = (∫ z, smooth PX w z ^ 2 * h z) -
      2 * (∫ z, smooth PX w z * smooth PY w z * h z) + ∫ z, smooth PY w z ^ 2 * h z := by
    unfold L2div
    have hfun : (fun z => (smooth PX w z - smooth PY w z) ^ 2 * h z) =
        fun z => (smooth PX w z ^ 2 * h z - 2 * (smooth PX w z * smooth PY w z * h z)) +
          smooth PY w z ^ 2 * h z := by
      funext z; ring
    have i2 : Integrable (fun z => 2 * (smooth PX w z * smooth PY w z * h z)) := hXY.const_mul 2
    have i1 : Integrable (fun z => smooth PX w z ^ 2 * h z -
        2 * (smooth PX w z * smooth PY w z * h z)) := (hA.sq_smooth PX hPX).sub i2
    rw [hfun, integral_add i1 (hA.sq_smooth PY hPY), integral_sub (hA.sq_smooth PX hPX) i2,
      integral_const_mul]
  have hYY : ∫ z, smooth PY w z * smooth PY w z * h z = ∫ z, smooth PY w z ^ 2 * h z := by
    congr 1; funext z; ring
  refine ⟨?_, ?_⟩
  · rw [key PX hPX, key PY hPY, hL, hYY]
    ring
  · exact integral_nonneg fun z => mul_nonneg (sq_nonneg _) (hA.h_nonneg z)
