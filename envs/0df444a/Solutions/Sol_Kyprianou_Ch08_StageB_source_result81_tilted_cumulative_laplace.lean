-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_tilted_cumulative_laplace
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:06:11.924831+00:00
-- url     : https://prove2.me/submissions/54d0837a-3262-4c50-b2cc-f9607f458495

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_cumulative_measure
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Positivity

open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (ψ : ℝ → ℝ) (q : ℝ) (hroot : IsScaleTransformDomainBridge ψ q)
    (ν : Measure ℝ) (hsupp : ν (Iio (0 : ℝ)) = 0)
    (hf : ∀ x : ℝ, ν (Iic x) < ⊤)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫⁻ y, ENNReal.ofReal (Real.exp (-s * y)) ∂ν) =
        ENNReal.ofReal (s / (ψ (Phi ψ q + s) - q))) :
    ∀ β : ℝ, 0 ≤ β → Phi ψ q < β →
      IntegrableOn
        (fun x => Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * (ν (Iic x)).toReal))
        (Ioi 0) volume ∧
      (∫ x in Ioi 0, Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * (ν (Iic x)).toReal)) =
        (ψ β - q)⁻¹ := by
  classical
  letI : IsLocallyFiniteMeasure ν :=
    ⟨fun x => ⟨Iic (x + 1), Iic_mem_nhds (lt_add_one x), hf _⟩⟩
  let v (x : ℝ) := (ν (Iic x)).toReal
  have hmono : Monotone v := fun x y hxy =>
    ENNReal.toReal_mono (hf y).ne (measure_mono (Iic_subset_Iic.mpr hxy))
  intro β hβ hlt
  let s := β - Phi ψ q
  have hs : 0 < s := sub_pos.mpr hlt
  have hsum : Phi ψ q + s = β := by simp [s]
  have hpos : 0 < ψ β - q := sub_pos.mpr ((hroot.2 β hβ).mp hlt)
  let f (x : ℝ) := Real.exp (-s * x) * v x
  have heq : (fun x => Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * (ν (Iic x)).toReal)) = f := by
    funext x
    change Real.exp (-β * x) * (Real.exp (Phi ψ q * x) * v x) =
      Real.exp (-s * x) * v x
    have hsx : -β * x + Phi ψ q * x = -s * x := by
      dsimp [s]
      ring
    rw [← mul_assoc, ← Real.exp_add, hsx]
  have hpoint (x : ℝ) : ENNReal.ofReal (f x) =
      ENNReal.ofReal (Real.exp (-s * x)) * ν (Iic x) := by
    change ENNReal.ofReal (Real.exp (-s * x) * (ν (Iic x)).toReal) = _
    rw [ENNReal.ofReal_mul (Real.exp_nonneg _), ENNReal.ofReal_toReal (hf x).ne]
  have hL : (∫⁻ x in Ioi 0, ENNReal.ofReal (f x)) =
      ENNReal.ofReal (ψ β - q)⁻¹ := by
    simp_rw [hpoint]
    rw [AvramDividend.Classical.positiveLaplace_cumulative_measure ν s hs hsupp,
      hlap s hs, hsum, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 1 / s)]
    congr 1
    field_simp [hs.ne', hpos.ne']
  have hnn : ∀ᵐ x ∂(volume.restrict (Ioi 0)), 0 ≤ f x :=
    Eventually.of_forall fun _ => mul_nonneg (Real.exp_nonneg _) ENNReal.toReal_nonneg
  have hm : Measurable f :=
    (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.mul
      hmono.measurable
  have hi : IntegrableOn f (Ioi 0) volume :=
    ⟨hm.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal hnn).2
      (hL.trans_lt ENNReal.ofReal_lt_top)⟩
  rw [heq]
  exact ⟨hi, by rw [integral_eq_lintegral_of_nonneg_ae hnn hm.aestronglyMeasurable,
    hL, ENNReal.toReal_ofReal (inv_nonneg.mpr hpos.le)]⟩
