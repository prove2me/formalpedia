-- Prove2me | solution 1 for OAI.CubicTorus.cmc_linearized_holder_gradient
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T17:18:16.157732+00:00
-- url     : https://prove2.me/submissions/cf6a7b97-0549-4253-8637-ca4cd73ea072

import Mathlib
import Definitions.Def_OAIQ079A003

section
-- module Solutions.OAIQ079_CT.Compat
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_UnitAngle
attribute [-instance] _root_.OAI.CubicTorus.circle_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Interval
namespace CubicTorus

lemma integral_square_le_mass {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable f μ) (hfsq : Integrable (fun x ↦ f x ^ 2) μ) :
    (∫ x, f x ∂μ) ^ 2 ≤ μ.real univ * ∫ x, f x ^ 2 ∂μ := by
  let m := μ.real univ
  let q := ∫ x, f x ∂μ
  have hm : 0 ≤ m := measureReal_nonneg
  by_cases hm0 : m = 0
  · have hμ0 : μ = 0 := by
      apply Measure.measure_univ_eq_zero.mp
      exact (ENNReal.toReal_eq_zero_iff _).mp hm0 |>.resolve_right (measure_ne_top μ univ)
    simp [hμ0]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hi : Integrable (fun x ↦ f x ^ 2 - (2 * (q / m)) * f x) μ :=
    hfsq.sub (hf.const_mul _)
  have hp : 0 ≤ ∫ x, f x ^ 2 - (2 * (q / m)) * f x + (q / m) ^ 2 ∂μ := by
    apply integral_nonneg
    intro x
    change 0 ≤ f x ^ 2 - 2 * (q / m) * f x + (q / m) ^ 2
    nlinarith [sq_nonneg (f x - q / m)]
  rw [integral_add hi (integrable_const ((q / m) ^ 2)),
    integral_sub hfsq (hf.const_mul (2 * (q / m))), integral_const_mul, integral_const,
    smul_eq_mul] at hp
  change 0 ≤ (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 at hp
  have heq : (∫ x, f x ^ 2 ∂μ) - 2 * (q / m) * q + m * (q / m) ^ 2 =
      (∫ x, f x ^ 2 ∂μ) - q ^ 2 / m := by field_simp; ring
  rw [heq] at hp
  exact (div_le_iff₀ hmpos).mp (by linarith : q ^ 2 / m ≤ ∫ x, f x ^ 2 ∂μ) |>.trans_eq (mul_comm _ _)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVScaledFlux
attribute [-instance] _root_.OAI.CubicTorus.graphSmoothingMeasure_probability _root_.OAI.CubicTorus.plane_hausdorff_two_haar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ball_real {s : ℝ} (hs : 0 ≤ s) :
    (volume : Measure Plane).real (Metric.ball 0 s) = Real.pi * s ^ 2 := by
  simp only [Measure.real, EuclideanSpace.volume_ball_fin_two, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hs, ENNReal.toReal_ofReal Real.pi_pos.le]
  ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_BVNormalTiltMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma laplacian_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ (f ∘ L) x = Δ f (L x) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis (f ∘ L)
    (stdOrthonormalBasis ℝ X),
    InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis f
      ((stdOrthonormalBasis ℝ X).map L)]
  apply Finset.sum_congr rfl
  intro i _
  have hh := L.toContinuousLinearEquiv.toContinuousLinearMap.iteratedFDeriv_comp_right hf x
    (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2)
  have hh' := congrArg (fun A ↦ A ![(stdOrthonormalBasis ℝ X) i,
    (stdOrthonormalBasis ℝ X) i]) hh
  have hv : (fun j : Fin 2 ↦ L (![ (stdOrthonormalBasis ℝ X) i,
      (stdOrthonormalBasis ℝ X) i] j)) =
      ![L ((stdOrthonormalBasis ℝ X) i), L ((stdOrthonormalBasis ℝ X) i)] := by
    funext j
    fin_cases j <;> rfl
  simpa [ContinuousMultilinearMap.compContinuousLinearMap_apply, Function.comp_def, hv] using hh'

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma fderiv_fderiv_apply {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (x u v : X) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x u = fderiv ℝ (fderiv ℝ f) x u v := by
  rw [fderiv_clm_apply ((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable
    (by simp) |>.differentiableAt) (differentiableAt_const v)]
  simp

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_eq_sum_directional {f : X → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : X) :
    Δ f x = ∑ i, fderiv ℝ (fun y ↦ fderiv ℝ f y ((stdOrthonormalBasis ℝ X) i)) x
      ((stdOrthonormalBasis ℝ X) i) := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis]
  apply Finset.sum_congr rfl
  intro i _
  rw [iteratedFDeriv_two_apply, fderiv_fderiv_apply hf]
  rfl

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_tsupport_subset {f : X → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    tsupport (Δ f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hn
  apply hx
  rw [laplacian_eq_sum_directional hf]
  apply Finset.sum_eq_zero
  intro i _
  rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hn ((tsupport_fderiv_apply_subset ℝ _ ) hh))]
  rfl

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma fderiv_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x v : X) :
    fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x v =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v)) x := by
  rw [(hs.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf
    (hk.of_le (by simp)) x).fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hf (hs.fderiv ℝ)
    (hk.continuous_fderiv (by simp)) x v

theorem laplacian_compact_convolution {f k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) (x : X) :
    Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] Δ k) x := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  rw [laplacian_eq_sum_directional hc, convolution_mul]
  simp_rw [laplacian_eq_sum_directional hk, Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    let v := (stdOrthonormalBasis ℝ X) i
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y v) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    have he : (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) =
        f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (fun y ↦ fderiv ℝ k y v) :=
      funext (fun y ↦ fderiv_compact_convolution hf hk hs y v)
    change fderiv ℝ (fun y ↦ fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y v) x v = _
    rw [he, fderiv_compact_convolution hf hd (hs.fderiv_apply ℝ v)]
    rfl
  · intro i _
    have hd : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ k y ((stdOrthonormalBasis ℝ X) i)) :=
      (hk.fderiv_right (by simp)).clm_apply contDiff_const
    exact ((hs.fderiv_apply ℝ _).fderiv_apply ℝ _).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) hf
      ((hd.continuous_fderiv (by simp)).clm_apply continuous_const) x

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_translate {k : X → ℝ} (a x : X) :
    Δ (fun y ↦ k (a + y)) x = Δ k (a + x) := by
  simp only [InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis,
    iteratedFDeriv_comp_add_left]

omit [MeasurableSpace X] [BorelSpace X] in
lemma laplacian_reflect_translate {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (a x : X) :
    Δ (fun y ↦ k (a - y)) x = Δ k (a - x) := by
  let L : X ≃ₗᵢ[ℝ] X := LinearIsometryEquiv.neg ℝ
  have hh := laplacian_comp_isometry L (hk.comp ((contDiff_const (c := a)).add contDiff_id)) x
  change Δ (fun y ↦ k (a + -y)) x = Δ (fun y ↦ k (a + y)) (-x) at hh
  rw [laplacian_translate] at hh
  simpa only [sub_eq_add_neg] using hh

theorem weak_harmonic_convolution {f k : X → ℝ} {Ω W : Set X}
    (hf : LocallyIntegrable f μ)
    (hweak : ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y ∂μ) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    (hW : IsOpen W)
    (hkernel : ∀ x ∈ W, tsupport (fun y ↦ k (x - y)) ⊆ Ω) :
    InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) W := by
  have hc := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf hk
  have hz (x : X) (hx : x ∈ W) : Δ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x = 0 := by
    rw [laplacian_compact_convolution hf hk hs, convolution_mul]
    have hp : HasCompactSupport (fun y ↦ k (x - y)) := by
      exact hs.comp_homeomorph (Homeomorph.subLeft x)
    have hh := hweak (fun y ↦ k (x - y)) (hk.comp (contDiff_const.sub contDiff_id)) hp
      (hkernel x hx)
    simpa only [laplacian_reflect_translate hk] using hh
  intro x hx
  refine ⟨(hc.of_le (show (2 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) from by norm_cast)).contDiffAt, ?_⟩
  filter_upwards [hW.mem_nhds hx] with y hy
  exact hz y hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma harmonic_angular_integral {h : ℂ → ℝ} {c : ℂ} {r : ℝ}
    (hh : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c |r|)) :
    (∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) = 2 * Real.pi * h c := by
  have hm := hh.circleAverage_eq
  rw [Real.circleAverage_eq_integral_add (-Real.pi),
    intervalIntegral.integral_comp_add_right (fun θ ↦ h (circleMap c r θ))] at hm
  norm_num only [zero_add] at hm
  have he : 2 * Real.pi + -Real.pi = Real.pi := by ring
  rw [he, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    integral_Ioc_eq_integral_Ioo] at hm
  simp only [smul_eq_mul] at hm
  have hp : 2 * Real.pi ≠ 0 := by positivity
  calc
    _ = (2 * Real.pi) * ((2 * Real.pi)⁻¹ *
        ∫ θ in Ioo (-Real.pi) Real.pi, h (circleMap c r θ)) := by field_simp
    _ = _ := by rw [hm]

lemma add_polarCoord_eq_circleMap (c : ℂ) (r θ : ℝ) :
    c + Complex.polarCoord.symm (r, θ) = circleMap c r θ := by
  simp [circleMap, Complex.polarCoord_symm_apply, Complex.exp_mul_I, mul_add]

theorem harmonic_radial_mean {h : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (∫ z : ℂ, κ ‖z‖ * h (c + z)) = h c * ∫ z : ℂ, κ ‖z‖ := by
  let S : Set (ℝ × ℝ) := Ioc 0 R ×ˢ Ioo (-Real.pi) Real.pi
  let T : Set (ℝ × ℝ) := Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi
  have hST : S ⊆ T := by intro p hp; exact ⟨hp.1.1, hp.2⟩
  have hTm : MeasurableSet T := measurableSet_Ioi.prod measurableSet_Ioo
  have hpcont : Continuous (Complex.polarCoord.symm) := by
    change Continuous (fun p : ℝ × ℝ ↦ _)
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  have hF : Continuous (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) :=
    continuous_fst.mul ((hk.comp continuous_fst.abs).mul
      (hh.comp (continuous_const.add hpcont)))
  have hG : Continuous (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) :=
    continuous_fst.mul (hk.comp continuous_fst.abs)
  have hSS : S ⊆ Icc (0, -Real.pi) (R, Real.pi) := by
    intro p hp
    exact ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2, hp.2.2.le⟩⟩
  have hFi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) S :=
    hF.integrableOn_Icc.mono_set hSS
  have hGi : IntegrableOn (fun p : ℝ × ℝ ↦ p.1 * κ |p.1|) S :=
    hG.integrableOn_Icc.mono_set hSS
  have hangle (r : ℝ) (hr : r ∈ Ioc 0 R) :
      (∫ θ in Ioo (-Real.pi) Real.pi, h (c + Complex.polarCoord.symm (r, θ))) =
        2 * Real.pi * h c := by
    simp_rw [add_polarCoord_eq_circleMap]
    apply harmonic_angular_integral
    apply harm.mono
    exact Metric.closedBall_subset_closedBall (by simpa only [abs_of_pos hr.1] using hr.2)
  rw [← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖ * h (c + z)),
    ← Complex.integral_comp_polarCoord_symm (fun z ↦ κ ‖z‖)]
  simp only [Complex.norm_polarCoord_symm, smul_eq_mul]
  change (∫ p in T, p.1 * (κ |p.1| * h (c + Complex.polarCoord.symm p))) =
    h c * ∫ p in T, p.1 * κ |p.1|
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hTm hST (fun p hp ↦ ?_)]
  · simp only [Measure.volume_eq_prod] at hFi hGi ⊢
    dsimp only [S] at hFi hGi ⊢
    rw [setIntegral_prod _ hFi, setIntegral_prod _ hGi, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro r hr
    simp_rw [← mul_assoc, integral_const_mul, hangle r hr]
    simp only [integral_const, Measure.real, Measure.restrict_apply_univ, Real.volume_Ioo,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos] : 0 ≤ Real.pi - -Real.pi),
      smul_eq_mul]
    ring
  all_goals
    have hr : R < p.1 := by
      by_contra hn
      exact hp.2 ⟨⟨hp.1.1, le_of_not_gt hn⟩, hp.1.2⟩
    simp only [abs_of_pos (show 0 < p.1 from hp.1.1), hs p.1 hr, zero_mul, mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem exists_radial_smoothing_kernel {R : ℝ} (hR : 0 < R) :
    ∃ (k : ℂ → ℝ) (κ : ℝ → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) k ∧ HasCompactSupport k ∧
      (∀ z, k z = κ ‖z‖) ∧ Continuous κ ∧ (∀ r, R < r → κ r = 0) ∧
      tsupport k ⊆ Metric.closedBall 0 R ∧ (∫ z, k z) = 1 := by
  let b : ℂ → ℝ := fun z ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).toFun 2 ((2 / R) • z)
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := by
    have hg : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ ↦ ((2 : ℝ), (2 / R) • z)) :=
      contDiff_const.prodMk ((contDiff_const (c := (2 / R : ℝ))).smul contDiff_id)
    have ht : ∀ z : ℂ, ((2 : ℝ), (2 / R) • z) ∈ Ioi (1 : ℝ) ×ˢ (univ : Set ℂ) :=
      fun _ ↦ ⟨by norm_num, mem_univ _⟩
    exact (ContDiffBumpBase.ofInnerProductSpace ℂ).smooth.comp_contDiff hg ht
  have hbformula (z : ℂ) : b z = Real.smoothTransition (2 - (2 / R) * ‖z‖) := by
    simp [b, ContDiffBumpBase.ofInnerProductSpace, Real.norm_eq_abs, abs_of_pos hR, show (2 : ℝ) - 1 = 1 from by norm_num]
  have hzero (r : ℝ) (hr : R < r) : Real.smoothTransition (2 - (2 / R) * r) = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    have hh : 2 < (2 / R) * r := by
      have := (mul_lt_mul_of_pos_left hr (by positivity : 0 < 2 / R))
      field_simp at this ⊢
      nlinarith
    linarith
  have hbs : tsupport b ⊆ Metric.closedBall 0 R := by
    apply closure_minimal _ Metric.isClosed_closedBall
    intro z hz
    by_contra hn
    have hr : R < ‖z‖ := by simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hn
    exact hz (by rw [hbformula, hzero _ hr])
  have hbc : HasCompactSupport b := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hbs
  have hbpos : 0 < ∫ z, b z := by
    apply hb.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hbc
      (fun _ ↦ (ContDiffBumpBase.ofInnerProductSpace ℂ).mem_Icc _ _ |>.1)
    rw [hbformula 0]
    norm_num [Real.smoothTransition.one_of_one_le]
  let k : ℂ → ℝ := fun z ↦ b z / ∫ y, b y
  let κ : ℝ → ℝ := fun r ↦ Real.smoothTransition (2 - (2 / R) * r) / ∫ y, b y
  have hks : tsupport k ⊆ Metric.closedBall 0 R := by
    change tsupport (fun z ↦ b z * (∫ y, b y)⁻¹) ⊆ _
    exact tsupport_mul_subset_left.trans hbs
  have hkc : HasCompactSupport k := (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset
    isClosed_closure hks
  refine ⟨k, κ, hb.div_const _, hkc, ?_, ?_, ?_, hks, ?_⟩
  · intro z
    exact congrArg (fun t : ℝ ↦ t / ∫ y, b y) (hbformula z)
  · exact (Real.smoothTransition.continuous.comp
      (continuous_const.sub (continuous_const.mul continuous_id))).div_const _
  · intro r hr
    simp only [κ, hzero r hr, zero_div]
  · dsimp only [k]
    rw [integral_div, div_self hbpos.ne']

lemma harmonic_radial_convolution {h k : ℂ → ℝ} {κ : ℝ → ℝ} {c : ℂ} {R : ℝ}
    (hh : Continuous h) (hk : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hs : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1)
    (harm : InnerProductSpace.HarmonicOnNhd h (Metric.closedBall c R)) :
    (h ⋆[ContinuousLinearMap.mul ℝ ℝ] k) c = h c := by
  rw [convolution_eq_swap, ← integral_neg_eq_self]
  simp only [ContinuousLinearMap.mul_apply']
  simp only [hk, norm_neg, sub_neg_eq_add, mul_comm (h _)]
  rw [harmonic_radial_mean hh hc hs harm]
  have hi' : (∫ z : ℂ, κ ‖z‖) = 1 := by simpa only [hk] using hi
  rw [hi', mul_one]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

lemma real_convolution_comm (f g : X → ℝ) :
    f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g = g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] f := by
  ext x
  rw [convolution_mul_swap, convolution_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun _ ↦ mul_comm _ _)

lemma compact_convolution_assoc {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] (g ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k)) x := by
  apply convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (fun a b c ↦ mul_assoc a b c) hf.aestronglyMeasurable
    hg.aestronglyMeasurable hk.aestronglyMeasurable
  · exact Eventually.of_forall (hgs.convolutionExists_right _ hf hg)
  · exact Eventually.of_forall (hks.norm.convolutionExists_right _ hg.norm.locallyIntegrable hk.norm)
  · exact (hgs.norm.convolution (ContinuousLinearMap.mul ℝ ℝ) hks.norm).convolutionExists_right _
      (fun x ↦ (hf x).norm) (hks.norm.continuous_convolution_right _ hg.norm.locallyIntegrable hk.norm) x

lemma compact_convolutions_commute {f g k : X → ℝ} (hf : LocallyIntegrable f μ)
    (hg : Continuous g) (hgs : HasCompactSupport g)
    (hk : Continuous k) (hks : HasCompactSupport k) (x : X) :
    ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x =
      ((f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] g) x := by
  rw [compact_convolution_assoc hf hg hgs hk hks,
    compact_convolution_assoc hf hk hks hg hgs, real_convolution_comm g k]

omit [NormedSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in

lemma reflected_tsupport_subset_ball {k : X → ℝ} {c x : X} {r R : ℝ}
    (hk : tsupport k ⊆ Metric.closedBall 0 r) (hx : dist x c + r < R) :
    tsupport (fun y ↦ k (x - y)) ⊆ Metric.ball c R := by
  have hs : tsupport (fun y ↦ k (x - y)) ⊆
      (fun y ↦ x - y) ⁻¹' tsupport k := tsupport_comp_subset_preimage k (by fun_prop)
  intro y hy
  have ht := hk (hs hy)
  rw [Metric.mem_closedBall, dist_zero_right, ← dist_eq_norm] at ht
  rw [Metric.mem_ball]
  calc
    dist y c ≤ dist y x + dist x c := dist_triangle _ _ _
    _ = dist x y + dist x c := by rw [dist_comm y x]
    _ ≤ r + dist x c := by linarith
    _ < R := by linarith

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Compactness_BVWeyl
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

lemma planarMollifier_tendsto : Tendsto (fun i ↦ (planarMollifier i).rOut) atTop (𝓝 0) := by
  simpa only [planarMollifier, mul_one, mul_div, mul_zero] using
    (tendsto_const_nhds (x := (2 : ℝ))).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

lemma planarMollifier_ratio (i : ℕ) :
    (planarMollifier i).rOut ≤ 2 * (planarMollifier i).rIn := by
  dsimp only [planarMollifier]
  rw [mul_div, mul_one]

theorem weak_harmonic_radial_reproduction {f k : ℂ → ℝ} {κ : ℝ → ℝ}
    {Ω : Set ℂ} {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hball : Metric.ball c (4 * R) ⊆ Ω) (hf : LocallyIntegrable f)
    (hweak : ∀ φ : ℂ → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Ω → (∫ y, f y * Δ φ y) = 0)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hks : HasCompactSupport k)
    (hrad : ∀ z, k z = κ ‖z‖) (hc : Continuous κ)
    (hκ : ∀ r, R < r → κ r = 0) (hi : (∫ z, k z) = 1) :
    f =ᵐ[volume.restrict (Metric.ball c R)] f ⋆[ContinuousLinearMap.mul ℝ ℝ] k := by
  let p (i : ℕ) : ℂ → ℝ := (planarMollifier i).normed volume
  let u : ℂ → ℝ := f ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hu : Continuous u := hks.continuous_convolution_right _ hf hk.continuous
  have hp (i : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (p i) := (planarMollifier i).contDiff_normed
  have hps (i : ℕ) : HasCompactSupport (p i) := (planarMollifier i).hasCompactSupport_normed
  have hsmall : ∀ᶠ i in atTop, (planarMollifier i).rOut < R :=
    planarMollifier_tendsto.eventually (gt_mem_nhds hR)
  have hharm (i : ℕ) (hiR : (planarMollifier i).rOut < R) :
      InnerProductSpace.HarmonicOnNhd (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i)
        (Metric.ball c (3 * R)) := by
    apply weak_harmonic_convolution hf hweak (hp i) (hps i) Metric.isOpen_ball
    intro x hx
    apply Subset.trans _ hball
    apply reflected_tsupport_subset_ball
      (le_of_eq ((planarMollifier i).tsupport_normed_eq (μ := volume)))
    have hx' : dist x c < 3 * R := hx
    linarith
  have he (x : ℂ) (hx : x ∈ Metric.ball c R) :
      ∀ᶠ i in atTop, (u ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x =
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ] p i) x := by
    filter_upwards [hsmall] with i hiR
    rw [← compact_convolutions_commute hf (hp i).continuous (hps i) hk.continuous hks]
    apply harmonic_radial_convolution
      ((hps i).continuous_convolution_right _ hf (hp i).continuous) hrad hc hκ hi
    apply (hharm i hiR).mono
    intro y hy
    have hy' : dist y x ≤ R := hy
    have hx' : dist x c < R := hx
    change dist y c < 3 * R
    have ht := dist_triangle y x c
    linarith
  have hfa := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    planarMollifier_tendsto (Eventually.of_forall planarMollifier_ratio) hf
  filter_upwards [ae_restrict_of_ae hfa, ae_restrict_mem measurableSet_ball] with x hx hxball
  have hua := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := volume) planarMollifier_tendsto hu x
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] f) x) atTop (𝓝 (f x)) at hx
  change Tendsto (fun i ↦ (p i ⋆[ContinuousLinearMap.mul ℝ ℝ] u) x) atTop (𝓝 (u x)) at hua
  simp_rw [real_convolution_comm (p _) f] at hx
  simp_rw [real_convolution_comm (p _) u] at hua
  exact tendsto_nhds_unique hx (hua.congr' (he x hxball))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
lemma continuous_compact_norm_bound {Y : Type*} [NormedAddCommGroup Y]
    {g : X → Y} (hg : Continuous g) (hs : HasCompactSupport g) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, ‖g x‖ ≤ C := by
  obtain ⟨C, hC⟩ := hg.norm.bddAbove_range_of_hasCompactSupport hs.norm
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro x
  exact (hC (mem_range_self x)).trans (le_max_left _ _)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma weak_harmonic_comp_isometry {X Y : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
    [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
    [MeasurableSpace Y] [BorelSpace Y]
    (L : X ≃ₗᵢ[ℝ] Y) {f : Y → ℝ} {R : ℝ}
    (hf : ∀ φ : Y → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, f y * Δ φ y) = 0) :
    ∀ φ : X → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ Metric.ball 0 R → (∫ y, (f ∘ L) y * Δ φ y) = 0 := by
  intro φ hφ hs hb
  have hsupport : tsupport (φ ∘ L.symm) ⊆ Metric.ball 0 R := by
    rw [show tsupport (φ ∘ L.symm) = L.symm ⁻¹' tsupport φ from
      tsupport_comp_eq_preimage φ L.symm.toHomeomorph]
    intro y hy
    have hh := hb hy
    simpa only [Metric.mem_ball, dist_zero_right, LinearIsometryEquiv.norm_map] using hh
  have hh := hf (φ ∘ L.symm) (hφ.comp L.symm.contDiff)
    (hs.comp_homeomorph L.symm.toHomeomorph) hsupport
  rw [← L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding] at hh
  simpa only [Function.comp_apply, laplacian_comp_isometry L.symm hφ,
    LinearIsometryEquiv.symm_apply_apply] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Reflection_BVTorusGraphFlux
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_gradient_norm (g : Plane → ℝ) (y : Plane) :
    ‖gradient g y‖ = ‖fderiv ℝ g y‖ := by
  exact (InnerProductSpace.toDual ℝ Plane).symm.norm_map _

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Regularity_TorusC1Boundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcWeight_ge_one (p : Plane) : 1 ≤ cmcWeight p := by
  have hp := cmcWeight_sq p
  have hh := cmcWeight_pos p
  nlinarith [sq_nonneg ‖p‖]
lemma cmcWeight_le_two {p : Plane} (hp : ‖p‖≤1) : cmcWeight p≤2 := by
  have hh := cmcWeight_sq p
  nlinarith [sq_nonneg (cmcWeight p),norm_nonneg p]

lemma cmcWeight_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcWeight := by
  apply (contDiff_const.add (contDiff_id.norm_sq ℝ)).sqrt
  intro p
  positivity

lemma cmcFlux_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcFlux :=
  (cmcWeight_contDiff.inv (fun p ↦ (cmcWeight_pos p).ne')).smul contDiff_id

lemma cmcWeight_hasFDerivAt (p : Plane) :
    HasFDerivAt cmcWeight ((cmcWeight p)⁻¹ • innerSL ℝ p) p := by
  have h := ((hasStrictFDerivAt_norm_sq p).hasFDerivAt.const_add 1).sqrt
    (by positivity : (1 : ℝ)+‖p‖^2≠0)
  change HasFDerivAt cmcWeight ((1/(2*cmcWeight p)) • (2 • innerSL ℝ p)) p at h
  have he : (1/(2*cmcWeight p)) • (2 • innerSL ℝ p) =
      (cmcWeight p)⁻¹ • innerSL ℝ p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [smul_apply,innerSL_apply_apply,smul_eq_mul,two_smul,add_apply]
    field_simp
    ring
  exact he ▸ h

lemma cmcFlux_hasFDerivAt (p : Plane) : HasFDerivAt cmcFlux (cmcJacobian p) p := by
  have h := ((hasDerivAt_inv (cmcWeight_pos p).ne').comp_hasFDerivAt p (cmcWeight_hasFDerivAt p)).smul (hasFDerivAt_id p)
  have he : (cmcWeight p)⁻¹ • ContinuousLinearMap.id ℝ Plane +
      ((-((cmcWeight p)^2)⁻¹) • ((cmcWeight p)⁻¹ • innerSL ℝ p)).smulRight p =
      cmcJacobian p := by
    apply ContinuousLinearMap.ext
    intro v
    simp only [cmcJacobian,add_apply,sub_apply,smul_apply,ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_eq_mul,smul_smul]
    have hc : -((cmcWeight p)^2)⁻¹*(cmcWeight p)⁻¹*⟪p,v⟫ =
        -(((cmcWeight p)^3)⁻¹*⟪p,v⟫) := by field_simp
    rw [hc,neg_smul,sub_eq_add_neg]
  exact he ▸ h

lemma cmcJacobian_apply (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • v -
      (((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p := by
  simp only [cmcJacobian,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]

lemma cmcJacobian_self (p v : Plane) :
    ⟪v,cmcJacobian p v⟫=
      ((cmcWeight p)^2*‖v‖^2-⟪p,v⟫^2)/(cmcWeight p)^3 := by
  rw [cmcJacobian_apply,inner_sub_right,inner_smul_right,inner_smul_right,
    real_inner_self_eq_norm_sq,real_inner_comm v p]
  field_simp

lemma cmcJacobian_coercive {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    (1/8)*‖v‖^2≤⟪v,cmcJacobian p v⟫ := by
  have hs := cmcWeight_pos p
  have hsq := cmcWeight_sq p
  have hcs := real_inner_mul_inner_self_le p v
  simp only [real_inner_self_eq_norm_sq] at hcs
  have h8 : (cmcWeight p)^3≤8 := by
    have hh := cmcWeight_le_two hp
    nlinarith [sq_nonneg (cmcWeight p-2)]
  rw [cmcJacobian_self,le_div_iff₀ (by positivity : 0<(cmcWeight p)^3)]
  have hh := mul_le_mul_of_nonneg_right h8 (sq_nonneg ‖v‖)
  nlinarith [sq_nonneg ⟪p,v⟫]

lemma cmcJacobian_norm_le {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcJacobian p v‖≤2*‖v‖ := by
  have hs := cmcWeight_ge_one p
  have hs0 := cmcWeight_pos p
  have hsi : (cmcWeight p)⁻¹≤1 := inv_le_one₀ hs0 |>.mpr hs
  have hs3 : ((cmcWeight p)^3)⁻¹≤1 := by
    apply (inv_le_one₀ (by positivity : 0<(cmcWeight p)^3)).mpr
    nlinarith [sq_nonneg (cmcWeight p-1)]
  rw [cmcJacobian_apply]
  calc
    _ ≤ ‖(cmcWeight p)⁻¹ • v‖ + ‖(((cmcWeight p)^3)⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = (cmcWeight p)⁻¹*‖v‖+((cmcWeight p)^3)⁻¹*|⟪p,v⟫| *‖p‖ := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr hs0.le),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hs0.le 3))]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add
      · exact mul_le_of_le_one_left (norm_nonneg _) hsi
      · apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hs3) (norm_nonneg _)).trans
        apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
        exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
          (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_LinearCMCEquation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcJacobian_contDiff : ContDiff ℝ (⊤ : ℕ∞) cmcJacobian := by
  have he : cmcJacobian=fderiv ℝ cmcFlux := funext (fun p ↦ (cmcFlux_hasFDerivAt p).fderiv.symm)
  rw [he]
  exact cmcFlux_contDiff.fderiv_right (by simp)

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_DifferenceStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_vector_norm_sq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (u : Lp Plane 2 μ) : ‖u‖^2=∫ x, ‖u x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneWeakGradient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_test_poincare (R : ℝ) : ∃ C : ℝ, 0≤C ∧
    ∀ f : Plane → ℝ, ∀ hf : ContDiff ℝ 1 f, ∀ hc : HasCompactSupport f,
      tsupport f⊆Metric.ball 0 R →
      ‖(hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f‖≤
        C*‖(compact_C1_gradient_memLp hf hc).toLp (gradient f)‖ := by
  let A : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure Plane) 1
  let B : ℝ≥0∞ := volume (Metric.ball (0 : Plane) R)^(1/2:ℝ)
  have hB : B≠⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
  refine ⟨(A:ℝ)*B.toReal,by positivity,?_⟩
  intro f hf hc hs
  have hd := hf.continuous_fderiv (by simp : (1 : WithTop ℕ∞)≠0)
  have hm : MemLp (fderiv ℝ f) 2 := hd.memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have hsub : Function.support (fderiv ℝ f)⊆Metric.ball 0 R :=
    (subset_tsupport (fderiv ℝ f)).trans ((tsupport_fderiv_subset ℝ).trans hs)
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure Plane) hf hc
    (p := 1) (p' := 2) (by norm_num) (by simp [Plane]) (by norm_num [Plane])
  have hcomp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := volume.restrict (Metric.ball 0 R))
    (f := fderiv ℝ f) (p := 1) (q := 2) (by norm_num) hd.aestronglyMeasurable.restrict
  rw [eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 1) (f := fderiv ℝ f) hsub,
    eLpNorm_restrict_eq_of_support_subset (μ := volume) (p := 2) (f := fderiv ℝ f) hsub,Measure.restrict_apply_univ] at hcomp
  norm_num only [ENNReal.toReal_one,ENNReal.toReal_ofNat,div_one] at hcomp
  have hcomp' : eLpNorm (fderiv ℝ f) 1 volume≤eLpNorm (fderiv ℝ f) 2 volume*B := by
    exact hcomp
  have he : eLpNorm f 2 volume ≤ (A:ℝ≥0∞)*(eLpNorm (fderiv ℝ f) 2 volume*B) :=
    hgns.trans (mul_le_mul_right hcomp' _)
  have hgn : eLpNorm (gradient f) 2 volume=eLpNorm (fderiv ℝ f) 2 volume :=
    eLpNorm_congr_norm_ae (ae_of_all _ (plane_gradient_norm f))
  rw [Lp.norm_toLp,Lp.norm_toLp,hgn]
  have hh := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top
    (ENNReal.mul_ne_top hm.2.ne hB)) he
  simpa only [ENNReal.toReal_mul,ENNReal.coe_toReal,mul_assoc,mul_comm,mul_left_comm] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.congr {S : Set Plane} {u u' : Plane → ℝ} {G G' : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hu : u'=ᵐ[volume] u) (hG : G'=ᵐ[volume] G) :
    PlaneWeakGradient S u' G' := by
  intro v ψ hψ hc hs
  have ha : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) :=
    integral_congr_ae (hG.mono fun _ he ↦ by dsimp only; rw [he])
  have hb : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) :=
    integral_congr_ae (hu.mono fun _ he ↦ by dsimp only; rw [he])
  rw [ha,hb]
  exact h v ψ hψ hc hs

lemma compact_C1_weak_gradient {f : Plane → ℝ} (hf : ContDiff ℝ 1 f)
    (_hc : HasCompactSupport f) (S : Set Plane) : PlaneWeakGradient S f (gradient f) := by
  intro v ψ hψ hc _hs
  have hi₁ : Integrable (fun y ↦ fderiv ℝ f y v*ψ y) :=
    (((hf.continuous_fderiv (by simp)).clm_apply continuous_const).mul hψ.continuous).integrable_of_hasCompactSupport
      hc.mul_left
  have hi₂ : Integrable (fun y ↦ f y*fderiv ℝ ψ y v) :=
    (hf.continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_left
  have hi₃ : Integrable (fun y ↦ f y*ψ y) :=
    (hf.continuous.mul hψ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hi₁ hi₂ hi₃
    (fun _ _ ↦ (hf.differentiable (by simp)).differentiableAt)
    (fun _ _ ↦ (hψ.differentiable (by simp)).differentiableAt)
  simpa only [inner_gradient_left,neg_neg] using congrArg Neg.neg hh.symm

lemma L2_pair_scalar_test {u : Lp ℝ 2 (volume : Measure Plane)} {φ : Plane → ℝ}
    (hφ : MemLp φ 2 volume) : ⟪u,hφ.toLp φ⟫=(∫ y,u y*φ y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_pair_vector_test {G : Lp Plane 2 (volume : Measure Plane)} {φ : Plane → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : Plane) :
    let hm : MemLp (fun y ↦ φ y • v) 2 volume :=
      (hφ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
    ⟪G,hm.toLp (fun y ↦ φ y • v)⟫=(∫ y,⟪G y,v⟫*φ y) := by
  dsimp only
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [((hφ.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right :
    MemLp (fun y ↦ φ y • v) 2 volume).coeFn_toLp] with y hy
  simp only [Pi.smul_def'] at hy
  rw [hy,inner_smul_right,mul_comm]

lemma PlaneWeakGradient.L2_limit {S : Set Plane}
    {u : ℕ → Lp ℝ 2 (volume : Measure Plane)} {G : ℕ → Lp Plane 2 (volume : Measure Plane)}
    {u₀ : Lp ℝ 2 (volume : Measure Plane)} {G₀ : Lp Plane 2 (volume : Measure Plane)}
    (hu : Tendsto u atTop (𝓝 u₀)) (hG : Tendsto G atTop (𝓝 G₀))
    (hweak : ∀ i,PlaneWeakGradient S (u i) (G i)) : PlaneWeakGradient S u₀ G₀ := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y ↦ ψ y • v
  have ha : MemLp a 2 volume := (hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
  let A := ha.toLp a
  let b : Plane → ℝ := fun y ↦ fderiv ℝ ψ y v
  have hb : MemLp b 2 volume := ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)
  let B := hb.toLp b
  have he (i : ℕ) : ⟪G i,A⟫= -⟪u i,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hweak i v ψ hψ hc hs
  have hleft := hG.inner (𝕜 := ℝ) (tendsto_const_nhds (x := A))
  have hright := (hu.inner (𝕜 := ℝ) (tendsto_const_nhds (x := B))).neg
  have hh := tendsto_nhds_unique (hleft.congr' (Eventually.of_forall he)) hright
  rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb] at hh
  exact hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma C1_gradient_sub {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) :
    gradient (f-g)=gradient f-gradient g := by
  funext x
  simp only [gradient,fderiv_sub ((hf.differentiable (by simp)).differentiableAt)
    ((hg.differentiable (by simp)).differentiableAt),map_sub,Pi.sub_apply]

lemma zeroBoundaryGradientSpace_isClosed (S : Set Plane) :
    IsClosed (zeroBoundaryGradientSpace S : Set (Lp Plane 2 (volume : Measure Plane))) :=
  (smoothGradientSpace S).isClosed_topologicalClosure

lemma zeroBoundaryGradientSpace_approximation {S : Set Plane}
    {G : Lp Plane 2 (volume : Measure Plane)} (hG : G∈zeroBoundaryGradientSpace S) :
    ∃ f : ℕ → Plane → ℝ, ∃ hf : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (f i),
      ∃ hc : ∀ i, HasCompactSupport (f i),
        (∀ i,tsupport (f i)⊆S) ∧
        Tendsto (fun i ↦ (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp
          (gradient (f i))) atTop (𝓝 G) := by
  obtain ⟨F,hF,hlim⟩ := mem_closure_iff_seq_limit.mp hG
  choose f hf hc hs he using hF
  refine ⟨f,hf,hc,hs,?_⟩
  convert hlim using 1
  all_goals try with_reducible_and_instances rfl
  funext i
  exact (he i).symm

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma compact_test_poincare_difference {R C : ℝ}
    (hP : ∀ f : Plane → ℝ, ∀ hf : ContDiff ℝ 1 f, ∀ hc : HasCompactSupport f,
      tsupport f⊆Metric.ball 0 R →
      ‖(hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f‖≤
        C*‖(compact_C1_gradient_memLp hf hc).toLp (gradient f)‖)
    {f g : Plane → ℝ} (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport f) (hgc : HasCompactSupport g)
    (hs : tsupport f⊆Metric.ball 0 R) (hgs : tsupport g⊆Metric.ball 0 R) :
    dist ((hf.continuous.memLp_of_hasCompactSupport hc : MemLp f 2).toLp f)
      ((hg.continuous.memLp_of_hasCompactSupport hgc : MemLp g 2).toLp g)≤
    C*dist ((compact_C1_gradient_memLp hf hc).toLp (gradient f))
      ((compact_C1_gradient_memLp hg hgc).toLp (gradient g)) := by
  have hp := hP (f-g) (hf.sub hg) (hc.sub hgc)
    ((tsupport_sub f g).trans (union_subset hs hgs))
  rw [Lp.norm_toLp,Lp.norm_toLp,C1_gradient_sub hf hg] at hp
  simpa only [Lp.dist_edist,Lp.edist_toLp_toLp] using hp

lemma cauchySeq_of_distance_comparison {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    {f : ℕ → X} {g : ℕ → Y} {C : ℝ} (hC : 0≤C)
    (hg : CauchySeq g) (hbound : ∀ i j,dist (f i) (f j)≤C*dist (g i) (g j)) :
    CauchySeq f := by
  rw [Metric.cauchySeq_iff] at hg ⊢
  intro ε hε
  have hCp : 0<C+1 := by linarith
  obtain ⟨N,hN⟩ := hg (ε/(C+1)) (div_pos hε hCp)
  refine ⟨N,fun i hi j hj ↦ ?_⟩
  calc
    dist (f i) (f j) ≤ C*dist (g i) (g j) := hbound i j
    _ ≤ (C+1)*dist (g i) (g j) := by nlinarith [(dist_nonneg : 0≤dist (g i) (g j))]
    _ < ε := (lt_div_iff₀' hCp).mp (hN i hi j hj)

theorem zeroBoundaryGradientSpace_primitive {R : ℝ}
    {G : Lp Plane 2 (volume : Measure Plane)}
    (hG : G∈zeroBoundaryGradientSpace (Metric.ball 0 R)) :
    ∃ u : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ u G ∧
      ∃ f : ℕ → Plane → ℝ, ∃ hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i),
        ∃ hc : ∀ i,HasCompactSupport (f i), (∀ i,tsupport (f i)⊆Metric.ball 0 R) ∧
        Tendsto (fun i ↦ ((hf i).continuous.memLp_of_hasCompactSupport (hc i) :
          MemLp (f i) 2 volume).toLp (f i)) atTop (𝓝 u) ∧
        Tendsto (fun i ↦ (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp
          (gradient (f i))) atTop (𝓝 G) := by
  obtain ⟨C,hC,hP⟩ := compact_test_poincare R
  obtain ⟨f,hf,hc,hs,hlim⟩ := zeroBoundaryGradientSpace_approximation hG
  let U (i : ℕ) : Lp ℝ 2 (volume : Measure Plane) :=
    ((hf i).continuous.memLp_of_hasCompactSupport (hc i) : MemLp (f i) 2 volume).toLp (f i)
  let F (i : ℕ) : Lp Plane 2 (volume : Measure Plane) :=
    (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).toLp (gradient (f i))
  have hbound (i j : ℕ) : dist (U i) (U j)≤C*dist (F i) (F j) :=
    compact_test_poincare_difference hP ((hf i).of_le (by simp)) ((hf j).of_le (by simp))
      (hc i) (hc j) (hs i) (hs j)
  obtain ⟨u,hu⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_distance_comparison hC hlim.cauchySeq hbound)
  refine ⟨u,?_,f,hf,hc,hs,hu,hlim⟩
  apply PlaneWeakGradient.L2_limit hu hlim
  intro i
  apply (compact_C1_weak_gradient ((hf i).of_le (by simp)) (hc i) univ).congr
  · exact ((hf i).continuous.memLp_of_hasCompactSupport (hc i) : MemLp (f i) 2 volume).coeFn_toLp
  · exact (compact_C1_gradient_memLp ((hf i).of_le (by simp)) (hc i)).coeFn_toLp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_pair_gradient_test {G : Lp Plane 2 (volume : Measure Plane)}
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ) :
    ⟪G,(compact_C1_gradient_memLp hψ hc).toLp (gradient ψ)⟫=
      ∫ y, fderiv ℝ ψ y (G y) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(compact_C1_gradient_memLp hψ hc).coeFn_toLp] with y hy
  simp only [hy,inner_gradient_right,conj_trivial]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma L2_scalar_test_integrable (u : Lp ℝ 2 (volume : Measure Plane))
    {ψ : Plane → ℝ} (hψ : MemLp ψ 2 volume) : Integrable (fun y ↦ u y*ψ y) := by
  apply (L2.integrable_inner (𝕜 := ℝ) u (hψ.toLp ψ)).congr
  filter_upwards [hψ.coeFn_toLp] with y hy
  simp only [hy,RCLike.inner_apply,conj_trivial]
  ring

lemma L2_vector_test_integrable (G : Lp Plane 2 (volume : Measure Plane))
    {F : Plane → Plane} (hF : MemLp F 2 volume) : Integrable (fun y ↦ ⟪G y,F y⟫) := by
  apply (L2.integrable_inner (𝕜 := ℝ) G (hF.toLp F)).congr
  filter_upwards [hF.coeFn_toLp] with y hy
  exact congrArg (inner ℝ (G y)) hy

lemma PlaneWeakGradient.Lp_sub {S : Set Plane}
    {u w : Lp ℝ 2 (volume : Measure Plane)} {G W : Lp Plane 2 (volume : Measure Plane)}
    (hu : PlaneWeakGradient S u G) (hw : PlaneWeakGradient S w W) :
    PlaneWeakGradient S ((u-w : Lp ℝ 2 volume) : Plane → ℝ)
      ((G-W : Lp Plane 2 volume) : Plane → Plane) := by
  intro v ψ hψ hc hs
  let a : Plane → Plane := fun y ↦ ψ y • v
  have ha : MemLp a 2 volume := (hψ.continuous.smul continuous_const).memLp_of_hasCompactSupport hc.smul_right
  let A := ha.toLp a
  let b : Plane → ℝ := fun y ↦ fderiv ℝ ψ y v
  have hb : MemLp b 2 volume := ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    (hc.fderiv_apply ℝ v)
  let B := hb.toLp b
  have h₁ : ⟪G,A⟫= -⟪u,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hu v ψ hψ hc hs
  have h₂ : ⟪W,A⟫= -⟪w,B⟫ := by
    rw [L2_pair_vector_test hψ.continuous hc v,L2_pair_scalar_test hb]
    exact hw v ψ hψ hc hs
  rw [← L2_pair_vector_test hψ.continuous hc v,← L2_pair_scalar_test hb]
  change ⟪G-W,A⟫= -⟪u-w,B⟫
  rw [inner_sub_left,inner_sub_left,h₁,h₂]
  ring

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Curvature_CmcStretch
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.weak_laplacian {S : Set Plane}
    {u : Lp ℝ 2 (volume : Measure Plane)} {G : Lp Plane 2 (volume : Measure Plane)}
    (hu : PlaneWeakGradient S u G)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (G y))=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) : (∫ y,u y*Δ ψ y)=0 := by
  let b := stdOrthonormalBasis ℝ Plane
  let D (i : Fin (Module.finrank ℝ Plane)) : Plane → ℝ := fun y ↦ fderiv ℝ ψ y (b i)
  have hD (i) : ContDiff ℝ (⊤ : ℕ∞) (D i) :=
    (hψ.fderiv_right (by simp)).clm_apply contDiff_const
  have hDc (i) : HasCompactSupport (D i) := hc.fderiv_apply ℝ (b i)
  have hDs (i) : tsupport (D i)⊆S := (tsupport_fderiv_apply_subset (f := ψ) ℝ (b i)).trans hs
  have hI (i) : Integrable (fun y ↦ u y*fderiv ℝ (D i) y (b i)) :=
    L2_scalar_test_integrable u (((hD i).continuous_fderiv (by simp)).clm_apply continuous_const |>.memLp_of_hasCompactSupport
      ((hDc i).fderiv_apply ℝ (b i)))
  have hJ (i) : Integrable (fun y ↦ ⟪G y,b i⟫*D i y) := by
    have hh := L2_vector_test_integrable G
      (((hD i).continuous.smul continuous_const).memLp_of_hasCompactSupport (hDc i).smul_right :
        MemLp (fun y ↦ D i y • b i) 2 volume)
    simpa only [Pi.smul_def',inner_smul_right,mul_comm] using hh
  have he (y : Plane) : (∑ i,⟪G y,b i⟫*D i y)=fderiv ℝ ψ y (G y) := by
    simpa only [D,inner_gradient_right,conj_trivial] using
      b.sum_inner_mul_inner (G y) (gradient ψ y)
  simp_rw [laplacian_eq_sum_directional hψ,Finset.mul_sum]
  change (∫ y,∑ i,u y*fderiv ℝ (D i) y (b i))=0
  rw [integral_finsetSum Finset.univ (fun i _ ↦ hI i)]
  have hW (i) := hu (b i) (D i) (hD i) (hDc i) (hDs i)
  calc
    _ = -∑ i, ∫ y,⟪G y,b i⟫*D i y := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i _
      exact (neg_eq_iff_eq_neg.mpr (hW i)).symm
    _ = -(∫ y,∑ i,⟪G y,b i⟫*D i y) := by rw [integral_finsetSum Finset.univ (fun i _ ↦ hJ i)]
    _ = -(∫ y,fderiv ℝ ψ y (G y)) := by simp_rw [he]
    _ = 0 := by rw [hdiv ψ hψ hc hs,neg_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_constant_operator_coercive (A : Plane →L[ℝ] Plane) {c : ℝ}
    (hc : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    c*‖G‖^2≤⟪A.compLpL 2 volume G,G⟫ := by
  rw [← real_inner_self_eq_norm_sq G,L2.inner_def,L2.inner_def,← integral_const_mul]
  apply integral_mono_ae ((L2.integrable_inner (𝕜 := ℝ) G G).const_mul c)
    (L2.integrable_inner (𝕜 := ℝ) (A.compLpL 2 volume G) G)
  filter_upwards [A.coeFn_compLpL G] with y hy
  rw [hy,real_inner_self_eq_norm_sq]
  exact hc (G y)

lemma hilbert_coercive_replacement {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] (K : Submodule ℝ X)
    [hK : IsClosed (K : Set X)] (L : X →L[ℝ] X) {c : ℝ}
    (hc : 0 < c) (hL : ∀ v : X,c*‖v‖^2≤⟪L v,v⟫) (G : X) :
    ∃ W : X, W∈K ∧ c*‖W‖≤‖L G‖ ∧ ∀ F∈K,⟪L (G-W),F⟫=0 := by
  let B : K →L[ℝ] K →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (L.comp K.subtypeL) K.subtypeL
  have hb (x y : K) : B x y=⟪L x,(y : X)⟫ := rfl
  have hB : IsCoercive B := by
    refine ⟨c,hc,fun x ↦ ?_⟩
    rw [hb, ← Submodule.norm_coe x]
    simpa only [pow_two,mul_assoc] using hL (x : X)
  let f : K := K.orthogonalProjectionOnto (L G)
  let z : K := hB.continuousLinearEquivOfBilin.symm f
  let W : X := z
  have he (y : K) : ⟪L W,(y : X)⟫=⟪L G,(y : X)⟫ := by
    have hh := hB.continuousLinearEquivOfBilin_apply z y
    have hz : hB.continuousLinearEquivOfBilin z=f := hB.continuousLinearEquivOfBilin.apply_symm_apply f
    rw [hz,hb] at hh
    have hp := K.starProjection_inner_eq_zero (L G) (y : X) y.property
    rw [inner_sub_left] at hp
    exact hh.symm.trans (by exact (sub_eq_zero.mp hp).symm)
  have hbound : c*‖W‖≤‖L G‖ := by
    by_cases hz : ‖W‖=0
    · simp only [hz,mul_zero]
      positivity
    · have hpos : 0<‖W‖ := lt_of_le_of_ne (norm_nonneg W) (Ne.symm hz)
      apply (mul_le_mul_iff_left₀ hpos).mp
      calc
        (c*‖W‖)*‖W‖=c*‖W‖^2 := by ring
        _ ≤ ⟪L W,W⟫ := hL W
        _ = ⟪L G,W⟫ := he z
        _ ≤ ‖L G‖*‖W‖ := real_inner_le_norm _ _
  refine ⟨W,z.property,hbound,?_⟩
  intro F hF
  rw [map_sub,inner_sub_left,he ⟨F,hF⟩,sub_self]

theorem plane_constant_elliptic_replacement (R : ℝ) (A : Plane →L[ℝ] Plane)
    {c : ℝ} (hc : 0 < c) (hA : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    ∃ W : Lp Plane 2 (volume : Measure Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 R) ∧
      c*‖W‖≤‖A‖*‖G‖ ∧
      (∀ F∈zeroBoundaryGradientSpace (Metric.ball 0 R),
        ⟪A.compLpL 2 volume (G-W),F⟫=0) ∧
      ∃ w : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ w W := by
  let K := zeroBoundaryGradientSpace (Metric.ball (0 : Plane) R)
  let : IsClosed (K : Set (Lp Plane 2 (volume : Measure Plane))) :=
    zeroBoundaryGradientSpace_isClosed _
  obtain ⟨W,hW,hb,ho⟩ := hilbert_coercive_replacement K (A.compLpL 2 volume) hc
    (L2_constant_operator_coercive A hA) G
  obtain ⟨w,hw,_⟩ := zeroBoundaryGradientSpace_primitive hW
  exact ⟨W,hW,hb.trans (A.norm_compLp_le G),ho,w,hw⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_divergence_orthogonal {S : Set Plane}
    {F : Lp Plane 2 (volume : Measure Plane)}
    (hF : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (F y))=0) :
    ∀ W∈zeroBoundaryGradientSpace S,⟪F,W⟫=0 := by
  intro W hW
  obtain ⟨ψ,hψ,hc,hs,hlim⟩ := zeroBoundaryGradientSpace_approximation hW
  have he (i : ℕ) : ⟪F,(compact_C1_gradient_memLp ((hψ i).of_le (by simp))
      (hc i)).toLp (gradient (ψ i))⟫=0 := by
    rw [L2_pair_gradient_test ((hψ i).of_le (by simp)) (hc i)]
    exact hF (ψ i) (hψ i) (hc i) (hs i)
  exact tendsto_nhds_unique
    ((tendsto_const_nhds (x := F)).inner (𝕜 := ℝ) hlim |>.congr' (Eventually.of_forall he))
    tendsto_const_nhds

lemma hilbert_coercive_replacement_error {X : Type*} [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] (K : Submodule ℝ X) (L : X →L[ℝ] X) {c : ℝ}
    (hL : ∀ v : X,c*‖v‖^2≤⟪L v,v⟫) {G W F : X}
    (hW : W∈K) (ho : ∀ V∈K,⟪L (G-W),V⟫=0)
    (hF : ∀ V∈K,⟪F,V⟫=0) : c*‖W‖≤‖L G-F‖ := by
  have he : ⟪L W,W⟫=⟪L G-F,W⟫ := by
    have hh := ho W hW
    rw [map_sub,inner_sub_left] at hh
    rw [inner_sub_left,hF W hW,sub_zero]
    exact (sub_eq_zero.mp hh).symm
  by_cases hz : ‖W‖=0
  · simp only [hz,mul_zero]
    exact norm_nonneg _
  · have hp : 0<‖W‖ := lt_of_le_of_ne (norm_nonneg W) (Ne.symm hz)
    apply (mul_le_mul_iff_left₀ hp).mp
    calc
      (c*‖W‖)*‖W‖=c*‖W‖^2 := by ring
      _ ≤ ⟪L W,W⟫ := hL W
      _ = ⟪L G-F,W⟫ := he
      _ ≤ ‖L G-F‖*‖W‖ := real_inner_le_norm _ _

theorem plane_frozen_elliptic_replacement (R : ℝ) (A : Plane →L[ℝ] Plane)
    {c : ℝ} (hc : 0 < c) (hA : ∀ v : Plane,c*‖v‖^2≤⟪A v,v⟫)
    (G F : Lp Plane 2 (volume : Measure Plane))
    (hF : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (F y))=0) :
    ∃ W : Lp Plane 2 (volume : Measure Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 R) ∧
      c*‖W‖≤‖A.compLpL 2 volume G-F‖ ∧
      (∀ V∈zeroBoundaryGradientSpace (Metric.ball 0 R),
        ⟪A.compLpL 2 volume (G-W),V⟫=0) ∧
      ∃ w : Lp ℝ 2 (volume : Measure Plane), PlaneWeakGradient univ w W := by
  obtain ⟨W,hW,_hb,ho,w,hw⟩ := plane_constant_elliptic_replacement R A hc hA G
  exact ⟨W,hW,hilbert_coercive_replacement_error _ _
    (L2_constant_operator_coercive A hA) hW ho (L2_divergence_orthogonal hF),ho,w,hw⟩

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma bounded_coefficient_memLp {A : Plane → Plane →L[ℝ] Plane}
    (hA : AEStronglyMeasurable A volume) {C : ℝ}
    (hb : ∀ᵐ y ∂volume,∀ v,‖A y v‖≤C*‖v‖)
    (G : Lp Plane 2 (volume : Measure Plane)) :
    MemLp (fun y ↦ A y (G y)) 2 volume := by
  apply ((Lp.memLp G).norm.const_smul C).mono'
  · exact (ContinuousLinearMap.id ℝ (Plane →L[ℝ] Plane)).aestronglyMeasurable_comp₂ hA
      (Lp.aestronglyMeasurable G)
  · filter_upwards [hb] with y hy
    exact hy (G y)

lemma Lp.norm_le_mul_of_ae {G F : Lp Plane 2 (volume : Measure Plane)}
    {C : ℝ} (hC : 0≤C) (h : ∀ᵐ y ∂volume,‖F y‖≤C*‖G y‖) :
    ‖F‖≤C*‖G‖ := by
  calc
    _ ≤ ‖C • G‖ := by
      apply Lp.norm_le_norm_of_ae_le
      filter_upwards [h,Lp.coeFn_smul C G] with y hy hy'
      rw [hy']
      simpa only [Pi.smul_apply,norm_smul,Real.norm_eq_abs,abs_of_nonneg hC] using hy
    _ = C*‖G‖ := by rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hC]

lemma frozen_coefficient_local_residual_bound {A : Plane → Plane →L[ℝ] Plane}
    (A₀ : Plane →L[ℝ] Plane) {G F : Lp Plane 2 (volume : Measure Plane)}
    (hF : (F : Plane → Plane)=ᵐ[volume] (fun y ↦ A y (G y)))
    {S : Set Plane} (hG : ∀ᵐ y ∂volume,y∉S → G y=0)
    {δ : ℝ} (hδ : 0≤δ) (hA : ∀ y∈S,‖A₀-A y‖≤δ) :
    ‖A₀.compLpL 2 volume G-F‖≤δ*‖G‖ := by
  apply Lp.norm_le_mul_of_ae hδ
  filter_upwards [Lp.coeFn_sub (A₀.compLpL 2 volume G) F,
    A₀.coeFn_compLpL G,hF,hG] with y hy hz hf hg
  simp only [Pi.sub_apply] at hy
  rw [hy,hz,hf,← sub_apply]
  by_cases hys : y∈S
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right (hA y hys) (norm_nonneg _))
  · rw [hg hys,map_zero,norm_zero,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma cmcCompress_symm (p u v : Plane) : ⟪cmcCompress p u,v⟫=⟪u,cmcCompress p v⟫ := by
  simp only [cmcCompress_apply,inner_sub_left,inner_sub_right,inner_smul_left,
    inner_smul_right,conj_trivial,real_inner_comm u p]
  ring

lemma cmcCompress_sq (p v : Plane) :
    cmcCompress p (cmcCompress p v)=cmcWeight p • cmcJacobian p v := by
  rw [cmcCompress_apply,cmcCompress_apply,inner_sub_right,inner_smul_right,
    real_inner_self_eq_norm_sq,cmcJacobian_apply,smul_sub,smul_smul,smul_smul]
  have hp := cmcWeight_sq p
  have hw := (cmcWeight_pos p).ne'
  have hw1 : cmcWeight p+1≠0 := by have := cmcWeight_pos p; linarith
  rw [mul_inv_cancel₀ hw,one_smul,sub_sub]
  rw [← add_smul]
  congr 1
  congr 1
  rw [show ‖p‖^2=(cmcWeight p)^2-1 by linarith]
  field_simp
  ring

lemma cmcJacobian_compress (p v : Plane) :
    cmcJacobian p v=(cmcWeight p)⁻¹ • cmcCompress p (cmcCompress p v) := by
  rw [cmcCompress_sq,smul_smul,inv_mul_cancel₀ (cmcWeight_pos p).ne',one_smul]

lemma cmcStretch_jacobian (p v : Plane) :
    cmcStretch p (cmcJacobian p v)=(cmcWeight p)⁻¹ • cmcCompress p v := by
  rw [cmcJacobian_compress,map_smul,cmcStretch_compress]

lemma cmcStretch_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcStretch p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p+1 := by linarith
  have hi : (cmcWeight p+1)⁻¹≤1 := (inv_le_one₀ h0).mpr (by linarith)
  rw [cmcStretch_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p+1)⁻¹*⟪p,v⟫) • p‖ := norm_add_le _ _
    _ = ‖v‖+(cmcWeight p+1)⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

lemma cmcCompress_norm {p : Plane} (hp : ‖p‖≤1) (v : Plane) :
    ‖cmcCompress p v‖≤2*‖v‖ := by
  have hw := cmcWeight_ge_one p
  have h0 : 0 < cmcWeight p*(cmcWeight p+1) := by positivity
  have hi : (cmcWeight p*(cmcWeight p+1))⁻¹≤1 := (inv_le_one₀ h0).mpr (by nlinarith)
  rw [cmcCompress_apply]
  calc
    _ ≤ ‖v‖+‖((cmcWeight p*(cmcWeight p+1))⁻¹*⟪p,v⟫) • p‖ := norm_sub_le _ _
    _ = ‖v‖+(cmcWeight p*(cmcWeight p+1))⁻¹*|⟪p,v⟫| *‖p‖ := by
      rw [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (inv_nonneg.mpr h0.le)]
    _ ≤ ‖v‖+‖v‖ := by
      apply add_le_add le_rfl
      apply (mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (abs_nonneg _) hi) (norm_nonneg _)).trans
      apply (mul_le_mul_of_nonneg_right (abs_real_inner_le_norm p v) (norm_nonneg _)).trans
      exact (mul_le_of_le_one_right (mul_nonneg (norm_nonneg p) (norm_nonneg v)) hp).trans
        (mul_le_of_le_one_left (norm_nonneg v) hp)
    _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeChange_map (L : Plane ≃L[ℝ] Plane) :
    volume.map L=(planeChangeFactor L : ℝ≥0∞) • (volume : Measure Plane) := by
  let : (volume.map L).IsAddHaarMeasure := L.isAddHaarMeasure_map volume
  exact isAddLeftInvariant_eq_smul _ _

lemma planeChange_integral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Plane ≃L[ℝ] Plane) (f : Plane → X) :
    (∫ y,f (L y))=(planeChangeFactor L : ℝ) • ∫ y,f y := by
  have he := L.toHomeomorph.measurableEmbedding.integral_map (μ := volume) f
  change (∫ y,f y ∂volume.map L)=(∫ y,f (L y)) at he
  rw [← he,planeChange_map,integral_smul_measure]
  simp

lemma planeChange_memLp {X : Type*} [NormedAddCommGroup X]
    (L : Plane ≃L[ℝ] Plane) {f : Plane → X} {p : ℝ≥0∞}
    (hf : MemLp f p volume) : MemLp (f ∘ L) p volume := by
  apply L.toHomeomorph.measurableEmbedding.memLp_map_measure_iff.mp
  change MemLp f p (volume.map L)
  rw [planeChange_map]
  exact hf.smul_measure ENNReal.coe_ne_top

lemma PlaneWeakGradient.comp_selfAdjoint {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ a b : Plane,⟪L a,b⟫=⟪a,L b⟫) :
    PlaneWeakGradient (L ⁻¹' S) (u ∘ L) (fun y ↦ L (G (L y))) := by
  intro v ψ hψ hc hs
  let φ : Plane → ℝ := ψ ∘ L.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph L.symm.toHomeomorph
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ L.symm.toHomeomorph)⊆S
    rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
    intro z hz
    have hh : L (L.symm z)∈S := hs hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (z : Plane) : fderiv ℝ φ z (L v)=fderiv ℝ ψ (L.symm z) v := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe,ContinuousLinearEquiv.symm_apply_apply]
  have hh := h (L v) φ hφ hφc hφs
  have he (z : Plane) : ⟪G z,L v⟫*φ z=⟪L (G z),v⟫*ψ (L.symm z) := by
    rw [hL]; rfl
  simp_rw [he,hd] at hh
  have h₁ := planeChange_integral L (fun z ↦ ⟪L (G z),v⟫*ψ (L.symm z))
  have h₂ := planeChange_integral L (fun z ↦ u z*fderiv ℝ ψ (L.symm z) v)
  simp only [ContinuousLinearEquiv.symm_apply_apply,smul_eq_mul] at h₁ h₂
  change (∫ y,⟪L (G (L y)),v⟫*ψ y)= -(∫ y,u (L y)*fderiv ℝ ψ y v)
  rw [h₁,h₂,hh,mul_neg]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma frozen_cmc_divergence_change {S : Set Plane} (p : Plane) (G : Plane → Plane)
    (hdiv : ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) :
    ∀ ψ : Plane → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆(cmcMetricEquiv p) ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (cmcMetricEquiv p (G (cmcMetricEquiv p y))))=0 := by
  let L := cmcMetricEquiv p
  intro ψ hψ hc hs
  let φ : Plane → ℝ := ψ ∘ L.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph L.symm.toHomeomorph
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ L.symm.toHomeomorph)⊆S
    rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
    intro z hz
    have hh : L (L.symm z)∈S := hs hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (z : Plane) : fderiv ℝ φ z (cmcJacobian p (G z))=
      (cmcWeight p)⁻¹*fderiv ℝ ψ (L.symm z) (L (G z)) := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    change fderiv ℝ ψ (L.symm z) (cmcStretch p (cmcJacobian p (G z)))=_
    rw [cmcStretch_jacobian,map_smul,smul_eq_mul]
    rfl
  have hh := hdiv φ hφ hφc hφs
  simp_rw [hd] at hh
  rw [integral_const_mul] at hh
  have hh0 : (∫ z,fderiv ℝ ψ (L.symm z) (L (G z)))=0 :=
    (mul_eq_zero.mp hh).resolve_left (inv_ne_zero (cmcWeight_pos p).ne')
  have he := planeChange_integral L (fun z ↦ fderiv ℝ ψ (L.symm z) (L (G z)))
  simp only [ContinuousLinearEquiv.symm_apply_apply,hh0,smul_zero] at he
  exact he

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.local_congr {S : Set Plane} (hS : MeasurableSet S)
    {u u' : Plane → ℝ} {G G' : Plane → Plane} (h : PlaneWeakGradient S u G)
    (hu : u'=ᵐ[volume.restrict S] u) (hG : G'=ᵐ[volume.restrict S] G) :
    PlaneWeakGradient S u' G' := by
  have hu' := (ae_restrict_iff' hS).mp hu
  have hG' := (ae_restrict_iff' hS).mp hG
  intro v ψ hψ hc hs
  have hleft : (∫ y,⟪G' y,v⟫*ψ y)=(∫ y,⟪G y,v⟫*ψ y) := by
    apply integral_congr_ae
    filter_upwards [hG'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [image_eq_zero_of_notMem_tsupport (fun hh ↦ hys (hs hh)),mul_zero,mul_zero]
  have hright : (∫ y,u' y*fderiv ℝ ψ y v)=(∫ y,u y*fderiv ℝ ψ y v) := by
    apply integral_congr_ae
    filter_upwards [hu'] with y hy
    by_cases hys : y∈S
    · rw [hy hys]
    · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,mul_zero,mul_zero]
  rw [hleft,hright]
  exact h v ψ hψ hc hs

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma PlaneWeakGradient.mono {S T : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (h : PlaneWeakGradient S u G) (hTS : T⊆S) : PlaneWeakGradient T u G := by
  intro v ψ hψ hc hs
  exact h v ψ hψ hc (hs.trans hTS)

lemma planeChange_ae_prop (L : Plane ≃L[ℝ] Plane) {P : Plane → Prop}
    (hP : ∀ᵐ y ∂volume,P y) : ∀ᵐ y ∂volume,P (L y) := by
  apply ae_of_ae_map L.continuous.measurable.aemeasurable
  rw [planeChange_map]
  exact Measure.ae_smul_measure hP (planeChangeFactor L : ℝ≥0∞)

lemma cmcMetricEquiv_norm {p : Plane} (hp : ‖p‖≤1) (y : Plane) :
    ‖cmcMetricEquiv p y‖≤2*‖y‖ := cmcCompress_norm hp y

lemma cmcMetricEquiv_symm_norm {p : Plane} (hp : ‖p‖≤1) (y : Plane) :
    ‖(cmcMetricEquiv p).symm y‖≤2*‖y‖ := cmcStretch_norm hp y

lemma cmcMetricEquiv_ball {p : Plane} (hp : ‖p‖≤1) (R : ℝ) :
    Metric.ball 0 (4*R)⊆(cmcMetricEquiv p) ⁻¹' Metric.ball 0 (8*R) := by
  intro y hy
  have hy' : ‖y‖<4*R := by simpa only [Metric.mem_ball,dist_zero_right] using hy
  have hh : ‖cmcMetricEquiv p y‖<8*R := (cmcMetricEquiv_norm hp y).trans_lt (by linarith)
  simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using hh

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma frozen_replacement_divergence {S : Set Plane} (A : Plane →L[ℝ] Plane)
    {H : Lp Plane 2 (volume : Measure Plane)}
    (ho : ∀ V∈zeroBoundaryGradientSpace S,⟪A.compLpL 2 volume H,V⟫=0)
    {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ⊆S) : (∫ y,fderiv ℝ ψ y (A (H y)))=0 := by
  have hh : (∫ y,fderiv ℝ ψ y ((A.compLpL 2 volume H) y))=0 := by
    rw [← L2_pair_gradient_test (hψ.of_le (by simp)) hc]
    exact ho _ ((smoothGradientSpace S).le_topologicalClosure ⟨ψ,hψ,hc,hs,rfl⟩)
  rw [← hh]
  apply integral_congr_ae
  filter_upwards [A.coeFn_compLpL H] with y hy
  rw [hy]

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_PlaneScaleEquiv
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

lemma smooth_directional_commute {f : Plane → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v w x : Plane) :
    fderiv ℝ (fun y ↦ fderiv ℝ f y v) x w =
      fderiv ℝ (fun y ↦ fderiv ℝ f y w) x v := by
  rw [fderiv_fderiv_apply hf,fderiv_fderiv_apply hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top)) w v

lemma smooth_laplacian {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (Δ f) := by
  have he := funext (laplacian_eq_sum_directional hf)
  rw [he]
  apply ContDiff.sum
  intro i _
  exact (((hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const).fderiv_right (m := (⊤ : ℕ∞))
    (by simp)).clm_apply contDiff_const

lemma laplacian_directional {f : Plane → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (v x : Plane) : Δ (fun y ↦ fderiv ℝ f y v) x = fderiv ℝ (Δ f) x v := by
  have hd (w : Plane) : ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ fderiv ℝ f y w) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  have hdd (w : Plane) : ContDiff ℝ (⊤ : ℕ∞)
      (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z w) y w) :=
    ((hd w).fderiv_right (by simp)).clm_apply contDiff_const
  rw [laplacian_eq_sum_directional (hd v),funext (laplacian_eq_sum_directional hf),
    fderiv_fun_sum (fun w _ ↦ (hdd _).differentiable (by simp) |>.differentiableAt)]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [show (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z v) y ((stdOrthonormalBasis ℝ Plane) i))=
    (fun y ↦ fderiv ℝ (fun z ↦ fderiv ℝ f z ((stdOrthonormalBasis ℝ Plane) i)) y v) from
    funext (fun y ↦ smooth_directional_commute hf _ _ y)]
  exact smooth_directional_commute (hd _) _ _ _

lemma PlaneWeakGradient.harmonic_component {S : Set Plane}
    {u : Plane → ℝ} {G : Plane → Plane} (hg : PlaneWeakGradient S u G)
    (hh : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,u y*Δ ψ y)=0)
    (v : Plane) {ψ : Plane → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hs : tsupport ψ⊆S) :
    (∫ y,⟪G y,v⟫*Δ ψ y)=0 := by
  have hlc : HasCompactSupport (Δ ψ) := hc.of_isClosed_subset isClosed_closure (laplacian_tsupport_subset hψ)
  rw [hg v (Δ ψ) (smooth_laplacian hψ) hlc ((laplacian_tsupport_subset hψ).trans hs)]
  simp_rw [← laplacian_directional hψ]
  rw [hh _ ((hψ.fderiv_right (by simp)).clm_apply contDiff_const)
    (hc.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hs),neg_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
namespace CubicTorus

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X]
  {μ : Measure X} [μ.IsAddHaarMeasure]

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [BorelSpace X] [μ.IsAddHaarMeasure] in
lemma scalar_convolution_norm_le [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [BorelSpace X] [μ.IsAddHaarMeasure] {f k : X → ℝ} (hf : Integrable f μ)
    {C : ℝ} (hb : ∀ x,‖k x‖≤C) (x : X) :
    ‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ) := by
  rw [convolution_mul]
  calc
    _ ≤ ∫ y,C*‖f y‖ ∂μ := norm_integral_le_of_norm_le (hf.norm.const_mul C)
      (Eventually.of_forall fun y ↦ by
        rw [norm_mul,mul_comm C]
        exact mul_le_mul_of_nonneg_left (hb _) (norm_nonneg _))
    _ = _ := integral_const_mul _ _

lemma first_deriv_convolution_le {f k : X → ℝ} (hf : Integrable f μ)
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k)
    {C : ℝ} (hC : 0≤C) (hb : ∀ x,‖fderiv ℝ k x‖≤C) (x : X) :
    ‖fderiv ℝ (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ) := by
  have hm : 0≤∫ y,‖f y‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC hm)
  intro v
  rw [fderiv_compact_convolution hf.locallyIntegrable hk hs]
  have he := scalar_convolution_norm_le hf (fun y ↦
    (ContinuousLinearMap.le_opNorm (fderiv ℝ k y) v).trans
      (mul_le_mul_of_nonneg_right (hb y) (norm_nonneg v))) x
  convert he using 1
  all_goals try with_reducible_and_instances rfl
  ring

lemma compact_convolution_value_lipschitz {k : X → ℝ}
    (hk : ContDiff ℝ (⊤ : ℕ∞) k) (hs : HasCompactSupport k) :
    ∃ C : ℝ,0<C ∧ ∀ f : X → ℝ,Integrable f μ →
      (∀ x,‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x‖≤C*(∫ y,‖f y‖ ∂μ)) ∧
      (∀ x y,‖(f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) x-
        (f ⋆[ContinuousLinearMap.mul ℝ ℝ, μ] k) y‖≤C*(∫ z,‖f z‖ ∂μ)*‖x-y‖) := by
  obtain ⟨C₀,hC₀,hb₀⟩ := continuous_compact_norm_bound hk.continuous hs
  obtain ⟨C₁,hC₁,hb₁⟩ := continuous_compact_norm_bound
    (hk.continuous_fderiv (by simp)) (hs.fderiv ℝ)
  refine ⟨max C₀ C₁,lt_of_lt_of_le hC₀ (le_max_left _ _),fun f hf ↦ ⟨?_,?_⟩⟩
  · exact scalar_convolution_norm_le hf (fun x ↦ (hb₀ x).trans (le_max_left _ _))
  · intro x y
    have hu := hs.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hf.locallyIntegrable hk
    exact (convex_univ : Convex ℝ (univ : Set X)).norm_image_sub_le_of_norm_fderiv_le
      (fun z _ ↦ hu.differentiable (by simp) |>.differentiableAt)
      (fun z _ ↦ first_deriv_convolution_le hf hk hs
        (hC₀.le.trans (le_max_left _ _)) (fun t ↦ (hb₁ t).trans (le_max_right _ _)) z)
      (mem_univ y) (mem_univ x)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace Convolution
open Laplacian
namespace CubicTorus

theorem plane_weak_harmonic_value_lipschitz {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ f : Plane → ℝ,Integrable f →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,f y*Δ ψ y)=0) →
      ∃ u : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧
        f=ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        (∀ x,‖u x‖≤C*(∫ z,‖f z‖)) ∧
        (∀ x y,‖u x-u y‖≤C*(∫ z,‖f z‖)*‖x-y‖) := by
  let L := Complex.orthonormalBasisOneI.repr
  obtain ⟨k,κ,hk,hks,hrad,hc,hκ,_,hi⟩ := exists_radial_smoothing_kernel hR
  obtain ⟨C,hC,hbound⟩ := compact_convolution_value_lipschitz (μ := volume) hk hks
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let v := (f ∘ L) ⋆[ContinuousLinearMap.mul ℝ ℝ] k
  have hfL : Integrable (f ∘ L) := (L.measurePreserving.integrable_comp hf.aestronglyMeasurable).mpr hf
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hks.contDiff_convolution_right _ hfL.locallyIntegrable hk
  have heI : (∫ z,‖(f ∘ L) z‖)=∫ z,‖f z‖ :=
    by
      dsimp only [Function.comp_def]
      rw [L.measurePreserving.integral_comp L.toMeasurableEquiv.measurableEmbedding (fun z ↦ ‖f z‖)]
  obtain ⟨hb,hl⟩ := hbound _ hfL
  rw [heI] at hb hl
  refine ⟨v ∘ L.symm,hv.comp L.symm.contDiff,?_,?_,?_⟩
  · have he := weak_harmonic_radial_reproduction hR (Subset.refl _) hfL.locallyIntegrable
      (weak_harmonic_comp_isometry L hw) hk hks hrad hc hκ hi
    have hmp : MeasurePreserving L.symm
        (volume.restrict (Metric.ball (0 : Plane) R))
        (volume.restrict (Metric.ball (0 : ℂ) R)) := by
      simpa only [L.symm.preimage_ball,map_zero] using
        L.symm.measurePreserving.restrict_preimage (measurableSet_ball (x := (0 : ℂ)) (ε := R))
    have hh := hmp.quasiMeasurePreserving.ae_eq_comp he
    filter_upwards [hh] with z hz
    change f (L (L.symm z))=v (L.symm z) at hz
    simpa only [LinearIsometryEquiv.apply_symm_apply,Function.comp_apply] using hz
  · intro x
    simpa only [v,Function.comp_apply] using hb (L.symm x)
  · intro x y
    have hh := hl (L.symm x) (L.symm y)
    simpa only [v,Function.comp_apply,← map_sub,L.symm.norm_map] using hh

theorem plane_L2_harmonic_value_lipschitz {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ f : Plane → ℝ,MemLp f 2 volume →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,f y*Δ ψ y)=0) →
      ∃ u : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) u ∧
        f=ᵐ[volume.restrict (Metric.ball 0 R)] u ∧
        (∀ x,‖u x‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖f z‖)) ∧
        (∀ x y,‖u x-u y‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖f z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_weak_harmonic_value_lipschitz hR
  refine ⟨C,hC,fun f hf hw ↦ ?_⟩
  let S := Metric.closedBall (0 : Plane) (4*R)
  let F := S.indicator f
  have hfi : IntegrableOn f S := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact
    (isCompact_closedBall _ _)
  have hF : Integrable F := hfi.integrable_indicator measurableSet_closedBall
  have hFw : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,F y*Δ ψ y)=0 := by
    intro ψ hψ hc hs
    rw [← hw ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y∈S
    · simp only [F,indicator_of_mem hy]
    · have hz : Δ ψ y=0 := image_eq_zero_of_notMem_tsupport
        (fun h ↦ hy (Metric.ball_subset_closedBall (hs (laplacian_tsupport_subset hψ h))))
      simp only [hz,mul_zero]
  obtain ⟨u,hu,he,hb,hl⟩ := hbound F hF hFw
  have heI : (∫ z,‖F z‖)=∫ z in S,‖f z‖ := by
    rw [← integral_indicator measurableSet_closedBall]
    apply integral_congr_ae
    filter_upwards [] with z
    change ‖S.indicator f z‖=S.indicator (fun z ↦ ‖f z‖) z
    by_cases hz : z∈S <;> simp [hz]
  refine ⟨u,hu,?_,by simpa only [heI] using hb,by simpa only [heI] using hl⟩
  filter_upwards [he,ae_restrict_mem measurableSet_ball] with y hy hys
  have hS : y∈S := Metric.ball_subset_closedBall
    ((Metric.ball_subset_ball (by linarith : R≤4*R)) hys)
  simpa only [F,indicator_of_mem hS] using hy

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
open Laplacian
namespace CubicTorus

theorem plane_harmonic_gradient_bound {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (4*R)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,fderiv ℝ ψ y (G y))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H ∧
        (∀ x,‖H x‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*(∫ z in Metric.closedBall 0 (4*R),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_L2_harmonic_value_lipschitz hR
  refine ⟨2*C,by positivity,fun u G hg hd ↦ ?_⟩
  let b := stdOrthonormalBasis ℝ Plane
  let S := Metric.closedBall (0 : Plane) (4*R)
  let M := ∫ z in S,‖G z‖
  have hmem (i : Fin (Module.finrank ℝ Plane)) : MemLp (fun y ↦ ⟪G y,b i⟫) 2 volume := by
    simpa [Function.comp_def,real_inner_comm] using (innerSL ℝ (b i)).comp_memLp' (Lp.memLp G)
  have hh (i : Fin (Module.finrank ℝ Plane)) := hbound _ (hmem i)
    (fun ψ hψ hc hs ↦ hg.harmonic_component (fun φ hφ hfc hfs ↦ hg.weak_laplacian hd hφ hfc hfs)
      (b i) hψ hc hs)
  choose H hH he hb hl using hh
  have hGi : IntegrableOn (fun z ↦ ‖G z‖) S :=
    ((Lp.memLp G).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hM (i : Fin (Module.finrank ℝ Plane)) : (∫ z in S,‖⟪G z,b i⟫‖)≤M := by
    apply integral_mono
      (((hmem i).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)) hGi
    intro z
    simpa only [b.orthonormal.norm_eq_one i,mul_one] using norm_inner_le_norm (G z) (b i)
  let F : Plane → Plane := fun y ↦ ∑ i,H i y • b i
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := ContDiff.sum fun i _ ↦ (hH i).smul contDiff_const
  refine ⟨F,hF,?_,?_,?_⟩
  · filter_upwards [ae_all_iff.mpr he] with y hy
    change G y=∑ i,H i y • b i
    rw [← b.sum_repr' (G y)]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hy i,real_inner_comm]
  · intro x
    change ‖∑ i,H i x • b i‖≤_
    calc
      _ ≤ ∑ i,‖H i x • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (Module.finrank ℝ Plane),C*M := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [norm_smul,b.orthonormal.norm_eq_one i,mul_one] using
          (hb i x).trans (mul_le_mul_of_nonneg_left (hM i) hC.le)
      _ = _ := by simp [Plane,finrank_euclideanSpace]; ring
  · intro x y
    change ‖(∑ i,H i x • b i)-(∑ i,H i y • b i)‖≤_
    rw [← Finset.sum_sub_distrib]
    calc
      _ ≤ ∑ i,‖H i x • b i-H i y • b i‖ := norm_sum_le _ _
      _ ≤ ∑ _ : Fin (Module.finrank ℝ Plane),C*M*‖x-y‖ := by
        apply Finset.sum_le_sum
        intro i _
        simp only [← sub_smul,norm_smul,b.orthonormal.norm_eq_one i,mul_one]
        exact (hl i x y).trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hM i) hC.le) (norm_nonneg _))
      _ = _ := by simp [Plane,finrank_euclideanSpace]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeChange_real (L : Plane ≃L[ℝ] Plane) {S : Set Plane} (hS : MeasurableSet S) :
    (volume : Measure Plane).real (L ⁻¹' S)=
      (planeChangeFactor L : ℝ)*(volume : Measure Plane).real S := by
  simp only [Measure.real]
  rw [← Measure.map_apply L.continuous.measurable hS,planeChange_map,Measure.smul_apply,
    smul_eq_mul,ENNReal.toReal_mul,ENNReal.coe_toReal]

lemma planeChangeFactor_le_four (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ y,‖L.symm y‖≤2*‖y‖) : (planeChangeFactor L : ℝ)≤4 := by
  have hs : L ⁻¹' Metric.ball (0 : Plane) 1⊆Metric.ball 0 2 := by
    intro y hy
    have hy' : ‖L y‖<1 := by simpa only [mem_preimage,Metric.mem_ball,dist_zero_right] using hy
    have hn := hL (L y)
    simp only [ContinuousLinearEquiv.symm_apply_apply] at hn
    simpa only [Metric.mem_ball,dist_zero_right] using hn.trans_lt (by linarith : 2*‖L y‖<2)
  have hv : (volume : Measure Plane) (Metric.ball (0 : Plane) 2)≠⊤ := Metric.isBounded_ball.measure_lt_top.ne
  have hh := ENNReal.toReal_mono hv (measure_mono hs)
  change (volume : Measure Plane).real (L ⁻¹' Metric.ball 0 1)≤volume.real (Metric.ball 0 2) at hh
  rw [planeChange_real L measurableSet_ball,plane_ball_real (by norm_num : (0:ℝ)≤1),
    plane_ball_real (by norm_num : (0:ℝ)≤2)] at hh
  nlinarith [Real.pi_pos]

lemma planeChange_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (L : Plane ≃L[ℝ] Plane) {S : Set Plane} (hS : MeasurableSet S) (f : Plane → X) :
    (∫ y in L ⁻¹' S,f (L y))=(planeChangeFactor L : ℝ) • ∫ y in S,f y := by
  rw [← integral_indicator (hS.preimage L.continuous.measurable),← integral_indicator hS,
    ← planeChange_integral L]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : L y∈S <;> simp [hy]

lemma planeChange_closedBall_L1 (L : Plane ≃L[ℝ] Plane)
    (hL : ∀ y,‖L y‖≤2*‖y‖) (hLi : ∀ y,‖L.symm y‖≤2*‖y‖)
    (G : Lp Plane 2 (volume : Measure Plane)) {R : ℝ} (hR : 0≤R) :
    (∫ y in Metric.closedBall 0 (4*R),‖L (G (L y))‖)≤
      8*(∫ y in Metric.closedBall 0 (8*R),‖G y‖) := by
  let S := Metric.closedBall (0 : Plane) (8*R)
  let T := Metric.closedBall (0 : Plane) (4*R)
  have hs : T⊆L ⁻¹' S := by
    intro y hy
    have hy' : ‖y‖≤4*R := by simpa only [T,Metric.mem_closedBall,dist_zero_right] using hy
    change ‖L y-0‖≤8*R
    rw [sub_zero]
    calc
      ‖L y‖ ≤ 2*‖y‖ := hL y
      _ ≤ 2*(4*R) := by
        simpa only [mul_comm] using mul_le_mul hy' (le_refl (2 : ℝ))
          (by norm_num) (mul_nonneg (by norm_num) hR)
      _ = 8*R := by ring
  have hi := planeChange_memLp L (Lp.memLp G)
  have hj := L.toContinuousLinearMap.comp_memLp' hi
  have hcompact : IsCompact (L ⁻¹' S) := L.toHomeomorph.isCompact_preimage.mpr
    (isCompact_closedBall (0 : Plane) (8*R))
  have hInt : IntegrableOn (fun y ↦ ‖G (L y)‖) (L ⁻¹' S) :=
    (hi.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact hcompact
  have hIntT : IntegrableOn (fun y ↦ ‖L (G (L y))‖) T :=
    (hj.norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hM : 0≤∫ y in S,‖G y‖ := integral_nonneg fun _ ↦ norm_nonneg _
  calc
    _ ≤ ∫ y in T,2*‖G (L y)‖ := integral_mono hIntT ((hInt.mono_set hs).const_mul 2)
      (fun y ↦ hL (G (L y)))
    _ = 2*(∫ y in T,‖G (L y)‖) := integral_const_mul _ _
    _ ≤ 2*(∫ y in L ⁻¹' S,‖G (L y)‖) := by
      exact mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hInt (Eventually.of_forall fun _ ↦ norm_nonneg _) hs.eventuallyLE) (by norm_num)
    _ = 2*(planeChangeFactor L : ℝ)*(∫ y in S,‖G y‖) := by
      rw [planeChange_setIntegral L (S := S) measurableSet_closedBall (fun y ↦ ‖G y‖)]
      simp only [smul_eq_mul]; ring
    _ ≤ _ := by nlinarith [planeChangeFactor_le_four L hLi]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem frozen_cmc_gradient_bound {R : ℝ} (hR : 0<R) :
    ∃ C : ℝ,0<C ∧ ∀ p : Plane,‖p‖≤1 →
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] H ∧
        (∀ x,‖H x‖≤C*(∫ z in Metric.closedBall 0 (8*R),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*(∫ z in Metric.closedBall 0 (8*R),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := plane_harmonic_gradient_bound hR
  refine ⟨32*C,by positivity,fun p hp u G hg hd ↦ ?_⟩
  let L := cmcMetricEquiv p
  have hu := planeChange_memLp L (Lp.memLp u)
  have hG := L.toContinuousLinearMap.comp_memLp' (planeChange_memLp L (Lp.memLp G))
  let u' := hu.toLp ((u : Plane → ℝ) ∘ L)
  let G' := hG.toLp (fun y ↦ L (G (L y)))
  have hraw := hg.comp_selfAdjoint L (cmcCompress_symm p)
  have hg' : PlaneWeakGradient (Metric.ball 0 (4*R)) u' G' :=
    (hraw.congr hu.coeFn_toLp hG.coeFn_toLp).mono (cmcMetricEquiv_ball hp R)
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (4*R) → (∫ y,fderiv ℝ ψ y (G' y))=0 := by
    intro ψ hψ hc hs
    have hh := frozen_cmc_divergence_change p (G : Plane → Plane) hd ψ hψ hc
      (hs.trans (cmcMetricEquiv_ball hp R))
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    exact congrArg (fderiv ℝ ψ y) hy
  obtain ⟨H,hH,he,hb,hl⟩ := hbound u' G' hg' hd'
  let M := ∫ z in Metric.closedBall (0 : Plane) (8*R),‖G z‖
  have hM : (∫ z in Metric.closedBall 0 (4*R),‖G' z‖)≤8*M := by
    have hh := planeChange_closedBall_L1 L (cmcMetricEquiv_norm hp)
      (cmcMetricEquiv_symm_norm hp) G hR.le
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae hG.coeFn_toLp] with z hz
    exact congrArg norm hz
  let F : Plane → Plane := L.symm ∘ H ∘ L.symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := L.symm.contDiff.comp (hH.comp L.symm.contDiff)
  refine ⟨F,hF,?_,?_,?_⟩
  · have he' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) R → G' y=H y :=
      (ae_restrict_iff' measurableSet_ball).mp he
    have he'' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) R → G (L y)=L.symm (H y) := by
      filter_upwards [he',hG.coeFn_toLp] with y hy hz hys
      have hx : L (G (L y))=H y := hz.symm.trans (hy hys)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg L.symm hx
    have he''' := planeChange_ae_prop L.symm he''
    change ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) (R/2)), G y=F y
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [he'''] with y hy hys
    have hn : ‖y‖<R/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hys
    have hLy : L.symm y∈Metric.ball (0 : Plane) R := by
      rw [Metric.mem_ball,dist_zero_right]
      exact (cmcMetricEquiv_symm_norm hp y).trans_lt (by linarith)
    simpa only [ContinuousLinearEquiv.apply_symm_apply,F,Function.comp_apply] using hy hLy
  · intro x
    have hb' := (hb (L.symm x)).trans (mul_le_mul_of_nonneg_left hM hC.le)
    have hMn : 0≤M := integral_nonneg fun _ ↦ norm_nonneg _
    change ‖L.symm (H (L.symm x))‖≤_
    exact (cmcMetricEquiv_symm_norm hp _).trans (by nlinarith)
  · intro x y
    change ‖L.symm (H (L.symm x))-L.symm (H (L.symm y))‖≤_
    rw [← map_sub]
    calc
      _ ≤ 2*‖H (L.symm x)-H (L.symm y)‖ := cmcMetricEquiv_symm_norm hp _
      _ ≤ 2*(C*(∫ z in Metric.closedBall 0 (4*R),‖G' z‖)*‖L.symm x-L.symm y‖) :=
        mul_le_mul_of_nonneg_left (hl _ _) (by norm_num)
      _ ≤ 2*(C*(8*M)*(2*‖x-y‖)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hM hC.le
        · rw [← map_sub]; exact cmcMetricEquiv_symm_norm hp _
        · exact norm_nonneg _
        · exact mul_nonneg hC.le (mul_nonneg (by norm_num) (integral_nonneg fun _ ↦ norm_nonneg _))
      _ = _ := by ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma planeScaleEquiv_apply (r : ℝ) (hr : r≠0) (y : Plane) :
    planeScaleEquiv r hr y=r • y := rfl

lemma planeScaleEquiv_preimage_ball {r : ℝ} (hr : 0 < r) (s : ℝ) :
    planeScaleEquiv r hr.ne' ⁻¹' Metric.ball (0 : Plane) (r*s)=Metric.ball 0 s := by
  ext y
  simp only [mem_preimage,Metric.mem_ball,dist_zero_right,planeScaleEquiv_apply,
    norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_lt_mul_iff_right₀ hr

lemma planeScaleEquiv_preimage_closedBall {r : ℝ} (hr : 0 < r) (s : ℝ) :
    planeScaleEquiv r hr.ne' ⁻¹' Metric.closedBall (0 : Plane) (r*s)=Metric.closedBall 0 s := by
  ext y
  simp only [mem_preimage,Metric.mem_closedBall,dist_zero_right,planeScaleEquiv_apply,
    norm_smul,Real.norm_eq_abs,abs_of_pos hr]
  exact mul_le_mul_iff_right₀ hr

lemma planeScaleFactor {r : ℝ} (hr : 0 < r) :
    (planeChangeFactor (planeScaleEquiv r hr.ne') : ℝ)=r⁻¹^2 := by
  have hh := planeChange_real (planeScaleEquiv r hr.ne')
    (S := Metric.ball (0 : Plane) (r*1)) measurableSet_ball
  rw [planeScaleEquiv_preimage_ball hr,plane_ball_real (by norm_num : (0:ℝ)≤1),
    plane_ball_real (by positivity : 0 ≤ r*1)] at hh
  simp only [mul_one,one_pow] at hh
  field_simp
  nlinarith [Real.pi_pos]

lemma planeScale_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {r : ℝ} (hr : 0 < r) (s : ℝ) (f : Plane → X) :
    (∫ y in Metric.closedBall 0 s,f (r • y))=
      (r⁻¹^2) • ∫ y in Metric.closedBall 0 (r*s),f y := by
  have hh := planeChange_setIntegral (planeScaleEquiv r hr.ne')
    (S := Metric.closedBall (0 : Plane) (r*s)) measurableSet_closedBall f
  simpa only [planeScaleEquiv_preimage_closedBall hr,planeScaleEquiv_apply,planeScaleFactor hr] using hh

lemma constant_divergence_scale {S : Set Plane} {r : ℝ} (hr : 0 < r)
    (A : Plane →L[ℝ] Plane) (G : Plane → Plane)
    (hdiv : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A (G y)))=0) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆planeScaleEquiv r hr.ne' ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (r • A (G (r • y))))=0 := by
  let L := planeScaleEquiv r hr.ne'
  intro ψ hψ hc hs
  let φ : Plane → ℝ := ψ ∘ L.symm
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp L.symm.contDiff
  have hφc : HasCompactSupport φ := hc.comp_homeomorph L.symm.toHomeomorph
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ L.symm.toHomeomorph)⊆S
    rw [tsupport_comp_eq_preimage ψ L.symm.toHomeomorph]
    intro z hz
    have hh : L (L.symm z)∈S := hs hz
    simpa only [ContinuousLinearEquiv.apply_symm_apply] using hh
  have hd (z : Plane) : fderiv ℝ φ z (A (G z))=
      r⁻¹*fderiv ℝ ψ (L.symm z) (A (G z)) := by
    rw [fderiv_comp z (hψ.differentiable (by simp)).differentiableAt L.symm.differentiableAt]
    simp only [ContinuousLinearEquiv.fderiv,ContinuousLinearMap.coe_comp,Function.comp_apply,
      ContinuousLinearEquiv.coe_coe]
    change fderiv ℝ ψ (L.symm z) (r⁻¹ • A (G z))=_
    rw [map_smul,smul_eq_mul]
  have hh := hdiv φ hφ hφc hφs
  simp_rw [hd] at hh
  rw [integral_const_mul] at hh
  have hh0 : (∫ z,fderiv ℝ ψ (L.symm z) (A (G z)))=0 :=
    (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hr.ne')
  have he := planeChange_integral L (fun z ↦ fderiv ℝ ψ (L.symm z) (A (G z)))
  simp only [ContinuousLinearEquiv.symm_apply_apply,hh0,smul_zero] at he
  simp only [map_smul,smul_eq_mul,integral_const_mul]
  change r*(∫ y,fderiv ℝ ψ y (A (G (L y))))=0
  rw [he,mul_zero]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem frozen_cmc_gradient_scaled :
    ∃ C : ℝ,0<C ∧ ∀ r : ℝ,0 < r → ∀ p : Plane,‖p‖≤1 →
      ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 (8*r)) u G →
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 (8*r) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G y)))=0) →
      ∃ H : Plane → Plane,ContDiff ℝ (⊤ : ℕ∞) H ∧
        (G : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (r/2))] H ∧
        (∀ x,‖H x‖≤C*r⁻¹^2*(∫ z in Metric.closedBall 0 (8*r),‖G z‖)) ∧
        (∀ x y,‖H x-H y‖≤C*r⁻¹^3*(∫ z in Metric.closedBall 0 (8*r),‖G z‖)*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := frozen_cmc_gradient_bound (by norm_num : (0:ℝ)<1)
  refine ⟨C,hC,fun r hr p hp u G hg hd ↦ ?_⟩
  let L := planeScaleEquiv r hr.ne'
  have hu := planeChange_memLp L (Lp.memLp u)
  have hG := L.toContinuousLinearMap.comp_memLp' (planeChange_memLp L (Lp.memLp G))
  let u' := hu.toLp ((u : Plane → ℝ) ∘ L)
  let G' := hG.toLp (fun y ↦ L (G (L y)))
  have hpre : L ⁻¹' Metric.ball (0 : Plane) (8*r)=Metric.ball 0 (8*1) := by
    simpa only [mul_comm r,mul_one] using planeScaleEquiv_preimage_ball hr 8
  have hg' : PlaneWeakGradient (Metric.ball 0 (8*1)) u' G' := by
    rw [← hpre]
    apply (hg.comp_selfAdjoint L ?_).congr hu.coeFn_toLp hG.coeFn_toLp
    intro a b
    change ⟪r • a,b⟫=⟪a,r • b⟫
    simp only [real_inner_smul_left,real_inner_smul_right]
  have hd' : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*1) → (∫ y,fderiv ℝ ψ y (cmcJacobian p (G' y)))=0 := by
    intro ψ hψ hc hs
    have hh := constant_divergence_scale hr (cmcJacobian p) (G : Plane → Plane) hd
      ψ hψ hc (by change tsupport ψ⊆L ⁻¹' Metric.ball 0 (8*r); rw [hpre]; exact hs)
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [hG.coeFn_toLp] with y hy
    change G' y=r • G (r • y) at hy
    rw [hy]
    rw [map_smul]
  obtain ⟨H,hH,he,hb,hl⟩ := hbound p hp u' G' hg' hd'
  let M := ∫ z in Metric.closedBall (0 : Plane) (8*r),‖G z‖
  have hM : (∫ z in Metric.closedBall 0 (8*1),‖G' z‖)=r⁻¹*M := by
    have heq : (∫ z in Metric.closedBall 0 (8*1),‖G' z‖)=
        ∫ z in Metric.closedBall 0 8,‖r • G (r • z)‖ := by
      norm_num
      apply integral_congr_ae
      filter_upwards [ae_restrict_of_ae hG.coeFn_toLp] with z hz
      exact congrArg norm hz
    rw [heq]
    simp only [norm_smul,Real.norm_eq_abs,abs_of_pos hr,integral_const_mul]
    rw [planeScale_setIntegral hr 8 (fun z ↦ ‖G z‖)]
    simp only [smul_eq_mul,mul_comm r 8]
    change r*(r⁻¹^2*M)=r⁻¹*M
    field_simp
  have hb' : ∀ x,‖H x‖≤C*(r⁻¹*M) := by
    simpa only [hM] using hb
  have hl' : ∀ x y,‖H x-H y‖≤(C*(r⁻¹*M))*‖x-y‖ := by
    simpa only [hM] using hl
  let F : Plane → Plane := L.symm ∘ H ∘ L.symm
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := L.symm.contDiff.comp (hH.comp L.symm.contDiff)
  refine ⟨F,hF,?_,?_,?_⟩
  · have he' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) (1/2) → G' y=H y :=
      (ae_restrict_iff' measurableSet_ball).mp he
    have he'' : ∀ᵐ y ∂volume,y∈Metric.ball (0 : Plane) (1/2) → G (L y)=L.symm (H y) := by
      filter_upwards [he',hG.coeFn_toLp] with y hy hz hys
      have hx : L (G (L y))=H y := hz.symm.trans (hy hys)
      simpa only [ContinuousLinearEquiv.symm_apply_apply] using congrArg L.symm hx
    have he''' := planeChange_ae_prop L.symm he''
    change ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) (r/2)),G y=F y
    rw [ae_restrict_iff' measurableSet_ball]
    filter_upwards [he'''] with y hy hys
    have hLy : L.symm y∈Metric.ball (0 : Plane) (1/2) := by
      have hn : ‖y‖ < r/2 := by simpa only [Metric.mem_ball,dist_zero_right] using hys
      change ‖r⁻¹ • y-0‖<1/2
      rw [sub_zero,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
      apply (mul_lt_mul_of_pos_left hn (inv_pos.mpr hr)).trans_le
      field_simp
      norm_num
    simpa only [ContinuousLinearEquiv.apply_symm_apply,F,Function.comp_apply] using hy hLy
  · intro x
    change ‖r⁻¹ • H (L.symm x)‖≤_
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*(C*(r⁻¹*M)) := mul_le_mul_of_nonneg_left (hb' _) (inv_pos.mpr hr).le
      _ = _ := by ring
  · intro x y
    change ‖r⁻¹ • H (L.symm x)-r⁻¹ • H (L.symm y)‖≤_
    rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    calc
      _ ≤ r⁻¹*((C*(r⁻¹*M))*‖L.symm x-L.symm y‖) :=
        mul_le_mul_of_nonneg_left (hl' _ _) (inv_pos.mpr hr).le
      _ = _ := by
        change r⁻¹*((C*(r⁻¹*M))*‖r⁻¹ • x-r⁻¹ • y‖)=_
        rw [← smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
        ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_vector_norm_sq_integrable (G : Lp Plane 2 (volume : Measure Plane)) :
    Integrable (fun y ↦ ‖G y‖^2) := by
  exact (memLp_two_iff_integrable_sq (Lp.memLp G).norm.aestronglyMeasurable).mp
    (Lp.memLp G).norm

lemma plane_closedBall_mass_le {s : ℝ} (hs : 0 < s) :
    (volume : Measure Plane).real (Metric.closedBall 0 s)≤4*Real.pi*s^2 := by
  have hsub : Metric.closedBall (0 : Plane) s⊆Metric.ball 0 (2*s) :=
    Metric.closedBall_subset_ball (by linarith)
  have hh := ENNReal.toReal_mono (Metric.isBounded_ball.measure_lt_top.ne :
    (volume : Measure Plane) (Metric.ball (0 : Plane) (2*s))≠⊤) (measure_mono hsub)
  change volume.real (Metric.closedBall (0 : Plane) s)≤volume.real (Metric.ball 0 (2*s)) at hh
  rw [plane_ball_real (by positivity : 0≤2*s)] at hh
  nlinarith

lemma L2_local_L1 {s : ℝ} (hs : 0 < s) (G : Lp Plane 2 (volume : Measure Plane)) :
    (∫ y in Metric.closedBall (0 : Plane) s,‖G y‖)≤2*Real.sqrt Real.pi*s*‖G‖ := by
  let S := Metric.closedBall (0 : Plane) s
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr
    (isCompact_closedBall (0 : Plane) s).measure_lt_top.ne
  have hi : IntegrableOn (fun y ↦ ‖G y‖) S :=
    ((Lp.memLp G).norm.locallyIntegrable (by norm_num)).integrableOn_isCompact (isCompact_closedBall _ _)
  have hi₂ := L2_vector_norm_sq_integrable G
  have hh := integral_square_le_mass hi hi₂.integrableOn
  have hE : (∫ y in S,‖G y‖^2)≤‖G‖^2 := by
    rw [L2_vector_norm_sq_integral]
    exact setIntegral_le_integral hi₂ (Eventually.of_forall fun _ ↦ sq_nonneg _)
  have hmass : (volume.restrict S).real univ≤4*Real.pi*s^2 := by
    simpa only [Measure.real,Measure.restrict_apply_univ] using plane_closedBall_mass_le hs
  have hb := hh.trans (mul_le_mul hmass hE
    (integral_nonneg fun _ ↦ sq_nonneg _) (by positivity))
  have hsq := Real.sq_sqrt Real.pi_pos.le
  have hnon : 0≤2*Real.sqrt Real.pi*s*‖G‖ := by positivity
  nlinarith [sq_nonneg ((2*Real.sqrt Real.pi*s)*‖G‖),
    show (2*Real.sqrt Real.pi*s*‖G‖)^2=4*Real.pi*s^2*‖G‖^2 by
      rw [mul_pow,mul_pow,mul_pow,hsq]; ring]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_replacement_bounds :
    ∃ C : ℝ,0<C ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    (∀ᵐ y ∂volume,y∉Metric.ball 0 (8*R) → G y=0) →
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ (w : Lp ℝ 2 (volume : Measure Plane)) (W : Lp Plane 2 (volume : Measure Plane))
      (H : Plane → Plane),
      W∈zeroBoundaryGradientSpace (Metric.ball 0 (8*R)) ∧
      PlaneWeakGradient univ w W ∧ ‖W‖≤8*δ*‖G‖ ∧
      ContDiff ℝ (⊤ : ℕ∞) H ∧
      ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 (R/2))] H ∧
      (∀ x,‖H x‖≤C*R⁻¹*‖G‖) ∧
      (∀ x y,‖H x-H y‖≤C*R⁻¹^2*‖G‖*‖x-y‖) := by
  obtain ⟨C,hC,hbound⟩ := frozen_cmc_gradient_scaled
  refine ⟨144*Real.sqrt Real.pi*C,by positivity,fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G hgs hgrad hdiv ↦ ?_⟩
  have hA := (cmcJacobian_contDiff.continuous.comp hp).aestronglyMeasurable (μ := volume)
  have hmem := bounded_coefficient_memLp hA
    (Eventually.of_forall fun y v ↦ cmcJacobian_norm_le (hpb y) v) G
  let F := hmem.toLp (fun y ↦ cmcJacobian (p y) (G y))
  have hF : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (F y))=0 := by
    intro ψ hψ hc hs
    rw [← hdiv ψ hψ hc hs]
    apply integral_congr_ae
    filter_upwards [hmem.coeFn_toLp] with y hy
    exact congrArg (fderiv ℝ ψ y) hy
  obtain ⟨W,hW,herr,ho,w,hw⟩ := plane_frozen_elliptic_replacement (8*R)
    (cmcJacobian p₀) (by norm_num : (0:ℝ)<1/8)
    (fun v ↦ by simpa only [real_inner_comm] using cmcJacobian_coercive hp₀ v) G F hF
  have hres := frozen_coefficient_local_residual_bound (cmcJacobian p₀)
    hmem.coeFn_toLp hgs hδ hosc
  have herror : ‖W‖≤8*δ*‖G‖ := by nlinarith [herr.trans hres]
  have hn : ‖G-W‖≤9*‖G‖ := (norm_sub_le G W).trans (by
    nlinarith [mul_le_mul_of_nonneg_right hδ1 (norm_nonneg G)])
  have hg' := hgrad.Lp_sub (hw.mono (subset_univ _))
  obtain ⟨H,hH,he,hb,hl⟩ := hbound R hR p₀ hp₀ (u-w) (G-W) hg'
    (fun ψ hψ hc hs ↦ frozen_replacement_divergence (cmcJacobian p₀) ho hψ hc hs)
  have hM : (∫ y in Metric.closedBall (0 : Plane) (8*R),‖(G-W : Lp Plane 2 volume) y‖)≤
      144*Real.sqrt Real.pi*R*‖G‖ := by
    calc
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*‖G-W‖ := L2_local_L1 (by positivity) (G-W)
      _ ≤ 2*Real.sqrt Real.pi*(8*R)*(9*‖G‖) :=
        mul_le_mul_of_nonneg_left hn (by positivity)
      _ = _ := by ring
  refine ⟨w,W,H,hW,hw,herror,hH,he,?_,?_⟩
  · intro x
    calc
      _ ≤ C*R⁻¹^2*(∫ y in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) y‖) := hb x
      _ ≤ C*R⁻¹^2*(144*Real.sqrt Real.pi*R*‖G‖) := mul_le_mul_of_nonneg_left hM (by positivity)
      _ = _ := by field_simp
  · intro x y
    calc
      _ ≤ C*R⁻¹^3*(∫ z in Metric.closedBall 0 (8*R),‖(G-W : Lp Plane 2 volume) z‖)*‖x-y‖ := hl x y
      _ ≤ C*R⁻¹^3*(144*Real.sqrt Real.pi*R*‖G‖)*‖x-y‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hM (by positivity)) (norm_nonneg _)
      _ = _ := by field_simp

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_L2_sub_const_integrable (G : Lp Plane 2 (volume : Measure Plane))
    (q : Plane) (ρ : ℝ) :
    IntegrableOn (fun y ↦ ‖G y-q‖^2) (Metric.ball 0 ρ) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball (0 : Plane) ρ)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hh := ((Lp.memLp G).restrict (Metric.ball 0 ρ)).sub (memLp_const q)
  exact (memLp_two_iff_integrable_sq hh.norm.aestronglyMeasurable).mp hh.norm

end CubicTorus
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_L2ReplacementBallBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma L2_replacement_ball_bound (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) (q : Plane) {ρ M : ℝ} (hρ : 0≤ρ) (hM : 0≤M)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 ρ)] H)
    (hb : ∀ y∈Metric.ball 0 ρ,‖H y-q‖≤M) :
    (∫ y in Metric.ball 0 ρ,‖G y-q‖^2)≤2*‖W‖^2+2*Real.pi*ρ^2*M^2 := by
  have hi := plane_L2_sub_const_integrable G q ρ
  have hw := (L2_vector_norm_sq_integrable W).integrableOn (s := Metric.ball 0 ρ)
  have hc : IntegrableOn (fun _ : Plane ↦ 2*M^2) (Metric.ball 0 ρ) :=
    integrableOn_const measure_ball_lt_top.ne
  have hpoint : ∀ᵐ y ∂volume.restrict (Metric.ball (0 : Plane) ρ),
      ‖G y-q‖^2≤2*‖W y‖^2+2*M^2 := by
    filter_upwards [he,ae_restrict_of_ae (Lp.coeFn_sub G W),ae_restrict_mem measurableSet_ball]
      with y hy hz hys
    change (G-W : Lp Plane 2 volume) y=H y at hy
    change (G-W : Lp Plane 2 volume) y=G y-W y at hz
    have hEq : G y-q=W y+(H y-q) := by rw [← hy,hz]; abel
    have hn := (norm_add_le (W y) (H y-q))
    rw [← hEq] at hn
    have hs := (sq_le_sq₀ (norm_nonneg (H y-q)) hM).mpr (hb y hys)
    nlinarith [sq_nonneg (‖W y‖-‖H y-q‖),norm_nonneg (G y-q),norm_nonneg (W y),norm_nonneg (H y-q)]
  calc
    _ ≤ ∫ y in Metric.ball 0 ρ,2*‖W y‖^2+2*M^2 :=
      integral_mono_ae hi ((hw.const_mul 2).add hc) hpoint
    _ = 2*(∫ y in Metric.ball 0 ρ,‖W y‖^2)+2*Real.pi*ρ^2*M^2 := by
      rw [integral_add (hw.const_mul 2) hc,integral_const_mul,integral_const,smul_eq_mul]
      rw [show (volume.restrict (Metric.ball (0 : Plane) ρ)).real univ=
        volume.real (Metric.ball (0 : Plane) ρ) by simp [Measure.real],plane_ball_real hρ]
      ring
    _ ≤ _ := by
      apply add_le_add _ le_rfl
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      rw [L2_vector_norm_sq_integral]
      exact setIntegral_le_integral (L2_vector_norm_sq_integrable W)
        (Eventually.of_forall fun _ ↦ sq_nonneg _)

lemma L2_replacement_energy_decay (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) {R ρ M : ℝ} (hρ : 0≤ρ) (hρR : ρ≤R) (hM : 0≤M)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H)
    (hb : ∀ y,‖H y‖≤M) :
    (∫ y in Metric.ball 0 ρ,‖G y‖^2)≤2*‖W‖^2+2*Real.pi*ρ^2*M^2 := by
  simpa only [sub_zero] using L2_replacement_ball_bound G W H 0 hρ hM
    (ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρR)) he)
    (fun y _ ↦ by simpa only [sub_zero] using hb y)

lemma L2_replacement_oscillation_decay (G W : Lp Plane 2 (volume : Measure Plane))
    (H : Plane → Plane) {R ρ L : ℝ} (hρ : 0≤ρ) (hρR : ρ≤R) (hL : 0≤L)
    (he : ((G-W : Lp Plane 2 volume) : Plane → Plane)=ᵐ[volume.restrict (Metric.ball 0 R)] H)
    (hl : ∀ x y,‖H x-H y‖≤L*‖x-y‖) :
    (∫ y in Metric.ball 0 ρ,‖G y-H 0‖^2)≤2*‖W‖^2+2*Real.pi*L^2*ρ^4 := by
  have hb : ∀ y∈Metric.ball 0 ρ,‖H y-H 0‖≤L*ρ := by
    intro y hy
    have hn : ‖y‖≤ρ := (show ‖y‖<ρ from by
      simpa only [Metric.mem_ball,dist_zero_right] using hy).le
    have hh : ‖H y-H 0‖≤L*‖y‖ := by simpa only [sub_zero] using hl y 0
    exact hh.trans (mul_le_mul_of_nonneg_left hn hL)
  have hh := L2_replacement_ball_bound G W H (H 0) hρ (mul_nonneg hL hρ)
    (ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρR)) he) hb
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma weak_divergence_local_congr {S : Set Plane} (hS : MeasurableSet S)
    {G G' : Plane → Plane} (A : Plane → Plane →L[ℝ] Plane)
    (hG : G'=ᵐ[volume.restrict S] G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G y)))=0) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G' y)))=0 := by
  have he := (ae_restrict_iff' hS).mp hG
  intro ψ hψ hc hs
  rw [← hd ψ hψ hc hs]
  apply integral_congr_ae
  filter_upwards [he] with y hy
  by_cases hys : y∈S
  · rw [hy hys]
  · rw [fderiv_of_notMem_tsupport ℝ (fun hh ↦ hys (hs hh)),zero_apply,zero_apply]

lemma L2_gradient_truncate (G : Lp Plane 2 (volume : Measure Plane))
    {S : Set Plane} (hS : MeasurableSet S) :
    ∃ G' : Lp Plane 2 (volume : Measure Plane),
      (G' : Plane → Plane)=ᵐ[volume.restrict S] G ∧
      (∀ᵐ y ∂volume,y∉S → G' y=0) ∧
      ‖G'‖^2=(∫ y in S,‖G y‖^2) := by
  have hm := (Lp.memLp G).indicator hS
  let G' := hm.toLp (S.indicator (G : Plane → Plane))
  refine ⟨G',?_,?_,?_⟩
  · filter_upwards [ae_restrict_of_ae hm.coeFn_toLp,ae_restrict_mem hS] with y hy hys
    exact hy.trans (indicator_of_mem hys _)
  · filter_upwards [hm.coeFn_toLp] with y hy hys
    exact hy.trans (indicator_of_notMem hys _)
  · rw [L2_vector_norm_sq_integral,← integral_indicator hS]
    apply integral_congr_ae
    filter_upwards [hm.coeFn_toLp] with y hy
    change ‖G' y‖^2=S.indicator (fun y ↦ ‖G y‖^2) y
    change G' y=S.indicator (G : Plane → Plane) y at hy
    rw [hy]
    by_cases hys : y∈S <;> simp [hys]

lemma plane_L2_energy_mono (G : Lp Plane 2 (volume : Measure Plane)) :
    Monotone (fun r : ℝ ↦ ∫ y in Metric.ball (0 : Plane) r,‖G y‖^2) := by
  intro r s hrs
  exact setIntegral_mono_set (L2_vector_norm_sq_integrable G).integrableOn
    (Eventually.of_forall fun _ ↦ sq_nonneg _) (Metric.ball_subset_ball hrs).eventuallyLE

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma PlaneWeakGradient.comp_add {S : Set Plane} {u : Plane → ℝ} {G : Plane → Plane}
    (hg : PlaneWeakGradient S u G) (a : Plane) :
    PlaneWeakGradient ((fun y ↦ y+a) ⁻¹' S) (fun y ↦ u (y+a)) (fun y ↦ G (y+a)) := by
  intro v ψ hψ hc hs
  let φ : Plane → ℝ := fun y ↦ ψ (y + -a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight (-a))
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ Homeomorph.addRight (-a))⊆S
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simpa using hh
  have hh := hg v φ hφ hφc hφs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ ⟪G y,v⟫*φ y) a
  have hj := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ u y*fderiv ℝ φ y v) a
  simp only [φ,fderiv_comp_add_right,add_neg_cancel_right] at hi hj hh
  rw [hi,hj]
  exact hh

lemma variable_divergence_comp_add {S : Set Plane} (A : Plane → Plane →L[ℝ] Plane)
    (G : Plane → Plane)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆S → (∫ y,fderiv ℝ ψ y (A y (G y)))=0) (a : Plane) :
    ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆(fun y ↦ y+a) ⁻¹' S →
      (∫ y,fderiv ℝ ψ y (A (y+a) (G (y+a))))=0 := by
  intro ψ hψ hc hs
  let φ : Plane → ℝ := fun y ↦ ψ (y + -a)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := hψ.comp (contDiff_id.add contDiff_const)
  have hφc : HasCompactSupport φ := hc.comp_homeomorph (Homeomorph.addRight (-a))
  have hφs : tsupport φ⊆S := by
    change tsupport (ψ ∘ Homeomorph.addRight (-a))⊆S
    rw [tsupport_comp_eq_preimage]
    intro y hy
    have hh := hs hy
    simpa using hh
  have hh := hd φ hφ hφc hφs
  have hi := integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ fderiv ℝ φ y (A y (G y))) a
  simp only [φ,fderiv_comp_add_right,add_neg_cancel_right] at hh hi
  exact hi.trans hh

lemma translate_preimage_ball (a : Plane) (r : ℝ) :
    (fun y : Plane ↦ y+a) ⁻¹' Metric.ball a r=Metric.ball 0 r := by
  ext y
  simp [dist_eq_norm]

lemma translate_setIntegral {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (a : Plane) (r : ℝ) (f : Plane → X) :
    (∫ y in Metric.ball 0 r,f (y+a))=(∫ y in Metric.ball a r,f y) := by
  have hh := ((measurePreserving_add_right (volume : Measure Plane) a).restrict_preimage
    (s := Metric.ball a r) measurableSet_ball).integral_comp
      (Homeomorph.addRight a).measurableEmbedding f
  rwa [translate_preimage_ball] at hh

lemma L2_translate (G : Lp Plane 2 (volume : Measure Plane)) (a : Plane) :
    ∃ G' : Lp Plane 2 (volume : Measure Plane),
      (G' : Plane → Plane)=ᵐ[volume] (fun y ↦ G (y+a)) ∧
      ‖G'‖^2=‖G‖^2 ∧
      ∀ r : ℝ,∀ q : Plane,(∫ y in Metric.ball 0 r,‖G' y-q‖^2)=
        (∫ y in Metric.ball a r,‖G y-q‖^2) := by
  have hm := (Lp.memLp G).comp_measurePreserving (measurePreserving_add_right volume a)
  let G' := hm.toLp ((G : Plane → Plane) ∘ (fun y ↦ y+a))
  have he : (G' : Plane → Plane)=ᵐ[volume] (fun y ↦ G (y+a)) := hm.coeFn_toLp
  refine ⟨G',he,?_,fun r q ↦ ?_⟩
  · rw [L2_vector_norm_sq_integral,L2_vector_norm_sq_integral]
    exact (integral_congr_ae (he.fun_comp (fun z ↦ ‖z‖^2))).trans
      (integral_add_right_eq_self (μ := (volume : Measure Plane)) (fun y ↦ ‖G y‖^2) a)
  · calc
      _ = ∫ y in Metric.ball 0 r,‖G (y+a)-q‖^2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_of_ae he] with y hy
        rw [hy]
      _ = _ := translate_setIntegral a r (fun y ↦ ‖G y-q‖^2)

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_replacement_decay :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R δ : ℝ,0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball 0 (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball 0 (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball 0 ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+128*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2) ∧
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+128*δ^2)*(∫ y in Metric.ball 0 (8*R),‖G y‖^2) := by
  obtain ⟨C,hC,hbound⟩ := cmc_replacement_bounds
  refine ⟨2*Real.pi*C^2,by positivity,fun p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G hg hd ↦ ?_⟩
  obtain ⟨G',he,hgs,hn⟩ := L2_gradient_truncate G
    (S := Metric.ball (0 : Plane) (8*R)) measurableSet_ball
  have hg' := PlaneWeakGradient.local_congr measurableSet_ball hg EventuallyEq.rfl he
  have hd' := weak_divergence_local_congr measurableSet_ball (fun y ↦ cmcJacobian (p y)) he hd
  obtain ⟨w,W,H,hW,hw,herr,hH,hrep,hb,hl⟩ :=
    hbound p hp hpb p₀ hp₀ R δ hR hδ hδ1 hosc u G' hgs hg' hd'
  have heW : ‖W‖^2≤64*δ^2*‖G'‖^2 := by
    have hh := pow_le_pow_left₀ (norm_nonneg W) herr 2
    nlinarith
  refine ⟨H 0,fun ρ hρ hρR ↦ ?_⟩
  have hρ8 : ρ≤8*R := by linarith
  have heρ := ae_mono (Measure.restrict_mono_set volume (Metric.ball_subset_ball hρ8)) he
  have heq (q : Plane) : (∫ y in Metric.ball 0 ρ,‖G' y-q‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y-q‖^2) := by
    apply integral_congr_ae
    filter_upwards [heρ] with y hy
    rw [hy]
  have heq0 : (∫ y in Metric.ball 0 ρ,‖G' y‖^2)=
      (∫ y in Metric.ball 0 ρ,‖G y‖^2) := by simpa only [sub_zero] using heq 0
  have hh := L2_replacement_energy_decay G' W H hρ hρR (by positivity : 0≤C*R⁻¹*‖G'‖) hrep hb
  have ho := L2_replacement_oscillation_decay G' W H hρ hρR
    (by positivity : 0≤C*R⁻¹^2*‖G'‖) hrep hl
  rw [heq0] at hh
  rw [heq (H 0)] at ho
  constructor
  · calc
      _ ≤ 2*‖W‖^2+2*Real.pi*ρ^2*(C*R⁻¹*‖G'‖)^2 := hh
      _ ≤ 2*(64*δ^2*‖G'‖^2)+2*Real.pi*ρ^2*(C*R⁻¹*‖G'‖)^2 := by linarith
      _ = (2*Real.pi*C^2*(ρ/R)^2+128*δ^2)*‖G'‖^2 := by ring
      _ = _ := by rw [hn]
  · calc
      _ ≤ 2*‖W‖^2+2*Real.pi*(C*R⁻¹^2*‖G'‖)^2*ρ^4 := ho
      _ ≤ 2*(64*δ^2*‖G'‖^2)+2*Real.pi*(C*R⁻¹^2*‖G'‖)^2*ρ^4 := by linarith
      _ = (2*Real.pi*C^2*(ρ/R)^4+128*δ^2)*‖G'‖^2 := by ring
      _ = _ := by rw [hn]

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma geometric_energy_decay {E : ℝ → ℝ} {R θ β : ℝ}
    (hR : 0<R) (hER : 0≤E R) (hθ : 0<θ) (hθ1 : θ<1) (hβ : 0≤β)
    (hmono : MonotoneOn E (Ioc 0 R))
    (hdecay : ∀ s : ℝ,0 < s → s≤R → E (θ*s)≤θ^β*E s)
    {r : ℝ} (hr : 0 < r) (hrR : r≤R) :
    E r≤θ^(-β)*(r/R)^β*E R := by
  have hp (i : ℕ) : E (θ^i*R)≤(θ^β)^i*E R := by
    induction i with
    | zero => simp
    | succ i hi =>
      have hs : θ^i*R≤R := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hR.le
      calc
        _ = E (θ*(θ^i*R)) := by congr 1; ring
        _ ≤ θ^β*E (θ^i*R) := hdecay _ (by positivity) hs
        _ ≤ θ^β*((θ^β)^i*E R) := mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hθ.le β)
        _ = _ := by ring
  obtain ⟨i,hi,h'i⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) hθ hθ1
  have hs : r≤θ^i*R := (div_le_iff₀ hR).mp h'i
  have hsR : θ^i*R≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ hθ.le hθ1.le) hR.le
  have hpow : (θ^β)^(i+1)≤(r/R)^β := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hθ.le,mul_comm,
      Real.rpow_mul hθ.le,Real.rpow_natCast]
    exact Real.rpow_le_rpow (pow_nonneg hθ.le _) hi.le hβ
  have hdivide : (θ^β)^i≤θ^(-β)*(r/R)^β := by
    rw [pow_succ] at hpow
    rw [Real.rpow_neg hθ.le]
    have ht : 0<θ^β := Real.rpow_pos_of_pos hθ _
    exact (le_inv_mul_iff₀ ht).mpr (by simpa only [mul_comm] using hpow)
  exact (hmono ⟨hr,hrR⟩ ⟨by positivity,hsR⟩ hs).trans
    ((hp i).trans (mul_le_mul_of_nonneg_right hdivide hER))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma exists_decay_contraction {A β : ℝ} (hA : 0<A) (hβ : 0<β) (hβ2 : β<2) :
    ∃ θ δ₀ : ℝ, 0<θ ∧ θ≤1/16 ∧ 0<δ₀ ∧ δ₀≤1 ∧
      ∀ δ : ℝ,0≤δ → δ≤δ₀ → A*(8*θ)^2+128*δ^2≤θ^β := by
  have hc : ContinuousAt (fun t : ℝ ↦ t^(2-β)) 0 :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by linarith))
  have he : ∀ᶠ t : ℝ in 𝓝 0,t^(2-β)<(1/2)/(64*A) :=
    hc.eventually_lt continuousAt_const (by
      rw [Real.zero_rpow (by linarith : 2-β≠0)]
      exact div_pos (by norm_num) (mul_pos (by norm_num) hA))
  obtain ⟨ε,hε,hεs⟩ := Metric.mem_nhds_iff.mp he
  let θ : ℝ := min (ε/2) (1/16)
  have hθ : 0<θ := lt_min (half_pos hε) (by norm_num)
  have hθε : θ<ε := (min_le_left _ _).trans_lt (by linarith)
  have hθ1 : θ≤1/16 := min_le_right _ _
  have hsmall : 64*A*θ^(2-β)<1/2 := by
    have hpower : θ^(2-β)<(1/2)/(64*A) :=
      hεs (by simpa [Real.dist_eq,abs_of_pos hθ] using hθε)
    simpa only [mul_comm] using (lt_div_iff₀ (mul_pos (by norm_num) hA)).mp hpower
  let δ₀ : ℝ := Real.sqrt (θ^β/256)
  have htβ : 0<θ^β := Real.rpow_pos_of_pos hθ _
  have hd₀ : 0<δ₀ := Real.sqrt_pos.mpr (by positivity)
  have hd₀1 : δ₀≤1 := Real.sqrt_le_one.mpr (by
    have hpower := Real.rpow_le_one hθ.le (hθ1.trans (by norm_num)) hβ.le
    linarith)
  refine ⟨θ,δ₀,hθ,hθ1,hd₀,hd₀1,fun δ hδ hd ↦ ?_⟩
  have hsquare : δ^2≤θ^β/256 := by
    have hh : δ≤Real.sqrt (θ^β/256) := hd
    have hq := pow_le_pow_left₀ hδ hh 2
    rwa [Real.sq_sqrt (by positivity)] at hq
  have hpow : θ^(2-β)*θ^β=θ^2 := by
    rw [← Real.rpow_add hθ]
    simp
  have hfirst : 64*A*θ^2≤θ^β/2 := by
    have hh := mul_le_mul_of_nonneg_right hsmall.le htβ.le
    rw [mul_assoc,hpow] at hh
    linarith
  nlinarith

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_energy_decay {β : ℝ} (hβ : 0<β) (hβ2 : β<2) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ δ₀≤1 ∧
    ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ R : ℝ,0<R →
    (∀ y∈Metric.ball 0 R,‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ₀) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball 0 R) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∀ r : ℝ,0 < r → r≤R →
      (∫ y in Metric.ball 0 r,‖G y‖^2)≤
        C*(r/R)^β*(∫ y in Metric.ball 0 R,‖G y‖^2) := by
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay
  obtain ⟨θ,δ₀,hθ,hθs,hδ,hδ1,hcontract⟩ := exists_decay_contraction hA hβ hβ2
  refine ⟨θ^(-β),δ₀,Real.rpow_pos_of_pos hθ _,hδ,hδ1,
    fun p hp hpb p₀ hp₀ R hR hosc u G hg hd r hr hrR ↦ ?_⟩
  apply geometric_energy_decay hR (integral_nonneg (fun _ ↦ sq_nonneg _)) hθ
    (by linarith) hβ.le ((plane_L2_energy_mono G).monotoneOn _) ?_ hr hrR
  intro s hs hsR
  have h8 : 8*(s/8)=s := by ring
  have hsub : Metric.ball (0 : Plane) (8*(s/8))⊆Metric.ball 0 R :=
    Metric.ball_subset_ball (by rw [h8]; exact hsR)
  obtain ⟨q,hq⟩ := hreplace p hp hpb p₀ hp₀ (s/8) δ₀ (by positivity)
    hδ.le hδ1 (fun y hy ↦ hosc y (hsub hy)) u G
    (fun v ψ hψ hc hs' ↦ hg v ψ hψ hc (hs'.trans hsub))
    (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
  have hsmall : θ*s ≤ s/8/2 := by nlinarith
  have hh := (hq (θ*s) (by positivity) hsmall).1
  have hratio : θ*s/(s/8)=8*θ := by field_simp
  rw [h8,hratio] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right (hcontract δ₀ hδ.le le_rfl)
    (integral_nonneg (fun _ ↦ sq_nonneg _)))

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma linearized_cmc_translate (p : Plane → Plane) (a : Plane) (R : ℝ)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball a R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ (u' : Lp ℝ 2 (volume : Measure Plane)) (G' : Lp Plane 2 (volume : Measure Plane)),
      PlaneWeakGradient (Metric.ball 0 R) u' G' ∧
      (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        tsupport ψ⊆Metric.ball 0 R →
        (∫ y,fderiv ℝ ψ y (cmcJacobian (p (y+a)) (G' y)))=0) ∧
      ‖G'‖^2=‖G‖^2 ∧
      ∀ r : ℝ,∀ q : Plane,(∫ y in Metric.ball 0 r,‖G' y-q‖^2)=
        (∫ y in Metric.ball a r,‖G y-q‖^2) := by
  obtain ⟨G',he,hn,hint⟩ := L2_translate G a
  have hm := (Lp.memLp u).comp_measurePreserving (measurePreserving_add_right volume a)
  let u' := hm.toLp ((u : Plane → ℝ) ∘ (fun y ↦ y+a))
  have hg' := (hg.comp_add a).congr hm.coeFn_toLp he
  rw [translate_preimage_ball] at hg'
  have hd' := variable_divergence_comp_add (fun y ↦ cmcJacobian (p y)) G hd a
  rw [translate_preimage_ball] at hd'
  refine ⟨u',G',hg',?_,hn,hint⟩
  exact weak_divergence_local_congr measurableSet_ball (fun y ↦ cmcJacobian (p (y+a)))
    (ae_restrict_of_ae he) hd'

theorem cmc_replacement_decay_at :
    ∃ A : ℝ,0<A ∧ ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ (a : Plane) (R δ : ℝ),0<R → 0≤δ → δ≤1 →
    (∀ y∈Metric.ball a (8*R),‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball a (8*R)) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a (8*R) → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∃ q : Plane, ∀ ρ : ℝ,0≤ρ → ρ≤R/2 →
      (∫ y in Metric.ball a ρ,‖G y‖^2)≤
        (A*(ρ/R)^2+128*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2) ∧
      (∫ y in Metric.ball a ρ,‖G y-q‖^2)≤
        (A*(ρ/R)^4+128*δ^2)*(∫ y in Metric.ball a (8*R),‖G y‖^2) := by
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay
  refine ⟨A,hA,fun p hp hpb p₀ hp₀ a R δ hR hδ hδ1 hosc u G hg hd ↦ ?_⟩
  obtain ⟨u',G',hg',hd',hn,hint⟩ := linearized_cmc_translate p a (8*R) u G hg hd
  have hi (s : ℝ) : (∫ y in Metric.ball 0 s,‖G' y‖^2)=
      (∫ y in Metric.ball a s,‖G y‖^2) := by simpa only [sub_zero] using hint s 0
  obtain ⟨q,hq⟩ := hreplace (fun y ↦ p (y+a)) (hp.comp (continuous_id.add continuous_const))
    (fun y ↦ hpb _) p₀ hp₀ R δ hR hδ hδ1
    (fun y hy ↦ hosc (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) u' G' hg' hd'
  refine ⟨q,fun ρ hρ hρR ↦ ?_⟩
  have hh := hq ρ hρ hρR
  rwa [hi ρ,hi (8*R),hint ρ q] at hh

theorem cmc_energy_decay_at {β : ℝ} (hβ : 0<β) (hβ2 : β<2) :
    ∃ C δ₀ : ℝ,0<C ∧ 0<δ₀ ∧ δ₀≤1 ∧
    ∀ (p : Plane → Plane),Continuous p → (∀ y,‖p y‖≤1) →
    ∀ p₀ : Plane,‖p₀‖≤1 → ∀ (a : Plane) (R : ℝ),0<R →
    (∀ y∈Metric.ball a R,‖cmcJacobian p₀-cmcJacobian (p y)‖≤δ₀) →
    ∀ (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane)),
    PlaneWeakGradient (Metric.ball a R) u G →
    (∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball a R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) →
    ∀ r : ℝ,0 < r → r≤R →
      (∫ y in Metric.ball a r,‖G y‖^2)≤C*(r/R)^β*‖G‖^2 := by
  obtain ⟨C,δ₀,hC,hδ,hδ1,hdecay⟩ := cmc_energy_decay hβ hβ2
  refine ⟨C,δ₀,hC,hδ,hδ1,fun p hp hpb p₀ hp₀ a R hR hosc u G hg hd r hr hrR ↦ ?_⟩
  obtain ⟨u',G',hg',hd',hn,hint⟩ := linearized_cmc_translate p a R u G hg hd
  have hi (s : ℝ) : (∫ y in Metric.ball 0 s,‖G' y‖^2)=
      (∫ y in Metric.ball a s,‖G y‖^2) := by simpa only [sub_zero] using hint s 0
  have hh := hdecay (fun y ↦ p (y+a)) (hp.comp (continuous_id.add continuous_const))
    (fun y ↦ hpb _) p₀ hp₀ R hR
    (fun y hy ↦ hosc (y+a) (by simpa [Metric.mem_ball,dist_eq_norm] using hy)) u' G' hg' hd' r hr hrR
  rw [hi r] at hh
  have he : (∫ y in Metric.ball 0 R,‖G' y‖^2)≤‖G‖^2 := by
    rw [← hn,L2_vector_norm_sq_integral]
    exact setIntegral_le_integral (L2_vector_norm_sq_integrable G')
      (Eventually.of_forall fun _ ↦ sq_nonneg _)
  exact hh.trans (mul_le_mul_of_nonneg_left he (by positivity))

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma exists_small_power_scale {α ε R : ℝ} (hα : 0<α) (hε : 0<ε)
    (hR : 0<R) (D : ℝ) :
    ∃ r : ℝ,0 < r ∧ r≤R ∧ D*r^α≤ε := by
  have hc : ContinuousAt (fun t : ℝ ↦ D*t^α) 0 :=
    continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inr hα.le))
  have he : ∀ᶠ t : ℝ in 𝓝 0,D*t^α<ε :=
    hc.eventually_lt continuousAt_const (by simpa [Real.zero_rpow hα.ne'] using hε)
  obtain ⟨η,hη,hsub⟩ := Metric.mem_nhds_iff.mp he
  let r : ℝ := min (η/2) R
  have hr : 0 < r := lt_min (half_pos hη) hR
  refine ⟨r,hr,min_le_right _ _,le_of_lt (hsub ?_)⟩
  have hh : r<η := (min_le_left _ _).trans_lt (by linarith)
  simpa [Real.dist_eq,abs_of_pos hr] using hh

end CubicTorus

end
end

end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Estimates_InteriorBallSubset
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma interior_ball_subset {R s : ℝ} {x : Plane}
    (hR : 0<R) (hx : x∈Metric.ball (0 : Plane) (R/4)) (hs : s≤R/4) :
    Metric.ball x s⊆Metric.ball 0 R := by
  intro y hy
  have hh := dist_triangle y x (0 : Plane)
  have hy' : dist y x < s := hy
  have hx' : dist x 0<R/4 := hx
  change dist y 0<R
  linarith

theorem cmc_uniform_energy {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D β : ℝ} (hR : 0<R) (hα : 0<α) (hD : 0≤D)
    (hβ : 0<β) (hβ2 : β<2)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ S K : ℝ,0<S ∧ S≤1 ∧ S≤R/4 ∧ 0≤K ∧ D*S^α≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ s : ℝ,0 < s → s≤S →
        (∫ y in Metric.ball x s,‖G y‖^2)≤K*s^β := by
  obtain ⟨C,δ₀,hC,hδ,hδ1,hdecay⟩ := cmc_energy_decay_at hβ hβ2
  obtain ⟨S,hS,hSbound,hSsmall⟩ := exists_small_power_scale hα hδ
    (lt_min zero_lt_one (by positivity : 0<R/4)) D
  have hS1 : S≤1 := hSbound.trans (min_le_left _ _)
  have hSR : S≤R/4 := hSbound.trans (min_le_right _ _)
  refine ⟨S,C/S^β*‖G‖^2,hS,hS1,hSR,by positivity,hSsmall.trans hδ1,?_⟩
  intro x hx s hs hsS
  have hsub := interior_ball_subset hR hx hSR
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  have hosc : ∀ y∈Metric.ball x S,‖cmcJacobian (p x)-cmcJacobian (p y)‖≤δ₀ := by
    intro y hy
    calc
      _ ≤ D*(dist x y)^α := hHolder x hxR y (hsub hy)
      _ ≤ D*S^α := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow dist_nonneg (by simpa only [dist_comm] using (le_of_lt hy : dist y x≤S)) hα.le) hD
      _ ≤ δ₀ := hSsmall
  have hh := hdecay p hp hpb (p x) (hpb x) x S hS hosc u G (hg.mono hsub)
    (fun ψ hψ hc hsp ↦ hd ψ hψ hc (hsp.trans hsub)) s hs hsS
  rw [Real.div_rpow hs.le hS.le] at hh
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ring

end CubicTorus

end
end

section

noncomputable section
open Set Filter
open scoped Topology
namespace CubicTorus

lemma optimized_oscillation_scale {α s : ℝ} (hα : 0<α) (hα1 : α≤1)
    (hs : 0 < s) (hs1 : s≤1) :
    0 < s^(1+α/2)/16 ∧ s^(1+α/2)/16 ≤ s/8/2 := by
  have hlower : s^(3/2 : ℝ) ≤ s^(1+α/2) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith)
  have hh := Real.rpow_le_rpow_of_exponent_ge hs hs1 (by linarith : (1:ℝ)≤1+α/2)
  rw [Real.rpow_one] at hh
  exact ⟨div_pos ((Real.rpow_pos_of_pos hs _).trans_le hlower) (by norm_num),by linarith⟩

lemma optimized_oscillation_identity {α s : ℝ} (hα : 0<α) (hs : 0 < s)
    (A D K : ℝ) :
    (A*((s^(1+α/2)/16)/(s/8))^4+128*(D*s^α)^2)*(K*s^(2-α/2))=
      ((A/16+128*D^2)*K*16^(2+α/(2+α)))*(s^(1+α/2)/16)^(2+α/(2+α)) := by
  have hr : (s^(1+α/2)/16)/(s/8)=s^(α/2)/2 := by
    rw [Real.rpow_add hs,Real.rpow_one]
    field_simp
    norm_num
  have h4 : (s^(α/2))^4=s^(2*α) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 1
    ring
  have h2 : (s^α)^2=s^(2*α) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul hs.le]
    congr 1
    ring
  have he : s^(2*α)*s^(2-α/2)=s^(2+3*α/2) := by
    rw [← Real.rpow_add hs]
    congr 1
    ring
  have hex : (1+α/2)*(2+α/(2+α))=2+3*α/2 := by
    field_simp
    ring
  have hright : 16^(2+α/(2+α))*(s^(1+α/2)/16)^(2+α/(2+α))=s^(2+3*α/2) := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    rw [show (16:ℝ)*(s^(1+α/2)/16)=s^(1+α/2) by ring]
    rw [← Real.rpow_mul hs.le,hex]
  rw [hr,div_pow,mul_pow,h4,h2]
  calc
    _ = (A/16+128*D^2)*K*(s^(2*α)*s^(2-α/2)) := by ring
    _ = (A/16+128*D^2)*K*s^(2+3*α/2) := by rw [he]
    _ = _ := by rw [← hright]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

theorem cmc_uniform_oscillation {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ r C γ : ℝ,0 < r ∧ 0≤C ∧ 0<γ ∧ γ≤1 ∧
      ∀ x∈Metric.ball (0 : Plane) (R/4),∀ ρ : ℝ,0<ρ → ρ ≤ r →
        ∃ q : Plane,(∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+γ) := by
  obtain ⟨S,K,hS,hS1,hSR,hK,hSsmall,henergy⟩ :=
    cmc_uniform_energy hp hpb hR hα hD (by linarith : 0<2-α/2) (by linarith : 2-α/2<2)
      hHolder u G hg hd
  obtain ⟨A,hA,hreplace⟩ := cmc_replacement_decay_at
  let k : ℝ := 1+α/2
  have hk : 0<k := by dsimp [k]; linarith
  let γ : ℝ := α/(2+α)
  have hγ : 0<γ := by dsimp [γ]; positivity
  have hγ1 : γ≤1 := (div_le_one (by linarith : 0<2+α)).mpr (by linarith)
  let C : ℝ := (A/16+128*D^2)*K*16^(2+γ)
  refine ⟨S^k/16,C,γ,by positivity,by dsimp [C]; positivity,hγ,hγ1,?_⟩
  intro x hx ρ hρ hρr
  let s : ℝ := (16*ρ)^(1/k)
  have hs : 0 < s := Real.rpow_pos_of_pos (by positivity) _
  have hspow : s^k=16*ρ := by
    dsimp [s]
    rw [← Real.rpow_mul (by positivity)]
    rw [one_div_mul_cancel hk.ne',Real.rpow_one]
  have hSpow : (S^k)^(1/k)=S := by
    rw [← Real.rpow_mul hS.le]
    rw [mul_one_div_cancel hk.ne',Real.rpow_one]
  have hsS : s≤S := by
    rw [← hSpow]
    exact Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hs1 : s≤1 := hsS.trans hS1
  have hρeq : s^(1+α/2)/16=ρ := by change s^k/16=ρ; rw [hspow]; ring
  have h8 : 8*(s/8)=s := by ring
  have hsub : Metric.ball x (8*(s/8))⊆Metric.ball 0 R := by
    rw [h8]
    exact interior_ball_subset hR hx (hsS.trans hSR)
  have hxR : x∈Metric.ball (0 : Plane) R :=
    (Metric.ball_subset_ball (by linarith : R/4≤R)) hx
  have hδ1 : D*s^α≤1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hs.le hsS hα.le) hD).trans hSsmall
  have hosc : ∀ y∈Metric.ball x (8*(s/8)),
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*s^α := by
    intro y hy
    apply (hHolder x hxR y (hsub hy)).trans
    apply mul_le_mul_of_nonneg_left _ hD
    apply Real.rpow_le_rpow dist_nonneg _ hα.le
    rw [h8] at hy
    exact (dist_comm x y ▸ (le_of_lt hy : dist y x≤ s))
  obtain ⟨q,hq⟩ := hreplace p hp hpb (p x) (hpb x) x (s/8) (D*s^α)
    (by positivity) (by positivity) hδ1 hosc u G (hg.mono hsub)
    (fun ψ hψ hc hs' ↦ hd ψ hψ hc (hs'.trans hsub))
  have hscale := optimized_oscillation_scale hα hα1 hs hs1
  have hh := (hq (s^(1+α/2)/16) hscale.1.le hscale.2).2
  rw [h8,hρeq] at hh
  refine ⟨q,hh.trans ?_⟩
  calc
    _ ≤ (A*(ρ/(s/8))^4+128*(D*s^α)^2)*(K*s^(2-α/2)) :=
      mul_le_mul_of_nonneg_left (henergy x hx s hs hsS) (by positivity)
    _ = C*ρ^(2+γ) := by
      rw [← hρeq]
      exact optimized_oscillation_identity hα hs A D K

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_ball_real_at (a : Plane) {r : ℝ} (hr : 0 ≤ r) :
    (volume : Measure Plane).real (Metric.ball a r)=Real.pi*r^2 := by
  rw [show volume.real (Metric.ball a r)=volume.real (Metric.ball (0 : Plane) r) by
    simp only [Measure.real,Measure.addHaar_ball_center volume a]]
  exact plane_ball_real hr

lemma plane_L2_sub_const_integrable_at (G : Lp Plane 2 (volume : Measure Plane))
    (q a : Plane) (r : ℝ) : IntegrableOn (fun y ↦ ‖G y-q‖^2) (Metric.ball a r) := by
  let : IsFiniteMeasure (volume.restrict (Metric.ball a r)) :=
    isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hh := ((Lp.memLp G).restrict (Metric.ball a r)).sub (memLp_const q)
  exact (memLp_two_iff_integrable_sq hh.norm.aestronglyMeasurable).mp hh.norm

lemma plane_L2_sub_const_mono (G : Lp Plane 2 (volume : Measure Plane))
    (q : Plane) {a b : Plane} {r s : ℝ} (hsub : Metric.ball a r⊆Metric.ball b s) :
    (∫ y in Metric.ball a r,‖G y-q‖^2)≤(∫ y in Metric.ball b s,‖G y-q‖^2) :=
  setIntegral_mono_set (plane_L2_sub_const_integrable_at G q b s)
    (Eventually.of_forall fun _ ↦ sq_nonneg _) hsub.eventuallyLE

lemma campanato_constant_distance (G : Lp Plane 2 (volume : Measure Plane))
    {a q q' : Plane} {r C β : ℝ} (hr : 0 < r) (hC : 0≤C)
    (h₁ : (∫ y in Metric.ball a (r/2),‖G y-q‖^2)≤C*r^(2+2*β))
    (h₂ : (∫ y in Metric.ball a (r/2),‖G y-q'‖^2)≤C*r^(2+2*β)) :
    dist q q'≤4*Real.sqrt C*r^β := by
  have hi := plane_L2_sub_const_integrable_at G q a (r/2)
  have hj := plane_L2_sub_const_integrable_at G q' a (r/2)
  have hc : IntegrableOn (fun _ : Plane ↦ ‖q-q'‖^2) (Metric.ball a (r/2)) :=
    integrableOn_const measure_ball_lt_top.ne
  have hp (y : Plane) : ‖q-q'‖^2≤2*‖G y-q‖^2+2*‖G y-q'‖^2 := by
    have hn : ‖q-q'‖≤‖G y-q‖+‖G y-q'‖ := by
      simpa only [← dist_eq_norm,dist_comm q (G y)] using dist_triangle q (G y) q'
    nlinarith [norm_nonneg (q-q'),norm_nonneg (G y-q),norm_nonneg (G y-q'),
      sq_nonneg (‖G y-q‖-‖G y-q'‖)]
  have hh := integral_mono hc ((hi.const_mul 2).add (hj.const_mul 2)) hp
  change (∫ x in Metric.ball a (r/2),‖q-q'‖^2)≤
    (∫ x in Metric.ball a (r/2),2*‖G x-q‖^2+2*‖G x-q'‖^2) at hh
  rw [integral_add (hi.const_mul 2) (hj.const_mul 2),integral_const_mul,integral_const_mul,
    integral_const,smul_eq_mul] at hh
  rw [show (volume.restrict (Metric.ball a (r/2))).real univ=
    volume.real (Metric.ball a (r/2)) by simp [Measure.real],plane_ball_real_at a (by positivity)] at hh
  have hpow : r^(2+2*β)=r^2*(r^β)^2 := by
    rw [Real.rpow_add hr,Real.rpow_two,mul_comm (2:ℝ) β,Real.rpow_mul hr.le,Real.rpow_two]
  rw [hpow] at h₁ h₂
  have hpi : r^2*‖q-q'‖^2≤Real.pi*r^2*‖q-q'‖^2 := by
    have hπ : (1:ℝ)≤Real.pi := by linarith [Real.pi_gt_three]
    simpa only [one_mul,mul_assoc] using mul_le_mul_of_nonneg_right hπ
      (mul_nonneg (sq_nonneg r) (sq_nonneg ‖q-q'‖))
  have hsquare : ‖q-q'‖^2≤(4*Real.sqrt C*r^β)^2 := by
    apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hr)).mp
    calc
      _ ≤ 16*C*r^2*(r^β)^2 := by nlinarith
      _ = _ := by rw [mul_pow,mul_pow,Real.sq_sqrt hC]; ring
  rw [dist_eq_norm]
  have hb : 0≤4*Real.sqrt C*r^β := by positivity
  nlinarith [norm_nonneg (q-q')]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_point_limit (G : Lp Plane 2 (volume : Measure Plane))
    (a : Plane) {R C β : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β)
    (hosc : ∀ r : ℝ,0 < r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane,∀ r : ℝ,0 < r → r≤R → ∀ q : Plane,
      (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β) →
      dist H q≤(4*Real.sqrt C*(1+1/(1-(1/2:ℝ)^β))*2^β)*r^β := by
  let s : ℕ → ℝ := fun i ↦ (1/2:ℝ)^i*R
  have hs (i : ℕ) : 0 < s i := by dsimp [s]; positivity
  have hsR (i : ℕ) : s i≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)) hR.le
  have hsucc (i : ℕ) : s (i+1)=s i/2 := by dsimp [s]; rw [pow_succ]; ring
  choose q hq using fun i ↦ hosc (s i) (hs i) (hsR i)
  let θ : ℝ := (1/2:ℝ)^β
  let M : ℝ := 4*Real.sqrt C
  have hM : 0≤M := by dsimp [M]; positivity
  have hθ : 0<θ := Real.rpow_pos_of_pos (by norm_num) _
  have hθ1 : θ<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hp (i : ℕ) : (s i)^β=R^β*θ^i := by
    dsimp [s,θ]
    rw [Real.mul_rpow (by positivity) hR.le]
    rw [← Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤1/2),mul_comm (i:ℝ),
      Real.rpow_mul (by norm_num : (0:ℝ)≤1/2),Real.rpow_natCast]
    ring
  have hstep (i : ℕ) : dist (q i) (q (i+1))≤(M*R^β)*θ^i := by
    have hlo : s i/2 ≤ s i := by linarith [hs i]
    have h₁ : (∫ y in Metric.ball a (s i/2),‖G y-q i‖^2)≤C*(s i)^(2+2*β) :=
      (plane_L2_sub_const_mono G (q i) (Metric.ball_subset_ball hlo)).trans (hq i)
    have h₂ : (∫ y in Metric.ball a (s i/2),‖G y-q (i+1)‖^2)≤C*(s i)^(2+2*β) := by
      rw [← hsucc]
      apply (hq (i+1)).trans
      apply mul_le_mul_of_nonneg_left _ hC
      exact Real.rpow_le_rpow (hs _).le (by rw [hsucc]; exact hlo) (by linarith)
    have hh := campanato_constant_distance G (hs i) hC h₁ h₂
    rw [hp i] at hh
    exact hh.trans_eq (by dsimp [M]; ring)
  obtain ⟨H,hH⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_le_geometric θ (M*R^β) hθ1 hstep)
  have happrox (i : ℕ) : dist H (q i)≤M/(1-θ)*(s i)^β := by
    have hh := dist_le_of_le_geometric_of_tendsto θ (M*R^β) hθ1 hstep hH i
    rw [dist_comm,hp i]
    exact hh.trans_eq (by ring)
  refine ⟨H,fun r hr hrR q₀ hq₀ ↦ ?_⟩
  obtain ⟨i,hi,h'i⟩ := exists_nat_pow_near_of_lt_one (div_pos hr hR)
    ((div_le_one hR).mpr hrR) (by norm_num : (0:ℝ)<1/2) (by norm_num : (1/2:ℝ)<1)
  have hrsi : r≤ s i := (div_le_iff₀ hR).mp h'i
  have hsir : s i≤2*r := by
    have hh := (lt_div_iff₀ hR).mp hi
    rw [pow_succ] at hh
    dsimp [s]
    nlinarith
  have hq₁ : (∫ y in Metric.ball a r,‖G y-q i‖^2)≤C*(2*r)^(2+2*β) := by
    apply (plane_L2_sub_const_mono G (q i) (Metric.ball_subset_ball hrsi)).trans
    exact (hq i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hs i).le hsir (by linarith)) hC)
  have hq₂ : (∫ y in Metric.ball a r,‖G y-q₀‖^2)≤C*(2*r)^(2+2*β) :=
    hq₀.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hr.le (by linarith : r≤2*r) (by linarith)) hC)
  have hnear : dist (q i) q₀≤M*(2*r)^β := by
    apply campanato_constant_distance G (by positivity : 0<2*r) hC
    · simpa only [mul_div_cancel_left₀ r (by norm_num : (2:ℝ)≠0)] using hq₁
    · simpa only [mul_div_cancel_left₀ r (by norm_num : (2:ℝ)≠0)] using hq₂
  calc
    _ ≤ dist H (q i)+dist (q i) q₀ := dist_triangle _ _ _
    _ ≤ M/(1-θ)*(s i)^β+M*(2*r)^β := add_le_add (happrox i) hnear
    _ ≤ M/(1-θ)*(2*r)^β+M*(2*r)^β := by
      apply add_le_add _ le_rfl
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (hs i).le hsir hβ.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num) hr.le]; dsimp [M,θ]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_holder_field (G : Lp Plane 2 (volume : Measure Plane))
    {R C β s : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β) (hs : 0 < s) (hsR : 4*s≤R)
    (hosc : ∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0 < r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane → Plane,∃ K L : ℝ,0≤K ∧ 0≤L ∧
      (∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β) ∧
      (∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0 < r → r≤R → ∀ q : Plane,
        (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β) → dist (H x) q≤L*r^β) := by
  classical
  let L : ℝ := 4*Real.sqrt C*(1+1/(1-(1/2:ℝ)^β))*2^β
  have hθ : (1/2:ℝ)^β<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hβ
  have hL : 0≤L := by dsimp [L]; positivity
  have hex := fun (x : Plane) (hx : x∈Metric.ball (0 : Plane) s) ↦
    campanato_point_limit G x hR hC hβ (hosc x hx)
  choose H₀ hH₀ using hex
  let H : Plane → Plane := fun x ↦
    if hx : x∈Metric.ball (0 : Plane) s then H₀ x hx else H₀ 0 (Metric.mem_ball_self hs)
  have hH (x : Plane) (hx : x∈Metric.ball (0 : Plane) s) (r : ℝ) (hr : 0 < r) (hrR : r≤R)
      (q : Plane) (hq : (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
      dist (H x) q≤L*r^β := by
    simpa only [H,dite_eq_left hx] using hH₀ x hx r hr hrR q hq
  refine ⟨H,(2*L+4*Real.sqrt C)*2^β,L,by positivity,hL,?_,hH⟩
  intro x hx y hy
  by_cases hxy : x=y
  · subst y; simp [Real.zero_rpow hβ.ne']
  have hd : 0<dist x y := dist_pos.mpr hxy
  let r := 2*dist x y
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r≤R := by
    have hh := dist_triangle x (0 : Plane) y
    have hx' : dist x 0 < s := hx
    have hy' : dist y 0 < s := hy
    rw [dist_comm (0 : Plane) y] at hh
    dsimp [r]; linarith
  obtain ⟨q,hq⟩ := hosc x hx r hr hrR
  obtain ⟨q',hq'⟩ := hosc y hy r hr hrR
  have hsub : Metric.ball x (r/2)⊆Metric.ball y r := by
    intro z hz
    have hz' : dist z x < r/2 := hz
    have hh := dist_triangle z x y
    change dist z y < r
    dsimp [r] at *; linarith
  have h₁ : (∫ z in Metric.ball x (r/2),‖G z-q‖^2)≤C*r^(2+2*β) :=
    (plane_L2_sub_const_mono G q (Metric.ball_subset_ball (by linarith))).trans hq
  have h₂ : (∫ z in Metric.ball x (r/2),‖G z-q'‖^2)≤C*r^(2+2*β) :=
    (plane_L2_sub_const_mono G q' hsub).trans hq'
  have hnear := campanato_constant_distance G hr hC h₁ h₂
  have hxq := hH x hx r hr hrR q hq
  have hyq := hH y hy r hr hrR q' hq'
  calc
    _ ≤ dist (H x) q+dist q q'+dist q' (H y) := dist_triangle4 _ _ _ _
    _ ≤ L*r^β+4*Real.sqrt C*r^β+L*r^β :=
      add_le_add (add_le_add hxq hnear) (by simpa only [dist_comm] using hyq)
    _ = _ := by dsimp [r]; rw [Real.mul_rpow (by norm_num) dist_nonneg]; ring

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma plane_closedBall_ae_ball (a : Plane) (r : ℝ) :
    Metric.closedBall a r =ᵐ[(volume : Measure Plane)] Metric.ball a r := by
  have hh : ∀ᵐ x ∂(volume : Measure Plane),x∉Metric.sphere a r := by
    rw [ae_iff]
    simpa only [not_not,Set.ofPred_mem_eq] using Measure.addHaar_sphere (volume : Measure Plane) a r
  filter_upwards [hh] with x hx
  change dist x a ≠ r at hx
  apply propext
  change (dist x a ≤ r) ↔ (dist x a < r)
  exact ⟨fun h ↦ lt_of_le_of_ne h hx,le_of_lt⟩

lemma campanato_average_distance (G : Lp Plane 2 (volume : Measure Plane))
    {a q : Plane} {r C β : ℝ} (hr : 0 < r) (hC : 0≤C)
    (h : (∫ y in Metric.ball a r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    dist (⨍ y in Metric.ball a r,G y) q≤Real.sqrt C*r^β := by
  let S := Metric.ball a r
  let m : ℝ := volume.real S
  have hm : m=Real.pi*r^2 := plane_ball_real_at a hr.le
  have hmpos : 0 < m := by rw [hm]; positivity
  let : IsFiniteMeasure (volume.restrict S) := isFiniteMeasure_restrict.mpr measure_ball_lt_top.ne
  have hG : IntegrableOn (fun y ↦ G y) S :=
    ((Lp.memLp G).restrict S).integrable (by norm_num)
  have hc : IntegrableOn (fun _ : Plane ↦ q) S := integrableOn_const measure_ball_lt_top.ne
  have hnorm := (hG.sub hc).norm
  have hi := plane_L2_sub_const_integrable_at G q a r
  have hh := integral_square_le_mass hnorm hi
  simp only [Pi.sub_apply] at hh
  have hm' : (volume.restrict S).real univ=m := by simp [Measure.real,m]
  rw [hm'] at hh
  have hpow : r^(2+2*β)=r^2*(r^β)^2 := by
    rw [Real.rpow_add hr,Real.rpow_two,mul_comm (2:ℝ) β,Real.rpow_mul hr.le,Real.rpow_two]
  have hbound : (∫ y in S,‖G y-q‖)≤ m*(Real.sqrt C*r^β) := by
    have hπ : (1:ℝ)≤Real.pi := by linarith [Real.pi_gt_three]
    have haux : m*(C*r^(2+2*β))≤(m*(Real.sqrt C*r^β))^2 := by
      rw [hpow,mul_pow,mul_pow,Real.sq_sqrt hC]
      have hh' : r^2≤ m := by rw [hm]; nlinarith [sq_nonneg r]
      have hh'' := mul_le_mul_of_nonneg_left hh' (mul_nonneg hmpos.le
        (mul_nonneg hC (sq_nonneg (r^β))))
      nlinarith
    have hs := hh.trans ((mul_le_mul_of_nonneg_left h hmpos.le).trans haux)
    have hn : 0≤ m*(Real.sqrt C*r^β) := by positivity
    nlinarith
  have havg : (⨍ y in S,G y)-q=m⁻¹ • (∫ y in S,G y-q) := by
    rw [setAverage_eq,integral_sub hG hc,integral_const]
    rw [hm']
    change m⁻¹ • (∫ y in S,G y)-q=m⁻¹ • ((∫ y in S,G y)-m • q)
    rw [smul_sub,smul_smul,inv_mul_cancel₀ hmpos.ne',one_smul]
  rw [dist_eq_norm,havg,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hmpos)]
  calc
    _ ≤ m⁻¹*(∫ y in S,‖G y-q‖) := mul_le_mul_of_nonneg_left
      (norm_integral_le_integral_norm _) (inv_nonneg.mpr hmpos.le)
    _ ≤ m⁻¹*(m*(Real.sqrt C*r^β)) := mul_le_mul_of_nonneg_left hbound (inv_nonneg.mpr hmpos.le)
    _ = _ := by rw [← mul_assoc,inv_mul_cancel₀ hmpos.ne',one_mul]

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma campanato_identify_ae (G : Lp Plane 2 (volume : Measure Plane))
    {S : Set Plane} (hS : MeasurableSet S) {H : Plane → Plane} {R C β L : ℝ}
    (hR : 0<R) (hC : 0≤C) (hβ : 0<β)
    (hosc : ∀ x∈S,∀ r : ℝ,0 < r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β))
    (hH : ∀ x∈S,∀ r : ℝ,0 < r → r≤R → ∀ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β) → dist (H x) q≤L*r^β) :
    H =ᵐ[volume.restrict S] (G : Plane → Plane) := by
  have hLeb := IsUnifLocDoublingMeasure.ae_tendsto_average (volume : Measure Plane)
    ((Lp.memLp G).locallyIntegrable (by norm_num)) 1
  apply (ae_restrict_iff' hS).mpr
  filter_upwards [hLeb] with x hx hxS
  let s : ℕ → ℝ := fun i ↦ (1/2:ℝ)^i*R
  have hs (i : ℕ) : 0 < s i := by dsimp [s]; positivity
  have hsR (i : ℕ) : s i≤R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (pow_le_one₀ (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)) hR.le
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa only [zero_mul] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
        (by norm_num : (1/2:ℝ)<1)).mul_const R
  have hs0' : Tendsto s atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hs0,Eventually.of_forall hs⟩
  have hLeb' := hx (fun _ : ℕ ↦ x) s hs0' (Eventually.of_forall fun i ↦ by
    simpa only [one_mul,Metric.mem_closedBall,dist_self] using (hs i).le)
  have hLebBall : Tendsto (fun i ↦ ⨍ y in Metric.ball x (s i),G y) atTop (𝓝 (G x)) := by
    convert hLeb' using 1
    all_goals try with_reducible_and_instances rfl
    funext i
    exact (setAverage_congr (f := fun y ↦ G y) (plane_closedBall_ae_ball x (s i))).symm
  have hβlim : Tendsto (fun i ↦ (Real.sqrt C+L)*(s i)^β) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using
      (hs0.rpow_const (Or.inr hβ.le)).const_mul (Real.sqrt C+L)
  have hlim : Tendsto (fun i ↦ ⨍ y in Metric.ball x (s i),G y) atTop (𝓝 (H x)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) _ hβlim
    intro i
    obtain ⟨q,hq⟩ := hosc x hxS (s i) (hs i) (hsR i)
    calc
      _ ≤ dist (⨍ y in Metric.ball x (s i),G y) q+dist q (H x) := dist_triangle _ _ _
      _ ≤ Real.sqrt C*(s i)^β+L*(s i)^β := add_le_add
        (campanato_average_distance G (hs i) hC hq)
        (by simpa only [dist_comm] using hH x hxS (s i) (hs i) (hsR i) q hq)
      _ = _ := by ring
  exact tendsto_nhds_unique hlim hLebBall

end CubicTorus

end
end

section

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace
namespace CubicTorus

lemma continuousOn_of_power_distance {F : Plane → Plane} {S : Set Plane}
    {K β : ℝ} (hβ : 0<β)
    (h : ∀ x∈S,∀ y∈S,dist (F x) (F y)≤K*(dist x y)^β) : ContinuousOn F S := by
  intro x hx
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hd : Tendsto (fun y : Plane ↦ dist y x) (𝓝[S] x) (𝓝 0) := by
    have hc : ContinuousAt (fun y : Plane ↦ dist y x) x :=
      ((continuous_id : Continuous (fun y : Plane ↦ y)).dist continuous_const).continuousAt
    simpa only [dist_self] using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hb : Tendsto (fun y : Plane ↦ K*(dist y x)^β) (𝓝[S] x) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne',mul_zero] using (hd.rpow_const (Or.inr hβ.le)).const_mul K
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ dist_nonneg) _ hb
  filter_upwards [self_mem_nhdsWithin] with y hy
  exact h y hy x hx

theorem plane_campanato_regularity (G : Lp Plane 2 (volume : Measure Plane))
    {R C β s : ℝ} (hR : 0<R) (hC : 0≤C) (hβ : 0<β) (hs : 0 < s) (hsR : 4*s≤R)
    (hosc : ∀ x∈Metric.ball (0 : Plane) s,∀ r : ℝ,0 < r → r≤R → ∃ q : Plane,
      (∫ y in Metric.ball x r,‖G y-q‖^2)≤C*r^(2+2*β)) :
    ∃ H : Plane → Plane,∃ K : ℝ,0≤K ∧ ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  obtain ⟨H,K,L,hK,hL,hHolder,happrox⟩ := campanato_holder_field G hR hC hβ hs hsR hosc
  exact ⟨H,K,hK,continuousOn_of_power_distance hβ hHolder,
    campanato_identify_ae G measurableSet_ball hR hC hβ hosc happrox,hHolder⟩

theorem cmc_linearized_holder_gradient_oai {p : Plane → Plane} (hp : Continuous p)
    (hpb : ∀ y,‖p y‖≤1) {R α D : ℝ} (hR : 0<R) (hα : 0<α) (hα1 : α≤1) (hD : 0≤D)
    (hHolder : ∀ x∈Metric.ball (0 : Plane) R,∀ y∈Metric.ball (0 : Plane) R,
      ‖cmcJacobian (p x)-cmcJacobian (p y)‖≤D*(dist x y)^α)
    (u : Lp ℝ 2 (volume : Measure Plane)) (G : Lp Plane 2 (volume : Measure Plane))
    (hg : PlaneWeakGradient (Metric.ball 0 R) u G)
    (hd : ∀ ψ : Plane → ℝ,ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      tsupport ψ⊆Metric.ball 0 R → (∫ y,fderiv ℝ ψ y (cmcJacobian (p y) (G y)))=0) :
    ∃ H : Plane → Plane,∃ s K β : ℝ,0 < s ∧ s≤R/4 ∧ 0≤K ∧ 0<β ∧ β≤1 ∧
      ContinuousOn H (Metric.ball 0 s) ∧
      H =ᵐ[volume.restrict (Metric.ball (0 : Plane) s)] (G : Plane → Plane) ∧
      ∀ x∈Metric.ball (0 : Plane) s,∀ y∈Metric.ball (0 : Plane) s,
        dist (H x) (H y)≤K*(dist x y)^β := by
  obtain ⟨r,C,γ,hr,hC,hγ,hγ1,hosc⟩ := cmc_uniform_oscillation hp hpb hR hα hα1 hD hHolder u G hg hd
  let s := min (R/4) (r/4)
  have hs : 0 < s := lt_min (by positivity) (by positivity)
  have hsR : s≤R/4 := min_le_left _ _
  have hsr : 4*s ≤ r := by have := min_le_right (R/4) (r/4); dsimp [s]; linarith
  have hh : ∀ x∈Metric.ball (0 : Plane) s,∀ ρ : ℝ,0<ρ → ρ ≤ r → ∃ q : Plane,
      (∫ y in Metric.ball x ρ,‖G y-q‖^2)≤C*ρ^(2+2*(γ/2)) := by
    intro x hx ρ hρ hρr
    simpa only [mul_div_cancel₀ γ (by norm_num : (2:ℝ)≠0)] using
      hosc x ((Metric.ball_subset_ball hsR) hx) ρ hρ hρr
  obtain ⟨H,K,hK,hHc,hHe,hHp⟩ := plane_campanato_regularity G hr hC (half_pos hγ) hs hsr hh
  exact ⟨H,s,K,γ/2,hs,hsR,hK,half_pos hγ,by linarith,hHc,hHe,hHp⟩

end CubicTorus

end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.cmc_linearized_holder_gradient_oai := @OAI.CubicTorus.cmc_linearized_holder_gradient_oai
