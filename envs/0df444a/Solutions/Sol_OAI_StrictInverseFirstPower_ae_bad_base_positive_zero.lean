-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.ae_bad_base_positive_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:29:52.505517+00:00
-- url     : https://prove2.me/submissions/def8882a-c1b4-4c94-a6f1-71ed9eca07d7

import Mathlib
import Definitions.Def_OAIQWSIFP000
import Theorems.Thm_OAI_StrictInverseFirstPower_koebe_quarter
import Theorems.Thm_OAI_StrictInverseFirstPower_good_targets_bad_source_mass_zero

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

theorem holomorphic_integral_image {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s) (g : ℂ → ℝ) :
    (∫ z in f '' s, g z) = ∫ z in s, ‖deriv f z‖ ^ 2 * g (f z) := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  have h := integral_image_eq_integral_abs_det_fderiv_smul volume hs hreal hi g
  simpa only [det_complexDerivative, abs_sq, smul_eq_mul] using h

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma affineAt_inverse (z : UpperHalfPlane) :
    affineAt z (affineInverse z) = I := by
  dsimp [affineAt, affineInverse]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex Function
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DyadicBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function
open scoped Topology

open Set Filter Metric Complex Function MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 :=
  pow_le_one₀ (by norm_num) (by norm_num)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AffineAveraging
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology

open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

namespace StrictInverseFirstPower
noncomputable section

lemma measurable_rebase_fixed (z : UpperHalfPlane) : Measurable (fun f => rebase f z) :=
  (continuous_rebase.comp (continuous_id.prodMk continuous_const)).measurable

lemma measurable_Qnorm_fixed (z : UpperHalfPlane) : Measurable (fun f => ‖halfPlaneQ f z‖₊) :=
  ((continuous_halfPlaneQ.comp (continuous_id.prodMk continuous_const)).nnnorm).measurable

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FamilyDerivatives
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_holomorphicFamily_deriv {X : Type*} [TopologicalSpace X] {U : Set ℂ}
    (hU : IsOpen U) (F : X → ℂ → ℂ)
    (hF : Continuous (fun p : X × U => F p.1 p.2))
    (hd : ∀ x, DifferentiableOn ℂ (F x) U) :
    Continuous (fun p : X × U => deriv (F p.1) p.2) := by
  let : LocallyCompactSpace U := hU.locallyCompactSpace
  let g : X → C(U, ℂ) := fun x => ⟨fun z => F x z,
    hF.comp (continuous_const.prodMk continuous_id)⟩
  have hg : Continuous g := ContinuousMap.continuous_of_continuous_uncurry g hF
  let g' : X → C(U, ℂ) := fun x => ⟨fun z => deriv (F x) z,
    ((hd x).deriv hU).continuousOn.comp_continuous continuous_subtype_val (fun z => z.property)⟩
  have hg' : Continuous g' := by
    rw [continuous_iff_continuousAt]
    intro x
    rw [ContinuousAt, ContinuousMap.tendsto_iff_tendstoLocallyUniformly]
    have hh : TendstoLocallyUniformlyOn F (F x) (𝓝 x) U := by
      rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
      exact ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hg.tendsto x)
    have hh' := hh.deriv (Eventually.of_forall hd) hU
    rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe] at hh'
    exact hh'
  exact hg'.comp continuous_fst |>.eval continuous_snd

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.ReciprocalMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_reciprocalFunction :
    Continuous (fun p : DiskFamily × HalfPlaneSet => reciprocalFunction p.1 p.2) := by
  have hc : Continuous (fun z : HalfPlaneSet => (⟨z, z.property⟩ : UpperHalfPlane)) :=
    continuous_subtype_val.upperHalfPlaneMk (fun z => z.property)
  change Continuous (fun p : DiskFamily × HalfPlaneSet => halfPlaneQ p.1 ⟨p.2, p.2.property⟩)
  have hmap : Continuous (fun p : DiskFamily × HalfPlaneSet =>
      (p.1, (⟨p.2, p.2.property⟩ : UpperHalfPlane))) :=
    continuous_fst.prodMk (hc.comp continuous_snd)
  have hh := continuous_halfPlaneQ.comp hmap
  exact hh

lemma continuous_reciprocalFunction_deriv :
    Continuous (fun p : DiskFamily × HalfPlaneSet => deriv (reciprocalFunction p.1) p.2) :=
  continuous_holomorphicFamily_deriv isOpen_halfPlane _ continuous_reciprocalFunction
    reciprocalFunction_differentiableOn

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.ImageBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma scale_disk_mem {r : ℝ} (hr : 0 < r) {w : ℂ} (hw : w ∈ ball 0 1) :
    (r : ℂ) * w ∈ ball (0 : ℂ) r := by
  simp only [mem_ball, dist_zero_right] at hw ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  exact mul_lt_of_lt_one_right hr hw

theorem local_koebe_quarter {F : ℂ → ℂ} {a : ℂ} {r : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ F (ball a r)) (hi : InjOn F (ball a r))
    (hn : deriv F a ≠ 0) :
    ball (F a) (r * ‖deriv F a‖ / 4) ⊆ F '' ball a r := by
  let d : ℂ := (r : ℂ) * deriv F a
  have hdne : d ≠ 0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hn
  let g : ℂ → ℂ := fun w => (F (a + (r : ℂ) * w) - F a) / d
  have hm : MapsTo (fun w : ℂ => a + (r : ℂ) * w) (ball 0 1) (ball a r) := by
    intro w hw
    simpa only [mem_ball, dist_eq_norm, add_sub_cancel_left, sub_zero] using scale_disk_mem hr hw
  have hcomp : DifferentiableOn ℂ (fun w => F (a + (r : ℂ) * w)) (ball 0 1) :=
    hd.comp (by fun_prop) hm
  have hgd : DifferentiableOn ℂ g (ball 0 1) := hcomp.sub_const _ |>.div_const _
  have hgi : InjOn g (ball 0 1) := by
    intro w hw u hu he
    have hh := hi (hm hw) (hm hu) (by
      have he' := (div_left_inj' hdne).mp he
      exact sub_left_injective he')
    exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') (add_left_cancel hh)
  have hg0 : g 0 = 0 := by simp [g]
  have hg1 : deriv g 0 = 1 := by
    have ha := (hd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_self hr))).hasDerivAt
    have hb : HasDerivAt (fun w : ℂ => a + (r : ℂ) * w) (r : ℂ) 0 := by
      simpa using ((hasDerivAt_id (0 : ℂ)).const_mul (r : ℂ)).const_add a
    have he : a + (r : ℂ) * 0 = a := by simp
    rw [← he] at ha
    have h := ((ha.comp 0 hb).sub_const (F a)).div_const d
    have hh : HasDerivAt g (deriv F (a + (r : ℂ) * 0) * (r : ℂ) / d) 0 := h
    rw [hh.deriv, he]
    dsimp [d]
    field_simp [hn, Complex.ofReal_ne_zero.mpr hr.ne']
  intro ξ hξ
  have hnorm : ‖d‖ = r * ‖deriv F a‖ := by simp [d, abs_of_pos hr]
  have hh : (ξ - F a) / d ∈ ball (0 : ℂ) (1 / 4) := by
    simp only [mem_ball, dist_eq_norm] at hξ
    simp only [mem_ball, dist_zero_right, norm_div]
    rw [div_lt_iff₀ (norm_pos_iff.mpr hdne), hnorm]
    linarith
  obtain ⟨w, hw, he⟩ := koebe_quarter hgd hgi hg0 hg1 hh
  refine ⟨a + r * w, hm hw, ?_⟩
  exact sub_left_injective ((div_left_inj' hdne).mp he)

lemma disk_outside_half_norm_lower {f : ℂ → ℂ}
    (hd : DifferentiableOn ℂ f (ball 0 1)) (hi : InjOn f (ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) {z : ℂ}
    (hz : z ∈ ball 0 1) (hhalf : 1 / 2 ≤ ‖z‖) : 1 / 8 ≤ ‖f z‖ := by
  by_contra hh
  have hsub : ball (0 : ℂ) (1 / 2) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have him := local_koebe_quarter (F := f) (a := 0) (r := 1 / 2) (by norm_num)
    (hd.mono hsub) (hi.mono hsub) (by rw [h1]; exact one_ne_zero)
  have hball : f z ∈ ball (f 0) ((1 / 2) * ‖deriv f 0‖ / 4) := by
    simp only [h0, h1, norm_one, mul_one, mem_ball, dist_zero_right]
    exact lt_of_lt_of_le (lt_of_not_ge hh) (by norm_num)
  obtain ⟨w, hw, he⟩ := him hball
  have hwz : w = z := hi (hsub hw) hz he
  rw [hwz, mem_ball, dist_zero_right] at hw
  exact (not_lt_of_ge hhalf) hw

lemma halfPlaneFunction_outside_norm_lower (f : DiskFamily) {z : ℂ} (hz : 0 < z.im)
    (hhalf : 1 / 2 ≤ ‖cayleyToDisk z‖) : 1 / 4 ≤ ‖halfPlaneFunction f z‖ := by
  have hh := disk_outside_half_norm_lower f.property.1 f.property.2.1
    f.property.2.2.1 f.property.2.2.2 (cayleyToDisk_mem hz) hhalf
  simp only [halfPlaneFunction, norm_mul, norm_ofNat, norm_I, mul_one]
  linarith

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTails
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma affineInversePlane_re (z : ℂ) : (affineInversePlane z).re = -z.re / z.im := by
  simp [affineInversePlane, Complex.div_ofReal_re]
lemma affineInversePlane_im (z : ℂ) : (affineInversePlane z).im = 1 / z.im := by
  simp [affineInversePlane, Complex.div_ofReal_im]

lemma affineInversePlane_mapsTo :
    MapsTo affineInversePlane {z : ℂ | 0 < z.im} {z : ℂ | 0 < z.im} := by
  intro z hz
  change 0 < (affineInversePlane z).im
  rw [affineInversePlane_im]
  exact one_div_pos.mpr hz

lemma affineInversePlane_involution {z : ℂ} (hz : z.im ≠ 0) :
    affineInversePlane (affineInversePlane z) = z := by
  apply Complex.ext
  · simp only [affineInversePlane_re, affineInversePlane_im]
    field_simp
  · simp [affineInversePlane_im]

lemma affineInversePlane_injOn : InjOn affineInversePlane {z : ℂ | 0 < z.im} := by
  intro z hz w hw he
  have hh := congrArg affineInversePlane he
  rwa [affineInversePlane_involution (ne_of_gt hz),
    affineInversePlane_involution (ne_of_gt hw)] at hh

lemma measurableSet_outsideCenter : MeasurableSet outsideCenter := by
  have hc : Measurable (fun z : ℂ => ‖cayleyToDisk z‖) := by
    unfold cayleyToDisk
    fun_prop
  exact (isOpen_halfPlane.measurableSet).inter (measurableSet_le measurable_const hc)

lemma norm_cayley_inverse {z : ℂ} (hz : 0 < z.im) :
    ‖cayleyToDisk (affineInversePlane z)‖ = ‖cayleyToDisk z‖ := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hnum : affineInversePlane z - I = -(z - I) / (z.im : ℂ) := by
    apply Complex.ext <;>
      simp [affineInversePlane_re, affineInversePlane_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im]; field_simp
  have hden : affineInversePlane z + I = -(conj (z + I)) / (z.im : ℂ) := by
    apply Complex.ext <;>
      simp [affineInversePlane_re, affineInversePlane_im, Complex.div_ofReal_re,
        Complex.div_ofReal_im]; field_simp
  simp only [cayleyToDisk, hnum, hden, norm_div, norm_neg, norm_conj]
  exact div_div_div_cancel_right₀ (norm_ne_zero_iff.mpr hy) _ _

lemma affineInversePlane_outside_image : affineInversePlane '' outsideCenter = outsideCenter := by
  apply Subset.antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨affineInversePlane_mapsTo hz.1, by simpa only [norm_cayley_inverse hz.1] using hz.2⟩
  · intro z hz
    refine ⟨affineInversePlane z, ⟨affineInversePlane_mapsTo hz.1, ?_⟩,
      affineInversePlane_involution hz.1.ne'⟩
    simpa only [norm_cayley_inverse hz.1] using hz.2

lemma affineInversePlane_hasFDerivAt {z : ℂ} (hz : z.im ≠ 0) :
    HasFDerivAt affineInversePlane
      ((z.im : ℂ)⁻¹ • -(Complex.ofRealCLM.comp Complex.reCLM) -
        ((-(z.re : ℂ) + I) / (z.im : ℂ)^2) •
          (Complex.ofRealCLM.comp Complex.imCLM)) z := by
  have h1 := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt (x := z)).neg.add_const I
  have h2 := (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt (x := z)
  have hinv := ((hasDerivAt_inv (Complex.ofReal_ne_zero.mpr hz)).hasFDerivAt.restrictScalars ℝ).comp z h2
  have hh := h1.mul hinv
  convert hh using 1
  all_goals first | rfl | (ext w; simp [smul_eq_mul, div_eq_mul_inv]; ring)

lemma det_affineInversePlane {z : ℂ} (hz : z.im ≠ 0) :
    (fderiv ℝ affineInversePlane z).det = (z.im ^ 3)⁻¹ := by
  change LinearMap.det (fderiv ℝ affineInversePlane z : ℂ →ₗ[ℝ] ℂ) = _
  rw [(affineInversePlane_hasFDerivAt hz).fderiv, real_det_eq]
  simp only [ContinuousLinearMap.coe_coe, sub_apply,
    smul_apply, neg_apply,
    ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply, Complex.reCLM_apply,
    Complex.imCLM_apply, one_re, one_im, I_re, I_im, Complex.ofReal_one,
    Complex.ofReal_zero, neg_zero, smul_eq_mul, mul_zero, sub_zero, mul_one]
  simp [pow_two, Complex.mul_re, Complex.mul_im, Complex.inv_re, Complex.inv_im,
    Complex.div_re, Complex.div_im, Complex.normSq_apply]
  field_simp [hz]

lemma lintegral_affineInverse_outside (g : ℂ → ℝ≥0∞) :
    (∫⁻ z in outsideCenter, g z) =
      ∫⁻ z in outsideCenter, ENNReal.ofReal ((z.im ^ 3)⁻¹) * g (affineInversePlane z) := by
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    measurableSet_outsideCenter
    (fun z (hz : z ∈ outsideCenter) =>
      (affineInversePlane_hasFDerivAt hz.1.ne').differentiableAt.hasFDerivAt.hasFDerivWithinAt)
    (affineInversePlane_injOn.mono (fun _ hz => hz.1)) g
  rw [affineInversePlane_outside_image] at h
  rw [h]
  apply setLIntegral_congr_fun measurableSet_outsideCenter
  intro z hz
  dsimp only
  rw [det_affineInversePlane hz.1.ne',
    abs_of_pos (inv_pos.mpr (pow_pos hz.1 3))]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma holomorphic_lintegral_image {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (g : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, g w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖ ^ 2) * g (F z) := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hreal hi g
  simpa only [det_complexDerivative, abs_sq] using h

lemma integrable_inverse_cube_outside {r : ℝ} (hr : 0 < r) :
    IntegrableOn (fun w : ℂ => ‖w‖⁻¹ ^ 3) {w : ℂ | r ≤ ‖w‖} := by
  have h1 : IntegrableOn (fun y : ℝ => y ^ (-2 : ℝ)) (Ici r) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr
      (integrableOn_Ioi_rpow_of_lt (by norm_num) hr)
  have h2 : Integrable ((Ici r).indicator (fun y : ℝ => y ^ (-2 : ℝ))) :=
    h1.integrable_indicator measurableSet_Ici
  have h3 : IntegrableOn (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) •
      (Ici r).indicator (fun t : ℝ => t⁻¹ ^ 3) y) (Ioi 0) := by
    apply h2.integrableOn.congr_fun _ measurableSet_Ioi
    intro y hy
    by_cases hyr : r ≤ y
    · simp only [indicator_of_mem (show y ∈ Ici r from hyr), Complex.finrank_real_complex, Nat.reduceSub,
        pow_one, smul_eq_mul]
      have he : y ^ (-2 : ℝ) = (y ^ 2)⁻¹ := by
        rw [Real.rpow_neg (le_of_lt hy)]
        congr 1
        exact Real.rpow_two y
      rw [he]
      field_simp
    · simp [hyr, Complex.finrank_real_complex]
  have h4 : Integrable (fun w : ℂ => (Ici r).indicator (fun t : ℝ => t⁻¹ ^ 3) ‖w‖) :=
    (integrable_fun_norm_addHaar volume).mpr h3
  have hset : MeasurableSet {w : ℂ | r ≤ ‖w‖} := measurableSet_le measurable_const (by fun_prop)
  apply (integrable_indicator_iff hset).mp
  convert h4 using 1
  all_goals rfl

lemma inverse_cube_tail_finite {r : ℝ} (hr : 0 < r) :
    (∫⁻ w : ℂ in {w : ℂ | r ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3)) < ∞ := by
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun _ => by positivity))).mp
    (integrable_inverse_cube_outside hr).hasFiniteIntegral

lemma halfPlane_area_tail_uniform (f : DiskFamily) :
    (∫⁻ z in outsideCenter, ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖ ^ 2) *
      ENNReal.ofReal (‖halfPlaneFunction f z‖⁻¹ ^ 3)) ≤
    ∫⁻ w : ℂ in {w : ℂ | 1 / 4 ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3) := by
  rw [← holomorphic_lintegral_image measurableSet_outsideCenter
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt
      (isOpen_halfPlane.mem_nhds hz.1))
    ((halfPlaneFunction_injOn f).mono (fun _ hz => hz.1))
    (fun w => ENNReal.ofReal (‖w‖⁻¹ ^ 3))]
  apply lintegral_mono_set
  rintro _ ⟨z, hz, rfl⟩
  exact halfPlaneFunction_outside_norm_lower f hz.1 hz.2

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma measurable_halfPlaneProjection : Measurable halfPlaneProjection :=
  UpperHalfPlane.measurableEmbedding_coe.measurable_invFun

lemma halfPlaneProjection_of_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlaneProjection z = ⟨z, hz⟩ := halfPlaneProjection_coe ⟨z, hz⟩

lemma halfPlaneFunction_inverse_rebase (f : DiskFamily) (z : UpperHalfPlane) :
    halfPlaneFunction (rebase f z) (affineInverse z) =
      -halfPlaneFunction f z / ((z.im : ℂ) * deriv (halfPlaneFunction f) z) := by
  rw [halfPlaneFunction_rebase f z (affineInverse z).im_pos, affineAt_inverse,
    halfPlaneFunction_I, zero_sub]

lemma measurable_inverseCubeValue : Measurable (fun p : DiskFamily × UpperHalfPlane =>
    inverseCubeValue p.1 p.2) := by
  exact ENNReal.measurable_ofReal.comp (continuous_halfPlaneFunction.measurable.norm.inv.pow_const 3)

lemma measurable_conformalAreaCube : Measurable (fun p : DiskFamily × UpperHalfPlane =>
    conformalAreaCube p.1 p.2) := by
  exact (ENNReal.measurable_ofReal.comp (continuous_halfPlaneFunction_deriv.measurable.norm.pow_const 2)).mul
    measurable_inverseCubeValue

lemma weighted_inverse_cube_rebase (f : DiskFamily) (z : UpperHalfPlane) :
    (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * inverseCubeValue (rebase f z) (affineInverse z) =
      ENNReal.ofReal (z.im ^ 3) * conformalAreaCube f z := by
  have hd : ‖deriv (halfPlaneFunction f) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  rw [inverseCubeValue, halfPlaneFunction_inverse_rebase]
  simp only [norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos z.im_pos]
  rw [show (‖halfPlaneQ f z‖₊ : ℝ≥0∞) = ENNReal.ofReal (‖deriv (halfPlaneFunction f) z‖⁻¹) by
    rw [← ENNReal.ofReal_coe_nnreal]
    simp only [coe_nnnorm, halfPlaneQ, norm_inv]]
  unfold conformalAreaCube inverseCubeValue
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (norm_nonneg _)),
    ← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul (pow_nonneg z.im_pos.le 3)]
  congr 1
  rw [inv_div, div_pow]
  field_simp

lemma area_cube_expectation (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily))
    (z : UpperHalfPlane) :
    (∫⁻ f, conformalAreaCube f z ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal ((z.im ^ 3)⁻¹) *
        (ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, inverseCubeValue f (affineInverse z) ∂(μ : Measure DiskFamily)) := by
  have he := hlaw z (fun f => inverseCubeValue f (affineInverse z))
    (measurable_inverseCubeValue.comp (f := fun f : DiskFamily => (f, affineInverse z)) measurable_prodMk_right)
  simp only [weighted_inverse_cube_rebase] at he
  have hm : Measurable (fun f : DiskFamily => conformalAreaCube f z) :=
    measurable_conformalAreaCube.comp (f := fun f : DiskFamily => (f, z)) measurable_prodMk_right
  rw [lintegral_const_mul (ENNReal.ofReal (z.im ^ 3)) hm] at he
  rw [← he, ENNReal.ofReal_inv_of_pos (pow_pos z.im_pos 3)]
  exact (ENNReal.inv_mul_cancel_left (by positivity) ENNReal.ofReal_ne_top).symm

lemma measurable_inverseCube_plane : Measurable (fun p : DiskFamily × ℂ =>
    inverseCubeValue p.1 (halfPlaneProjection p.2)) :=
  measurable_inverseCubeValue.comp (f := fun p : DiskFamily × ℂ => (p.1, halfPlaneProjection p.2))
    ((measurable_fst : Measurable (fun p : DiskFamily × ℂ => p.1)).prodMk
      (measurable_halfPlaneProjection.comp measurable_snd))

lemma measurable_conformalArea_plane : Measurable (fun p : DiskFamily × ℂ =>
    conformalAreaCube p.1 (halfPlaneProjection p.2)) :=
  measurable_conformalAreaCube.comp (f := fun p : DiskFamily × ℂ => (p.1, halfPlaneProjection p.2))
    ((measurable_fst : Measurable (fun p : DiskFamily × ℂ => p.1)).prodMk
      (measurable_halfPlaneProjection.comp measurable_snd))

lemma measurable_areaTail_density (β : ℝ) : Measurable (fun p : DiskFamily × ℂ =>
    ENNReal.ofReal (p.2.im ^ β) * inverseCubeValue p.1 (halfPlaneProjection p.2)) :=
  (ENNReal.measurable_ofReal.comp
    ((Complex.measurable_im.comp (measurable_snd : Measurable (fun p : DiskFamily × ℂ => p.2))).pow_const β)).mul
    measurable_inverseCube_plane

lemma measurable_weightedAreaTail (β : ℝ) : Measurable (weightedAreaTail β) :=
  (measurable_areaTail_density β).lintegral_prod_right' (ν := volume.restrict outsideCenter)

lemma expected_area_tail (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    (∫⁻ f, weightedAreaTail β f ∂(μ : Measure DiskFamily)) =
      ∫⁻ f, (∫⁻ z in outsideCenter, conformalAreaCube f (halfPlaneProjection z)) ∂(μ : Measure DiskFamily) := by
  have hm := measurable_areaTail_density β
  have ha := measurable_conformalArea_plane
  change (∫⁻ f, (∫⁻ z in outsideCenter, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z)) ∂(μ : Measure DiskFamily)) = _
  conv_lhs => rw [lintegral_lintegral_swap hm.aemeasurable]
  conv_rhs => rw [lintegral_lintegral_swap ha.aemeasurable]
  have hfun (z : ℂ) :
      (∫⁻ f, ENNReal.ofReal (z.im ^ β) * inverseCubeValue f (halfPlaneProjection z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im ^ β) * ∫⁻ f, inverseCubeValue f (halfPlaneProjection z) ∂(μ : Measure DiskFamily) :=
    lintegral_const_mul _ (measurable_inverseCubeValue.comp (f := fun f : DiskFamily => (f, halfPlaneProjection z)) measurable_prodMk_right)
  simp only [hfun]
  rw [lintegral_affineInverse_outside]
  apply setLIntegral_congr_fun measurableSet_outsideCenter
  intro z hz
  have hpos := affineInversePlane_mapsTo hz.1
  dsimp only
  rw [halfPlaneProjection_of_pos hz.1,
    halfPlaneProjection_of_pos hpos, affineInversePlane_im]
  change ENNReal.ofReal ((z.im ^ 3)⁻¹) *
    (ENNReal.ofReal ((1 / z.im) ^ β) * ∫⁻ f, inverseCubeValue f (affineInverse ⟨z, hz.1⟩) ∂(μ : Measure DiskFamily)) = _
  rw [one_div, Real.inv_rpow hz.1.le, ← Real.rpow_neg hz.1.le]
  exact (area_cube_expectation μ β hlaw ⟨z, hz.1⟩).symm

 theorem weightedAreaTail_ae_finite (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), weightedAreaTail β f < ∞ := by
  have hb (f : DiskFamily) : (∫⁻ z in outsideCenter, conformalAreaCube f (halfPlaneProjection z)) ≤
      ∫⁻ w : ℂ in {w : ℂ | 1 / 4 ≤ ‖w‖}, ENNReal.ofReal (‖w‖⁻¹ ^ 3) := by
    convert halfPlane_area_tail_uniform f using 1
    apply setLIntegral_congr_fun measurableSet_outsideCenter
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz.1]
    rfl
  apply ae_lt_top (measurable_weightedAreaTail β)
  apply ne_of_lt
  rw [expected_area_tail μ β hlaw]
  refine lt_of_le_of_lt (lintegral_mono (μ := (μ : Measure DiskFamily)) hb) ?_
  simpa only [lintegral_const, measure_univ, mul_one] using
    inverse_cube_tail_finite (show (0 : ℝ) < 1 / 4 by norm_num)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.InfinityEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma im_lower_of_mem_ball {z w : ℂ} {r : ℝ} (hw : w ∈ ball z r) :
    z.im - r < w.im := by
  have hn : ‖w - z‖ < r := by simpa only [mem_ball, dist_eq_norm] using hw
  have h := (abs_le.mp (Complex.abs_im_le_norm (w - z))).1
  simp only [sub_im] at h
  linarith

lemma ball_halfplane_subset (z : UpperHalfPlane) :
    ball (z : ℂ) (z.im / 2) ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have hh := im_lower_of_mem_ball hw
  change z.im - z.im / 2 < w.im at hh
  change 0 < w.im
  linarith [z.im_pos]

lemma norm_large_cayley {w : ℂ} (hw : 0 < w.im) (hn : 3 ≤ ‖w‖) :
    1 / 2 ≤ ‖cayleyToDisk w‖ := by
  rw [cayleyToDisk, norm_div, le_div_iff₀ (norm_pos_iff.mpr (add_I_ne_zero hw))]
  have ha : ‖w + I‖ ≤ ‖w‖ + 1 := by simpa using norm_add_le w I
  have hb : ‖w‖ - 1 ≤ ‖w - I‖ := by simpa using norm_sub_norm_le w I
  linarith

lemma far_ball_outside (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ball (z : ℂ) (z.im / 2) ⊆ outsideCenter := by
  intro w hw
  have hp := ball_halfplane_subset z hw
  refine ⟨hp, norm_large_cayley hp ?_⟩
  have hn : ‖w - (z : ℂ)‖ < z.im / 2 := by simpa only [mem_ball, dist_eq_norm] using hw
  have htri : ‖(z : ℂ)‖ ≤ ‖w‖ + ‖w - (z : ℂ)‖ := by
    simpa only [norm_sub_rev] using norm_le_norm_add_norm_sub w (z : ℂ)
  have hi : z.im ≤ ‖(z : ℂ)‖ := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  linarith

lemma omitted_local_quarter_bound {F : ℂ → ℂ} {z : ℂ} {r : ℝ}
    (hr : 0 < r) (hd : DifferentiableOn ℂ F (ball z r)) (hi : InjOn F (ball z r))
    (hne : deriv F z ≠ 0) (homit : 0 ∉ F '' ball z r) :
    r * ‖deriv F z‖ / 4 ≤ ‖F z‖ := by
  by_contra hh
  apply homit
  apply local_koebe_quarter hr hd hi hne
  simpa only [mem_ball, dist_zero_left] using lt_of_not_ge hh

lemma far_derivative_bound (f : DiskFamily) (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    z.im * ‖deriv (halfPlaneFunction f) z‖ ≤ 8 * ‖halfPlaneFunction f z‖ := by
  have hs := ball_halfplane_subset z
  have h := omitted_local_quarter_bound (F := halfPlaneFunction f) (z := z)
    (half_pos z.im_pos) ((halfPlaneFunction_differentiableOn f).mono hs)
    ((halfPlaneFunction_injOn f).mono hs) (halfPlaneFunction_deriv_ne_zero f z.im_pos) (by
      rintro ⟨w, hw, he⟩
      have hl := halfPlaneFunction_outside_norm_lower f (far_ball_outside z hz hw).1
        (far_ball_outside z hz hw).2
      rw [he, norm_zero] at hl
      norm_num at hl)
  linarith

lemma halfPlaneFunction_small_ball_bound (f : DiskFamily) {u : ℂ}
    (hu : u ∈ ball I (1 / 4)) : ‖halfPlaneFunction f u‖ ≤ 12 := by
  have hn : ‖u - I‖ < 1 / 4 := by simpa only [mem_ball, dist_eq_norm] using hu
  have him : 0 < u.im := by
    have hh := im_lower_of_mem_ball hu
    simp only [I_im] at hh
    linarith
  have hden : 7 / 4 ≤ ‖u + I‖ := by
    have hh := norm_add_le (u + I) (I - u)
    rw [show u + I + (I - u) = (2 : ℂ) * I by ring, norm_sub_rev] at hh
    norm_num at hh
    linarith
  have hm : ‖cayleyToDisk u‖ ≤ 1 / 2 := by
    rw [cayleyToDisk, norm_div, div_le_iff₀ (by linarith : 0 < ‖u + I‖)]
    linarith
  have h := disk_lipschitz_bound f.property.1 f.property.2.1 f.property.2.2.2
    (r := 1 / 2) (z := 0) (w := cayleyToDisk u) (by norm_num) (by norm_num) hm
  rw [f.property.2.2.1, sub_zero, sub_zero] at h
  norm_num at h
  have hb : ‖diskExtension f.val (cayleyToDisk u)‖ ≤ 6 := by linarith
  simp only [halfPlaneFunction, norm_mul, norm_ofNat, norm_I, mul_one]
  linarith

lemma nearbyFunction_bound (f : DiskFamily) (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖)
    {w : ℂ} (hw : w ∈ ball (z : ℂ) (z.im / 4)) :
    ‖halfPlaneFunction f w‖ ≤ 97 * ‖halfPlaneFunction f z‖ := by
  let u : ℂ := (w - (z.re : ℂ)) / (z.im : ℂ)
  have hye : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have heu : u - I = (w - (z : ℂ)) / (z.im : ℂ) := by
    dsimp [u]
    field_simp
    rw [← Complex.re_add_im (z : ℂ)]
    change w - (z.re : ℂ) - (z.im : ℂ) * I = w - ((z.re : ℂ) + (z.im : ℂ) * I)
    ring
  have hu : u ∈ ball I (1 / 4) := by
    simp only [mem_ball, dist_eq_norm, heu, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos z.im_pos]
    rw [div_lt_iff₀ z.im_pos]
    have hn : ‖w - (z : ℂ)‖ < z.im / 4 := by simpa only [mem_ball, dist_eq_norm] using hw
    linarith
  have huim : 0 < u.im := by
    have hh := im_lower_of_mem_ball hu
    simp only [I_im] at hh
    linarith
  have hew : affineAt z u = w := by dsimp [affineAt, u]; field_simp; ring
  have he := halfPlaneFunction_rebase f z huim
  rw [hew] at he
  have hb := halfPlaneFunction_small_ball_bound (rebase f z) hu
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos z.im_pos] at hb
  have hdn : 0 < ‖deriv (halfPlaneFunction f) z‖ :=
    norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hmul := (div_le_iff₀ (mul_pos z.im_pos hdn)).mp hb
  have hder := far_derivative_bound f z hz
  have htri := norm_le_norm_add_norm_sub (halfPlaneFunction f z) (halfPlaneFunction f w)
  rw [norm_sub_rev] at htri
  linarith

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma inverse_cube_lower {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    b⁻¹ ^ 3 ≤ a⁻¹ ^ 3 := by
  exact pow_le_pow_left₀ (inv_nonneg.mpr (ha.le.trans hab)) (inv_anti₀ ha hab) 3

lemma nearbyAreaDensity_lower (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖)
    {w : ℂ} (hw : w ∈ ball (z : ℂ) (z.im / 4)) :
    ENNReal.ofReal ((z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) ≤
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  have hwhalf : w ∈ ball (z : ℂ) (z.im / 2) :=
    ball_subset_ball (by linarith [z.im_pos]) hw
  have hwo := far_ball_outside z hz hwhalf
  rw [halfPlaneProjection_of_pos hwo.1, inverseCubeValue,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg hwo.1.le β)]
  apply ENNReal.ofReal_le_ofReal
  have hy : z.im / 2 ≤ w.im := by
    have hh := im_lower_of_mem_ball hw
    rw [UpperHalfPlane.coe_im] at hh
    linarith [z.im_pos]
  have hfpos : 0 < ‖halfPlaneFunction f w‖ := lt_of_lt_of_le (by norm_num)
    (halfPlaneFunction_outside_norm_lower f hwo.1 hwo.2)
  exact mul_le_mul (Real.rpow_le_rpow (by positivity) hy hβ)
    (inverse_cube_lower hfpos (nearbyFunction_bound f z hz hw)) (by positivity)
    (Real.rpow_nonneg hwo.1.le β)

lemma ball_lower_bound_area_tail (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ENNReal.ofReal ((z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) *
      (ENNReal.ofReal (z.im / 4) ^ 2 * NNReal.pi) ≤
      ∫⁻ w in ball (z : ℂ) (z.im / 4),
        ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  rw [← Complex.volume_ball, ← setLIntegral_const]
  exact setLIntegral_mono' measurableSet_ball (fun w hw => nearbyAreaDensity_lower f β hβ z hz hw)

lemma infinity_local_constant_identity (β y a : ℝ) (hy : 0 < y) (ha : 0 < a) :
    y ^ (β + 2) * a⁻¹ ^ 3 =
      (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) *
        (((y / 2) ^ β * (97 * a)⁻¹ ^ 3) * ((y / 4) ^ (2 : ℕ) * Real.pi)) := by
  rw [Real.rpow_add hy, Real.rpow_two, Real.div_rpow hy.le (by norm_num)]
  have hp : (2 : ℝ) ^ β ≠ 0 := (Real.rpow_pos_of_pos (by norm_num) β).ne'
  field_simp
  ring

lemma ball_source_norm_lower (z : UpperHalfPlane) {w : ℂ}
    (hw : w ∈ ball (z : ℂ) (z.im / 4)) : ‖(z : ℂ)‖ / 2 ≤ ‖w‖ := by
  have hn : ‖w - (z : ℂ)‖ < z.im / 4 := by simpa only [mem_ball, dist_eq_norm] using hw
  have htri := norm_le_norm_add_norm_sub w (z : ℂ)
  have hi : z.im ≤ ‖(z : ℂ)‖ := (le_abs_self z.im).trans (Complex.abs_im_le_norm z)
  linarith [z.im_pos]

lemma infinity_local_tail_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (z : UpperHalfPlane) (hz : 6 ≤ ‖(z : ℂ)‖) :
    ENNReal.ofReal (z.im ^ (β + 2) * ‖halfPlaneFunction f z‖⁻¹ ^ 3) ≤
      ENNReal.ofReal (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) *
        ∫⁻ w in outsideCenter ∩ {w : ℂ | ‖(z : ℂ)‖ / 2 ≤ ‖w‖},
          ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w) := by
  have hzout := far_ball_outside z hz (mem_ball_self (half_pos z.im_pos))
  have hzpos : 0 < ‖halfPlaneFunction f z‖ := lt_of_lt_of_le (by norm_num)
    (halfPlaneFunction_outside_norm_lower f hzout.1 hzout.2)
  have hv : ENNReal.ofReal ((z.im / 4) ^ (2 : ℕ) * Real.pi) =
      ENNReal.ofReal (z.im / 4) ^ 2 * NNReal.pi := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [← NNReal.coe_real_pi, ENNReal.ofReal_coe_nnreal]
  rw [infinity_local_constant_identity β z.im _ z.im_pos hzpos,
    ENNReal.ofReal_mul (p := 16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi) (by positivity),
    ENNReal.ofReal_mul (p := (z.im / 2) ^ β * (97 * ‖halfPlaneFunction f z‖)⁻¹ ^ 3) (by positivity), hv]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact (ball_lower_bound_area_tail f β hβ z hz).trans
    (lintegral_mono_set (fun w hw => ⟨far_ball_outside z hz
      (ball_subset_ball (by linarith [z.im_pos]) hw), ball_source_norm_lower z hw⟩))

lemma tendsto_weighted_area_tail_zero (f : DiskFamily) (β : ℝ)
    (hfin : weightedAreaTail β f < ∞) :
    Tendsto (fun R : ℝ => ∫⁻ w in outsideCenter ∩ {w : ℂ | R ≤ ‖w‖},
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)) atTop (𝓝 0) := by
  let d : ℂ → ℝ≥0∞ := fun w => ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)
  have hd : Measurable d := (measurable_areaTail_density β).comp
    (f := fun w : ℂ => (f, w)) (measurable_const.prodMk measurable_id)
  have hm (R : ℝ) : MeasurableSet {w : ℂ | R ≤ ‖w‖} :=
    measurableSet_le measurable_const (by fun_prop)
  have hh := tendsto_lintegral_filter_of_dominated_convergence (μ := volume.restrict outsideCenter)
    (l := atTop) (F := fun R : ℝ => {w : ℂ | R ≤ ‖w‖}.indicator d) (f := fun _ => 0)
    d (Eventually.of_forall (fun R => hd.indicator (hm R)))
    (Eventually.of_forall (fun _ => Eventually.of_forall (fun w => indicator_le_self' (fun _ _ => bot_le) w)))
    (ne_of_lt hfin) (Eventually.of_forall (fun w => ?_))
  · simpa only [lintegral_indicator (hm _), lintegral_zero,
      Measure.restrict_restrict (hm _), inter_comm] using hh
  · apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop ‖w‖] with R hR
    exact (indicator_of_notMem (by simpa using not_le.mpr hR) d).symm

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

theorem escape_at_infinity (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) (hZ : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => (Z a).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z a)‖) l (𝓝 0) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (16 * 97 ^ (3 : ℕ) * (2 : ℝ) ^ β / Real.pi)
  have htail := (tendsto_weighted_area_tail_zero f β hfin).comp
    (hZ.atTop_div_const (by norm_num : (0 : ℝ) < 2))
  have hu : Tendsto (fun a => C * ∫⁻ w in outsideCenter ∩ {w : ℂ | ‖(Z a : ℂ)‖ / 2 ≤ ‖w‖},
      ENNReal.ofReal (w.im ^ β) * inverseCubeValue f (halfPlaneProjection w)) l (𝓝 0) := by
    simpa only [mul_zero, Function.comp_def] using ENNReal.Tendsto.const_mul (a := C) htail
      (Or.inr ENNReal.ofReal_ne_top)
  have he : ∀ᶠ a in l, 6 ≤ ‖(Z a : ℂ)‖ := hZ.eventually (eventually_ge_atTop 6)
  have hsmall : Tendsto (fun a => ENNReal.ofReal
      ((Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3)) l (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
      (Eventually.of_forall (fun _ => bot_le))
      (he.mono (fun a ha => infinity_local_tail_bound f β hβ (Z a) ha))
  have hr : Tendsto (fun a => (Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3) l (𝓝 0) := by
    have hh := (ENNReal.tendsto_toReal (a := 0) ENNReal.zero_ne_top).comp hsmall
    simpa only [Function.comp_def, ENNReal.toReal_zero,
      ENNReal.toReal_ofReal (by positivity : 0 ≤ (Z _).im ^ (β + 2) * ‖halfPlaneFunction f (Z _)‖⁻¹ ^ 3)] using hh
  have hc (a : ι) : (Z a).im ^ (β + 2) * ‖halfPlaneFunction f (Z a)‖⁻¹ ^ 3 =
      ((Z a).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z a)‖) ^ (3 : ℕ) := by
    rw [div_pow, ← Real.rpow_mul_natCast (Z a).im_pos.le]
    rw [show (β + 2) / 3 * (3 : ℕ) = β + 2 by ring]
    simp only [div_eq_mul_inv, inv_pow]
  have hp := hr.rpow_const_nhds_zero (by norm_num : (0 : ℝ) < (3 : ℝ)⁻¹)
  convert hp using 1
  funext a
  rw [hc]
  exact (Real.pow_rpow_inv_natCast (n := 3) (by positivity) (by norm_num)).symm

theorem bounded_strip_preimage (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ε R : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, ∀ z : UpperHalfPlane, ε ≤ z.im → ‖halfPlaneFunction f z‖ ≤ R → ‖(z : ℂ)‖ ≤ M := by
  by_contra h
  push Not at h
  choose Z hZ using fun n : ℕ => h (max 6 n)
  have hnorm : Tendsto (fun n => ‖(Z n : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (le_max_right (6 : ℝ) n).trans (hZ n).2.2.le)
      tendsto_natCast_atTop_atTop
  have he := escape_at_infinity f β hβ hfin Z hnorm
  have kpos : 0 < (β + 2) / 3 := by linarith
  have Rpos : 0 < R := by
    have hzfar : 6 ≤ ‖(Z 0 : ℂ)‖ := (le_max_left (6 : ℝ) ((0 : ℕ) : ℝ)).trans (hZ 0).2.2.le
    have hzo := far_ball_outside (Z 0) hzfar (mem_ball_self (half_pos (Z 0).im_pos))
    exact lt_of_lt_of_le ((by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (halfPlaneFunction_outside_norm_lower f hzo.1 hzo.2)) (hZ 0).2.1
  have hpos : 0 < ε ^ ((β + 2) / 3) / R := div_pos (Real.rpow_pos_of_pos hε _) Rpos
  have hlo : ∀ n, ε ^ ((β + 2) / 3) / R ≤
      (Z n).im ^ ((β + 2) / 3) / ‖halfPlaneFunction f (Z n)‖ := by
    intro n
    have hzfar : 6 ≤ ‖(Z n : ℂ)‖ := (le_max_left 6 (n : ℝ)).trans (hZ n).2.2.le
    have hzo := far_ball_outside (Z n) hzfar (mem_ball_self (half_pos (Z n).im_pos))
    have hv : 0 < ‖halfPlaneFunction f (Z n)‖ := (by norm_num : (0 : ℝ) < 1 / 4).trans_le
      (halfPlaneFunction_outside_norm_lower f hzo.1 hzo.2)
    exact div_le_div₀ (by positivity) (Real.rpow_le_rpow hε.le (hZ n).1 kpos.le) hv (hZ n).2.1
  exact (not_le_of_gt hpos) (ge_of_tendsto' he hlo)

lemma bounded_preimage_height (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) (R : ℝ) :
    ∃ Y : ℝ, 0 < Y ∧ ∀ z : UpperHalfPlane, ‖halfPlaneFunction f z‖ ≤ R → z.im ≤ Y := by
  obtain ⟨M, hM⟩ := bounded_strip_preimage f β hβ hfin (ε := 1) (R := R) zero_lt_one
  refine ⟨max 1 M, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun z hz => ?_⟩
  by_cases h : 1 ≤ z.im
  · exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans
      ((hM z h hz).trans (le_max_right _ _))
  · exact (le_of_not_ge h).trans (le_max_left _ _)

lemma compact_strip_preimage_plane (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ∞) {ε : ℝ} (hε : 0 < ε) {K : Set ℂ} (hK : IsCompact K) :
    IsCompact {z : ℂ | ε ≤ z.im ∧ halfPlaneFunction f z ∈ K} := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨M, hM⟩ := bounded_strip_preimage f β hβ hfin (R := R) hε
  have hs : IsClosed {z : ℂ | ε ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hc : ContinuousOn (halfPlaneFunction f) {z : ℂ | ε ≤ z.im} :=
    (halfPlaneFunction_differentiableOn f).continuousOn.mono (fun z hz => hε.trans_le hz)
  apply (isCompact_closedBall (0 : ℂ) M).of_isClosed_subset
    (hc.preimage_isClosed_of_isClosed hs hK.isClosed)
  intro z hz
  have hp : 0 < z.im := hε.trans_le hz.1
  have hn : ‖halfPlaneFunction f z‖ ≤ R := by
    simpa only [mem_closedBall, dist_zero_right] using hR hz.2
  simpa only [mem_closedBall, dist_zero_right] using hM ⟨z, hp⟩ hz.1 hn

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GreenIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma compact_integral_deriv_zero {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) : ∫ x, deriv g x = 0 := by
  exact integral_eq_zero_of_hasDerivAt_of_integrable
    (fun x => (hg.differentiable one_ne_zero x).hasDerivAt)
    ((hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv)
    (hg.continuous.integrable_of_hasCompactSupport hc)

lemma compact_second_deriv_green {g : ℝ → ℝ} (hg : ContDiff ℝ 2 g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ t in Ioi s, (t - s) * deriv (deriv g) t) = g s := by
  let H : ℝ → ℝ := fun t => (t - s) * deriv g t - g t
  have h1 : ContDiff ℝ 1 (deriv g) := hg.deriv'
  have hH : ContDiff ℝ 1 H :=
    ((contDiff_id.sub contDiff_const).mul h1).sub (hg.of_le (by norm_num))
  have hcH : HasCompactSupport H := (hc.deriv.mul_left).sub hc
  have hder (t : ℝ) : deriv H t = (t - s) * deriv (deriv g) t := by
    have h := (((hasDerivAt_id t).sub_const s).mul
      ((h1.differentiable one_ne_zero t).hasDerivAt)).sub
      ((hg.differentiable (by norm_num) t).hasDerivAt)
    have he : ((fun x => id x - s) * deriv g - g) = H := rfl
    rw [he] at h
    rw [h.deriv]
    simp
  simpa only [H, hder, sub_self, zero_mul, zero_sub, neg_neg] using
    hcH.integral_Ioi_deriv_eq hH s

lemma contDiff_realPlanePartial {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (v : ℝ × ℝ) :
    ContDiff ℝ ∞ (realPlanePartial v g) := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma compact_realPlanePartial {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (v : ℝ × ℝ) :
    HasCompactSupport (realPlanePartial v g) := hc.fderiv_apply ℝ v

lemma deriv_vertical_line {g : ℝ × ℝ → ℝ} {x y : ℝ} (hg : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t => g (x,t)) y = realPlanePartial (0,1) g (x,y) := by
  exact (hg.hasFDerivAt.comp_hasDerivAt y
    ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))).deriv

lemma deriv_horizontal_line {g : ℝ × ℝ → ℝ} {x y : ℝ} (hg : DifferentiableAt ℝ g (x,y)) :
    deriv (fun t => g (t,y)) x = realPlanePartial (1,0) g (x,y) := by
  exact (hg.hasFDerivAt.comp_hasDerivAt x
    ((hasDerivAt_id x).prodMk (hasDerivAt_const x y))).deriv

lemma compact_vertical_line {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (x : ℝ) :
    HasCompactSupport (fun y => g (x,y)) := by
  apply hc.comp_isClosedEmbedding
  exact ⟨isEmbedding_prodMkRight x, (isClosedMap_prodMk_left x).isClosed_range⟩

lemma compact_horizontal_line {g : ℝ × ℝ → ℝ} (hc : HasCompactSupport g) (y : ℝ) :
    HasCompactSupport (fun x => g (x,y)) := by
  apply hc.comp_isClosedEmbedding
  exact ⟨isEmbedding_prodMkLeft y, (isClosedMap_prodMk_right y).isClosed_range⟩

lemma compact_plane_second_horizontal_zero {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
  (hc : HasCompactSupport g) (y : ℝ) :
  (∫ x, realPlanePartial (1,0) (realPlanePartial (1,0) g) (x,y)) = 0 := by
  have hdx := contDiff_realPlanePartial hg (1,0)
  have hL : ContDiff ℝ 2 (fun x => g (x,y)) :=
    contDiff_infty.mp (hg.comp (contDiff_id.prodMk contDiff_const)) 2
  have hL' : deriv (fun x => g (x,y)) = fun x => realPlanePartial (1,0) g (x,y) := by
    funext x
    exact deriv_horizontal_line (hg.differentiable (by simp) (x,y))
  have hL'' : deriv (deriv (fun x => g (x,y))) = fun x => realPlanePartial (1,0) (realPlanePartial (1,0) g) (x,y) := by
    rw [hL']
    funext x
    exact deriv_horizontal_line (hdx.differentiable (by simp) (x,y))
  simpa only [hL''] using compact_integral_deriv_zero hL.deriv'
    (compact_horizontal_line hc y).deriv

lemma compact_plane_second_vertical_green {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
  (hc : HasCompactSupport g) (x s : ℝ) :
  (∫ y in Ioi s, (y - s) * realPlanePartial (0,1) (realPlanePartial (0,1) g) (x,y)) = g (x,s) := by
  have hdy := contDiff_realPlanePartial hg (0,1)
  have hL : ContDiff ℝ 2 (fun y => g (x,y)) :=
    contDiff_infty.mp (hg.comp (contDiff_const.prodMk contDiff_id)) 2
  have hL' : deriv (fun y => g (x,y)) = fun y => realPlanePartial (0,1) g (x,y) := by
    funext y
    exact deriv_vertical_line (hg.differentiable (by simp) (x,y))
  have hL'' : deriv (deriv (fun y => g (x,y))) = fun y => realPlanePartial (0,1) (realPlanePartial (0,1) g) (x,y) := by
    rw [hL']
    funext y
    exact deriv_vertical_line (hdy.differentiable (by simp) (x,y))
  simpa only [hL''] using compact_second_deriv_green hL (compact_vertical_line hc x) s

lemma compact_plane_weight_integrable {D : ℝ × ℝ → ℝ} (hD : Continuous D)
    (hc : HasCompactSupport D) (s : ℝ) :
    Integrable (fun p : ℝ × ℝ => (p.2 - s) * D p)
      (volume.prod (volume.restrict (Ioi s))) :=
  ((continuous_snd.sub continuous_const).mul hD).integrable_of_hasCompactSupport hc.mul_left

lemma compact_plane_horizontal_integral_zero {X : ℝ × ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hcX : HasCompactSupport X)
    (hxx : ∀ y : ℝ, (∫ x, X (x,y)) = 0) :
    (∫ p : ℝ × ℝ, (p.2-s) * X p ∂(volume.prod (volume.restrict (Ioi s)))) = 0 := by
  have hi := compact_plane_weight_integrable hX hcX s
  rw [integral_prod _ hi]
  have he : (∫ x : ℝ, ∫ y in Ioi s, (y-s)*X (x,y)) =
      ∫ y in Ioi s, ∫ x : ℝ, (y-s)*X (x,y) :=
    integral_integral_swap_of_hasCompactSupport
      ((continuous_snd.sub continuous_const).mul hX) hcX.mul_left
  rw [he]
  simp only [integral_const_mul, hxx, mul_zero, integral_zero]

lemma compact_plane_green_assemble {X Y : ℝ × ℝ → ℝ} {H : ℝ → ℝ} {s : ℝ}
    (hX : Continuous X) (hcX : HasCompactSupport X)
    (hY : Continuous Y) (hcY : HasCompactSupport Y)
    (hxx : ∀ y : ℝ, (∫ x, X (x,y)) = 0)
    (hyy : ∀ x : ℝ, (∫ y in Ioi s, (y - s) * Y (x,y)) = H x) :
    (∫ x, H x) = ∫ p : ℝ × ℝ, (p.2 - s) * (X p + Y p)
      ∂(volume.prod (volume.restrict (Ioi s))) := by
  have hiX := compact_plane_weight_integrable hX hcX s
  have hiY := compact_plane_weight_integrable hY hcY s
  have he : (fun p : ℝ × ℝ => (p.2-s)*(X p+Y p)) =
      (fun p => (p.2-s)*X p + (p.2-s)*Y p) := by
    funext p
    exact mul_add _ _ _
  rw [he, integral_add hiX hiY, compact_plane_horizontal_integral_zero hX hcX hxx,
    zero_add, integral_prod _ hiY]
  simp only [hyy]

lemma compact_plane_horizontal_green {g : ℝ × ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ x, g (x,s)) =
    ∫ p : ℝ × ℝ, (p.2 - s) *
      (realPlanePartial (1,0) (realPlanePartial (1,0) g) p +
       realPlanePartial (0,1) (realPlanePartial (0,1) g) p)
      ∂(volume.prod (volume.restrict (Ioi s))) := by
  apply compact_plane_green_assemble
  · exact (contDiff_realPlanePartial (contDiff_realPlanePartial hg (1,0)) (1,0)).continuous
  · exact (compact_realPlanePartial (compact_realPlanePartial hc (1,0)) (1,0))
  · exact (contDiff_realPlanePartial (contDiff_realPlanePartial hg (0,1)) (0,1)).continuous
  · exact (compact_realPlanePartial (compact_realPlanePartial hc (0,1)) (0,1))
  · exact compact_plane_second_horizontal_zero hg hc
  · exact fun x => compact_plane_second_vertical_green hg hc x s

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma planePartial_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hψ : DifferentiableAt ℝ ψ (F z)) (v : ℂ) :
    planePartial v (fun w => ψ (F w)) z = fderiv ℝ ψ (F z) (deriv F z * v) := by
  change (fderiv ℝ (ψ ∘ F) z) v = _
  rw [fderiv_comp z hψ (hF.restrictScalars (𝕜 := ℝ))]
  simp only [ContinuousLinearMap.comp_apply, hF.hasDerivAt.complexToReal_fderiv.fderiv]
  rfl

lemma second_planePartial_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hψ : ContDiffAt ℝ 2 ψ (F z)) (v : ℂ) :
    planePartial v (planePartial v (fun w => ψ (F w))) z =
      fderiv ℝ ψ (F z) (deriv (deriv F) z * v * v) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * v) (deriv F z * v) := by
  have he : planePartial v (fun w => ψ (F w)) =ᶠ[𝓝 z]
      fun w => fderiv ℝ ψ (F w) (deriv F w * v) := by
    have hp := hψ.eventually (by norm_num)
    filter_upwards [hF.eventually_analyticAt, hF.continuousAt.eventually hp] with w hw hpw
    exact planePartial_comp_holomorphic hw.differentiableAt
      (hpw.differentiableAt (by norm_num)) v
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) (F z) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hA := hDψ.hasFDerivAt.comp z hF.differentiableAt.hasDerivAt.complexToReal_fderiv
  have hB := ((hF.deriv.differentiableAt.hasDerivAt).mul_const v).complexToReal_fderiv
  change fderiv ℝ (planePartial v (fun w => ψ (F w))) z v = _
  rw [he.fderiv_eq]
  have hh := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) (hA.clm_apply hB).fderiv
  simpa only [Function.comp_def, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, smul_apply, one_apply_eq_self,
    smul_eq_mul] using hh

lemma real_bilinear_complex_trace (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (a : ℂ) :
    B a a + B (a * I) (a * I) = ‖a‖ ^ 2 * (B 1 1 + B I I) := by
  have ha : a = a.re • (1 : ℂ) + a.im • I := by apply Complex.ext <;> simp
  have hai : a * I = (-a.im) • (1 : ℂ) + a.re • I := by apply Complex.ext <;> simp
  calc
    B a a + B (a * I) (a * I) =
        B (a.re • 1 + a.im • I) (a.re • 1 + a.im • I) +
        B ((-a.im) • 1 + a.re • I) ((-a.im) • 1 + a.re • I) := by rw [← ha, ← hai]
    _ = _ := by
      simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring

lemma planeLaplacian_comp_holomorphic {F : ℂ → ℂ} {ψ : ℂ → ℝ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (hψ : ContDiffAt ℝ 2 ψ (F z)) :
    planeLaplacian (fun w => ψ (F w)) z = ‖deriv F z‖ ^ 2 * planeLaplacian ψ (F z) := by
  have hDψ : DifferentiableAt ℝ (fderiv ℝ ψ) (F z) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hp (v : ℂ) : planePartial v (planePartial v ψ) (F z) =
      fderiv ℝ (fderiv ℝ ψ) (F z) v v := by
    unfold planePartial
    rw [fderiv_clm_apply hDψ (differentiableAt_const v)]
    simp
  rw [planeLaplacian, second_planePartial_comp_holomorphic hF hψ,
    second_planePartial_comp_holomorphic hF hψ]
  simp only [mul_one, mul_assoc, I_mul_I, mul_neg_one, map_neg]
  rw [show fderiv ℝ ψ (F z) (deriv (deriv F) z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z) (deriv F z) +
      (-fderiv ℝ ψ (F z) (deriv (deriv F) z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * I) (deriv F z * I)) =
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z) (deriv F z) +
      fderiv ℝ (fderiv ℝ ψ) (F z) (deriv F z * I) (deriv F z * I) by ring]
  rw [real_bilinear_complex_trace]
  simp only [planeLaplacian, hp]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma planePartial_contDiff {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (v : ℂ) :
    ContDiff ℝ ∞ (planePartial v g) := by
  exact (hg.fderiv_right (by simp)).clm_apply contDiff_const

lemma partial_realProd_comp {g : ℂ → ℝ} (hg : Differentiable ℝ g) (v : ℝ × ℝ) :
    realPlanePartial v (fun p => g (Complex.equivRealProdCLM.symm p)) =
      fun p => planePartial (Complex.equivRealProdCLM.symm v) g (Complex.equivRealProdCLM.symm p) := by
  funext p
  unfold realPlanePartial planePartial
  change fderiv ℝ (g ∘ Complex.equivRealProdCLM.symm) p v = _
  rw [fderiv_comp p (hg _) Complex.equivRealProdCLM.symm.differentiableAt,
    Complex.equivRealProdCLM.symm.fderiv]
  rfl

lemma laplacian_realProd_comp {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g) (p : ℝ × ℝ) :
    realPlanePartial (1,0) (realPlanePartial (1,0)
      (fun p => g (Complex.equivRealProdCLM.symm p))) p +
    realPlanePartial (0,1) (realPlanePartial (0,1)
      (fun p => g (Complex.equivRealProdCLM.symm p))) p =
      planeLaplacian g (Complex.equivRealProdCLM.symm p) := by
  rw [partial_realProd_comp (hg.differentiable (by simp)),
    partial_realProd_comp ((planePartial_contDiff hg _).differentiable (by simp)),
    partial_realProd_comp (hg.differentiable (by simp)),
    partial_realProd_comp ((planePartial_contDiff hg _).differentiable (by simp))]
  rfl

lemma integral_realProd_above (H : ℂ → ℝ) (s : ℝ) :
    (∫ p : ℝ × ℝ, H (Complex.equivRealProdCLM.symm p)
      ∂(volume.prod (volume.restrict (Ioi s)))) =
    ∫ z in {z : ℂ | s < z.im}, H z := by
  have hp := Complex.volume_preserving_equiv_real_prod.restrict_preimage
    (MeasurableSet.univ.prod measurableSet_Ioi : MeasurableSet ((univ : Set ℝ) ×ˢ Ioi s))
  have he := hp.integral_comp Complex.measurableEquivRealProd.measurableEmbedding
    (fun p => H (Complex.equivRealProdCLM.symm p))
  have hm : (volume : Measure (ℝ × ℝ)).restrict ((univ : Set ℝ) ×ˢ Ioi s) =
      volume.prod (volume.restrict (Ioi s)) := by
    rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
  rw [hm] at he
  have hs : (Complex.measurableEquivRealProd ⁻¹' ((univ : Set ℝ) ×ˢ Ioi s)) =
      {z : ℂ | s < z.im} := by ext z; simp
  have hx (z : ℂ) : Complex.equivRealProdCLM.symm (Complex.measurableEquivRealProd z) = z :=
    Complex.equivRealProdCLM.symm_apply_apply z
  simpa only [hs, hx] using he.symm

lemma compact_complex_horizontal_green {g : ℂ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) (s : ℝ) :
    (∫ x : ℝ, g ((x : ℂ) + (s : ℂ) * I)) =
    ∫ z in {z : ℂ | s < z.im}, (z.im-s) * planeLaplacian g z := by
  have hgc : ContDiff ℝ ∞ (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hg.comp Complex.equivRealProdCLM.symm.contDiff
  have hcc : HasCompactSupport (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hc.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding
  have he := compact_plane_horizontal_green hgc hcc s
  simp only [laplacian_realProd_comp hg] at he
  have hz (x : ℝ) : Complex.equivRealProdCLM.symm (x,s) = (x : ℂ) + (s : ℂ) * I := by
    apply Complex.ext <;> simp
  simp only [hz] at he
  rw [he]
  exact integral_realProd_above (fun z => (z.im-s) * planeLaplacian g z) s

lemma planeLaplacian_congr_nhds {g h : ℂ → ℝ} {z : ℂ} (he : g =ᶠ[𝓝 z] h) :
    planeLaplacian g z = planeLaplacian h z := by
  have hp (v : ℂ) : planePartial v g =ᶠ[𝓝 z] planePartial v h := by
    filter_upwards [he.fderiv (𝕜 := ℝ)] with w hw
    exact congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hw
  change fderiv ℝ (planePartial 1 g) z 1 + fderiv ℝ (planePartial I g) z I =
    fderiv ℝ (planePartial 1 h) z 1 + fderiv ℝ (planePartial I h) z I
  rw [(hp 1).fderiv_eq, (hp I).fderiv_eq]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HorizontalLength
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma horizontalCutoff_zero (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : z.im ≤ s / 2) : horizontalCutoff f ψ s z = 0 := by
  have h : 4 * z.im / s - 2 ≤ 0 := by
    have hd : 4 * z.im / s ≤ 2 := (div_le_iff₀ hs).mpr (by linarith)
    linarith
  simp only [horizontalCutoff, Real.smoothTransition.zero_of_nonpos h, zero_mul]

lemma horizontalCutoff_one (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : 3 * s / 4 ≤ z.im) : horizontalCutoff f ψ s z = ψ (halfPlaneFunction f z) := by
  have h : 1 ≤ 4 * z.im / s - 2 := by
    have hd : 3 ≤ 4 * z.im / s := (le_div_iff₀ hs).mpr (by linarith)
    linarith
  simp only [horizontalCutoff, Real.smoothTransition.one_of_one_le h, one_mul]

lemma horizontalCutoff_eq_nhds (f : DiskFamily) (ψ : ℂ → ℝ) {s : ℝ} (hs : 0 < s)
    {z : ℂ} (hz : s ≤ z.im) :
    horizontalCutoff f ψ s =ᶠ[𝓝 z] fun w => ψ (halfPlaneFunction f w) := by
  have hlt : 3 * s / 4 < z.im := by linarith
  filter_upwards [Complex.continuous_im.continuousAt.eventually (lt_mem_nhds hlt)] with w hw
  exact horizontalCutoff_one f ψ hs hw.le

lemma horizontalCutoff_contDiff (f : DiskFamily) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    {s : ℝ} (hs : 0 < s) : ContDiff ℝ ∞ (horizontalCutoff f ψ s) := by
  apply contDiff_iff_contDiffAt.mpr
  intro z
  by_cases hz : 0 < z.im
  · have hF : AnalyticAt ℂ (halfPlaneFunction f) z :=
      (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
    have hf : ContDiffAt ℝ ∞ (halfPlaneFunction f) z := hF.contDiffAt.restrict_scalars ℝ
    exact (Real.smoothTransition.contDiffAt.comp z
      (((contDiffAt_const.mul Complex.imCLM.contDiff.contDiffAt).div_const s).sub contDiffAt_const)).mul
      (hψ.contDiffAt.comp z hf)
  · have hlt : z.im < s / 2 := (le_of_not_gt hz).trans_lt (half_pos hs)
    have he : horizontalCutoff f ψ s =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [Complex.continuous_im.continuousAt.eventually (gt_mem_nhds hlt)] with w hw
      exact horizontalCutoff_zero f ψ hs hw.le
    exact contDiffAt_const.congr_of_eventuallyEq he

lemma horizontalCutoff_compact (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ)
    {s : ℝ} (hs : 0 < s) : HasCompactSupport (horizontalCutoff f ψ s) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (compact_strip_preimage_plane f β hβ hfin (half_pos hs) hc)
  intro z hz
  have hn : horizontalCutoff f ψ s z ≠ 0 := hz
  refine ⟨?_, ?_⟩
  · by_contra h
    exact hn (horizontalCutoff_zero f ψ hs (le_of_not_ge h))
  · apply subset_tsupport ψ
    exact (mul_ne_zero_iff.mp hn).2

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
namespace StrictInverseFirstPower
noncomputable section

lemma planeLaplacian_continuous {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ) :
    Continuous (planeLaplacian ψ) :=
  ((planePartial_contDiff (planePartial_contDiff hψ 1) 1).continuous).add
    ((planePartial_contDiff (planePartial_contDiff hψ I) I).continuous)

lemma planeLaplacian_compact {ψ : ℂ → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (planeLaplacian ψ) :=
  ((hc.fderiv_apply ℝ 1).fderiv_apply ℝ 1).add
    ((hc.fderiv_apply ℝ I).fderiv_apply ℝ I)

lemma holomorphic_integrable_image {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hd : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (g : ℂ → ℝ) :
    IntegrableOn g (F '' s) ↔ IntegrableOn (fun z => ‖deriv F z‖ ^ 2 * g (F z)) s := by
  have hreal (z : ℂ) (hz : z ∈ s) :=
    (hd z hz).hasDerivAt.complexToReal_fderiv.hasFDerivWithinAt (s := s)
  simpa only [det_complexDerivative, abs_sq, smul_eq_mul] using
    integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hreal hi g

lemma horizontal_smooth_green (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {s : ℝ} (hs : 0 < s) :
    (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) =
      ∫ z in {z : ℂ | s < z.im},
        (z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z)) := by
  have hg := horizontalCutoff_contDiff f hψ hs
  have hgc := horizontalCutoff_compact f β hβ hfin hc hs
  have he := compact_complex_horizontal_green hg hgc s
  have hline (x : ℝ) : horizontalCutoff f ψ s ((x : ℂ) + (s : ℂ) * I) =
      ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) :=
    horizontalCutoff_one f ψ hs (by simp; linarith)
  simp only [hline] at he
  rw [he]
  apply setIntegral_congr_fun (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  intro z hz
  dsimp only
  rw [planeLaplacian_congr_nhds (horizontalCutoff_eq_nhds f ψ hs hz.le),
    planeLaplacian_comp_holomorphic
      ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds (hs.trans hz)))
      ((contDiff_infty.mp hψ 2).contDiffAt)]

lemma pullback_laplacian_integrable (f : DiskFamily) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    IntegrableOn (fun z => ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
      |planeLaplacian ψ (halfPlaneFunction f z)|) {z : ℂ | 0 < z.im} := by
  apply (holomorphic_integrable_image isOpen_halfPlane.measurableSet
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hz))
    (halfPlaneFunction_injOn f) (fun w => |planeLaplacian ψ w|)).mp
  exact ((planeLaplacian_continuous hψ).abs.integrable_of_hasCompactSupport
    (planeLaplacian_compact hc).abs).integrableOn

lemma pullback_laplacian_integral_le (f : DiskFamily) {ψ : ℂ → ℝ}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    (∫ z in {z : ℂ | 0 < z.im}, ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
      |planeLaplacian ψ (halfPlaneFunction f z)|) ≤ ∫ w : ℂ, |planeLaplacian ψ w| := by
  rw [← holomorphic_integral_image isOpen_halfPlane.measurableSet
    (fun z hz => (halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hz))
    (halfPlaneFunction_injOn f) (fun w => |planeLaplacian ψ w|)]
  exact setIntegral_le_integral
    ((planeLaplacian_continuous hψ).abs.integrable_of_hasCompactSupport
      (planeLaplacian_compact hc).abs)
    (ae_of_all _ (fun w => abs_nonneg _))

lemma horizontal_smooth_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s →
      (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) ≤ C := by
  obtain ⟨R, hR⟩ := (planeLaplacian_compact hc).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨Y, hY, hheight⟩ := bounded_preimage_height f β hβ hfin R
  refine ⟨Y * ∫ w : ℂ, |planeLaplacian ψ w|, fun s hs => ?_⟩
  let A : ℂ → ℝ := fun z => ‖deriv (halfPlaneFunction f) z‖ ^ 2 *
    |planeLaplacian ψ (halfPlaneFunction f z)|
  have hiA : IntegrableOn A {z : ℂ | 0 < z.im} := pullback_laplacian_integrable f hψ hc
  have hiAs : IntegrableOn A {z : ℂ | s < z.im} := hiA.mono_set (fun z hz => hs.trans hz)
  have hA (z : ℂ) : 0 ≤ A z := mul_nonneg (sq_nonneg _) (abs_nonneg _)
  have hpoint (z : ℂ) (hz : s < z.im) :
      |(z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| ≤ Y * A z := by
    rw [abs_mul, abs_mul, abs_of_pos (sub_pos.mpr hz), abs_sq]
    change (z.im-s) * A z ≤ Y * A z
    by_cases hd : planeLaplacian ψ (halfPlaneFunction f z) = 0
    · simp [A, hd]
    · apply mul_le_mul_of_nonneg_right _ (hA z)
      have hmem := hR (subset_tsupport (planeLaplacian ψ) hd)
      have hn : ‖halfPlaneFunction f z‖ ≤ R := by simpa using hmem
      have hy := hheight ⟨z, hs.trans hz⟩ hn
      change z.im ≤ Y at hy
      linarith
  rw [horizontal_smooth_green f β hβ hfin hψ hc hs]
  calc
    _ ≤ |∫ z in {z : ℂ | s < z.im}, (z.im-s) *
        (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| := le_abs_self _
    _ ≤ ∫ z in {z : ℂ | s < z.im}, |(z.im-s) *
        (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))| :=
      by
        simpa only [Real.norm_eq_abs] using (norm_integral_le_integral_norm
          (μ := volume.restrict {z : ℂ | s < z.im})
          (fun z : ℂ => (z.im-s) * (‖deriv (halfPlaneFunction f) z‖ ^ 2 * planeLaplacian ψ (halfPlaneFunction f z))))
    _ ≤ ∫ z in {z : ℂ | s < z.im}, Y * A z := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) (hiAs.const_mul Y)
      exact (ae_restrict_mem (isOpen_lt continuous_const Complex.continuous_im).measurableSet).mono hpoint
    _ = Y * ∫ z in {z : ℂ | s < z.im}, A z := integral_const_mul _ _
    _ ≤ Y * ∫ z in {z : ℂ | 0 < z.im}, A z := by
      apply mul_le_mul_of_nonneg_left _ hY.le
      exact setIntegral_mono_set hiA (ae_of_all _ hA) (ae_of_all _ (fun z hz => hs.trans hz))
    _ ≤ _ := mul_le_mul_of_nonneg_left (pullback_laplacian_integral_le f hψ hc) hY.le

lemma horizontal_smooth_integrable (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ψ : ℂ → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) := by
  let g := horizontalCutoff f ψ s
  have hg : ContDiff ℝ ∞ g := horizontalCutoff_contDiff f hψ hs
  have hgc : HasCompactSupport g := horizontalCutoff_compact f β hβ hfin hc hs
  have hcP : HasCompactSupport (fun p => g (Complex.equivRealProdCLM.symm p)) :=
    hgc.comp_isClosedEmbedding Complex.equivRealProdCLM.symm.toHomeomorph.isClosedEmbedding
  have hL : Continuous (fun x : ℝ => g (Complex.equivRealProdCLM.symm (x,s))) :=
    (hg.continuous.comp Complex.equivRealProdCLM.symm.continuous).comp
      (continuous_id.prodMk continuous_const)
  have hi : Integrable (fun x : ℝ => g (Complex.equivRealProdCLM.symm (x,s))) :=
    hL.integrable_of_hasCompactSupport (compact_horizontal_line hcP s)
  have he (x : ℝ) : g (Complex.equivRealProdCLM.symm (x,s)) =
      ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) := by
    have hz : Complex.equivRealProdCLM.symm (x,s) = (x : ℂ) + (s : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hz]
    exact horizontalCutoff_one f ψ hs (by simp; linarith)
  simpa only [he] using hi

lemma continuous_halfPlaneFunction_line (f : DiskFamily) {s : ℝ} (hs : 0 < s) :
    Continuous (fun x : ℝ => halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hz : 0 < ((x : ℂ) + (s : ℂ) * I).im := by simpa using hs
  have hC : ContinuousAt (fun x : ℝ => (x : ℂ) + (s : ℂ) * I) x :=
    Complex.continuous_ofReal.continuousAt.add continuousAt_const
  exact ContinuousAt.comp (f := fun x : ℝ => (x : ℂ) + (s : ℂ) * I)
    ((halfPlaneFunction_differentiableOn f).differentiableAt
      (isOpen_halfPlane.mem_nhds hz)).continuousAt hC

lemma compact_smooth_majorant {K : Set ℂ} (hK : IsCompact K) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ z, 0 ≤ ψ z) ∧ ∀ z ∈ K, 1 ≤ ψ z := by
  obtain ⟨R, hRpos, hR⟩ := hK.isBounded.subset_ball_lt 0 (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) :=
    { rIn := R
      rOut := R + 1
      rIn_pos := hRpos
      rIn_lt_rOut := by linarith }
  refine ⟨b, b.contDiff, b.hasCompactSupport, fun _ => b.nonneg, ?_⟩
  intro z hz
  have he : b z = 1 := b.one_of_mem_closedBall (ball_subset_closedBall (hR hz))
  exact he.ge

theorem horizontal_length_bound (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ, ∀ s : ℝ, 0 < s →
      volume {x : ℝ | halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I) ∈ K} ≤ ENNReal.ofReal C := by
  obtain ⟨ψ, hψ, hc, hnonneg, hmajor⟩ := compact_smooth_majorant hK
  obtain ⟨C, hC⟩ := horizontal_smooth_bound f β hβ hfin hψ hc
  refine ⟨C, fun s hs => ?_⟩
  let A : Set ℝ := {x | halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I) ∈ K}
  have hA : MeasurableSet A := hK.isClosed.measurableSet.preimage
    (continuous_halfPlaneFunction_line f hs).measurable
  rw [← lintegral_indicator_one hA]
  calc
    _ ≤ ∫⁻ x : ℝ, ENNReal.ofReal (ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) := by
      apply lintegral_mono
      intro x
      by_cases hx : x ∈ A
      · simp only [indicator_of_mem hx, Pi.one_apply]
        exact_mod_cast (ENNReal.ofReal_le_ofReal (hmajor _ hx))
      · simp only [indicator_of_notMem hx]
        exact bot_le
    _ = ENNReal.ofReal (∫ x : ℝ, ψ (halfPlaneFunction f ((x : ℂ) + (s : ℂ) * I))) :=
      (ofReal_integral_eq_lintegral_ofReal
        (horizontal_smooth_integrable f β hβ hfin hψ hc hs)
        (ae_of_all _ (fun x => hnonneg _))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hC s hs)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoundaryCells
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma scaled_integer_cells_disjoint {h : ℝ} (hh : 0 < h) :
    Pairwise (fun i j : ℤ => Disjoint (Ico ((i : ℝ)*h) (((i : ℝ)+1)*h))
      (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h))) := by
  have hl (i j : ℤ) (hij : i < j) :
      Disjoint (Ico ((i : ℝ)*h) (((i : ℝ)+1)*h))
        (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) := by
    have he : (i : ℝ)+1 ≤ (j : ℝ) := by exact_mod_cast (Int.add_one_le_iff.mpr hij)
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hle := mul_le_mul_of_nonneg_right he hh.le
    linarith [hx.2, hy.1]
  intro i j hij
  rcases lt_or_gt_of_ne hij with hij' | hij'
  · exact hl i j hij'
  · exact (hl j i hij').symm

lemma volume_scaled_integer_cell {h : ℝ} (j : ℤ) :
    volume (Ico ((j : ℝ)*h) (((j : ℝ)+1)*h)) = ENNReal.ofReal h := by
  rw [Real.volume_Ico]
  congr 1
  ring

lemma cell_disks_measure_bound {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (J : Set ℤ) (c : ℤ → ℂ) {C : ℝ≥0∞}
    (hC : volume (⋃ j : J, Ico (((j : ℤ) : ℝ)*h) ((((j : ℤ) : ℝ)+1)*h)) ≤ C) :
    volume (⋃ j : J, closedBall (c j) r) ≤ ENNReal.ofReal (Real.pi*r^2/h) * C := by
  have hd : Pairwise (fun i j : J => Disjoint
      (Ico (((i : ℤ) : ℝ)*h) ((((i : ℤ) : ℝ)+1)*h))
      (Ico (((j : ℤ) : ℝ)*h) ((((j : ℤ) : ℝ)+1)*h))) :=
    fun i j hij => scaled_integer_cells_disjoint hh (Subtype.coe_ne_coe.mpr hij)
  have he : (∑' j : J, ENNReal.ofReal h) ≤ C := by
    simpa only [measure_iUnion hd (fun _ => measurableSet_Ico), volume_scaled_integer_cell] using hC
  calc
    _ ≤ ∑' j : J, volume (closedBall (c j) r) := measure_iUnion_le _
    _ = ∑' j : J, ENNReal.ofReal (Real.pi*r^2/h) * ENNReal.ofReal h := by
      apply tsum_congr
      intro j
      rw [Complex.volume_closedBall]
      rw [← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal r ^ 2 * ENNReal.ofReal Real.pi = _
      rw [← ENNReal.ofReal_pow hr, ← ENNReal.ofReal_mul (sq_nonneg r),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      field_simp
    _ = ENNReal.ofReal (Real.pi*r^2/h) * ∑' j : J, ENNReal.ofReal h :=
      ENNReal.tsum_mul_left
    _ ≤ _ := by gcongr

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma isCompact_cellRectangle : IsCompact cellRectangle := by
  rw [UpperHalfPlane.isEmbedding_coe.isCompact_iff]
  have he : ((↑) '' cellRectangle : Set ℂ) =
      {z | |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1} := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact hw
    · intro hz
      exact ⟨⟨z, by linarith [hz.2.1]⟩, hz, rfl⟩
  rw [he]
  apply (isCompact_closedBall (0 : ℂ) 2).of_isClosed_subset
    ((isClosed_le Complex.continuous_re.abs continuous_const).inter
      ((isClosed_le continuous_const Complex.continuous_im).inter
        (isClosed_le Complex.continuous_im continuous_const)))
  intro z hz
  change |z.re| ≤ 1 ∧ 1/2 ≤ z.im ∧ z.im ≤ 1 at hz
  simp only [mem_closedBall, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  rw [abs_of_nonneg (by linarith [hz.2.1] : 0 ≤ z.im)] at hn
  linarith [hz.1, hz.2.2]

lemma family_rectangle_bound : ∃ M : ℝ, 0 < M ∧
    ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle →
      ‖halfPlaneFunction f z‖ ≤ M := by
  have hc := (isCompact_univ (X := DiskFamily)).prod isCompact_cellRectangle
  obtain ⟨M, hMpos, hM⟩ := (hc.image continuous_halfPlaneFunction).isBounded.subset_ball_lt 0 (0 : ℂ)
  refine ⟨M, hMpos, fun f z hz => ?_⟩
  have hh := hM (mem_image_of_mem (fun p : DiskFamily × UpperHalfPlane => halfPlaneFunction p.1 p.2)
    (show (f,z) ∈ (univ : Set DiskFamily) ×ˢ cellRectangle from ⟨mem_univ _, hz⟩))
  exact (by simpa only [mem_ball, dist_zero_right] using hh : ‖halfPlaneFunction f z‖ < M).le

lemma full_ball_halfplane_subset (z : UpperHalfPlane) :
    ball (z : ℂ) z.im ⊆ {w : ℂ | 0 < w.im} := by
  intro w hw
  have he := im_lower_of_mem_ball hw
  change z.im - z.im < w.im at he
  change 0 < w.im
  linarith

lemma omitted_derivative_bound (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) (z : UpperHalfPlane) :
    z.im * ‖deriv (halfPlaneFunction f) z‖ ≤ 4 * ‖halfPlaneFunction f z - ξ‖ := by
  let F := halfPlaneFunction f
  have hd : DifferentiableOn ℂ (fun w => F w - ξ) (ball (z : ℂ) z.im) :=
    ((halfPlaneFunction_differentiableOn f).mono (full_ball_halfplane_subset z)).sub_const ξ
  have hi : InjOn (fun w => F w - ξ) (ball (z : ℂ) z.im) := by
    intro a ha b hb hab
    exact halfPlaneFunction_injOn f (full_ball_halfplane_subset z ha)
      (full_ball_halfplane_subset z hb) (sub_left_injective hab)
  have he : deriv (fun w => F w - ξ) z = deriv F z := deriv_sub_const ξ
  have hn : deriv (fun w => F w - ξ) z ≠ 0 := by
    rw [he]
    exact halfPlaneFunction_deriv_ne_zero f z.im_pos
  have ho : 0 ∉ (fun w => F w - ξ) '' ball (z : ℂ) z.im := by
    rintro ⟨w, hw, hh⟩
    exact hξ ⟨w, full_ball_halfplane_subset z hw, sub_eq_zero.mp hh⟩
  have hh := omitted_local_quarter_bound z.im_pos hd hi hn ho
  rw [he] at hh
  linarith

lemma cell_rebased_mem (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h) :
    ∃ v : UpperHalfPlane, v ∈ cellRectangle ∧ affineAt z v = (u : ℂ) + (h : ℂ)*I := by
  let v : ℂ := ((u-z.re : ℝ) : ℂ) / (z.im : ℂ) + (h/z.im : ℝ)*I
  have hre : v.re = (u-z.re)/z.im := by simp [v]
  have him : v.im = h/z.im := by simp [v]
  have hv : 0 < v.im := by rw [him]; exact div_pos hh z.im_pos
  refine ⟨⟨v,hv⟩, ?_, ?_⟩
  · change |v.re| ≤ 1 ∧ 1/2 ≤ v.im ∧ v.im ≤ 1
    rw [hre, him, abs_div, abs_of_pos z.im_pos]
    refine ⟨(div_le_one z.im_pos).mpr (hu.trans hlo), ?_, (div_le_one z.im_pos).mpr hlo⟩
    rw [le_div_iff₀ z.im_pos]
    linarith
  · apply Complex.ext <;> simp only [affineAt, v, add_re, add_im,
      mul_re, mul_im, div_ofReal_re, div_ofReal_im, ofReal_re, ofReal_im, I_re, I_im,
      mul_zero, mul_one, zero_mul, zero_add, add_zero, sub_zero]
    · field_simp
      ring
    · field_simp
      ring

lemma omitted_cell_comparison {M : ℝ} (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane),
    z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M) (hM0 : 0 ≤ M)
    (f : DiskFamily) {ξ : ℂ} (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im})
    (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h) :
    ‖halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-ξ‖ ≤
      (4*M+1)*‖halfPlaneFunction f z-ξ‖ := by
  obtain ⟨v, hv, he⟩ := cell_rebased_mem z hh hlo hhi hu
  have hb := hM (rebase f z) v hv
  rw [halfPlaneFunction_rebase f z v.im_pos, he, norm_div, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos z.im_pos] at hb
  have hd : 0 < ‖deriv (halfPlaneFunction f) z‖ :=
    norm_pos_iff.mpr (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hm := (div_le_iff₀ (mul_pos z.im_pos hd)).mp hb
  have hq := mul_le_mul_of_nonneg_left (omitted_derivative_bound f hξ z) hM0
  have ht := norm_add_le (halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-halfPlaneFunction f z)
    (halfPlaneFunction f z-ξ)
  rw [sub_add_sub_cancel] at ht
  nlinarith

lemma omitted_cell_power_bound {M k δ : ℝ} (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane),
    z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M) (hM0 : 0 ≤ M)
    (hk : 0 ≤ k) (hδ : 0 < δ) (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im})
    (z : UpperHalfPlane) {h u : ℝ} (hh : 0 < h)
    (hlo : h ≤ z.im) (hhi : z.im ≤ 2*h) (hu : |u-z.re| ≤ h)
    (hw : ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ) :
    ‖halfPlaneFunction f ((u : ℂ)+(h : ℂ)*I)-ξ‖ ≤
      ((4*M+1)*2^k/δ)*h^k := by
  calc
    _ ≤ (4*M+1)*‖halfPlaneFunction f z-ξ‖ := omitted_cell_comparison hM hM0 f hξ z hh hlo hhi hu
    _ ≤ (4*M+1)*(z.im^k/δ) := mul_le_mul_of_nonneg_left hw (by positivity)
    _ ≤ (4*M+1)*((2*h)^k/δ) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right (Real.rpow_le_rpow z.im_pos.le hhi hk) hδ.le) (by positivity)
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hh.le]; ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma same_cell_difference {j : ℤ} {h u v : ℝ}
    (hu : u ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h))
    (hv : v ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h)) : |u-v| ≤ h := by
  apply abs_le.mpr
  constructor <;> nlinarith [hu.1, hu.2, hv.1, hv.2]

lemma midpoint_mem_cell {h : ℝ} (hh : 0 < h) (j : ℤ) :
    ((j:ℝ)+1/2)*h ∈ Ico ((j:ℝ)*h) (((j:ℝ)+1)*h) := by
  constructor <;> nlinarith

lemma floor_cell_mem {h : ℝ} (hh : 0 < h) (x : ℝ) :
    x ∈ Ico (((⌊x/h⌋ : ℤ):ℝ)*h) ((((⌊x/h⌋ : ℤ):ℝ)+1)*h) := by
  constructor
  · exact (le_div_iff₀ hh).mp (Int.floor_le (x/h))
  · exact (div_lt_iff₀ hh).mp (Int.lt_floor_add_one (x/h))

lemma boundaryBadScale_subset_cover {M k R δ h : ℝ}
    (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M)
    (hM0 : 0 ≤ M) (hk : 0 ≤ k) (hδ : 0 < δ) (hh : 0 < h) (f : DiskFamily) :
    boundaryBadScale f k R δ h ⊆ ⋃ j : boundaryMarkedCells f k R δ h,
      closedBall (cellMidpointImage f h j) (((4*M+1)*2^k/δ)*h^k) := by
  rintro ξ ⟨z, hz⟩
  let j : ℤ := ⌊z.re/h⌋
  have hj : j ∈ boundaryMarkedCells f k R δ h := ⟨ξ,z,hz,floor_cell_mem hh z.re⟩
  apply mem_iUnion.mpr
  refine ⟨⟨j,hj⟩, ?_⟩
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  exact omitted_cell_power_bound hM hM0 hk hδ f hz.1 z hh hz.2.2.1 hz.2.2.2.1
    (same_cell_difference (midpoint_mem_cell hh j) (floor_cell_mem hh z.re)) hz.2.2.2.2

lemma marked_segments_image_bounded {M k R δ h : ℝ}
    (hM : ∀ (f : DiskFamily) (z : UpperHalfPlane), z ∈ cellRectangle → ‖halfPlaneFunction f z‖ ≤ M)
    (hM0 : 0 ≤ M) (hk : 0 ≤ k) (hδ : 0 < δ) (hh : 0 < h) (hh1 : h ≤ 1) (f : DiskFamily) :
    (⋃ j : boundaryMarkedCells f k R δ h,
      Ico (((j:ℤ):ℝ)*h) ((((j:ℤ):ℝ)+1)*h)) ⊆
      {u : ℝ | halfPlaneFunction f ((u:ℂ)+(h:ℂ)*I) ∈ closedBall 0 (R+(4*M+1)*2^k/δ)} := by
  rintro u hu
  obtain ⟨j,hj⟩ := mem_iUnion.mp hu
  obtain ⟨ξ,z,hz,hzcell⟩ := j.property
  have hb := omitted_cell_power_bound hM hM0 hk hδ f hz.1 z hh hz.2.2.1 hz.2.2.2.1
    (same_cell_difference hj hzcell) hz.2.2.2.2
  have hp : h^k ≤ 1 := Real.rpow_le_one hh.le hh1 hk
  have hc : 0 ≤ (4*M+1)*2^k/δ := by positivity
  have ht := norm_add_le (halfPlaneFunction f ((u:ℂ)+(h:ℂ)*I)-ξ) ξ
  rw [sub_add_cancel] at ht
  simp only [mem_ofPred_eq, mem_closedBall, dist_zero_right]
  nlinarith [hz.2.1, mul_le_of_le_one_right hc hp]

lemma cell_area_power_identity {h : ℝ} (hh : 0 < h) (A k : ℝ) :
    Real.pi*(A*h^k)^2/h = (Real.pi*A^2)*h^(2*k-1) := by
  rw [Real.rpow_sub_one hh.ne', show 2*k = k*2 by ring,
    Real.rpow_mul hh.le, Real.rpow_two]
  ring

theorem boundaryBadScale_measure_bound (f : DiskFamily) (β k R δ : ℝ)
    (hβ : 0 ≤ β) (hk : 0 ≤ k) (hδ : 0 < δ) (hfin : weightedAreaTail β f < ⊤) :
    ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      volume (boundaryBadScale f k R δ h) ≤ D * ENNReal.ofReal (h^(2*k-1)) := by
  obtain ⟨M,hM0,hM⟩ := family_rectangle_bound
  let A : ℝ := (4*M+1)*2^k/δ
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C,hC⟩ := horizontal_length_bound f β hβ hfin (isCompact_closedBall (0:ℂ) (R+A))
  refine ⟨ENNReal.ofReal (Real.pi*A^2)*ENNReal.ofReal C, ENNReal.mul_lt_top
    ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top, fun h hh hh1 => ?_⟩
  have hseg : volume (⋃ j : boundaryMarkedCells f k R δ h,
      Ico (((j:ℤ):ℝ)*h) ((((j:ℤ):ℝ)+1)*h)) ≤ ENNReal.ofReal C :=
    (measure_mono (marked_segments_image_bounded hM hM0.le hk hδ hh hh1 f)).trans (hC h hh)
  calc
    _ ≤ volume (⋃ j : boundaryMarkedCells f k R δ h,
        closedBall (cellMidpointImage f h j) (A*h^k)) :=
      measure_mono (boundaryBadScale_subset_cover hM hM0.le hk hδ hh f)
    _ ≤ ENNReal.ofReal (Real.pi*(A*h^k)^2/h)*ENNReal.ofReal C :=
      cell_disks_measure_bound hh (by positivity) _ _ hseg
    _ = _ := by rw [cell_area_power_identity hh, ENNReal.ofReal_mul (by positivity)]; ring

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoundaryEscape
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma dyadicHeight_rpow (γ : ℝ) (n : ℕ) :
    (dyadicHeight n)^γ = ((1/2 : ℝ)^γ)^n := by
  dsimp only [dyadicHeight]
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm (n:ℝ), Real.rpow_mul_natCast (by norm_num)]

lemma ae_eventually_dyadic_cover {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {s : ℕ → Set α} {D : ℝ≥0∞} (hD : D < ⊤) {γ : ℝ} (hγ : 0 < γ)
    (hbound : ∀ n, μ (s n) ≤ D * ENNReal.ofReal ((dyadicHeight n)^γ)) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n := by
  apply ae_eventually_notMem
  apply ne_of_lt
  calc
    (∑' n, μ (s n)) ≤ ∑' n, D * ENNReal.ofReal ((dyadicHeight n)^γ) := ENNReal.tsum_le_tsum hbound
    _ = D * (1 - ENNReal.ofReal ((1/2:ℝ)^γ))⁻¹ := by
      simp only [dyadicHeight_rpow, ENNReal.ofReal_pow (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) γ),
        ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ < ⊤ := ENNReal.mul_lt_top hD (ENNReal.inv_lt_top.mpr (by
      exact tsub_pos_iff_lt.mpr (ENNReal.ofReal_lt_one.mpr
        (Real.rpow_lt_one (by norm_num) (by norm_num) hγ))))

lemma dyadic_band_after {y : ℝ} (hy : 0 < y) (N : ℕ) (hNy : y < dyadicHeight N) :
    ∃ n : ℕ, N ≤ n ∧ dyadicHeight n ≤ y ∧ y ≤ 2*dyadicHeight n := by
  have hy1 : y ≤ 1 := hNy.le.trans (dyadicHeight_le_one N)
  obtain ⟨m,hmlo,hmhi⟩ := exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  refine ⟨m+1, ?_, hmlo.le, ?_⟩
  · by_contra hh
    have hmN : m+1 ≤ N := le_of_lt (lt_of_not_ge hh)
    have hp : dyadicHeight N ≤ dyadicHeight (m+1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hmN
    exact (hNy.trans_le hp).not_ge hmlo.le
  · dsimp [dyadicHeight]
    rw [pow_succ]
    linarith

lemma boundaryBadScale_ae_eventually (f : DiskFamily) (β k R δ : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hδ : 0 < δ) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ∀ᶠ n in atTop, ξ ∉ boundaryBadScale f k R δ (dyadicHeight n) := by
  obtain ⟨D,hD,hbound⟩ := boundaryBadScale_measure_bound f β k R δ hβ (by linarith) hδ hfin
  exact ae_eventually_dyadic_cover volume hD (by linarith : 0 < 2*k-1)
    (fun n => hbound _ (dyadicHeight_pos n) (dyadicHeight_le_one n))

theorem ae_omitted_boundary_escape (f : DiskFamily) (β k : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ξ ∉ halfPlaneFunction f '' {z : ℂ | 0 < z.im} →
      boundaryEscape k (halfPlaneFunction f) ξ := by
  have hall : ∀ᵐ ξ : ℂ, ∀ m n : ℕ, ∀ᶠ j in atTop,
      ξ ∉ boundaryBadScale f k (m:ℝ) (1/(n+1)) (dyadicHeight j) := by
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro n
    exact boundaryBadScale_ae_eventually f β k m (1/(n+1)) hβ hk (by positivity) hfin
  filter_upwards [hall] with ξ hξ
  intro homit δ hδ
  obtain ⟨m,hm⟩ := exists_nat_gt ‖ξ‖
  obtain ⟨n,hn⟩ := exists_nat_one_div_lt hδ
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hξ m n)
  refine ⟨dyadicHeight N, dyadicHeight_pos N, fun z hz => ?_⟩
  obtain ⟨j,hj,hjlo,hjhi⟩ := dyadic_band_after z.im_pos N hz
  by_contra hbad
  apply hN j hj
  refine ⟨z, homit, hm.le, hjlo, hjhi, ?_⟩
  calc
    ‖halfPlaneFunction f z-ξ‖ ≤ z.im^k/δ := le_of_not_gt hbad
    _ ≤ z.im^k/(1/(n+1:ℝ)) := by gcongr

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma image_target_separated_near_boundary (f : DiskFamily) {ξ : ℂ}
    (hξ : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) :
    ∃ ε a : ℝ, 0 < ε ∧ 0 < a ∧ ∀ z : UpperHalfPlane,
      z.im < ε → a ≤ ‖halfPlaneFunction f z - ξ‖ := by
  obtain ⟨w,hw,rfl⟩ := hξ
  change 0 < w.im at hw
  let r : ℝ := w.im/2
  have hr : 0 < r := half_pos hw
  have hsub : ball w r ⊆ {z : ℂ | 0 < z.im} := by
    intro z hz
    have he := im_lower_of_mem_ball hz
    change 0 < z.im
    dsimp [r] at he
    linarith
  have hd := (halfPlaneFunction_differentiableOn f).mono hsub
  have hi := (halfPlaneFunction_injOn f).mono hsub
  have hn := halfPlaneFunction_deriv_ne_zero f hw
  have hq := local_koebe_quarter hr hd hi hn
  refine ⟨r, r * ‖deriv (halfPlaneFunction f) w‖ / 4, hr,
    div_pos (mul_pos hr (norm_pos_iff.mpr hn)) (by norm_num), ?_⟩
  intro z hz
  by_contra he
  have hzball : halfPlaneFunction f z ∈
      ball (halfPlaneFunction f w) (r * ‖deriv (halfPlaneFunction f) w‖ /4) := by
    simpa only [mem_ball, dist_eq_norm] using lt_of_not_ge he
  obtain ⟨u,hu,heu⟩ := hq hzball
  have huz : u = z := halfPlaneFunction_injOn f (hsub hu) z.im_pos heu
  rw [huz] at hu
  have he := im_lower_of_mem_ball hu
  change w.im-r < z.im at he
  dsimp [r] at he hz
  linarith

lemma image_target_boundary_escape (f : DiskFamily) {k : ℝ} (hk : 0 < k) {ξ : ℂ}
    (hξ : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}) :
    boundaryEscape k (halfPlaneFunction f) ξ := by
  obtain ⟨ε,a,hε,ha,hsep⟩ := image_target_separated_near_boundary f hξ
  intro δ hδ
  have hc : ContinuousAt (fun y : ℝ => y^k / δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he : ∀ᶠ y : ℝ in 𝓝 0, y^k/δ < a :=
    hc.preimage_mem_nhds (Iio_mem_nhds (by simpa [Real.zero_rpow hk.ne'] using ha))
  obtain ⟨η,hη,hb⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨min ε η, lt_min hε hη, fun z hz => ?_⟩
  have hzη : (z.im : ℝ) ∈ ball 0 η := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos z.im_pos]
      using (lt_of_lt_of_le hz (min_le_right _ _))
  exact (hb hzη).trans_le (hsep z (lt_of_lt_of_le hz (min_le_left _ _)))

lemma ae_boundary_escape (f : DiskFamily) (β k : ℝ)
    (hβ : 0 ≤ β) (hk : 1/2 < k) (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, boundaryEscape k (halfPlaneFunction f) ξ := by
  filter_upwards [ae_omitted_boundary_escape f β k hβ hk hfin] with ξ hξ
  by_cases hi : ξ ∈ halfPlaneFunction f '' {z : ℂ | 0 < z.im}
  · exact image_target_boundary_escape f (by linarith) hi
  · exact hξ hi

lemma norm_image_at_infinity_in_strip (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ᶠ a in l, ε ≤ (Z a).im)
    (hnorm : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => ‖halfPlaneFunction f (Z a)‖) l atTop := by
  apply Filter.tendsto_atTop.2
  intro R
  obtain ⟨M,hM⟩ := bounded_strip_preimage f β hβ hfin (ε := ε) (R := R) hε
  filter_upwards [hstrip, hnorm.eventually_gt_atTop M] with a ha ham
  by_contra h
  exact (hM (Z a) ha (le_of_not_ge h)).not_gt ham

lemma translated_escape_at_infinity_in_strip (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ) {ι : Type*} {l : Filter ι}
    (Z : ι → UpperHalfPlane) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ᶠ a in l, ε ≤ (Z a).im)
    (hnorm : Tendsto (fun a => ‖(Z a : ℂ)‖) l atTop) :
    Tendsto (fun a => (Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)-ξ‖) l (𝓝 0) := by
  have he := escape_at_infinity f β hβ hfin Z hnorm
  have hf := norm_image_at_infinity_in_strip f β hβ hfin Z hε hstrip hnorm
  have hb : ∀ᶠ a in l, (Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)-ξ‖ ≤
      2*((Z a).im ^ ((β+2)/3) / ‖halfPlaneFunction f (Z a)‖) := by
    filter_upwards [hf.eventually_gt_atTop (2*‖ξ‖+1)] with a ha
    have hn := norm_sub_norm_le (halfPlaneFunction f (Z a)) ξ
    have hF : 0 < ‖halfPlaneFunction f (Z a)‖-‖ξ‖ := by linarith [norm_nonneg ξ]
    have hd : 0 < ‖halfPlaneFunction f (Z a)-ξ‖ := hF.trans_le hn
    rw [div_le_iff₀ hd]
    have hp : 0 < ‖halfPlaneFunction f (Z a)‖ := by linarith [norm_nonneg ξ]
    have ht : 2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖ ≥ 1 := by
      change 1 ≤ 2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖
      rw [le_div_iff₀ hp]
      linarith
    have ht' := mul_le_mul_of_nonneg_left ht
      (Real.rpow_nonneg (Z a).im_pos.le ((β+2)/3))
    nlinarith [show (Z a).im ^ ((β+2)/3) * (2*‖halfPlaneFunction f (Z a)-ξ‖ / ‖halfPlaneFunction f (Z a)‖) =
      2*((Z a).im ^ ((β+2)/3)/‖halfPlaneFunction f (Z a)‖)*‖halfPlaneFunction f (Z a)-ξ‖ by ring]
  apply squeeze_zero' (Eventually.of_forall (fun a => div_nonneg (Real.rpow_nonneg (Z a).im_pos.le _) (norm_nonneg _))) hb
  simpa using he.const_mul 2

lemma bounded_strip_superlevel (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : UpperHalfPlane, ε ≤ z.im →
      ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ → ‖(z:ℂ)‖ ≤ M := by
  by_contra h
  push Not at h
  choose Z hZ using fun n : ℕ => h (n:ℝ)
  have hn : Tendsto (fun n => ‖(Z n : ℂ)‖) atTop atTop :=
    tendsto_atTop_mono (fun n => (hZ n).2.2.le) tendsto_natCast_atTop_atTop
  have he := translated_escape_at_infinity_in_strip f β hβ hfin ξ Z hε
    (Eventually.of_forall (fun n => (hZ n).1)) hn
  have hF := norm_image_at_infinity_in_strip f β hβ hfin Z hε
    (Eventually.of_forall (fun n => (hZ n).1)) hn
  have hlo : ∀ᶠ n in atTop, δ ≤ (Z n).im^((β+2)/3)/‖halfPlaneFunction f (Z n)-ξ‖ := by
    filter_upwards [hF.eventually_gt_atTop ‖ξ‖] with n hh
    have hd : 0 < ‖halfPlaneFunction f (Z n)-ξ‖ :=
      (sub_pos.mpr hh).trans_le (norm_sub_norm_le _ _)
    rw [le_div_iff₀ hd]
    have h := (le_div_iff₀ hδ).mp (hZ n).2.1
    linarith
  exact hδ.not_ge (ge_of_tendsto he hlo)

lemma compact_superlevels_of_boundary_escape (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) (ξ : ℂ)
    (hescape : boundaryEscape ((β+2)/3) (halfPlaneFunction f) ξ) {δ : ℝ} (hδ : 0 < δ) :
    IsCompact (potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ) := by
  obtain ⟨ε,hε,hbound⟩ := hescape δ hδ
  have heq : potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ =
      {z : ℂ | ε ≤ z.im ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ} := by
    ext z
    constructor
    · intro hz
      refine ⟨?_,hz.2⟩
      by_contra hh
      exact (hbound ⟨z,hz.1⟩ (lt_of_not_ge hh)).not_ge hz.2
    · intro hz
      exact ⟨hε.trans_le hz.1,hz.2⟩
  rw [heq]
  have hclosed : IsClosed {z : ℂ | ε ≤ z.im ∧ ‖halfPlaneFunction f z-ξ‖ ≤ z.im^((β+2)/3)/δ} := by
    apply (isClosed_le continuous_const Complex.continuous_im).isClosed_le
    · have hc : ContinuousOn (halfPlaneFunction f) {z : ℂ | ε ≤ z.im} :=
        (halfPlaneFunction_differentiableOn f).continuousOn.mono (fun z hz => hε.trans_le hz)
      exact (hc.sub continuousOn_const).norm
    · exact ((Real.continuous_rpow_const (by linarith : 0 ≤ (β+2)/3)).comp Complex.continuous_im).continuousOn.div_const δ
  obtain ⟨M,hM⟩ := bounded_strip_superlevel f β hβ hfin ξ hε hδ
  apply (isCompact_closedBall (0:ℂ) M).of_isClosed_subset hclosed
  intro z hz
  simpa only [mem_closedBall, dist_zero_right] using hM ⟨z,hε.trans_le hz.1⟩ hz.1 hz.2

theorem ae_compact_positive_superlevels (f : DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hfin : weightedAreaTail β f < ⊤) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      IsCompact (potentialSuperlevel ((β+2)/3) (halfPlaneFunction f) ξ δ) := by
  filter_upwards [ae_boundary_escape f β ((β+2)/3) hβ (by linarith) hfin] with ξ hξ
  exact fun δ hδ => compact_superlevels_of_boundary_escape f β hβ hfin ξ hξ hδ

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalPotential
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma complex_log_norm_fderiv {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (hne : F z ≠ 0) :
    fderiv ℝ (fun w => Real.log ‖F w‖) z =
      Complex.reCLM.comp ((ContinuousLinearMap.toSpanSingleton ℂ (deriv F z / F z)).restrictScalars ℝ) := by
  have hd := hF.hasDerivAt.complexToReal_fderiv
  have hn : ‖F z‖^2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr hne)
  have hh := ((hd.norm_sq).log hn).const_mul (1/2)
  have he : (fun w => (1/2:ℝ) * Real.log (‖F w‖^2)) = (fun w => Real.log ‖F w‖) := by
    funext w
    rw [Real.log_pow]
    ring
  rw [he] at hh
  rw [hh.fderiv]
  ext v
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.reCLM_apply, innerSL_apply_apply, one_apply_eq_self]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.div_re,
    Complex.div_im, Complex.conj_re, Complex.conj_im]
  rw [← Complex.normSq_eq_norm_sq]
  field_simp
  ring

lemma logPotential_fderiv_apply {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) (v : ℂ) :
    fderiv ℝ (logPotential k F ξ) z v =
      k / z.im * v.im - ((deriv F z / (F z-ξ))*v).re := by
  have hu : HasFDerivAt (fun w : ℂ => Real.log w.im) ((z.im)⁻¹ • Complex.imCLM) z := by
    simpa only [Complex.imCLM_apply] using (Complex.imCLM.hasFDerivAt (x := z)).log hz.ne'
  have h1 := hu.const_mul k
  have h2 : DifferentiableAt ℝ (fun w => Real.log ‖F w-ξ‖) z :=
    (((hF.restrictScalars (𝕜 := ℝ)).sub_const ξ).norm ℝ (sub_ne_zero.mpr hne)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne))
  change (fderiv ℝ ((fun w => k * Real.log w.im) - (fun w => Real.log ‖F w-ξ‖)) z) v = _
  rw [fderiv_sub h1.differentiableAt h2, h1.fderiv,
    complex_log_norm_fderiv (hF.sub_const ξ) (sub_ne_zero.mpr hne)]
  simp only [sub_apply, smul_apply, smul_eq_mul, Complex.imCLM_apply,
    ContinuousLinearMap.comp_apply, Complex.reCLM_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    deriv_sub_const]
  rw [mul_comm v (deriv F z / (F z-ξ))]
  congr 1
  ring

lemma logPotential_critical_iff {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) :
    fderiv ℝ (logPotential k F ξ) z = 0 ↔ criticalMap k F z = ξ := by
  have hkC : (k:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have hyC : (z.im:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hz.ne'
  have hFC : F z-ξ ≠ 0 := sub_ne_zero.mpr hne
  let r : ℂ := deriv F z / (F z-ξ)
  have hx := logPotential_fderiv_apply (k := k) hz hF hne 1
  have hy := logPotential_fderiv_apply (k := k) hz hF hne I
  have hrc : fderiv ℝ (logPotential k F ξ) z = 0 ↔ r = -I * (k:ℂ)/(z.im:ℂ) := by
    constructor
    · intro h
      rw [h] at hx hy
      apply Complex.ext
      · simp only [zero_apply, one_im, mul_zero, zero_sub, mul_one] at hx
        simp only [Complex.div_ofReal_re, neg_mul, neg_re, Complex.mul_re,
          I_re, ofReal_re, I_im, ofReal_im, zero_mul, mul_zero, sub_self, neg_zero, zero_div]
        dsimp [r]
        linarith
      · simp only [zero_apply, I_im, mul_one, mul_I_re, sub_neg_eq_add] at hy
        simp only [Complex.div_ofReal_im, neg_mul, neg_im, Complex.mul_im,
          I_re, ofReal_re, I_im, ofReal_im, mul_zero, one_mul, zero_add, neg_div]
        dsimp [r]
        linarith
    · intro h
      ext v
      rw [zero_apply, logPotential_fderiv_apply hz hF hne]
      change k/z.im*v.im-(r*v).re=0
      rw [h]
      simp [Complex.div_re, Complex.div_im, mul_re, mul_im]
      field_simp
      ring
  rw [hrc]
  dsimp [r,criticalMap]
  constructor
  · intro h
    have he := (div_eq_iff hFC).mp h
    rw [he]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  · intro h
    apply (div_eq_iff hFC).mpr
    apply_fun (fun w : ℂ => w * (k:ℂ)) at h
    field_simp at h ⊢
    linear_combination (norm := ring_nf) I*h
    simp [Complex.I_sq]

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma criticalHeight_pos {k : ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hF : deriv F z ≠ 0) :
    0 < criticalHeight k F z := by
  exact mul_pos (mul_pos hk (Real.rpow_pos_of_pos hz _)) (norm_pos_iff.mpr (inv_ne_zero hF))

lemma continuous_criticalMap (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalMap k (halfPlaneFunction p.1) p.2) := by
  exact continuous_halfPlaneFunction.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (UpperHalfPlane.continuous_im.comp continuous_snd))).mul
    continuous_halfPlaneFunction_deriv |>.div_const _)

lemma continuous_criticalHeight (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => criticalHeight k (halfPlaneFunction p.1) p.2) := by
  apply (continuous_const.mul ?_).mul ?_
  · exact (UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
      (fun p => Or.inl p.2.im_ne_zero)
  · exact (continuous_halfPlaneFunction_deriv.inv₀
      (fun p => halfPlaneFunction_deriv_ne_zero p.1 p.2.im_pos)).norm

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.MeasurableGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isClosed_exists_mem_compact {P X : Type*} [TopologicalSpace P] [TopologicalSpace X]
    {K : Set X} (hK : IsCompact K) {R : Set (P × X)} (hR : IsClosed R) :
    IsClosed {p : P | ∃ x ∈ K, (p,x) ∈ R} := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hc : IsClosed {q : P × K | (q.1,(q.2:X)) ∈ R} :=
    hR.preimage (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hh := isClosedMap_fst_of_compactSpace _ hc
  convert hh using 1
  ext p
  simp only [mem_ofPred_eq, mem_image, Prod.exists, Subtype.exists, exists_and_right,
    exists_eq_right]
  constructor <;> rintro ⟨x,hx,hr⟩ <;> exact ⟨x,hx,hr⟩

lemma measurableSet_exists_of_closed_sigmaCompact {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    {R : Set (P × X)} (hR : IsClosed R) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ R} := by
  have he : {p : P | ∃ x : X, (p,x) ∈ R} =
      ⋃ n : ℕ, {p : P | ∃ x ∈ compactCovering X n, (p,x) ∈ R} := by
    ext p
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · rintro ⟨x,hx⟩
      obtain ⟨n,hn⟩ := (iUnion_eq_univ_iff.mp (iUnion_compactCovering X)) x
      exact ⟨n,x,hn,hx⟩
    · rintro ⟨n,x,_,hx⟩
      exact ⟨x,hx⟩
  rw [he]
  exact MeasurableSet.iUnion (fun n =>
    (isClosed_exists_mem_compact (isCompact_compactCovering X n) hR).measurableSet)

lemma measurableSet_compact_positive_sublevels {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [SigmaCompactSpace X] [WeaklyLocallyCompactSpace X]
    {g : P × X → ℝ} (hg : Continuous g) :
    MeasurableSet {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} := by
  let K : CompactExhaustion X := CompactExhaustion.choice X
  let C (n m : ℕ) : Set P := {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
  have hC (n m : ℕ) : IsClosed (C n m) := by
    change IsClosed {p | ∀ x : X, x ∉ K m → (n:ℝ)+1 ≤ g (p,x)}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun _ =>
      isClosed_le continuous_const (hg.comp (continuous_id.prodMk continuous_const))))
  have he : {p : P | ∀ r : ℝ, 0 < r → IsCompact {x : X | g (p,x) ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, C n m := by
    ext p
    simp only [mem_ofPred_eq, mem_iInter, mem_iUnion]
    constructor
    · intro hp n
      obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact (hp ((n:ℝ)+1) (by positivity))
      refine ⟨m, ?_⟩
      intro x hx
      exact le_of_lt (lt_of_not_ge (fun hh => hx (hm hh)))
    · intro hp r hr
      obtain ⟨n,hn⟩ := exists_nat_gt r
      obtain ⟨m,hm⟩ := hp n
      have hs : {x : X | g (p,x) ≤ r} ⊆ K m := by
        intro x hx
        by_contra hxK
        have hh := hm x hxK
        exact (not_le_of_gt (lt_trans hn (by linarith : (n:ℝ)<(n:ℝ)+1))) (hh.trans hx)
      exact IsCompact.of_isClosed_subset (K.isCompact m)
        (isClosed_le (hg.comp (continuous_const.prodMk continuous_id)) continuous_const) hs
  rw [he]
  exact MeasurableSet.iInter (fun n => MeasurableSet.iUnion (fun m => (hC n m).measurableSet))

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma continuous_logarithmicDerivative :
    Continuous (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) := by
  have he : (fun p : DiskFamily × HalfPlaneSet => logarithmicDerivative (halfPlaneFunction p.1) p.2) =
      (fun p => I * (p.2.val.im : ℂ) * (deriv (reciprocalFunction p.1) p.2 / reciprocalFunction p.1 p.2)) := by
    funext p
    exact logarithmicDerivative_eq_reciprocal _ p.2.property
  rw [he]
  exact (continuous_const.mul (Complex.continuous_ofReal.comp
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)))).mul
    (continuous_reciprocalFunction_deriv.div continuous_reciprocalFunction
      (fun p => reciprocalFunction_ne_zero _ p.2.property))

lemma continuous_jacobianExpression (k : ℝ) :
    Continuous (fun p : DiskFamily × HalfPlaneSet => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  unfold jacobianExpression
  exact ((continuous_const.add ((Complex.continuous_re.comp continuous_logarithmicDerivative).const_mul _)).add
    (continuous_logarithmicDerivative.norm.pow 2)).div_const _

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_reciprocalPotential (k : ℝ) :
    Continuous (fun p : (DiskFamily × ℂ) × UpperHalfPlane => reciprocalPotential k p.1 p.2) := by
  exact ((continuous_halfPlaneFunction.comp
    ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).sub
      (continuous_snd.comp continuous_fst)).norm.div
    ((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const (fun p => Or.inl p.2.im_ne_zero))
    (fun p => (Real.rpow_pos_of_pos p.2.im_pos _).ne')

lemma continuous_jacobianExpression_upper (k : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianExpression k (halfPlaneFunction p.1) p.2) := by
  have hc : Continuous (fun p : DiskFamily × UpperHalfPlane =>
      (p.1, (⟨(p.2:ℂ),p.2.im_pos⟩ : HalfPlaneSet))) :=
    continuous_fst.prodMk ((UpperHalfPlane.continuous_coe.comp continuous_snd).subtype_mk _)
  have hh := (continuous_jacobianExpression k).comp hc
  exact hh

lemma measurableSet_regular_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
        jacobianExpression k (halfPlaneFunction p.1) z ≠ 0} := by
  have hm : Continuous (fun q : (DiskFamily × ℂ) × UpperHalfPlane => (q.1.1,q.2)) :=
    (continuous_fst.comp continuous_fst).prodMk continuous_snd
  have hG := (continuous_criticalMap k).comp hm
  have hJ := (continuous_jacobianExpression_upper k).comp hm
  have he := measurableSet_exists_of_closed_sigmaCompact
    ((isClosed_eq hG (continuous_snd.comp continuous_fst)).inter (isClosed_eq hJ (continuous_const (y := (0 : ℝ)))))
  convert he.compl using 1
  ext p
  simp

lemma measurableSet_untied_pairs (k : ℝ) :
    MeasurableSet {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} := by
  let R (n : ℕ) : Set ((DiskFamily × ℂ) × (UpperHalfPlane × UpperHalfPlane)) :=
    {q | criticalMap k (halfPlaneFunction q.1.1) q.2.1 = q.1.2 ∧
      criticalMap k (halfPlaneFunction q.1.1) q.2.2 = q.1.2 ∧
      criticalHeight k (halfPlaneFunction q.1.1) q.2.1 = criticalHeight k (halfPlaneFunction q.1.1) q.2.2 ∧
      1/((n:ℝ)+1) ≤ dist (q.2.1 : ℂ) (q.2.2 : ℂ)}
  have hR (n : ℕ) : IsClosed (R n) := by
    exact (isClosed_eq ((continuous_criticalMap k).comp
      ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalMap k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))
          (continuous_snd.comp continuous_fst)).inter <|
      (isClosed_eq ((continuous_criticalHeight k).comp
        ((continuous_fst.comp continuous_fst).prodMk (continuous_fst.comp continuous_snd)))
        ((continuous_criticalHeight k).comp
          ((continuous_fst.comp continuous_fst).prodMk (continuous_snd.comp continuous_snd)))).inter <|
      isClosed_le continuous_const
        ((UpperHalfPlane.continuous_coe.comp (continuous_fst.comp continuous_snd)).dist
          (UpperHalfPlane.continuous_coe.comp (continuous_snd.comp continuous_snd)))
  have he : {p : DiskFamily × ℂ | ∀ z w : UpperHalfPlane,
      criticalMap k (halfPlaneFunction p.1) z = p.2 →
      criticalMap k (halfPlaneFunction p.1) w = p.2 →
      criticalHeight k (halfPlaneFunction p.1) z = criticalHeight k (halfPlaneFunction p.1) w → z = w} =
      (⋃ n : ℕ, {p : DiskFamily × ℂ | ∃ x : UpperHalfPlane × UpperHalfPlane, (p,x) ∈ R n})ᶜ := by
    ext p
    simp only [mem_ofPred_eq, mem_compl_iff, mem_iUnion]
    constructor
    · intro hp
      rintro ⟨n,⟨z,w⟩,hz,hw,hv,hd⟩
      have := hp z w hz hw hv
      subst w
      have h0 := one_div_pos.mpr (by positivity : (0:ℝ)<(n:ℝ)+1)
      rw [dist_self] at hd
      linarith
    · intro hp z w hz hw hv
      by_contra hne
      have hd : 0 < dist (z:ℂ) (w:ℂ) := dist_pos.mpr (fun he => hne (UpperHalfPlane.ext he))
      obtain ⟨n,hn⟩ := exists_nat_gt (1 / dist (z:ℂ) (w:ℂ))
      apply hp
      refine ⟨n,(z,w),hz,hw,hv,?_⟩
      apply (div_le_iff₀ (by positivity : (0:ℝ)<(n:ℝ)+1)).mpr
      have hh := (div_lt_iff₀ hd).mp hn
      nlinarith
  rw [he]
  exact (MeasurableSet.iUnion (fun n => measurableSet_exists_of_closed_sigmaCompact (hR n))).compl

lemma measurableSet_goodPairs (k : ℝ) : MeasurableSet {p : DiskFamily × ℂ | GoodPair k p} := by
  have hc : MeasurableSet {p : DiskFamily × ℂ |
      ∀ h : ℝ, 0 < h → IsCompact (potentialSuperlevel k (halfPlaneFunction p.1) p.2 h)} := by
    simp only [compactPotential_iff]
    exact measurableSet_compact_positive_sublevels (continuous_reciprocalPotential k)
  exact hc.inter ((measurableSet_regular_pairs k).inter (measurableSet_untied_pairs k))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RegularTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter MeasureTheory Complex
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma countable_scalar_regular_fiber {f : ℝ → ℝ} {s : Set ℝ} {c : ℝ}
    (hs : ∀ x ∈ s, f x = c ∧ ∃ d : ℝ, HasDerivAt f d x ∧ d ≠ 0) : s.Countable := by
  have hd : DiscreteTopology s := discreteTopology_subtype_iff.mpr (by
    intro x hx
    obtain ⟨_,d,hder,hd⟩ := hs x hx
    have he : ∀ᶠ z in 𝓝[≠] x, f z ≠ c := hder.eventually_ne hd
    rw [Filter.inf_principal_eq_bot]
    exact he.mono (fun z hz hzs => hz (hs z hzs).1))
  have : Countable s := countable_of_Lindelof_of_discrete
  exact Set.countable_coe_iff.mp inferInstance

lemma plane_regular_slice_null {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : ∀ p ∈ s, f p = 0 ∧
      ∃ d : ℝ, HasDerivAt (fun y => f (p.1,y)) d p.2 ∧ d ≠ 0) :
    volume s = 0 := by
  rw [Measure.volume_eq_prod]
  apply Measure.measure_prod_null_of_ae_null hs
  apply Filter.Eventually.of_forall
  intro x
  apply Set.Countable.measure_zero
  apply countable_scalar_regular_fiber (f := fun y => f (x,y)) (c := 0)
  intro y hy
  exact hf (x,y) hy

lemma plane_regular_slice_fst_null {f : ℝ × ℝ → ℝ} {s : Set (ℝ × ℝ)}
    (hs : MeasurableSet s) (hf : ∀ p ∈ s, f p = 0 ∧
      ∃ d : ℝ, HasDerivAt (fun x => f (x,p.2)) d p.1 ∧ d ≠ 0) :
    volume s = 0 := by
  have hh : volume (Prod.swap ⁻¹' s) = 0 := by
    apply plane_regular_slice_null (hs.preimage measurable_swap)
    intro p hp
    exact hf p.swap hp
  have hm := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ))
    (ν := (volume : Measure ℝ))).measure_preimage hs.nullMeasurableSet
  rw [← Measure.volume_eq_prod] at hm
  exact hm ▸ hh

lemma measurableSet_zero_in_open {E : Type*} [TopologicalSpace E] [MeasurableSpace E]
    [BorelSpace E] {f : E → ℝ} {U : Set E} (hU : IsOpen U) (hf : ContinuousOn f U) :
    MeasurableSet {x ∈ U | f x = 0} := by
  have ho := hf.isOpen_inter_preimage hU (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))
  have he : {x ∈ U | f x = 0} = U \ (U ∩ f ⁻¹' {x : ℝ | x ≠ 0}) := by
    ext x
    simp only [mem_ofPred_eq, Set.mem_sdiff, mem_inter_iff, mem_preimage, not_and, not_not]
    tauto
  rw [he]
  exact hU.measurableSet.diff ho.measurableSet

lemma plane_regular_level_null {f : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    volume {p ∈ U | f p = 0 ∧ fderiv ℝ f p ≠ 0} = 0 := by
  let S (v : ℝ × ℝ) : Set (ℝ × ℝ) := {p ∈ U | f p = 0 ∧ fderiv ℝ f p v ≠ 0}
  have hS (v : ℝ × ℝ) : MeasurableSet (S v) := by
    have hc := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply (continuousOn_const (c := v))
    have ho := hc.isOpen_inter_preimage hU (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))
    exact (measurableSet_zero_in_open hU hf.continuousOn).inter ho.measurableSet |>.congr
      (by ext p; simp only [S, mem_inter_iff, mem_ofPred_eq, mem_preimage]; tauto)
  have hy : volume (S (0,1)) = 0 := by
    apply plane_regular_slice_null (hS (0,1))
    intro p hp
    refine ⟨hp.2.1, fderiv ℝ f p (0,1), ?_, hp.2.2⟩
    exact ((hf.differentiableOn one_ne_zero p hp.1).differentiableAt
      (hU.mem_nhds hp.1)).hasFDerivAt.comp_hasDerivAt p.2
        ((hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2))
  have hx : volume (S (1,0)) = 0 := by
    apply plane_regular_slice_fst_null (hS (1,0))
    intro p hp
    refine ⟨hp.2.1, fderiv ℝ f p (1,0), ?_, hp.2.2⟩
    exact ((hf.differentiableOn one_ne_zero p hp.1).differentiableAt
      (hU.mem_nhds hp.1)).hasFDerivAt.comp_hasDerivAt p.1
        ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2))
  apply measure_mono_null (t := S (1,0) ∪ S (0,1)) _ (measure_union_null hx hy)
  intro p hp
  by_cases h1 : fderiv ℝ f p (1,0) ≠ 0
  · exact Or.inl ⟨hp.1, hp.2.1, h1⟩
  · refine Or.inr ⟨hp.1, hp.2.1, ?_⟩
    intro h2
    apply hp.2.2
    apply ContinuousLinearMap.ext
    intro v
    have hv : v = v.1 • (1,0) + v.2 • (0,1) := by ext <;> simp
    simp only [ne_eq, not_not] at h1
    rw [hv, map_add, map_smul, map_smul, h1, h2]
    simp

lemma complex_regular_level_null {f : ℂ → ℝ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ContDiffOn ℝ 1 f U) :
    volume {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} = 0 := by
  let e := Complex.equivRealProdCLM
  let g : ℝ × ℝ → ℝ := f ∘ e.symm
  have hV : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hg : ContDiffOn ℝ 1 g (e.symm ⁻¹' U) :=
    hf.comp e.symm.contDiff.contDiffOn (fun _ h => h)
  have he (p : ℝ × ℝ) (hp : e.symm p ∈ U) :
      fderiv ℝ g p ≠ 0 ↔ fderiv ℝ f (e.symm p) ≠ 0 := by
    have hdf := (hf.differentiableOn one_ne_zero (e.symm p) hp).differentiableAt (hU.mem_nhds hp)
    have hdg : fderiv ℝ g p = (fderiv ℝ f (e.symm p)).comp (e.symm : (ℝ × ℝ) →L[ℝ] ℂ) := by
      rw [show g = f ∘ e.symm from rfl, fderiv_comp p hdf e.symm.differentiableAt,
        e.symm.fderiv]
    rw [hdg]
    constructor
    · intro hn hh
      exact hn (by rw [hh]; apply ContinuousLinearMap.ext; intro v; simp)
    · intro hn hh
      apply hn
      apply ContinuousLinearMap.ext
      intro z
      have h := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (e z)) hh
      simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
        ContinuousLinearEquiv.symm_apply_apply, zero_apply] using h
  have hset : {p ∈ e.symm ⁻¹' U | g p = 0 ∧ fderiv ℝ g p ≠ 0} =
      e.symm ⁻¹' {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} := by
    ext p
    simp only [mem_ofPred_eq, mem_preimage, g, Function.comp_apply]
    by_cases hp : e.symm p ∈ U
    · rw [and_iff_right hp, and_iff_right hp, he p hp]
    · simp only [hp, false_and]
  have hz := plane_regular_level_null hV hg
  rw [hset] at hz
  have hmeas : MeasurableSet {z ∈ U | f z = 0 ∧ fderiv ℝ f z ≠ 0} := by
    have hd := (hf.continuousOn_fderiv_of_isOpen hU le_rfl).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id (continuous_const (y := (0 : ℂ →L[ℝ] ℝ))))
    convert (measurableSet_zero_in_open hU hf.continuousOn).inter hd.measurableSet using 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, mem_preimage]
    tauto
  have hmp := Complex.volume_preserving_equiv_real_prod.symm
  exact hmp.measure_preimage hmeas.nullMeasurableSet ▸ hz

end
end StrictInverseFirstPower

open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma isOpen_regular_locus {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    IsOpen {z ∈ U | (fderiv ℝ G z).det ≠ 0} := by
  exact ((ContinuousLinearMap.continuous_det).comp_continuousOn
    (hG.continuousOn_fderiv_of_isOpen hU le_rfl)).isOpen_inter_preimage hU
      (isOpen_ne_fun continuous_id (continuous_const (y := (0:ℝ))))

lemma regular_inverse_chart {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {z : ℂ} (hz : z ∈ U) (hd : (fderiv ℝ G z).det ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, (e : ℂ → ℂ) = G ∧ z ∈ e.source ∧
      e.source ⊆ {w ∈ U | (fderiv ℝ G w).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target := by
  let R := {w ∈ U | (fderiv ℝ G w).det ≠ 0}
  have hR : IsOpen R := isOpen_regular_locus hU hG
  have hcz : ContDiffAt ℝ 1 G z := hG.contDiffAt (hU.mem_nhds hz)
  let L := (fderiv ℝ G z).toContinuousLinearEquivOfDetNeZero hd
  have hdz : HasFDerivAt G (L : ℂ →L[ℝ] ℂ) z := by
    simpa only [L, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
      (hcz.differentiableAt one_ne_zero).hasFDerivAt
  let e0 := hcz.toOpenPartialHomeomorph G hdz one_ne_zero
  let e := e0.restr R
  have he : (e : ℂ → ℂ) = G := rfl
  have hs : e.source ⊆ R := by
    rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact inter_subset_right
  refine ⟨e, he, ?_, hs, ?_⟩
  · rw [show e = e0.restr R from rfl, e0.restr_source' R hR]
    exact ⟨hcz.mem_toOpenPartialHomeomorph_source hdz one_ne_zero, hz, hd⟩
  · intro ξ hξ
    have hp := hs (e.map_target hξ)
    have hc : ContDiffAt ℝ 1 G (e.symm ξ) := hG.contDiffAt (hU.mem_nhds hp.1)
    let A := (fderiv ℝ G (e.symm ξ)).toContinuousLinearEquivOfDetNeZero hp.2
    have hdf : HasFDerivAt e (A : ℂ →L[ℝ] ℂ) (e.symm ξ) := by
      rw [he]
      simpa only [A, ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        (hc.differentiableAt one_ne_zero).hasFDerivAt
    exact (e.contDiffAt_symm hξ hdf (he ▸ hc)).contDiffWithinAt

lemma countable_regular_inverse_charts {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) :
    ∃ C : Set (OpenPartialHomeomorph ℂ ℂ), C.Countable ∧
      (∀ e ∈ C, (e : ℂ → ℂ) = G ∧
        e.source ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0} ∧ ContDiffOn ℝ 1 e.symm e.target) ∧
      {z ∈ U | (fderiv ℝ G z).det ≠ 0} ⊆ ⋃ e ∈ C, e.source := by
  classical
  let R := {z ∈ U | (fderiv ℝ G z).det ≠ 0}
  have hex (z : R) := regular_inverse_chart hU hG z.property.1 z.property.2
  choose E hE hmem hsub hdiff using hex
  have hcover : R ⊆ ⋃ z : R, (E z).source := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hmem ⟨z,hz⟩⟩
  obtain ⟨c,hc,hcov⟩ := (HereditarilyLindelofSpace.isLindelof R).elim_countable_subcover
    (fun z : R => (E z).source) (fun z => (E z).open_source) hcover
  refine ⟨E '' c,hc.image E,?_,?_⟩
  · rintro e ⟨z,_,rfl⟩
    exact ⟨hE z,hsub z,hdiff z⟩
  · intro z hz
    obtain ⟨w,hw,hz'⟩ := mem_iUnion₂.mp (hcov hz)
    exact mem_iUnion₂.mpr ⟨E w,⟨w,hw,rfl⟩,hz'⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GenericTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function
open scoped Topology
open Set Filter Metric Complex Function MeasureTheory
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology
open Set Filter Function MeasureTheory
open scoped Topology ENNReal NNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ContDiff
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
open Set Filter MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter Metric Complex MeasureTheory
open scoped Topology
open Set Filter MeasureTheory Complex
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma real_complex_log_norm_fderiv {H : ℂ → ℂ} {ξ : ℂ}
    (hH : DifferentiableAt ℝ H ξ) (hne : H ξ ≠ 0) (v : ℂ) :
    fderiv ℝ (fun η => Real.log ‖H η‖) ξ v = ((fderiv ℝ H ξ v) / H ξ).re := by
  have hh := ((hH.hasFDerivAt.norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hne))).const_mul (1/2)
  have he : (fun η => (1/2:ℝ) * Real.log (‖H η‖^2)) = (fun η => Real.log ‖H η‖) := by
    funext η
    rw [Real.log_pow]
    ring
  rw [he] at hh
  rw [hh.fderiv]
  simp only [smul_apply, ContinuousLinearMap.comp_apply, smul_eq_mul, innerSL_apply_apply]
  simp only [Complex.inner, Complex.mul_re, Complex.div_re, Complex.conj_re, Complex.conj_im]
  rw [← Complex.normSq_eq_norm_sq]
  field_simp
  ring

lemma logPotential_branch_contDiffAt {k : ℝ} {F Z : ℂ → ℂ} {ξ : ℂ}
    (hF : AnalyticAt ℂ F (Z ξ)) (hZ : ContDiffAt ℝ 1 Z ξ)
    (hy : 0 < (Z ξ).im) (hp : F (Z ξ) ≠ ξ) :
    ContDiffAt ℝ 1 (fun η => logPotential k F η (Z η)) ξ := by
  have hh := (hF.restrictScalars (𝕜 := ℝ)).contDiffAt (n := 1)
  exact (contDiffAt_const.mul ((Complex.imCLM.contDiff.contDiffAt.comp ξ hZ).log hy.ne')).sub
    ((((hh.comp ξ hZ).sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hp)).log
      (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)))

lemma critical_branch_derivative {k : ℝ} {F Z : ℂ → ℂ} {ξ : ℂ}
    (hk : k ≠ 0) (hy : 0 < (Z ξ).im) (hF : DifferentiableAt ℂ F (Z ξ))
    (hp : F (Z ξ) ≠ ξ) (hZ : DifferentiableAt ℝ Z ξ)
    (hG : criticalMap k F (Z ξ) = ξ) (v : ℂ) :
    fderiv ℝ (fun η => logPotential k F η (Z η)) ξ v = (v / (F (Z ξ)-ξ)).re := by
  have h1 := (((Complex.imCLM.hasFDerivAt (x := Z ξ)).comp ξ hZ.hasFDerivAt).log hy.ne').const_mul k
  change HasFDerivAt (fun η => k * Real.log (Z η).im)
    (k • (Z ξ).im⁻¹ • (Complex.imCLM.comp (fderiv ℝ Z ξ))) ξ at h1
  have hpr : DifferentiableAt ℝ (fun η => F (Z η)-η) ξ :=
    ((hF.restrictScalars (𝕜 := ℝ)).comp ξ hZ).sub differentiableAt_id
  have h2 := (hpr.norm ℝ (sub_ne_zero.mpr hp)).log
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
  have hcomp : fderiv ℝ (fun η => F (Z η)-η) ξ v =
      deriv F (Z ξ) * fderiv ℝ Z ξ v - v := by
    have hd := ((hF.hasDerivAt.complexToReal_fderiv).comp ξ hZ.hasFDerivAt).sub (hasFDerivAt_id ξ)
    change (fderiv ℝ (F ∘ Z - id) ξ) v = _
    rw [hd.fderiv]
    simp only [sub_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self,
      ContinuousLinearMap.id_apply, smul_apply, smul_eq_mul]
  change (fderiv ℝ ((fun η => k * Real.log (Z η).im) -
    (fun η => Real.log ‖F (Z η)-η‖)) ξ) v = _
  rw [fderiv_sub h1.differentiableAt h2, sub_apply, h1.fderiv,
    real_complex_log_norm_fderiv hpr (sub_ne_zero.mpr hp), hcomp]
  simp only [smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply, Complex.imCLM_apply]
  have hz := congrArg (fun L : ℂ →L[ℝ] ℝ => L (fderiv ℝ Z ξ v))
    ((logPotential_critical_iff hk hy hF hp).mpr hG)
  rw [logPotential_fderiv_apply hy hF hp, zero_apply] at hz
  have he : (deriv F (Z ξ) * fderiv ℝ Z ξ v - v) / (F (Z ξ)-ξ) =
      (deriv F (Z ξ) / (F (Z ξ)-ξ)) * fderiv ℝ Z ξ v - v/(F (Z ξ)-ξ) := by ring
  rw [he, Complex.sub_re]
  linear_combination hz

lemma critical_branch_difference_nz {k : ℝ} {F Z W : ℂ → ℂ} {ξ : ℂ}
    (hk : k ≠ 0) (hZy : 0 < (Z ξ).im) (hWy : 0 < (W ξ).im)
    (hFZ : DifferentiableAt ℂ F (Z ξ)) (hFW : DifferentiableAt ℂ F (W ξ))
    (hpZ : F (Z ξ) ≠ ξ) (hpW : F (W ξ) ≠ ξ)
    (hZ : DifferentiableAt ℝ Z ξ) (hW : DifferentiableAt ℝ W ξ)
    (hGZ : criticalMap k F (Z ξ) = ξ) (hGW : criticalMap k F (W ξ) = ξ)
    (hne : F (Z ξ) ≠ F (W ξ)) :
    fderiv ℝ (fun η => logPotential k F η (Z η) - logPotential k F η (W η)) ξ ≠ 0 := by
  have hdZ : DifferentiableAt ℝ (fun η => logPotential k F η (Z η)) ξ := by
    exact (((Complex.imCLM.differentiableAt.comp ξ hZ).log hZy.ne').const_mul k).sub
      (((((hFZ.restrictScalars (𝕜 := ℝ)).comp ξ hZ).sub differentiableAt_id).norm ℝ
        (sub_ne_zero.mpr hpZ)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpZ)))
  have hdW : DifferentiableAt ℝ (fun η => logPotential k F η (W η)) ξ := by
    exact (((Complex.imCLM.differentiableAt.comp ξ hW).log hWy.ne').const_mul k).sub
      (((((hFW.restrictScalars (𝕜 := ℝ)).comp ξ hW).sub differentiableAt_id).norm ℝ
        (sub_ne_zero.mpr hpW)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpW)))
  intro hh
  have he (v : ℂ) : (v / (F (Z ξ)-ξ)).re = (v/(F (W ξ)-ξ)).re := by
    have h := congrArg (fun L : ℂ →L[ℝ] ℝ => L v) hh
    change (fderiv ℝ ((fun η => logPotential k F η (Z η)) -
      (fun η => logPotential k F η (W η))) ξ) v = (0 : ℂ →L[ℝ] ℝ) v at h
    rw [fderiv_sub hdZ hdW, sub_apply, critical_branch_derivative hk hZy hFZ hpZ hZ hGZ,
      critical_branch_derivative hk hWy hFW hpW hW hGW, zero_apply] at h
    exact sub_eq_zero.mp h
  have hc : (F (Z ξ)-ξ)⁻¹ = (F (W ξ)-ξ)⁻¹ := by
    apply Complex.ext
    · simpa only [one_div] using he 1
    · have ht := he I
      simp only [div_eq_mul_inv, I_mul_re] at ht
      linarith
  have hc' := inv_injective hc
  exact hne (by simpa using congrArg (fun w : ℂ => w + ξ) hc')

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma singular_values_null {G : ℂ → ℂ} {U : Set ℂ}
    (hG : ∀ z ∈ U, DifferentiableAt ℝ G z) :
    volume (G '' {z ∈ U | (fderiv ℝ G z).det = 0}) = 0 := by
  apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
    (f' := fderiv ℝ G)
  · intro z hz
    exact (hG z hz.1).hasFDerivAt.hasFDerivWithinAt
  · intro z hz
    exact hz.2

lemma criticalMap_contDiffOn (k : ℝ) (f : DiskFamily) :
    ContDiffOn ℝ 1 (criticalMap k (halfPlaneFunction f)) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact ((criticalMap_contDiffAt k f hz).of_le (by simp)).contDiffWithinAt

lemma logPotential_eq_log_criticalHeight {k : ℝ} (f : DiskFamily) {ξ z : ℂ}
    (hk : 0 < k) (hz : 0 < z.im) (hg : criticalMap k (halfPlaneFunction f) z = ξ) :
    logPotential k (halfPlaneFunction f) ξ z = Real.log (criticalHeight k (halfPlaneFunction f) z) := by
  have hp : halfPlaneFunction f z ≠ ξ := by
    intro he
    exact criticalMap_ne_image hk.ne' hz (halfPlaneFunction_deriv_ne_zero f hz) (hg.trans he.symm)
  rw [← criticalHeight_value hk hz hg, Real.log_div
    (Real.rpow_pos_of_pos hz k).ne' (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)),
    Real.log_rpow hz]
  unfold logPotential
  rw [mul_comm k]

lemma critical_inverse_chart_data {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hs : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    {ξ : ℂ} (hξ : ξ ∈ e.target) :
    0 < (e.symm ξ).im ∧ halfPlaneFunction f (e.symm ξ) ≠ ξ ∧
      criticalMap k (halfPlaneFunction f) (e.symm ξ) = ξ := by
  have hy := (hs (e.map_target hξ)).1
  have hg : criticalMap k (halfPlaneFunction f) (e.symm ξ) = ξ := by
    rw [← he]
    exact e.right_inv hξ
  refine ⟨hy,?_,hg⟩
  intro hp
  exact criticalMap_ne_image hk hy (halfPlaneFunction_deriv_ne_zero f hy) (hg.trans hp.symm)

lemma critical_inverse_branch_contDiffOn {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e : OpenPartialHomeomorph ℂ ℂ) (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hs : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (hd : ContDiffOn ℝ 1 e.symm e.target) :
    ContDiffOn ℝ 1 (fun ξ => logPotential k (halfPlaneFunction f) ξ (e.symm ξ)) e.target := by
  intro ξ hξ
  obtain ⟨hy,hp,_⟩ := critical_inverse_chart_data hk f e he hs hξ
  exact (logPotential_branch_contDiffAt
    ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hy))
    (hd.contDiffAt (e.open_target.mem_nhds hξ)) hy hp).contDiffWithinAt

lemma inverse_chart_pair_ties_null {k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (e d : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (hd : (d : ℂ → ℂ) = criticalMap k (halfPlaneFunction f))
    (heS : e.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (hdS : d.source ⊆ {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0})
    (heD : ContDiffOn ℝ 1 e.symm e.target) (hdD : ContDiffOn ℝ 1 d.symm d.target) :
    volume {ξ | ξ ∈ e.target ∧ ξ ∈ d.target ∧ e.symm ξ ≠ d.symm ξ ∧
      logPotential k (halfPlaneFunction f) ξ (e.symm ξ) =
        logPotential k (halfPlaneFunction f) ξ (d.symm ξ)} = 0 := by
  let U := e.target ∩ d.target
  let V := {ξ ∈ U | e.symm ξ ≠ d.symm ξ}
  let φ := fun ξ => logPotential k (halfPlaneFunction f) ξ (e.symm ξ) -
    logPotential k (halfPlaneFunction f) ξ (d.symm ξ)
  have hU : IsOpen U := e.open_target.inter d.open_target
  have hV : IsOpen V := by
    have ht := (e.continuousOn_symm.mono inter_subset_left |>.sub
      (d.continuousOn_symm.mono inter_subset_right)).isOpen_inter_preimage hU
        (isOpen_compl_singleton (x := (0:ℂ)))
    convert ht using 1
    ext ξ
    simp only [V,U, mem_inter_iff, mem_ofPred_eq,
      mem_preimage, mem_compl_iff, mem_singleton_iff, Pi.sub_apply, sub_ne_zero]
  have hφ : ContDiffOn ℝ 1 φ V :=
    ((critical_inverse_branch_contDiffOn hk f e he heS heD).mono
      (fun _ hx => hx.1.1)).sub
      ((critical_inverse_branch_contDiffOn hk f d hd hdS hdD).mono (fun _ hx => hx.1.2))
  have hn (ξ : ℂ) (hξ : ξ ∈ V) : fderiv ℝ φ ξ ≠ 0 := by
    obtain ⟨hy,hp,hg⟩ := critical_inverse_chart_data hk f e he heS hξ.1.1
    obtain ⟨hy',hp',hg'⟩ := critical_inverse_chart_data hk f d hd hdS hξ.1.2
    exact critical_branch_difference_nz hk hy hy'
      ((halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hy))
      ((halfPlaneFunction_differentiableOn f).differentiableAt (isOpen_halfPlane.mem_nhds hy')) hp hp'
      ((heD.contDiffAt (e.open_target.mem_nhds hξ.1.1)).differentiableAt one_ne_zero)
      ((hdD.contDiffAt (d.open_target.mem_nhds hξ.1.2)).differentiableAt one_ne_zero) hg hg'
      (fun hh => hξ.2 (halfPlaneFunction_injOn f hy hy' hh))
  apply measure_mono_null (t := {ξ ∈ V | φ ξ = 0 ∧ fderiv ℝ φ ξ ≠ 0}) _
    (complex_regular_level_null hV hφ)
  intro ξ hξ
  have hv : ξ ∈ V := ⟨⟨hξ.1,hξ.2.1⟩,hξ.2.2.1⟩
  exact ⟨hv,sub_eq_zero.mpr hξ.2.2.2,hn ξ hv⟩

theorem ae_regular_distinct_critical_heights {k : ℝ} (hk : 0 < k) (f : DiskFamily) :
    ∀ᵐ ξ : ℂ,
      (∀ z : UpperHalfPlane, criticalMap k (halfPlaneFunction f) z = ξ →
        jacobianExpression k (halfPlaneFunction f) z ≠ 0) ∧
      (∀ z w : UpperHalfPlane, criticalMap k (halfPlaneFunction f) z = ξ →
        criticalMap k (halfPlaneFunction f) w = ξ →
        criticalHeight k (halfPlaneFunction f) z = criticalHeight k (halfPlaneFunction f) w → z = w) := by
  classical
  let G := criticalMap k (halfPlaneFunction f)
  let H := {z : ℂ | 0 < z.im}
  have hc : ContDiffOn ℝ 1 G H := criticalMap_contDiffOn k f
  have hs := singular_values_null (U := H) (G := G)
    (fun z hz => (hc.contDiffAt (isOpen_halfPlane.mem_nhds hz)).differentiableAt one_ne_zero)
  have ha : ∀ᵐ ξ : ℂ, ξ ∉ G '' {z ∈ H | (fderiv ℝ G z).det = 0} := by
    apply ae_iff.mpr
    simpa only [not_not, ofPred_mem_eq] using hs
  obtain ⟨C,hC,hcharts,hcover⟩ := countable_regular_inverse_charts isOpen_halfPlane hc
  have : Countable C := hC.to_subtype
  have ht : ∀ᵐ ξ : ℂ, ∀ e d : C,
      ¬ (ξ ∈ e.1.target ∧ ξ ∈ d.1.target ∧ e.1.symm ξ ≠ d.1.symm ξ ∧
        logPotential k (halfPlaneFunction f) ξ (e.1.symm ξ) =
          logPotential k (halfPlaneFunction f) ξ (d.1.symm ξ)) := by
    apply ae_all_iff.mpr
    intro e
    apply ae_all_iff.mpr
    intro d
    apply ae_iff.mpr
    simpa only [not_not] using inverse_chart_pair_ties_null hk.ne' f e.1 d.1
      (hcharts e.1 e.2).1 (hcharts d.1 d.2).1
      (hcharts e.1 e.2).2.1 (hcharts d.1 d.2).2.1
      (hcharts e.1 e.2).2.2 (hcharts d.1 d.2).2.2
  filter_upwards [ha,ht] with ξ hξ htξ
  have hreg (z : ℂ) (hz : z ∈ H) (hg : G z = ξ) : (fderiv ℝ G z).det ≠ 0 := by
    intro hh
    exact hξ ⟨z,⟨hz,hh⟩,hg⟩
  refine ⟨?_,?_⟩
  · intro z hz
    exact fun hJ => hreg z z.im_pos hz ((jacobianExpression_zero_iff k hk.ne' f z.im_pos).mp hJ)
  · intro z w hz hw hv
    by_contra hne
    have hzR : (z:ℂ) ∈ {z ∈ H | (fderiv ℝ G z).det ≠ 0} := ⟨z.im_pos,hreg z z.im_pos hz⟩
    have hwR : (w:ℂ) ∈ {z ∈ H | (fderiv ℝ G z).det ≠ 0} := ⟨w.im_pos,hreg w w.im_pos hw⟩
    obtain ⟨e,he,hze⟩ := mem_iUnion₂.mp (hcover hzR)
    obtain ⟨d,hd,hwd⟩ := mem_iUnion₂.mp (hcover hwR)
    have heξ : e z = ξ := by rw [(hcharts e he).1]; exact hz
    have hdξ : d w = ξ := by rw [(hcharts d hd).1]; exact hw
    have hξe : ξ ∈ e.target := heξ ▸ e.map_source hze
    have hξd : ξ ∈ d.target := hdξ ▸ d.map_source hwd
    have hzeq : e.symm ξ = z := heξ ▸ e.left_inv hze
    have hwdeq : d.symm ξ = w := hdξ ▸ d.left_inv hwd
    apply htξ ⟨e,he⟩ ⟨d,hd⟩
    refine ⟨hξe,hξd,?_,?_⟩
    · rw [hzeq,hwdeq]
      exact fun hh => hne (UpperHalfPlane.ext hh)
    · rw [hzeq,hwdeq, logPotential_eq_log_criticalHeight f hk z.im_pos hz,
        logPotential_eq_log_criticalHeight f hk w.im_pos hw,hv]

theorem affine_law_ae_good_pairs (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β)
    (hlaw : ∀ (z : UpperHalfPlane) (φ : DiskFamily → ℝ≥0∞), Measurable φ →
      (∫⁻ f, (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
        ENNReal.ofReal (z.im ^ (-β)) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily)) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), ∀ᵐ ξ : ℂ, GoodPair ((β+2)/3) (f,ξ) := by
  filter_upwards [weightedAreaTail_ae_finite μ β hlaw] with f hf
  filter_upwards [ae_compact_positive_superlevels f β hβ hf,ae_regular_distinct_critical_heights (by linarith : 0 < (β+2)/3) f]
    with ξ hc hr
  exact ⟨hc,hr⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DescendingRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set

namespace StrictInverseFirstPower
noncomputable section

lemma descendingRank_lt_of_value_lt {X : Type*} {v : X → ℝ} {S : Set X}
    {x y : X} (hy : y ∈ S) (hxy : v x < v y)
    (hfin : {z | z ∈ S ∧ v x < v z}.Finite) :
    descendingRank v S y < descendingRank v S x := by
  unfold descendingRank
  apply Set.ncard_lt_ncard (Set.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩) hfin
  · intro z hz
    exact ⟨hz.1,hxy.trans hz.2⟩
  · intro he
    have hyx : y ∈ {z | z ∈ S ∧ v x < v z} := ⟨hy,hxy⟩
    rw [← he] at hyx
    exact lt_irrefl _ hyx.2

lemma descendingRank_injOn {X : Type*} {v : X → ℝ} {S : Set X}
    (hv : InjOn v S) (hfin : ∀ x ∈ S, {z | z ∈ S ∧ v x < v z}.Finite) :
    InjOn (descendingRank v S) S := by
  intro x hx y hy he
  apply hv hx hy
  rcases lt_trichotomy (v x) (v y) with hlt | heq | hgt
  · exact False.elim ((descendingRank_lt_of_value_lt hy hlt (hfin x hx)).ne he.symm)
  · exact heq
  · exact False.elim ((descendingRank_lt_of_value_lt hx hgt (hfin y hy)).ne he)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BorelRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter MeasureTheory
open scoped Topology

namespace StrictInverseFirstPower
noncomputable section

lemma measurableSet_exists_closed_open {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X] [PerfectlyNormalSpace (P × X)]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U) :
    MeasurableSet {p : P | ∃ x : X, (p,x) ∈ C ∩ U} := by
  obtain ⟨W,hW,hUW⟩ := hU.isClosed_compl.isGδ.eq_iInter_nat
  have he : U = ⋃ n : ℕ, (W n)ᶜ := by
    rw [← compl_iInter, ← hUW, compl_compl]
  have hp : {p : P | ∃ x : X, (p,x) ∈ C ∩ U} =
      ⋃ n : ℕ, {p : P | ∃ x : X, (p,x) ∈ C ∩ (W n)ᶜ} := by
    ext p
    simp only [mem_ofPred_eq,mem_iUnion,mem_inter_iff,he]
    constructor
    · rintro ⟨x,hx,n,hn⟩
      exact ⟨n,x,hx,hn⟩
    · rintro ⟨n,x,hx,hn⟩
      exact ⟨x,hx,n,hn⟩
  rw [hp]
  exact MeasurableSet.iUnion (fun n =>
    measurableSet_exists_of_closed_sigmaCompact (hC.inter (hW n).isClosed_compl))

lemma finite_ncard_ge_iff_tuple {X : Type*} {S : Set X} (hS : S.Finite) (n : ℕ) :
    n ≤ S.ncard ↔ ∃ t : Fin n → X, Function.Injective t ∧ ∀ i, t i ∈ S := by
  classical
  let := hS.fintype
  have hc : S.ncard = Fintype.card S := by
    rw [Set.ncard_eq_toFinset_card']
    exact Set.toFinset_card S
  rw [hc]
  constructor
  · intro hn
    let e : Fin n ↪ S := (Fin.castLEEmb hn).trans (Fintype.equivFin S).symm.toEmbedding
    exact ⟨fun i => (e i : X), Subtype.val_injective.comp e.injective, fun i => (e i).2⟩
  · rintro ⟨t,ht,hS⟩
    simpa using Fintype.card_le_of_injective (fun i : Fin n => (⟨t i,hS i⟩ : S))
      (fun i j h => ht (congrArg Subtype.val h))

lemma measurable_ncard_locally_closed_fiber {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P] [TopologicalSpace.MetrizableSpace P]
    [TopologicalSpace X] [TopologicalSpace.MetrizableSpace X] [SigmaCompactSpace X]
    {C U : Set (P × X)} (hC : IsClosed C) (hU : IsOpen U)
    (hf : ∀ p : P, {x : X | (p,x) ∈ C ∩ U}.Finite) :
    Measurable (fun p : P => {x : X | (p,x) ∈ C ∩ U}.ncard) := by
  apply measurable_of_Ici
  intro n
  let Cn : Set (P × (Fin n → X)) := {q | ∀ i, (q.1,q.2 i) ∈ C}
  let Un : Set (P × (Fin n → X)) :=
    {q | (∀ i, (q.1,q.2 i) ∈ U) ∧ Function.Injective q.2}
  have hCn : IsClosed Cn := by
    change IsClosed {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ C}
    simp only [ofPred_forall]
    exact isClosed_iInter (fun i => hC.preimage
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
  have hUn : IsOpen Un := by
    have hmem : IsOpen {q : P × (Fin n → X) | ∀ i, (q.1,q.2 i) ∈ U} := by
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => hU.preimage
        (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd)))
    have hinj : IsOpen {q : P × (Fin n → X) | Function.Injective q.2} := by
      have he : {q : P × (Fin n → X) | Function.Injective q.2} =
          {q | ∀ i j : Fin n, i ≠ j → q.2 i ≠ q.2 j} := by
        ext q
        simp only [mem_ofPred_eq]
        constructor
        · intro h i j hij heq
          exact hij (h heq)
        · intro h i j heq
          by_contra hij
          exact h i j hij heq
      rw [he]
      simp only [ofPred_forall]
      exact isOpen_iInter_of_finite (fun i => isOpen_iInter_of_finite (fun j =>
        isOpen_iInter_of_finite (fun _ => isOpen_ne_fun
          ((continuous_apply i).comp continuous_snd) ((continuous_apply j).comp continuous_snd))))
    exact hmem.inter hinj
  have hp := measurableSet_exists_closed_open hCn hUn
  convert hp using 1
  ext p
  simp only [mem_preimage,mem_Ici,mem_ofPred_eq,Cn,Un,mem_inter_iff]
  have htest := finite_ncard_ge_iff_tuple (hf p) n
  simp only [mem_inter_iff] at htest
  rw [htest]
  constructor
  · rintro ⟨t,ht,hm⟩
    exact ⟨t,fun i => (hm i).1,fun i => (hm i).2,ht⟩
  · rintro ⟨t,hC,hU,ht⟩
    exact ⟨t,ht,fun i => ⟨hC i,hU i⟩⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalRanks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma signedCriticalFiber_strictCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) (z : UpperHalfPlane) :
    {w | w ∈ signedCriticalFiber k f ξ positive ∧
      criticalHeight k (halfPlaneFunction f) z < criticalHeight k (halfPlaneFunction f) w}.Finite := by
  apply (goodPair_criticalCut_finite hk hg
    (criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos))).subset
  intro w hw
  exact ⟨hw.1.1,hw.2.le⟩

lemma goodPair_criticalHeight_injOn {k : ℝ} {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) :
    InjOn (fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w)
      {w : UpperHalfPlane | criticalMap k (halfPlaneFunction f) w = ξ} := by
  intro z hz w hw he
  exact hg.2.2 z w hz hw he

lemma criticalRank_injOn {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) (positive : Bool) :
    InjOn (criticalRank k f ξ positive) (signedCriticalFiber k f ξ positive) := by
  apply descendingRank_injOn
    ((goodPair_criticalHeight_injOn hg).mono (fun _ hz => hz.1))
  intro z _
  exact signedCriticalFiber_strictCut_finite hk hg positive z

lemma continuous_rank_f (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.1) :=
  continuous_fst.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))

lemma continuous_rank_z (k : ℝ) :
    Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.2) :=
  continuous_snd.comp (continuous_subtype_val.comp continuous_fst)

lemma isClosed_rankClosedRelation (k : ℝ) : IsClosed (rankClosedRelation k) := by
  have hG := (continuous_criticalMap k).comp ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  exact isClosed_eq hG hξ

lemma isOpen_rankOpenRelation (k : ℝ) (positive : Bool) :
    IsOpen (rankOpenRelation k positive) := by
  have hJ := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hVz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hVw := (continuous_criticalHeight k).comp ((continuous_rank_f k).prodMk continuous_snd)
  apply IsOpen.inter _ (isOpen_lt hVz hVw)
  cases positive
  · exact isOpen_lt hJ continuous_const
  · exact isOpen_lt continuous_const hJ

lemma rankRelation_finite {k : ℝ} (hk : 0 < k) (positive : Bool) (p : RankParameters k) :
    {w | (p,w) ∈ rankClosedRelation k ∩ rankOpenRelation k positive}.Finite := by
  convert signedCriticalFiber_strictCut_finite hk p.2 positive p.1.2 using 1
  ext w
  change (_ ∧ _ ∧ _) ↔ ((_ ∧ _) ∧ _)
  tauto

lemma measurable_criticalRank {k : ℝ} (hk : 0 < k) (positive : Bool) :
    Measurable (fun p : RankParameters k =>
      criticalRank k p.1.1.1 p.1.1.2 positive p.1.2) := by
  have hr := measurable_ncard_locally_closed_fiber
    (isClosed_rankClosedRelation k) (isOpen_rankOpenRelation k positive)
    (rankRelation_finite hk positive)
  convert hr using 1
  funext p
  unfold criticalRank descendingRank
  congr 1
  ext w
  change ((_ ∧ _) ∧ _) ↔ (_ ∧ _ ∧ _)
  tauto

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RankPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

instance rankParameters_standardBorel (k : ℝ) : StandardBorelSpace (RankParameters k) :=
  ((measurableSet_goodPairs k).preimage measurable_fst).standardBorel

lemma measurableSet_rankPairRelation {k : ℝ} (hk : 0 < k) :
    MeasurableSet {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2} := by
  have hGz := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hGw := (continuous_criticalMap k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hξ : Continuous (fun q : RankParameters k × UpperHalfPlane => q.1.1.1.2) :=
    continuous_snd.comp (continuous_fst.comp (continuous_subtype_val.comp continuous_fst))
  have hJz := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hJw := (continuous_jacobianExpression_upper k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  have hHz := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk (continuous_rank_z k))
  have hHw := (continuous_criticalHeight k).comp
    ((continuous_rank_f k).prodMk continuous_snd)
  let replace : RankParameters k × UpperHalfPlane → RankParameters k :=
    fun q => ⟨(q.1.1.1,q.2),q.1.2⟩
  have hr : Measurable replace :=
    ((measurable_fst.comp (measurable_subtype_coe.comp measurable_fst)).prodMk
      measurable_snd).subtype_mk
  have hm1 := (measurable_criticalRank hk false).comp hr
  have hm2 : Measurable (fun q : RankParameters k × UpperHalfPlane =>
      criticalRank k q.1.1.1.1 q.1.1.1.2 true q.1.1.2) :=
    (measurable_criticalRank hk true).comp measurable_fst
  exact ((isClosed_eq hGz hξ).measurableSet.inter (isOpen_lt continuous_const hJz).measurableSet).inter
    (((isClosed_eq hGw hξ).measurableSet.inter (isOpen_lt hJw continuous_const).measurableSet).inter
      ((measurableSet_eq_fun hm1 hm2).inter (isOpen_lt hHz hHw).measurableSet))

lemma rankPairRelation_unique {k : ℝ} (hk : 0 < k) {p : RankParameters k}
    {v w : UpperHalfPlane} (hv : RankPairRelation k p v) (hw : RankPairRelation k p w) : v = w := by
  exact criticalRank_injOn hk p.2 false hv.2.1 hw.2.1 (hv.2.2.1.trans hw.2.2.1.symm)

lemma measurableSet_rankPairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (rankPairingDomain k) := by
  let R := {q : RankParameters k × UpperHalfPlane | RankPairRelation k q.1 q.2}
  have hR : MeasurableSet R := measurableSet_rankPairRelation hk
  let : StandardBorelSpace R := hR.standardBorel
  let π : R → RankParameters k := fun q => q.1.1
  have hπ : MeasurableEmbedding π :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro q r he
      apply Subtype.ext
      apply Prod.ext he
      have hr : RankPairRelation k q.1.1 r.1.2 := by
        change q.val.fst = r.val.fst at he
        rw [he]
        exact r.property
      exact rankPairRelation_unique hk q.2 hr)
  have he : π '' univ = rankPairingDomain k := by
    ext p
    constructor
    · rintro ⟨q,_,rfl⟩
      exact ⟨q.1.2,q.2⟩
    · rintro ⟨w,hw⟩
      exact ⟨⟨(p,w),hw⟩,mem_univ _,rfl⟩
  rw [← he]
  exact hπ.measurableSet_image.mpr MeasurableSet.univ

lemma availableRankPartner_spec (k : ℝ) (p : AvailableRankPair k) :
    RankPairRelation k p.1 (availableRankPartner k p) := Classical.choose_spec p.2

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology
namespace StrictInverseFirstPower
noncomputable section

lemma goodPair_rebase_iff (k : ℝ) (f : DiskFamily) (ξ : ℂ) (z : UpperHalfPlane) :
    GoodPair k (rebase f z,targetRebase f z ξ) ↔ GoodPair k (f,ξ) := by
  refine ⟨fun hg => ?_,fun hg => goodPair_rebase hg z⟩
  refine ⟨?_,?_,?_⟩
  · apply (compactPotential_iff _ _).mpr
    intro r hr
    have hc := (compactPotential_iff _ _).mp hg.1
      (r / heightRebaseScale k f z) (div_pos hr (heightRebaseScale_pos k f z))
    convert hc.image (affineUpperHomeomorph z).continuous using 1
    ext w
    constructor
    · intro hw
      let v := (affineUpperHomeomorph z).symm w
      have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
      refine ⟨v,?_,hv⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _
      rw [reciprocalPotential_rebase,hv]
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mpr hw
    · rintro ⟨v,hv,rfl⟩
      change reciprocalPotential k (rebase f z,targetRebase f z ξ) v ≤ _ at hv
      rw [reciprocalPotential_rebase] at hv
      exact (div_le_div_iff_of_pos_right (heightRebaseScale_pos k f z)).mp hv
  · intro w hw
    let v := (affineUpperHomeomorph z).symm w
    have hv : affineProduct z v = w := (affineUpperHomeomorph z).apply_symm_apply w
    have hc : criticalMap k (halfPlaneFunction (rebase f z)) v = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z v ξ).mpr (hv.symm ▸ hw)
    simpa only [jacobianExpression_rebase,← coe_affineProduct,hv] using hg.2.1 v hc
  · intro u v hu hv he
    let a := (affineUpperHomeomorph z).symm u
    let b := (affineUpperHomeomorph z).symm v
    have ha : affineProduct z a = u := (affineUpperHomeomorph z).apply_symm_apply u
    have hb : affineProduct z b = v := (affineUpperHomeomorph z).apply_symm_apply v
    have hca : criticalMap k (halfPlaneFunction (rebase f z)) a = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z a ξ).mpr (ha.symm ▸ hu)
    have hcb : criticalMap k (halfPlaneFunction (rebase f z)) b = targetRebase f z ξ :=
      (criticalMap_rebase_eq_iff k f z b ξ).mpr (hb.symm ▸ hv)
    have hab := hg.2.2 a b hca hcb (by
      rw [criticalHeight_rebase,criticalHeight_rebase,ha,hb,he])
    calc u = affineProduct z a := ha.symm
         _ = affineProduct z b := congrArg (affineProduct z) hab
         _ = v := hb

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportPairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma availableSource_injective {k : ℝ} : Function.Injective (availableSource k) := by
  intro p q he
  have hf : p.1.1.1.1 = q.1.1.1.1 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.1) he
  have hz : p.1.1.2 = q.1.1.2 := congrArg (fun q : DiskFamily × UpperHalfPlane => q.2) he
  have hp := (availableRankPartner_spec k p).1.1
  have hq := (availableRankPartner_spec k q).1.1
  have hξ : p.1.1.1.2 = q.1.1.1.2 := by
    rw [← hp,← hq,hf,hz]
  apply Subtype.ext
  apply Subtype.ext
  exact Prod.ext (Prod.ext hf hξ) hz

lemma measurable_availableSource (k : ℝ) : Measurable (availableSource k) := by
  exact (measurable_fst.comp (measurable_fst.comp (measurable_subtype_coe.comp measurable_subtype_coe))).prodMk
    (measurable_snd.comp (measurable_subtype_coe.comp measurable_subtype_coe))

lemma measurableEmbedding_availableSource {k : ℝ} (hk : 0 < k) :
    MeasurableEmbedding (availableSource k) := by
  let : StandardBorelSpace (AvailableRankPair k) := (measurableSet_rankPairingDomain hk).standardBorel
  exact (measurable_availableSource k).measurableEmbedding availableSource_injective

lemma measurableSet_sourcePairingDomain {k : ℝ} (hk : 0 < k) :
    MeasurableSet (sourcePairingDomain k) := (measurableEmbedding_availableSource hk).measurableSet_range

lemma sourcePairingDomain_iff (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    (f,z) ∈ sourcePairingDomain k ↔
      ∃ hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z),
        (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) ∈ rankPairingDomain k := by
  constructor
  · rintro ⟨p,hp⟩
    have hf : p.1.1.1.1 = f := congrArg Prod.fst hp
    have hz : p.1.1.2 = z := congrArg Prod.snd hp
    have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
      rw [← (availableRankPartner_spec k p).1.1,hf,hz]
    have hg : GoodPair k (f,criticalMap k (halfPlaneFunction f) z) := by
      rw [← hξ,← hf]
      exact p.1.2
    refine ⟨hg,?_⟩
    have he : (⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩ : RankParameters k) = p.1 := by
      apply Subtype.ext
      exact (Prod.ext (Prod.ext hf hξ) hz).symm
    rw [he]
    exact p.2
  · rintro ⟨hg,hp⟩
    exact ⟨⟨⟨((f,criticalMap k (halfPlaneFunction f) z),z),hg⟩,hp⟩,rfl⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PairingCovariance
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma sourcePairingDomain_rebase_iff (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) :
    (rebase f t,w) ∈ sourcePairingDomain k ↔ (f,affineProduct t w) ∈ sourcePairingDomain k := by
  rw [sourcePairingDomain_iff,sourcePairingDomain_iff,criticalMap_rebase]
  constructor
  · rintro ⟨hg',hp⟩
    have hg := (goodPair_rebase_iff k f _ t).mp hg'
    exact ⟨hg,(rankPairingDomain_rebase_iff hg t w).mp hp⟩
  · rintro ⟨hg,hp⟩
    exact ⟨goodPair_rebase hg t,(rankPairingDomain_rebase_iff hg t w).mpr hp⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.AreaTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory Filter Function
open scoped ENNReal Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_jacobianPart (k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => jacobianPart k p.1 positive p.2) := by
  cases positive
  · exact (continuous_jacobianExpression_upper k).neg.max continuous_const
  · exact (continuous_jacobianExpression_upper k).max continuous_const

lemma continuous_sourceMassDensity (β k : ℝ) (positive : Bool) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => sourceMassDensity β k p.1 positive p.2) := by
  exact ENNReal.continuous_ofReal.comp ((((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul continuous_halfPlaneQ.norm).mul
      (continuous_jacobianPart k positive))

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LawDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma spatialWeight_eq (β : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    spatialWeight β f z = ENNReal.ofReal (z.im^(β-1)) * (‖halfPlaneQ f z‖₊ : ℝ≥0∞) := by
  rw [spatialWeight,ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _)]
  simp [enorm_eq_nnnorm]

lemma law_spatialWeight (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (z : UpperHalfPlane)
    {φ : DiskFamily → ℝ≥0∞} (hφ : Measurable φ) :
    (∫⁻ f, spatialWeight β f z * φ (rebase f z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f, φ f ∂(μ : Measure DiskFamily) := by
  simp only [spatialWeight_eq,mul_assoc]
  have hm : Measurable (fun f => (‖halfPlaneQ f z‖₊ : ℝ≥0∞) * φ (rebase f z)) :=
    (measurable_Qnorm_fixed z).coe_nnreal_ennreal.mul (hφ.comp (measurable_rebase_fixed z))
  rw [lintegral_const_mul (μ := (μ : Measure DiskFamily)) (ENNReal.ofReal (z.im^(β-1))) hm,
    hlaw z φ hφ,← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg z.im_pos.le _),← Real.rpow_add z.im_pos]
  congr 1
  rw [show β-1+-β = -(1:ℝ) by ring,Real.rpow_neg_one]

lemma spatialWeight_jacobianPart (β k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    spatialWeight β f z * ENNReal.ofReal (jacobianPart k f positive z) =
      sourceMassDensity β k f positive z := by
  rw [spatialWeight,sourceMassDensity,
    ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg z.im_pos.le _) (norm_nonneg _))]

lemma jacobianPart_rebase (k : ℝ) (f : DiskFamily) (t w : UpperHalfPlane) (positive : Bool) :
    jacobianPart k (rebase f t) positive w = jacobianPart k f positive (affineProduct t w) := by
  simp only [jacobianPart,jacobianExpression_rebase,coe_affineProduct]

lemma law_sourceMassDensity (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (z : UpperHalfPlane) :
    (∫⁻ f, sourceMassDensity β k f positive z * H (f,z) ∂(μ : Measure DiskFamily)) =
      ENNReal.ofReal (z.im⁻¹) * ∫⁻ f,
        ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
        ∂(μ : Measure DiskFamily) := by
  let φ : DiskFamily → ℝ≥0∞ := fun f =>
    ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) * H (f,UpperHalfPlane.I)
  have hφ : Measurable φ :=
    ((continuous_jacobianPart k positive).measurable.comp
      (measurable_id.prodMk measurable_const)).ennreal_ofReal.mul
      (hH.comp (measurable_id.prodMk measurable_const))
  have he (f : DiskFamily) : sourceMassDensity β k f positive z * H (f,z) =
      spatialWeight β f z * φ (rebase f z) := by
    rw [← spatialWeight_jacobianPart,hcov]
    simp only [φ,jacobianPart_rebase,affineProduct_I,mul_assoc]
  simp_rw [he]
  exact law_spatialWeight μ β hlaw z hφ

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportBasic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma coe_upperArea_preserving : MeasurePreserving UpperHalfPlane.coe upperArea
    (volume.restrict {z : ℂ | 0 < z.im}) := by
  refine ⟨UpperHalfPlane.measurable_coe,?_⟩
  rw [UpperHalfPlane.measurableEmbedding_coe.map_comap,UpperHalfPlane.range_coe]

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.NormalizedTargets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma upperArea_ne_zero : upperArea ≠ 0 := by
  intro h
  have he := coe_upperArea_preserving.map_eq
  rw [h,Measure.map_zero] at he
  have hh : (volume : Measure ℂ) {z | 0 < z.im} = 0 := by
    have hc := congrArg (fun ν : Measure ℂ => ν univ) he
    simpa using hc.symm
  have hp : 0 < (volume : Measure ℂ) {z | 0 < z.im} :=
    isOpen_halfPlane.measure_pos volume ⟨I,by simp⟩
  exact hp.ne' hh

lemma expected_source_mass (μ : ProbabilityMeasure DiskFamily) (β k : ℝ)
    (hlaw : AffineProbabilityLaw μ β) (positive : Bool)
    {H : DiskFamily × UpperHalfPlane → ℝ≥0∞} (hH : Measurable H)
    (hcov : ∀ f z, H (f,z) = H (rebase f z,UpperHalfPlane.I)) (A : Set UpperHalfPlane) :
    (∫⁻ f, ∫⁻ z in A, sourceMassDensity β k f positive z * H (f,z) ∂upperArea
      ∂(μ : Measure DiskFamily)) =
      (∫⁻ z in A, ENNReal.ofReal (z.im⁻¹) ∂upperArea) *
        ∫⁻ f, ENNReal.ofReal (jacobianPart k f positive UpperHalfPlane.I) *
          H (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily) := by
  have hm := (continuous_sourceMassDensity β k positive).measurable.mul hH
  rw [lintegral_lintegral_swap hm.aemeasurable]
  simp_rw [law_sourceMassDensity μ β k hlaw positive hH hcov]
  exact lintegral_mul_const _ (UpperHalfPlane.continuous_im.inv₀
    (fun z => z.im_ne_zero)).measurable.ennreal_ofReal

lemma measurable_badSourceTest {k : ℝ} (hk : 0 < k) : Measurable (badSourceTest k) :=
  measurable_const.indicator (measurableSet_sourcePairingDomain hk).compl

lemma badSourceTest_rebase (k : ℝ) (f : DiskFamily) (z : UpperHalfPlane) :
    badSourceTest k (f,z) = badSourceTest k (rebase f z,UpperHalfPlane.I) := by
  classical
  have he := sourcePairingDomain_rebase_iff k f z UpperHalfPlane.I
  rw [affineProduct_I] at he
  simp only [badSourceTest,Set.indicator,mem_compl_iff,he]

lemma affine_law_base_good (μ : ProbabilityMeasure DiskFamily) (β : ℝ) (hβ : 0 ≤ β)
    (hlaw : AffineProbabilityLaw μ β) :
    (∫⁻ f, ENNReal.ofReal (jacobianPart ((β+2)/3) f true UpperHalfPlane.I) *
      badSourceTest ((β+2)/3) (f,UpperHalfPlane.I) ∂(μ : Measure DiskFamily)) = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hz : (∫⁻ f, ∫⁻ z, sourceMassDensity β k f true z * badSourceTest k (f,z)
      ∂upperArea ∂(μ : Measure DiskFamily)) = 0 := by
    apply lintegral_eq_zero_of_ae_eq_zero
    filter_upwards [affine_law_ae_good_pairs μ β hβ hlaw] with f hf
    exact good_targets_bad_source_mass_zero hk f hf
  have he := expected_source_mass μ β k hlaw true (measurable_badSourceTest hk)
    (badSourceTest_rebase k) univ
  simp only [Measure.restrict_univ] at he
  rw [he] at hz
  rcases mul_eq_zero.mp hz with ha | hb
  · have hm : Measurable (fun z : UpperHalfPlane=>ENNReal.ofReal (z.im⁻¹)) :=
      (UpperHalfPlane.continuous_im.inv₀ (fun z=>z.im_ne_zero)).measurable.ennreal_ofReal
    have hz0 := (lintegral_eq_zero_iff' hm.aemeasurable).mp ha
    let : NeZero upperArea := ⟨upperArea_ne_zero⟩
    obtain ⟨z,hz⟩ := hz0.exists
    exact False.elim ((ENNReal.ofReal_ne_zero_iff.mpr (inv_pos.mpr z.im_pos)) hz)
  · exact hb

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TransportLimit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma jacobianPart_nonneg (k : ℝ) (f : DiskFamily) (positive : Bool) (z : UpperHalfPlane) :
    0 ≤ jacobianPart k f positive z := le_max_right _ _

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.StrictTransport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma ae_bad_base_positive_zero_oai (μ : ProbabilityMeasure DiskFamily) (β : ℝ)
    (hβ : 0 ≤ β) (hlaw : AffineProbabilityLaw μ β) :
    ∀ᵐ f ∂(μ : Measure DiskFamily), (f,UpperHalfPlane.I)∉sourcePairingDomain ((β+2)/3) →
      jacobianPart ((β+2)/3) f true UpperHalfPlane.I = 0 := by
  let k := (β+2)/3
  have hk : 0 < k := by dsimp [k]; linarith
  have hm : Measurable (fun f : DiskFamily => ENNReal.ofReal (jacobianPart k f true UpperHalfPlane.I) *
      badSourceTest k (f,UpperHalfPlane.I)) :=
    (((continuous_jacobianPart k true).measurable.comp (measurable_id.prodMk measurable_const)).ennreal_ofReal).mul
      ((measurable_badSourceTest hk).comp (measurable_id.prodMk measurable_const))
  have hz := (lintegral_eq_zero_iff' hm.aemeasurable).mp (affine_law_base_good μ β hβ hlaw)
  filter_upwards [hz] with f hf
  intro hD
  have hDc : (f,UpperHalfPlane.I) ∈ (sourcePairingDomain k)ᶜ := hD
  simp only [badSourceTest,indicator_of_mem hDc,mul_one,Pi.zero_apply] at hf
  exact le_antisymm (ENNReal.ofReal_eq_zero.mp hf) (jacobianPart_nonneg k f true _)

end
end StrictInverseFirstPower

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.ae_bad_base_positive_zero_oai := @OAI.StrictInverseFirstPower.ae_bad_base_positive_zero_oai
