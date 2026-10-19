-- Prove2me | solution 1 for OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:20:38.052008+00:00
-- url     : https://prove2.me/submissions/f2e246f6-cbb2-49f7-a675-43c69d336d50

import Mathlib
import Definitions.Def_OAIQWSIFP000

section
-- module Solutions.OAIQW_StrictInverseFirstPower.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434
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

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma measurable_halfPlaneProjection : Measurable halfPlaneProjection :=
  UpperHalfPlane.measurableEmbedding_coe.measurable_invFun

lemma halfPlaneProjection_of_pos {z : ℂ} (hz : 0 < z.im) :
    halfPlaneProjection z = ⟨z, hz⟩ := halfPlaneProjection_coe ⟨z, hz⟩

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

lemma logPotential_differentiableAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : DifferentiableAt ℂ F z) (hne : F z ≠ ξ) :
    DifferentiableAt ℝ (logPotential k F ξ) z := by
  exact ((Complex.imCLM.differentiableAt).log hz.ne').const_mul k |>.sub
    (((hF.restrictScalars (𝕜 := ℝ)).sub_const ξ).norm ℝ (sub_ne_zero.mpr hne) |>.log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)))

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
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexGeometry
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

lemma maximaCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (maximaCut k f ξ h).Finite :=
  (goodPair_criticalCut_finite hk hg hh).subset (fun _ hz => hz.1)

lemma saddleCut_finite {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0 < h) : (saddleCut k f ξ h).Finite :=
  (goodPair_criticalCut_finite hk hg hh).subset (fun _ hz => hz.1)

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma logPotential_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) (v w : ℂ) :
    realHessian (logPotential k F ξ) z v w =
      -(k / z.im^2) * v.im * w.im -
        ((((deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2) * v) * w).re := by
  let r := fun t => deriv F t / (F t-ξ)
  have hdr : HasDerivAt r
      ((deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2) z := by
    exact (hF.deriv.differentiableAt.hasDerivAt).div
      (hF.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)
  have hy := ((hasDerivAt_const z.im k).div (hasDerivAt_id z.im) hz.ne')
  have h1 := (hy.comp_hasFDerivAt z (Complex.imCLM.hasFDerivAt (x := z))).mul_const w.im
  have h2 := (Complex.reCLM.hasFDerivAt (x := r z * w)).comp z
    (hdr.complexToReal_fderiv.mul_const w)
  have he : (fun t => fderiv ℝ (logPotential k F ξ) t w) =ᶠ[𝓝 z]
      (fun t => k / t.im * w.im - (r t*w).re) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz, hF.eventually_analyticAt,
      hF.continuousAt.eventually_ne hp] with t ht hFt hpt
    exact logPotential_fderiv_apply ht hFt.differentiableAt hpt w
  have hh := (h1.sub h2).congr_of_eventuallyEq he
  unfold realHessian
  rw [hh.fderiv]
  simp only [sub_apply, ContinuousLinearMap.comp_apply, smul_apply, smul_eq_mul,
    Complex.imCLM_apply, Complex.reCLM_apply, one_apply_eq_self, id_eq]
  ring_nf

lemma logPotential_hessian_trace {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    realHessian (logPotential k F ξ) z 1 1 + realHessian (logPotential k F ξ) z I I =
      -k / z.im^2 := by
  rw [logPotential_hessian hz hF hp, logPotential_hessian hz hF hp]
  simp only [one_im, I_im, mul_zero, zero_sub, mul_one, Complex.mul_I_re, Complex.mul_I_im]
  ring

lemma critical_logarithmic_quotient_deriv {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    (deriv (deriv F) z * (F z-ξ) - deriv F z * deriv F z) / (F z-ξ)^2 =
      (k:ℂ) * ((k:ℂ) + logarithmicDerivative F z) / (z.im:ℂ)^2 := by
  rw [criticalMap_sub_image hg]
  unfold logarithmicDerivative
  field_simp [Complex.ofReal_ne_zero.mpr hk, Complex.ofReal_ne_zero.mpr hz.ne',hd]
  simp only [I_sq]
  ring

lemma logPotential_critical_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    realHessian (logPotential k F ξ) z 1 1 =
        k / z.im^2 * (-(k+(logarithmicDerivative F z).re)) ∧
    realHessian (logPotential k F ξ) z 1 I =
        k / z.im^2 * (logarithmicDerivative F z).im ∧
    realHessian (logPotential k F ξ) z I 1 =
        k / z.im^2 * (logarithmicDerivative F z).im ∧
    realHessian (logPotential k F ξ) z I I =
        k / z.im^2 * (k-1+(logarithmicDerivative F z).re) := by
  have hp : F z ≠ ξ := fun he => criticalMap_ne_image hk hz hd (hg.trans he.symm)
  have hq := critical_logarithmic_quotient_deriv hk hz hd hg
  repeat' apply And.intro
  all_goals rw [logPotential_hessian hz hF hp,hq]
  all_goals simp only [one_im, I_im, I_re, mul_zero, zero_sub, mul_one, Complex.div_ofReal_re, Complex.div_ofReal_im,
    ← Complex.ofReal_pow, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_re, Complex.add_im, zero_mul, add_zero, sub_zero]
  all_goals ring

lemma logPotential_hessian_det {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hk : k ≠ 0) (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hd : deriv F z ≠ 0)
    (hg : criticalMap k F z = ξ) :
    realHessian (logPotential k F ξ) z 1 1 * realHessian (logPotential k F ξ) z I I -
      realHessian (logPotential k F ξ) z 1 I * realHessian (logPotential k F ξ) z I 1 =
        -(k^4 / z.im^4) * jacobianExpression k F z := by
  obtain ⟨hxx,hxy,hyx,hyy⟩ := logPotential_critical_hessian hk hz hF hd hg
  rw [hxx,hxy,hyx,hyy]
  unfold jacobianExpression
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  field_simp
  ring

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology

open Set Filter Metric Complex MeasureTheory
open scoped Topology

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SquaredPotential
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

lemma squaredReciprocalPotential_contDiffAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) :
    ContDiffAt ℝ ⊤ (squaredReciprocalPotential k F ξ) z := by
  exact (((hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const).norm_sq ℝ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne hz.ne')

lemma squaredReciprocalPotential_eq_exp {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hp : F z ≠ ξ) :
    squaredReciprocalPotential k F ξ z = Real.exp (-2 * logPotential k F ξ z) := by
  have hn : 0 < ‖F z-ξ‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  unfold squaredReciprocalPotential logPotential
  rw [show -2*(k*Real.log z.im-Real.log ‖F z-ξ‖) =
      2*Real.log ‖F z-ξ‖ + Real.log z.im * (-2*k) by ring,
    Real.exp_add, ← Real.rpow_def_of_pos hz]
  congr 1
  rw [show 2*Real.log ‖F z-ξ‖ = Real.log (‖F z-ξ‖^2) by rw [Real.log_pow]; ring,
    Real.exp_log (sq_pos_of_pos hn)]

lemma logPotential_contDiffAt {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    ContDiffAt ℝ ⊤ (logPotential k F ξ) z := by
  exact (contDiffAt_const.mul (Complex.imCLM.contDiff.contDiffAt.log hz.ne')).sub
    ((((hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const).norm ℝ
      (sub_ne_zero.mpr hp)).log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp)))

lemma realHessian_exp {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    realHessian (fun t => Real.exp (u t)) z v w =
      Real.exp (u z) * (fderiv ℝ u z v * fderiv ℝ u z w + realHessian u z v w) := by
  have hdu := hu.differentiableAt (by norm_num)
  have huD : DifferentiableAt ℝ (fderiv ℝ u) z :=
    (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hw : DifferentiableAt ℝ (fun t => fderiv ℝ u t w) z :=
    huD.clm_apply (differentiableAt_const w)
  have he : (fun t => fderiv ℝ (fun s => Real.exp (u s)) t w) =ᶠ[𝓝 z]
      (fun t => Real.exp (u t) * fderiv ℝ u t w) := by
    filter_upwards [hu.eventually (by norm_num)] with t ht
    rw [ht.differentiableAt (by norm_num) |>.hasFDerivAt.exp |>.fderiv]
    rfl
  unfold realHessian
  rw [he.fderiv_eq]
  change (fderiv ℝ ((fun t => Real.exp (u t)) * (fun t => fderiv ℝ u t w)) z) v = _
  rw [(hdu.hasFDerivAt.exp.mul hw.hasFDerivAt).fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma squaredReciprocalPotential_hessian {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) (v w : ℂ) :
    realHessian (squaredReciprocalPotential k F ξ) z v w =
      squaredReciprocalPotential k F ξ z *
        (4 * fderiv ℝ (logPotential k F ξ) z v * fderiv ℝ (logPotential k F ξ) z w -
          2 * realHessian (logPotential k F ξ) z v w) := by
  have he : squaredReciprocalPotential k F ξ =ᶠ[𝓝 z]
      (fun t => Real.exp (-2 * logPotential k F ξ t)) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with t ht hpt
    exact squaredReciprocalPotential_eq_exp ht hpt
  have heH : realHessian (squaredReciprocalPotential k F ξ) z v w =
      realHessian (fun t => Real.exp (-2 * logPotential k F ξ t)) z v w := by
    unfold realHessian
    apply congrArg (fun L : ℂ →L[ℝ] ℝ => L v)
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [he.eventuallyEq_nhds] with t ht
    rw [ht.fderiv_eq]
  rw [heH,realHessian_exp ((contDiffAt_const.mul (logPotential_contDiffAt hz hF hp)).of_le (by norm_num)),
    ← squaredReciprocalPotential_eq_exp hz hp]
  have hd := logPotential_differentiableAt (k := k) hz hF.differentiableAt hp
  have hfirst : ∀ a : ℂ, fderiv ℝ (fun t => -2*logPotential k F ξ t) z a =
      -2*fderiv ℝ (logPotential k F ξ) z a := by
    intro a
    rw [(hd.hasFDerivAt.const_mul (-2)).fderiv]
    rfl
  have hsecond : realHessian (fun t => -2*logPotential k F ξ t) z v w =
      -2*realHessian (logPotential k F ξ) z v w := by
    have he' : (fun t => fderiv ℝ (fun s => -2*logPotential k F ξ s) t w) =ᶠ[𝓝 z]
        (fun t => -2 * fderiv ℝ (logPotential k F ξ) t w) := by
      filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.eventually_analyticAt,
        hF.continuousAt.eventually_ne hp] with t ht hFt hpt
      rw [((logPotential_differentiableAt ht hFt.differentiableAt hpt).hasFDerivAt.const_mul (-2)).fderiv]
      rfl
    unfold realHessian
    rw [he'.fderiv_eq]
    have hw := ((logPotential_contDiffAt (k := k) hz hF hp).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
    rw [(hw.clm_apply (differentiableAt_const w)).hasFDerivAt.const_mul (-2) |>.fderiv]
    rfl
  rw [hfirst,hfirst,hsecond]
  ring

lemma squaredReciprocalPotential_laplacian_pos_off_pole {k : ℝ} (hk : 0 < k)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z ≠ ξ) :
    0 < planeLaplacian (squaredReciprocalPotential k F ξ) z := by
  change 0 < realHessian _ z 1 1 + realHessian _ z I I
  rw [squaredReciprocalPotential_hessian hz hF hp,squaredReciprocalPotential_hessian hz hF hp]
  have hu : 0 < squaredReciprocalPotential k F ξ z := by
    rw [squaredReciprocalPotential_eq_exp hz hp]
    exact Real.exp_pos _
  have ht := logPotential_hessian_trace (k := k) hz hF hp
  have hs : 0 < k/z.im^2 := div_pos hk (sq_pos_of_pos hz)
  calc
    _ = squaredReciprocalPotential k F ξ z *
        (4 * (fderiv ℝ (logPotential k F ξ) z 1)^2 +
         4 * (fderiv ℝ (logPotential k F ξ) z I)^2 + 2*(k/z.im^2)) := by
      rw [show k/z.im^2 = -(realHessian (logPotential k F ξ) z 1 1 +
        realHessian (logPotential k F ξ) z I I) by rw [ht]; ring]
      ring
    _ > 0 := mul_pos hu (by positivity)

lemma realHessian_mul {u t : ℂ → ℝ} {z : ℂ}
    (hu : ContDiffAt ℝ 2 u z) (ht : ContDiffAt ℝ 2 t z) (v w : ℂ) :
    realHessian (fun a => u a * t a) z v w =
      realHessian u z v w * t z + fderiv ℝ u z w * fderiv ℝ t z v +
      fderiv ℝ u z v * fderiv ℝ t z w + u z * realHessian t z v w := by
  have hu1 := hu.differentiableAt (by norm_num)
  have ht1 := ht.differentiableAt (by norm_num)
  have hu2 := (hu.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have ht2 := (ht.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hwU := hu2.clm_apply (differentiableAt_const w)
  have hwT := ht2.clm_apply (differentiableAt_const w)
  have he : (fun a => fderiv ℝ (fun b => u b*t b) a w) =ᶠ[𝓝 z]
      (fun a => fderiv ℝ u a w * t a + u a * fderiv ℝ t a w) := by
    filter_upwards [hu.eventually (by norm_num),ht.eventually (by norm_num)] with a hUa hTa
    change fderiv ℝ (u*t) a w = _
    rw [((hUa.differentiableAt (by norm_num)).hasFDerivAt.mul
      (hTa.differentiableAt (by norm_num)).hasFDerivAt).fderiv]
    simp only [add_apply,smul_apply,smul_eq_mul]
    ring
  unfold realHessian
  rw [he.fderiv_eq]
  have hd := (hwU.hasFDerivAt.mul ht1.hasFDerivAt).add
    (hu1.hasFDerivAt.mul hwT.hasFDerivAt)
  change fderiv ℝ (((fun a => fderiv ℝ u a w) * t) +
    (u * (fun a => fderiv ℝ t a w))) z v = _
  rw [hd.fderiv]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma realHessian_norm_sq_at_zero {F : ℂ → ℂ} {z : ℂ} (hF : ContDiffAt ℝ 2 F z)
    (hzero : F z = 0) (v w : ℂ) :
    realHessian (fun a => ‖F a‖^2) z v w =
      2 * inner ℝ (fderiv ℝ F z v) (fderiv ℝ F z w) := by
  have hd := hF.differentiableAt (by norm_num)
  have hd2 := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hw := hd2.clm_apply (differentiableAt_const w)
  have he : (fun a => fderiv ℝ (fun b => ‖F b‖^2) a w) =ᶠ[𝓝 z]
      (fun a => 2 * inner ℝ (F a) (fderiv ℝ F a w)) := by
    filter_upwards [hF.eventually (by norm_num)] with a ha
    rw [(ha.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp
    ring
  unfold realHessian
  rw [he.fderiv_eq]
  rw [((hd.hasFDerivAt.inner ℝ hw.hasFDerivAt).const_mul 2).fderiv]
  simp [hzero]

lemma squaredReciprocalPotential_fderiv_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z = ξ) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z = 0 := by
  have hd := (hF.differentiableAt.restrictScalars (𝕜 := ℝ)).sub_const ξ
  have hy : DifferentiableAt ℝ (fun a : ℂ => a.im^(-2*k)) z :=
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (p := -2*k) hz.ne').differentiableAt
      (by norm_num : (2 : WithTop ℕ∞) ≠ 0)
  unfold squaredReciprocalPotential
  change fderiv ℝ ((fun a => ‖F a-ξ‖^2) * (fun a : ℂ => a.im^(-2*k))) z = 0
  rw [(hd.hasFDerivAt.norm_sq.mul hy.hasFDerivAt).fderiv]
  simp [hp]

lemma squaredReciprocalPotential_hessian_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0 < z.im) (hF : AnalyticAt ℂ F z) (hp : F z = ξ) (v w : ℂ) :
    realHessian (squaredReciprocalPotential k F ξ) z v w =
      2 * inner ℝ (deriv F z * v) (deriv F z * w) * z.im^(-2*k) := by
  have hd : ContDiffAt ℝ 2 (fun a => F a-ξ) z :=
    (hF.restrictScalars (𝕜 := ℝ)).contDiffAt.sub contDiffAt_const
  have hy : ContDiffAt ℝ 2 (fun a : ℂ => a.im^(-2*k)) z :=
    Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne hz.ne'
  have hzF : F z-ξ = 0 := sub_eq_zero.mpr hp
  have hdn : fderiv ℝ (fun a => ‖F a-ξ‖^2) z = 0 := by
    rw [(hd.differentiableAt (by norm_num)).hasFDerivAt.norm_sq.fderiv]
    simp [hp]
  unfold squaredReciprocalPotential
  rw [realHessian_mul (hd.norm_sq ℝ) hy,hdn]
  simp only [zero_apply,zero_mul,add_zero,hzF,norm_zero,zero_pow (by norm_num : 2 ≠ 0)]
  rw [realHessian_norm_sq_at_zero hd hzF]
  have he : ∀ a : ℂ, fderiv ℝ (fun t => F t-ξ) z a = deriv F z * a := by
    intro a
    rw [((hF.differentiableAt.hasDerivAt.sub_const ξ).complexToReal_fderiv).fderiv]
    simp [mul_comm]
  rw [he,he]

lemma squaredReciprocalPotential_laplacian_pos {k : ℝ} (hk : 0 < k)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0 < z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z ≠ 0) :
    0 < planeLaplacian (squaredReciprocalPotential k F ξ) z := by
  by_cases hp : F z = ξ
  · change 0 < realHessian _ z 1 1 + realHessian _ z I I
    rw [squaredReciprocalPotential_hessian_pole hz hF hp,
      squaredReciprocalPotential_hessian_pole hz hF hp]
    rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
    have hpw := Real.rpow_pos_of_pos hz (-2*k)
    have hn : 0 < ‖deriv F z * 1‖^2 := by simp [hd]
    positivity
  · exact squaredReciprocalPotential_laplacian_pos_off_pole hk hz hF hp

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.QuadraticHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fderiv_apply_of_line {u : E → ℝ} {p d : E} {a : ℝ}
    (hu : DifferentiableAt ℝ u p)
    (ha : HasDerivAt (fun t : ℝ=>u (p+t•d)) a 0) : fderiv ℝ u p d=a := by
  have hl : HasDerivAt (fun t : ℝ=>p+t•d) d 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add p
  have hc := hu.hasFDerivAt.comp_hasDerivAt_of_eq (0:ℝ) hl (by simp)
  exact hc.unique ha

lemma derivative_homotopy_regular {g : E → F} {H : E →L[ℝ] F} {p : E}
    (hg : HasFDerivAt g H p) (hp : g p=0) {m : ℝ} (hm : 0 < m)
    (hH : ∀ d, m*‖d‖≤‖H d‖) :
    ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      (1-t)•g z+t•H (z-p)≠0 := by
  filter_upwards [hg.isLittleO.bound (show 0 < m/2 by positivity)] with z hz
  intro hzp t ht he
  have hd : 0<‖z-p‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzp)
  have herr : ‖g z-H (z-p)‖≤ m/2*‖z-p‖ := by simpa only [hp,sub_zero] using hz
  have hid : H (z-p) = -(1-t)•(g z-H (z-p)) := by
    have hh : (1-t)•(g z-H (z-p))+H (z-p) = (1-t)•g z+t•H (z-p) := by
      simp only [smul_sub,sub_smul,one_smul]
      abel
    rw [he] at hh
    exact (eq_neg_of_add_eq_zero_right hh).trans (by simp only [neg_smul])
  have hcoef : |-(1-t)|≤1 := by rw [abs_neg,abs_of_nonneg (by linarith [ht.2])]; linarith [ht.1]
  have hn : ‖H (z-p)‖≤ m/2*‖z-p‖ := calc
    ‖H (z-p)‖ = |-(1-t)| * ‖g z-H (z-p)‖ := by
      calc
        ‖H (z-p)‖ = ‖-(1-t)•(g z-H (z-p))‖ := congrArg norm hid
        _ = _ := by rw [norm_smul,Real.norm_eq_abs]
    _ ≤ 1*‖g z-H (z-p)‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ ≤ m/2*‖z-p‖ := by simpa using herr
  have := hH (z-p)
  nlinarith

lemma quadraticFamily_contDiff {A B C : ℝ → ℝ} {n : WithTop ℕ∞}
    (hA : ContDiff ℝ n A) (hB : ContDiff ℝ n B) (hC : ContDiff ℝ n C) (p : ℂ) :
    ContDiff ℝ n (quadraticFamily A B C p) := by
  have hr : ContDiff ℝ n (fun q : ℝ × ℂ => (q.2-p).re) :=
    Complex.reCLM.contDiff.comp (contDiff_snd.sub contDiff_const)
  have hi : ContDiff ℝ n (fun q : ℝ × ℂ => (q.2-p).im) :=
    Complex.imCLM.contDiff.comp (contDiff_snd.sub contDiff_const)
  exact ((((hA.comp contDiff_fst).mul (hr.pow 2)).add
    (((contDiff_const.mul (hB.comp contDiff_fst)).mul hr).mul hi)).add
    ((hC.comp contDiff_fst).mul (hi.pow 2))).div_const 2

lemma quadraticFamily_dx {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ (quadraticFamily A B C p) q) :
    fderiv ℝ (quadraticFamily A B C p) q (0,1) =
      A q.1*(q.2-p).re+B q.1*(q.2-p).im := by
  apply fderiv_apply_of_line hu
  have he : (fun t : ℝ=>quadraticFamily A B C p (q+t•(0,1))) =
      (fun t : ℝ=>(A q.1*((q.2-p).re+t)^2+
        2*B q.1*((q.2-p).re+t)*(q.2-p).im+C q.1*(q.2-p).im^2)/2) := by
    funext t
    simp [quadraticFamily,quadratic,Complex.sub_re,Complex.sub_im]
    ring
  rw [he]
  convert (((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).re)).pow 2).const_mul (A q.1)).add
    ((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).re)).const_mul (2*B q.1)).mul_const ((q.2-p).im))).add_const
      (C q.1*(q.2-p).im^2) |>.div_const 2 using 1 <;> (first | rfl | (simp only [id_eq]; ring))

lemma quadraticFamily_dy {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ (quadraticFamily A B C p) q) :
    fderiv ℝ (quadraticFamily A B C p) q (0,Complex.I) =
      B q.1*(q.2-p).re+C q.1*(q.2-p).im := by
  apply fderiv_apply_of_line hu
  have he : (fun t : ℝ=>quadraticFamily A B C p (q+t•(0,Complex.I))) =
      (fun t : ℝ=>(A q.1*(q.2-p).re^2+
        2*B q.1*(q.2-p).re*((q.2-p).im+t)+C q.1*((q.2-p).im+t)^2)/2) := by
    funext t
    simp [quadraticFamily,quadratic,Complex.sub_re,Complex.sub_im]
    ring
  rw [he]
  convert (((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).im)).const_mul
    (2*B q.1*(q.2-p).re)).const_add (A q.1*(q.2-p).re^2)).add
    ((((hasDerivAt_id (0:ℝ)).const_add ((q.2-p).im)).pow 2).const_mul (C q.1))).div_const 2 using 1 <;> (first | rfl | (simp only [id_eq]; ring))

lemma quadraticFamily_regular {A B C : ℝ → ℝ} {p : ℂ} {q : ℝ × ℂ}
    (hu : ContDiffAt ℝ 1 (quadraticFamily A B C p) q)
    (hD : A q.1*C q.1-(B q.1)^2≠0) (hp : q.2≠p) :
    ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt (quadraticFamily A B C p) L q ∧
      (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := by
  refine ⟨_,hu.hasStrictFDerivAt one_ne_zero,?_⟩
  rw [quadraticFamily_dx (hu.differentiableAt one_ne_zero),
    quadraticFamily_dy (hu.differentiableAt one_ne_zero)]
  by_contra hn
  obtain ⟨hx,hy⟩ := not_or.mp hn
  simp only [not_not] at hx hy
  have hxr : (q.2-p).re=0 := by
    apply (mul_eq_zero.mp (show (A q.1*C q.1-(B q.1)^2)*(q.2-p).re=0 by
      linear_combination C q.1 * hx - B q.1 * hy)).resolve_left hD
  have hyr : (q.2-p).im=0 := by
    apply (mul_eq_zero.mp (show (A q.1*C q.1-(B q.1)^2)*(q.2-p).im=0 by
      linear_combination A q.1 * hy - B q.1 * hx)).resolve_left hD
  exact hp (sub_eq_zero.mp (Complex.ext (by simpa using hxr) (by simpa using hyr)))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HessianLocal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma complex_real_decomposition (z : ℂ) : z.re • (1:ℂ)+z.im • Complex.I=z := by
  apply Complex.ext <;> simp

lemma realCLM_apply (L : ℂ →L[ℝ] ℝ) (z : ℂ) :
    L z=z.re*L 1+z.im*L Complex.I := by
  conv_lhs => rw [← complex_real_decomposition z]
  simp only [map_add,map_smul,smul_eq_mul]

lemma realCLM_eq_zero {L : ℂ →L[ℝ] ℝ} (hx : L 1=0) (hy : L Complex.I=0) : L=0 := by
  ext z
  simp [realCLM_apply L z,hx,hy]

lemma hessianCLM_apply (a b c : ℝ) (z w : ℂ) :
    hessianCLM a b c z w=(a*z.re+b*z.im)*w.re+(b*z.re+c*z.im)*w.im := by
  simp [hessianCLM]
  ring

lemma hessianCLM_injective {a b c : ℝ} (hD : a*c-b^2≠0) : Injective (hessianCLM a b c) := by
  apply (hessianCLM a b c).toLinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  change hessianCLM a b c z=0 at hz
  have hx := congrArg (fun L : ℂ →L[ℝ] ℝ =>L 1) hz
  have hy := congrArg (fun L : ℂ →L[ℝ] ℝ =>L Complex.I) hz
  simp only [hessianCLM_apply,Complex.one_re,Complex.one_im,Complex.I_re,Complex.I_im,
    mul_one,mul_zero,zero_add,add_zero,zero_apply] at hx hy
  have hxr : z.re=0 := (mul_eq_zero.mp (show (a*c-b^2)*z.re=0 by linear_combination c*hx-b*hy)).resolve_left hD
  have hyr : z.im=0 := (mul_eq_zero.mp (show (a*c-b^2)*z.im=0 by linear_combination a*hy-b*hx)).resolve_left hD
  exact Complex.ext (by simpa using hxr) (by simpa using hyr)

lemma injectiveCLM_lower_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {L : E →L[ℝ] F} (hL : Injective L) : ∃ m : ℝ, 0 < m ∧ ∀ z, m*‖z‖≤‖L z‖ := by
  obtain ⟨K,hK,hBound⟩ := L.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.mpr hL)
  have hKr : (0:ℝ)<K := hK
  refine ⟨(K:ℝ)⁻¹,inv_pos.mpr hKr,fun z=>?_⟩
  have h := ZeroHomClass.bound_of_antilipschitz L hBound z
  rw [inv_mul_le_iff₀ hKr]
  exact h

lemma hessianCLM_of_second {u : ℂ → ℝ} {p : ℂ} (hu : ContDiffAt ℝ 2 u p) :
    fderiv ℝ (fderiv ℝ u) p =
      hessianCLM (fderiv ℝ (fderiv ℝ u) p 1 1)
        (fderiv ℝ (fderiv ℝ u) p 1 Complex.I)
        (fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I) := by
  let L := fderiv ℝ (fderiv ℝ u) p
  have hsym := (hu.isSymmSndFDerivAt (by norm_num)).eq 1 Complex.I
  change L 1 Complex.I=L Complex.I 1 at hsym
  ext z w
  rw [hessianCLM_apply,realCLM_apply (L z) w]
  have he : L z=z.re•L 1+z.im•L Complex.I := by
    conv_lhs => rw [← complex_real_decomposition z]
    simp only [map_add,map_smul]
  rw [he]
  simp only [add_apply,smul_apply,smul_eq_mul]
  rw [← hsym]
  ring

lemma quadratic_contDiff (a b c : ℝ) : ContDiff ℝ ⊤ (quadratic a b c) := by
  have hr := Complex.reCLM.contDiff (n := (⊤ : WithTop ℕ∞))
  have hi := Complex.imCLM.contDiff (n := (⊤ : WithTop ℕ∞))
  exact (((contDiff_const.mul (hr.pow 2)).add (((contDiff_const.mul hr).mul hi))).add
    (contDiff_const.mul (hi.pow 2))).div_const 2

lemma quadratic_fderiv (a b c : ℝ) (z : ℂ) :
    fderiv ℝ (quadratic a b c) z=hessianCLM a b c z := by
  have hr := quadraticFamily_dx (A:=fun _=>a) (B:=fun _=>b) (C:=fun _=>c) (p:=0)
    (q:=(0,z)) ((quadraticFamily_contDiff contDiff_const contDiff_const contDiff_const 0).differentiable (by norm_num : (1 : WithTop ℕ∞)≠0) (0,z))
  have hi := quadraticFamily_dy (A:=fun _=>a) (B:=fun _=>b) (C:=fun _=>c) (p:=0)
    (q:=(0,z)) ((quadraticFamily_contDiff contDiff_const contDiff_const contDiff_const 0).differentiable (by norm_num : (1 : WithTop ℕ∞)≠0) (0,z))
  have he : quadraticFamily (fun _=>a) (fun _=>b) (fun _=>c) 0 = quadratic a b c ∘ Prod.snd := by
    funext q; simp [quadraticFamily]
  have hf : HasFDerivAt (quadratic a b c ∘ Prod.snd)
      ((fderiv ℝ (quadratic a b c) z).comp (ContinuousLinearMap.snd ℝ ℝ ℂ)) ((0:ℝ),z) :=
    ((quadratic_contDiff a b c).differentiable (by simp) z).hasFDerivAt.comp ((0:ℝ),z)
      (hasFDerivAt_snd (𝕜 := ℝ) (p := ((0:ℝ),z)))
  rw [he,hf.fderiv] at hr hi
  simp only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.coe_snd',sub_zero] at hr hi
  ext w
  rw [realCLM_apply _ w,hr,hi,hessianCLM_apply]
  ring

lemma affinePotential_contDiffAt {u v : ℂ → ℝ} {q : ℝ × ℂ}
    (hu : ContDiffAt ℝ 1 u q.2) (hv : ContDiffAt ℝ 1 v q.2) :
    ContDiffAt ℝ 1 (affinePotential u v) q := by
  exact (((contDiffAt_const.sub contDiffAt_fst).mul (hu.comp q contDiffAt_snd)).add
    (contDiffAt_fst.mul (hv.comp q contDiffAt_snd)))

lemma affinePotential_spatial {u v : ℂ → ℝ} {q : ℝ × ℂ}
    (hu : DifferentiableAt ℝ u q.2) (hv : DifferentiableAt ℝ v q.2) (d : ℂ) :
    fderiv ℝ (affinePotential u v) q (0,d)=
      (1-q.1)*fderiv ℝ u q.2 d+q.1*fderiv ℝ v q.2 d := by
  have hU := hu.hasFDerivAt.comp q hasFDerivAt_snd
  have hV := hv.hasFDerivAt.comp q hasFDerivAt_snd
  have hT := hasFDerivAt_fst (𝕜 := ℝ) (p := q)
  have hd := ((hasFDerivAt_const (1:ℝ) q).sub hT).mul hU |>.add (hT.mul hV)
  change fderiv ℝ (((fun _ : ℝ × ℂ => (1:ℝ))-Prod.fst) * (u ∘ Prod.snd) +
    (Prod.fst * (v ∘ Prod.snd))) q (0,d) = _
  rw [hd.fderiv]
  simp

lemma local_quadratic_homotopy_regular {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p) (hp : fderiv ℝ u p=0)
    (hD : (fderiv ℝ (fderiv ℝ u) p 1 1)*
      (fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I)-
      (fderiv ℝ (fderiv ℝ u) p 1 Complex.I)^2≠0) :
    let a := fderiv ℝ (fderiv ℝ u) p 1 1
    let b := fderiv ℝ (fderiv ℝ u) p 1 Complex.I
    let c := fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I
    ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ,
        HasStrictFDerivAt (affinePotential u (fun w=>quadratic a b c (w-p))) L (t,z) ∧
          (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := by
  dsimp only
  let a := fderiv ℝ (fderiv ℝ u) p 1 1
  let b := fderiv ℝ (fderiv ℝ u) p 1 Complex.I
  let c := fderiv ℝ (fderiv ℝ u) p Complex.I Complex.I
  obtain ⟨m,hm,hH⟩ := injectiveCLM_lower_bound (hessianCLM_injective hD)
  have hg : HasFDerivAt (fderiv ℝ u) (hessianCLM a b c) p := by
    rw [← hessianCLM_of_second hu]
    exact (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero |>.hasFDerivAt
  have hreg := derivative_homotopy_regular hg hp hm hH
  have hQ : ContDiff ℝ 1 (fun w=>quadratic a b c (w-p)) :=
    (quadratic_contDiff a b c).of_le (by simp) |>.comp (contDiff_id.sub contDiff_const)
  have hQd (z : ℂ) : fderiv ℝ (fun w=>quadratic a b c (w-p)) z=hessianCLM a b c (z-p) := by
    have he := ((quadratic_contDiff a b c).differentiable (by simp) (z-p)).hasFDerivAt.comp z
      ((hasFDerivAt_id z).sub_const p)
    change fderiv ℝ (quadratic a b c ∘ fun x => id x-p) z = _
    rw [he.fderiv,quadratic_fderiv]
    ext d; simp
  filter_upwards [hreg,(hu.of_le (by norm_num : (1 : WithTop ℕ∞)≤2)).eventually (by norm_num)] with z hz hzu
  intro hzp t ht
  have hd := affinePotential_contDiffAt hzu hQ.contDiffAt (q := (t,z))
  refine ⟨_,hd.hasStrictFDerivAt one_ne_zero,?_⟩
  rw [affinePotential_spatial (hzu.differentiableAt one_ne_zero) (hQ.differentiable one_ne_zero z),
    affinePotential_spatial (hzu.differentiableAt one_ne_zero) (hQ.differentiable one_ne_zero z),hQd]
  by_contra hn
  obtain ⟨hx,hy⟩ := not_or.mp hn
  simp only [not_not] at hx hy
  apply hz hzp t ht
  exact realCLM_eq_zero hx hy

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridLink
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid

lemma linkIndex_rotate (a b c d e f : Bool) : linkIndex a b c d e f = linkIndex b c d e f a := by
  unfold linkIndex
  ring

lemma regular_link_xpos {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hx : 2*e < gx) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  have hb₀ : b₀ = false := by cases b₀ <;> simp_all [signBound]; linarith
  have hb₃ : b₃ = true := by cases b₃ <;> simp_all [signBound]; linarith
  subst b₀; subst b₃
  cases b₁ <;> cases b₂ <;> cases b₄ <;> cases b₅ <;>
    norm_num [linkIndex,bit,signBound] at * <;> linarith

lemma regular_link_xneg {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hx : gx < -2*e) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  rw [linkIndex_rotate,linkIndex_rotate,linkIndex_rotate]
  apply regular_link_xpos (gx := -gx) (gy := -gy) (by linarith) he h₃
  · simpa only [sub_eq_add_neg] using h₄
  · exact h₅
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂

lemma linkIndex_reverse (a b c d e f : Bool) : linkIndex a b c d e f = linkIndex c b a f e d := by
  unfold linkIndex
  ring

lemma regular_link {gx gy e : ℝ} {b₀ b₁ b₂ b₃ b₄ b₅ : Bool}
    (hreg : 2*e < |gx| ∨ 2*e < |gy|) (he : 0 ≤ e)
    (h₀ : signBound b₀ gx e) (h₁ : signBound b₁ (gx+gy) e)
    (h₂ : signBound b₂ gy e) (h₃ : signBound b₃ (-gx) e)
    (h₄ : signBound b₄ (-gx-gy) e) (h₅ : signBound b₅ (-gy) e) :
    linkIndex b₀ b₁ b₂ b₃ b₄ b₅ = 0 := by
  have hbase : ∀ {x y : ℝ} {a b c d e' f : Bool}, 2*e < |x| →
      signBound a x e → signBound b (x+y) e → signBound c y e →
      signBound d (-x) e → signBound e' (-x-y) e → signBound f (-y) e →
      linkIndex a b c d e' f = 0 := by
    intro x y a b c d e' f hx ha hb hc hd he' hf
    rcases lt_abs.mp hx with hp | hn
    · exact regular_link_xpos hp he ha hb hc hd he' hf
    · exact regular_link_xneg (by linarith) he ha hb hc hd he' hf
  rcases hreg with hx | hy
  · exact hbase hx h₀ h₁ h₂ h₃ h₄ h₅
  · rw [linkIndex_reverse]
    exact hbase hy h₂ (by simpa [add_comm] using h₁) h₀ h₅
      (by convert h₄ using 1; ring) h₃

end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.TriangularIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

variable {V L : Type*} [LinearOrder L]

lemma rankBit_complement {r : V → L} (hr : Function.Injective r) {a b : V} (hab : a ≠ b) :
    rankBit r a b + rankBit r b a = 1 := by
  have hne := hr.ne hab
  rcases lt_or_gt_of_ne hne with h | h <;> simp [rankBit,h,not_lt_of_gt h]

lemma topBit_sum {r : V → L} (hr : Function.Injective r) {a b c : V}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    topBit r a b c + topBit r b c a + topBit r c a b = 1 := by
  have hab' := hr.ne hab
  have hbc' := hr.ne hbc
  have hac' := hr.ne hac
  rcases lt_or_gt_of_ne hab' with h₁ | h₁ <;>
    rcases lt_or_gt_of_ne hbc' with h₂ | h₂ <;>
    rcases lt_or_gt_of_ne hac' with h₃ | h₃ <;>
    simp_all [topBit,rankBit,not_lt_of_gt] <;> order

variable [AddCommGroup V]

lemma ne_self_add_of_ne_zero (a : V) {b : V} (hb : b ≠ 0) : a ≠ a+b := by
  intro h
  exact hb (add_left_cancel (show a+b=a+0 by simpa using h.symm))

lemma lowerTop_sum {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    lowerTop₀ r x y v + lowerTop₁ r x y v + lowerTop₂ r x y v = 1 := by
  apply topBit_sum hr
  · exact ne_self_add_of_ne_zero v hx
  · exact ne_self_add_of_ne_zero (v+x) hy
  · simpa only [add_assoc,ne_eq,left_eq_add] using hd

lemma upperTop_sum {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    upperTop₀ r x y v + upperTop₁ r x y v + upperTop₂ r x y v = 1 := by
  apply topBit_sum hr
  · exact ne_self_add_of_ne_zero v hy
  · simpa only [add_right_comm] using ne_self_add_of_ne_zero (v+y) hx
  · simpa only [add_assoc,ne_eq,left_eq_add] using hd

lemma meshIndex_eq_linkIndex (r : V → L) (x y v : V) :
    meshIndex r x y v = linkIndex
      (decide (r (v+x) < r v)) (decide (r (v+x+y) < r v))
      (decide (r (v+y) < r v)) (decide (r (v-x) < r v))
      (decide (r (v-(x+y)) < r v)) (decide (r (v-y) < r v)) := by
  have ha : v-(x+y)+x = v-y := by abel
  have hc : v-y+x+y = v+x := by abel
  have hd : v-(x+y)+y = v-x := by abel
  simp only [meshIndex,lowerTop₀,lowerTop₁,lowerTop₂,upperTop₀,upperTop₁,upperTop₂,
    topBit,edgeFlag,sub_add_cancel,ha,hc,hd,linkIndex,rankBit,bit,decide_eq_true_eq,add_assoc]
  ring

lemma meshIndex_eq_divergence {r : V → L} (hr : Function.Injective r) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    meshIndex r x y v =
      (edgeFlag r x (v-x)-edgeFlag r x v) +
      (edgeFlag r y (v-y)-edgeFlag r y v) +
      (edgeFlag r (x+y) (v-(x+y))-edgeFlag r (x+y) v) +
      (lowerTop₁ r x y (v-x)-lowerTop₁ r x y v) +
      (lowerTop₂ r x y (v-(x+y))-lowerTop₂ r x y v) +
      (upperTop₁ r x y (v-y)-upperTop₁ r x y v) +
      (upperTop₂ r x y (v-(x+y))-upperTop₂ r x y v) := by
  have hlow := lowerTop_sum hr hx hy hd v
  have hup := upperTop_sum hr hx hy hd v
  have h₁ : edgeFlag r x (v-x) + rankBit r (v-x) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-x by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hx))
  have h₂ : edgeFlag r y (v-y) + rankBit r (v-y) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-y by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hy))
  have h₃ : edgeFlag r (x+y) (v-(x+y)) + rankBit r (v-(x+y)) v = 1 := by
    simpa only [edgeFlag,sub_add_cancel] using rankBit_complement hr (show v ≠ v-(x+y) by simpa only [sub_eq_add_neg] using ne_self_add_of_ne_zero v (neg_ne_zero.mpr hd))
  unfold meshIndex
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexConservation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [LinearOrder L]

lemma finite_support_shift {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    HasFiniteSupport (fun v => f (v-s)) :=
  hf.preimage (Equiv.subRight s).injective.injOn

lemma finite_support_discreteDivergence {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    HasFiniteSupport (discreteDivergence s f) := (finite_support_shift hf s).sub hf

lemma finsum_discreteDivergence {f : V → ℤ} (hf : HasFiniteSupport f) (s : V) :
    ∑ᶠ v, discreteDivergence s f v = 0 := by
  simp only [discreteDivergence]
  rw [finsum_sub_distrib (finite_support_shift hf s) hf]
  have he := finsum_comp_equiv (Equiv.subRight s) (f := f)
  exact sub_eq_zero.mpr he

lemma finite_rank_difference {r t : V → L} (hfin : {v | r v ≠ t v}.Finite) (a b : V) :
    HasFiniteSupport (fun v => rankBit r (v+a) (v+b)-rankBit t (v+a) (v+b)) := by
  apply ((hfin.preimage (Equiv.addRight a).injective.injOn).union
    (hfin.preimage (Equiv.addRight b).injective.injOn)).subset
  intro v hv
  by_contra hh
  have h := not_or.mp hh
  have ha : r (v+a)=t (v+a) := not_not.mp h.1
  have hb : r (v+b)=t (v+b) := not_not.mp h.2
  exact hv (by simp [rankBit,ha,hb])

lemma finite_top_difference {r t : V → L} (hfin : {v | r v ≠ t v}.Finite) (a b c : V) :
    HasFiniteSupport (fun v => topBit r (v+a) (v+b) (v+c)-topBit t (v+a) (v+b) (v+c)) := by
  apply (((hfin.preimage (Equiv.addRight a).injective.injOn).union
    (hfin.preimage (Equiv.addRight b).injective.injOn)).union
    (hfin.preimage (Equiv.addRight c).injective.injOn)).subset
  intro v hv
  by_contra hh
  have hh := not_or.mp hh
  have ha : r (v+a)=t (v+a) := not_not.mp (not_or.mp hh.1).1
  have hb : r (v+b)=t (v+b) := not_not.mp (not_or.mp hh.1).2
  have hc : r (v+c)=t (v+c) := not_not.mp hh.2
  exact hv (by simp [topBit,rankBit,ha,hb,hc])

lemma meshIndex_difference_decomposition {r t : V → L} (hr : Injective r) (ht : Injective t)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (v : V) :
    meshIndex r x y v - meshIndex t x y v =
      discreteDivergence x (fun w => edgeFlag r x w-edgeFlag t x w) v +
      discreteDivergence y (fun w => edgeFlag r y w-edgeFlag t y w) v +
      discreteDivergence (x+y) (fun w => edgeFlag r (x+y) w-edgeFlag t (x+y) w) v +
      discreteDivergence x (fun w => lowerTop₁ r x y w-lowerTop₁ t x y w) v +
      discreteDivergence (x+y) (fun w => lowerTop₂ r x y w-lowerTop₂ t x y w) v +
      discreteDivergence y (fun w => upperTop₁ r x y w-upperTop₁ t x y w) v +
      discreteDivergence (x+y) (fun w => upperTop₂ r x y w-upperTop₂ t x y w) v := by
  rw [meshIndex_eq_divergence hr hx hy hd,meshIndex_eq_divergence ht hx hy hd]
  unfold discreteDivergence
  ring

lemma meshIndex_change_finsum_zero {r t : V → L} (hr : Injective r) (ht : Injective t)
    (hfin : {v | r v ≠ t v}.Finite) {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) :
    ∑ᶠ v, (meshIndex r x y v-meshIndex t x y v) = 0 := by
  have hE (s : V) : HasFiniteSupport (fun v => edgeFlag r s v-edgeFlag t s v) := by
    simpa only [edgeFlag,add_zero] using finite_rank_difference hfin s 0
  have hA₁ : HasFiniteSupport (fun v => lowerTop₁ r x y v-lowerTop₁ t x y v) := by
    simpa only [lowerTop₁,add_zero,add_assoc] using finite_top_difference hfin x (x+y) 0
  have hA₂ : HasFiniteSupport (fun v => lowerTop₂ r x y v-lowerTop₂ t x y v) := by
    simpa only [lowerTop₂,add_zero,add_assoc] using finite_top_difference hfin (x+y) 0 x
  have hB₁ : HasFiniteSupport (fun v => upperTop₁ r x y v-upperTop₁ t x y v) := by
    simpa only [upperTop₁,add_zero,add_assoc] using finite_top_difference hfin y (x+y) 0
  have hB₂ : HasFiniteSupport (fun v => upperTop₂ r x y v-upperTop₂ t x y v) := by
    simpa only [upperTop₂,add_zero,add_assoc] using finite_top_difference hfin (x+y) 0 y
  have h₁ := finite_support_discreteDivergence (hE x) x
  have h₂ := finite_support_discreteDivergence (hE y) y
  have h₃ := finite_support_discreteDivergence (hE (x+y)) (x+y)
  have h₄ := finite_support_discreteDivergence hA₁ x
  have h₅ := finite_support_discreteDivergence hA₂ (x+y)
  have h₆ := finite_support_discreteDivergence hB₁ y
  have h₇ := finite_support_discreteDivergence hB₂ (x+y)
  simp_rw [meshIndex_difference_decomposition hr ht hx hy hd]
  have he₇ := finsum_add_distrib (((((h₁.add h₂).add h₃).add h₄).add h₅).add h₆) h₇
  have he₆ := finsum_add_distrib ((((h₁.add h₂).add h₃).add h₄).add h₅) h₆
  have he₅ := finsum_add_distrib (((h₁.add h₂).add h₃).add h₄) h₅
  have he₄ := finsum_add_distrib ((h₁.add h₂).add h₃) h₄
  have he₃ := finsum_add_distrib (h₁.add h₂) h₃
  have he₂ := finsum_add_distrib h₁ h₂
  simp only [Pi.add_apply] at he₇ he₆ he₅ he₄ he₃ he₂
  rw [he₇,he₆,he₅,he₄,he₃,he₂]
  simp only [finsum_discreteDivergence (hE x),finsum_discreteDivergence (hE y),
    finsum_discreteDivergence (hE (x+y)),finsum_discreteDivergence hA₁,
    finsum_discreteDivergence hA₂,finsum_discreteDivergence hB₁,
    finsum_discreteDivergence hB₂,add_zero]

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.HeightIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V]

omit [LinearOrder V] in
lemma heightRank_injective (u : V → ℝ) : Injective (heightRank u) := by
  intro a b h
  exact congrArg (fun t : Lex (ℝ × V) => (ofLex t).2) h

lemma heightRank_lt_imp_le {u : V → ℝ} {a b : V} (h : heightRank u a < heightRank u b) : u a ≤ u b := by
  rw [heightRank,heightRank,Prod.Lex.toLex_lt_toLex] at h
  rcases h with h | h
  · exact h.le
  · exact h.1.le

lemma heightRank_not_lt_imp_le {u : V → ℝ} {a b : V} (h : ¬ heightRank u a < heightRank u b) : u b ≤ u a := by
  by_contra hh
  apply h
  rw [heightRank,heightRank,Prod.Lex.toLex_lt_toLex]
  exact Or.inl (lt_of_not_ge hh)

lemma heightRank_signBound {u : V → ℝ} {a b : V} {g e : ℝ}
    (herror : |u a-u b-g| ≤ e) :
    signBound (decide (heightRank u a < heightRank u b)) g e := by
  by_cases h : heightRank u a < heightRank u b
  · have hh := heightRank_lt_imp_le h
    have he := (abs_le.mp herror).1
    simpa [signBound,h] using (show g ≤ e by linarith)
  · have hh := heightRank_not_lt_imp_le h
    have he := (abs_le.mp herror).2
    simpa [signBound,h] using (show -e ≤ g by linarith)

variable [AddCommGroup V]

lemma heightIndex_regular {u : V → ℝ} {x y v : V} {gx gy e : ℝ}
    (hreg : 2*e < |gx| ∨ 2*e < |gy|) (he : 0 ≤ e)
    (h₀ : |u (v+x)-u v-gx| ≤ e)
    (h₁ : |u (v+x+y)-u v-(gx+gy)| ≤ e)
    (h₂ : |u (v+y)-u v-gy| ≤ e)
    (h₃ : |u (v-x)-u v-(-gx)| ≤ e)
    (h₄ : |u (v-(x+y))-u v-(-gx-gy)| ≤ e)
    (h₅ : |u (v-y)-u v-(-gy)| ≤ e) : heightIndex u x y v = 0 := by
  rw [heightIndex,meshIndex_eq_linkIndex]
  exact regular_link hreg he (heightRank_signBound h₀) (heightRank_signBound h₁)
    (heightRank_signBound h₂) (heightRank_signBound h₃) (heightRank_signBound h₄)
    (heightRank_signBound h₅)

lemma heightIndex_finite_change {u w : V → ℝ} (hfin : {v | u v ≠ w v}.Finite)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) :
    ∑ᶠ v, (heightIndex u x y v-heightIndex w x y v) = 0 := by
  apply meshIndex_change_finsum_zero (heightRank_injective u) (heightRank_injective w) _ hx hy hd
  exact hfin.subset fun v hv he => hv (by simp only [heightRank,he])

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexLocality
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

lemma mem_meshStar_self (x y v : V) : v ∈ meshStar x y v := by simp [meshStar]

lemma meshStar_symm (x y v w : V) : w ∈ meshStar x y v ↔ v ∈ meshStar x y w := by
  simp only [meshStar,Finset.mem_insert,Finset.mem_singleton]
  constructor <;> intro h
  · rcases h with h|h|h|h|h|h|h <;> subst w <;>
      simp only [add_sub_cancel_right,add_sub_cancel_left,sub_add_cancel,add_assoc,
        sub_add_eq_add_sub,sub_sub,add_sub_assoc] <;> abel_nf <;> tauto
  · rcases h with h|h|h|h|h|h|h <;> subst v <;>
      simp only [add_sub_cancel_right,add_sub_cancel_left,sub_add_cancel,add_assoc,
        sub_add_eq_add_sub,sub_sub,add_sub_assoc] <;> abel_nf <;> tauto

lemma heightIndex_congr_star {u w : V → ℝ} {x y v : V}
    (h : ∀ a ∈ meshStar x y v, u a = w a) : heightIndex u x y v = heightIndex w x y v := by
  have hv := h v (by simp [meshStar])
  have h₀ := h (v+x) (by simp [meshStar])
  have h₁ := h (v+x+y) (by simp [meshStar])
  have h₂ := h (v+y) (by simp [meshStar])
  have h₃ := h (v-x) (by simp [meshStar])
  have h₄ := h (v-(x+y)) (by simp [meshStar])
  have h₅ := h (v-y) (by simp [meshStar])
  simp only [heightIndex,meshIndex_eq_linkIndex,heightRank,hv,h₀,h₁,h₂,h₃,h₄,h₅]
  rfl

lemma mem_meshBoundary (x y v : V) (S : Finset V) : v ∈ meshBoundary x y S ↔
    (∃ w ∈ meshStar x y v, w ∈ S) ∧ ¬ meshStar x y v ⊆ S := by
  simp only [meshBoundary,Finset.mem_filter,Finset.mem_biUnion]
  aesop (add simp [meshStar_symm])

lemma meshStar_subset_of_mem_not_boundary {x y v : V} {S : Finset V}
    (hv : v ∈ S) (hb : v ∉ meshBoundary x y S) : meshStar x y v ⊆ S := by
  by_contra hh
  exact hb ((mem_meshBoundary x y v S).mpr ⟨⟨v,mem_meshStar_self _ _ _,hv⟩,hh⟩)

lemma meshStar_disjoint_of_not_mem_not_boundary {x y v : V} {S : Finset V}
    (hv : v ∉ S) (hb : v ∉ meshBoundary x y S) : ∀ w ∈ meshStar x y v, w ∉ S := by
  intro w hw hs
  apply hb
  rw [mem_meshBoundary]
  exact ⟨⟨w,hw,hs⟩,fun h => hv (h (mem_meshStar_self _ _ _))⟩

lemma heightIndex_local_change {u w : V → ℝ} {x y : V}
    (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (S : Finset V)
    (hu : ∀ v ∈ meshBoundary x y S, heightIndex u x y v = 0)
    (hw : ∀ v ∈ meshBoundary x y S, heightIndex w x y v = 0)
    (hm : ∀ v ∈ meshBoundary x y S,
      heightIndex (fun a => if a ∈ S then w a else u a) x y v = 0) :
    ∑ v ∈ S, heightIndex u x y v = ∑ v ∈ S, heightIndex w x y v := by
  let q : V → ℝ := fun a => if a ∈ S then w a else u a
  have hf : {v | q v ≠ u v}.Finite := S.finite_toSet.subset (by
    intro v hv
    by_contra hh
    change v ∉ S at hh
    exact hv (by simp [q,hh]))
  have hout (v : V) (hv : v ∉ S) : heightIndex q x y v = heightIndex u x y v := by
    by_cases hb : v ∈ meshBoundary x y S
    · exact (hm v hb).trans (hu v hb).symm
    · apply heightIndex_congr_star
      intro a ha
      simp [q,meshStar_disjoint_of_not_mem_not_boundary hv hb a ha]
  have hin (v : V) (hv : v ∈ S) : heightIndex q x y v = heightIndex w x y v := by
    by_cases hb : v ∈ meshBoundary x y S
    · exact (hm v hb).trans (hw v hb).symm
    · apply heightIndex_congr_star
      intro a ha
      simp [q,meshStar_subset_of_mem_not_boundary hv hb ha]
  have he := heightIndex_finite_change hf hx hy hd
  rw [finsum_eq_sum_of_support_subset _ (s := S)] at he
  · have hsum : ∑ v ∈ S, (heightIndex q x y v-heightIndex u x y v) =
        (∑ v ∈ S, heightIndex w x y v)-(∑ v ∈ S, heightIndex u x y v) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      exact Finset.sum_congr rfl hin
    rw [hsum] at he
    exact (sub_eq_zero.mp he).symm
  · intro v hv
    by_contra hh
    change v ∉ S at hh
    exact hv (sub_eq_zero.mpr (hout v hh))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma ex_ne_zero : ex ≠ 0 := by decide
lemma ey_ne_zero : ey ≠ 0 := by decide
lemma ex_add_ey_ne_zero : ex+ey ≠ 0 := by decide

lemma bool_congr {P Q : Prop} [Decidable P] [Decidable Q] (h : P ↔ Q) : decide P = decide Q :=
  decide_eq_decide.mpr h

lemma separable_strict_bits (A B : ℝ) :
    bit (decide (A+B<0)) * (bit (decide (A<0))+bit (decide (B<0))-1) =
      bit (decide (A<0))*bit (decide (B<0)) := by
  by_cases ha : A<0 <;> by_cases hb : B<0 <;> simp [ha,hb,bit]
  · have h : A+B<0 := by linarith
    simp [h]
  · linarith

lemma separable_weak_bits (A B : ℝ) :
    bit (decide (A+B≤0)) * (bit (decide (A≤0))+bit (decide (B≤0))-1) =
      bit (decide (A≤0))*bit (decide (B≤0)) := by
  by_cases ha : A≤0 <;> by_cases hb : B≤0 <;> simp [ha,hb,bit]
  · have h : A+B≤0 := by linarith
    simp [h]
  · linarith

lemma separable_linkIndex (A B C D : ℝ) :
    linkIndex (decide (A<0)) (decide (A+B<0)) (decide (B<0))
      (decide (C≤0)) (decide (C+D≤0)) (decide (D≤0)) =
    (1-bit (decide (A<0))-bit (decide (C≤0))) *
      (1-bit (decide (B<0))-bit (decide (D≤0))) := by
  have h₁ := separable_strict_bits A B
  have h₂ := separable_weak_bits C D
  unfold linkIndex
  nlinarith only [h₁,h₂]

lemma heightRank_pos_x (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ex) < heightRank u v ↔ u (v+ex)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ex < v := not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ex)))
  simp [hn]

lemma heightRank_pos_y (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ey) < heightRank u v ↔ u (v+ey)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ey < v := not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ey)))
  simp [hn]

lemma heightRank_pos_xy (u : Lattice → ℝ) (v : Lattice) :
    heightRank u (v+ex+ey) < heightRank u v ↔ u (v+ex+ey)<u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hn : ¬ v+ex+ey < v := by
    rw [add_assoc]
    exact not_lt.mpr (le_of_lt (lt_add_of_pos_right v (by decide : 0 < ex+ey)))
  simp [hn]

lemma heightRank_neg_step (u : Lattice → ℝ) (v s : Lattice) (hs : 0 < s) :
    heightRank u (v-s) < heightRank u v ↔ u (v-s)≤u v := by
  simp only [heightRank,Prod.Lex.toLex_lt_toLex]
  have hneg : v-s < v := sub_lt_self _ hs
  simp only [hneg,and_true]
  exact le_iff_lt_or_eq.symm

lemma latticeHeight_index (p q : ℤ → ℝ) (v : Lattice) :
    heightIndex (latticeHeight p q) ex ey v =
      (1-bit (decide (p ((ofLex v).1+1)<p (ofLex v).1))-
        bit (decide (p ((ofLex v).1-1)≤p (ofLex v).1))) *
      (1-bit (decide (q ((ofLex v).2+1)<q (ofLex v).2))-
        bit (decide (q ((ofLex v).2-1)≤q (ofLex v).2))) := by
  rw [heightIndex,meshIndex_eq_linkIndex]
  have hx := bool_congr (heightRank_pos_x (latticeHeight p q) v)
  have hy := bool_congr (heightRank_pos_y (latticeHeight p q) v)
  have hxy := bool_congr (heightRank_pos_xy (latticeHeight p q) v)
  have hmx := bool_congr (heightRank_neg_step (latticeHeight p q) v ex (by decide))
  have hmy := bool_congr (heightRank_neg_step (latticeHeight p q) v ey (by decide))
  have hmxy := bool_congr (heightRank_neg_step (latticeHeight p q) v (ex+ey) (by decide))
  rw [hx,hy,hxy,hmx,hmy,hmxy]
  simp only [latticeHeight,ofLex_add,ofLex_sub,ex,ey,ofLex_toLex,Prod.fst_add,
    Prod.snd_add,Prod.fst_sub,Prod.snd_sub,add_zero,zero_add,sub_zero]
  have h := separable_linkIndex (p ((ofLex v).1+1)-p (ofLex v).1)
    (q ((ofLex v).2+1)-q (ofLex v).2) (p ((ofLex v).1-1)-p (ofLex v).1)
    (q ((ofLex v).2-1)-q (ofLex v).2)
  simp only [sub_lt_zero,sub_nonpos] at h
  simp only [add_lt_add_iff_left,add_lt_add_iff_right,add_le_add_iff_left,add_le_add_iff_right]
  convert h using 1
  congr 1 <;> apply bool_congr <;> constructor <;> intro ht <;> linarith

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.QuadraticLine
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma convex_line_index (t : ℝ) (i : ℤ) :
    lineIndex (fun j => ((j:ℝ)-t)^2) i = if i=⌈t-1/2⌉ then 1 else 0 := by
  have h₁ := Int.le_ceil (t-1/2)
  have h₂ := Int.ceil_lt_add_one (t-1/2)
  have right_iff : (((i+1:ℤ):ℝ)-t)^2 < ((i:ℝ)-t)^2 ↔ (i:ℝ)<t-1/2 := by
    push_cast
    constructor <;> intro h <;> nlinarith
  have left_iff : (((i-1:ℤ):ℝ)-t)^2 ≤ ((i:ℝ)-t)^2 ↔ t+1/2≤(i:ℝ) := by
    push_cast
    constructor <;> intro h <;> nlinarith
  unfold lineIndex
  simp only [right_iff,left_iff]
  rcases lt_trichotomy i ⌈t-1/2⌉ with hi|hi|hi
  · have hir : (i:ℝ) ≤ (⌈t-1/2⌉:ℝ)-1 := by exact_mod_cast (show i≤⌈t-1/2⌉-1 by omega)
    have hr : (i:ℝ)<t-1/2 := by linarith
    have hl : ¬ t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_lt hi]; norm_num
  · have hir : (i:ℝ) = (⌈t-1/2⌉:ℝ) := by exact_mod_cast hi
    have hr : ¬ (i:ℝ)<t-1/2 := by linarith
    have hl : ¬ t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_false]; simp [hi]
  · have hir : (⌈t-1/2⌉:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (show ⌈t-1/2⌉ + 1 ≤ i by omega)
    have hr : ¬ (i:ℝ)<t-1/2 := by linarith
    have hl : t+1/2≤(i:ℝ) := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_gt hi]; norm_num

lemma concave_line_index (t : ℝ) (i : ℤ) :
    lineIndex (fun j => -((j:ℝ)-t)^2) i = if i=⌊t+1/2⌋ then -1 else 0 := by
  have h₁ := Int.floor_le (t+1/2)
  have h₂ := Int.lt_floor_add_one (t+1/2)
  have right_iff : -(((i+1:ℤ):ℝ)-t)^2 < -((i:ℝ)-t)^2 ↔ t-1/2<(i:ℝ) := by
    push_cast
    constructor <;> intro h <;> nlinarith
  have left_iff : -(((i-1:ℤ):ℝ)-t)^2 ≤ -((i:ℝ)-t)^2 ↔ (i:ℝ)≤t+1/2 := by
    push_cast
    constructor <;> intro h <;> nlinarith
  unfold lineIndex
  simp only [right_iff,left_iff]
  rcases lt_trichotomy i ⌊t+1/2⌋ with hi|hi|hi
  · have hir : (i:ℝ) ≤ (⌊t+1/2⌋:ℝ)-1 := by exact_mod_cast (show i≤⌊t+1/2⌋-1 by omega)
    have hr : ¬ t-1/2<(i:ℝ) := by linarith
    have hl : (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_lt hi]; norm_num
  · have hir : (i:ℝ) = (⌊t+1/2⌋:ℝ) := by exact_mod_cast hi
    have hr : t-1/2<(i:ℝ) := by linarith
    have hl : (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true]; simp [hi]
  · have hir : (⌊t+1/2⌋:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast (show ⌊t+1/2⌋ + 1 ≤ i by omega)
    have hr : t-1/2<(i:ℝ) := by linarith
    have hl : ¬ (i:ℝ)≤t+1/2 := by linarith
    simp only [bit,decide_eq_true_eq,hr,hl,ite_true,ite_false,ne_of_gt hi]; norm_num

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V : Type*} [LinearOrder V] [AddCommGroup V]

lemma RegularStar.index_zero {u : V → ℝ} {x y v : V} (h : RegularStar u x y v) :
    heightIndex u x y v = 0 := by
  obtain ⟨gx,gy,e,he,hr,h₀,h₁,h₂,h₃,h₄,h₅⟩ := h
  apply heightIndex_regular (gx := gx) (gy := gy) (e := e) _ he.le h₀ h₁ h₂ h₃ h₄ h₅
  rcases hr with h|h <;> [left;right] <;> linarith

lemma star_error_perturb {A B a b g e : ℝ}
    (h : |A-B-g| ≤ e) (ha : |a-A|<e/2) (hb : |b-B|<e/2) : |a-b-g| ≤ 2*e := by
  have h₁ := (abs_lt.mp ha)
  have h₂ := (abs_lt.mp hb)
  have h₃ := (abs_le.mp h)
  rw [abs_le]
  constructor <;> linarith

lemma RegularStar.eventually_index_zero {P : Type*} [TopologicalSpace P]
    {u : P → V → ℝ} {t : P} {x y v : V}
    (hc : ∀ a ∈ meshStar x y v, ContinuousAt (fun s => u s a) t)
    (hr : RegularStar (u t) x y v) : ∀ᶠ s in 𝓝 t, heightIndex (u s) x y v = 0 := by
  obtain ⟨gx,gy,e,he,hr,h₀,h₁,h₂,h₃,h₄,h₅⟩ := hr
  have ht : ∀ᶠ s in 𝓝 t, ∀ a ∈ meshStar x y v, |u s a-u t a|<e/2 := by
    rw [Finset.eventually_all]
    intro a ha
    have hc' := (hc a ha).sub_const (u t a)
    have hm := hc'.abs.eventually (gt_mem_nhds (show |u t a-u t a|<e/2 by simpa using half_pos he))
    exact hm
  filter_upwards [ht] with s hs
  apply heightIndex_regular (gx := gx) (gy := gy) (e := 2*e) (by simpa only [← mul_assoc,show (2:ℝ)*2=4 by norm_num] using hr) (by linarith)
  · exact star_error_perturb h₀ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₁ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₂ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₃ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₄ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))
  · exact star_error_perturb h₅ (hs _ (by simp [meshStar])) (hs _ (by simp [meshStar]))

lemma local_index_homotopy {P : Type*} [TopologicalSpace P] [PreconnectedSpace P]
    (u : P → V → ℝ) (hc : ∀ a, Continuous (fun t => u t a))
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) (hd : x+y ≠ 0) (S : Finset V)
    (hr : ∀ t v, v ∈ meshBoundary x y S → RegularStar (u t) x y v) (a b : P) :
    ∑ v ∈ S, heightIndex (u a) x y v = ∑ v ∈ S, heightIndex (u b) x y v := by
  have hl : IsLocallyConstant (fun t => ∑ v ∈ S, heightIndex (u t) x y v) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro t
    have hm : ∀ᶠ s in 𝓝 t, ∀ v ∈ meshBoundary x y S,
        heightIndex (fun w => if w ∈ S then u s w else u t w) x y v = 0 := by
      rw [Finset.eventually_all]
      intro v hv
      apply RegularStar.eventually_index_zero
      · intro w _
        by_cases hw : w ∈ S
        · simpa only [ite_eq_left hw] using (hc w).continuousAt (x := t)
        · simpa only [ite_eq_right hw] using (continuousAt_const : ContinuousAt (fun _ : P => u t w) t)
      · simpa only [ite_self] using hr t v hv
    filter_upwards [hm] with s hs
    exact (heightIndex_local_change hx hy hd S
      (fun v hv => (hr t v hv).index_zero) (fun v hv => (hr s v hv).index_zero) hs).symm
  exact congrFun (hl.eq_const b) a

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothGridRegular
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma strict_direction_bound {u : E → ℝ} {L : E →L[ℝ] ℝ} {p : E}
    (h : HasStrictFDerivAt u L p) (d : E) {c : ℝ} (hc : 0<c) :
    ∀ᶠ q : ℝ × E in 𝓝 (0,p),
      |u (q.2+q.1•d)-u q.2-q.1*L d| ≤ c*|q.1| *‖d‖ := by
  have ht : Tendsto (fun q : ℝ × E => (q.2+q.1•d,q.2)) (𝓝 (0,p)) (𝓝 (p,p)) := by
    have hc : Continuous (fun q : ℝ × E => (q.2+q.1•d,q.2)) := by fun_prop
    simpa using hc.tendsto (0,p)
  filter_upwards [ht.eventually (h.isLittleO.bound hc)] with q hq
  simpa only [add_sub_cancel_left,map_smul,smul_eq_mul,
    norm_smul,Real.norm_eq_abs,mul_assoc] using hq

lemma remainder_enlarge {A s c d e : ℝ} (h : |A| ≤ c*|s| *d)
    (hs : 0<s) (hc : 0≤c) (hd : d≤2) (he : 2*c*s≤e) : |A|≤e := by
  rw [abs_of_pos hs] at h
  have := mul_le_mul_of_nonneg_left hd (mul_nonneg hc hs.le)
  nlinarith

lemma strict_regular_star {u : E → ℝ} {L : E →L[ℝ] ℝ} {p dx dy : E}
    (h : HasStrictFDerivAt u L p) (hx : ‖dx‖≤1) (hy : ‖dy‖≤1)
    (hr : L dx ≠ 0 ∨ L dy ≠ 0) :
    ∀ᶠ q : ℝ × E in 𝓝 (0,p), 0<q.1 → StarCertificate u q.2 dx dy q.1 := by
  let M := max |L dx| |L dy|
  have hM : 0<M := by
    rcases hr with h|h
    · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_left _ _)
    · exact lt_of_lt_of_le (abs_pos.mpr h) (le_max_right _ _)
  have hc : 0<M/32 := by positivity
  filter_upwards [strict_direction_bound h dx hc,strict_direction_bound h (dx+dy) hc,
    strict_direction_bound h dy hc,strict_direction_bound h (-dx) hc,
    strict_direction_bound h (-(dx+dy)) hc,strict_direction_bound h (-dy) hc] with q h₀ h₁ h₂ h₃ h₄ h₅
  intro hs
  have hnxy : ‖dx+dy‖≤2 := (norm_add_le _ _).trans (by linarith)
  have hb {A : ℝ} {d : E} (hd : ‖d‖≤2)
      (ha : |A|≤M/32*|q.1| *‖d‖) : |A| ≤ q.1*M/16 :=
    remainder_enlarge ha hs hc.le hd (by ring_nf; rfl)
  refine ⟨q.1*L dx,q.1*L dy,q.1*M/16,by positivity,?_,
    hb (d:=dx) (by linarith) h₀,?_,hb (d:=dy) (by linarith) h₂,?_,?_,?_⟩
  · simp only [abs_mul,abs_of_pos hs]
    rcases le_total |L dx| |L dy| with hl|hl
    · right
      dsimp [M]
      rw [max_eq_right hl]
      have := mul_pos hs (lt_of_lt_of_le hM (by dsimp [M]; rw [max_eq_right hl]))
      nlinarith
    · left
      dsimp [M]
      rw [max_eq_left hl]
      have := mul_pos hs (lt_of_lt_of_le hM (by dsimp [M]; rw [max_eq_left hl]))
      nlinarith
  · simpa only [map_add,mul_add] using hb hnxy h₁
  · simpa only [norm_neg,smul_neg,← sub_eq_add_neg,map_neg,mul_neg] using
      hb (d := -dx) (by simpa using hx.trans (by norm_num : (1:ℝ)≤2)) h₃
  · have ht := hb (d := -(dx+dy)) (by simpa only [norm_neg] using hnxy) h₄
    rw [smul_neg, ← sub_eq_add_neg,map_neg,map_add,mul_neg,mul_add] at ht
    convert ht using 1
    congr 2
    ring
  · simpa only [norm_neg,smul_neg,← sub_eq_add_neg,map_neg,mul_neg] using
      hb (d := -dy) (by simpa using hy.trans (by norm_num : (1:ℝ)≤2)) h₅

lemma compact_regular_star {u : E → ℝ} {dx dy : E} {K : Set E}
    (hK : IsCompact K) (hx : ‖dx‖≤1) (hy : ‖dy‖≤1)
    (h : ∀ p∈K, ∃ L : E →L[ℝ] ℝ,
      HasStrictFDerivAt u L p ∧ (L dx≠0 ∨ L dy≠0)) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ p∈K, 0<s → StarCertificate u p dx dy s := by
  apply hK.eventually_forall_of_forall_eventually
  intro p hp
  obtain ⟨L,hL,hr⟩ := h p hp
  exact strict_regular_star hL hx hy hr

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma meshPoint_add (o : ℂ) (s : ℝ) (v w : Lattice) :
    meshPoint o s (v+w) = meshPoint o s v+s•latticeCoord w := by
  simp [meshPoint,smul_add,add_assoc]
lemma meshPoint_sub (o : ℂ) (s : ℝ) (v w : Lattice) :
    meshPoint o s (v-w) = meshPoint o s v-s•latticeCoord w := by
  simp [meshPoint,smul_sub,add_sub_assoc]

lemma StarCertificate.toRegularStar {u : ℂ → ℝ} {o : ℂ} {s : ℝ} {v : Lattice}
    (h : StarCertificate u (meshPoint o s v) 1 Complex.I s) :
    RegularStar (u ∘ meshPoint o s) ex ey v := by
  simpa only [StarCertificate,RegularStar,Function.comp_apply,meshPoint_add,
    meshPoint_sub,map_add,latticeCoord_ex,latticeCoord_ey,smul_add,add_assoc] using h

lemma meshPoint_bounded_preimage {o : ℂ} {s : ℝ} (hs : s≠0) {K : Set ℂ}
    (hK : Bornology.IsBounded K) : (meshPoint o s ⁻¹' K).Finite := by
  obtain ⟨R,hR⟩ := hK.exists_norm_le
  obtain ⟨N,hN⟩ := exists_nat_gt ((R+‖o‖)/|s|)
  apply ((Set.finite_Icc (- (N:ℤ)) N).prod (Set.finite_Icc (-(N:ℤ)) N)).preimage
    ofLex.injective.injOn |>.subset
  intro v hv
  have hb : ‖s•latticeCoord v‖≤R+‖o‖ := by
    have h := norm_sub_le (meshPoint o s v) o
    have he : meshPoint o s v-o=s•latticeCoord v := by simp [meshPoint]
    rw [he] at h
    exact h.trans (add_le_add (hR _ hv) le_rfl)
  have hc : ‖latticeCoord v‖ < (N:ℝ) := by
    rw [norm_smul,Real.norm_eq_abs] at hb
    exact (le_div_iff₀ (abs_pos.mpr hs)).mpr (by simpa [mul_comm] using hb) |>.trans_lt hN
  have hx : |((ofLex v).1:ℝ)| < (N:ℝ) := by simpa only [latticeCoord_re] using (Complex.abs_re_le_norm _).trans_lt hc
  have hy : |((ofLex v).2:ℝ)| < (N:ℝ) := by simpa only [latticeCoord_im] using (Complex.abs_im_le_norm _).trans_lt hc
  constructor <;> constructor
  · exact_mod_cast (abs_lt.mp hx).1.le
  · exact_mod_cast (abs_lt.mp hx).2.le
  · exact_mod_cast (abs_lt.mp hy).1.le
  · exact_mod_cast (abs_lt.mp hy).2.le

lemma norm_latticeCoord_star {v w : Lattice} (hw : w ∈ meshStar ex ey v) :
    ‖latticeCoord w-latticeCoord v‖≤2 := by
  simp only [meshStar,Finset.mem_insert,Finset.mem_singleton] at hw
  rcases hw with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · simp
  · simp
  · simpa only [map_add,latticeCoord_ex,latticeCoord_ey,add_sub_cancel_left,
      show ∀ a : ℂ, a+1+Complex.I-a=1+Complex.I by intro a; ring] using
      (norm_add_le (1:ℂ) Complex.I).trans (by norm_num)
  · simp
  · simp
  · have he : latticeCoord (v-(ex+ey))-latticeCoord v=-(1+Complex.I) := by simp
    rw [he,norm_neg]
    exact (norm_add_le (1:ℂ) Complex.I).trans (by norm_num)
  · simp

lemma meshPoint_star_dist {o : ℂ} {s : ℝ} {v w : Lattice}
    (hw : w ∈ meshStar ex ey v) : dist (meshPoint o s w) (meshPoint o s v) ≤ 2*|s| := by
  rw [dist_eq_norm]
  have he : meshPoint o s w-meshPoint o s v=s•(latticeCoord w-latticeCoord v) := by
    simp [meshPoint,smul_sub]
  rw [he,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left (norm_latticeCoord_star hw) (abs_nonneg s)).trans_eq (mul_comm _ _)

lemma meshBoundary_annulus {o p : ℂ} {s r : ℝ} {S : Finset Lattice}
    (hS : ∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) {v : Lattice}
    (hv : v ∈ meshBoundary ex ey S) :
    r-2*|s| < dist (meshPoint o s v) p ∧ dist (meshPoint o s v) p ≤r+2*|s| := by
  obtain ⟨⟨w,hw,hwS⟩,hb⟩ := (mem_meshBoundary _ _ _ _).mp hv
  obtain ⟨a,ha,haS⟩ := Finset.not_subset.mp hb
  have hwi := (hS w).mp hwS
  have hao : r < dist (meshPoint o s a) p := lt_of_not_ge (fun he => haS ((hS a).mpr he))
  have h₁ := dist_triangle (meshPoint o s a) (meshPoint o s v) p
  have h₂ := dist_triangle (meshPoint o s v) (meshPoint o s w) p
  have ha' := meshPoint_star_dist (o:=o) (s:=s) ha
  have hw' := meshPoint_star_dist (o:=o) (s:=s) hw
  rw [dist_comm (meshPoint o s w) (meshPoint o s v)] at hw'
  constructor <;> linarith

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiagonalIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma lineIndex_mul_pos (p : ℤ → ℝ) (a : ℝ) (ha : 0<a) (i : ℤ) :
    lineIndex (fun j=>a*p j) i=lineIndex p i := by
  simp only [lineIndex,mul_lt_mul_iff_right₀ ha,mul_le_mul_iff_right₀ ha]

lemma signed_square_index (a t : ℝ) (ha : a≠0) (i : ℤ) :
    lineIndex (fun j=>a*((j:ℝ)-t)^2) i =
      if i=(if 0<a then ⌈t-1/2⌉ else ⌊t+1/2⌋) then (if 0<a then 1 else -1) else 0 := by
  rcases lt_or_gt_of_ne ha with ha|ha
  · have he : (fun j : ℤ=>a*((j:ℝ)-t)^2) = (fun j : ℤ =>(-a)*(-((j:ℝ)-t)^2)) := by funext j; ring
    rw [he,lineIndex_mul_pos _ _ (by linarith),concave_line_index]
    simp [not_lt.mpr ha.le]
  · rw [lineIndex_mul_pos _ _ ha,convex_line_index]
    simp [ha]

lemma signed_diagonal_index (a c x y : ℝ) (ha : a≠0) (hc : c≠0) (v : Lattice) :
    heightIndex (latticeHeight (fun i=>a*((i:ℝ)-x)^2) (fun j=>c*((j:ℝ)-y)^2)) ex ey v =
      if v=signedVertex a c x y then (if 0<a then 1 else -1)*(if 0<c then 1 else -1) else 0 := by
  rw [latticeHeight_index]
  change lineIndex (fun i=>a*((i:ℝ)-x)^2) (ofLex v).1 *
    lineIndex (fun j=>c*((j:ℝ)-y)^2) (ofLex v).2 = _
  rw [signed_square_index _ _ ha,signed_square_index _ _ hc]
  have hv : v=signedVertex a c x y ↔
      (ofLex v).1=(if 0<a then ⌈x-1/2⌉ else ⌊x+1/2⌋) ∧
      (ofLex v).2=(if 0<c then ⌈y-1/2⌉ else ⌊y+1/2⌋) := by
    change v=toLex _ ↔ _
    rw [← ofLex_inj]
    exact Prod.ext_iff
  simp only [hv]
  split_ifs <;> simp_all

lemma diagonal_sample {o p : ℂ} {s a c : ℝ} (hs : s≠0) :
    (fun v=>quadratic a 0 c (meshPoint o s v-p)) =
      latticeHeight (fun i=>(a*s^2/2)*((i:ℝ)-(p.re-o.re)/s)^2)
        (fun j=>(c*s^2/2)*((j:ℝ)-(p.im-o.im)/s)^2) := by
  funext v
  simp only [quadratic,latticeHeight,meshPoint,Complex.sub_re,Complex.sub_im,
    Complex.add_re,Complex.add_im,Complex.smul_re,Complex.smul_im,latticeCoord_re,latticeCoord_im,
    smul_eq_mul]
  field_simp
  ring

lemma nearest_integer_bound (t : ℝ) :
    |(⌈t-1/2⌉:ℝ)-t|≤1/2 ∧ |(⌊t+1/2⌋:ℝ)-t|≤1/2 := by
  have h₁ := Int.le_ceil (t-1/2)
  have h₂ := Int.ceil_lt_add_one (t-1/2)
  have h₃ := Int.floor_le (t+1/2)
  have h₄ := Int.lt_floor_add_one (t+1/2)
  constructor <;> rw [abs_le] <;> constructor <;> linarith

lemma signedVertex_close {o p : ℂ} {s : ℝ} (hs : 0<s) (a c : ℝ) :
    dist (meshPoint o s (signedVertex a c ((p.re-o.re)/s) ((p.im-o.im)/s))) p≤ s := by
  let v := signedVertex a c ((p.re-o.re)/s) ((p.im-o.im)/s)
  have hx : |((ofLex v).1:ℝ)-(p.re-o.re)/s|≤1/2 := by
    dsimp [v,signedVertex]
    split_ifs <;> [exact (nearest_integer_bound _).1; exact (nearest_integer_bound _).2]
  have hy : |((ofLex v).2:ℝ)-(p.im-o.im)/s|≤1/2 := by
    dsimp [v,signedVertex]
    split_ifs <;> [exact (nearest_integer_bound _).1; exact (nearest_integer_bound _).2]
  have hre : (meshPoint o s v-p).re=s*(((ofLex v).1:ℝ)-(p.re-o.re)/s) := by
    simp only [meshPoint,Complex.sub_re,Complex.add_re,Complex.smul_re,latticeCoord_re,smul_eq_mul]
    field_simp; ring
  have him : (meshPoint o s v-p).im=s*(((ofLex v).2:ℝ)-(p.im-o.im)/s) := by
    simp only [meshPoint,Complex.sub_im,Complex.add_im,Complex.smul_im,latticeCoord_im,smul_eq_mul]
    field_simp; ring
  calc
    dist (meshPoint o s v) p = ‖meshPoint o s v-p‖ := dist_eq_norm _ _
    _ ≤ |(meshPoint o s v-p).re|+|(meshPoint o s v-p).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ s := by
      rw [hre,him,abs_mul,abs_mul,abs_of_pos hs]
      nlinarith [mul_le_mul_of_nonneg_left hx hs.le,mul_le_mul_of_nonneg_left hy hs.le]

lemma diagonal_local_sum {a c : ℝ} (ha : a≠0) (hc : c≠0)
    {o p : ℂ} {s r : ℝ} (hs : 0<s) (hr : s≤r) {S : Finset Lattice}
    (hS : ∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) :
    ∑ v∈S, heightIndex (fun w=>quadratic a 0 c (meshPoint o s w-p)) ex ey v =
      (if 0<a then 1 else -1)*(if 0<c then 1 else -1) := by
  rw [diagonal_sample hs.ne']
  have has : a*s^2/2≠0 := div_ne_zero (mul_ne_zero ha (pow_ne_zero _ hs.ne')) (by norm_num)
  have hcs : c*s^2/2≠0 := div_ne_zero (mul_ne_zero hc (pow_ne_zero _ hs.ne')) (by norm_num)
  simp_rw [signed_diagonal_index _ _ _ _ has hcs]
  have hv : signedVertex (a*s^2/2) (c*s^2/2) ((p.re-o.re)/s) ((p.im-o.im)/s)∈S :=
    (hS _).mpr ((signedVertex_close hs _ _).trans hr)
  simp only [Finset.sum_ite_eq',hv,ite_true]
  have hA : 0<a*s^2/2 ↔ 0<a := by
    rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hs.ne')]
  have hC : 0<c*s^2/2 ↔ 0<c := by
    rw [div_pos_iff_of_pos_right (by norm_num),mul_pos_iff_of_pos_right (sq_pos_of_ne_zero hs.ne')]
  simp only [hA,hC]

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothIndexHomotopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma StarCertificate.joint {u : ℝ × ℂ → ℝ} {t s : ℝ} {p : ℂ}
    (h : StarCertificate u (t,p) (0,1) (0,Complex.I) s) :
    StarCertificate (fun z=>u (t,z)) p 1 Complex.I s := by
  simpa only [StarCertificate,Prod.smul_mk,smul_zero,Prod.mk_add_mk,Prod.mk_sub_mk,
    add_zero,sub_zero,zero_add] using h

lemma compact_indexAnnulus (p : ℂ) (r : ℝ) : IsCompact (indexAnnulus p r) :=
  (isCompact_closedBall p (3*r/2)).diff Metric.isOpen_ball

lemma mem_indexAnnulus {p z : ℂ} {r : ℝ} : z ∈ indexAnnulus p r ↔
    r/2 ≤ dist z p ∧ dist z p ≤ 3*r/2 := by
  simp only [indexAnnulus,Set.mem_sdiff,Metric.mem_closedBall,Metric.mem_ball,not_lt]
  exact and_comm

lemma smooth_local_index_homotopy (u : ℝ × ℂ → ℝ) (hc : ∀ z, Continuous (fun t : ℝ => u (t,z)))
    {p : ℂ} {r : ℝ} (hr : 0<r)
    (hd : ∀ q∈ (Icc (0:ℝ) 1) ×ˢ indexAnnulus p r,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt u L q ∧
        (L (0,1)≠0 ∨ L (0,Complex.I)≠0)) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) →
      ∑ v∈S, heightIndex (fun w=>u (0,meshPoint o s w)) ex ey v =
      ∑ v∈S, heightIndex (fun w=>u (1,meshPoint o s w)) ex ey v := by
  have hk : IsCompact ((Icc (0:ℝ) 1) ×ˢ indexAnnulus p r) := isCompact_Icc.prod (compact_indexAnnulus p r)
  have hn₀ : ‖((0,1):ℝ × ℂ)‖≤1 := by simp
  have hn₁ : ‖((0,Complex.I):ℝ × ℂ)‖≤1 := by simp
  have hcert := compact_regular_star hk hn₀ hn₁ hd
  filter_upwards [hcert,gt_mem_nhds (show (0:ℝ)<r/8 by positivity)] with s hs hsbound
  intro hspos o S hS
  let a : Icc (0:ℝ) 1 := ⟨0,by simp⟩
  let b : Icc (0:ℝ) 1 := ⟨1,by simp⟩
  apply local_index_homotopy (fun t : Icc (0:ℝ) 1 => fun v=>u (t,meshPoint o s v))
    (fun v=>(hc (meshPoint o s v)).comp continuous_subtype_val)
    ex_ne_zero ey_ne_zero ex_add_ey_ne_zero S ?_ a b
  intro t v hv
  have hb := meshBoundary_annulus hS hv
  rw [abs_of_pos hspos] at hb
  have hvK : meshPoint o s v∈ indexAnnulus p r := by
    rw [mem_indexAnnulus]
    constructor <;> linarith
  exact (StarCertificate.joint (hs ((t:ℝ),meshPoint o s v) ⟨t.property,hvK⟩ hspos)).toRegularStar

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.QuadraticIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma quadratic_family_index {A B C : ℝ → ℝ}
    (hA : ContDiff ℝ 1 A) (hB : ContDiff ℝ 1 B) (hC : ContDiff ℝ 1 C)
    (hD : ∀ t∈Icc (0:ℝ) 1, A t*C t-(B t)^2≠0) {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic (A 0) (B 0) (C 0) (meshPoint o s w-p)) ex ey v =
      ∑ v∈S, heightIndex (fun w=>quadratic (A 1) (B 1) (C 1) (meshPoint o s w-p)) ex ey v := by
  have hu := quadraticFamily_contDiff hA hB hC p
  apply smooth_local_index_homotopy (quadraticFamily A B C p)
    (fun z=>hu.continuous.comp (continuous_id.prodMk continuous_const)) hr
  intro q hq
  apply quadraticFamily_regular hu.contDiffAt (hD _ hq.1)
  intro he
  have h := (mem_indexAnnulus.mp hq.2).1
  rw [he,dist_self] at h
  linarith

lemma quadratic_shear_x {a b c : ℝ} (ha : 0<a) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  let B : ℝ → ℝ := fun t=>(1-t)*b
  let C : ℝ → ℝ := fun t=>(a*c-b^2+(B t)^2)/a
  have hB : ContDiff ℝ 1 B := (contDiff_const.sub contDiff_id).mul contDiff_const
  have hC : ContDiff ℝ 1 C := (contDiff_const.add (hB.pow 2)).div_const a
  have hdet (t : ℝ) : a*C t-(B t)^2=a*c-b^2 := by dsimp [C]; field_simp; ring
  have hh := quadratic_family_index (A:=fun _=>a) contDiff_const hB hC
    (fun t _=>by rw [hdet]; exact hD) (p:=p) hr
  have hC0 : C 0=c := by dsimp [C,B]; field_simp; ring
  have hC1 : C 1=(a*c-b^2)/a := by simp [C,B]
  have hd : (a*c-b^2)/a≠0 := div_ne_zero hD ha.ne'
  filter_upwards [hh,gt_mem_nhds hr] with s hs hsbound
  intro hspos o S hS
  have he := hs hspos o S hS
  simp only [B,sub_zero,one_mul,sub_self,zero_mul,hC0,hC1] at he
  rw [he,diagonal_local_sum ha.ne' hd hspos hsbound.le hS]
  have hsign : 0<(a*c-b^2)/a ↔ 0<a*c-b^2 := div_pos_iff_of_pos_right ha
  simp only [ha,ite_true,one_mul,hsign]

lemma quadratic_shear_y {a b c : ℝ} (hc : 0<c) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  let B : ℝ → ℝ := fun t=>(1-t)*b
  let A : ℝ → ℝ := fun t=>(a*c-b^2+(B t)^2)/c
  have hB : ContDiff ℝ 1 B := (contDiff_const.sub contDiff_id).mul contDiff_const
  have hA : ContDiff ℝ 1 A := (contDiff_const.add (hB.pow 2)).div_const c
  have hdet (t : ℝ) : A t*c-(B t)^2=a*c-b^2 := by dsimp [A]; field_simp; ring
  have hh := quadratic_family_index hA hB (C:=fun _=>c) contDiff_const
    (fun t _=>by rw [hdet]; exact hD) (p:=p) hr
  have hA0 : A 0=a := by dsimp [A,B]; field_simp; ring
  have hA1 : A 1=(a*c-b^2)/c := by simp [A,B]
  have hd : (a*c-b^2)/c≠0 := div_ne_zero hD hc.ne'
  filter_upwards [hh,gt_mem_nhds hr] with s hs hsbound
  intro hspos o S hS
  have he := hs hspos o S hS
  simp only [B,sub_zero,one_mul,sub_self,zero_mul,hA0,hA1] at he
  rw [he,diagonal_local_sum hd hc.ne' hspos hsbound.le hS]
  have hsign : 0<(a*c-b^2)/c ↔ 0<a*c-b^2 := div_pos_iff_of_pos_right hc
  simp only [hc,ite_true,mul_one,hsign]

lemma quadratic_local_index {a b c : ℝ} (htr : 0<a+c) (hD : a*c-b^2≠0)
    {p : ℂ} {r : ℝ} (hr : 0<r) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (fun w=>quadratic a b c (meshPoint o s w-p)) ex ey v =
        if 0<a*c-b^2 then 1 else -1 := by
  by_cases ha : 0<a
  · exact quadratic_shear_x ha hD hr
  · exact quadratic_shear_y (by linarith) hD hr

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothMorseIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma smooth_morse_local_index {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p) (hp : fderiv ℝ u p=0)
    (htr : 0<second u p 1 1+second u p Complex.I Complex.I)
    (hD : hessianDet u p≠0) :
    ∃ R>0, ∀ r∈Ioo (0:ℝ) R, ∀ᶠ s in 𝓝 (0:ℝ), 0<s →
      ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p ≤ r) →
      ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v = morseSign u p := by
  let a := second u p 1 1
  let b := second u p 1 Complex.I
  let c := second u p Complex.I Complex.I
  let Q : ℂ → ℝ := fun z=>quadratic a b c (z-p)
  have hg : ∀ᶠ z in 𝓝 p, z≠p → ∀ t∈Icc (0:ℝ) 1,
      ∃ L : (ℝ × ℂ) →L[ℝ] ℝ, HasStrictFDerivAt (affinePotential u Q) L (t,z) ∧
        (L (0,1)≠0 ∨ L (0,Complex.I)≠0) := local_quadratic_homotopy_regular hu hp hD
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hg
  refine ⟨R/2,by positivity,?_⟩
  intro r hr
  have ha := smooth_local_index_homotopy (affinePotential u Q)
    (fun z=>by
      dsimp only [affinePotential]
      exact ((continuous_const.sub continuous_id).mul continuous_const).add
        (continuous_id.mul continuous_const)) hr.1 (p:=p) (by
      intro q hq
      have hd := mem_indexAnnulus.mp hq.2
      have hqR : q.2∈Metric.ball p R := by rw [Metric.mem_ball]; linarith [hr.2]
      apply hball hqR
      · intro he; rw [he,dist_self] at hd; linarith [hr.1]
      · exact hq.1)
  have hb := quadratic_local_index htr hD (p:=p) hr.1
  filter_upwards [ha,hb] with s hs hs'
  intro hspos o S hS
  have he := hs hspos o S hS
  have he' := hs' hspos o S hS
  simp only [affinePotential,sub_zero,one_mul,zero_mul,add_zero,sub_self,zero_add] at he
  exact he.trans he'

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.MorseGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate
namespace StrictInverseFirstPower
noncomputable section

lemma realHessian_eq_second {u : ℂ → ℝ} {z : ℂ} (hu : ContDiffAt ℝ 2 u z) (v w : ℂ) :
    realHessian u z v w = Grid.second u z v w := by
  have hd := (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  unfold realHessian Grid.second
  rw [(hd.hasFDerivAt.clm_apply (hasFDerivAt_const w z)).fderiv]
  simp

lemma squaredReciprocalPotential_eq_sq {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) :
    squaredReciprocalPotential k F ξ z = (‖F z-ξ‖ / z.im^k)^2 := by
  unfold squaredReciprocalPotential
  rw [show -2*k=-(k*2) by ring,Real.rpow_neg hz.le,
    Real.rpow_mul hz.le k 2,Real.rpow_two,div_pow,div_eq_mul_inv]

lemma squaredReciprocalPotential_sublevel {k : ℝ} {F : ℂ → ℂ} {ξ : ℂ} {h : ℝ} (hh : 0<h) :
    {z : ℂ | 0<z.im ∧ squaredReciprocalPotential k F ξ z≤(1/h)^2} =
      potentialSuperlevel k F ξ h := by
  ext z
  change (0<z.im ∧ _≤_) ↔ (0<z.im ∧ ‖F z-ξ‖≤z.im^k/h)
  apply and_congr_right
  intro hz
  rw [squaredReciprocalPotential_eq_sq hz,
    sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos hz k).le) (one_div_nonneg.mpr hh.le),
    div_le_iff₀ (Real.rpow_pos_of_pos hz k)]
  ring_nf

lemma squaredReciprocalPotential_lt_sublevel {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ} {h : ℝ}
    (hz : 0<z.im) (hh : 0<h) :
    squaredReciprocalPotential k F ξ z<(1/h)^2 ↔ ‖F z-ξ‖<z.im^k/h := by
  rw [squaredReciprocalPotential_eq_sq hz,
    sq_lt_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_pos_of_pos hz k).le) (one_div_nonneg.mpr hh.le),
    div_lt_iff₀ (Real.rpow_pos_of_pos hz k)]
  ring_nf

lemma squaredReciprocalPotential_fderiv_off_pole {k : ℝ} {F : ℂ → ℂ} {ξ z : ℂ}
    (hz : 0<z.im) (hF : AnalyticAt ℂ F z) (hp : F z≠ξ) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z =
      (-2*squaredReciprocalPotential k F ξ z) • fderiv ℝ (logPotential k F ξ) z := by
  have he : squaredReciprocalPotential k F ξ =ᶠ[𝓝 z]
      (fun t=>Real.exp (-2*logPotential k F ξ t)) := by
    filter_upwards [isOpen_halfPlane.mem_nhds hz,hF.continuousAt.eventually_ne hp] with t ht hpt
    exact squaredReciprocalPotential_eq_exp ht hpt
  rw [he.fderiv_eq]
  rw [(((logPotential_differentiableAt hz hF.differentiableAt hp).hasFDerivAt.const_mul (-2)).exp).fderiv]
  rw [← squaredReciprocalPotential_eq_exp hz hp]
  ext v
  simp
  ring

lemma squaredReciprocalPotential_critical_iff {k : ℝ} (hk : k≠0)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z) :
    fderiv ℝ (squaredReciprocalPotential k F ξ) z=0 ↔
      F z=ξ ∨ criticalMap k F z=ξ := by
  by_cases hp : F z=ξ
  · simp [hp,squaredReciprocalPotential_fderiv_pole hz hF hp]
  rw [or_iff_right hp,squaredReciprocalPotential_fderiv_off_pole hz hF hp,
    smul_eq_zero,or_iff_right (mul_ne_zero (by norm_num) (by rw [squaredReciprocalPotential_eq_exp hz hp]; exact (Real.exp_pos _).ne'))]
  exact logPotential_critical_iff hk hz hF.differentiableAt hp

lemma squaredReciprocalPotential_hessian_det {k : ℝ} (hk : k≠0)
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z≠0) (hg : criticalMap k F z=ξ) :
    Grid.hessianDet (squaredReciprocalPotential k F ξ) z =
      -(4*(squaredReciprocalPotential k F ξ z)^2*(k^4/z.im^4))*jacobianExpression k F z := by
  have hp : F z≠ξ := fun he=>criticalMap_ne_image hk hz hd (hg.trans he.symm)
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz hF).of_le (show (2 : WithTop ℕ∞)≤⊤ by simp)
  have hl := logPotential_contDiffAt (k:=k) hz hF hp
  have hzD := (logPotential_critical_iff hk hz hF.differentiableAt hp).mpr hg
  have hsym : realHessian (logPotential k F ξ) z 1 I = realHessian (logPotential k F ξ) z I 1 := by
    rw [realHessian_eq_second (hl.of_le (by simp)),realHessian_eq_second (hl.of_le (by simp))]
    exact (hl.isSymmSndFDerivAt (by simp)).eq 1 I
  have hn := logPotential_hessian_det hk hz hF hd hg
  unfold Grid.hessianDet
  rw [← realHessian_eq_second hu,← realHessian_eq_second hu,← realHessian_eq_second hu]
  rw [squaredReciprocalPotential_hessian hz hF hp,squaredReciprocalPotential_hessian hz hF hp,
    squaredReciprocalPotential_hessian hz hF hp,hzD]
  simp only [zero_apply,mul_zero,zero_sub]
  rw [← hsym] at hn
  calc
    _ = 4*(squaredReciprocalPotential k F ξ z)^2 *
        (realHessian (logPotential k F ξ) z 1 1 * realHessian (logPotential k F ξ) z I I -
          realHessian (logPotential k F ξ) z 1 I * realHessian (logPotential k F ξ) z 1 I) := by ring
    _ = _ := by rw [hn]; ring

lemma squaredReciprocalPotential_hessian_det_pole {k : ℝ}
    {F : ℂ → ℂ} {ξ z : ℂ} (hz : 0<z.im) (hF : AnalyticAt ℂ F z)
    (hd : deriv F z≠0) (hp : F z=ξ) :
    0<Grid.hessianDet (squaredReciprocalPotential k F ξ) z := by
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz hF).of_le (show (2 : WithTop ℕ∞)≤⊤ by simp)
  unfold Grid.hessianDet
  rw [← realHessian_eq_second hu,← realHessian_eq_second hu,← realHessian_eq_second hu]
  rw [squaredReciprocalPotential_hessian_pole hz hF hp,squaredReciprocalPotential_hessian_pole hz hF hp,
    squaredReciprocalPotential_hessian_pole hz hF hp]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  have hi : inner ℝ (deriv F z*1) (deriv F z*I)=0 := by
    rw [real_inner_eq_re_inner ℂ, RCLike.inner_apply]
    simp only [mul_one]
    change (deriv F z * I * conj (deriv F z)).re = 0
    simp only [Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
      Complex.I_re,Complex.I_im,mul_zero,mul_one,zero_sub]
    ring
  rw [hi]
  simp only [mul_zero,zero_mul,zero_pow (by norm_num : 2≠0),sub_zero]
  have hn : 0<‖deriv F z*1‖^2 := by simp [hd]
  have hn' : 0<‖deriv F z*I‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero hd I_ne_zero))
  have hy := Real.rpow_pos_of_pos hz (-2*k)
  positivity

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.RegularLevels
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

lemma goodPair_lower_regular_cut {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    ∃ a : ℝ, 0<a ∧ a<h ∧ criticalCut k f ξ a=criticalCut k f ξ h ∧
      ∀ z∈criticalCut k f ξ h, a<criticalHeight k (halfPlaneFunction f) z := by
  classical
  have hfin := goodPair_criticalCut_finite hk hg (show 0<h/2 by positivity)
  have hev : ∀ᶠ a in 𝓝 h, ∀ z∈criticalCut k f ξ (h/2),
      criticalHeight k (halfPlaneFunction f) z<h → criticalHeight k (halfPlaneFunction f) z<a := by
    apply (hfin.eventually_all).mpr
    intro z hz
    by_cases hz' : criticalHeight k (halfPlaneFunction f) z<h
    · exact (lt_mem_nhds hz').mono (fun _ ha _=>ha)
    · exact Filter.Eventually.of_forall (fun _ ha=>False.elim (hz' ha))
  obtain ⟨a,ha,hhalf,hbound⟩ := ((lt_mem_nhds (show h/2<h by linarith)).and hev).exists_lt
  refine ⟨a,by linarith,ha,?_,?_⟩
  · ext z
    constructor
    · intro hz
      have hz' : z∈criticalCut k f ξ (h/2) := ⟨hz.1,hhalf.le.trans hz.2⟩
      refine ⟨hz.1,?_⟩
      by_contra hn
      have hx := hbound z hz' (lt_of_not_ge hn)
      linarith [hz.2]
    · intro hz
      exact ⟨hz.1,ha.le.trans hz.2⟩
  · intro z hz
    exact ha.trans_le hz.2

lemma source_squared_critical_strict {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    {z : UpperHalfPlane} {a : ℝ} (ha : 0<a)
    (hz : criticalMap k (halfPlaneFunction f) z=ξ)
    (hheight : a<criticalHeight k (halfPlaneFunction f) z) :
    squaredReciprocalPotential k (halfPlaneFunction f) ξ z<(1/a)^2 := by
  apply (squaredReciprocalPotential_lt_sublevel z.im_pos ha).mpr
  have hn : 0<‖halfPlaneFunction f z-ξ‖ := by
    exact norm_pos_iff.mpr (sub_ne_zero.mpr (fun he=>criticalMap_ne_image hk.ne' z.im_pos
      (halfPlaneFunction_deriv_ne_zero f z.im_pos) (hz.trans he.symm)))
  rw [← criticalHeight_value hk z.im_pos hz] at hheight
  rw [lt_div_iff₀ ha]
  have ht := (lt_div_iff₀ hn).mp hheight
  nlinarith

lemma source_squared_interior {k : ℝ} {f : DiskFamily} {ξ z : ℂ} {c : ℝ}
    (hz : 0<z.im) (hc : squaredReciprocalPotential k (halfPlaneFunction f) ξ z<c) :
    z∈interior {w : ℂ | 0<w.im ∧ squaredReciprocalPotential k (halfPlaneFunction f) ξ w≤c} := by
  apply mem_interior_iff_mem_nhds.mpr
  have ha := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have hu := (squaredReciprocalPotential_contDiffAt (k:=k) (ξ:=ξ) hz ha).continuousAt
  filter_upwards [isOpen_halfPlane.mem_nhds hz,hu (gt_mem_nhds hc)] with w hw hwc
  exact ⟨hw,hwc.le⟩

lemma source_poles_subsingleton (f : DiskFamily) (ξ : ℂ) :
    {z : ℂ | 0<z.im ∧ halfPlaneFunction f z=ξ}.Subsingleton := by
  intro z hz w hw
  exact halfPlaneFunction_injOn f hz.1 hw.1 (hz.2.trans hw.2.symm)

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CompactIndexSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_sum_local_indices {u : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (C : Finset ℂ) (r : ℂ → ℝ) (sign : ℂ → ℤ)
    (hballs : ∀ p∈C, Metric.closedBall p (r p) ⊆ K)
    (hdisj : (C:Set ℂ).PairwiseDisjoint (fun p=>Metric.closedBall p (r p)))
    (hregular : ∀ z∈K, (∀ p∈C, r p≤dist z p) →
      ContDiffAt ℝ 1 u z ∧ fderiv ℝ u z≠0)
    (hlocal : ∀ p∈C, ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r p) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=sign p) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ meshPoint o s v∈K) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=∑ p∈C, sign p := by
  classical
  let A := K \ ⋃ p∈C, Metric.ball p (r p)
  have hA : IsCompact A := hK.diff (isOpen_biUnion (fun p _=>Metric.isOpen_ball))
  have hreg : ∀ z∈A, ∃ L : ℂ →L[ℝ] ℝ,
      HasStrictFDerivAt u L z ∧ (L 1≠0 ∨ L Complex.I≠0) := by
    intro z hz
    have hh := hregular z hz.1 (by
      intro p hp
      exact le_of_not_gt (fun hb=>hz.2 (mem_iUnion.mpr ⟨p,mem_iUnion.mpr ⟨hp,hb⟩⟩)))
    refine ⟨fderiv ℝ u z,hh.1.hasStrictFDerivAt one_ne_zero,?_⟩
    by_contra h
    push Not at h
    exact hh.2 (realCLM_eq_zero h.1 h.2)
  have hg := compact_regular_star hA (by simp : ‖(1:ℂ)‖≤1) (by simp : ‖Complex.I‖≤1) hreg
  have hl := (C.eventually_all).mpr hlocal
  filter_upwards [hg,hl] with s hs hs'
  intro hspos o S hS
  let L : ℂ → Finset Lattice := fun p=>(meshPoint_bounded_preimage (o:=o) hspos.ne'
    (Metric.isBounded_closedBall (x:=p) (r:=r p))).toFinset
  have hL (p : ℂ) (v : Lattice) : v∈L p ↔ dist (meshPoint o s v) p≤r p := by
    simp only [L,Set.Finite.mem_toFinset,mem_preimage,Metric.mem_closedBall]
  let T := C.biUnion L
  have hTS : T⊆S := by
    intro v hv
    obtain ⟨p,hp,hv⟩ := Finset.mem_biUnion.mp hv
    exact (hS v).mpr (hballs p hp ((hL p v).mp hv))
  have hzero : ∀ v∈S, v∉T → heightIndex (u ∘ meshPoint o s) ex ey v=0 := by
    intro v hv hvt
    have hva : meshPoint o s v∈A := by
      refine ⟨(hS v).mp hv,?_⟩
      intro hm
      obtain ⟨p,hp,hm⟩ := mem_iUnion₂.mp hm
      apply hvt
      exact Finset.mem_biUnion.mpr ⟨p,hp,(hL p v).mpr hm.le⟩
    exact RegularStar.index_zero ((hs _ hva hspos).toRegularStar)
  have hpair : (C:Set ℂ).PairwiseDisjoint L := by
    intro p hp q hq hpq
    apply Finset.disjoint_left.mpr
    intro v hvp hvq
    exact Set.disjoint_left.mp (hdisj hp hq hpq) ((hL p v).mp hvp) ((hL q v).mp hvq)
  calc
    ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v = ∑ v∈T, heightIndex (u ∘ meshPoint o s) ex ey v :=
      (Finset.sum_subset hTS (fun v hv hvt=>hzero v hv hvt)).symm
    _ = ∑ p∈C, ∑ v∈L p, heightIndex (u ∘ meshPoint o s) ex ey v := Finset.sum_biUnion hpair
    _ = ∑ p∈C, sign p := Finset.sum_congr rfl (fun p hp=>hs' p hp hspos o (L p) (hL p))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CompactMorseIndex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_morse_index_sum {u : ℂ → ℝ} {K : Set ℂ} (hK : IsCompact K)
    (C : Finset ℂ) (hc : ∀ z∈K, fderiv ℝ u z=0 ↔ z∈C)
    (hC : ∀ p∈C, p∈interior K)
    (hu : ∀ p∈K, ContDiffAt ℝ 2 u p)
    (htr : ∀ p∈C, 0<second u p 1 1+second u p Complex.I Complex.I)
    (hdet : ∀ p∈C, hessianDet u p≠0) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
      (∀ v, v∈S ↔ meshPoint o s v∈K) →
        ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=∑ p∈C, morseSign u p := by
  classical
  have hchoose : ∀ p : ℂ, ∃ r>0, p∈C →
      (Metric.closedBall p r⊆K) ∧
      (∀ q∈C, q≠p → 3*r<dist p q) ∧
      (∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ (o : ℂ) (S : Finset Lattice),
        (∀ v, v∈S ↔ dist (meshPoint o s v) p≤r) →
          ∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v=morseSign u p) := by
    intro p
    by_cases hp : p∈C
    · have hpK := interior_subset (hC p hp)
      obtain ⟨R,hR,hlocal⟩ := smooth_morse_local_index (hu p hpK) ((hc p hpK).mpr hp)
        (htr p hp) (hdet p hp)
      obtain ⟨ρ,hρ,hnb⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp (hC p hp))
      have hsep : ∀ᶠ r in 𝓝 (0:ℝ), ∀ q∈C, q≠p → r<dist p q/3 := by
        apply (C.eventually_all).mpr
        intro q hq
        by_cases hqp : q=p
        · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h hqp))
        · exact (gt_mem_nhds (by simpa using (div_pos (dist_pos.mpr (Ne.symm hqp)) (by norm_num : (0:ℝ)<3)))).mono
            (fun _ hh _=>hh)
      obtain ⟨r,hr,hrr,hrr',hrs⟩ := ((gt_mem_nhds hR).and ((gt_mem_nhds hρ).and hsep)).exists_gt
      refine ⟨r,hr,fun _=>⟨?_,?_,hlocal r ⟨hr,hrr⟩⟩⟩
      · intro z hz
        exact hnb (lt_of_le_of_lt hz hrr')
      · intro q hq hqp
        have := hrs q hq hqp
        linarith
    · exact ⟨1,by norm_num,fun h=>False.elim (hp h)⟩
  choose r hrpos hr using hchoose
  apply compact_sum_local_indices hK C r (morseSign u) (fun p hp=>(hr p hp).1) ?_ ?_
    (fun p hp=>(hr p hp).2.2)
  · intro p hp q hq hpq
    apply Set.disjoint_left.mpr
    intro z hpz hqz
    have ha := (hr p hp).2.1 q hq hpq.symm
    have hb := (hr q hq).2.1 p hp hpq
    rw [dist_comm q p] at hb
    have ht := dist_triangle p z q
    rw [dist_comm p z] at ht
    change dist z p≤r p at hpz
    change dist z q≤r q at hqz
    linarith [dist_nonneg (x:=p) (y:=q)]
  · intro z hz hdist
    refine ⟨(hu z hz).of_le (by norm_num),?_⟩
    intro hzero
    have hzC := (hc z hz).mp hzero
    have hd := hdist z hzC
    rw [dist_self] at hd
    exact (not_le_of_gt (hrpos z)) hd

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PlaneRectangle
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_planeRectangle (o : ℂ) (A B : ℝ) : IsCompact (planeRectangle o A B) := by
  have hc : IsClosed (planeRectangle o A B) :=
    (isClosed_le ((Complex.continuous_re.sub continuous_const).abs) continuous_const).inter
    (isClosed_le ((Complex.continuous_im.sub continuous_const).abs) continuous_const)
  apply (isCompact_closedBall o (A+B)).of_isClosed_subset hc
  intro z hz
  rw [Metric.mem_closedBall,dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im (z-o)).trans (add_le_add hz.1 hz.2)

lemma compact_halfPlane_rectangle {K : Set ℂ} (hK : IsCompact K) (hne : K.Nonempty)
    (hH : ∀ z∈K, 0<z.im) :
    ∃ (o : ℂ) (A B δ : ℝ), 0<A ∧ 0<B ∧ 0<δ ∧
      (∀ z∈K, |z.re-o.re|+δ≤A ∧ |z.im-o.im|+δ≤B) ∧
      (∀ z∈planeRectangle o A B, 0<z.im) := by
  obtain ⟨p,hp,hmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  let a := p.im
  have ha : 0<a := hH p hp
  have haR : a≤R := (Complex.im_le_norm p).trans (hR p hp)
  let o : ℂ := ((a+R)/2:ℂ)*Complex.I
  let δ := min 1 (a/4)
  have hδ : 0<δ := lt_min (by norm_num) (by positivity)
  refine ⟨o,R+1,R/2,δ,by linarith,by linarith,hδ,?_,?_⟩
  · intro z hz
    have hzR := hR z hz
    have hzA := (Complex.abs_re_le_norm z).trans hzR
    have hzB := (Complex.im_le_norm z).trans hzR
    have haz : a≤z.im := hmin hz
    have hδ₁ : δ≤1 := min_le_left _ _
    have hδ₂ : δ≤a/4 := min_le_right _ _
    have hor : o.re=0 := by simp [o]
    have hoi : o.im=(a+R)/2 := by simp [o]
    rw [hor,hoi,sub_zero]
    constructor
    · linarith
    · have hab : |z.im-(a+R)/2|≤(R-a)/2 := abs_le.mpr ⟨by linarith,by linarith⟩
      linarith
  · intro z hz
    have hoi : o.im=(a+R)/2 := by simp [o]
    have hh := (abs_le.mp hz.2).1
    rw [hoi] at hh
    linarith

lemma meshPoint_re (o : ℂ) (s : ℝ) (v : Lattice) :
    (meshPoint o s v).re=o.re+s*((ofLex v).1:ℝ) := by simp [meshPoint]
lemma meshPoint_im (o : ℂ) (s : ℝ) (v : Lattice) :
    (meshPoint o s v).im=o.im+s*((ofLex v).2:ℝ) := by simp [meshPoint]

lemma meshPoint_near (o z : ℂ) {s : ℝ} (hs : 0 < s) :
    ∃ v : Lattice, dist (meshPoint o s v) z < 2*s := by
  let i : ℤ := ⌊(z.re-o.re)/s⌋
  let j : ℤ := ⌊(z.im-o.im)/s⌋
  let v : Lattice := toLex (i,j)
  have hi : s*(i:ℝ)≤z.re-o.re ∧ z.re-o.re<s*((i:ℝ)+1) := by
    constructor
    · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Int.floor_le _)
    · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _) |>.trans_eq (mul_comm _ _)
  have hj : s*(j:ℝ)≤z.im-o.im ∧ z.im-o.im<s*((j:ℝ)+1) := by
    constructor
    · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Int.floor_le _)
    · exact (div_lt_iff₀ hs).mp (Int.lt_floor_add_one _) |>.trans_eq (mul_comm _ _)
  have hvx : |(meshPoint o s v-z).re|<s := by
    rw [Complex.sub_re,meshPoint_re]
    change |o.re+s*(i:ℝ)-z.re|<s
    exact abs_lt.mpr ⟨by linarith [hi.2],by linarith [hi.1]⟩
  have hvy : |(meshPoint o s v-z).im|<s := by
    rw [Complex.sub_im,meshPoint_im]
    change |o.im+s*(j:ℝ)-z.im|<s
    exact abs_lt.mpr ⟨by linarith [hj.2],by linarith [hj.1]⟩
  refine ⟨v,?_⟩
  rw [dist_eq_norm]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans_lt (by linarith)

lemma meshPoint_hits_interior {K : Set ℂ} (hne : (interior K).Nonempty) (o : ℂ) :
    ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∃ v, meshPoint o s v∈K := by
  obtain ⟨z,hz⟩ := hne
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hz)
  filter_upwards [gt_mem_nhds (show (0:ℝ)<r/2 by positivity)] with s hs
  intro hspos
  obtain ⟨v,hv⟩ := meshPoint_near o z hspos
  exact ⟨v,hball (show meshPoint o s v∈Metric.ball z r by rw [Metric.mem_ball]; linarith)⟩

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridChains
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma y_sub_one_ne_zero : y - 1 ≠ 0 := by
  intro h
  have he := congrArg (fun p : Chain => (p.coeff 1).coeff 0) h
  norm_num [y,coeff_one] at he

lemma boundary_face (a b : Chain) : boundary₁ (faceH a b) (faceV a b) (faceD a b) = 0 := by
  unfold boundary₁ faceH faceV faceD
  ring

lemma square_cycle_fills {h v : Chain} (hc : (x-1)*h+(y-1)*v=0) :
    ∃ s : Chain, h=(1-y)*s ∧ v=(x-1)*s := by
  have hv : eval (1 : Polynomial ℚ) h = 0 := by
    have he := congrArg (eval (1 : Polynomial ℚ)) hc
    simp only [eval_add,eval_mul,eval_sub,eval_one,eval_zero,x,y,eval_C,eval_X,
      sub_self,zero_mul,add_zero] at he
    have hn : (X : Polynomial ℚ)-1 ≠ 0 := by
      intro hn
      have ha := congrArg (fun p : Polynomial ℚ => p.coeff 1) hn
      norm_num [coeff_one] at ha
    exact (mul_eq_zero.mp he).resolve_left hn
  have hd : (y-1) ∣ h := by
    simpa only [y,C_1] using (dvd_iff_isRoot.mpr hv : (X-C (1 : Polynomial ℚ)) ∣ h)
  obtain ⟨a,ha⟩ := hd
  refine ⟨-a,?_,?_⟩
  · rw [ha]
    ring
  · have he : (y-1)*((x-1)*a+v)=0 := by
      rw [ha] at hc
      convert hc using 1
      ring
    have he' := (mul_eq_zero.mp he).resolve_left y_sub_one_ne_zero
    have hv' : v = -(x-1)*a := by linear_combination he'
    rw [hv']
    ring

lemma cycle_fills {h v d : Chain} (hc : boundary₁ h v d = 0) :
    ∃ a b : Chain, faceH a b = h ∧ faceV a b = v ∧ faceD a b = d := by
  have hs : (x-1)*(h+d)+(y-1)*(v+x*d)=0 := by
    unfold boundary₁ at hc
    convert hc using 1
    ring
  obtain ⟨s,hh,hv⟩ := square_cycle_fills hs
  refine ⟨s-d,s,?_,?_,?_⟩
  · unfold faceH
    linear_combination -hh
  · unfold faceV
    linear_combination -hv
  · unfold faceD
    ring

lemma face_eq_aux {R : Type*} [CommRing R] (Y : R) {a b c d : R}
    (hH : a-Y*b=c-Y*d) (hD : b-a=d-c) : (Y-1)*(b-d)=0 := by
  linear_combination -hH-hD

lemma face_boundary_injective : Function.Injective
    (fun p : Chain × Chain => (faceH p.1 p.2,faceV p.1 p.2,faceD p.1 p.2)) := by
  intro p q he
  have hH := congrArg (fun a : Chain × Chain × Chain => a.1) he
  have hD := congrArg (fun a : Chain × Chain × Chain => a.2.2) he
  change p.1-y*p.2 = q.1-y*q.2 at hH
  change p.2-p.1 = q.2-q.1 at hD
  have hm := face_eq_aux y hH hD
  have hp := (mul_eq_zero.mp hm).resolve_left y_sub_one_ne_zero
  have hb : p.2=q.2 := sub_eq_zero.mp hp
  have ha : p.1=q.1 := by
    rw [hb] at hH
    exact sub_left_injective hH
  exact Prod.ext ha hb

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridSupport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma finite_coeff_support (p : Chain) : {v : ℕ × ℕ | coeff p v.1 v.2 ≠ 0}.Finite := by
  classical
  apply ((p.support.biUnion fun j => ((p.coeff j).support).map ⟨fun i => (i,j),by intro i k h; exact congrArg Prod.fst h⟩).finite_toSet).subset
  intro v hv
  simp only [Finset.mem_coe,Finset.mem_biUnion,Finset.mem_map]
  refine ⟨v.2,mem_support_iff.mpr ?_,v.1,mem_support_iff.mpr hv,rfl⟩
  intro he
  exact hv (by simp [coeff,he])

lemma BoundarySupported.anchor_eq {S : Set (ℕ × ℕ)} {a b : Chain} (hb : BoundarySupported S a b)
    {i j : ℕ} (hv : (i,j) ∉ S) : coeff a i j = coeff b i j := by
  have h := hb.diagonal i j (Or.inl hv)
  exact (sub_eq_zero.mp (by simpa only [faceD,coeff_sub] using h)).symm

lemma BoundarySupported.anchor_zero_axis₁ {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {j : ℕ} (hv : (0,j) ∉ S) : coeff a 0 j = 0 := by
  have h := hb.vertical 0 j (Or.inl hv)
  rw [hb.anchor_eq hv]
  simpa only [faceV,coeff_sub,coeff_x_zero,zero_sub,neg_eq_zero] using h

lemma BoundarySupported.anchor_zero_axis₂ {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i : ℕ} (hv : (i,0) ∉ S) : coeff a i 0 = 0 := by
  have h := hb.horizontal i 0 (Or.inl hv)
  simpa only [faceH,coeff_sub,coeff_y_zero,sub_zero] using h

lemma BoundarySupported.anchor_eq_right {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i+1,j) ∉ S) :
    coeff a i j = coeff a (i+1) j := by
  have h := hb.vertical (i+1) j (Or.inl hv)
  simpa only [faceV,coeff_sub,coeff_x_succ,sub_eq_zero,← hb.anchor_eq hv] using h

lemma BoundarySupported.anchor_eq_up {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S) (hw : (i,j+1) ∉ S) :
    coeff a i j = coeff a i (j+1) := by
  have h := hb.horizontal i (j+1) (Or.inl hw)
  exact (sub_eq_zero.mp (by simpa only [faceH,coeff_sub,coeff_y_succ,← hb.anchor_eq hv] using h)).symm

lemma BoundarySupported.anchor_eq_left {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S) (hi : 0 < i) :
    coeff a i j = coeff a (i-1) j := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hi)
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using (hb.anchor_eq_right hv).symm

lemma BoundarySupported.anchor_eq_down {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) {i j : ℕ} (hv : (i,j) ∉ S)
    (hw : (i,j-1) ∉ S) (hj : 0 < j) : coeff a i j = coeff a i (j-1) := by
  obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hj)
  simpa only [Nat.succ_eq_add_one,Nat.add_sub_cancel] using (hb.anchor_eq_up hw hv).symm

lemma BoundarySupported.anchor_zero_of_ascent {u : ℕ × ℕ → ℝ} {c : ℝ} {a b : Chain}
    (hb : BoundarySupported {v | u v ≤ c} a b)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    ∀ i j, c < u (i,j) → coeff a i j = 0 := by
  classical
  let T : Set (ℕ × ℕ) := {v : ℕ × ℕ | coeff a v.1 v.2 ≠ 0 ∧ c < u v}
  have hT : T.Finite := (finite_coeff_support a).subset (fun _ h => h.1)
  by_contra hall
  push Not at hall
  obtain ⟨i,j,hij,hne⟩ := hall
  have hneT : T.Nonempty := ⟨(i,j),hne,hij⟩
  obtain ⟨v,hv,hmax⟩ := Set.exists_max_image T u hT hneT
  have hvout : v ∉ {w | u w ≤ c} := not_le.mpr hv.2
  have hi : 0 < v.1 := by
    by_contra h
    have hz : v.1 = 0 := Nat.eq_zero_of_not_pos h
    exact hv.1 (by simpa [hz] using hb.anchor_zero_axis₁ (by simpa only [← hz,Prod.mk.eta] using hvout))
  have hj : 0 < v.2 := by
    by_contra h
    have hz : v.2 = 0 := Nat.eq_zero_of_not_pos h
    exact hv.1 (by simpa [hz] using hb.anchor_zero_axis₂ (by simpa only [← hz,Prod.mk.eta] using hvout))
  have hcontr (w : ℕ × ℕ) (hle : u v < u w) (he : coeff a v.1 v.2 = coeff a w.1 w.2) : False := by
    have hw : w ∈ T := ⟨fun h => hv.1 (he.trans h),hv.2.trans hle⟩
    exact (not_lt_of_ge (hmax w hw)) hle
  rcases hascent v.1 v.2 hv.2 hi hj with h|h|h|h
  · exact hcontr (v.1+1,v.2) h (hb.anchor_eq_right (not_le.mpr (hv.2.trans h)))
  · exact hcontr (v.1,v.2+1) h (hb.anchor_eq_up hvout (not_le.mpr (hv.2.trans h)))
  · exact hcontr (v.1-1,v.2) h (hb.anchor_eq_left hvout hi)
  · exact hcontr (v.1,v.2-1) h (hb.anchor_eq_down hvout (not_le.mpr (hv.2.trans h)) hj)

lemma BoundarySupported.faceSupported {S : Set (ℕ × ℕ)} {a b : Chain}
    (hb : BoundarySupported S a b) (ha : ∀ i j, (i,j) ∉ S → coeff a i j = 0) : FaceSupported S a b := by
  have hbzero (i j : ℕ) (hv : (i,j) ∉ S) : coeff b i j = 0 :=
    (hb.anchor_eq hv).symm.trans (ha i j hv)
  have hdiag (i j : ℕ) (hv : (i+1,j+1) ∉ S) : coeff b i j = 0 := by
    have hvv := hb.vertical (i+1) (j+1) (Or.inl hv)
    have hhh := hb.horizontal i (j+1) (Or.inr hv)
    simp only [faceV,coeff_sub,coeff_x_succ,hbzero _ _ hv,sub_zero] at hvv
    simpa only [faceH,coeff_sub,coeff_y_succ,hvv,zero_sub,neg_eq_zero] using hhh
  constructor
  · intro i j hne
    refine ⟨?_,?_,?_⟩
    · by_contra hv
      exact hne (ha i j hv)
    · by_contra hv
      exact hne ((hb.anchor_eq_right hv).trans (ha (i+1) j hv))
    · by_contra hv
      have h := hb.diagonal i j (Or.inr hv)
      exact hne (by simpa only [faceD,coeff_sub,hdiag i j hv,zero_sub,neg_eq_zero] using h)
  · intro i j hne
    refine ⟨?_,?_,?_⟩
    · by_contra hv
      exact hne (hbzero i j hv)
    · by_contra hv
      have h := hb.horizontal i (j+1) (Or.inl hv)
      exact hne (by simpa only [faceH,coeff_sub,coeff_y_succ,ha _ _ hv,zero_sub,neg_eq_zero] using h)
    · by_contra hv
      exact hne (hdiag i j hv)

lemma cycle_fills_sublevel {u : ℕ × ℕ → ℝ} {c : ℝ} {h v d : Chain}
    (hc : boundary₁ h v d = 0)
    (hH : ∀ i j, c < u (i,j) ∨ c < u (i+1,j) → coeff h i j = 0)
    (hV : ∀ i j, c < u (i,j) ∨ c < u (i,j+1) → coeff v i j = 0)
    (hD : ∀ i j, c < u (i,j) ∨ c < u (i+1,j+1) → coeff d i j = 0)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    ∃ a b, faceH a b = h ∧ faceV a b = v ∧ faceD a b = d ∧
      FaceSupported {w | u w ≤ c} a b := by
  obtain ⟨a,b,ha,hb,hd⟩ := cycle_fills hc
  have hs : BoundarySupported {w | u w ≤ c} a b := by
    constructor
    · simpa only [ha,mem_ofPred_eq,not_le] using hH
    · simpa only [hb,mem_ofPred_eq,not_le] using hV
    · simpa only [hd,mem_ofPred_eq,not_le] using hD
  refine ⟨a,b,ha,hb,hd,hs.faceSupported ?_⟩
  intro i j hi
  exact hs.anchor_zero_of_ascent hascent i j (not_le.mp hi)

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FiniteEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace StrictInverseFirstPower
open LinearMap Module

lemma finite_euler_inequality {K V₀ V₁ V₂ : Type*} [Field K]
    [AddCommGroup V₀] [Module K V₀] [FiniteDimensional K V₀]
    [AddCommGroup V₁] [Module K V₁] [FiniteDimensional K V₁]
    [AddCommGroup V₂] [Module K V₂] [FiniteDimensional K V₂]
    (d₁ : V₁ →ₗ[K] V₀) (d₂ : V₂ →ₗ[K] V₁) (aug : V₀ →ₗ[K] K)
    (hinj : Function.Injective d₂) (hexact : d₂.range = d₁.ker)
    (haug : aug ∘ₗ d₁ = 0) (hne : aug ≠ 0) :
    finrank K V₁ + 1 ≤ finrank K V₀ + finrank K V₂ := by
  have hr := d₁.finrank_range_add_finrank_ker
  have hd : finrank K d₁.ker = finrank K V₂ := by
    rw [← hexact]
    exact LinearMap.finrank_range_of_inj hinj
  have hle : d₁.range ≤ aug.ker := LinearMap.range_le_ker_iff.mpr haug
  have hh : aug.ker < ⊤ := lt_top_iff_ne_top.mpr (by simpa using hne)
  have ht := Submodule.finrank_lt_finrank_of_lt hh
  have hm := Submodule.finrank_mono hle
  simp only [finrank_top] at ht
  omega

end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridLinear
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma finrank_chainSpace (S : Set (ℕ × ℕ)) (hS : S.Finite) :
    finrank ℚ (chainSpace S) = S.ncard := by
  let := hS.fintype
  rw [(chainSpaceEquiv S).finrank_eq]
  simp

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridComplex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma faceBoundary_injective (S : Set (ℕ × ℕ)) : Function.Injective (faceBoundary S) := by
  intro f g he
  have hh : (faceH f.1.1 f.2.1,faceV f.1.1 f.2.1,faceD f.1.1 f.2.1) =
      (faceH g.1.1 g.2.1,faceV g.1.1 g.2.1,faceD g.1.1 g.2.1) :=
    congrArg (fun e : EdgeSpace S => (e.1.1,e.2.1.1,e.2.2.1)) he
  have hf := @face_boundary_injective (f.1.1,f.2.1) (g.1.1,g.2.1) hh
  exact Prod.ext (Subtype.ext (congrArg Prod.fst hf)) (Subtype.ext (congrArg Prod.snd hf))

lemma boundary_exact {u : ℕ × ℕ → ℝ} {c : ℝ}
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    (faceBoundary {w | u w ≤ c}).range = (edgeBoundary {w | u w ≤ c}).ker := by
  let S := {w | u w ≤ c}
  apply le_antisymm
  · rintro _ ⟨f,rfl⟩
    apply Subtype.ext
    exact boundary_face f.1.1 f.2.1
  · intro e he
    have hc : boundary₁ e.1.1 e.2.1.1 e.2.2.1 = 0 := congrArg Subtype.val he
    have hH := (mem_chainSpace (horizontalSet S) e.1.1).mp e.1.2
    have hV := (mem_chainSpace (verticalSet S) e.2.1.1).mp e.2.1.2
    have hD := (mem_chainSpace (diagonalSet S) e.2.2.1).mp e.2.2.2
    obtain ⟨a,b,ha,hb,hd,hs⟩ := cycle_fills_sublevel hc
      (fun i j h => hH i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh)))
      (fun i j h => hV i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh)))
      (fun i j h => hD i j (by intro hw; exact h.elim (fun hh => (not_lt_of_ge hw.1) hh) (fun hh => (not_lt_of_ge hw.2) hh))) hascent
    have ha' : a ∈ chainSpace (lowerSet S) := (mem_chainSpace _ _).mpr
      (fun i j h => by by_contra hn; exact h (hs.lower i j hn))
    have hb' : b ∈ chainSpace (upperSet S) := (mem_chainSpace _ _).mpr
      (fun i j h => by by_contra hn; exact h (hs.upper i j hn))
    exact ⟨(⟨a,ha'⟩,⟨b,hb'⟩),Prod.ext (Subtype.ext ha) (Prod.ext (Subtype.ext hb) (Subtype.ext hd))⟩

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.GridEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Polynomial Set Module
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma augmentation_boundary₁ (h v d : Chain) : augmentation (boundary₁ h v d) = 0 := by
  simp [augmentation,boundary₁,x,y]

lemma vertexAugmentation_boundary (S : Set (ℕ × ℕ)) :
    vertexAugmentation S ∘ₗ edgeBoundary S = 0 := by
  apply LinearMap.ext
  intro e
  exact augmentation_boundary₁ e.1.1 e.2.1.1 e.2.2.1

lemma vertexAugmentation_ne_zero {S : Set (ℕ × ℕ)} (hne : S.Nonempty) :
    vertexAugmentation S ≠ 0 := by
  classical
  obtain ⟨⟨i,j⟩,hv⟩ := hne
  let p : Chain := monomial j (monomial i 1)
  have hp : p ∈ chainSpace S := by
    rw [mem_chainSpace]
    intro l m hm
    by_cases hmi : m=j
    · subst m
      have hli : l ≠ i := by rintro rfl; exact hm hv
      simp [p,coeff,coeff_monomial,Ne.symm hli]
    · simp [p,coeff,coeff_monomial,Ne.symm hmi]
  intro he
  have hh := congrArg (fun f : chainSpace S →ₗ[ℚ] ℚ => f ⟨p,hp⟩) he
  simp [vertexAugmentation,augmentation,p,eval_monomial] at hh

lemma sublevel_euler {u : ℕ × ℕ → ℝ} {c : ℝ}
    (hfin : {v | u v ≤ c}.Finite) (hne : {v | u v ≤ c}.Nonempty)
    (hascent : ∀ i j, c < u (i,j) → 0 < i → 0 < j →
      u (i,j) < u (i+1,j) ∨ u (i,j) < u (i,j+1) ∨
      u (i,j) < u (i-1,j) ∨ u (i,j) < u (i,j-1)) :
    (horizontalSet {v | u v ≤ c}).ncard + (verticalSet {v | u v ≤ c}).ncard +
      (diagonalSet {v | u v ≤ c}).ncard + 1 ≤
    {v | u v ≤ c}.ncard + (lowerSet {v | u v ≤ c}).ncard + (upperSet {v | u v ≤ c}).ncard := by
  let S := {v | u v ≤ c}
  have hH : (horizontalSet S).Finite := hfin.subset fun _ h => h.1
  have hV : (verticalSet S).Finite := hfin.subset fun _ h => h.1
  have hD : (diagonalSet S).Finite := hfin.subset fun _ h => h.1
  have hL : (lowerSet S).Finite := hfin.subset fun _ h => h.1
  have hU : (upperSet S).Finite := hfin.subset fun _ h => h.1
  let := hfin.fintype
  let := hH.fintype
  let := hV.fintype
  let := hD.fintype
  let := hL.fintype
  let := hU.fintype
  have he := finite_euler_inequality (K := ℚ) (V₀ := chainSpace S) (V₁ := EdgeSpace S) (V₂ := FaceSpace S) (edgeBoundary S) (faceBoundary S) (vertexAugmentation S)
    (faceBoundary_injective S) (boundary_exact hascent) (vertexAugmentation_boundary S)
    (vertexAugmentation_ne_zero hne)
  let (T : Set (ℕ × ℕ)) : Module.Free ℚ (chainSpace T) := Module.Free.of_equiv (chainSpaceEquiv T).symm
  have hdimE : finrank ℚ (EdgeSpace S) = finrank ℚ (chainSpace (horizontalSet S)) + finrank ℚ (chainSpace (verticalSet S)) + finrank ℚ (chainSpace (diagonalSet S)) := by
    dsimp only [EdgeSpace]
    rw [Module.finrank_prod,Module.finrank_prod]
    omega
  have hdimF : finrank ℚ (FaceSpace S) = finrank ℚ (chainSpace (lowerSet S)) + finrank ℚ (chainSpace (upperSet S)) := by
    exact Module.finrank_prod
  rw [hdimE,hdimF] at he
  simp only [finrank_chainSpace S hfin,
    finrank_chainSpace _ hH,finrank_chainSpace _ hV,finrank_chainSpace _ hD,
    finrank_chainSpace _ hL,finrank_chainSpace _ hU] at he
  dsimp only [S] at he
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.IndexEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function
namespace StrictInverseFirstPower.Grid
noncomputable section
variable {V L : Type*} [AddCommGroup V] [DecidableEq V] [LinearOrder L]

omit [AddCommGroup V] in
lemma finite_vertexMass (S : Finset V) : HasFiniteSupport (vertexMass S) :=
  S.finite_toSet.subset (by classical intro v hv; simpa [vertexMass] using hv)

omit [AddCommGroup V] in
lemma finite_weight (S : Finset V) (f : V → ℤ) :
    HasFiniteSupport (fun v => vertexMass S v*f v) := (finite_vertexMass S).mul_left f

lemma finite_weight_shift (S : Finset V) (a : V) (f : V → ℤ) :
    HasFiniteSupport (fun v => vertexMass S (v+a)*f v) := by
  have h : HasFiniteSupport (fun v => vertexMass S (v+a)) :=
    (finite_vertexMass S).preimage (Equiv.addRight a).injective.injOn
  exact h.mul_left f

omit [AddCommGroup V] in
lemma finsum_weight (S : Finset V) (f : V → ℤ) :
    ∑ᶠ v, vertexMass S v*f v = ∑ v∈S, f v := by
  classical
  rw [finsum_eq_sum_of_support_subset _ (s:=S)]
  · exact Finset.sum_congr rfl (by intro v hv; simp [vertexMass,hv])
  · intro v hv
    by_contra hn
    change v ∉ S at hn
    exact hv (by simp [vertexMass,hn])

lemma finsum_weight_shift (S : Finset V) (f : V → ℤ) (a : V) :
    ∑ᶠ v, vertexMass S v*f (v-a) = ∑ᶠ v, vertexMass S (v+a)*f v := by
  simpa only [Equiv.coe_addRight,add_sub_cancel_right] using
    (finsum_comp_equiv (Equiv.addRight a) (f := fun v => vertexMass S v*f (v-a))).symm

omit [AddCommGroup V] in
lemma edge_mass {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {a b : V} (hab : a≠b) :
    vertexMass S a*rankBit r b a+vertexMass S b*rankBit r a b =
      if a∈S ∧ b∈S then 1 else 0 := by
  classical
  have ht := rankBit_complement hr hab
  by_cases ha : a∈S <;> by_cases hb : b∈S
  · simpa [vertexMass,ha,hb,add_comm] using ht
  · have hn : ¬ r b<r a := fun h => hb (hS a ha b h)
    simp [vertexMass,ha,hb,rankBit,hn]
  · have hn : ¬ r a<r b := fun h => ha (hS b hb a h)
    simp [vertexMass,ha,hb,rankBit,hn]
  · simp [vertexMass,ha,hb]

omit [AddCommGroup V] in
lemma top_mass_factor {r : V → L} {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) (a b c : V) :
    vertexMass S a*topBit r a b c =
      (if a∈S ∧ b∈S ∧ c∈S then 1 else 0)*topBit r a b c := by
  classical
  by_cases hab : r b<r a <;> by_cases hac : r c<r a
  · by_cases ha : a∈S
    · simp [vertexMass,topBit,rankBit,hab,hac,ha,hS a ha b hab,hS a ha c hac]
    · simp [vertexMass,ha]
  · simp [topBit,rankBit,hac]
  · simp [topBit,rankBit,hab]
  · simp [topBit,rankBit,hab]

omit [AddCommGroup V] in
lemma triangle_mass {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {a b c : V}
    (hab : a≠b) (hbc : b≠c) (hac : a≠c) :
    vertexMass S a*topBit r a b c + vertexMass S b*topBit r b c a +
      vertexMass S c*topBit r c a b = if a∈S ∧ b∈S ∧ c∈S then 1 else 0 := by
  classical
  rw [top_mass_factor hS,top_mass_factor hS,top_mass_factor hS]
  have h₁ : (b∈S ∧ c∈S ∧ a∈S) ↔ (a∈S ∧ b∈S ∧ c∈S) := by tauto
  have h₂ : (c∈S ∧ a∈S ∧ b∈S) ↔ (a∈S ∧ b∈S ∧ c∈S) := by tauto
  simp only [h₁,h₂]
  rw [← mul_add,← mul_add,topBit_sum hr hab hbc hac,mul_one]

omit [AddCommGroup V] in
lemma finsum_vertexMass (S : Finset V) : ∑ᶠ v, vertexMass S v = S.card := by
  simpa only [mul_one,Finset.sum_const,Finset.sum_const_zero,nsmul_eq_mul,mul_one] using
    finsum_weight S (fun _=>1)

lemma edge_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x : V} (hx : x≠0) :
    ∑ v∈S, (edgeFlag r x v+rankBit r (v-x) v) = (meshEdges S x).card := by
  classical
  rw [← finsum_weight S]
  simp_rw [mul_add]
  rw [finsum_add_distrib (finite_weight S _) (finite_weight S _)]
  have he : (fun v => vertexMass S v*rankBit r (v-x) v) =
      (fun v => vertexMass S v*(fun w => rankBit r w (w+x)) (v-x)) := by
    funext v
    simp
  rw [he,finsum_weight_shift S (fun w=>rankBit r w (w+x)) x]
  rw [← finsum_add_distrib (finite_weight S _) (finite_weight_shift S x _)]
  have hpoint (v : V) : vertexMass S v*edgeFlag r x v+
      vertexMass S (v+x)*rankBit r v (v+x) = vertexMass (meshEdges S x) v := by
    simpa only [edgeFlag,vertexMass,meshEdges,Finset.mem_filter] using
      edge_mass hr hS (ne_self_add_of_ne_zero v hx)
  simp_rw [hpoint]
  exact finsum_vertexMass _

lemma lower_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, (lowerTop₀ r x y v +lowerTop₁ r x y (v-x)+lowerTop₂ r x y (v-(x+y))) =
      (meshLower S x y).card := by
  classical
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,
    ← finsum_weight S (lowerTop₀ r x y),
    ← finsum_weight S (fun v=>lowerTop₁ r x y (v-x)),
    ← finsum_weight S (fun v=>lowerTop₂ r x y (v-(x+y)))]
  rw [finsum_weight_shift S (lowerTop₁ r x y) x,
    finsum_weight_shift S (lowerTop₂ r x y) (x+y)]
  rw [← finsum_add_distrib (finite_weight S _) (finite_weight_shift S x _)]
  have hadd := finsum_add_distrib
    ((finite_weight S (lowerTop₀ r x y)).add (finite_weight_shift S x (lowerTop₁ r x y)))
    (finite_weight_shift S (x+y) (lowerTop₂ r x y))
  simp only [Pi.add_apply] at hadd
  rw [← hadd]
  have hpoint (v : V) : vertexMass S v*lowerTop₀ r x y v+
      vertexMass S (v+x)*lowerTop₁ r x y v+
      vertexMass S (v+(x+y))*lowerTop₂ r x y v = vertexMass (meshLower S x y) v := by
    simpa only [lowerTop₀,lowerTop₁,lowerTop₂,vertexMass,meshLower,Finset.mem_filter,add_assoc] using
      triangle_mass hr hS (ne_self_add_of_ne_zero v hx)
        (ne_self_add_of_ne_zero (v+x) hy)
        (show v≠v+x+y by simpa only [add_assoc] using ne_self_add_of_ne_zero v hd)
  simp_rw [hpoint]
  exact finsum_vertexMass _

lemma upper_index_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, (upperTop₀ r x y v +upperTop₁ r x y (v-y)+upperTop₂ r x y (v-(x+y))) =
      (meshUpper S x y).card := by
  simpa only [lowerTop₀,lowerTop₁,lowerTop₂,upperTop₀,upperTop₁,upperTop₂,
    meshLower,meshUpper,add_right_comm,add_comm x y] using
      lower_index_sum hr hS hy hx (by simpa only [add_comm] using hd)

lemma index_euler_sum {r : V → L} (hr : Injective r) {S : Finset V}
    (hS : ∀ a∈S, ∀ b, r b<r a → b∈S) {x y : V}
    (hx : x≠0) (hy : y≠0) (hd : x+y≠0) :
    ∑ v∈S, meshIndex r x y v = (S.card:ℤ) - (meshEdges S x).card -
      (meshEdges S y).card - (meshEdges S (x+y)).card +
      (meshLower S x y).card + (meshUpper S x y).card := by
  have he (v : V) : meshIndex r x y v = 1-
      (edgeFlag r x v+rankBit r (v-x) v)-
      (edgeFlag r y v+rankBit r (v-y) v)-
      (edgeFlag r (x+y) v+rankBit r (v-(x+y)) v)+
      (lowerTop₀ r x y v+lowerTop₁ r x y (v-x)+lowerTop₂ r x y (v-(x+y)))+
      (upperTop₀ r x y v+upperTop₁ r x y (v-y)+upperTop₂ r x y (v-(x+y))) := by
    unfold meshIndex
    ring
  simp_rw [he]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    Finset.sum_sub_distrib,Finset.sum_sub_distrib]
  rw [edge_index_sum hr hS hx,edge_index_sum hr hS hy,edge_index_sum hr hS hd,
    lower_index_sum hr hS hx hy hd,upper_index_sum hr hS hx hy hd]
  simp

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.LatticeEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma natEmbed_injective (M : ℤ) : Injective (natEmbed M) := by
  intro v w he
  have h := toLex.injective he
  apply Prod.ext <;> [have hh := congrArg Prod.fst h; have hh := congrArg Prod.snd h] <;>
    dsimp at hh <;> exact_mod_cast (add_right_cancel hh)

lemma natEmbed_x (M : ℤ) (i j : ℕ) : natEmbed M (i+1,j)=natEmbed M (i,j)+ex := by
  apply ofLex.injective
  simp [natEmbed,ex,add_assoc,add_comm]
lemma natEmbed_y (M : ℤ) (i j : ℕ) : natEmbed M (i,j+1)=natEmbed M (i,j)+ey := by
  apply ofLex.injective
  simp [natEmbed,ey,add_assoc,add_comm]
lemma natEmbed_xy (M : ℤ) (i j : ℕ) : natEmbed M (i+1,j+1)=natEmbed M (i,j)+ex+ey := by
  rw [natEmbed_x,natEmbed_y]
  abel
lemma natEmbed_mx (M : ℤ) (i j : ℕ) (hi : 0 < i) : natEmbed M (i-1,j)=natEmbed M (i,j)-ex := by
  apply eq_sub_iff_add_eq.mpr
  rw [← natEmbed_x,Nat.sub_add_cancel hi]
lemma natEmbed_my (M : ℤ) (i j : ℕ) (hj : 0 < j) : natEmbed M (i,j-1)=natEmbed M (i,j)-ey := by
  apply eq_sub_iff_add_eq.mpr
  rw [← natEmbed_y,Nat.sub_add_cancel hj]

lemma natEmbed_coverage {M : ℤ} {v : Lattice}
    (hx : M≤(ofLex v).1) (hy : M≤(ofLex v).2) : v∈range (natEmbed M) := by
  refine ⟨(((ofLex v).1-M).toNat,((ofLex v).2-M).toNat),?_⟩
  apply ofLex.injective
  simp only [natEmbed,ofLex_toLex,Int.toNat_of_nonneg (sub_nonneg.mpr hx),
    Int.toNat_of_nonneg (sub_nonneg.mpr hy),sub_add_cancel,Prod.mk.eta]

lemma finite_natEmbed_coverage {S : Set Lattice} (hS : S.Finite) :
    ∃ M : ℤ, S ⊆ range (natEmbed M) := by
  have hb := ((hS.image (fun v=>(ofLex v).1)).union
    (hS.image (fun v=>(ofLex v).2))).bddBelow
  obtain ⟨M,hM⟩ := hb
  refine ⟨M,fun v hv=>natEmbed_coverage ?_ ?_⟩
  · exact hM (Or.inl ⟨v,hv,rfl⟩)
  · exact hM (Or.inr ⟨v,hv,rfl⟩)

lemma ncard_natEmbed_preimage {M : ℤ} {S : Set Lattice}
    (hS : S ⊆ range (natEmbed M)) : (natEmbed M ⁻¹' S).ncard=S.ncard := by
  rw [← ncard_image_of_injective _ (natEmbed_injective M),image_preimage_eq_of_subset hS]

lemma lattice_sublevel_euler {u : Lattice → ℝ} {c : ℝ}
    (hfin : {v | u v≤c}.Finite) (hne : {v | u v≤c}.Nonempty)
    (hascent : ∀ v, c<u v →
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    let S := hfin.toFinset
    (meshEdges S ex).card+(meshEdges S ey).card+(meshEdges S (ex+ey)).card+1 ≤
      S.card+(meshLower S ex ey).card+(meshUpper S ex ey).card := by
  classical
  obtain ⟨M,hM⟩ := finite_natEmbed_coverage hfin
  let U : ℕ × ℕ → ℝ := u ∘ natEmbed M
  let T : Set (ℕ × ℕ) := {v | U v≤c}
  let S := hfin.toFinset
  have hT : T.Finite := hfin.preimage (natEmbed_injective M).injOn
  have hTne : T.Nonempty := by
    obtain ⟨v,hv⟩ := hne
    obtain ⟨w,rfl⟩ := hM hv
    exact ⟨w,hv⟩
  have he := sublevel_euler hT hTne (u:=U) (c:=c) (by
    intro i j hc hi hj
    simpa only [U,Function.comp_apply,natEmbed_x,natEmbed_y,natEmbed_mx M i j hi,
      natEmbed_my M i j hj] using hascent (natEmbed M (i,j)) hc)
  have hV : T.ncard=S.card := by
    rw [show T=natEmbed M ⁻¹' {v | u v≤c} from rfl,ncard_natEmbed_preimage hM]
    exact Set.ncard_eq_toFinset_card _ hfin
  have hcast (K : Finset Lattice) (hKS : (K:Set Lattice)⊆{v | u v≤c}) :
      (natEmbed M ⁻¹' (K:Set Lattice)).ncard=K.card := by
    rw [ncard_natEmbed_preimage (hKS.trans hM),Set.ncard_coe_finset]
  have hH : (horizontalSet T).ncard=(meshEdges S ex).card := by
    have hh : horizontalSet T=natEmbed M ⁻¹' (meshEdges S ex:Set Lattice) := by
      ext ⟨i,j⟩
      simp [horizontalSet,meshEdges,S,T,U,natEmbed_x]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hY : (verticalSet T).ncard=(meshEdges S ey).card := by
    have hh : verticalSet T=natEmbed M ⁻¹' (meshEdges S ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [verticalSet,meshEdges,S,T,U,natEmbed_y]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hD : (diagonalSet T).ncard=(meshEdges S (ex+ey)).card := by
    have hh : diagonalSet T=natEmbed M ⁻¹' (meshEdges S (ex+ey):Set Lattice) := by
      ext ⟨i,j⟩
      simp [diagonalSet,meshEdges,S,T,U,natEmbed_xy,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hL : (lowerSet T).ncard=(meshLower S ex ey).card := by
    have hh : lowerSet T=natEmbed M ⁻¹' (meshLower S ex ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [lowerSet,meshLower,S,T,U,natEmbed_x,natEmbed_y,add_comm,add_left_comm,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  have hR : (upperSet T).ncard=(meshUpper S ex ey).card := by
    have hh : upperSet T=natEmbed M ⁻¹' (meshUpper S ex ey:Set Lattice) := by
      ext ⟨i,j⟩
      simp [upperSet,meshUpper,S,T,U,natEmbed_y,natEmbed_x,add_assoc]
    rw [hh]
    apply hcast
    intro v hv
    exact hfin.mem_toFinset.mp (Finset.mem_filter.mp hv).1
  rw [hV,hH,hY,hD,hL,hR] at he
  exact he

lemma lattice_sublevel_index {u : Lattice → ℝ} {c : ℝ}
    (hfin : {v | u v≤c}.Finite) (hne : {v | u v≤c}.Nonempty)
    (hascent : ∀ v, c<u v →
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    1≤∑ v∈hfin.toFinset, heightIndex u ex ey v := by
  have hS : ∀ a∈hfin.toFinset, ∀ b, heightRank u b<heightRank u a→b∈hfin.toFinset := by
    intro a ha b hb
    simp only [heightRank,Prod.Lex.toLex_lt_toLex] at hb
    apply hfin.mem_toFinset.mpr
    have ha' := hfin.mem_toFinset.mp ha
    rcases hb with hb|⟨hb,_⟩ <;> dsimp at ha' ⊢ <;> linarith
  have he := index_euler_sum (heightRank_injective u) hS ex_ne_zero ey_ne_zero ex_add_ey_ne_zero
  have h := lattice_sublevel_euler hfin hne hascent
  change 1≤∑ v∈hfin.toFinset, meshIndex (heightRank u) ex ey v
  rw [he]
  omega

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.BoxExtension
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma latticeTaxicab_nonneg (v : Lattice) : 0≤latticeTaxicab v := add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma latticeBox_finite (N M : ℕ) : (latticeBox N M).Finite := by
  have he : latticeBox N M=ofLex ⁻¹' ((Icc (-(N:ℤ)) N) ×ˢ (Icc (-(M:ℤ)) M)) := by
    ext v
    change (|(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)) ↔
      ((-(N:ℤ)≤(ofLex v).1 ∧ (ofLex v).1≤(N:ℤ)) ∧
       (-(M:ℤ)≤(ofLex v).2 ∧ (ofLex v).2≤(M:ℤ)))
    simp only [abs_le]
  rw [he]
  exact ((Set.finite_Icc _ _).prod (Set.finite_Icc _ _)).preimage ofLex.injective.injOn

lemma outside_box_ascent {N M : ℕ} {v : Lattice} (hv : v∉latticeBox N M) :
    ∃ w, (w=v+ex ∨ w=v+ey ∨ w=v-ex ∨ w=v-ey) ∧ w∉latticeBox N M ∧
      latticeTaxicab v<latticeTaxicab w := by
  have hpos {i : ℤ} {n : ℕ} (hi : (n:ℤ) < |i|) :
      (0 ≤ i ∧ (n:ℤ) < i) ∨ (i < 0 ∧ i < -(n:ℤ)) := by
    rcases le_or_gt 0 i with h|h
    · exact Or.inl ⟨h,by simpa [abs_of_nonneg h] using hi⟩
    · exact Or.inr ⟨h,by rw [abs_of_neg h] at hi; omega⟩
  rcases not_and_or.mp hv with hx|hy
  · have hi := hpos (lt_of_not_ge hx)
    rcases hi with ⟨hi,hiN⟩|⟨hi,hiN⟩
    · refine ⟨v+ex,Or.inl rfl,?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_add,ex,ofLex_toLex,Prod.fst_add,Prod.snd_add]
        rw [abs_of_nonneg (by omega : 0≤(ofLex v).1+1)]
        omega
      · have hi' : (0:ℝ)≤(ofLex v).1 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_add,ex,ofLex_toLex,Prod.fst_add,Prod.snd_add,
          Int.cast_add,Int.cast_one,add_zero]
        rw [abs_of_nonneg hi',abs_of_nonneg (by linarith : (0:ℝ)≤(ofLex v).1+1)]
        linarith
    · refine ⟨v-ex,Or.inr (Or.inr (Or.inl rfl)),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_sub,ex,ofLex_toLex,Prod.fst_sub,Prod.snd_sub]
        rw [abs_of_neg (by omega : (ofLex v).1-1<0)]
        omega
      · have hi' : ((ofLex v).1:ℝ)<0 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_sub,ex,ofLex_toLex,Prod.fst_sub,Prod.snd_sub,
          Int.cast_sub,Int.cast_one,sub_zero]
        rw [abs_of_neg hi',abs_of_neg (by linarith : ((ofLex v).1:ℝ)-1<0)]
        linarith
  · have hi := hpos (lt_of_not_ge hy)
    rcases hi with ⟨hi,hiN⟩|⟨hi,hiN⟩
    · refine ⟨v+ey,Or.inr (Or.inl rfl),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_add,ey,ofLex_toLex,Prod.fst_add,Prod.snd_add]
        rw [abs_of_nonneg (by omega : 0≤(ofLex v).2+1)]
        omega
      · have hi' : (0:ℝ)≤(ofLex v).2 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_add,ey,ofLex_toLex,Prod.fst_add,Prod.snd_add,
          Int.cast_add,Int.cast_one,add_zero]
        rw [abs_of_nonneg hi',abs_of_nonneg (by linarith : (0:ℝ)≤(ofLex v).2+1)]
        linarith
    · refine ⟨v-ey,Or.inr (Or.inr (Or.inr rfl)),?_,?_⟩
      · change ¬ (_ ∧ _)
        simp only [ofLex_sub,ey,ofLex_toLex,Prod.fst_sub,Prod.snd_sub]
        rw [abs_of_neg (by omega : (ofLex v).2-1<0)]
        omega
      · have hi' : ((ofLex v).2:ℝ)<0 := by exact_mod_cast hi
        simp only [latticeTaxicab,ofLex_sub,ey,ofLex_toLex,Prod.fst_sub,Prod.snd_sub,
          Int.cast_sub,Int.cast_one,sub_zero]
        rw [abs_of_neg hi',abs_of_neg (by linarith : ((ofLex v).2:ℝ)-1<0)]
        linarith

lemma box_sublevel_index {u : Lattice → ℝ} {N M : ℕ} {c : ℝ}
    (hne : {v | v∈latticeBox N M ∧ u v≤c}.Nonempty)
    (hstar : ∀ v, v∈latticeBox N M → u v≤c →
      ∀ w∈meshStar ex ey v, w∈latticeBox N M)
    (ha : ∀ v∈latticeBox N M,
      u v<u (v+ex) ∨ u v<u (v+ey) ∨ u v<u (v-ex) ∨ u v<u (v-ey)) :
    ∀ S : Finset Lattice, (∀ v, v∈S ↔ v∈latticeBox N M ∧ u v≤c) →
      1≤∑ v∈S, heightIndex u ex ey v := by
  classical
  obtain ⟨B,hB⟩ := (latticeBox_finite N M).image u |>.bddAbove
  let D := max B c+1
  let w : Lattice → ℝ := fun v=>if v∈latticeBox N M then u v else D+latticeTaxicab v
  have hlow (v : Lattice) : w v≤c ↔ v∈latticeBox N M ∧ u v≤c := by
    by_cases hv : v∈latticeBox N M
    · simp [w,hv]
    · have hb : c<D+latticeTaxicab v := by
        have := latticeTaxicab_nonneg v
        dsimp [D]; linarith [le_max_right B c]
      simp [w,hv,not_le.mpr hb]
  have hfin : {v|w v≤c}.Finite := (latticeBox_finite N M).subset (fun v hv=>(hlow v).mp hv |>.1)
  have hne' : {v|w v≤c}.Nonempty := by obtain ⟨v,hv⟩:=hne; exact ⟨v,(hlow v).mpr hv⟩
  have hascent (v : Lattice) : w v<w (v+ex) ∨ w v<w (v+ey) ∨ w v<w (v-ex) ∨ w v<w (v-ey) := by
    by_cases hv : v∈latticeBox N M
    · have hstep (a : Lattice) (ha' : u v<u a) : w v<w a := by
        have hvi : u v≤B := hB ⟨v,hv,rfl⟩
        by_cases hai : a∈latticeBox N M
        · simpa [w,hv,hai] using ha'
        · simp only [w,ite_eq_left hv,ite_eq_right hai]
          have := latticeTaxicab_nonneg a
          dsimp [D]; linarith [le_max_left B c]
      exact (ha v hv).imp (hstep _) (Or.imp (hstep _) (Or.imp (hstep _) (hstep _)))
    · obtain ⟨a,ha',hai,hn⟩ := outside_box_ascent hv
      have hh : w v<w a := by simpa [w,hv,hai] using add_lt_add_left hn D
      rcases ha' with rfl|rfl|rfl|rfl
      · exact Or.inl hh
      · exact Or.inr (Or.inl hh)
      · exact Or.inr (Or.inr (Or.inl hh))
      · exact Or.inr (Or.inr (Or.inr hh))
  have he := lattice_sublevel_index hfin hne' (fun v _=>hascent v)
  intro S hS
  have hSe : hfin.toFinset=S := by
    ext v
    exact hfin.mem_toFinset.trans ((hlow v).trans (hS v).symm)
  rw [hSe] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro v hv
  apply heightIndex_congr_star
  intro a ha'
  have hai := hstar v ((hS v).mp hv).1 ((hS v).mp hv).2 a ha'
  simp [w,hai]

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.DiscreteLaplacian
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma line_hasDerivAt {u : ℂ → ℝ} {z d : ℂ} {t : ℝ}
    (hu : DifferentiableAt ℝ u (z+t•d)) :
    HasDerivAt (fun t : ℝ=>u (z+t•d)) (fderiv ℝ u (z+t•d) d) t := by
  have hl : HasDerivAt (fun t : ℝ=>z+t•d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add z
  exact hu.hasFDerivAt.comp_hasDerivAt t hl

lemma line_second_hasDerivAt {u : ℂ → ℝ} {z d : ℂ} {t : ℝ}
    (hu : ContDiffAt ℝ 2 u (z+t•d)) :
    HasDerivAt (fun t : ℝ=>fderiv ℝ u (z+t•d) d) (second u (z+t•d) d d) t := by
  have hl : HasDerivAt (fun t : ℝ=>z+t•d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add z
  have hf := (hu.fderiv_right (m:=1) (by norm_num)).differentiableAt one_ne_zero
  have hd : HasDerivAt (fun t : ℝ=>fderiv ℝ u (z+t•d))
      (fderiv ℝ (fderiv ℝ u) (z+t•d) d) t := hf.hasFDerivAt.comp_hasDerivAt t hl
  simpa only [second,map_zero,add_zero] using hd.clm_apply (hasDerivAt_const t d)

lemma centered_difference_lower {u : ℂ → ℝ} {z d : ℂ} {s a : ℝ}
    (hs : 0 ≤ s) (hu : ∀ t∈Icc (-s) s, ContDiffAt ℝ 2 u (z+t•d))
    (ha : ∀ t∈Icc (-s) s, a ≤ second u (z+t•d) d d) :
    a*s^2 ≤ u (z+s•d)+u (z-s•d)-2*u z := by
  let f : ℝ → ℝ := fun t=>u (z+t•d)-a*t^2/2
  let f' : ℝ → ℝ := fun t=>fderiv ℝ u (z+t•d) d-a*t
  let f'' : ℝ → ℝ := fun t=>second u (z+t•d) d d-a
  have hf (t : ℝ) (ht : t∈Icc (-s) s) : HasDerivAt f (f' t) t := by
    have hu' := line_hasDerivAt ((hu t ht).differentiableAt (by norm_num))
    convert hu'.sub ((((hasDerivAt_id t).pow 2).const_mul a).div_const 2) using 1 <;>
      first | rfl | (dsimp only [f',id_eq]; ring)
  have hf' (t : ℝ) (ht : t∈Icc (-s) s) : HasDerivAt f' (f'' t) t := by
    convert (line_second_hasDerivAt (hu t ht)).sub ((hasDerivAt_id t).const_mul a) using 1 <;>
      first | rfl | (simp only [f'',mul_one])
  have hc : ConvexOn ℝ (Icc (-s) s) f := convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc _ _) (fun t ht=>(hf t ht).continuousAt.continuousWithinAt)
    (fun t ht=>(hf t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht=>(hf' t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht=>sub_nonneg.mpr (ha t (interior_subset ht)))
  have he := hc.2 (show -s∈Icc (-s) s by constructor <;> linarith)
    (show s∈Icc (-s) s by constructor <;> linarith)
    (show (0:ℝ)≤1/2 by norm_num) (show (0:ℝ)≤1/2 by norm_num) (by norm_num)
  change f ((1/2:ℝ)*(-s)+1/2*s) ≤ (1/2:ℝ)*f (-s)+(1/2:ℝ)*f s at he
  have hz : (1/2:ℝ)*(-s)+1/2*s=0 := by ring
  rw [hz] at he
  simp only [f] at he
  simp only [zero_smul,add_zero,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,zero_div,sub_zero,
    neg_smul,← sub_eq_add_neg,neg_sq] at he
  nlinarith

lemma second_continuousAt {u : ℂ → ℝ} {p : ℂ} (hu : ContDiffAt ℝ 2 u p) (d : ℂ) :
    ContinuousAt (fun z=>second u z d d) p := by
  have hf := ((hu.fderiv_right (m:=1) (by norm_num)).fderiv_right (m:=0) (by norm_num)).continuousAt
  exact (hf.clm_apply continuousAt_const).clm_apply continuousAt_const

lemma positive_laplace_ascent {u : ℂ → ℝ} {p : ℂ}
    (hu : ContDiffAt ℝ 2 u p)
    (htr : 0<second u p 1 1+second u p Complex.I Complex.I) :
    ∀ᶠ q : ℝ × ℂ in 𝓝 (0,p), 0<q.1 →
      u q.2 < u (q.2+q.1•(1:ℂ)) ∨ u q.2 < u (q.2+q.1•Complex.I) ∨
      u q.2 < u (q.2-q.1•(1:ℂ)) ∨ u q.2 < u (q.2-q.1•Complex.I) := by
  let A := second u p 1 1
  let B := second u p Complex.I Complex.I
  let e := (A+B)/4
  have he : 0<e := by dsimp [e,A,B]; positivity
  have hx : ∀ᶠ z in 𝓝 p, A-e < second u z 1 1 :=
    (second_continuousAt hu 1).eventually (lt_mem_nhds (by change A-e<A; linarith))
  have hy : ∀ᶠ z in 𝓝 p, B-e < second u z Complex.I Complex.I :=
    (second_continuousAt hu Complex.I).eventually (lt_mem_nhds (by change B-e<B; linarith))
  have hh := (hu.eventually (by norm_num)).and (hx.and hy)
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hh
  have hn : ∀ᶠ q : ℝ × ℂ in 𝓝 (0,p), |q.1|<R/2 ∧ dist q.2 p<R/2 := by
    apply ((continuous_fst.norm.continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hR))).and
      ((continuous_snd.dist continuous_const).continuousAt.eventually (gt_mem_nhds (by simpa using half_pos hR))))
  filter_upwards [hn] with q hq
  intro hs
  have hpoint (d : ℂ) (hd : ‖d‖≤1) (t : ℝ) (ht : t∈Icc (-q.1) q.1) :
      ContDiffAt ℝ 2 u (q.2+t•d) ∧ A-e < second u (q.2+t•d) 1 1 ∧
        B-e < second u (q.2+t•d) Complex.I Complex.I := by
    apply hball
    rw [Metric.mem_ball]
    have ht' : |t|≤q.1 := abs_le.mpr ht
    have hb : dist (q.2+t•d) q.2≤q.1 := by
      rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs]
      exact (mul_le_mul_of_nonneg_left hd (abs_nonneg t)).trans (by simpa using ht')
    have := dist_triangle (q.2+t•d) q.2 p
    rw [abs_of_pos hs] at hq
    linarith
  have hdx := centered_difference_lower hs.le (fun t ht=>(hpoint 1 (by simp) t ht).1)
    (fun t ht=>(hpoint 1 (by simp) t ht).2.1.le)
  have hdy := centered_difference_lower hs.le (fun t ht=>(hpoint Complex.I (by simp) t ht).1)
    (fun t ht=>(hpoint Complex.I (by simp) t ht).2.2.le)
  by_contra h
  push Not at h
  have hpos : 0<(A-e+B-e)*q.1^2 := mul_pos (by dsimp [e]; linarith [htr]) (sq_pos_of_pos hs)
  nlinarith [h.1,h.2.1,h.2.2.1,h.2.2.2]

lemma compact_laplace_ascent {u : ℂ → ℝ} {K : Set ℂ}
    (hK : IsCompact K) (hu : ∀ p∈K, ContDiffAt ℝ 2 u p)
    (htr : ∀ p∈K, 0<second u p 1 1+second u p Complex.I Complex.I) :
    ∀ᶠ s in 𝓝 (0:ℝ), ∀ p∈K, 0<s →
      u p < u (p+s•(1:ℂ)) ∨ u p < u (p+s•Complex.I) ∨
      u p < u (p-s•(1:ℂ)) ∨ u p < u (p-s•Complex.I) := by
  exact hK.eventually_forall_of_forall_eventually (fun p hp=>positive_laplace_ascent (hu p hp) (htr p hp))

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.SmoothSublevelEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma scalar_floor_mesh {A s : ℝ} (hA : 0≤A) (hs : 0<s) :
    s*(⌊A/s⌋₊:ℝ)≤A ∧ A-s<s*(⌊A/s⌋₊:ℝ) := by
  constructor
  · exact by simpa only [mul_comm] using (le_div_iff₀ hs).mp (Nat.floor_le (div_nonneg hA hs.le))
  · have h := (div_lt_iff₀ hs).mp (Nat.lt_floor_add_one (A/s))
    nlinarith

lemma meshPoint_mem_latticeBox {o : ℂ} {s : ℝ} (hs : 0<s) {N M : ℕ} {v : Lattice} :
    v∈latticeBox N M ↔ |(meshPoint o s v).re-o.re|≤ s*N ∧ |(meshPoint o s v).im-o.im|≤ s*M := by
  rw [meshPoint_re,meshPoint_im,add_sub_cancel_left,add_sub_cancel_left,
    abs_mul,abs_mul,abs_of_pos hs,mul_le_mul_iff_right₀ hs,mul_le_mul_iff_right₀ hs]
  change (|(ofLex v).1|≤(N:ℤ) ∧ |(ofLex v).2|≤(M:ℤ)) ↔ _
  constructor <;> intro h <;> constructor
  · exact_mod_cast h.1
  · exact_mod_cast h.2
  · exact_mod_cast h.1
  · exact_mod_cast h.2

lemma meshBox_in_rectangle {o : ℂ} {s A B : ℝ} (hs : 0<s) (hA : 0≤A) (hB : 0≤B)
    {v : Lattice} (hv : v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊) :
    meshPoint o s v∈planeRectangle o A B := by
  have h := (meshPoint_mem_latticeBox (o:=o) hs).mp hv
  exact ⟨h.1.trans (scalar_floor_mesh hA hs).1,h.2.trans (scalar_floor_mesh hB hs).1⟩

lemma meshBox_contains_star {o : ℂ} {s A B δ : ℝ} (hs : 0<s) (hA : 0≤A) (hB : 0≤B)
    (hsmall : 3*s<δ) {v : Lattice}
    (hv : |(meshPoint o s v).re-o.re|+δ≤A ∧ |(meshPoint o s v).im-o.im|+δ≤B)
    {w : Lattice} (hw : w∈meshStar ex ey v) : w∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ := by
  apply (meshPoint_mem_latticeBox (o:=o) hs).mpr
  have hd := meshPoint_star_dist (o:=o) (s:=s) hw
  rw [abs_of_pos hs,dist_eq_norm] at hd
  have hx : |(meshPoint o s w).re-(meshPoint o s v).re|≤2*s :=
    (Complex.abs_re_le_norm ((meshPoint o s w)-(meshPoint o s v))).trans hd
  have hy : |(meshPoint o s w).im-(meshPoint o s v).im|≤2*s :=
    (Complex.abs_im_le_norm ((meshPoint o s w)-(meshPoint o s v))).trans hd
  have hxf := (scalar_floor_mesh hA hs).2
  have hyf := (scalar_floor_mesh hB hs).2
  constructor
  · have ht := abs_sub_le (meshPoint o s w).re (meshPoint o s v).re o.re
    linarith [hv.1]
  · have ht := abs_sub_le (meshPoint o s w).im (meshPoint o s v).im o.im
    linarith [hv.2]

lemma smooth_halfPlane_sublevel_index_lower {u : ℂ → ℝ} {c : ℝ}
    (hK : IsCompact {z : ℂ | 0<z.im ∧ u z≤c})
    (hne : (interior {z : ℂ | 0<z.im ∧ u z≤c}).Nonempty)
    (hu : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ 2 u z)
    (htr : ∀ z : ℂ, 0<z.im → 0<second u z 1 1+second u z Complex.I Complex.I) :
    ∃ o : ℂ, ∀ᶠ s in 𝓝 (0:ℝ), 0<s → ∀ S : Finset Lattice,
      (∀ v, v∈S ↔ 0<(meshPoint o s v).im ∧ u (meshPoint o s v)≤c) →
        1≤∑ v∈S, heightIndex (u ∘ meshPoint o s) ex ey v := by
  classical
  let K : Set ℂ := {z | 0<z.im ∧ u z≤c}
  obtain ⟨o,A,B,δ,hA,hB,hδ,hmargin,hrect⟩ := compact_halfPlane_rectangle hK
    (hne.mono interior_subset) (fun z hz=>hz.1)
  have ha := compact_laplace_ascent (compact_planeRectangle o A B)
    (fun z hz=>hu z (hrect z hz)) (fun z hz=>htr z (hrect z hz))
  have hh := meshPoint_hits_interior hne o
  refine ⟨o,?_⟩
  filter_upwards [ha,hh,gt_mem_nhds (show (0:ℝ)<δ/3 by positivity)] with s hs hsample hsmall
  intro hspos S hS
  have hcontains (v : Lattice) (hv : meshPoint o s v∈K) (w : Lattice)
      (hw : w∈meshStar ex ey v) : w∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ :=
    meshBox_contains_star hspos hA.le hB.le (by linarith) (hmargin _ hv) hw
  have hbox (v : Lattice) (hv : v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊) : meshPoint o s v∈planeRectangle o A B :=
    meshBox_in_rectangle hspos hA.le hB.le hv
  have hS' (v : Lattice) : v∈S ↔ v∈latticeBox ⌊A/s⌋₊ ⌊B/s⌋₊ ∧ (u ∘ meshPoint o s) v≤c := by
    constructor
    · intro hv
      have hv' := (hS v).mp hv
      exact ⟨hcontains v hv' v (mem_meshStar_self _ _ _),hv'.2⟩
    · intro hv
      exact (hS v).mpr ⟨hrect _ (hbox v hv.1),hv.2⟩
  apply box_sublevel_index (u:=u ∘ meshPoint o s) (c:=c) ?_ ?_ ?_ S hS'
  · obtain ⟨v,hv⟩ := hsample hspos
    exact ⟨v,hcontains v hv v (mem_meshStar_self _ _ _),hv.2⟩
  · intro v hv hvc w hw
    exact hcontains v ⟨hrect _ (hbox v hv),hvc⟩ w hw
  · intro v hv
    simpa only [Function.comp_apply,meshPoint_add,meshPoint_sub,latticeCoord_ex,latticeCoord_ey]
      using hs _ (hbox v hv) hspos

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CompactMorseEuler
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set Function Filter
open scoped Topology
namespace StrictInverseFirstPower.Grid
noncomputable section

lemma compact_halfPlane_morse_sum {u : ℂ → ℝ} {c : ℝ}
    (hK : IsCompact {z : ℂ | 0<z.im ∧ u z≤c})
    (hne : (interior {z : ℂ | 0<z.im ∧ u z≤c}).Nonempty)
    (C : Finset ℂ)
    (hc : ∀ z, 0<z.im ∧ u z≤c → (fderiv ℝ u z=0 ↔ z∈C))
    (hC : ∀ p∈C, p∈interior {z : ℂ | 0<z.im ∧ u z≤c})
    (hu : ∀ z : ℂ, 0<z.im → ContDiffAt ℝ 2 u z)
    (htr : ∀ z : ℂ, 0<z.im → 0<second u z 1 1+second u z Complex.I Complex.I)
    (hdet : ∀ p∈C, hessianDet u p≠0) :
    1≤∑ p∈C, morseSign u p := by
  classical
  obtain ⟨o,hlower⟩ := smooth_halfPlane_sublevel_index_lower hK hne hu htr
  have heq := compact_morse_index_sum hK C hc hC
    (fun z hz=>hu z hz.1) (fun z hz=>htr z (interior_subset (hC z hz)).1) hdet
  obtain ⟨s,hs,hl,he⟩ := (hlower.and heq).exists_gt
  let S := (meshPoint_bounded_preimage (o:=o) hs.ne' hK.isBounded).toFinset
  have hS : ∀ v, v∈S ↔ 0<(meshPoint o s v).im ∧ u (meshPoint o s v)≤c := by
    intro v
    exact Set.Finite.mem_toFinset _
  rw [← he hs o S hS]
  exact hl hs S hS

end
end StrictInverseFirstPower.Grid

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.CriticalCounts
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

lemma source_morse_sign {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    {z : UpperHalfPlane} (hg : criticalMap k (halfPlaneFunction f) z=ξ) :
    Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z =
      if jacobianExpression k (halfPlaneFunction f) z<0 then 1 else -1 := by
  have hz := z.im_pos
  have hF := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have hd := halfPlaneFunction_deriv_ne_zero f hz
  have hp : halfPlaneFunction f z≠ξ := fun he=>criticalMap_ne_image hk.ne' hz hd (hg.trans he.symm)
  have hpos : 0<4*(squaredReciprocalPotential k (halfPlaneFunction f) ξ z)^2*(k^4/z.im^4) := by
    rw [squaredReciprocalPotential_eq_exp hz hp]
    positivity
  unfold Grid.morseSign
  rw [squaredReciprocalPotential_hessian_det hk.ne' hz hF hd hg]
  congr 1
  apply propext
  constructor
  · intro h
    exact ((mul_pos_iff.mp h).resolve_left (fun h' =>
      (not_lt_of_gt (neg_neg_of_pos hpos)) h'.1)).2
  · intro h
    exact mul_pos_of_neg_of_neg (neg_neg_of_pos hpos) h

lemma criticalCut_morse_sum {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    ∑ z∈(goodPair_criticalCut_finite hk hg hh).toFinset,
      Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z =
        ((maximaCut k f ξ h).ncard : ℤ)-(saddleCut k f ξ h).ncard := by
  classical
  let T := (goodPair_criticalCut_finite hk hg hh).toFinset
  have hsum : (∑ z∈T, Grid.morseSign (squaredReciprocalPotential k (halfPlaneFunction f) ξ) z)=
      ∑ z∈T, if jacobianExpression k (halfPlaneFunction f) z<0 then (1:ℤ) else -1 := by
    apply Finset.sum_congr rfl
    intro z hz
    have hz' := (Set.Finite.mem_toFinset _).mp hz
    exact source_morse_sign hk hz'.1
  have hm : T.filter (fun z : UpperHalfPlane=>jacobianExpression k (halfPlaneFunction f) z<0)=
      (maximaCut_finite hk hg hh).toFinset := by
    ext z
    simp [T,maximaCut]
  have hs : T.filter (fun z : UpperHalfPlane=>¬jacobianExpression k (halfPlaneFunction f) z<0)=
      (saddleCut_finite hk hg hh).toFinset := by
    ext z
    simp only [T,Finset.mem_filter,Set.Finite.mem_toFinset,saddleCut,Set.mem_ofPred_eq]
    apply and_congr_right
    intro hz
    rw [not_lt]
    exact ⟨fun hh => lt_of_le_of_ne hh (Ne.symm (hg.2.1 z hz.1)),le_of_lt⟩
  rw [hsum,Finset.sum_ite,hm,hs]
  rw [Set.ncard_eq_toFinset_card _ (maximaCut_finite hk hg hh),Set.ncard_eq_toFinset_card _ (saddleCut_finite hk hg hh)]
  simp [sub_eq_add_neg]

lemma goodPair_superlevel_count {k : ℝ} (hk : 0<k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {h : ℝ} (hh : 0<h) :
    (saddleCut k f ξ h).ncard≤(maximaCut k f ξ h).ncard := by
  classical
  by_cases hne : (saddleCut k f ξ h).Nonempty
  · obtain ⟨a,ha,hah,hcut,hstrict⟩ := goodPair_lower_regular_cut hk hg hh
    let u := squaredReciprocalPotential k (halfPlaneFunction f) ξ
    let K : Set ℂ := {z | 0<z.im ∧ u z≤(1/a)^2}
    let T := (goodPair_criticalCut_finite hk hg hh).toFinset
    let P := (source_poles_subsingleton f ξ).finite.toFinset
    let B : Finset ℂ := T.image UpperHalfPlane.coe
    let C := B∪P
    have hT (z : UpperHalfPlane) : z∈T ↔ z∈criticalCut k f ξ h := Set.Finite.mem_toFinset _
    have hP (z : ℂ) : z∈P ↔ 0<z.im ∧ halfPlaneFunction f z=ξ := Set.Finite.mem_toFinset _
    have hK : IsCompact K := by
      change IsCompact {z : ℂ | 0<z.im ∧ squaredReciprocalPotential k (halfPlaneFunction f) ξ z≤(1/a)^2}
      rw [squaredReciprocalPotential_sublevel ha]
      exact hg.1 a ha
    have hU (z : ℂ) (hz : 0<z.im) : ContDiffAt ℝ 2 u z :=
      (squaredReciprocalPotential_contDiffAt hz
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz))).of_le (by simp)
    have htr (z : ℂ) (hz : 0<z.im) : 0<Grid.second u z 1 1+Grid.second u z I I := by
      rw [← realHessian_eq_second (hU z hz),← realHessian_eq_second (hU z hz)]
      exact squaredReciprocalPotential_laplacian_pos hk hz
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz))
        (halfPlaneFunction_deriv_ne_zero f hz)
    have hBint (z : UpperHalfPlane) (hz : z∈T) : (z:ℂ)∈interior K :=
      source_squared_interior z.im_pos (source_squared_critical_strict hk ha
        ((hT z).mp hz).1 (hstrict z ((hT z).mp hz)))
    have hCint : ∀ z∈C, z∈interior K := by
      intro z hz
      rcases Finset.mem_union.mp hz with hb|hp
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
        exact hBint w hw
      · have hp' := (hP z).mp hp
        apply source_squared_interior hp'.1
        have hu0 : u z=0 := by simp [u,squaredReciprocalPotential,hp'.2]
        change u z < (1/a)^2
        rw [hu0]
        exact sq_pos_of_pos (one_div_pos.mpr ha)
    have hc : ∀ z, z∈K → (fderiv ℝ u z=0 ↔ z∈C) := by
      intro z hz
      rw [squaredReciprocalPotential_critical_iff hk.ne' hz.1
        ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz.1))]
      constructor
      · intro hh
        rcases hh with hp|hfib
        · exact Finset.mem_union_right B ((hP z).mpr ⟨hz.1,hp⟩)
        · let w : UpperHalfPlane := ⟨z,hz.1⟩
          have hza : z∈potentialSuperlevel k (halfPlaneFunction f) ξ a := by
            rw [← squaredReciprocalPotential_sublevel ha]
            exact hz
          have hw : w∈criticalCut k f ξ a := ⟨hfib,
            (criticalHeight_superlevel hk hz.1 (halfPlaneFunction_deriv_ne_zero f hz.1) ha hfib).mp hza⟩
          rw [hcut] at hw
          exact Finset.mem_union_left P (Finset.mem_image.mpr ⟨w,(hT w).mpr hw,rfl⟩)
      · intro hzC
        rcases Finset.mem_union.mp hzC with hb|hp
        · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
          exact Or.inr ((hT w).mp hw).1
        · exact Or.inl ((hP z).mp hp).2
    have hdet : ∀ z∈C, Grid.hessianDet u z≠0 := by
      intro z hz
      have hzH := (interior_subset (hCint z hz)).1
      have hF := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hzH)
      have hd := halfPlaneFunction_deriv_ne_zero f hzH
      rcases Finset.mem_union.mp hz with hb|hp
      · obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hb
        have hw' := (hT w).mp hw
        rw [squaredReciprocalPotential_hessian_det hk.ne' hzH hF hd hw'.1]
        apply mul_ne_zero _ (hg.2.1 w hw'.1)
        apply neg_ne_zero.mpr
        have hpole : halfPlaneFunction f w≠ξ := fun he=>criticalMap_ne_image hk.ne' w.im_pos hd (hw'.1.trans he.symm)
        have hhU : 0<squaredReciprocalPotential k (halfPlaneFunction f) ξ w := by
          rw [squaredReciprocalPotential_eq_exp w.im_pos hpole]
          exact Real.exp_pos _
        positivity
      · exact (squaredReciprocalPotential_hessian_det_pole hzH hF hd ((hP z).mp hp).2).ne'
    have hneK : (interior K).Nonempty := by
      obtain ⟨z,hz⟩ := hne
      exact ⟨z,hBint z ((hT z).mpr hz.1)⟩
    have hlower := Grid.compact_halfPlane_morse_sum hK hneK C hc hCint hU htr hdet
    have hdisj : Disjoint B P := by
      apply Finset.disjoint_left.mpr
      intro z hz hp
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hz
      have hw' := (hT w).mp hw
      exact criticalMap_ne_image hk.ne' w.im_pos (halfPlaneFunction_deriv_ne_zero f w.im_pos)
        (hw'.1.trans ((hP w).mp hp).2.symm)
    have hsumB : (∑ z∈B,Grid.morseSign u z)=
        ((maximaCut k f ξ h).ncard:ℤ)-(saddleCut k f ξ h).ncard := by
      rw [Finset.sum_image (fun _ _ _ _ he=>UpperHalfPlane.coe_injective he)]
      exact criticalCut_morse_sum hk hg hh
    have hsumP : (∑ z∈P,Grid.morseSign u z)=(P.card:ℤ) := by
      have hs : (∑ z∈P, Grid.morseSign u z)=∑ _z∈P,(1:ℤ) := by
        apply Finset.sum_congr rfl
        intro z hz
        have hp := (hP z).mp hz
        have hd := squaredReciprocalPotential_hessian_det_pole (k:=k) hp.1
          ((halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hp.1))
          (halfPlaneFunction_deriv_ne_zero f hp.1) hp.2
        exact ite_eq_left hd
      rw [hs]
      simp
    have hPcard : P.card≤1 := Finset.card_le_one.mpr (by
      intro z hz w hw
      exact source_poles_subsingleton f ξ ((hP z).mp hz) ((hP w).mp hw))
    have hPcardZ : (P.card:ℤ)≤1 := by exact_mod_cast hPcard
    change 1≤∑ z∈B∪P,Grid.morseSign u z at hlower
    rw [Finset.sum_union hdisj,hsumB,hsumP] at hlower
    have hhZ : ((saddleCut k f ξ h).ncard:ℤ)≤(maximaCut k f ξ h).ncard := by omega
    exact_mod_cast hhZ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne,Set.ncard_empty]
    exact Nat.zero_le _

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

lemma exists_descendingRank_eq_of_finite {X : Type*} {v : X → ℝ} {S : Set X}
    (hS : S.Finite) (hv : InjOn v S) {n : ℕ} (hn : n < S.ncard) :
    ∃ x ∈ S, descendingRank v S x = n := by
  classical
  induction n generalizing S with
  | zero =>
    obtain ⟨m,hm,hmax⟩ := Set.exists_max_image S v hS (Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt hn))
    refine ⟨m,hm,?_⟩
    unfold descendingRank
    have he : {y | y ∈ S ∧ v m < v y} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y hy
      exact (hmax y hy.1).not_gt hy.2
    rw [he,Set.ncard_empty]
  | succ n ih =>
    obtain ⟨m,hm,hmax⟩ := Set.exists_max_image S v hS (Set.nonempty_of_ncard_ne_zero (Nat.ne_of_gt (Nat.zero_lt_of_lt hn)))
    let T := S \ {m}
    have hT : T.Finite := hS.sdiff
    have hnT : n < T.ncard := by
      have he : T.ncard + 1 = S.ncard := by
        simpa [T] using Set.ncard_sdiff_singleton_add_one hm hS
      omega
    obtain ⟨x,hx,hxrank⟩ := ih hT (hv.mono sdiff_subset) hnT
    have hxm : x ≠ m := by simpa only [T,mem_sdiff,mem_singleton_iff] using hx.2
    have hvxm : v x < v m := lt_of_le_of_ne (hmax x hx.1)
      (fun he => hxm (hv hx.1 hm he))
    have he : {y | y ∈ S ∧ v x < v y} = insert m {y | y ∈ T ∧ v x < v y} := by
      ext y
      simp only [mem_ofPred_eq,mem_insert_iff,T,mem_sdiff,mem_singleton_iff]
      constructor
      · intro hy
        by_cases hym : y = m
        · exact Or.inl hym
        · exact Or.inr ⟨⟨hy.1,hym⟩,hy.2⟩
      · rintro (rfl | hy)
        · exact ⟨hm,hvxm⟩
        · exact ⟨hy.1.1,hy.2⟩
    refine ⟨x,hx.1,?_⟩
    unfold descendingRank at hxrank ⊢
    rw [he,Set.ncard_insert_of_notMem (by simp [T]) (hT.subset (by intro y hy; exact hy.1)),hxrank]

lemma closedCut_ncard_eq_rank_succ {X : Type*} {v : X → ℝ} {S : Set X}
    (hv : InjOn v S) {x : X} (hx : x ∈ S)
    (hf : {y | y ∈ S ∧ v x ≤ v y}.Finite) :
    {y | y ∈ S ∧ v x ≤ v y}.ncard = descendingRank v S x + 1 := by
  classical
  have he : {y | y ∈ S ∧ v x ≤ v y} = insert x {y | y ∈ S ∧ v x < v y} := by
    ext y
    simp only [mem_ofPred_eq,mem_insert_iff]
    constructor
    · intro hy
      rcases eq_or_lt_of_le hy.2 with h | h
      · exact Or.inl (hv hy.1 hx h.symm)
      · exact Or.inr ⟨hy.1,h⟩
    · rintro (rfl | hy)
      · exact ⟨hx,le_rfl⟩
      · exact ⟨hy.1,hy.2.le⟩
  unfold descendingRank
  rw [he,Set.ncard_insert_of_notMem (by simp) (hf.subset (by intro y hy; exact ⟨hy.1,hy.2.le⟩))]

lemma descendingRank_closedCut {X : Type*} (v : X → ℝ) (S : Set X)
    {h : ℝ} {x : X} (hx : h ≤ v x) :
    descendingRank v {y | y ∈ S ∧ h ≤ v y} x = descendingRank v S x := by
  unfold descendingRank
  congr 1
  ext y
  constructor
  · intro hh
    exact ⟨hh.1.1,hh.2⟩
  · intro hh
    exact ⟨⟨hh.1,hx.trans hh.2.le⟩,hh.2⟩

lemma higher_partner_of_cut_domination {X : Type*} {v : X → ℝ} {A B : Set X}
    (hdisj : Disjoint A B) (hv : InjOn v (A ∪ B)) {a : X} (ha : a ∈ A)
    (hfA : {y | y ∈ A ∧ v a ≤ v y}.Finite)
    (hfB : {y | y ∈ B ∧ v a ≤ v y}.Finite)
    (hcount : {y | y ∈ A ∧ v a ≤ v y}.ncard ≤ {y | y ∈ B ∧ v a ≤ v y}.ncard) :
    ∃ b ∈ B, v a < v b ∧ descendingRank v B b = descendingRank v A a := by
  have hrank : descendingRank v A a < {y | y ∈ B ∧ v a ≤ v y}.ncard := by
    rw [closedCut_ncard_eq_rank_succ (hv.mono subset_union_left) ha hfA] at hcount
    omega
  obtain ⟨b,hb,hr⟩ := exists_descendingRank_eq_of_finite hfB
    (hv.mono (by intro x hx; exact Or.inr hx.1)) hrank
  refine ⟨b,hb.1,?_,?_⟩
  · apply lt_of_le_of_ne hb.2
    intro he
    have hab := hv (Or.inl ha) (Or.inr hb.1) he
    exact Set.disjoint_left.mp hdisj (hab ▸ ha) hb.1
  · rwa [descendingRank_closedCut v B hb.2] at hr

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

lemma sourcePair_apply (k : ℝ) (q : sourcePairingDomain k) :
    availableSource k (sourcePair k q) = q.1 := q.2.choose_spec

lemma sourcePartner_of_mem (k : ℝ) {q : DiskFamily × UpperHalfPlane}
    (hq : q ∈ sourcePairingDomain k) : sourcePartner k q = sourcePartnerOn k ⟨q,hq⟩ := by
  classical
  simp only [sourcePartner,dite_eq_left hq]

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

lemma sourcePartner_spec (k : ℝ) {f : DiskFamily} {z : UpperHalfPlane}
    (hq : (f,z) ∈ sourcePairingDomain k) :
    GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
    0 < jacobianExpression k (halfPlaneFunction f) z ∧
    jacobianExpression k (halfPlaneFunction f) (sourcePartner k (f,z)) < 0 ∧
    criticalMap k (halfPlaneFunction f) (sourcePartner k (f,z)) =
      criticalMap k (halfPlaneFunction f) z ∧
    criticalHeight k (halfPlaneFunction f) z <
      criticalHeight k (halfPlaneFunction f) (sourcePartner k (f,z)) := by
  let p := sourcePair k ⟨(f,z),hq⟩
  have hp := availableRankPartner_spec k p
  have hsource := sourcePair_apply k ⟨(f,z),hq⟩
  have hf : p.1.1.1.1 = f := congrArg Prod.fst hsource
  have hz : p.1.1.2 = z := congrArg Prod.snd hsource
  have hξ : p.1.1.1.2 = criticalMap k (halfPlaneFunction f) z := by
    rw [← hp.1.1,hf,hz]
  have hr : sourcePartner k (f,z) = availableRankPartner k p := sourcePartner_of_mem k hq
  have hg := p.1.2
  change GoodPair k (p.1.1.1.1,p.1.1.1.2) at hg
  simp only [RankPairRelation,signedCriticalFiber,mem_ofPred_eq] at hp
  rw [hf,hz,hξ] at hp
  rw [hf,hξ] at hg
  rw [hr]
  exact ⟨hg,hp.1.2,hp.2.1.2,hp.2.1.1,hp.2.2.2⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.PairingCoverage
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

lemma goodPair_rank_partner {k : ℝ} (hk : 0 < k) {f : DiskFamily} {ξ : ℂ}
    (hg : GoodPair k (f,ξ)) {z : UpperHalfPlane}
    (hz : z ∈ signedCriticalFiber k f ξ true) :
    ∃ w, RankPairRelation k ⟨((f,ξ),z),hg⟩ w := by
  let v := fun w : UpperHalfPlane => criticalHeight k (halfPlaneFunction f) w
  let A := signedCriticalFiber k f ξ true
  let B := signedCriticalFiber k f ξ false
  have hdisj : Disjoint A B := by
    apply Set.disjoint_left.mpr
    intro w ha hb
    exact (not_lt_of_gt ha.2) hb.2
  have hv : InjOn v (A ∪ B) := (goodPair_criticalHeight_injOn hg).mono (by
    intro w hw
    rcases hw with hw | hw <;> exact hw.1)
  have hA : {w | w ∈ A ∧ v z ≤ v w} = saddleCut k f ξ (v z) := by
    ext w
    change ((_ = _ ∧ 0 < _) ∧ _ ≤ _) ↔ ((_ = _ ∧ _ ≤ _) ∧ 0 < _)
    tauto
  have hB : {w | w ∈ B ∧ v z ≤ v w} = maximaCut k f ξ (v z) := by
    ext w
    change ((_ = _ ∧ _ < 0) ∧ _ ≤ _) ↔ ((_ = _ ∧ _ ≤ _) ∧ _ < 0)
    tauto
  have hp : 0 < v z := criticalHeight_pos hk z.im_pos (halfPlaneFunction_deriv_ne_zero f z.im_pos)
  have hfinA : {w | w ∈ A ∧ v z ≤ v w}.Finite := by
    rw [hA]
    exact saddleCut_finite hk hg hp
  have hfinB : {w | w ∈ B ∧ v z ≤ v w}.Finite := by
    rw [hB]
    exact maximaCut_finite hk hg hp
  have hcount : {w | w ∈ A ∧ v z ≤ v w}.ncard ≤ {w | w ∈ B ∧ v z ≤ v w}.ncard := by
    rw [hA,hB]
    exact goodPair_superlevel_count hk hg hp
  obtain ⟨w,hw,hh,hr⟩ := higher_partner_of_cut_domination hdisj hv hz hfinA hfinB hcount
  exact ⟨w,hz,hw,hr,hh⟩

lemma sourcePairingDomain_eq_good_positive {k : ℝ} (hk : 0 < k)
    (f : DiskFamily) (z : UpperHalfPlane) :
    (f,z) ∈ sourcePairingDomain k ↔
      GoodPair k (f,criticalMap k (halfPlaneFunction f) z) ∧
        0 < jacobianExpression k (halfPlaneFunction f) z := by
  constructor
  · intro hz
    exact ⟨(sourcePartner_spec k hz).1,(sourcePartner_spec k hz).2.1⟩
  · rintro ⟨hg,hJ⟩
    apply (sourcePairingDomain_iff k f z).mpr
    exact ⟨hg,goodPair_rank_partner hk hg ⟨rfl,hJ⟩⟩

end
end StrictInverseFirstPower

end

end OAI
end

section
-- module Solutions.OAIQW_StrictInverseFirstPower.FiberSum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open Set MeasureTheory
open scoped ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma fiberSum_iUnion {X Y I : Type*} (G : X → Y) (s : I → Set X) (h : X → ℝ≥0∞)
    (hd : Pairwise (fun i j => Disjoint (s i) (s j))) (ξ : Y) :
    fiberSum G (⋃ i, s i) h ξ = ∑' i, fiberSum G (s i) h ξ := by
  unfold fiberSum
  have he : {z | z ∈ ⋃ i, s i ∧ G z = ξ} = ⋃ i, {z | z ∈ s i ∧ G z = ξ} := by
    ext z
    simp only [mem_ofPred_eq,mem_iUnion]
    tauto
  rw [he]
  apply ENNReal.tsum_biUnion
  intro i _ j _ hij
  exact (hd hij).mono (fun _ hz => hz.1) (fun _ hz => hz.1)

lemma fiberSum_eq_single {X Y : Type*} {G : X → Y} {s : Set X} {h : X → ℝ≥0∞}
    (hi : InjOn G s) {z : X} (hz : z ∈ s) : fiberSum G s h (G z) = h z := by
  unfold fiberSum
  apply tsum_eq_single (⟨z,hz,rfl⟩ : {w | w ∈ s ∧ G w = G z})
  intro w hw
  exact False.elim (hw (Subtype.ext (hi w.2.1 hz w.2.2)))

lemma fiberSum_eq_zero_of_not_mem_image {X Y : Type*} {G : X → Y} {s : Set X}
    {h : X → ℝ≥0∞} {ξ : Y} (hξ : ξ ∉ G '' s) : fiberSum G s h ξ = 0 := by
  have : IsEmpty {z | z ∈ s ∧ G z = ξ} := ⟨fun z => hξ ⟨z,z.2.1,z.2.2⟩⟩
  simp [fiberSum]

lemma fiberSum_eq_indicator_inverse {X Y : Type*} {G : X → Y} {s : Set X}
    (hi : InjOn G s) (h : X → ℝ≥0∞) (φ : Y → X) (hφ : ∀ z ∈ s, φ (G z) = z) :
    fiberSum G s h = (G '' s).indicator (fun ξ => h (φ ξ)) := by
  classical
  funext ξ
  by_cases hξ : ξ ∈ G '' s
  · obtain ⟨z,hz,rfl⟩ := hξ
    rw [fiberSum_eq_single hi hz,indicator_of_mem (mem_image_of_mem G hz),hφ z hz]
  · rw [fiberSum_eq_zero_of_not_mem_image hξ,indicator_of_notMem hξ]

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
namespace StrictInverseFirstPower
noncomputable section

lemma chart_measurable_fiberSum {G : ℂ → ℂ} (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s) (hse : s ⊆ e.source)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) : Measurable (fiberSum G s h) := by
  classical
  have him : MeasurableSet (G '' s) := by
    rw [← he]
    exact hs.image_of_continuousOn_injOn (e.continuousOn.mono hse) (e.injOn.mono hse)
  let φ := e.target.piecewise e.symm (fun _ => 0)
  have hφ : Measurable φ := e.continuousOn_symm.measurable_piecewise
    continuousOn_const e.open_target.measurableSet
  have hinv : ∀ z ∈ s, φ (G z) = z := by
    intro z hz
    rw [show G z = e z from congrFun he.symm z]
    simp only [φ, piecewise_eq_of_mem _ _ _ (e.map_source (hse hz)), e.left_inv (hse hz)]
  rw [fiberSum_eq_indicator_inverse (he ▸ e.injOn.mono hse) h φ hinv]
  exact (hh.comp hφ).indicator him

lemma chart_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) (e : OpenPartialHomeomorph ℂ ℂ)
    (he : (e : ℂ → ℂ) = G) {s : Set ℂ} (hs : MeasurableSet s)
    (hsU : s ⊆ U) (hse : s ⊆ e.source) (h : ℂ → ℝ≥0∞) :
    ∫⁻ ξ, fiberSum G s h ξ =
      ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  have hinv : ∀ z ∈ s, e.symm (G z) = z := by
    intro z hz
    rw [← he]
    exact e.left_inv (hse hz)
  have hi : InjOn G s := he ▸ e.injOn.mono hse
  have hf : ∀ z ∈ s, HasFDerivWithinAt G (fderiv ℝ G z) s z := by
    intro z hz
    exact ((hG.contDiffAt (hU.mem_nhds (hsU hz))).differentiableAt one_ne_zero).hasFDerivAt.hasFDerivWithinAt
  have him := measurable_image_of_fderivWithin hs hf hi
  rw [fiberSum_eq_indicator_inverse hi h e.symm hinv,lintegral_indicator him]
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hf hi]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hs] with z hz
  rw [hinv z hz]

lemma regular_area_formula {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hG : ContDiffOn ℝ 1 G U) {s : Set ℂ} (hs : MeasurableSet s)
    (hsR : s ⊆ {z ∈ U | (fderiv ℝ G z).det ≠ 0})
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    Measurable (fiberSum G s h) ∧
      ∫⁻ ξ, fiberSum G s h ξ = ∫⁻ z in s, ENNReal.ofReal |(fderiv ℝ G z).det| * h z := by
  classical
  obtain ⟨C,hC,hchart,hcov⟩ := countable_regular_inverse_charts hU hG
  by_cases hn : C.Nonempty
  · obtain ⟨e,he⟩ := hC.exists_eq_range hn
    have hem (n : ℕ) : e n ∈ C := he ▸ mem_range_self n
    let A (n : ℕ) := s ∩ (e n).source
    let B := disjointed A
    have hmA (n : ℕ) : MeasurableSet (A n) := hs.inter (e n).open_source.measurableSet
    have hmB (n : ℕ) : MeasurableSet (B n) := MeasurableSet.disjointed hmA n
    have hbA (n : ℕ) : B n ⊆ A n := disjointed_le A n
    have hbE (n : ℕ) : B n ⊆ (e n).source := (hbA n).trans inter_subset_right
    have hbS (n : ℕ) : B n ⊆ s := (hbA n).trans inter_subset_left
    have hbs : (⋃ n, B n) = s := by
      rw [iUnion_disjointed]
      apply Subset.antisymm
      · exact iUnion_subset (fun n => inter_subset_left)
      · intro z hz
        obtain ⟨c,hc,hzc⟩ := mem_iUnion₂.mp (hcov (hsR hz))
        obtain ⟨n,rfl⟩ := he ▸ hc
        exact mem_iUnion.mpr ⟨n,hz,hzc⟩
    have hmb (n : ℕ) : Measurable (fiberSum G (B n) h) :=
      chart_measurable_fiberSum (e n) (hchart _ (hem n)).1 (hmB n) (hbE n) hh
    have heq : fiberSum G s h = fun ξ => ∑' n, fiberSum G (B n) h ξ := by
      funext ξ
      rw [← hbs]
      exact fiberSum_iUnion G B h (disjoint_disjointed A) ξ
    refine ⟨heq ▸ .tsum hmb,?_⟩
    rw [heq,lintegral_tsum (fun n => (hmb n).aemeasurable)]
    simp_rw [chart_area_formula hU hG _ (hchart _ (hem _)).1 (hmB _)
      ((hbS _).trans (fun z hz => (hsR hz).1)) (hbE _)]
    rw [← lintegral_iUnion (fun n => hmB n) (disjoint_disjointed A),hbs]
  · have hs0 : s = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro z hz
      obtain ⟨e,he,_⟩ := mem_iUnion₂.mp (hcov (hsR hz))
      exact hn ⟨e,he⟩
    subst s
    have he : fiberSum G ∅ h = 0 := by ext ξ; simp [fiberSum]
    rw [he]
    exact ⟨measurable_const, by simp⟩

end
end StrictInverseFirstPower

open Set Filter Metric Complex MeasureTheory
open scoped Topology ENNReal
namespace StrictInverseFirstPower
noncomputable section

lemma continuous_unsignedTargetWeight (β : ℝ) :
    Continuous (fun p : DiskFamily × UpperHalfPlane => unsignedTargetWeight β p.1 p.2) := by
  exact ENNReal.continuous_ofReal.comp (((UpperHalfPlane.continuous_im.comp continuous_snd).rpow_const
    (fun p => Or.inl p.2.im_ne_zero)).mul (continuous_halfPlaneQ.norm.pow 3))

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

lemma measurableSet_signedJacobianLocus (k : ℝ) (f : DiskFamily) (positive : Bool) :
    MeasurableSet (signedJacobianLocus k f positive) := by
  have hc : Continuous (fun z : UpperHalfPlane => (f,z)) := continuous_const.prodMk continuous_id
  have hm := (continuous_jacobianExpression_upper k).comp hc
  have hs : MeasurableSet {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    cases positive
    · change MeasurableSet {z : UpperHalfPlane | jacobianExpression k (halfPlaneFunction f) z < 0}
      exact measurableSet_lt hm.measurable measurable_const
    · change MeasurableSet {z : UpperHalfPlane | 0 < jacobianExpression k (halfPlaneFunction f) z}
      exact measurableSet_lt measurable_const hm.measurable
  have he : signedJacobianLocus k f positive = UpperHalfPlane.coe '' {z : UpperHalfPlane | if positive then
      0 < jacobianExpression k (halfPlaneFunction f) z else
      jacobianExpression k (halfPlaneFunction f) z < 0} := by
    ext z
    constructor
    · intro hz
      refine ⟨⟨z,hz.1⟩,?_,rfl⟩
      exact hz.2
    · rintro ⟨w,hw,rfl⟩
      exact ⟨w.im_pos,hw⟩
  rw [he]
  exact UpperHalfPlane.measurableEmbedding_coe.measurableSet_image.mpr hs

lemma criticalMap_det_eq (k : ℝ) (hk : k ≠ 0) (f : DiskFamily) {z : ℂ} (hz : 0 < z.im) :
    (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det =
      ‖deriv (halfPlaneFunction f) z‖^2 * jacobianExpression k (halfPlaneFunction f) z := by
  have ha := (halfPlaneFunction_differentiableOn f).analyticAt (isOpen_halfPlane.mem_nhds hz)
  have he := normalizedJacobian_eq hk ha.differentiableAt ha.deriv.differentiableAt
    (halfPlaneFunction_deriv_ne_zero f hz)
  exact (div_eq_iff (pow_ne_zero 2 (norm_ne_zero_iff.mpr
    (halfPlaneFunction_deriv_ne_zero f hz)))).mp he |>.trans (mul_comm _ _)

lemma sourceMassDensity_eq_targetWeight_det {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily)
    (positive : Bool) {z : ℂ} (hz : z ∈ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive ⟨z,hz.1⟩ =
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        unsignedTargetWeight β f ⟨z,hz.1⟩ := by
  have hJ : jacobianPart k f positive ⟨z,hz.1⟩ = |jacobianExpression k (halfPlaneFunction f) z| := by
    cases positive
    · simp only [signedJacobianLocus,Bool.false_eq_true,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,Bool.false_eq_true,↓reduceIte,max_eq_left (neg_nonneg.mpr hz.2.le),
        abs_of_neg hz.2]
    · simp only [signedJacobianLocus,↓reduceIte,mem_ofPred_eq] at hz
      simp only [jacobianPart,↓reduceIte,max_eq_left hz.2.le,abs_of_pos hz.2]
  have hd : ‖deriv (halfPlaneFunction f) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (halfPlaneFunction_deriv_ne_zero f hz.1)
  rw [sourceMassDensity,unsignedTargetWeight,hJ,criticalMap_det_eq k hk f hz.1,
    ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  simp only [halfPlaneQ,norm_inv,abs_mul,abs_pow,abs_norm]
  field_simp

lemma sourceMassDensity_zero_of_not_sign {β k : ℝ} (f : DiskFamily) (positive : Bool)
    (z : UpperHalfPlane) (hz : (z:ℂ) ∉ signedJacobianLocus k f positive) :
    sourceMassDensity β k f positive z = 0 := by
  have hp : jacobianPart k f positive z = 0 := by
    cases positive
    · have hJ : 0 ≤ jacobianExpression k (halfPlaneFunction f) z := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,Bool.false_eq_true,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right (neg_nonpos.mpr hJ)
    · have hJ : jacobianExpression k (halfPlaneFunction f) z ≤ 0 := by
        simpa only [signedJacobianLocus,mem_ofPred_eq,↓reduceIte,
          UpperHalfPlane.coe_im, and_iff_right z.im_pos,not_lt] using hz
      exact max_eq_right hJ
  simp [sourceMassDensity,hp]

lemma source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : ℂ → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z in {z : ℂ | 0 < z.im}, h z * sourceMassDensity β k f positive (halfPlaneProjection z)) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hreg : signedJacobianLocus k f positive ⊆
      {z ∈ {z : ℂ | 0 < z.im} | (fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det ≠ 0} := by
    intro z hz
    refine ⟨hz.1, (not_congr (jacobianExpression_zero_iff k hk f hz.1)).mp ?_⟩
    cases positive
    · exact ne_of_lt hz.2
    · exact ne_of_gt hz.2
  have hG : ContDiffOn ℝ 1 (criticalMap k (halfPlaneFunction f)) {z : ℂ | 0 < z.im} := by
    intro z hz
    exact (criticalMap_contDiffAt k f hz).contDiffWithinAt.of_le (by norm_num)
  have ht : Measurable (fun z => h z * unsignedTargetWeight β f (halfPlaneProjection z)) := hh.mul
    ((continuous_unsignedTargetWeight β).measurable.comp (measurable_const.prodMk measurable_halfPlaneProjection))
  rw [(regular_area_formula isOpen_halfPlane hG (measurableSet_signedJacobianLocus k f positive) hreg ht).2]
  have he : (∫⁻ z in signedJacobianLocus k f positive,
      ENNReal.ofReal |(fderiv ℝ (criticalMap k (halfPlaneFunction f)) z).det| *
        (h z * unsignedTargetWeight β f (halfPlaneProjection z))) =
      ∫⁻ z in signedJacobianLocus k f positive,
        h z * sourceMassDensity β k f positive (halfPlaneProjection z) := by
    apply setLIntegral_congr_fun (measurableSet_signedJacobianLocus k f positive)
    intro z hz
    dsimp only
    rw [halfPlaneProjection_of_pos hz.1,sourceMassDensity_eq_targetWeight_det hk f positive hz]
    ring
  rw [he,← lintegral_indicator (measurableSet_signedJacobianLocus k f positive),
    ← lintegral_indicator isOpen_halfPlane.measurableSet]
  apply lintegral_congr
  intro z
  by_cases hz : 0 < z.im
  · rw [indicator_of_mem (show z ∈ {z : ℂ | 0 < z.im} from hz)]
    by_cases hs : z ∈ signedJacobianLocus k f positive
    · rw [indicator_of_mem hs]
    · rw [indicator_of_notMem hs,halfPlaneProjection_of_pos hz,
        sourceMassDensity_zero_of_not_sign f positive ⟨z,hz⟩ hs,mul_zero]
  · rw [indicator_of_notMem (show z ∉ {z : ℂ | 0 < z.im} from hz),
      indicator_of_notMem (show z ∉ signedJacobianLocus k f positive from fun hs => hz hs.1)]

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

lemma upperArea_lintegral {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z ∂upperArea) = ∫⁻ z in {z : ℂ | 0 < z.im}, h (halfPlaneProjection z) := by
  have he := coe_upperArea_preserving.lintegral_comp (hh.comp measurable_halfPlaneProjection)
  have hp (z : UpperHalfPlane) : halfPlaneProjection z = z := by
    rw [halfPlaneProjection_of_pos z.im_pos]
  simpa only [Function.comp_apply,hp] using he

lemma upper_source_area_formula {β k : ℝ} (hk : k ≠ 0) (f : DiskFamily) (positive : Bool)
    {h : UpperHalfPlane → ℝ≥0∞} (hh : Measurable h) :
    (∫⁻ z, h z * sourceMassDensity β k f positive z ∂upperArea) =
      ∫⁻ ξ, fiberSum (criticalMap k (halfPlaneFunction f)) (signedJacobianLocus k f positive)
        (fun z => h (halfPlaneProjection z) * unsignedTargetWeight β f (halfPlaneProjection z)) ξ := by
  have hm : Measurable (fun z => h z * sourceMassDensity β k f positive z) :=
    hh.mul ((continuous_sourceMassDensity β k positive).measurable.comp
      (measurable_const.prodMk measurable_id))
  rw [upperArea_lintegral hm]
  exact source_area_formula hk f positive (hh.comp measurable_halfPlaneProjection)

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

lemma measurable_badSourceTest {k : ℝ} (hk : 0 < k) : Measurable (badSourceTest k) :=
  measurable_const.indicator (measurableSet_sourcePairingDomain hk).compl

lemma good_targets_bad_source_mass_zero_oai {β k : ℝ} (hk : 0 < k) (f : DiskFamily)
    (hg : ∀ᵐ ξ : ℂ, GoodPair k (f,ξ)) :
    (∫⁻ z, sourceMassDensity β k f true z * badSourceTest k (f,z) ∂upperArea) = 0 := by
  have hm : Measurable (fun z : UpperHalfPlane => badSourceTest k (f,z)) :=
    (measurable_badSourceTest hk).comp (measurable_const.prodMk measurable_id)
  simp_rw [mul_comm (sourceMassDensity β k f true _) (badSourceTest k _)]
  rw [upper_source_area_formula hk.ne' f true hm]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with ξ hξ
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hz := z.2.1
  have hp : 0 < z.1.im := hz.1
  have hD : (f,halfPlaneProjection z.1)∈sourcePairingDomain k := by
    rw [halfPlaneProjection_of_pos hp,sourcePairingDomain_eq_good_positive hk]
    refine ⟨?_,hz.2⟩
    rw [z.2.2]
    exact hξ
  simp [badSourceTest,hD]

end
end StrictInverseFirstPower

end

end OAI
end

theorem solution : type_of% @OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero_oai := @OAI.StrictInverseFirstPower.good_targets_bad_source_mass_zero_oai
