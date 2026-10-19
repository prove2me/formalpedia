-- Prove2me | solution 1 for OAI.Brennan.main_theorem
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T20:27:31.175995+00:00
-- url     : https://prove2.me/submissions/a99a0e66-dcbb-44e4-b0f3-b1627fcefb4b

import Mathlib
import Definitions.Def_Brennan
import Definitions.Def_OAIQWBRNK000
import Definitions.Def_OAIQWBRN000
import Theorems.Thm_OAI_Brennan_univalent_growth_upper
import Theorems.Thm_OAI_Brennan_jacobian_expectation_nonpos

section
-- module Solutions.OAIQW_Brennan.HalfPlane
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma affine_assoc (z w u : ℂ) : affine (affine z w) u = affine z (affine w u) := by
  apply Complex.ext <;> simp [affine, Complex.mul_re, Complex.mul_im] <;> ring

lemma reroot_comp {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    reroot (reroot f z) w = reroot f (affine z w) := by
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hv : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  have hdf : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hdg : deriv f (affine z w) ≠ 0 :=
    univalent_deriv_ne_zero isOpen_halfPlane hf (affine_mem hz hw)
  funext u
  have him : ((affine z w).im : ℂ) = (z.im : ℂ) * (w.im : ℂ) := by
    simp [affine]
  change (reroot f z (affine w u) - reroot f z w) /
    ((w.im : ℂ) * deriv (reroot f z) w) = _
  rw [deriv_reroot hf hz hw]
  simp only [reroot, affine_assoc, him]
  field_simp
  ring

lemma reciprocalDeriv_reroot {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z w : ℂ} (hz : z ∈ halfPlane) (hw : w ∈ halfPlane) :
    reciprocalDeriv (reroot f z) w = reciprocalDeriv f (affine z w) / reciprocalDeriv f z := by
  simp [reciprocalDeriv, deriv_reroot hf hz hw, div_eq_mul_inv, mul_comm]

lemma rerootClass_comp (g : DiskClass) (z w : halfPlane) :
    rerootClass (rerootClass g z) w = rerootClass g ⟨affine z w,affine_mem z.2 w.2⟩ := by
  apply class_ext
  intro u hu
  rw [classFun_rerootClass _ _ hu,reroot_congr (classFun_rerootClass g z) w.2 hu,
    reroot_comp (classFun_schlicht g).1 z.2 w.2,classFun_rerootClass _ _ hu]

lemma classWeight_cocycle (g : DiskClass) (z w : halfPlane) :
    classWeight g z * classWeight (rerootClass g z) w =
      classWeight g ⟨affine z w,affine_mem z.2 w.2⟩ := by
  have he := (classFun_rerootClass g z).deriv isOpen_halfPlane w.2
  have hq : reciprocalDeriv (classFun (rerootClass g z)) w =
      reciprocalDeriv (reroot (classFun g) z) w := congrArg Inv.inv he
  simp only [classWeight,hq,reciprocalDeriv_reroot (classFun_schlicht g).1 z.2 w.2,norm_div,div_pow]
  have hn : ‖reciprocalDeriv (classFun g) z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (inv_ne_zero
      (univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht g).1 z.2))
  field_simp

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CriticalMap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma logarithmicJet_eq {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) :
    logarithmicJet f z = -Complex.I * (z.im : ℂ) * deriv (deriv f) z / deriv f z := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hq : deriv (reciprocalDeriv f) z = -deriv (deriv f) z / (deriv f z)^2 :=
    (han.deriv.differentiableAt.hasDerivAt.inv hd).deriv
  rw [logarithmicJet, hq, reciprocalDeriv]
  field_simp

lemma fderiv_criticalMap_apply {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (v : ℂ) :
    fderiv ℝ (criticalMap f k) z v = deriv f z * v -
      Complex.I / (k : ℂ) * ((v.im : ℂ) * deriv f z +
        (z.im : ℂ) * (deriv (deriv f) z * v)) := by
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_halfPlane z hz
  have ha := han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hb := han.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hG := ha.sub ((hc.const_mul (Complex.I / (k : ℂ))).mul hb)
  have hG' : HasFDerivAt (criticalMap f k)
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv f z)) -
        ((Complex.I / (k : ℂ) * (z.im : ℂ)) •
          ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv f) z)) +
        deriv f z • (Complex.I / (k : ℂ)) •
          (Complex.ofRealCLM.comp Complex.imCLM))) z := hG
  rw [hG'.fderiv]
  change v * deriv f z -
    ((Complex.I / (k : ℂ) * (z.im : ℂ)) * (v * deriv (deriv f) z) +
      deriv f z * (Complex.I / (k : ℂ) * (v.im : ℂ))) = _
  ring

lemma criticalMap_columns {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    fderiv ℝ (criticalMap f k) z 1 = deriv f z / (k : ℂ) * ((k : ℂ) + logarithmicJet f z) ∧
    fderiv ℝ (criticalMap f k) z Complex.I =
      Complex.I * (deriv f z / (k : ℂ)) * ((k : ℂ) - 1 + logarithmicJet f z) := by
  have hd : deriv f z ≠ 0 := univalent_deriv_ne_zero isOpen_halfPlane hf hz
  have hk' : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  constructor <;> rw [fderiv_criticalMap_apply hf hz, logarithmicJet_eq hf hz] <;>
    simp only [Complex.one_im, Complex.I_im, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, one_mul, mul_one, zero_add] <;> field_simp <;> ring

lemma critical_columns_det (u q : ℂ) (k : ℝ) :
    (u * ((k : ℂ) + q)).re * (Complex.I * u * ((k : ℂ) - 1 + q)).im -
      (Complex.I * u * ((k : ℂ) - 1 + q)).re * (u * ((k : ℂ) + q)).im =
    ‖u‖^2 * (k * (k-1) + (2*k-1)*q.re + ‖q‖^2) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring

lemma normalizedJacobian_formula {f : ℂ → ℂ} (hf : UnivalentOn f halfPlane)
    {z : ℂ} (hz : z ∈ halfPlane) (k : ℝ) (hk : k ≠ 0) :
    k^2 * normalizedJacobian f k z =
      k * (k - 1) + (2*k - 1) * (logarithmicJet f z).re + ‖logarithmicJet f z‖^2 := by
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane hf hz)
  obtain ⟨hc₁, hc₂⟩ := criticalMap_columns hf hz k hk
  rw [normalizedJacobian, determinant_complex_real]
  change k ^ 2 * (((fderiv ℝ (criticalMap f k) z 1).re *
    (fderiv ℝ (criticalMap f k) z Complex.I).im -
    (fderiv ℝ (criticalMap f k) z Complex.I).re *
    (fderiv ℝ (criticalMap f k) z 1).im) / ‖deriv f z‖^2) = _
  rw [hc₁, hc₂, critical_columns_det, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  field_simp

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TraceIdentity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma traceFlux_contDiffAt {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    ContDiffAt ℝ 1 (traceFluxX g ε) p ∧ ContDiffAt ℝ 1 (traceFluxY g ε) p := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ g) p := hg.fderiv_right (by norm_num)
  have htr : ContDiffAt ℝ 1 g p := hg.of_le (by norm_num)
  constructor
  · unfold traceFluxX; fun_prop
  · unfold traceFluxY; fun_prop

lemma divergence_traceFlux {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    fderiv ℝ (traceFluxX g ε) p (1,0)+fderiv ℝ (traceFluxY g ε) p (0,1) =
      (p.2-ε)*pairLaplacian g p := by
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) p)
  have hy := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) p)
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2-ε) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub_const ε
  unfold traceFluxX traceFluxY
  have hfx := (hs.mul hx).fderiv
  have hfy := ((hs.mul hy).sub hdg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (1,0)) p = _ at hfx
  change fderiv ℝ (fun p => (p.2-ε)*fderiv ℝ g p (0,1)-g p) p = _ at hfy
  rw [hfx,hfy]
  simp [pairLaplacian,ContinuousLinearMap.flip_apply,mul_add]

lemma continuousAt_pairLaplacian {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) : ContinuousAt (pairLaplacian g) p := by
  have hh : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ g)) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuousAt
  unfold pairLaplacian
  fun_prop

lemma secondReal_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : ContDiffAt ℝ 2 F z) (u v : ℂ) :
    secondReal (ψ ∘ F) z u v =
      fderiv ℝ ψ (F z) (complexSecondReal F z u v) +
      secondReal ψ (F z) (fderiv ℝ F z u) (fderiv ℝ F z v) := by
  have hdψ := hψ.differentiableAt (by norm_num)
  have hdF := hF.differentiableAt (by norm_num)
  have hddψ := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hddF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (ψ ∘ F) =ᶠ[𝓝 z] fun w =>
      (fderiv ℝ ψ (F w)).comp (fderiv ℝ F w) := by
    filter_upwards [hF.eventually (by simp),hdF.continuousAt.eventually (hψ.eventually (by simp))] with w hFw hψw
    exact fderiv_comp w (hψw.differentiableAt (by norm_num)) (hFw.differentiableAt (by norm_num))
  have hh := ((hddψ.hasFDerivAt.comp z hdF.hasFDerivAt).clm_comp hddF.hasFDerivAt).congr_of_eventuallyEq he
  rw [secondReal,hh.fderiv]
  simp [secondReal,complexSecondReal,ContinuousLinearMap.compL_apply]

lemma bilinear_complex_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c*Complex.I) (c*Complex.I) = ‖c‖^2*(B 1 1+B Complex.I Complex.I) := by
  have hc : c = c.re • (1 : ℂ)+c.im • Complex.I := by simp
  have hci : c*Complex.I = (-c.im) • (1 : ℂ)+c.re • Complex.I := by
    apply Complex.ext <;> simp [Complex.mul_re,Complex.mul_im]
  have hn : ‖c‖^2 = c.re^2+c.im^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply,pow_two]
  rw [hci,hc]
  simp only [map_add,map_smul,add_apply,smul_apply,smul_eq_mul]
  rw [← hc,hn]
  ring

lemma laplacian_eq_secondReal (f : ℂ → ℝ) (z : ℂ) :
    Laplacian.laplacian f z = secondReal f z 1 1+secondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,secondReal]

lemma laplacian_eq_complexSecondReal (f : ℂ → ℂ) (z : ℂ) :
    Laplacian.laplacian f z = complexSecondReal f z 1 1+complexSecondReal f z Complex.I Complex.I := by
  simp [laplacian_eq_iteratedFDeriv_complexPlane,iteratedFDeriv_two_apply,complexSecondReal]

lemma fderiv_real_complex_apply {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) : fderiv ℝ F z v = deriv F z*v := by
  rw [(hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [smul_eq_mul,mul_comm]

lemma laplacian_holomorphic_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : AnalyticAt ℂ F z) :
    Laplacian.laplacian (ψ ∘ F) z = ‖deriv F z‖^2*Laplacian.laplacian ψ (F z) := by
  rw [laplacian_eq_secondReal,secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ),
    secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ)]
  have hz := hF.harmonicAt.2.eq_of_nhds
  rw [laplacian_eq_complexSecondReal] at hz
  change complexSecondReal F z 1 1+complexSecondReal F z Complex.I Complex.I = 0 at hz
  have he : fderiv ℝ ψ (F z) (complexSecondReal F z 1 1)+
      fderiv ℝ ψ (F z) (complexSecondReal F z Complex.I Complex.I) = 0 := by
    rw [← map_add,hz,map_zero]
  simp only [fderiv_real_complex_apply hF.differentiableAt,mul_one]
  have hb := bilinear_complex_rotation (fderiv ℝ (fderiv ℝ ψ) (F z)) (deriv F z)
  rw [laplacian_eq_secondReal]
  dsimp only [secondReal] at *
  linarith

lemma pairLaplacian_complex (f : ℂ → ℝ) (p : ℝ × ℝ) :
    pairLaplacian (f ∘ Complex.equivRealProdCLM.symm) p =
      Laplacian.laplacian f (Complex.equivRealProdCLM.symm p) := by
  have he := Complex.equivRealProdCLM.symm.iteratedFDerivWithin_comp_right
    f (s := univ) uniqueDiffOn_univ (mem_univ (Complex.equivRealProdCLM.symm p)) 2
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  have h₁ := congrArg (fun B => B ![((1,0) : ℝ × ℝ),(1,0)]) he
  have h₂ := congrArg (fun B => B ![((0,1) : ℝ × ℝ),(0,1)]) he
  simp only [iteratedFDeriv_two_apply,ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,ContinuousLinearEquiv.coe_coe] at h₁ h₂
  have hc₁ : Complex.equivRealProdCLM.symm (1,0) = 1 := by simp [Complex.equivRealProdCLM_symm_apply]
  have hc₂ : Complex.equivRealProdCLM.symm (0,1) = Complex.I := by simp [Complex.equivRealProdCLM_symm_apply]
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  rw [pairLaplacian,h₁,h₂,laplacian_eq_secondReal]
  rfl

lemma conformal_lintegral_le {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) ≤ ∫⁻ w, b w := by
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b
  have hh : (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z)) = ∫⁻ w in F '' s, b w := by
    rw [he]
    apply setLIntegral_congr_fun hs
    intro z hz
    have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
    have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
    dsimp only
    rw [hf]
    have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
    rw [hd',abs_of_nonneg (sq_nonneg _)]
  rw [hh]
  exact lintegral_mono' Measure.restrict_le_self le_rfl

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TransferOperator
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun

lemma halfPoint_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    halfMul (halfPoint x y hy) (halfPoint u v hv) = halfPoint (x+y*u) (y*v) (mul_pos hy hv) := by
  apply Subtype.ext
  apply Complex.ext <;> simp [halfMul,halfPoint,affine]

lemma rerootClass_one (g : DiskClass) : rerootClass g halfOne = g := by
  apply class_ext
  intro z hz
  rw [classFun_rerootClass _ _ hz]
  simp [reroot,halfOne,(classFun_schlicht g).2.1,(classFun_schlicht g).2.2]

lemma classWeight_one (g : DiskClass) : classWeight g halfOne = 1 := by
  simp [classWeight,reciprocalDeriv,halfOne,(classFun_schlicht g).2.2]

attribute [local irreducible] rerootClass

lemma affineOperator_mul (z w : halfPlane) :
    affineOperator z * affineOperator w = affineOperator (halfMul z w) := by
  ext f g
  change classWeight g z * (classWeight (rerootClass g z) w * f (rerootClass (rerootClass g z) w)) = _
  rw [← mul_assoc,classWeight_cocycle,rerootClass_comp]
  rfl

lemma affineOperator_one : affineOperator halfOne = 1 := by
  ext f g
  simp only [affineOperator_apply,classWeight_one,rerootClass_one,one_mul]
  rfl

lemma affineOperator_norm_le {z : halfPlane} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ g : DiskClass, classWeight g z ≤ B) : ‖affineOperator z‖ ≤ B := by
  apply (affineOperator z).opNorm_le_bound hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro g
  rw [affineOperator_apply,norm_mul,Real.norm_of_nonneg (classWeight_pos g z).le]
  exact mul_le_mul (hw g) (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) hB

lemma transferOperator_pos (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) : 0 ≤ transferOperator f := by
  intro g
  change 0 ≤ (1/2 : ℝ)*(affineOperator dyadicLeft f g+affineOperator dyadicRight f g)
  exact mul_nonneg (by norm_num) (add_nonneg (affineOperator_pos _ f hf g) (affineOperator_pos _ f hf g))

lemma diskCayley_norm_sq_identity {z : ℂ} (hz : z ∈ halfPlane) :
    (1-‖diskCayley z‖^2)*‖z+Complex.I‖^2 = 4*z.im := by
  have hd : ‖z+Complex.I‖ ≠ 0 := norm_ne_zero_iff.mpr (cayley_den_ne_zero hz)
  rw [diskCayley,norm_div,div_pow]
  field_simp
  rw [Complex.sq_norm,Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring

lemma classFun_deriv_norm (g : DiskClass) (z : halfPlane) :
    ‖deriv (classFun g) z‖ = 4*‖deriv (diskExtend g.1) (diskCayley z)‖/‖z.val+Complex.I‖^2 := by
  have hd := (hasDerivAt_diskToHalf g.2.1.1 z.2).deriv
  rw [classFun]
  rw [hd,norm_div,norm_mul,norm_neg,norm_pow]
  norm_num

lemma classFun_reciprocal_norm (g : DiskClass) (z : halfPlane) :
    ‖reciprocalDeriv (classFun g) z‖ = ‖z.val+Complex.I‖^2/
      (4*‖deriv (diskExtend g.1) (diskCayley z)‖) := by
  rw [reciprocalDeriv,norm_inv,classFun_deriv_norm,inv_div]

lemma classFun_reciprocal_bound (g : DiskClass) (z : halfPlane) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ ‖z.val+Complex.I‖^4/z.val.im := by
  let r := ‖diskCayley z‖
  let D := ‖z.val+Complex.I‖^2
  let a := ‖deriv (diskExtend g.1) (diskCayley z)‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hr1 : r < 1 := by simpa [r,disk] using diskCayley_maps z.2
  have hD0 : 0 < D := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cayley_den_ne_zero z.2))
  have ha0 : 0 < a := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball g.2.1 (diskCayley_maps z.2))
  have he : (1-r^2)*D = 4*z.val.im := diskCayley_norm_sq_identity z.2
  have hlo : (1-r)/(1+r)^3 ≤ a := (schlicht_deriv_bounds g.2 (diskCayley_maps z.2)).1
  have hden : 0 < (1+r)^3 := pow_pos (by linarith) 3
  have h8 : (1+r)^3 ≤ 8 := by nlinarith [sq_nonneg (1-r),sq_nonneg r,mul_nonneg hr0 (sq_nonneg (1-r))]
  have hl : 1-r ≤ 8*a := by
    have hh := (div_le_iff₀ hden).mp hlo
    nlinarith [mul_le_mul_of_nonneg_left h8 ha0.le]
  have hD : 2*z.val.im ≤ (1-r)*D := by
    have hh : (1-r^2) ≤ 2*(1-r) := by nlinarith [sq_nonneg (1-r)]
    nlinarith [mul_le_mul_of_nonneg_right hh hD0.le]
  have hDa : z.val.im ≤ 4*a*D := by
    have hh := mul_le_mul_of_nonneg_right hl hD0.le
    nlinarith
  rw [classFun_reciprocal_norm]
  change D/(4*a) ≤ ‖z.val+Complex.I‖^4/z.val.im
  rw [div_le_div_iff₀ (by positivity : 0 < 4*a) z.2]
  have hh := mul_le_mul_of_nonneg_right hDa hD0.le
  dsimp [D] at *
  nlinarith

lemma classFun_strip_bound (g : DiskClass) {C₀ : ℝ} (hC : 0 ≤ C₀) (z : halfPlane)
    (hx : |z.val.re| ≤ C₀) (hy : z.val.im ≤ 1) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ (C₀^2+4)^2/z.val.im := by
  apply (classFun_reciprocal_bound g z).trans
  apply div_le_div_of_nonneg_right _ z.2.le
  have hD : ‖z.val+Complex.I‖^2 = z.val.re^2+(z.val.im+1)^2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply]
    ring
  have hxr : z.val.re^2 ≤ C₀^2 := by nlinarith [sq_abs z.val.re,(sq_le_sq₀ (abs_nonneg _) hC).mpr hx]
  have hDle : ‖z.val+Complex.I‖^2 ≤ C₀^2+4 := by
    have hz0 : 0 < z.val.im := z.2
    rw [hD]
    nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hy)]
  nlinarith [sq_nonneg (‖z.val+Complex.I‖^2-(C₀^2+4))]

lemma classFun_strip_bound_two (g : DiskClass) (z : halfPlane)
    (hx : |z.val.re| ≤ 2) (hy : z.val.im ≤ 1) :
    ‖reciprocalDeriv (classFun g) z‖ ≤ 64/z.val.im := by
  convert classFun_strip_bound g (by norm_num : (0 : ℝ) ≤ 2) z hx hy using 1
  norm_num

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Eigenmeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma positive_operator_mono.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : Monotone L := by
  intro f g h
  have := hp (g-f) (sub_nonneg.mpr h)
  simpa only [map_sub,sub_nonneg] using this

lemma positive_operator_abs_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (f : C(X,ℝ)) (x : X) :
    |L f x| ≤ ‖f‖ * L 1 x := by
  have hlo : (-‖f‖) • (1 : C(X,ℝ)) ≤ f := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  have hhi : f ≤ ‖f‖ • (1 : C(X,ℝ)) := by
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  have h1 := positive_operator_mono L hp hlo x
  have h2 := positive_operator_mono L hp hhi x
  simp only [map_smul,ContinuousMap.toFun_eq_coe,ContinuousMap.smul_apply,smul_eq_mul,neg_mul] at h1 h2
  exact abs_le.mpr ⟨h1,h2⟩

lemma positive_operator_norm.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : ‖L‖ = ‖L 1‖ := by
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le (L f) (by positivity)).mpr
    intro x
    calc
      ‖L f x‖ = |L f x| := Real.norm_eq_abs _
      _ ≤ ‖f‖ * L 1 x := positive_operator_abs_bound L hp f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (ContinuousMap.norm_coe_le_norm (L 1) x)) (norm_nonneg _)
      _ = ‖L 1‖ * ‖f‖ := mul_comm _ _
  · simpa using L.le_opNorm (1 : C(X,ℝ))

lemma positive_operator_pow.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (n : ℕ) :
    ∀ f, 0 ≤ f → 0 ≤ (L^n) f := by
  induction n with
  | zero => simp
  | succ n ih =>
    intro f hf
    simpa only [pow_succ',mul_apply_eq_comp] using hp ((L^n) f) (ih f hf)

lemma log_norm_pow_bddBelow.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : BddBelow (range (fun n : ℕ => Real.log ‖a^n‖/n)) := by
  refine ⟨0,?_⟩
  rintro _ ⟨n,rfl⟩
  exact div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)

lemma tendsto_log_norm_pow.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) :
    Tendsto (fun n : ℕ => Real.log ‖a^n‖/n) atTop (𝓝 (growthLog a h)) :=
  (log_norm_pow_subadditive a h).tendsto_lim (log_norm_pow_bddBelow a h)

lemma growthLog_nonneg.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : 0 ≤ growthLog a h :=
  ge_of_tendsto (tendsto_log_norm_pow a h)
    (Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (h n)) (Nat.cast_nonneg n)))

lemma growthRate_ge_one.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) : 1 ≤ growthRate a h :=
  Real.one_le_exp_iff.mpr (growthLog_nonneg a h)

lemma norm_pow_eventually_le.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {r : ℝ} (hr : growthRate a h < r) :
    ∀ᶠ n : ℕ in atTop, ‖a^n‖ ≤ r^n := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hlog : growthLog a h < Real.log r := by
    rwa [← Real.exp_lt_exp,Real.exp_log hr0]
  filter_upwards [(tendsto_log_norm_pow a h).eventually (gt_mem_nhds hlog),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : Real.log ‖a^n‖ ≤ (n : ℝ)*Real.log r := by
    have := (div_lt_iff₀ hnR).mp hn
    linarith
  have := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log (lt_of_lt_of_le zero_lt_one (h n)),Real.exp_nat_mul,
    Real.exp_log hr0] using this

lemma summable_scaled_pow.{u_1} {A : Type u_1} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : A) (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {τ : ℝ} (hτ : growthRate a h < τ) :
    Summable (fun n : ℕ => (τ⁻¹)^n • a^n) := by
  obtain ⟨r,hr,hrτ⟩ := exists_between hτ
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one a h).trans hr.le)
  have hτ0 : 0 < τ := hr0.trans hrτ
  apply Summable.of_norm_bounded_eventually (g := fun n : ℕ => (r/τ)^n)
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hτ0).mpr hrτ))
  have he := norm_pow_eventually_le a h hr
  rw [← Nat.cofinite_eq_atTop] at he
  filter_upwards [he] with n hn
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ (τ⁻¹)^n)]
  calc
    (τ⁻¹)^n * ‖a^n‖ ≤ (τ⁻¹)^n*r^n := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (r/τ)^n := by rw [← mul_pow]; congr 1; ring

lemma growthRate_le_of_pow_bound.{u_1} {A : Type u_1} [NormedRing A] (a : A)
    (h : ∀ n : ℕ, 1 ≤ ‖a^n‖) {M c : ℝ} (hM : 0 < M) (_hc : 0 ≤ c)
    (hb : ∀ n : ℕ, ‖a^n‖ ≤ M*c^n) : growthRate a h ≤ c := by
  have hc0 : 0 < c := by
    have := hb 1
    have := h 1
    simp only [pow_one] at *
    nlinarith
  have ht : Tendsto (fun n : ℕ => Real.log M/(n : ℝ)+Real.log c) atTop (𝓝 (Real.log c)) := by
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (Real.log c)
  have hl : growthLog a h ≤ Real.log c := by
    apply le_of_tendsto_of_tendsto (tendsto_log_norm_pow a h) ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (lt_of_lt_of_le zero_lt_one (h n)) (hb n)
    rw [Real.log_mul hM.ne' (pow_pos hc0 n).ne',Real.log_pow] at hlog
    calc
      Real.log ‖a^n‖/(n : ℝ) ≤ (Real.log M+(n : ℝ)*Real.log c)/(n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
      _ = Real.log M/(n : ℝ)+Real.log c := by field_simp
  simpa [growthRate,Real.exp_log hc0] using Real.exp_le_exp.mpr hl

lemma summable_resolvent_eval.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) (f : C(X,ℝ)) (x : X) :
    Summable (fun n : ℕ => (τ⁻¹)^n * (L^n) f x) := by
  let e : (C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  have hs := e.summable (summable_scaled_pow L h hτ)
  simpa only [e,ContinuousLinearMap.comp_apply,ContinuousLinearMap.apply_apply,
    smul_apply,ContinuousMap.evalCLM_apply,ContinuousMap.smul_apply,smul_eq_mul] using hs

lemma positiveResolvent_eval.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) (f : C(X,ℝ)) (x : X) :
    positiveResolvent L τ f x = ∑' n : ℕ, (τ⁻¹)^n * (L^n) f x := by
  let e : (C(X,ℝ) →L[ℝ] C(X,ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(X,ℝ) f)
  exact e.map_tsum (summable_scaled_pow L h hτ)

lemma positiveResolvent_nonneg.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    ∀ f, 0 ≤ f → 0 ≤ positiveResolvent L τ f := by
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro f hf x
  change 0 ≤ positiveResolvent L τ f x
  rw [positiveResolvent_eval L h hτ]
  exact tsum_nonneg (fun n => mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n)
    (positive_operator_pow L hp n f hf x))

lemma positiveResolvent_ge_one.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    1 ≤ positiveResolvent L τ 1 := by
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  intro x
  change 1 ≤ positiveResolvent L τ 1 x
  rw [positiveResolvent_eval L h hτ]
  have hn (n : ℕ) : 0 ≤ (τ⁻¹)^n * (L^n) (1 : C(X,ℝ)) x :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n) (positive_operator_pow L hp n 1 (by intro; simp) x)
  simpa using (summable_resolvent_eval L h hτ 1 x).le_tsum 0 (fun n _ => hn n)

lemma positiveResolvent_mul.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (h : ∀ n : ℕ, 1 ≤ ‖L^n‖)
    {τ : ℝ} (hτ : growthRate L h < τ) :
    positiveResolvent L τ * L = τ • (positiveResolvent L τ-1) ∧
    L * positiveResolvent L τ = τ • (positiveResolvent L τ-1) := by
  have ht : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le))
  have hs := summable_scaled_pow L h hτ
  have htail : ∑' n : ℕ, (τ⁻¹)^(n+1) • L^(n+1) = positiveResolvent L τ-1 := by
    have he := hs.sum_add_tsum_nat_add 1
    simpa [positiveResolvent] using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
  have he (n : ℕ) : τ • ((τ⁻¹)^(n+1) • L^(n+1)) = (τ⁻¹)^n • (L^n*L) := by
    rw [smul_smul,pow_succ,pow_succ]
    congr 1
    field_simp
  constructor
  · change (∑' n : ℕ, (τ⁻¹)^n • L^n)*L = _
    rw [show (∑' n : ℕ, (τ⁻¹)^n • L^n)*L =
      ∑' n : ℕ, ((τ⁻¹)^n • L^n)*L from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)).flip L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    exact tsum_congr (fun n => by
      rw [he]; change ((τ⁻¹)^n • L^n).comp L = (τ⁻¹)^n • ((L^n).comp L)
      exact ContinuousLinearMap.smul_comp _ _ _)
  · change L*(∑' n : ℕ, (τ⁻¹)^n • L^n) = _
    rw [show L*(∑' n : ℕ, (τ⁻¹)^n • L^n) =
      ∑' n : ℕ, L*((τ⁻¹)^n • L^n) from
      ((ContinuousLinearMap.compL ℝ C(X,ℝ) C(X,ℝ) C(X,ℝ)) L).map_tsum hs,
      ← htail,← tsum_const_smul'']
    apply tsum_congr
    intro n
    rw [he]
    change L.comp ((τ⁻¹)^n • L^n) = (τ⁻¹)^n • ((L^n).comp L)
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    change L * L^n = L^n * L
    rw [← pow_succ',← pow_succ]

lemma positive_operator_pow_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    {g : C(X,ℝ)} (hg : 1 ≤ g) {c : ℝ} (hc : 0 ≤ c) (hLg : L g ≤ c • g) (n : ℕ) :
    ‖L^n‖ ≤ ‖g‖*c^n := by
  have hiter : ∀ n : ℕ, (L^n) g ≤ c^n • g := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have h1 := positive_operator_mono L hp ih
      have h2 : c^n • L g ≤ c^n • (c • g) := smul_le_smul_of_nonneg_left hLg (pow_nonneg hc n)
      rw [map_smul] at h1
      have h3 := h1.trans h2
      simpa only [pow_succ',mul_apply_eq_comp,smul_smul,mul_comm] using h3
  rw [positive_operator_norm (L^n) (positive_operator_pow L hp n)]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg hc n))).mpr
  intro x
  have hn := positive_operator_pow L hp n 1 (by intro; simp) x
  have h1 := positive_operator_mono (L^n) (positive_operator_pow L hp n) hg x
  have h2 := hiter n x
  change (L^n) g x ≤ c^n*g x at h2
  calc
    ‖(L^n) 1 x‖ = (L^n) 1 x := Real.norm_of_nonneg hn
    _ ≤ c^n*g x := h1.trans h2
    _ ≤ c^n*‖g‖ := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)) (pow_nonneg hc n)
    _ = ‖g‖*c^n := mul_comm _ _

lemma positiveResolvent_norm_bound.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    1 ≤ ‖positiveResolvent L τ 1‖ ∧
    τ / ‖positiveResolvent L τ 1‖ ≤ τ - growthRate L h := by
  let g := positiveResolvent L τ 1
  have hg : 1 ≤ g := positiveResolvent_ge_one L hp h hτ
  have hM : 1 ≤ ‖g‖ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    exact (hg x).trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x))
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le)
  let c := τ*(1-1/‖g‖)
  have hc : 0 ≤ c := mul_nonneg ht.le (sub_nonneg.mpr ((div_le_one hM0).mpr hM))
  have he : L g = τ • (g-1) := by
    have hv := congrArg (fun A : C(X,ℝ) →L[ℝ] C(X,ℝ) => A 1) (positiveResolvent_mul L h hτ).2
    simpa only [mul_apply_eq_comp,smul_apply,
      sub_apply,one_apply_eq_self] using hv
  have hLg : L g ≤ c • g := by
    rw [he]
    intro x
    change τ*(g x-1) ≤ c*g x
    have hgx : g x ≤ ‖g‖ := (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)
    have hdiv : g x / ‖g‖ ≤ 1 := (div_le_one hM0).mpr hgx
    dsimp [c]
    have hh := mul_le_mul_of_nonneg_left hdiv ht.le
    simp only [div_eq_mul_inv,one_mul] at hh ⊢
    nlinarith
  have hr := growthRate_le_of_pow_bound L h hM0 hc (positive_operator_pow_bound L hp hg hc hLg)
  refine ⟨hM,?_⟩
  dsimp [c] at hr
  change τ/‖g‖ ≤ τ-growthRate L h
  simp only [div_eq_mul_inv,one_mul] at hr ⊢
  nlinarith

lemma probability_of_positive_functional.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X]
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : Λ 1 = 1) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ), ∫ x, f x ∂(μ : Measure X) = Λ f := by
  let Λ' : C_c(X,ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => map_add Λ f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => map_smul Λ c f.toContinuousMap
      monotone' := by
        intro f g hfg
        have hn : 0 ≤ Λ (g.toContinuousMap-f.toContinuousMap) := hp _ (sub_nonneg.mpr hfg)
        simpa only [map_sub,sub_nonneg] using hn }
  let μ := RealRMK.rieszMeasure Λ'
  have hi (f : C(X,ℝ)) : ∫ x, f x ∂μ = Λ f := by
    let f' : C_c(X,ℝ) := ⟨f,HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ' f'
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr (by
    have hh := hi 1
    simpa [h1] using hh)
  exact ⟨⟨μ,hμ⟩,hi⟩

lemma exists_max_of_nonneg_continuous.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [Nonempty X] (f : C(X,ℝ)) (hf : 0 ≤ f) : ∃ x : X, f x = ‖f‖ := by
  obtain ⟨x,_,hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  refine ⟨x,le_antisymm ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm f x)) ?_⟩
  apply (ContinuousMap.norm_le f (hf x)).mpr
  intro y
  calc
    ‖f y‖ = f y := Real.norm_of_nonneg (hf y)
    _ ≤ f x := hx (mem_univ y)

lemma exists_resolvent_probability.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) {τ : ℝ} (hτ : growthRate L h < τ) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ),
      |(∫ x, L f x ∂(μ : Measure X))-τ*(∫ x, f x ∂(μ : Measure X))| ≤
      (τ-growthRate L h)*‖f‖ := by
  let R := positiveResolvent L τ
  let g := R 1
  have hg : 1 ≤ g := positiveResolvent_ge_one L hp h hτ
  have hg0 : 0 ≤ g := le_trans (by intro; simp) hg
  obtain ⟨x,hx⟩ := exists_max_of_nonneg_continuous g hg0
  have hM := positiveResolvent_norm_bound L hp h hτ
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM.1
  let Λ : C(X,ℝ) →L[ℝ] ℝ := (‖g‖⁻¹ • ContinuousMap.evalCLM (R := ℝ) x).comp R
  have hΛ (f : C(X,ℝ)) : Λ f = R f x / ‖g‖ := by change ‖g‖⁻¹ * R f x = R f x / ‖g‖; ring
  have hpΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f := by
    intro f hf
    rw [hΛ]
    exact div_nonneg (positiveResolvent_nonneg L hp h hτ f hf x) hM0.le
  have h1 : Λ 1 = 1 := by rw [hΛ]; change g x / ‖g‖ = 1; rw [hx,div_self hM0.ne']
  obtain ⟨μ,hμ⟩ := probability_of_positive_functional Λ hpΛ h1
  refine ⟨μ,fun f => ?_⟩
  rw [hμ (L f),hμ f,hΛ,hΛ]
  have he : R (L f) x = τ*(R f x-f x) := by
    have hv := congrArg (fun A : C(X,ℝ) →L[ℝ] C(X,ℝ) => A f x) (positiveResolvent_mul L h hτ).1
    exact hv
  rw [he]
  have hτ0 : 0 ≤ τ := lt_of_lt_of_le zero_lt_one ((growthRate_ge_one L h).trans hτ.le) |>.le
  calc
    |τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖)| = (τ/‖g‖)*|f x| := by
      rw [show τ*(R f x-f x)/‖g‖-τ*(R f x/‖g‖) = -(τ/‖g‖)*f x by ring,
        abs_mul,abs_neg,abs_of_nonneg (div_nonneg hτ0 hM0.le)]
    _ ≤ (τ/‖g‖)*‖f‖ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f x)
      (div_nonneg hτ0 hM0.le)
    _ ≤ (τ-growthRate L h)*‖f‖ := mul_le_mul_of_nonneg_right hM.2 (norm_nonneg f)

lemma exists_growth_eigenmeasure.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    (L : C(X,ℝ) →L[ℝ] C(X,ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f)
    (h : ∀ n : ℕ, 1 ≤ ‖L^n‖) :
    ∃ μ : ProbabilityMeasure X, ∀ f : C(X,ℝ),
      (∫ x, L f x ∂(μ : Measure X)) = growthRate L h*(∫ x, f x ∂(μ : Measure X)) := by
  let ρ := growthRate L h
  let τ : ℕ → ℝ := fun n => ρ+1/((n : ℝ)+1)
  have hτ (n : ℕ) : growthRate L h < τ n := by
    dsimp [τ,ρ]
    exact lt_add_of_pos_right _ (by positivity)
  choose μ hμ using fun n : ℕ => exists_resolvent_probability L hp h (hτ n)
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let V := U.map μ
  let ν := V.lim
  have hν : Tendsto μ (U : Filter ℕ) (𝓝 ν) := V.le_nhds_lim
  have ht : Tendsto τ (U : Filter ℕ) (𝓝 ρ) := by
    have hh : Tendsto τ atTop (𝓝 ρ) := by
      simpa [τ] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add ρ
    exact hh.mono_left (Ultrafilter.of_le atTop)
  refine ⟨ν,fun f => ?_⟩
  have hi := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLi := (ProbabilityMeasure.continuous_integral_continuousMap (L f)).tendsto ν |>.comp hν
  have hb := le_of_tendsto_of_tendsto ((hLi.sub (ht.mul hi)).abs)
    ((ht.sub_const ρ).mul_const ‖f‖) (Eventually.of_forall (hμ · f))
  simp only [sub_self,zero_mul] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.AffineLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass

lemma intervalFunctional_apply.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ a b hab f = ∫ t in a..b, Λ (A t f) := rfl

lemma intervalFunctional_nonneg.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(X,ℝ)) (hf : 0 ≤ f) :
    0 ≤ intervalFunctional A hc hp Λ hΛ a b hab f :=
  intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf))

lemma pointOperator_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    pointOperator x y hy * pointOperator u v hv = pointOperator (x+y*u) (y*v) (mul_pos hy hv) := by
  simp only [pointOperator,affineOperator_mul,halfPoint_mul]

lemma pointOperator_zero_one : pointOperator 0 1 zero_lt_one = 1 := by
  have h : halfPoint 0 1 zero_lt_one = halfOne := by
    apply Subtype.ext
    simp [halfPoint,halfOne]
  rw [pointOperator,h,affineOperator_one]

lemma pointOperator_horizontal (x : ℝ) : pointOperator x 1 zero_lt_one = affineOperator (horizontal x) := rfl

lemma transfer_endpoint_step (v : ℝ) (hv : 0 < v) :
    transferOperator * (pointOperator (1+v) v hv-pointOperator (-1+v) v hv) =
      (1/2 : ℝ) • (pointOperator (1+v/2) (v/2) (by positivity)-
        pointOperator (-1+v/2) (v/2) (by positivity)) := by
  change ((1/2 : ℝ) • (pointOperator (-1/2) (1/2) (by norm_num)+
    pointOperator (1/2) (1/2) (by norm_num))) * _ = _
  rw [smul_mul_assoc,add_mul,mul_sub,mul_sub]
  simp only [pointOperator_mul]
  have h1 : -1/2+1/2*(1+v) = v/2 := by ring
  have h2 : -1/2+1/2*(-1+v) = -1+v/2 := by ring
  have h3 : 1/2+1/2*(1+v) = 1+v/2 := by ring
  have h4 : 1/2+1/2*(-1+v) = v/2 := by ring
  simp only [h1,h2,h3,h4,show (1/2 : ℝ)*v = v/2 by ring]
  congr 1
  abel

lemma transfer_endpoint (n : ℕ) :
    transferOperator^n * (affineOperator (horizontal 2)-1) =
      ((1/2 : ℝ)^n) • (pointOperator (1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)-
        pointOperator (-1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)) := by
  induction n with
  | zero =>
    simp only [pow_zero,one_mul,one_smul]
    norm_num only [show (1+(1 : ℝ)) = 2 by norm_num,show (-1+(1 : ℝ)) = 0 by norm_num]
    rw [pointOperator_zero_one,pointOperator_horizontal]
  | succ n ih =>
    rw [pow_succ',mul_assoc,ih,mul_smul_comm,transfer_endpoint_step,smul_smul]
    simp only [pow_succ,div_eq_mul_inv,one_mul]

lemma endpoint_norm_bound (n : ℕ) :
    ‖pointOperator (1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)-
      pointOperator (-1+(1/2 : ℝ)^n) ((1/2 : ℝ)^n) (by positivity)‖ ≤
      8192 / ((1/2 : ℝ)^n)^2 := by
  let v := (1/2 : ℝ)^n
  have hv : 0 < v := by positivity
  have hv1 : v ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb (x : ℝ) (hx : |x| ≤ 2) : ‖pointOperator x v hv‖ ≤ 4096/v^2 := by
    apply affineOperator_norm_le (by positivity)
    intro g
    have hq := classFun_strip_bound_two g (halfPoint x v hv) (by simpa [halfPoint] using hx)
      (by simpa [halfPoint] using hv1)
    simp only [halfPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hq
    rw [classWeight]
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 64/v)).mpr hq
    simpa only [halfPoint,div_pow,show (64 : ℝ)^2 = 4096 by norm_num] using hh
  have hp := hb (1+v) (by rw [abs_le]; constructor <;> linarith)
  have hm := hb (-1+v) (by rw [abs_le]; constructor <;> linarith)
  calc
    _ ≤ ‖pointOperator (1+v) v hv‖+‖pointOperator (-1+v) v hv‖ := norm_sub_le (pointOperator (1+v) v hv) (pointOperator (-1+v) v hv)
    _ ≤ 4096/v^2+4096/v^2 := add_le_add hp hm
    _ = 8192/v^2 := by ring

lemma eigenfunctional_pow (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hΛ : ∀ f, Λ (transferOperator f) = ρ*Λ f) (n : ℕ) (f : C(DiskClass,ℝ)) :
    Λ ((transferOperator^n) f) = ρ^n*Λ f := by
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ',mul_apply_eq_comp,hΛ,ih]; ring

lemma eigenfunctional_horizontal_period (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hρ : 2 < ρ) (hΛ : ∀ f, Λ (transferOperator f) = ρ*Λ f) (f : C(DiskClass,ℝ)) :
    Λ (affineOperator (horizontal 2) f) = Λ f := by
  have hρ0 : 0 < ρ := by linarith
  have hn (n : ℕ) : ‖Λ (affineOperator (horizontal 2) f)-Λ f‖ ≤
      (8192*‖Λ‖*‖f‖)*(2/ρ)^n := by
    let v := (1/2 : ℝ)^n
    let B := pointOperator (1+v) v (by positivity)-pointOperator (-1+v) v (by positivity)
    have he : ρ^n*(Λ (affineOperator (horizontal 2) f)-Λ f) = v*Λ (B f) := by
      rw [← map_sub,← eigenfunctional_pow Λ ρ hΛ]
      change Λ ((transferOperator^n * (affineOperator (horizontal 2)-1)) f) = _
      rw [transfer_endpoint]
      change Λ (v • B f) = _
      exact map_smul Λ v (B f)
    have hb : ‖B‖ ≤ 8192/v^2 := endpoint_norm_bound n
    have hh : ρ^n*‖Λ (affineOperator (horizontal 2) f)-Λ f‖ ≤
        v*(‖Λ‖*(8192/v^2*‖f‖)) := by
      calc
        _ = ‖v*Λ (B f)‖ := by rw [← he,norm_mul,Real.norm_of_nonneg (pow_nonneg hρ0.le n)]
        _ ≤ v*(‖Λ‖*(‖B‖*‖f‖)) := by
          rw [norm_mul,Real.norm_of_nonneg (by positivity : 0 ≤ v)]
          exact mul_le_mul_of_nonneg_left ((Λ.le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg Λ))) (by positivity)
        _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hb (norm_nonneg f)) (norm_nonneg Λ)) (by positivity)
    calc
      _ ≤ (v*(‖Λ‖*(8192/v^2*‖f‖)))/ρ^n :=
        (le_div_iff₀ (pow_pos hρ0 n)).mpr (by simpa only [mul_comm] using hh)
      _ = _ := by
        dsimp [v]
        simp only [div_pow,one_pow]
        field_simp
  have ht : Tendsto (fun n : ℕ => (8192*‖Λ‖*‖f‖)*(2/ρ)^n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 2/ρ)
      ((div_lt_one hρ0).mpr hρ)).const_mul (8192*‖Λ‖*‖f‖)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (norm_nonneg _)))

lemma probabilityFunctional_apply.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) (f : C(X,ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂(μ : Measure X) := rfl

lemma probabilityFunctional_one.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) :
    probabilityFunctional μ 1 = 1 := by simp [probabilityFunctional_apply]

lemma probabilityFunctional_pos.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : ProbabilityMeasure X) (f : C(X,ℝ)) (hf : 0 ≤ f) :
    0 ≤ probabilityFunctional μ f := integral_nonneg hf

lemma periodic_dyadic_integral (F : ℝ → ℝ) (hc : Continuous F) (hp : Function.Periodic F 2) :
    (∫ x in (0 : ℝ)..2, (F (-1/2+x/2)+F (1/2+x/2))) = 2*∫ x in (0 : ℝ)..2, F x := by
  have hm : (∫ x in (0 : ℝ)..2, F (-1/2+x/2)) = 2*∫ x in (-1/2 : ℝ)..(1/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (-1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hp' : (∫ x in (0 : ℝ)..2, F (1/2+x/2)) = 2*∫ x in (1/2 : ℝ)..(3/2), F x := by
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1/2 : ℝ) ≠ 0) (1/2)
    convert hh using 1 <;> (try { congr 1; funext x; congr 1; ring }); norm_num
  have hi : (∫ x in (-1/2 : ℝ)..(3/2), F x) = ∫ x in (0 : ℝ)..2, F x := by
    convert hp.intervalIntegral_add_eq (-1/2) 0 using 1 <;> norm_num
  have hcm : Continuous (fun x : ℝ => F (-1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  have hcp : Continuous (fun x : ℝ => F (1/2+x/2)) := hc.comp (continuous_const.add (continuous_id.div_const 2))
  rw [intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),hm,hp',← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _),hi]

lemma horizontalAverage_apply (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass,ℝ)) : horizontalAverage Λ hp f = (1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f) := rfl

lemma horizontalAverage_nonneg (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) : 0 ≤ horizontalAverage Λ hp f := by
  rw [horizontalAverage_apply]
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hp _ (affineOperator_pos _ f hf))

lemma horizontalAverage_mass_pos (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) : 0 < horizontalAverage Λ hp 1 := by
  rw [horizontalAverage_apply]
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num)
    (Λ.continuous.comp (continuous_horizontalOperator 1)).continuousOn
    (fun x _ => hp _ (affineOperator_pos _ 1 (by intro; simp)))
  refine ⟨0,by norm_num,?_⟩
  change 0 < Λ (pointOperator 0 1 zero_lt_one 1)
  rw [pointOperator_zero_one,one_apply_eq_self]
  exact h1

lemma functional_point_periodic (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    Function.Periodic (fun x : ℝ => Λ (pointOperator x y hy f)) 2 := by
  intro x
  have hh := hper (pointOperator x y hy f)
  rw [← pointOperator_horizontal,← mul_apply_eq_comp,pointOperator_mul] at hh
  simpa only [one_mul,add_comm x 2] using hh

lemma horizontalAverage_point (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (u v : ℝ) (hv : 0 < v) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (pointOperator u v hv f) =
      (1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (pointOperator (x+u) v hv f) := by
  rw [horizontalAverage_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← pointOperator_horizontal,← mul_apply_eq_comp,pointOperator_mul]
  simp only [one_mul]

lemma horizontalAverage_invariant (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (t : ℝ) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (affineOperator (horizontal t) f) = horizontalAverage Λ hp f := by
  rw [← pointOperator_horizontal,horizontalAverage_point]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (pointOperator x 1 zero_lt_one f)) t]
  have hh := (functional_point_periodic Λ hper 1 zero_lt_one f).intervalIntegral_add_eq t 0
  rw [zero_add] at hh
  rw [zero_add,add_comm 2 t,hh,horizontalAverage_apply]
  rfl

lemma horizontalAverage_half_scale (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (heig : ∀ f, Λ (transferOperator f) = ρ*Λ f) (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (pointOperator 0 (1/2) (by norm_num) f) = ρ*horizontalAverage Λ hp f := by
  have he (x : ℝ) : ρ*Λ (affineOperator (horizontal x) f) =
      (1/2 : ℝ)*(Λ (pointOperator (-1/2+x/2) (1/2) (by norm_num) f)+
        Λ (pointOperator (1/2+x/2) (1/2) (by norm_num) f)) := by
    rw [← heig]
    change Λ (((1/2 : ℝ) • (pointOperator (-1/2) (1/2) (by norm_num)+pointOperator (1/2) (1/2) (by norm_num)))
      (pointOperator x 1 zero_lt_one f)) = _
    rw [← mul_apply_eq_comp,smul_mul_assoc,add_mul]
    simp only [pointOperator_mul,mul_one,smul_apply,map_smul,add_apply,map_add,smul_eq_mul]
    simp only [show (1/2 : ℝ)*x = x/2 by ring]
  have hc : Continuous (fun x : ℝ => Λ (pointOperator x (1/2) (by norm_num) f)) :=
    Λ.continuous.comp (continuous_pointOperator_x _ _ f)
  have hi := periodic_dyadic_integral (fun x => Λ (pointOperator x (1/2) (by norm_num) f)) hc
    (functional_point_periodic Λ hper (1/2) (by norm_num) f)
  rw [horizontalAverage_point,horizontalAverage_apply]
  simp only [add_zero]
  rw [show ρ*((1/2 : ℝ)*∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f)) =
    (1/2 : ℝ)*(∫ x in (0 : ℝ)..2, ρ*Λ (affineOperator (horizontal x) f)) by
      rw [intervalIntegral.integral_const_mul]; ring]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,hi]
  ring

lemma period_average_invariant.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (hm : ∀ t s, A (t+s) = A t*A s)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (l : ℝ) (hl : 0 ≤ l) (hper : ∀ f, Λ (A l f) = Λ f)
    (s : ℝ) (f : C(X,ℝ)) :
    intervalFunctional A hc hp Λ hΛ 0 l hl (A s f) =
      intervalFunctional A hc hp Λ hΛ 0 l hl f := by
  have hfper : Function.Periodic (fun t : ℝ => Λ (A t f)) l := by
    intro t
    dsimp only
    rw [add_comm t l,hm,mul_apply_eq_comp,hper]
  rw [intervalFunctional_apply,intervalFunctional_apply]
  have he (t : ℝ) : Λ (A t (A s f)) = Λ (A (t+s) f) := by rw [hm,mul_apply_eq_comp]
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun t => Λ (A t f)) s]
  simpa only [zero_add,add_comm l s] using hfper.intervalIntegral_add_eq s 0

lemma intervalFunctional_mass_pos.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    (A : ℝ → C(X,ℝ) →L[ℝ] C(X,ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (h0 : A 0 = 1)
    (Λ : C(X,ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) (l : ℝ) (hl : 0 < l) :
    0 < intervalFunctional A hc hp Λ hΛ 0 l hl.le 1 := by
  rw [intervalFunctional_apply]
  apply intervalIntegral.integral_pos hl (Λ.continuous.comp (hc 1)).continuousOn
    (fun t _ => hΛ _ (hp _ _ (by intro; simp)))
  refine ⟨0,by simp [hl.le],?_⟩
  change 0 < Λ (A 0 1)
  simpa only [h0,one_apply_eq_self] using h1

lemma logScaledOperator_zero (β : ℝ) : logScaledOperator β 0 = 1 := by
  simp only [logScaledOperator,mul_zero,Real.exp_zero,one_smul,pointOperator_zero_one]

lemma logScaledOperator_add (β t s : ℝ) :
    logScaledOperator β (t+s) = logScaledOperator β t*logScaledOperator β s := by
  simp only [logScaledOperator,smul_mul_smul_comm,pointOperator_mul,mul_zero,add_zero,Real.exp_add,mul_add]

lemma logScaledOperator_horizontal (β t u : ℝ) :
    logScaledOperator β t*affineOperator (horizontal u) =
      affineOperator (horizontal (Real.exp t*u))*logScaledOperator β t := by
  simp only [logScaledOperator,← pointOperator_horizontal,smul_mul_assoc,mul_smul_comm,pointOperator_mul,
    mul_one,one_mul,mul_zero,zero_add,add_zero]

lemma horizontalAverage_log_period (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (hρ : 0 < ρ) (heig : ∀ f, Λ (transferOperator f) = ρ*Λ f)
    (f : C(DiskClass,ℝ)) :
    horizontalAverage Λ hp (logScaledOperator (Real.log ρ/Real.log 2) (Real.log 2) f) =
      horizontalAverage Λ hp f := by
  have he := horizontalAverage_half_scale Λ hp hper ρ heig (pointOperator 0 2 (by norm_num) f)
  rw [← mul_apply_eq_comp,pointOperator_mul] at he
  norm_num only [mul_zero,add_zero,show (1/2 : ℝ)*2 = 1 by norm_num,pointOperator_zero_one,one_apply_eq_self] at he
  rw [logScaledOperator_apply,map_smul,smul_eq_mul]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    Real.exp_log hρ]
  simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact he.symm

lemma scaleAverage_apply (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp f = ∫ t in (0 : ℝ)..Real.log 2, Λ (logScaledOperator β t f) := rfl

lemma scaleAverage_pos (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass,ℝ)) (hf : 0 ≤ f) :
    0 ≤ scaleAverage β Λ hp f :=
  intervalFunctional_nonneg _ _ _ _ hp _ _ _ f hf

lemma scaleAverage_mass_pos (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : 0 < Λ 1) : 0 < scaleAverage β Λ hp 1 :=
  intervalFunctional_mass_pos _ _ _ (logScaledOperator_zero β) Λ hp h1 _ (Real.log_pos (by norm_num))

lemma scaleAverage_covariant (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (logScaledOperator β (Real.log 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp (pointOperator 0 y hy f) = y^(-β)*scaleAverage β Λ hp f := by
  have he := period_average_invariant (logScaledOperator β) (continuous_logScaledOperator β)
    (logScaledOperator_pos β) (logScaledOperator_add β) Λ hp (Real.log 2)
    (Real.log_nonneg (by norm_num)) hper (Real.log y) f
  change scaleAverage β Λ hp (logScaledOperator β (Real.log y) f) = scaleAverage β Λ hp f at he
  simp only [logScaledOperator_apply,map_smul,smul_eq_mul,Real.exp_log hy] at he
  rw [Real.rpow_def_of_pos hy]
  have hinv : Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y) = 1 := by
    rw [← Real.exp_add,show Real.log y*(-β)+β*Real.log y = 0 by ring,Real.exp_zero]
  calc
    _ = (Real.exp (Real.log y*(-β))*Real.exp (β*Real.log y))*scaleAverage β Λ hp (pointOperator 0 y hy f) := by rw [hinv,one_mul]
    _ = _ := by rw [mul_assoc,he]

lemma scaleAverage_horizontal (β : ℝ) (Λ : C(DiskClass,ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hh : ∀ u f, Λ (affineOperator (horizontal u) f) = Λ f)
    (u : ℝ) (f : C(DiskClass,ℝ)) :
    scaleAverage β Λ hp (affineOperator (horizontal u) f) = scaleAverage β Λ hp f := by
  rw [scaleAverage_apply,scaleAverage_apply]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← mul_apply_eq_comp,logScaledOperator_horizontal,mul_apply_eq_comp,hh]

lemma transferBeta_gt_one (hρ : 2 < transferRho) : 1 < transferBeta := by
  apply (lt_div_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
  rw [one_mul]
  exact Real.log_lt_log (by norm_num) hρ

lemma exists_weighted_continuous_law (hρ : 2 < transferRho) :
    ∃ P : ProbabilityMeasure DiskClass, ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-transferBeta)*(∫ g, f g ∂(P : Measure DiskClass)) := by
  obtain ⟨μ,hμ⟩ := exists_growth_eigenmeasure transferOperator transferOperator_pos transferOperator_pow_norm_ge_one
  let Λ := probabilityFunctional μ
  have hp : ∀ f, 0 ≤ f → 0 ≤ Λ f := probabilityFunctional_pos μ
  have h1 : Λ 1 = 1 := probabilityFunctional_one μ
  have heig : ∀ f, Λ (transferOperator f) = transferRho*Λ f := hμ
  have hper := eigenfunctional_horizontal_period Λ transferRho hρ heig
  let H := horizontalAverage Λ hp
  have hH : ∀ f, 0 ≤ f → 0 ≤ H f := horizontalAverage_nonneg Λ hp
  have hH1 : 0 < H 1 := horizontalAverage_mass_pos Λ hp (by rw [h1]; norm_num)
  have hHper : ∀ f, H (logScaledOperator transferBeta (Real.log 2) f) = H f :=
    horizontalAverage_log_period Λ hp hper transferRho (by linarith) heig
  have hHh : ∀ u f, H (affineOperator (horizontal u) f) = H f := horizontalAverage_invariant Λ hp hper
  let ν := scaleAverage transferBeta H hH
  have hν : ∀ f, 0 ≤ f → 0 ≤ ν f := scaleAverage_pos transferBeta H hH
  have hν1 : 0 < ν 1 := scaleAverage_mass_pos transferBeta H hH hH1
  have hνh : ∀ u f, ν (affineOperator (horizontal u) f) = ν f := scaleAverage_horizontal transferBeta H hH hHh
  have hνs : ∀ y (hy : 0 < y) f, ν (pointOperator 0 y hy f) = y^(-transferBeta)*ν f :=
    scaleAverage_covariant transferBeta H hH hHper
  let PiF : C(DiskClass,ℝ) →L[ℝ] ℝ := (ν 1)⁻¹ • ν
  have hPiF : ∀ f, 0 ≤ f → 0 ≤ PiF f := fun f hf => mul_nonneg (inv_nonneg.mpr hν1.le) (hν f hf)
  have hPiF1 : PiF 1 = 1 := by change (ν 1)⁻¹*ν 1 = 1; exact inv_mul_cancel₀ (ne_of_gt hν1)
  obtain ⟨P,hP⟩ := probability_of_positive_functional PiF hPiF hPiF1
  refine ⟨P,fun z f => ?_⟩
  have hz : 0 < z.val.im := z.2
  have hez : affineOperator z = affineOperator (horizontal z.val.re)*pointOperator 0 z.val.im hz := by
    rw [← pointOperator_horizontal,pointOperator_mul]
    congr 1
    apply Subtype.ext
    simpa only [halfPoint,mul_zero,add_zero,one_mul] using z.val.re_add_im.symm
  change (∫ g, (affineOperator z f) g ∂(P : Measure DiskClass)) = _
  rw [hP,hP]
  change (ν 1)⁻¹*ν (affineOperator z f) = _
  rw [hez,mul_apply_eq_comp,hνh,hνs]
  change (ν 1)⁻¹*((z.val.im)^(-transferBeta)*ν f) = (z.val.im)^(-transferBeta)*((ν 1)⁻¹*ν f)
  ring

lemma weighted_measure_eq.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X,ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X,X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X,ℝ), (∫ x, w x*f (T x) ∂μ) = c*∫ x, f x ∂μ) :
    Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x))) = ENNReal.ofReal c • μ := by
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal
    (w.continuous.integrable_of_hasCompactSupport (μ := μ) (HasCompactSupport.of_compactSpace w)).hasFiniteIntegral
  have : (ENNReal.ofReal c • μ).Regular := Measure.Regular.smul (μ := μ) ENNReal.ofReal_ne_top
  have hwmeas : Measurable (fun x => ENNReal.ofReal (w x)) := w.continuous.measurable.ennreal_ofReal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x)))) = ∫ x, f.toContinuousMap x ∂ENNReal.ofReal c • μ
  rw [integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hwmeas (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw _),smul_eq_mul]
  rw [he f.toContinuousMap,integral_smul_measure,ENNReal.toReal_ofReal hc,smul_eq_mul]

lemma weighted_lintegral_of_continuous.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X,ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X,X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X,ℝ), (∫ x, w x*f (T x) ∂μ) = c*∫ x, f x ∂μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (w x)*f (T x) ∂μ) = ENNReal.ofReal c*∫⁻ x, f x ∂μ := by
  have hh := weighted_measure_eq μ w hw T c hc he
  have hi := congrArg (fun ν : Measure X => ∫⁻ x, f x ∂ν) hh
  rw [lintegral_map hf T.continuous.measurable, lintegral_smul_measure] at hi
  change (∫⁻ x, (f ∘ T) x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _ at hi
  rw [lintegral_withDensity_eq_lintegral_mul μ w.continuous.measurable.ennreal_ofReal (hf.comp T.continuous.measurable)] at hi
  simpa only [Pi.mul_apply,smul_eq_mul,Function.comp_def] using hi

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Moments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

attribute [local irreducible] classWeight
attribute [local irreducible] classFun
attribute [local irreducible] rerootClass
attribute [local irreducible] inverseDensity inverseJacDensity

lemma continuous_classReciprocal_eval :
    Continuous (fun p : DiskClass × halfPlane => reciprocalDeriv (classFun p.1) p.2) := by
  have hd : Continuous (fun p : DiskClass × halfPlane => deriv (classFun p.1) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_classJet_eval 1
  exact hd.inv₀ (fun p => univalent_deriv_ne_zero isOpen_halfPlane (classFun_schlicht p.1).1 p.2.2)

lemma continuous_reciprocalJet (n : ℕ) : Continuous (reciprocalJet n) := by
  have hc : Continuous (reciprocalJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_classReciprocal_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn (fun a => reciprocalDeriv (classFun a))
      (reciprocalDeriv (classFun g)) (𝓝 g) halfPlane :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_halfPlane h
      (Eventually.of_forall differentiableOn_classReciprocal) n)

lemma continuous_reciprocalJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × halfPlane => iteratedDeriv n (reciprocalDeriv (classFun p.1)) p.2) :=
  continuous_eval.comp ((continuous_reciprocalJet n).prodMap continuous_id)

lemma classReciprocal_at_I (g : DiskClass) : reciprocalDeriv (classFun g) Complex.I = 1 := by
  rw [reciprocalDeriv,(classFun_schlicht g).2.2,inv_one]

lemma hasDerivAt_integral_compact.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (F F' : ℝ → X → ℝ) {U : Set ℝ} (hU : IsOpen U)
    (hF : ∀ x ∈ U, Continuous (F x))
    (hc : ContinuousOn (fun p : ℝ × X => F' p.1 p.2) (U ×ˢ univ))
    (hd : ∀ x ∈ U, ∀ a, HasDerivAt (fun t => F t a) (F' x a) x)
    {x : ℝ} (hx : x ∈ U) :
    HasDerivAt (fun t => ∫ a, F t a ∂μ) (∫ a, F' x a ∂μ) x := by
  obtain ⟨r,hr,hsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx)
  have hr2 : 0 < r/2 := half_pos hr
  have hsub' : Metric.closedBall x (r/2) ⊆ U :=
    (Metric.closedBall_subset_ball (by linarith)).trans hsub
  have hk : IsCompact (Metric.closedBall x (r/2) ×ˢ (univ : Set X)) :=
    (isCompact_closedBall _ _).prod isCompact_univ
  obtain ⟨C,hC⟩ := hk.exists_bound_of_continuousOn (hc.mono (Set.prod_mono hsub' Subset.rfl))
  have hc0 : Continuous (F' x) := by
    have hs : Continuous (fun a : X => (x,a)) := continuous_const.prodMk continuous_id
    exact continuousOn_univ.mp
      (hc.comp hs.continuousOn (fun a _ => ⟨hx,mem_univ a⟩))
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball x (r/2)) (bound := fun _ : X => C) (Metric.ball_mem_nhds _ hr2)
    ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards [hU.mem_nhds hx] with y hy
    exact (hF y hy).aestronglyMeasurable
  · exact (hF x hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · exact hc0.aestronglyMeasurable
  · exact Eventually.of_forall (fun a y hy => hC (y,a) ⟨Metric.mem_closedBall.mpr (Metric.mem_ball.mp hy).le,mem_univ a⟩)
  · exact integrable_const C
  · exact Eventually.of_forall (fun a y hy => hd y (hsub' (Metric.ball_subset_closedBall hy)) a)

lemma complex_line_deriv {Q : ℂ → ℂ} {z d v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => Q (z+(s : ℂ)*v)) (d*v) t := by
  have hv : HasDerivAt (fun s : ℝ => z+(s : ℂ)*v) v t := by
    simpa using ((Complex.ofRealCLM.hasDerivAt.mul_const v).const_add z :
      HasDerivAt (fun s : ℝ => z+Complex.ofRealCLM s*v) (Complex.ofRealCLM 1*v) t)
  convert HasDerivAt.comp (𝕜 := ℝ) t hQ hv using 1 <;> rfl

lemma norm_line_hasDerivAt {Q : ℂ → ℂ} {z d v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => ‖Q (z+(s : ℂ)*v)‖^2)
      (normFirst (Q (z+(t : ℂ)*v)) d v) t :=
  (complex_line_deriv hQ).norm_sq

lemma norm_first_hasDerivAt {Q D : ℂ → ℂ} {z d e v : ℂ} {t : ℝ}
    (hQ : HasDerivAt Q d (z+(t : ℂ)*v))
    (hD : HasDerivAt D e (z+(t : ℂ)*v)) :
    HasDerivAt (fun s : ℝ => normFirst (Q (z+(s : ℂ)*v)) (D (z+(s : ℂ)*v)) v)
      (2*(inner ℝ (d*v) (D (z+(t : ℂ)*v)*v)+inner ℝ (Q (z+(t : ℂ)*v)) ((e*v)*v))) t := by
  simpa only [normFirst, add_comm] using ((complex_line_deriv hQ).inner ℝ ((complex_line_deriv hD).mul_const v)).const_mul 2

lemma norm_first_one (d : ℂ) : normFirst 1 d 1 = 2*d.re := by
  simp [normFirst,Complex.inner]

lemma norm_first_I (d : ℂ) : normFirst 1 d Complex.I = -2*d.im := by
  simp [normFirst,Complex.inner]

lemma norm_second_laplacian (q d e : ℂ) :
    normSecond q d e 1+normSecond q d e Complex.I = 4*‖d‖^2 := by
  simp only [normSecond,mul_one]
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul,Complex.norm_I,mul_one]
  have he : (e*Complex.I)*Complex.I = -e := by rw [mul_assoc,Complex.I_mul_I,mul_neg_one]
  rw [he,inner_neg_right]
  ring

lemma continuous_normSecond : Continuous (fun p : ℂ × ℂ × ℂ × ℂ => normSecond p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  unfold normSecond
  fun_prop

lemma isOpen_lineDomain (v : ℂ) : IsOpen (lineDomain v) :=
  isOpen_lt continuous_const (by fun_prop)

lemma complexLine_im (v : ℂ) (t : ℝ) : (complexLine v t).im = 1+t*v.im := by
  simp [complexLine,Complex.mul_im]

lemma complexLine_mem {v : ℂ} {t : ℝ} (ht : t ∈ lineDomain v) :
    0 < (complexLine v t).im := (complexLine_im v t).symm ▸ ht

lemma zero_mem_lineDomain (v : ℂ) : (0 : ℝ) ∈ lineDomain v := by simp [lineDomain]

lemma continuousOn_complexLine.{u_1} {X : Type u_1} [TopologicalSpace X] (G : X → ℂ → ℂ)
    (hG : Continuous (fun p : X × {z : ℂ | 0 < z.im} => G p.1 p.2)) (v : ℂ) :
    ContinuousOn (fun p : ℝ × X => G p.2 (complexLine v p.1)) (lineDomain v ×ˢ univ) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  let H : (lineDomain v ×ˢ (univ : Set X)) → X × {z : ℂ | 0 < z.im} :=
    fun p => (p.val.2,⟨complexLine v p.val.1,complexLine_mem p.2.1⟩)
  have hH : Continuous H := by
    apply Continuous.prodMk
    · exact continuous_snd.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      exact continuous_const.add (((Complex.continuous_ofReal.comp continuous_fst).comp continuous_subtype_val).mul continuous_const)
  exact hG.comp hH

lemma continuous_prod_section.{u_1} {X : Type u_1} [TopologicalSpace X]
    {U : Set ℝ} {G : ℝ × X → ℝ} (hG : ContinuousOn G (U ×ˢ univ)) {t : ℝ} (ht : t ∈ U) :
    Continuous (fun a => G (t,a)) :=
  continuousOn_univ.mp (hG.comp (continuous_const.prodMk continuous_id).continuousOn
    (fun _ _ => ⟨ht,mem_univ _⟩))

lemma continuousOn_normFirst_line.{u_1} {X : Type u_1} [TopologicalSpace X]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2)) (v : ℂ) :
    ContinuousOn (fun p : ℝ × X => normFirst (Q p.2 (complexLine v p.1)) (D p.2 (complexLine v p.1)) v) (lineDomain v ×ˢ univ) := by
  unfold normFirst
  exact continuousOn_const.mul ((continuousOn_complexLine Q hQc v).inner ((continuousOn_complexLine D hDc v).mul continuousOn_const))

lemma integral_norm_line_derivative.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    HasDerivAt (fun s => ∫ a, ‖Q a (complexLine v s)‖^2 ∂μ)
      (∫ a, normFirst (Q a (complexLine v t)) (D a (complexLine v t)) v ∂μ) t := by
  refine hasDerivAt_integral_compact μ
    (fun s a => ‖Q a (complexLine v s)‖^2)
    (fun s a => normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v)
    (isOpen_lineDomain v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section ((continuousOn_complexLine Q hQc v).norm.pow 2) hs
  · exact continuousOn_normFirst_line Q D hQc hDc v
  · intro s hs a
    exact norm_line_hasDerivAt (hD a _ (complexLine_mem hs))

lemma integral_normFirst_line_derivative.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    HasDerivAt (fun s => ∫ a, normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v ∂μ)
      (∫ a, normSecond (Q a (complexLine v t)) (D a (complexLine v t)) (E a (complexLine v t)) v ∂μ) t := by
  refine hasDerivAt_integral_compact μ
    (fun s a => normFirst (Q a (complexLine v s)) (D a (complexLine v s)) v)
    (fun s a => normSecond (Q a (complexLine v s)) (D a (complexLine v s)) (E a (complexLine v s)) v)
    (isOpen_lineDomain v) ?_ ?_ ?_ ht
  · intro s hs
    exact continuous_prod_section (continuousOn_normFirst_line Q D hQc hDc v) hs
  · have hcQ := continuousOn_complexLine Q hQc v
    have hcD := continuousOn_complexLine D hDc v
    have hcE := continuousOn_complexLine E hEc v
    unfold normSecond
    exact continuousOn_const.mul (((hcD.mul continuousOn_const).inner (hcD.mul continuousOn_const)).add
      (hcQ.inner ((hcE.mul continuousOn_const).mul continuousOn_const)))
  · intro s hs a
    exact norm_first_hasDerivAt (hD a _ (complexLine_mem hs)) (hE a _ (complexLine_mem hs))

lemma normFirst_expected.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v : ℂ) {t : ℝ} (ht : t ∈ lineDomain v) :
    (∫ a, normFirst (Q a (complexLine v t)) (D a (complexLine v t)) v ∂μ) =
      v.im*(-β)*(1+t*v.im)^(-β-1) := by
  have hdR := (((hasDerivAt_id t).mul_const v.im).const_add 1).rpow_const
    (p := -β) (Or.inl (ne_of_gt ht))
  simp only [one_mul,id_eq] at hdR
  apply (integral_norm_line_derivative μ Q D hQc hDc hD v ht).unique
  apply hdR.congr_of_eventuallyEq
  filter_upwards [(isOpen_lineDomain v).mem_nhds ht] with s hs
  exact (hmean (complexLine v s) (complexLine_mem hs)).trans
    (congrArg (fun x : ℝ => x^(-β)) (complexLine_im v s))

lemma compact_holomorphic_line_moments.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β))
    (v : ℂ) :
    (∫ a, normFirst (Q a Complex.I) (D a Complex.I) v ∂μ) = -β*v.im ∧
    (∫ a, normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) v ∂μ) =
      β*(β+1)*v.im^2 := by
  have hm' {t : ℝ} (ht : t ∈ lineDomain v) := normFirst_expected μ Q D hQc hDc hD β hmean v ht
  constructor
  · simpa only [complexLine_zero,zero_mul,add_zero,Real.one_rpow,mul_one,mul_comm,mul_zero] using hm' (zero_mem_lineDomain v)
  · have hdR := (((((hasDerivAt_id (0 : ℝ)).mul_const v.im).const_add 1).rpow_const
        (p := -β-1) (Or.inl (by norm_num))).const_mul (v.im*(-β)))
    have he : (∫ a, normSecond (Q a (complexLine v 0)) (D a (complexLine v 0)) (E a (complexLine v 0)) v ∂μ) =
        v.im*(-β)*(1*v.im*(-β-1)*(1+0*v.im)^((-β-1)-1)) := by
      apply (integral_normFirst_line_derivative μ Q D E hQc hDc hEc hD hE v (zero_mem_lineDomain v)).unique
      apply hdR.congr_of_eventuallyEq
      filter_upwards [(isOpen_lineDomain v).mem_nhds (zero_mem_lineDomain v)] with s hs
      exact hm' hs
    simp only [complexLine_zero,one_mul,zero_mul,add_zero,Real.one_rpow,mul_one] at he
    exact he.trans (by ring)

lemma compact_holomorphic_moments.{u_1} {X : Type u_1} [TopologicalSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsFiniteMeasure μ]
    (Q D E : X → ℂ → ℂ)
    (hQc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => Q p.1 p.2))
    (hDc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => D p.1 p.2))
    (hEc : Continuous (fun p : X × {z : ℂ | 0 < z.im} => E p.1 p.2))
    (hD : ∀ a z, 0 < z.im → HasDerivAt (Q a) (D a z) z)
    (hE : ∀ a z, 0 < z.im → HasDerivAt (D a) (E a z) z)
    (hQ1 : ∀ a, Q a Complex.I = 1)
    (β : ℝ) (hmean : ∀ z : ℂ, 0 < z.im → (∫ a, ‖Q a z‖^2 ∂μ) = z.im^(-β)) :
    (∫ a, (Complex.I*D a Complex.I).re ∂μ) = -β/2 ∧
    (∫ a, (Complex.I*D a Complex.I).im ∂μ) = 0 ∧
    (∫ a, ‖Complex.I*D a Complex.I‖^2 ∂μ) = β*(β+1)/4 := by
  obtain ⟨hx,hxx⟩ := compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean 1
  obtain ⟨hy,hyy⟩ := compact_holomorphic_line_moments μ Q D E hQc hDc hEc hD hE β hmean Complex.I
  have hx' := hx
  have hy' := hy
  simp_rw [hQ1,norm_first_one] at hx'
  simp_rw [hQ1,norm_first_I] at hy'
  rw [integral_const_mul] at hx' hy'
  simp only [Complex.one_im,Complex.I_im,mul_zero,mul_one] at hx' hy' hxx hyy
  have hDc0 : Continuous (fun a => D a Complex.I) :=
    hDc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hQc0 : Continuous (fun a => Q a Complex.I) :=
    hQc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hEc0 : Continuous (fun a => E a Complex.I) :=
    hEc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp⟩ : {z : ℂ | 0 < z.im}))))
  have hi (v : ℂ) : Integrable (fun a => normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) v) μ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_normSecond.comp (hQc0.prodMk (hDc0.prodMk (hEc0.prodMk continuous_const)))
  have hsum : 4*(∫ a, ‖D a Complex.I‖^2 ∂μ) = β*(β+1) := by
    rw [← integral_const_mul]
    calc
      _ = ∫ a, normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) 1+
          normSecond (Q a Complex.I) (D a Complex.I) (E a Complex.I) Complex.I ∂μ := by
        apply integral_congr_ae
        exact Eventually.of_forall (fun a => (norm_second_laplacian _ _ _).symm)
      _ = _ := by rw [integral_add (hi 1) (hi Complex.I),hxx,hyy]; norm_num
  simp only [Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,zero_mul,one_mul,
    zero_sub,zero_add,Complex.norm_mul,Complex.norm_I]
  rw [integral_neg]
  exact ⟨by linarith,by linarith,by linarith⟩

lemma class_logarithmicJet_I (g : DiskClass) :
    logarithmicJet (classFun g) Complex.I = Complex.I*deriv (reciprocalDeriv (classFun g)) Complex.I := by
  simp only [logarithmicJet,Complex.I_im,Complex.ofReal_one,mul_one,classReciprocal_at_I,div_one]

lemma continuous_root_logarithmicJet : Continuous (fun g : DiskClass => logarithmicJet (classFun g) Complex.I) := by
  simp_rw [class_logarithmicJet_I]
  have hc : Continuous (fun p : DiskClass × halfPlane => deriv (reciprocalDeriv (classFun p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_reciprocalJet_eval 1
  exact (hc.comp (continuous_id.prodMk (continuous_const (y := (⟨Complex.I,by simp [halfPlane]⟩ : halfPlane))))).const_mul _

lemma weighted_law_moments (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-β)*(∫ g, f g ∂(P : Measure DiskClass))) :
    (∫ g, (logarithmicJet (classFun g) Complex.I).re ∂(P : Measure DiskClass)) = -β/2 ∧
    (∫ g, (logarithmicJet (classFun g) Complex.I).im ∂(P : Measure DiskClass)) = 0 ∧
    (∫ g, ‖logarithmicJet (classFun g) Complex.I‖^2 ∂(P : Measure DiskClass)) = β*(β+1)/4 := by
  have hcD : Continuous (fun p : DiskClass × halfPlane => deriv (reciprocalDeriv (classFun p.1)) p.2) := by
    simpa only [iteratedDeriv_one] using continuous_reciprocalJet_eval 1
  have hcE : Continuous (fun p : DiskClass × halfPlane => deriv (deriv (reciprocalDeriv (classFun p.1))) p.2) := by
    simpa only [show (2 : ℕ) = 1+1 from rfl,iteratedDeriv_succ,iteratedDeriv_one,iteratedDeriv_zero] using continuous_reciprocalJet_eval 2
  have hm (z : ℂ) (hz : 0 < z.im) :
      (∫ g, ‖reciprocalDeriv (classFun g) z‖^2 ∂(P : Measure DiskClass)) = z.im^(-β) := by
    simpa only [classWeight,ContinuousMap.one_apply,mul_one,integral_const,ProbabilityMeasure.coeFn_univ,
      probReal_univ,smul_eq_mul,one_mul] using hP ⟨z,hz⟩ 1
  have hE (g : DiskClass) (z : ℂ) (hz : 0 < z.im) :
      HasDerivAt (deriv (reciprocalDeriv (classFun g)))
        (deriv (deriv (reciprocalDeriv (classFun g))) z) z :=
    ((differentiableOn_classReciprocal g).analyticOnNhd isOpen_halfPlane z hz).deriv.differentiableAt.hasDerivAt
  simp_rw [class_logarithmicJet_I]
  exact compact_holomorphic_moments (P : Measure DiskClass)
    (fun g => reciprocalDeriv (classFun g)) (fun g => deriv (reciprocalDeriv (classFun g)))
    (fun g => deriv (deriv (reciprocalDeriv (classFun g))))
    continuous_classReciprocal_eval hcD hcE
    (fun g z hz => hasDerivAt_reciprocalDeriv (classFun_schlicht g).1 hz)
    hE classReciprocal_at_I β hm

lemma jacobian_expectation_value (P : ProbabilityMeasure DiskClass) (β : ℝ)
    (hP : ∀ z : halfPlane, ∀ f : C(DiskClass,ℝ),
      (∫ g, classWeight g z*f (rerootClass g z) ∂(P : Measure DiskClass)) =
        (z.val.im)^(-β)*(∫ g, f g ∂(P : Measure DiskClass)))
    {k : ℝ} (hk : k ≠ 0) :
    k^2 * (∫ g, normalizedJacobian (classFun g) k Complex.I ∂(P : Measure DiskClass)) =
      k*(k-1) - (2*k-1)*β/2 + β*(β+1)/4 := by
  obtain ⟨hr,-,hs⟩ := weighted_law_moments P β hP
  have hiR : Integrable (fun g : DiskClass => (2*k-1)*(logarithmicJet (classFun g) Complex.I).re) (P : Measure DiskClass) :=
    (continuous_const.mul (Complex.continuous_re.comp continuous_root_logarithmicJet)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiS : Integrable (fun g : DiskClass => ‖logarithmicJet (classFun g) Complex.I‖^2) (P : Measure DiskClass) :=
    (continuous_root_logarithmicJet.norm.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [← integral_const_mul]
  calc
    _ = ∫ g, k*(k-1)+(2*k-1)*(logarithmicJet (classFun g) Complex.I).re+
        ‖logarithmicJet (classFun g) Complex.I‖^2 ∂(P : Measure DiskClass) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun g => normalizedJacobian_formula (classFun_schlicht g).1 (by simp [halfPlane]) k hk)
    _ = _ := by
      have h1 := integral_add ((integrable_const (k*(k-1))).add hiR) hiS
      have h2 := integral_add (integrable_const (k*(k-1))) hiR
      simp only [Pi.add_apply] at h1 h2
      rw [h1,h2]
      simp only [integral_const_mul,integral_const,probReal_univ,smul_eq_mul,one_mul,hr,hs]
      ring

theorem transferRho_le_two : transferRho ≤ 2 := by
  by_contra! hρ
  obtain ⟨P,hP⟩ := exists_weighted_continuous_law hρ
  have hPb : HasWeightedLaw P transferBeta := by
    intro z f hf
    exact weighted_lintegral_of_continuous (P : Measure DiskClass) (weightAt z)
      (fun g => (classWeight_pos g z).le) (actionAt z) ((z.val.im)^(-transferBeta))
      (Real.rpow_nonneg z.2.le _) (hP z) f hf
  have hβ := transferBeta_gt_one hρ
  have hn := jacobian_expectation_nonpos P transferBeta hPb hβ
  have hv := jacobian_expectation_value P transferBeta hP (k := (transferBeta+3)/4) (by linarith)
  have hp : 0 < ((transferBeta+3)/4)*((transferBeta+3)/4-1) := mul_pos (by linarith) (by linarith)
  have he : ((transferBeta+3)/4)*((transferBeta+3)/4-1) -
      (2*((transferBeta+3)/4)-1)*transferBeta/2 + transferBeta*(transferBeta+1)/4 =
      ((transferBeta+3)/4)*((transferBeta+3)/4-1) := by ring
  rw [he] at hv
  have hnon := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg ((transferBeta+3)/4)) hn
  linarith

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.CircleBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma arc_cos_nonneg {θ : ℝ} (hθ : θ ∈ arcInterval) : 0 ≤ Real.cos θ := by
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> have hp := Real.pi_pos <;> dsimp [arcInterval] at hθ <;> linarith [hθ.1,hθ.2]

lemma arcD_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1 ≤ arcD r θ ∧ arcD r θ ≤ (1+r)^2 ∧ arcD r θ ≤ 4 := by
  have hc := arc_cos_nonneg hθ
  have hc1 := Real.cos_le_one θ
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 0 ≤ 2*r := by positivity
  dsimp [arcD]
  have hm := mul_nonneg hr2 hc
  have hm1 := mul_le_mul_of_nonneg_left hc1 hr2
  constructor
  · nlinarith [sq_nonneg r]
  constructor <;> nlinarith

lemma arcX_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    arcX r θ ∈ Icc (-1) 1 := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  have hs := Real.neg_one_le_sin θ
  have hs1 := Real.sin_le_one θ
  have h2r : 0 ≤ 2*r := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hs h2r
  have hm2 := mul_le_mul_of_nonneg_left hs1 h2r
  have hD2 : 2*r ≤ arcD r θ := by
    dsimp [arcD]
    nlinarith [mul_nonneg h2r hc,sq_nonneg (r-1)]
  constructor
  · exact (le_div_iff₀ hD).mpr (by nlinarith)
  · exact (div_le_iff₀ hD).mpr (by nlinarith)

lemma arcY_bounds {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    (1-r)/2 ≤ arcY r θ ∧ arcY r θ ≤ 2*(1-r) := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hr0 : 0 ≤ r := by linarith
  have hd0 : 0 ≤ 1-r := by linarith
  constructor
  · apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ (1-r)/2)
    have hb : (1-r)/2*(1+r)^2 ≤ 1-r^2 := by nlinarith [mul_nonneg hd0 (sq_nonneg (1+r))]
    exact h.trans hb
  · apply (div_le_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ 2*(1-r))
    nlinarith [sq_nonneg (r-1)]

lemma arcX_hasDerivAt {r θ : ℝ} (hD : arcD r θ ≠ 0) :
    HasDerivAt (arcX r) (arcXDeriv r θ) θ := by
  have hn := (Real.hasDerivAt_sin θ).const_mul (2*r)
  have hd := (((Real.hasDerivAt_cos θ).const_mul (2*r)).const_add 1).add_const (r^2)
  have h := hn.div hd hD
  change HasDerivAt (arcX r) _ θ at h
  have he : arcXDeriv r θ =
      (2*r*Real.cos θ*arcD r θ-2*r*Real.sin θ*(2*r * -Real.sin θ))/(arcD r θ)^2 := by
    unfold arcXDeriv arcD
    congr 1
    have hc := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg r]
  rw [he]
  exact h

lemma arcXDeriv_lower {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1/16 ≤ arcXDeriv r θ := by
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  dsimp only [arcXDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hm : 0 ≤ 2*r*(1+r^2)*Real.cos θ := mul_nonneg (by positivity) hc
  have hsq : (arcD r θ)^2 ≤ 16 := by nlinarith [hd.2.2]
  nlinarith [sq_nonneg (r-1/2)]

lemma continuousOn_arcXDeriv {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) :
    ContinuousOn (arcXDeriv r) arcInterval := by
  apply ContinuousOn.div
  · fun_prop
  · unfold arcD
    fun_prop
  · intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))

lemma arcX_monotone {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) : MonotoneOn (arcX r) arcInterval := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))).continuousAt.continuousWithinAt
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 (interior_subset hθ)).1))).hasDerivWithinAt
  · intro θ hθ
    exact le_trans (by norm_num) (arcXDeriv_lower hr hr1 (interior_subset hθ))

lemma circlePoint_norm (r θ : ℝ) : ‖circlePoint r θ‖ = |r| := by
  simp [circlePoint,Complex.norm_exp]

lemma circlePoint_re (r θ : ℝ) : (circlePoint r θ).re = r*Real.cos θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma circlePoint_im (r θ : ℝ) : (circlePoint r θ).im = r*Real.sin θ := by
  simp [circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma one_add_circlePoint_norm_sq (r θ : ℝ) : ‖1+circlePoint r θ‖^2 = arcD r θ := by
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.one_re,Complex.one_im,circlePoint_re,circlePoint_im,zero_add]
  dsimp [arcD]
  nlinarith [Real.sin_sq_add_cos_sq θ,sq_nonneg r]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : circlePoint r θ ∈ disk := by
  simpa [disk,circlePoint_norm,abs_of_nonneg hr] using hr1

lemma neg_circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) : -circlePoint r θ ∈ disk := by
  simpa only [disk,Metric.mem_ball,dist_zero_right,norm_neg] using circlePoint_mem_disk hr hr1 θ

lemma halfCayley_re (z : ℂ) : (halfCayley z).re = -2*z.im/‖1-z‖^2 := by
  simp only [halfCayley,Complex.div_re,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.add_re,Complex.add_im,Complex.one_re,
    Complex.one_im,Complex.sub_re,Complex.sub_im,Complex.sq_norm,Complex.normSq_apply]
  ring

lemma halfCayley_neg_circlePoint {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    halfCayley (-circlePoint r θ) = (arcX r θ:ℂ)+(arcY r θ:ℂ)*Complex.I := by
  have hz := neg_circlePoint_mem_disk hr hr1 θ
  apply Complex.ext
  · rw [halfCayley_re]
    simp only [Complex.neg_im,circlePoint_im,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.ofReal_im,Complex.I_im]
    dsimp [arcX]
    ring
  · rw [halfCayley_im hz]
    simp only [norm_neg,circlePoint_norm,abs_of_nonneg hr,sub_neg_eq_add,one_add_circlePoint_norm_sq,
      Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,Complex.ofReal_re,Complex.I_im]
    simp [arcY]

lemma classWeight_vertical_bound (g : DiskClass) {η : ℝ} (hη : 1/2 ≤ η) (hη4 : η ≤ 4) :
    classWeight g (halfPoint 0 η (by linarith)) ≤ 1562500 := by
  let z := halfPoint 0 η (by linarith : 0 < η)
  have hb := classFun_reciprocal_bound g z
  have he : ‖z.val+Complex.I‖ = η+1 := by
    have hz : z.val+Complex.I = ((η+1:ℝ):ℂ)*Complex.I := by
      dsimp [z,halfPoint]
      push_cast
      ring
    rw [hz,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith)]
  have hη0 : 0 < η := by linarith
  have ht : ‖reciprocalDeriv (classFun g) z‖ ≤ 1250 := by
    rw [he] at hb
    simp only [z,halfPoint,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.ofReal_re,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero,zero_add] at hb
    have hp : (η+1)^4 ≤ (5:ℝ)^4 := pow_le_pow_left₀ (by linarith) (by linarith) _
    apply hb.trans
    apply (div_le_iff₀ hη0).mpr
    norm_num at hp
    linarith
  unfold classWeight
  change ‖reciprocalDeriv (classFun g) z‖^2 ≤ _
  nlinarith [norm_nonneg (reciprocalDeriv (classFun g) z)]

lemma classWeight_vertical_compare (g : DiskClass) (x v y : ℝ) (hv : 0 < v)
    (hy : v/2 ≤ y) (hy4 : y ≤ 4*v) :
    classWeight g (halfPoint x y (by linarith)) ≤
      1562500*classWeight g (halfPoint x v hv) := by
  have hη : 1/2 ≤ y/v := (le_div_iff₀ hv).mpr (by linarith)
  have hη4 : y/v ≤ 4 := (div_le_iff₀ hv).mpr hy4
  have hη0 : 0 < y/v := by linarith
  have he : halfMul (halfPoint x v hv) (halfPoint 0 (y/v) hη0) = halfPoint x y (by linarith) := by
    rw [halfPoint_mul]
    apply Subtype.ext
    dsimp [halfPoint]
    congr 2 <;> simp [mul_div_cancel₀ y hv.ne']
  have hc := classWeight_cocycle g (halfPoint x v hv) (halfPoint 0 (y/v) hη0)
  change _ = classWeight g (halfMul _ _) at hc
  rw [he] at hc
  rw [← hc,mul_comm (1562500:ℝ)]
  exact mul_le_mul_of_nonneg_left (classWeight_vertical_bound _ hη hη4) (classWeight_pos g _).le

lemma inverse_deriv_square_conversion {f : ℂ → ℂ} (hf : Schlicht f) {w : ℂ} (hw : w ∈ disk) :
    ‖deriv f w‖^(-2:ℝ) ≤ 16*classWeight (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf))
      ⟨halfCayley w,halfCayley_maps hw⟩ := by
  let g := classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)
  let z : halfPlane := ⟨halfCayley w,halfCayley_maps hw⟩
  have he := (classFun_classOfHalf (diskToHalf_schlicht hf)).deriv isOpen_halfPlane z.2
  have hfhe : EqOn (halfToDisk (diskToHalf f)) f disk := fun _ hz => halfToDisk_diskToHalf hz
  have hd := (hasDerivAt_halfToDisk (diskToHalf_schlicht hf).1.1 hw).deriv
  rw [hfhe.deriv Metric.isOpen_ball hw] at hd
  have hw1 : ‖w‖ < 1 := by simpa [disk] using hw
  have hb : ‖1-w‖ ≤ 2 := (norm_sub_le _ _).trans (by simpa using (show 1+‖w‖ ≤ 2 by linarith))
  have ha : 0 < ‖deriv (diskToHalf f) (halfCayley w)‖ := norm_pos_iff.mpr
    (univalent_deriv_ne_zero isOpen_halfPlane (diskToHalf_schlicht hf).1 z.2)
  rw [hd,norm_div,norm_pow,Real.rpow_neg (by positivity),Real.rpow_two]
  unfold classWeight
  change _ ≤ 16*‖reciprocalDeriv (classFun g) z‖^2
  rw [reciprocalDeriv,he,norm_inv]
  have hb4 : ‖1-w‖^4 ≤ (2:ℝ)^4 := pow_le_pow_left₀ (norm_nonneg _) hb _
  have hz0 : ‖1-w‖ ≠ 0 := norm_ne_zero_iff.mpr (halfCayley_den_ne_zero hw)
  dsimp only [z]
  field_simp [ha.ne',hz0]
  nlinarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_weightAt : Continuous weightAt := by
  have he : weightAt = fun z => affineOperator z 1 := by
    funext z
    ext g
    simp only [affineOperator_apply,ContinuousMap.one_apply,mul_one]
    rfl
  rw [he]
  exact continuous_affineOperator_apply 1

lemma horizontalMass_apply (v : ℝ) (hv : 0 < v) (g : DiskClass) :
    horizontalMass v hv g = ∫ x in (-1:ℝ)..1, classWeight g (halfPoint x v hv) := by
  exact ((ContinuousMap.evalCLM ℝ g).intervalIntegral_comp_comm
    ((continuous_weightAt.comp (continuous_halfPoint continuous_id continuous_const (fun _ => hv))).intervalIntegrable (μ := volume) _ _)).symm

lemma continuous_horizontalWeight (g : DiskClass) (v : ℝ) (hv : 0 < v) :
    Continuous (fun x => classWeight g (halfPoint x v hv)) :=
  continuous_classWeight.comp (continuous_const.prodMk
    (continuous_halfPoint continuous_id continuous_const (fun _ => hv)))

lemma horizontalMass_half (v : ℝ) (hv : 0 < v) :
    horizontalMass (v/2) (by positivity) = transferOperator (horizontalMass v hv) := by
  ext g
  rw [horizontalMass_apply]
  change _ = (1/2:ℝ)*(classWeight g dyadicLeft * horizontalMass v hv (rerootClass g dyadicLeft)+
    classWeight g dyadicRight * horizontalMass v hv (rerootClass g dyadicRight))
  rw [horizontalMass_apply,horizontalMass_apply,← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_const_mul]
  have hL (x : ℝ) : classWeight g dyadicLeft * classWeight (rerootClass g dyadicLeft) (halfPoint x v hv) =
      classWeight g (halfPoint ((1/2)*x+(-(1/2))) (v/2) (by positivity)) := by
    rw [classWeight_cocycle]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [dyadicLeft,halfPoint,affine] <;> ring
  have hR (x : ℝ) : classWeight g dyadicRight * classWeight (rerootClass g dyadicRight) (halfPoint x v hv) =
      classWeight g (halfPoint ((1/2)*x+1/2) (v/2) (by positivity)) := by
    rw [classWeight_cocycle]
    congr 1
    apply Subtype.ext
    apply Complex.ext <;> simp [dyadicRight,halfPoint,affine] <;> ring
  simp_rw [hL,hR]
  have hl := intervalIntegral.integral_comp_mul_add
    (f := fun x => classWeight g (halfPoint x (v/2) (by positivity)))
    (a := (-1:ℝ)) (b := 1) (by norm_num : (1/2:ℝ) ≠ 0) (-1/2)
  have hr := intervalIntegral.integral_comp_mul_add
    (f := fun x => classWeight g (halfPoint x (v/2) (by positivity)))
    (a := (-1:ℝ)) (b := 1) (by norm_num : (1/2:ℝ) ≠ 0) (1/2)
  norm_num at hl hr
  have hi := (continuous_horizontalWeight g (v/2) (by positivity)).intervalIntegrable (μ := volume)
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1)
  rw [hl,hr]
  linarith [hs]

lemma horizontalMass_dyadic (n : ℕ) :
    horizontalMass ((1/2:ℝ)^n) (by positivity) = (transferOperator^n) (horizontalMass 1 zero_lt_one) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have he : (1/2:ℝ)^(n+1) = (1/2:ℝ)^n/2 := by rw [pow_succ]; ring
    have hm : horizontalMass ((1/2:ℝ)^(n+1)) (by positivity) = horizontalMass ((1/2:ℝ)^n/2) (by positivity) := by congr 1
    rw [hm,horizontalMass_half _ (by positivity),ih,pow_succ',mul_apply_eq_comp]

lemma horizontalMass_dyadic_le (n : ℕ) (g : DiskClass) :
    (∫ x in (-1:ℝ)..1, classWeight g (halfPoint x ((1/2:ℝ)^n) (by positivity))) ≤
      ‖horizontalMass 1 zero_lt_one‖*‖transferOperator^n‖ := by
  rw [← horizontalMass_apply,horizontalMass_dyadic,mul_comm]
  exact (le_abs_self _).trans ((ContinuousMap.norm_coe_le_norm _ _).trans ((transferOperator^n).le_opNorm _))

lemma transferOperator_uniform_growth {lam : ℝ} (hlam : 2 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ‖transferOperator^n‖ ≤ C*lam^n := by
  have hl : 0 < lam := by linarith
  obtain ⟨N,hN⟩ := eventually_atTop.mp (norm_pow_eventually_le transferOperator transferOperator_pow_norm_ge_one
    (lt_of_le_of_lt transferRho_le_two hlam))
  let C : ℝ := 1 + ∑ j ∈ Finset.range N, ‖transferOperator^j‖/lam^j
  have hC : 1 ≤ C := le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ => div_nonneg (norm_nonneg (transferOperator^j)) (pow_pos hl j).le))
  refine ⟨C,zero_lt_one.trans_le hC,fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_pos hl n).le hC)
  · have hs : ‖transferOperator^n‖/lam^n ≤ ∑ j ∈ Finset.range N, ‖transferOperator^j‖/lam^j :=
      Finset.single_le_sum (fun j _ => div_nonneg (norm_nonneg (transferOperator^j)) (pow_pos hl j).le) (Finset.mem_range.mpr (lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hl n)).mp
    exact hs.trans (by dsimp [C]; linarith)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
  unfold circlePoint
  fun_prop

lemma continuous_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r)
      (circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (circlePoint_mem_disk hr hr1 θ))))

lemma continuous_neg_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (-circlePoint r θ)‖^t) := by
  have hc : Continuous (fun θ => deriv f (-circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r).neg
      (neg_circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (univalent_deriv_ne_zero Metric.isOpen_ball hf (neg_circlePoint_mem_disk hr hr1 θ))))

lemma arc_integral_bound {f : ℂ → ℂ} (hf : Schlicht f) {r v : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (hv : 0 < v) (hvδ : v ≤ 1-r) (hδv : 1-r ≤ 2*v) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4), ‖deriv f (-circlePoint r θ)‖^(-2:ℝ)) ≤
      400000000 * horizontalMass v hv (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)) := by
  let g := classOfHalf (diskToHalf f) (diskToHalf_schlicht hf)
  let W : ℝ → ℝ := fun x => classWeight g (halfPoint x v hv)
  have hW : Continuous W := continuous_horizontalWeight g v hv
  have hab : -Real.pi/4 ≤ Real.pi/4 := by linarith [Real.pi_pos]
  have hu : uIcc (-Real.pi/4) (Real.pi/4) = arcInterval := uIcc_of_le hab
  have hX (θ : ℝ) (hθ : θ ∈ arcInterval) : HasDerivAt (arcX r) (arcXDeriv r θ) θ :=
    arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))
  have hXc : ContinuousOn (arcX r) arcInterval := fun θ hθ => (hX θ hθ).continuousAt.continuousWithinAt
  have hprod : ContinuousOn (fun θ => W (arcX r θ)*arcXDeriv r θ) arcInterval :=
    (hW.comp_continuousOn hXc).mul (continuousOn_arcXDeriv hr hr1)
  have hi := intervalIntegral.integral_mono_on hab
    ((continuous_neg_circle_deriv_rpow hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume) _ _)
    ((hprod.const_mul 400000000).intervalIntegrable_of_Icc hab)
    (fun θ hθ => show ‖deriv f (-circlePoint r θ)‖^(-2:ℝ) ≤
      400000000*(W (arcX r θ)*arcXDeriv r θ) from by
      have hθ' : θ ∈ arcInterval := hθ
      have hy := arcY_bounds hr hr1 hθ'
      have hz : (⟨halfCayley (-circlePoint r θ),halfCayley_maps (neg_circlePoint_mem_disk (by linarith) hr1 θ)⟩ : halfPlane) =
          halfPoint (arcX r θ) (arcY r θ) (by linarith) :=
        Subtype.ext (halfCayley_neg_circlePoint (by linarith) hr1 θ)
      have hc := inverse_deriv_square_conversion hf (neg_circlePoint_mem_disk (by linarith) hr1 θ)
      rw [hz] at hc
      have hb := classWeight_vertical_compare g (arcX r θ) v (arcY r θ) hv (by linarith) (by linarith)
      have hd := arcXDeriv_lower hr hr1 hθ'
      have hWp : 0 ≤ W (arcX r θ) := (classWeight_pos g _).le
      have hm := mul_nonneg hWp (sub_nonneg.mpr hd)
      change _ ≤ 16*classWeight g _ at hc
      change classWeight g _ ≤ 1562500*W (arcX r θ) at hb
      nlinarith)
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (fun θ hθ => hX θ (hu ▸ hθ)) (hu ▸ continuousOn_arcXDeriv hr hr1) hW
  change (∫ θ in (-Real.pi/4)..(Real.pi/4), W (arcX r θ)*arcXDeriv r θ) = _ at hchange
  rw [hchange] at hi
  have hlo : -Real.pi/4 ∈ arcInterval := ⟨le_rfl,hab⟩
  have hhi : Real.pi/4 ∈ arcInterval := ⟨hab,le_rfl⟩
  have hm := arcX_monotone hr hr1 hlo hhi hab
  have hb := intervalIntegral.integral_mono_interval (arcX_bounds hr hr1 hlo).1 hm
    (arcX_bounds hr hr1 hhi).2
    (Eventually.of_forall (fun x => (classWeight_pos g (halfPoint x v hv)).le))
    (hW.intervalIntegrable (μ := volume) (-1) 1)
  rw [horizontalMass_apply]
  exact hi.trans (mul_le_mul_of_nonneg_left hb (by norm_num))

lemma arc_integral_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in (-Real.pi/4)..(Real.pi/4), ‖deriv f (-circlePoint r θ)‖^(-2:ℝ)) ≤
      (400000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  have hb := arc_integral_bound hf hr hr1 (by positivity) hvδ hδv
  have hm := horizontalMass_dyadic_le n (classOfHalf (diskToHalf f) (diskToHalf_schlicht hf))
  rw [← horizontalMass_apply] at hm
  exact hb.trans ((mul_le_mul_of_nonneg_left hm (by norm_num)).trans_eq (by ring))

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan
attribute [local irreducible] classFun classWeight rerootClass

lemma rotateDisk_maps {α : ℂ} (hα : ‖α‖ = 1) : MapsTo (fun z => α*z) disk disk := by
  intro z hz
  simpa [disk,norm_mul,hα] using hz

lemma rotateDisk_hasDerivAt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f disk)
    {α z : ℂ} (hα : ‖α‖ = 1) (hz : z ∈ disk) :
    HasDerivAt (rotateDisk f α) (deriv f (α*z)) z := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  have hd := ((hf _ (rotateDisk_maps hα hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (rotateDisk_maps hα hz))).hasDerivAt
  convert (hd.comp z ((hasDerivAt_id z).const_mul α)).div_const α using 1 <;> try rfl
  simp [hα0]

lemma rotateDisk_schlicht {f : ℂ → ℂ} (hf : Schlicht f) {α : ℂ} (hα : ‖α‖ = 1) :
    Schlicht (rotateDisk f α) := by
  have hα0 : α ≠ 0 := by intro h; simp [h] at hα
  refine ⟨⟨fun z hz => (rotateDisk_hasDerivAt hf.1.1 hα hz).differentiableAt.differentiableWithinAt,?_⟩,?_,?_⟩
  · intro z hz w hw he
    exact mul_left_cancel₀ hα0 (hf.1.2 (rotateDisk_maps hα hz) (rotateDisk_maps hα hw)
      ((div_left_inj' hα0).mp he))
  · simp [rotateDisk,hf.2.1]
  · rw [(rotateDisk_hasDerivAt hf.1.1 hα (show (0:ℂ) ∈ disk by simp [disk])).deriv]
    simpa using hf.2.2

lemma circlePoint_shift (r θ c : ℝ) :
    (-Complex.exp ((c:ℂ)*Complex.I))*(-circlePoint r θ) = circlePoint r (θ+c) := by
  simp only [circlePoint,Complex.ofReal_add,add_mul,Complex.exp_add,neg_mul_neg]
  ring

lemma circle_arc_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) (c : ℝ) :
    (∫ θ in (c-Real.pi/4)..(c+Real.pi/4), ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤
      (400000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  let α := -Complex.exp ((c:ℂ)*Complex.I)
  have hα : ‖α‖ = 1 := by simp [α,Complex.norm_exp]
  have hb := arc_integral_dyadic_bound (rotateDisk_schlicht hf hα) hr hr1 n hvδ hδv
  have he (θ : ℝ) : deriv (rotateDisk f α) (-circlePoint r θ) = deriv f (circlePoint r (θ+c)) := by
    rw [(rotateDisk_hasDerivAt hf.1.1 hα (neg_circlePoint_mem_disk (by linarith) hr1 θ)).deriv]
    rw [show α*(-circlePoint r θ) = circlePoint r (θ+c) from circlePoint_shift r θ c]
  simp_rw [he] at hb
  rw [intervalIntegral.integral_comp_add_right (f := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) c] at hb
  convert hb using 1
  congr 1 <;> ring

lemma periodic_circlePoint (r : ℝ) : Periodic (circlePoint r) (2*Real.pi) := by
  simpa [circlePoint,circleMap] using periodic_circleMap (0:ℂ) r

lemma full_circle_dyadic_bound {f : ℂ → ℂ} (hf : Schlicht f) {r : ℝ}
    (hr : 1/2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : (1/2:ℝ)^n ≤ 1-r) (hδv : 1-r ≤ 2*(1/2:ℝ)^n) :
    (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤
      (1600000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^n‖ := by
  let F : ℝ → ℝ := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ)
  have hF := (continuous_circle_deriv_rpow hf.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hper : Periodic F (2*Real.pi) := (periodic_circlePoint r).comp (fun z => ‖deriv f z‖^(-2:ℝ))
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) (-Real.pi/4)
  have h1 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv 0
  have h2 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (Real.pi/2)
  have h3 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv Real.pi
  have h4 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (3*Real.pi/2)
  have e1 : (0:ℝ)-Real.pi/4 = -Real.pi/4 := by ring
  have e2 : (0:ℝ)+Real.pi/4 = Real.pi/4 := by ring
  have e3 : Real.pi/2-Real.pi/4 = Real.pi/4 := by ring
  have e4 : Real.pi/2+Real.pi/4 = 3*Real.pi/4 := by ring
  have e5 : Real.pi-Real.pi/4 = 3*Real.pi/4 := by ring
  have e6 : Real.pi+Real.pi/4 = 5*Real.pi/4 := by ring
  have e7 : 3*Real.pi/2-Real.pi/4 = 5*Real.pi/4 := by ring
  have e8 : 3*Real.pi/2+Real.pi/4 = 7*Real.pi/4 := by ring
  rw [e1,e2] at h1
  rw [e3,e4] at h2
  rw [e5,e6] at h3
  rw [e7,e8] at h4
  have ha := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (Real.pi/4)) (hF (Real.pi/4) (3*Real.pi/4))
  have hb := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (3*Real.pi/4)) (hF (3*Real.pi/4) (5*Real.pi/4))
  have hc := intervalIntegral.integral_add_adjacent_intervals (hF (-Real.pi/4) (5*Real.pi/4)) (hF (5*Real.pi/4) (7*Real.pi/4))
  have es1 : -Real.pi+2*Real.pi = Real.pi := by ring
  have es2 : -Real.pi/4+2*Real.pi = 7*Real.pi/4 := by ring
  rw [es1,es2] at hshift
  dsimp only [F] at hshift
  linarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma dyadic_growth_compare {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) {n : ℕ}
    (hn : δ ≤ 2*(1/2:ℝ)^n) :
    ((2:ℝ)^a)^n ≤ (2:ℝ)^a * δ^(-a) := by
  have hv : 0 < (1/2:ℝ)^n := by positivity
  have he : ((2:ℝ)^a)^n = ((1/2:ℝ)^n)^(-a) := by
    rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num),← Real.rpow_natCast (1/2:ℝ),
      ← Real.rpow_mul (by norm_num)]
    rw [show (1/2:ℝ) = 2^(-1:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  rw [he]
  have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ/2)
    (show δ/2 ≤ (1/2:ℝ)^n by linarith) (neg_nonpos.mpr ha)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hδ.le (by norm_num),Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),div_inv_eq_mul,mul_comm]

lemma uniform_inverse_square_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Schlicht f → ∀ r : ℝ, 1/2 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C*(1-r)^(-1-ε) := by
  have hlam : 2 < (2:ℝ)^(1+ε) := by
    calc
      (2:ℝ) = 2^(1:ℝ) := by rw [Real.rpow_one]
      _ < 2^(1+ε) := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith)
  obtain ⟨K,hK,hKn⟩ := transferOperator_uniform_growth hlam
  let A := (2*Real.pi)⁻¹*(1600000000*‖horizontalMass 1 zero_lt_one‖)*K*(2:ℝ)^(1+ε)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A+1,by linarith,fun f hf r hr hr1 => ?_⟩
  obtain ⟨n,hn1,hn2⟩ := exists_nat_pow_near_of_lt_one (by linarith : 0 < 1-r)
    (by linarith : 1-r ≤ 1) (by norm_num : (0:ℝ) < 1/2) (by norm_num : (1/2:ℝ) < 1)
  have hn : 1-r ≤ 2*(1/2:ℝ)^(n+1) := by rw [pow_succ]; nlinarith
  have hb := full_circle_dyadic_bound hf hr hr1 (n+1) hn1.le hn
  have hc := dyadic_growth_compare (by linarith : 0 ≤ 1+ε) (by linarith : 0 < 1-r) hn
  have hx : 0 ≤ (2*Real.pi)⁻¹ := by positivity
  have hy : 0 ≤ 1600000000*‖horizontalMass 1 zero_lt_one‖ := by positivity
  have he : (-1-ε:ℝ) = -(1+ε) := by ring
  change (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤ _
  calc
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*‖transferOperator^(n+1)‖) :=
      mul_le_mul_of_nonneg_left hb hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε))^(n+1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKn (n+1)) hy) hx
    _ ≤ (2*Real.pi)⁻¹*((1600000000*‖horizontalMass 1 zero_lt_one‖)*(K*((2:ℝ)^(1+ε)*(1-r)^(-(1+ε))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK.le) hy) hx
    _ = A*(1-r)^(-1-ε) := by rw [he]; dsimp [A]; ring
    _ ≤ (A+1)*(1-r)^(-1-ε) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Koebe
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma one_sub_ne_zero_disk {z : ℂ} (hz : z ∈ disk) : 1-z ≠ 0 := by
  have h : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have : z = 1 := by linear_combination -he
  simp [this] at h

lemma koebeMap_hasDerivAt {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt koebeMap ((1+z)/(1-z)^3) z := by
  have hn := one_sub_ne_zero_disk hz
  have h := (hasDerivAt_id z).div (((hasDerivAt_const z (1:ℂ)).sub (hasDerivAt_id z)).pow 2) (pow_ne_zero 2 hn)
  convert h using 1 <;> try rfl
  dsimp
  field_simp [hn]
  ring

lemma koebeMap_schlicht : Schlicht koebeMap := by
  refine ⟨⟨fun z hz => (koebeMap_hasDerivAt hz).differentiableAt.differentiableWithinAt,?_⟩,by simp [koebeMap],?_⟩
  · intro z hz w hw he
    have hnz := one_sub_ne_zero_disk hz
    have hnw := one_sub_ne_zero_disk hw
    have he' : (z-w)*(1-z*w) = 0 := by
      have hh := (div_eq_div_iff (pow_ne_zero 2 hnz) (pow_ne_zero 2 hnw)).mp he
      linear_combination hh
    have hzw : 1-z*w ≠ 0 := by
      have hz' : ‖z‖ < 1 := by simpa [disk] using hz
      have hw' : ‖w‖ < 1 := by simpa [disk] using hw
      have hn : ‖z*w‖ < 1 := by rw [norm_mul]; nlinarith [norm_nonneg z,norm_nonneg w]
      intro h
      have : z*w = 1 := by linear_combination -h
      simp [this] at hn
    exact sub_eq_zero.mp ((mul_eq_zero.mp he').resolve_right hzw)
  · simpa using (koebeMap_hasDerivAt (show (0:ℂ) ∈ disk by simp [disk])).deriv

lemma koebe_arc_deriv_bound {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hθ : |θ| ≤ 1-r) : ‖deriv koebeMap (-circlePoint r θ)‖ ≤ 2*(1-r) := by
  have hr0 : 0 ≤ r := by linarith
  have hδ : 0 < 1-r := by linarith
  have hcos : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by
    have hp := Real.pi_gt_three; have := (abs_le.mp hθ).1; linarith,
    by have hp := Real.pi_gt_three; have := (abs_le.mp hθ).2; linarith⟩
  have he : ‖Complex.exp ((θ:ℂ)*Complex.I)-1‖ ≤ |θ| := by
    simpa [mul_comm] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ))
  have hnum : ‖1-circlePoint r θ‖ ≤ 2*(1-r) := by
    have hident : (1:ℂ)-circlePoint r θ = ((1-r:ℝ):ℂ)-(r:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1) := by
      simp only [circlePoint,Complex.ofReal_sub,Complex.ofReal_one]; ring
    rw [hident]
    calc
      _ ≤ ‖((1-r:ℝ):ℂ)‖+‖(r:ℂ)*(Complex.exp ((θ:ℂ)*Complex.I)-1)‖ := norm_sub_le _ _
      _ ≤ (1-r)+r*|θ| := by
        rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos hδ,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr0]
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left he hr0)
      _ ≤ 2*(1-r) := by nlinarith [abs_nonneg θ]
  have hden : 1 ≤ ‖1+circlePoint r θ‖ := by
    calc
      (1:ℝ) ≤ ((1:ℂ)+circlePoint r θ).re := by
        simp [circlePoint,Complex.exp_mul_I,Complex.mul_re]
        exact mul_nonneg hr0 hcos
      _ ≤ ‖1+circlePoint r θ‖ := Complex.re_le_norm _
  rw [(koebeMap_hasDerivAt (neg_circlePoint_mem_disk hr0 hr1 θ)).deriv,norm_div,norm_pow]
  simp only [← sub_eq_add_neg,sub_neg_eq_add]
  exact (div_le_self (norm_nonneg _) (one_le_pow₀ hden)).trans hnum

lemma koebe_arc_inverse_lower {r θ : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1)
    (hθ : |θ| ≤ 1-r) : 1/(4*(1-r)^2) ≤ ‖deriv koebeMap (-circlePoint r θ)‖^(-2:ℝ) := by
  have hn := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball koebeMap_schlicht.1
    (neg_circlePoint_mem_disk (by linarith) hr1 θ))
  have hb := Real.rpow_le_rpow_of_nonpos hn (koebe_arc_deriv_bound hr hr1 hθ) (by norm_num : (-2:ℝ) ≤ 0)
  refine (show 1/(4*(1-r)^2) = (2*(1-r))^(-2:ℝ) by
    rw [Real.rpow_neg (by positivity),Real.rpow_two]; ring).trans_le hb

lemma koebe_mean_lower {r : ℝ} (hr : 1/2 ≤ r) (hr1 : r < 1) :
    1/(4*Real.pi*(1-r)) ≤ integralMean koebeMap (-2) r := by
  let F : ℝ → ℝ := fun θ => ‖deriv koebeMap (circlePoint r θ)‖^(-2:ℝ)
  let G : ℝ → ℝ := fun θ => ‖deriv koebeMap (-circlePoint r θ)‖^(-2:ℝ)
  have hF := (continuous_circle_deriv_rpow koebeMap_schlicht.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hG := (continuous_neg_circle_deriv_rpow koebeMap_schlicht.1 (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hfull : (∫ θ in -Real.pi..Real.pi, G θ) = ∫ θ in -Real.pi..Real.pi, F θ := by
    have he (θ : ℝ) : G θ = F (θ+Real.pi) := by
      dsimp [G,F]
      congr 3
      simp [circlePoint,Complex.ofReal_add,add_mul,Complex.exp_add,Complex.exp_pi_mul_I]
    simp_rw [he]
    rw [intervalIntegral.integral_comp_add_right (f := F) Real.pi]
    have hp := ((periodic_circlePoint r).comp (fun z => ‖deriv koebeMap z‖^(-2:ℝ))).intervalIntegral_add_eq (-Real.pi) 0
    convert hp.symm using 1 <;> congr 1 <;> ring
  have hδ : 0 < 1-r := by linarith
  have hpart := intervalIntegral.integral_mono_on (by linarith : -(1-r) ≤ 1-r)
    (intervalIntegrable_const (a := -(1-r)) (b := 1-r) (c := 1/(4*(1-r)^2)))
    (hG (-(1-r)) (1-r)) (fun θ hθ => koebe_arc_inverse_lower hr hr1 (abs_le.mpr hθ))
  have heq : (∫ _ in -(1-r)..(1-r), 1/(4*(1-r)^2)) = 1/(2*(1-r)) := by
    rw [intervalIntegral.integral_const,smul_eq_mul]; field_simp; ring
  rw [heq] at hpart
  have hlarge := intervalIntegral.integral_mono_interval
    (by linarith [Real.pi_gt_three] : -Real.pi ≤ -(1-r)) (by linarith : -(1-r) ≤ 1-r)
    (by linarith [Real.pi_gt_three] : 1-r ≤ Real.pi)
    (Eventually.of_forall (fun θ => Real.rpow_nonneg (norm_nonneg (deriv koebeMap (-circlePoint r θ))) (-2))) (hG (-Real.pi) Real.pi)
  change _ ≤ integralMean koebeMap (-2) r
  calc
    _ = (2*Real.pi)⁻¹*(1/(2*(1-r))) := by field_simp; ring
    _ ≤ (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi, G θ) :=
      mul_le_mul_of_nonneg_left (hpart.trans hlarge) (by positivity)
    _ = integralMean koebeMap (-2) r := by rw [hfull]; rfl

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Spectrum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma integralMean_pos {f : ℂ → ℂ} (hf : UnivalentOn f disk) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r < 1) (t : ℝ) : 0 < integralMean f t r := by
  apply mul_pos (by positivity)
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (continuous_circle_deriv_rpow hf hr0 hr1 t).continuousOn
    (fun θ _ => Real.rpow_nonneg (norm_nonneg _) t)
  refine ⟨0,⟨by linarith [Real.pi_pos],by linarith [Real.pi_pos]⟩,?_⟩
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf
    (circlePoint_mem_disk hr0 hr1 0))) t

lemma tendsto_log_boundary : Tendsto (fun r : ℝ => Real.log (1/(1-r))) (𝓝[<] (1:ℝ)) atTop := by
  have hδ : Tendsto (fun r : ℝ => 1-r) (𝓝[<] (1:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun r : ℝ => 1-r) := continuous_const.sub continuous_id
      have h := hc.continuousAt.tendsto.mono_left
        (nhdsWithin_le_nhds : 𝓝[<] (1:ℝ) ≤ 𝓝 1)
      simpa only [sub_self] using h
    · filter_upwards [self_mem_nhdsWithin] with r hr
      exact sub_pos.mpr (show r < 1 from hr)
  have h := tendsto_neg_atBot_atTop.comp (Real.tendsto_log_nhdsGT_zero.comp hδ)
  simpa only [Function.comp_def,one_div,Real.log_inv] using h

lemma eventually_radius : ∀ᶠ r : ℝ in 𝓝[<] (1:ℝ), 1/2 ≤ r ∧ r < 1 := by
  filter_upwards [eventually_nhdsWithin_of_eventually_nhds (eventually_gt_nhds (by norm_num : (1/2:ℝ) < 1)),self_mem_nhdsWithin] with r hr hr1
  exact ⟨hr.le,hr1⟩

lemma log_power_upper {M C a r : ℝ} (hM : 0 < M) (hC : 0 < C)
    (hr : 0 < r) (hr1 : r < 1) (h : M ≤ C*(1-r)^(-a)) :
    Real.log M / Real.log (1/(1-r)) ≤ Real.log C / Real.log (1/(1-r)) + a := by
  have hd : 0 < 1-r := by linarith
  have hl : 0 < Real.log (1/(1-r)) := Real.log_pos ((one_lt_div hd).mpr (by linarith))
  have hb := Real.log_le_log hM h
  rw [Real.log_mul hC.ne' (Real.rpow_pos_of_pos hd _).ne',Real.log_rpow hd] at hb
  have he : Real.log (1/(1-r)) = -Real.log (1-r) := by simp [one_div]
  rw [div_le_iff₀ hl]
  calc
    Real.log M ≤ Real.log C + (-a)*Real.log (1-r) := hb
    _ = (Real.log C / Real.log (1/(1-r))+a)*Real.log (1/(1-r)) := by
      rw [add_mul,div_mul_cancel₀ _ hl.ne',he]; ring

lemma beta_inverse_le_one {f : ℂ → ℂ} (hf : Schlicht f) : beta f (-2) ≤ 1 := by
  have hb (ε : ℝ) (hε : 0 < ε) : beta f (-2) ≤ ((1+ε:ℝ):EReal) := by
    obtain ⟨C,hC,hbound⟩ := uniform_inverse_square_bound ε hε
    have hc : Tendsto (fun r : ℝ => ((Real.log C/Real.log (1/(1-r))+(1+ε):ℝ):EReal))
        (𝓝[<] (1:ℝ)) (𝓝 ((1+ε:ℝ):EReal)) := by
      have hh := (tendsto_log_boundary.const_div_atTop (Real.log C)).add_const (1+ε)
      simpa [Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hh
    rw [← hc.limsup_eq]
    refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
    filter_upwards [eventually_radius] with r hr
    apply EReal.coe_le_coe
    exact log_power_upper (integralMean_pos hf.1 (by linarith [hr.1]) hr.2 (-2)) hC
      (by linarith [hr.1]) hr.2 (by simpa only [show -(1+ε) = -1-ε by ring] using hbound f hf r hr.1 hr.2)
  by_contra h
  obtain ⟨a,ha,hfa⟩ := EReal.exists_between_coe_real (lt_of_not_ge h)
  have ha' : 1 < a := by exact_mod_cast ha
  have he := hb ((a-1)/2) (by linarith)
  have he' : ((1+(a-1)/2:ℝ):EReal) < a := EReal.coe_lt_coe_iff.mpr (by linarith)
  exact (not_lt_of_ge he) (he'.trans hfa)

lemma koebe_beta_ge_one : 1 ≤ beta koebeMap (-2) := by
  let C : ℝ := 1/(4*Real.pi)
  have hC : 0 < C := by dsimp [C]; positivity
  have hc : Tendsto (fun r : ℝ => ((Real.log C/Real.log (1/(1-r))+1:ℝ):EReal))
      (𝓝[<] (1:ℝ)) (𝓝 (1:EReal)) := by
    have hh := (tendsto_log_boundary.const_div_atTop (Real.log C)).add_const 1
    simpa [Function.comp_def] using continuous_coe_real_ereal.continuousAt.tendsto.comp hh
  rw [← hc.limsup_eq]
  refine limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
  filter_upwards [eventually_radius] with r hr
  apply EReal.coe_le_coe
  have hd : 0 < 1-r := by linarith [hr.2]
  have hl : 0 < Real.log (1/(1-r)) := Real.log_pos ((one_lt_div hd).mpr (by linarith [hr.1]))
  have hb := koebe_mean_lower hr.1 hr.2
  have hid : 1/(4*Real.pi*(1-r)) = C*(1/(1-r)) := by dsimp [C]; field_simp
  rw [hid] at hb
  have hh := Real.log_le_log (mul_pos hC (by positivity)) hb
  rw [Real.log_mul hC.ne' (by positivity)] at hh
  rw [le_div_iff₀ hl,add_mul,div_mul_cancel₀ _ hl.ne',one_mul]
  exact hh

lemma inverse_spectrum_eq_one : spectrum (-2) = 1 := by
  apply le_antisymm
  · apply sSup_le
    rintro _ ⟨f,hf,rfl⟩
    exact beta_inverse_le_one hf
  · exact koebe_beta_ge_one.trans (le_sSup (show beta koebeMap (-2) ∈ {b | ∃ f,Schlicht f ∧ beta f (-2) = b} from
      ⟨koebeMap,koebeMap_schlicht,rfl⟩))

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.NegativeArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma polar_symm_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p = circlePoint p.1 p.2 := by
  simp [Complex.polarCoord_symm_apply,circlePoint,Complex.exp_mul_I,← Complex.ofReal_cos,← Complex.ofReal_sin]

lemma disk_lintegral_le_polar (F : ℂ → ℝ≥0∞) :
    (∫⁻ z in disk, F z) ≤ ∫⁻ r in Ioo (0:ℝ) 1,
      ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi, F (circlePoint r θ) := by
  have hm : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator hm,← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) ≤ _
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have he : (Ioi (0:ℝ) ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) =
      (Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (circlePoint p.1 p.2)) := by
    ext p
    simp_rw [polar_symm_circle]
    by_cases h0 : 0 < p.1
    · have hd : circlePoint p.1 p.2 ∈ disk ↔ p.1 < 1 := by
        simp [disk,circlePoint_norm,abs_of_pos h0]
      by_cases h1 : p.1 < 1 <;> by_cases hθ : p.2 ∈ Ioo (-Real.pi) Real.pi <;>
        simp [Set.indicator,h0,h1,hθ,hd]
    · simp [Set.indicator,h0]
  rw [he,lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  change (∫⁻ p in Ioo (0:ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (circlePoint p.1 p.2) ∂(volume.prod volume)) ≤ _
  rw [← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans_eq ?_
  apply lintegral_congr
  intro r
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

lemma integrableOn_disk_of_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioo (0:ℝ) 1))
    (hBn : ∀ r ∈ Ioo (0:ℝ) 1, 0 ≤ B r)
    (hbound : ∀ r ∈ Ioo (0:ℝ) 1,
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤ ENNReal.ofReal (B r)) :
    IntegrableOn F disk := by
  refine ⟨hF.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  have hn : ∀ᵐ z ∂(volume.restrict disk), 0 ≤ F z := ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hFn
  apply (hasFiniteIntegral_iff_ofReal hn).mpr
  refine lt_of_le_of_lt (disk_lintegral_le_polar (fun z => ENNReal.ofReal (F z))) ?_
  refine lt_of_le_of_lt ?_ hB.hasFiniteIntegral
  apply setLIntegral_mono' measurableSet_Ioo
  intro r hr
  calc
    ENNReal.ofReal r * (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal r * ENNReal.ofReal (B r) := mul_le_mul le_rfl (hbound r hr) zero_le zero_le
    _ ≤ ENNReal.ofReal (B r) := by
      exact mul_le_of_le_one_left zero_le (by exact_mod_cast hr.2.le)
    _ = ‖B r‖ₑ := by rw [Real.enorm_eq_ofReal (hBn r hr)]

lemma circle_lintegral_eq {F : ℂ → ℝ} {r : ℝ}
    (hc : Continuous (fun θ : ℝ => F (circlePoint r θ)))
    (hn : ∀ θ, 0 ≤ F (circlePoint r θ)) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) =
      ENNReal.ofReal (∫ θ in -Real.pi..Real.pi, F (circlePoint r θ)) := by
  rw [restrict_Ioo_eq_restrict_Ioc]
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall hn)).symm

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma continuousOn_deriv_univalent {f : ℂ → ℂ} (hf : UnivalentOn f disk) :
    ContinuousOn (deriv f) disk :=
  (hf.1.deriv Metric.isOpen_ball).continuousOn

lemma continuousOn_deriv_norm_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk) (t : ℝ) :
    ContinuousOn (fun z => ‖deriv f z‖^t) disk := by
  apply (continuousOn_deriv_univalent hf).norm.rpow_const
  intro z hz
  exact Or.inl (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf hz))

lemma integrableOn_boundary_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => (1-r)^a) (Ioo (0:ℝ) 1) := by
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0:ℝ)) (b := (1:ℝ)) ha).comp_sub_left 1
  have hi' : IntervalIntegrable (fun r : ℝ => (1-r)^a) volume 0 1 := by
    simpa using hi.symm
  exact hi'.1.mono_set Ioo_subset_Ioc_self

lemma integrableOn_disk_of_power_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {C a : ℝ} (hC : 0 ≤ C) (ha : -1 < a)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal (C*(1-r)^a)) :
    IntegrableOn F disk :=
  integrableOn_disk_of_circle_bound hF hFn ((integrableOn_boundary_rpow ha).const_mul C)
    (fun r hr => mul_nonneg hC (Real.rpow_nonneg (by linarith [hr.2]) _))
    (fun r hr => hbound r hr.1 hr.2)

lemma integrableOn_disk_boundary_power {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun z : ℂ => (1-‖z‖)^a) disk := by
  have hc : ContinuousOn (fun z : ℂ => (1-‖z‖)^a) disk := by
    apply (continuous_const.sub continuous_norm).continuousOn.rpow_const
    intro z hz
    exact Or.inl (ne_of_gt (by simpa [disk] using sub_pos.mpr (show ‖z‖ < 1 by simpa [disk] using hz)))
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (by simpa [disk] using hz))) _) (C := 2*Real.pi)
    (by positivity) ha
  intro r hr hr1
  have he : (fun θ : ℝ => (1-‖circlePoint r θ‖)^a) = fun _ => (1-r)^a := by
    ext θ
    rw [circlePoint_norm,abs_of_pos hr]
  rw [circle_lintegral_eq (F := fun z => (1-‖z‖)^a) (r := r) (by rw [he]; exact continuous_const) (fun θ => Real.rpow_nonneg (by rw [circlePoint_norm,abs_of_pos hr]; linarith) _)]
  rw [he,intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  rw [show Real.pi + Real.pi = 2*Real.pi by ring]

lemma integrableOn_geometric_product {A B F : ℂ → ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (hA : IntegrableOn A s) (hB : IntegrableOn B s) (hF : AEStronglyMeasurable F (volume.restrict s))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (hEq : ∀ z ∈ s, F z = A z^q * B z^(1-q)) : IntegrableOn F s := by
  apply ((hA.const_mul q).add (hB.const_mul (1-q))).mono' hF
  apply ae_restrict_of_forall_mem hs
  intro z hz
  rw [hEq z hz,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (hAn z hz) _) (Real.rpow_nonneg (hBn z hz) _))]
  exact Real.geom_mean_le_arith_mean2_weighted hq (by linarith) (hAn z hz) (hBn z hz) (by ring)

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_inverse_bound_small {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ}
    (hz : ‖z‖ ≤ 1/2) : ‖deriv f z‖^(-2:ℝ) ≤ 256 := by
  have hm : z ∈ disk := by simp only [disk,Metric.mem_ball,dist_zero_right]; linarith
  have hb := (schlicht_deriv_bounds hf hm).1
  have hp : (1+‖z‖)^3 ≤ (2:ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hl : (1/16:ℝ) ≤ (1-‖z‖)/(1+‖z‖)^3 := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  have he := Real.rpow_le_rpow_of_nonpos (by norm_num : (0:ℝ) < 1/16) (hl.trans hb) (by norm_num : (-2:ℝ) ≤ 0)
  norm_num at he
  simpa only [Real.rpow_neg (norm_nonneg _), Real.rpow_ofNat] using he

lemma inverse_square_bound_all (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Schlicht f → ∀ r : ℝ, 0 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C*(1-r)^(-1-ε) := by
  obtain ⟨C,hC,hbound⟩ := uniform_inverse_square_bound ε hε
  refine ⟨C+256,by linarith,fun f hf r hr hr1 => ?_⟩
  have hd : 0 < 1-r := by linarith
  have hp : 1 ≤ (1-r)^(-1-ε) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd (by linarith) (by linarith)
  by_cases hrh : 1/2 ≤ r
  · exact (hbound f hf r hrh hr1).trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hd.le _))
  · have hn (θ : ℝ) : ‖deriv f (circlePoint r θ)‖^(-2:ℝ) ≤ 256 :=
      schlicht_inverse_bound_small hf (by rw [circlePoint_norm,abs_of_nonneg hr]; linarith)
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (f := fun θ => ‖deriv f (circlePoint r θ)‖^(-2:ℝ))
      (g := fun _ => (256:ℝ)) (by linarith [Real.pi_pos])
      ((continuous_circle_deriv_rpow hf.1 hr hr1 (-2)).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hn θ)
    have hm : integralMean f (-2) r ≤ 256 := by
      change (2*Real.pi)⁻¹*(∫ θ in -Real.pi..Real.pi,‖deriv f (circlePoint r θ)‖^(-2:ℝ)) ≤ _
      have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (by positivity : (0:ℝ) ≤ 2*Real.pi))
      refine hh.trans_eq ?_
      simp only [intervalIntegral.integral_const,smul_eq_mul]
      field_simp
      ring
    nlinarith

lemma weighted_inverse_integrable {f : ℂ → ℂ} (hf : Schlicht f) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) disk := by
  obtain ⟨C,hC,hbound⟩ := inverse_square_bound_all (α/2) (by linarith)
  have hδ (z : ℂ) (hz : z ∈ disk) : 0 < 1-‖z‖ := by
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    linarith
  have hc : ContinuousOn (fun z : ℂ => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) disk :=
    ((continuous_const.sub continuous_norm).continuousOn.rpow_const (fun z hz => Or.inl (hδ z hz).ne')).mul
      (continuousOn_deriv_norm_rpow hf.1 _)
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => mul_nonneg (Real.rpow_nonneg (hδ z hz).le _) (Real.rpow_nonneg (norm_nonneg _) _))
    (C := 2*Real.pi*C) (a := α/2-1) (by positivity) (by linarith)
  intro r hr hr1
  have hd : 0 < 1-r := by linarith
  have he : (fun θ => (1-‖circlePoint r θ‖)^α*‖deriv f (circlePoint r θ)‖^(-2:ℝ)) =
      fun θ => (1-r)^α*‖deriv f (circlePoint r θ)‖^(-2:ℝ) := by
    ext θ
    rw [circlePoint_norm,abs_of_pos hr]
  rw [circle_lintegral_eq (F := fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)) (r := r) (by rw [he]; exact continuous_const.mul (continuous_circle_deriv_rpow hf.1 hr.le hr1 _))
    (fun θ => by rw [circlePoint_norm,abs_of_pos hr]; positivity),he,intervalIntegral.integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have hmean : (∫ θ in -Real.pi..Real.pi,‖deriv f (circlePoint r θ)‖^(-2:ℝ)) =
      2*Real.pi*integralMean f (-2) r := by
    unfold integralMean circlePoint
    field_simp
    simp only [mul_comm Complex.I]
  rw [hmean]
  calc
    _ ≤ (1-r)^α*(2*Real.pi*(C*(1-r)^(-1-α/2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbound f hf r hr.le hr1) (by positivity)) (by positivity)
    _ = 2*Real.pi*C*(1-r)^(α/2-1) := by
      have hp : (1-r)^α*(1-r)^(-1-α/2) = (1-r)^(α/2-1) := by
        rw [← Real.rpow_add hd]
        congr 1
        ring
      calc
        _ = (2*Real.pi*C)*((1-r)^α*(1-r)^(-1-α/2)) := by ring
        _ = _ := by rw [hp]

lemma schlicht_negative_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : -2 < t) (ht0 : t < 0) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  let q : ℝ := -t/2
  let α : ℝ := (1-q)/(2*q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hα : 0 < α := div_pos (by linarith) (by positivity)
  let A : ℂ → ℝ := fun z => (1-‖z‖)^α*‖deriv f z‖^(-2:ℝ)
  let B : ℂ → ℝ := fun z => (1-‖z‖)^(-1/2:ℝ)
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (weighted_inverse_integrable hf hα)
    (integrableOn_disk_boundary_power (by norm_num))
    ((continuousOn_deriv_norm_rpow hf.1 t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z hz
    dsimp [A]
    apply mul_nonneg
    · apply Real.rpow_nonneg
      have hn : ‖z‖ < 1 := by simpa [disk] using hz
      linarith
    · exact Real.rpow_nonneg (norm_nonneg _) _
  · intro z hz
    apply Real.rpow_nonneg
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    linarith
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk] using hz
    have hd : 0 < 1-‖z‖ := by linarith
    dsimp [A,B]
    rw [Real.mul_rpow (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul hd.le,← Real.rpow_mul (norm_nonneg _),← Real.rpow_mul hd.le]
    have he : α*q+(-1/2)*(1-q) = 0 := by
      dsimp [α]
      field_simp
      ring
    have htq : (-2:ℝ)*q = t := by dsimp [q]; ring
    rw [htq]
    calc
      _ = ‖deriv f z‖^t*1 := by ring
      _ = ‖deriv f z‖^t*((1-‖z‖)^(α*q)*(1-‖z‖)^((-1/2)*(1-q))) := by rw [← Real.rpow_add hd,he,Real.rpow_zero]
      _ = _ := by ring

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.TraceBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma rectangle_trace_periodic {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R,ε) (R,Y), ContDiffAt ℝ 2 g p)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R,y) (1,0) = fderiv ℝ g (R,y) (1,0)) :
    (∫ p in Icc (-R,ε) (R,Y), (p.2-ε)*pairLaplacian g p) =
      (∫ x in -R..R, traceFluxY g ε (x,Y)) + ∫ x in -R..R, g (x,ε) := by
  have hf : ContinuousOn (traceFluxX g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).1.continuousAt).continuousWithinAt
  have hh : ContinuousOn (traceFluxY g ε) (Icc (-R,ε) (R,Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).2.continuousAt).continuousWithinAt
  have hint : IntegrableOn (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p)
      (Icc (-R,ε) (R,Y)) volume := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.2-ε)*pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub_const ε).mul (continuousAt_pairLaplacian (hg p hp))
    exact hc.continuousWithinAt
  have heq (p : ℝ × ℝ) (hp : p ∈ Icc (-R,ε) (R,Y)) := divergence_traceFlux (hg p hp) ε
  have hi : IntegrableOn (fun p => fderiv ℝ (traceFluxX g ε) p (1,0)+
      fderiv ℝ (traceFluxY g ε) p (0,1)) (Icc (-R,ε) (R,Y)) volume :=
    hint.congr (ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => (heq p hp).symm))
  have hb := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (traceFluxX g ε) (traceFluxY g ε) (fderiv ℝ (traceFluxX g ε))
    (fderiv ℝ (traceFluxY g ε)) (-R,ε) (R,Y) ⟨by linarith,hεY⟩ hf hh
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).1.differentiableAt (by norm_num)).hasFDerivAt)
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩) ε).2.differentiableAt (by norm_num)).hasFDerivAt) hi
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hb
  have hsideint : (∫ y in ε..Y, traceFluxX g ε (R,y)) =
      ∫ y in ε..Y, traceFluxX g ε (-R,y) := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [traceFluxX]
    rw [hside y (by simpa only [uIcc_of_le hεY] using hy)]
  change _ = ((∫ x in -R..R, traceFluxY g ε (x,Y)) - ∫ x in -R..R, traceFluxY g ε (x,ε)) +
    (∫ y in ε..Y, traceFluxX g ε (R,y)) - ∫ y in ε..Y, traceFluxX g ε (-R,y) at hb
  rw [hsideint] at hb
  simpa only [traceFluxY,sub_self,zero_mul,zero_sub,
    intervalIntegral.integral_neg,sub_neg_eq_add, zero_add,add_zero,sub_zero,add_sub_cancel_right] using hb

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma rectangle_restrict_open (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Icc (a,c) (b,d)) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) := by
  rw [Icc_prod_eq]
  change (volume.prod volume).restrict (Icc a b ×ˢ Icc c d) =
    (volume.prod volume).restrict (Ioo a b ×ˢ Ioo c d)
  rw [← Measure.prod_restrict,← Measure.prod_restrict,
    restrict_Ioo_eq_restrict_Icc,restrict_Ioo_eq_restrict_Icc]

lemma rectangle_conformal_lintegral_le {F : ℂ → ℂ} {R ε Y : ℝ} (hε : 0 < ε)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    (hi : InjOn F {z : ℂ | -R < z.re ∧ z.re < R ∧ 0 < z.im}) (b : ℂ → ℝ≥0∞) :
    (∫⁻ p in Icc (-R,ε) (R,Y),
      ENNReal.ofReal (‖deriv F (Complex.equivRealProdCLM.symm p)‖^2)*
        b (F (Complex.equivRealProdCLM.symm p))) ≤ ∫⁻ w, b w := by
  rw [rectangle_restrict_open]
  let s : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo ε Y
  let E := Complex.equivRealProdCLM
  have hs : MeasurableSet (E ⁻¹' s) :=
    (measurableSet_Ioo.prod measurableSet_Ioo).preimage E.continuous.measurable
  have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) s
  have hh : (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) =
      ∫⁻ z in E ⁻¹' s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
    rw [← he]
    apply lintegral_congr
    intro z
    change ENNReal.ofReal (‖deriv F (E.symm (E z))‖^2)*b (F (E.symm (E z))) = _
    rw [E.symm_apply_apply]
  change (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2)*b (F (E.symm p))) ≤ _
  rw [hh]
  apply conformal_lintegral_le hs
  · intro z hz
    exact hF z (hε.trans hz.2.1)
  · apply hi.mono
    intro z hz
    exact ⟨hz.1.1,hz.1.2,hε.trans hz.2.1⟩

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma periodic_conformal_trace_bounded {F : ℂ → ℂ} {ψ b : ℂ → ℝ} {K : ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi ∧ 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hb : Integrable b) (hbn : ∀ w, 0 ≤ b w) (hK : 0 ≤ K)
    (hside : ∀ y : ℝ, 0 < y →
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (-Real.pi,y) (1,0) =
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (Real.pi,y) (1,0))
    (hlap : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 ≤ Laplacian.laplacian (ψ ∘ F) z ∧
      z.im * Laplacian.laplacian (ψ ∘ F) z ≤ K*‖deriv F z‖^2*b (F z)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ x in -Real.pi..Real.pi, ψ (F (x+ε*Complex.I))) ≤ C := by
  let E := Complex.equivRealProdCLM.symm
  let g := (ψ ∘ F) ∘ E
  have hg (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p :=
    (hψ.contDiffAt.comp _ ((hF (E p) hp).contDiffAt.restrict_scalars ℝ)).comp _ E.contDiff.contDiffAt
  have hc (x : ℝ) : ContinuousAt (fun x : ℝ => g (x,1)) x := by
    exact (hg (x,1) zero_lt_one).continuousAt.comp (f := fun v : ℝ => (v,(1:ℝ))) (show ContinuousAt (fun v : ℝ => (v,(1:ℝ))) x from (continuous_id.prodMk continuous_const).continuousAt)
  have hd (x : ℝ) : ContinuousAt (fun x : ℝ => fderiv ℝ g (x,1) (0,1)) x := by
    have hh := ((hg (x,1) zero_lt_one).fderiv_right (m := 0) (by norm_num)).continuousAt
    have hl : ContinuousAt (fun x : ℝ => fderiv ℝ g (x,1)) x :=
      hh.comp (f := fun v : ℝ => (v,(1:ℝ))) (show ContinuousAt (fun v : ℝ => (v,(1:ℝ))) x from (continuous_id.prodMk continuous_const).continuousAt)
    exact hl.clm_apply continuousAt_const
  let A : ℝ := ∫ x in -Real.pi..Real.pi, |g (x,1)|+|fderiv ℝ g (x,1) (0,1)|
  have hAint : IntervalIntegrable (fun x : ℝ => |g (x,1)|+|fderiv ℝ g (x,1) (0,1)|)
      volume (-Real.pi) Real.pi :=
    ((continuous_iff_continuousAt.mpr hc).abs.add (continuous_iff_continuousAt.mpr hd).abs).intervalIntegrable _ _
  have hIb : 0 ≤ ∫ w, b w := integral_nonneg hbn
  refine ⟨K*(∫ w, b w)+A,fun ε hε hε1 => ?_⟩
  let S := Icc (-Real.pi,ε) (Real.pi,(1:ℝ))
  let U : ℝ × ℝ → ℝ := fun p => (p.2-ε)*pairLaplacian g p
  have hbox (p : ℝ × ℝ) (hp : p ∈ S) : ContDiffAt ℝ 2 g p := hg p (hε.trans_le hp.1.2)
  have hUi : IntegrableOn U S := by
    apply ContinuousOn.integrableOn_compact isCompact_Icc
    intro p hp
    apply ContinuousAt.continuousWithinAt
    exact (continuous_snd.continuousAt.sub_const ε).mul
      (continuousAt_pairLaplacian (hbox p hp))
  have hUn (p : ℝ × ℝ) (hp : p ∈ S) : 0 ≤ U p := by
    dsimp [U,g,E]
    rw [pairLaplacian_complex]
    exact mul_nonneg (by linarith [hp.1.2]) (hlap _ (hε.trans_le hp.1.2) hp.2.2).1
  have hUp (p : ℝ × ℝ) (hp : p ∈ S) :
      U p ≤ K*‖deriv F (E p)‖^2*b (F (E p)) := by
    have hx := hlap (E p) (hε.trans_le hp.1.2) hp.2.2
    dsimp only [U,g]
    rw [pairLaplacian_complex]
    calc
      _ ≤ p.2*Laplacian.laplacian (ψ ∘ F) (E p) := mul_le_mul_of_nonneg_right (by linarith) hx.1
      _ ≤ _ := hx.2
  have hIle : (∫ p in S, U p) ≤ K*(∫ w, b w) := by
    have he := ofReal_integral_eq_lintegral_ofReal hUi
      (ae_restrict_of_forall_mem measurableSet_Icc hUn)
    have hb' := ofReal_integral_eq_lintegral_ofReal hb (Eventually.of_forall hbn)
    have hL : (∫⁻ p in S, ENNReal.ofReal (U p)) ≤ ENNReal.ofReal (K*(∫ w, b w)) := by
      calc
        _ ≤ ∫⁻ p in S, ENNReal.ofReal K *
            (ENNReal.ofReal (‖deriv F (E p)‖^2)*ENNReal.ofReal (b (F (E p)))) := by
          apply setLIntegral_mono' measurableSet_Icc
          intro p hp
          rw [← ENNReal.ofReal_mul (sq_nonneg _),← ENNReal.ofReal_mul hK]
          apply ENNReal.ofReal_le_ofReal
          simpa only [mul_assoc] using hUp p hp
        _ = ENNReal.ofReal K * ∫⁻ p in S,
            ENNReal.ofReal (‖deriv F (E p)‖^2)*ENNReal.ofReal (b (F (E p))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
        _ ≤ ENNReal.ofReal K * ∫⁻ w, ENNReal.ofReal (b w) :=
          mul_le_mul le_rfl (rectangle_conformal_lintegral_le hε
            (fun z hz => (hF z hz).differentiableAt) hi
            (fun w => ENNReal.ofReal (b w))) zero_le zero_le
        _ = ENNReal.ofReal (K*(∫ w, b w)) := by rw [← hb',ENNReal.ofReal_mul hK]
    rw [← he] at hL
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK hIb)).mp hL
  have ht := rectangle_trace_periodic Real.pi_pos.le hε1 hbox
    (fun y hy => hside y (hε.trans_le hy.1))
  have htop : -(∫ x in -Real.pi..Real.pi, traceFluxY g ε (x,1)) ≤ A := by
    rw [← intervalIntegral.integral_neg]
    have htopc : Continuous (fun x : ℝ => -traceFluxY g ε (x,1)) := by
      simp only [traceFluxY]
      exact ((continuous_const.mul (continuous_iff_continuousAt.mpr hd)).sub
        (continuous_iff_continuousAt.mpr hc)).neg
    apply intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (htopc.intervalIntegrable _ _) hAint
    intro x _hx
    dsimp [traceFluxY]
    have hgabs := le_abs_self (g (x,1))
    have hdabs := neg_le_abs (fderiv ℝ g (x,1) (0,1))
    have hmul : -(1-ε)*fderiv ℝ g (x,1) (0,1) ≤ |fderiv ℝ g (x,1) (0,1)| := by
      calc
        _ = (1-ε)*(-fderiv ℝ g (x,1) (0,1)) := by ring
        _ ≤ (1-ε)*|fderiv ℝ g (x,1) (0,1)| := mul_le_mul_of_nonneg_left hdabs (by linarith)
        _ ≤ |fderiv ℝ g (x,1) (0,1)| := mul_le_of_le_one_left (abs_nonneg _) (by linarith)
    linarith
  have hid : (∫ x in -Real.pi..Real.pi, ψ (F (x+ε*Complex.I))) =
      ∫ x in -Real.pi..Real.pi, g (x,ε) := by
    apply intervalIntegral.integral_congr
    intro x _
    simp only [g,E,Function.comp_apply,Complex.equivRealProdCLM_symm_apply]
  rw [hid]
  change (∫ p in S, U p) = _ at ht
  linarith

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology
namespace Brennan

lemma schlicht_growth_upper {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    ‖f z‖ ≤ ‖z‖/(1-‖z‖)^2 :=
  OAI.Brennan.univalent_growth_upper hf.1.1 hf.1.2 hf.2.1 hf.2.2
    (by simpa [disk, Metric.mem_ball, dist_zero_right] using hz)

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.SmoothMeans
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma logDisk_norm (z : ℂ) : ‖logDisk z‖ = Real.exp (-z.im) := by
  simp [logDisk,Complex.norm_exp]

lemma logDisk_mem_disk {z : ℂ} (hz : 0 < z.im) : logDisk z ∈ disk := by
  simp only [disk,Metric.mem_ball,dist_zero_right,logDisk_norm]
  exact Real.exp_lt_one_iff.mpr (by linarith)

lemma logDisk_analytic (z : ℂ) : AnalyticAt ℂ logDisk z := by
  exact (analyticAt_cexp).comp ((analyticAt_id.mul analyticAt_const))

lemma logDisk_injOn : InjOn logDisk {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi} := by
  intro z hz w hw h
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hz.1 : -Real.pi < (z*Complex.I).im)
    (by simpa using hz.2.le : (z*Complex.I).im ≤ Real.pi)
    (by simpa using hw.1 : -Real.pi < (w*Complex.I).im)
    (by simpa using hw.2.le : (w*Complex.I).im ≤ Real.pi) h
  exact mul_right_cancel₀ Complex.I_ne_zero he

lemma logDisk_realProd (x y : ℝ) :
    logDisk (Complex.equivRealProdCLM.symm (x,y)) = circlePoint (Real.exp (-y)) x := by
  rw [logDisk,Complex.equivRealProdCLM_symm_apply]
  have he : ((x:ℂ)+y*Complex.I)*Complex.I = (-y:ℂ)+(x:ℂ)*Complex.I := by rw [add_mul,mul_assoc,Complex.I_mul_I]; ring
  rw [he,Complex.exp_add,← Complex.ofReal_neg,← Complex.ofReal_exp]
  rfl

lemma logDisk_periodic (z : ℂ) : logDisk (z+2*Real.pi) = logDisk z := by
  simp only [logDisk,add_mul,Complex.exp_add,Complex.exp_two_pi_mul_I,mul_one]

lemma logStrip_smooth_periodic_side (H : ℂ → ℝ) (y : ℝ) :
    fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (-Real.pi,y) (1,0) =
      fderiv ℝ ((H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (Real.pi,y) (1,0) := by
  let g := (H ∘ logDisk) ∘ Complex.equivRealProdCLM.symm
  have he : (fun p : ℝ × ℝ => g (p+(2*Real.pi,0))) = g := by
    ext p
    dsimp [g]
    have hz : Complex.equivRealProdCLM.symm ((p.1,p.2)+(2*Real.pi,0)) =
        Complex.equivRealProdCLM.symm p+2*Real.pi := by
      simp [Complex.equivRealProdCLM_symm_apply]
      ring
    rw [hz,logDisk_periodic]
  have hd := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1,0))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (-Real.pi,y)) (2*Real.pi,0))
  rw [he] at hd
  have hp : (-Real.pi,y)+(2*Real.pi,0) = (Real.pi,y) := by
    ext <;> dsimp <;> ring
  simpa only [hp] using hd

lemma exp_boundary_lower {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : y/2 ≤ 1-Real.exp (-y) := by
  have he := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  have hn : Real.exp (-y) = (Real.exp y)⁻¹ := Real.exp_neg y
  rw [hn]
  have hi : (Real.exp y)⁻¹ ≤ (1+y)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hden : 0 < 1+y := by linarith
  have hf : y/2 ≤ 1-(1+y)⁻¹ := by
    rw [inv_eq_one_div]
    have hh : 1/(1+y) ≤ 1-y/2 := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith
  linarith

lemma logStrip_height_bound {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ}
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im ≤ 3*(1+‖f (logDisk z)‖^2)^(-1/4:ℝ) := by
  let y := z.im
  let r := Real.exp (-y)
  have hy : 0 < y := hz
  have hyr : r < 1 := Real.exp_lt_one_iff.mpr (by dsimp [y]; linarith)
  have hr : 0 < r := Real.exp_pos _
  have hd : 0 < 1-r := by linarith
  have hg := schlicht_growth_upper hf (logDisk_mem_disk hz)
  rw [logDisk_norm] at hg
  change ‖f (logDisk z)‖ ≤ r/(1-r)^2 at hg
  have hb : ‖f (logDisk z)‖ ≤ 4/y^2 := by
    have hyb := exp_boundary_lower hy hz1
    change y/2 ≤ 1-r at hyb
    calc
      ‖f (logDisk z)‖ ≤ r/(1-r)^2 := hg
      _ ≤ 1/(y/2)^2 := div_le_div₀ (by norm_num) hyr.le (by positivity) (by nlinarith)
      _ = 4/y^2 := by field_simp; ring
  have hy4 : y^4 ≤ 1 := pow_le_one₀ hy.le hz1
  have hs : (1+‖f (logDisk z)‖^2)*y^4 ≤ 17 := by
    have hb' : ‖f (logDisk z)‖*y^2 ≤ 4 := (le_div_iff₀ (sq_pos_of_pos hy)).mp hb
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ ‖f (logDisk z)‖*y^2) hb' 2
    nlinarith [hsquare]
  have hbase : 0 < 1+‖f (logDisk z)‖^2 := by positivity
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1+‖f (logDisk z)‖^2)*y^4) hs (by norm_num : (0:ℝ) ≤ 1/4)
  rw [Real.mul_rpow (by positivity) (by positivity),← Real.rpow_natCast y 4,
    ← Real.rpow_mul hy.le] at hpow
  norm_num at hpow
  have h17 : (17:ℝ)^(1/4:ℝ) ≤ 3 := by
    calc
      (17:ℝ)^(1/4:ℝ) ≤ (81:ℝ)^(1/4:ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [show (81:ℝ) = 3^(4:ℝ) by norm_num,← Real.rpow_mul (by norm_num)]; norm_num
  have hmul : y*(1+‖f (logDisk z)‖^2)^(1/4:ℝ) ≤ 3 := by nlinarith
  have hpos := Real.rpow_pos_of_pos hbase (1/4:ℝ)
  rw [show (-1/4:ℝ) = -(1/4) by ring,Real.rpow_neg hbase.le,← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr hmul

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology
namespace Brennan

lemma bracketSq_eq (z : ℂ) : bracketSq z = 1+‖z‖^2 := by
  rw [Complex.sq_norm]
  simp [bracketSq,Complex.normSq_apply,pow_two,add_assoc]

lemma bracketSq_pos (z : ℂ) : 0 < bracketSq z := by rw [bracketSq_eq]; positivity

lemma bracketSq_contDiff (n : ℕ∞) : ContDiff ℝ n bracketSq := by
  exact (contDiff_const.add (Complex.reCLM.contDiff.pow 2)).add (Complex.imCLM.contDiff.pow 2)

lemma smoothPower_contDiff (q : ℝ) (n : ℕ∞) : ContDiff ℝ n (smoothPower q) :=
  (bracketSq_contDiff n).rpow_const_of_ne (fun z => (bracketSq_pos z).ne')

lemma bracketSq_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSq (bracketSqDeriv z) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).pow 2).const_add 1).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  convert! h using 1
  simp [bracketSqDeriv]

lemma smoothPower_hasFDerivAt (q : ℝ) (z : ℂ) :
    HasFDerivAt (smoothPower q) ((q*bracketSq z^(q-1)) • bracketSqDeriv z) z :=
  (bracketSq_hasFDerivAt z).rpow_const (Or.inl (bracketSq_pos z).ne')

lemma bracketSqDeriv_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSqDeriv
    ((ContinuousLinearMap.smulRight Complex.reCLM (2 • Complex.reCLM))+
      (ContinuousLinearMap.smulRight Complex.imCLM (2 • Complex.imCLM))) z := by
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.reCLM).add
    (((Complex.imCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.imCLM)
  convert! h using 1
  ext v w
  simp [ContinuousLinearMap.smulRight_apply,smul_eq_mul]
  ring

lemma smoothPower_secondReal (q : ℝ) (z u v : ℂ) :
    secondReal (smoothPower q) z u v =
      q*(q-1)*bracketSq z^(q-2)*(2*z.re*u.re+2*z.im*u.im)*(2*z.re*v.re+2*z.im*v.im)+
        q*bracketSq z^(q-1)*(2*u.re*v.re+2*u.im*v.im) := by
  have he : fderiv ℝ (smoothPower q) = fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z :=
    funext (fun z => (smoothPower_hasFDerivAt q z).fderiv)
  have hscalar := ((bracketSq_hasFDerivAt z).rpow_const (p := q-1) (Or.inl (bracketSq_pos z).ne')).const_mul q
  have hd := (hscalar.smul (bracketSqDeriv_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun z => (q*bracketSq z^(q-1)) • bracketSqDeriv z) z = _ at hd
  rw [secondReal,he,hd]
  simp [bracketSqDeriv,ContinuousLinearMap.smulRight_apply,smul_eq_mul,show q-1-1=q-2 by ring]
  ring

lemma laplacian_smoothPower (q : ℝ) (z : ℂ) :
    Laplacian.laplacian (smoothPower q) z =
      4*q*bracketSq z^(q-2)*(1+q*‖z‖^2) := by
  rw [laplacian_eq_secondReal,smoothPower_secondReal,smoothPower_secondReal]
  have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
    simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
  rw [he,Complex.sq_norm]
  simp [Complex.normSq_apply,bracketSq]
  ring

lemma laplacian_smoothPower_bounds {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : ℂ) :
    0 ≤ Laplacian.laplacian (smoothPower q) z ∧
      Laplacian.laplacian (smoothPower q) z ≤ 4*q*bracketSq z^(q-1) := by
  have hz := bracketSq_pos z
  rw [laplacian_smoothPower]
  constructor
  · positivity
  · have he : bracketSq z^(q-1) = bracketSq z^(q-2)*bracketSq z := by
      simpa only [show q-2+1=q-1 by ring,Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q-2) 1
    rw [he,← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [bracketSq_eq]
    nlinarith [sq_nonneg ‖z‖]

lemma bracketSq_decay_integrable {q : ℝ} (hq : q < 1/4) :
    Integrable (fun z : ℂ => bracketSq z^(q-5/4)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 5/2-2*q)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_smooth_trace {f : ℂ → ℂ} (hf : Schlicht f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1/4) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (∫ x in -Real.pi..Real.pi, smoothPower q (f (logDisk (x+y*Complex.I)))) ≤ C := by
  let F : ℂ → ℂ := f ∘ logDisk
  have hF (z : ℂ) (hz : 0 < z.im) : AnalyticAt ℂ F z :=
    ((hf.1.1.analyticOnNhd Metric.isOpen_ball _ (logDisk_mem_disk hz)).comp (logDisk_analytic z))
  apply periodic_conformal_trace_bounded (F := F) (ψ := smoothPower q)
    (b := fun w => bracketSq w^(q-5/4)) (K := 12*q) hF
  · intro z hz w hw he
    apply logDisk_injOn ⟨hz.1,hz.2.1⟩ ⟨hw.1,hw.2.1⟩
    exact hf.1.2 (logDisk_mem_disk hz.2.2) (logDisk_mem_disk hw.2.2) he
  · exact smoothPower_contDiff q 2
  · exact bracketSq_decay_integrable hq4
  · intro w
    exact Real.rpow_nonneg (bracketSq_pos w).le _
  · positivity
  · intro y _hy
    exact logStrip_smooth_periodic_side (smoothPower q ∘ f) y
  · intro z hz hz1
    rw [laplacian_holomorphic_comp (smoothPower_contDiff q 2).contDiffAt (hF z hz)]
    have hl := laplacian_smoothPower_bounds hq.le (by linarith) (F z)
    have hy := logStrip_height_bound hf hz hz1
    rw [← bracketSq_eq] at hy
    change z.im ≤ 3*bracketSq (F z)^(-1/4:ℝ) at hy
    constructor
    · exact mul_nonneg (sq_nonneg _) hl.1
    · calc
        _ ≤ (3*bracketSq (F z)^(-1/4:ℝ)) * (‖deriv F z‖^2*(4*q*bracketSq (F z)^(q-1))) :=
          mul_le_mul hy (mul_le_mul_of_nonneg_left hl.2 (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) hl.1) (mul_nonneg (by norm_num) (Real.rpow_nonneg (bracketSq_pos _).le _))
        _ = _ := by
          have he : bracketSq (F z)^(-1/4:ℝ)*bracketSq (F z)^(q-1) = bracketSq (F z)^(q-5/4) := by
            rw [← Real.rpow_add (bracketSq_pos _)]
            congr 1
            ring
          calc
            _ = (12*q*‖deriv F z‖^2)*(bracketSq (F z)^(-1/4:ℝ)*bracketSq (F z)^(q-1)) := by ring
            _ = _ := by rw [he]

lemma continuous_circle_smoothPower {f : ℂ → ℂ} (hf : Schlicht f) (q r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (fun θ => smoothPower q (f (circlePoint r θ))) := by
  apply (smoothPower_contDiff q 0).continuous.comp
  apply hf.1.1.continuousOn.comp_continuous (show Continuous (circlePoint r) from by unfold circlePoint; fun_prop)
  intro θ
  simpa only [disk,Metric.mem_ball,dist_zero_right,circlePoint_norm,abs_of_nonneg hr] using hr1

lemma schlicht_smooth_means {f : ℂ → ℂ} (hf : Schlicht f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1/4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 →
      (∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ))) ≤ C := by
  obtain ⟨C,hC⟩ := schlicht_smooth_trace hf hq hq4
  refine ⟨|C|+2*Real.pi*(5:ℝ)^q+1,by positivity,fun r hr hr1 => ?_⟩
  by_cases hrh : r ≤ 1/2
  · have hb (θ : ℝ) : smoothPower q (f (circlePoint r θ)) ≤ (5:ℝ)^q := by
      have hm : circlePoint r θ ∈ disk := by
        simpa [disk,circlePoint_norm,abs_of_pos hr] using hr1
      have hg := schlicht_growth_upper hf hm
      rw [circlePoint_norm,abs_of_pos hr] at hg
      have hv : ‖f (circlePoint r θ)‖ ≤ 2 := by
        have hd : 0 < (1-r)^2 := sq_pos_of_pos (by linarith)
        have hh : r/(1-r)^2 ≤ 2 := (div_le_iff₀ hd).mpr (by nlinarith)
        exact hg.trans hh
      apply Real.rpow_le_rpow (bracketSq_pos _).le _ hq.le
      rw [bracketSq_eq]
      nlinarith [norm_nonneg (f (circlePoint r θ))]
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      ((continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hb θ)
    simp only [intervalIntegral.integral_const,smul_eq_mul] at hi
    have hn := abs_nonneg C
    nlinarith
  · let y := -Real.log r
    have hy : 0 < y := neg_pos.mpr (Real.log_neg hr hr1)
    have hy1 : y ≤ 1 := by
      have hexp : Real.exp (-1) ≤ (1/2:ℝ) := by
        rw [Real.exp_neg]
        have he := Real.add_one_le_exp (1:ℝ)
        exact inv_le_comm₀ (Real.exp_pos _) (by norm_num) |>.mpr (by norm_num; linarith)
      have hlog : -1 ≤ Real.log r := (Real.le_log_iff_exp_le hr).mpr (hexp.trans (by linarith))
      dsimp [y]
      linarith
    have he (x : ℝ) : logDisk ((x:ℂ)+y*Complex.I) = circlePoint r x := by
      have hh := logDisk_realProd x y
      rw [Complex.equivRealProdCLM_symm_apply] at hh
      simpa only [y,neg_neg,Real.exp_log hr] using hh
    have hs := hC y hy hy1
    simp_rw [he] at hs
    have hc' := le_abs_self C
    have hn : 0 ≤ 2*Real.pi*(5:ℝ)^q := by positivity
    linarith

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.PositiveArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_bracketSq_growth {f : ℂ → ℂ} (hf : Schlicht f) {z : ℂ} (hz : z ∈ disk) :
    bracketSq (f z) ≤ 2*(1-‖z‖)^(-4:ℝ) := by
  have hr : ‖z‖ < 1 := by simpa [disk] using hz
  have hd : 0 < 1-‖z‖ := by linarith
  have hg := schlicht_growth_upper hf hz
  have hb : ‖f z‖ ≤ 1/(1-‖z‖)^2 := hg.trans (div_le_div_of_nonneg_right hr.le (sq_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hδ : (1-‖z‖)^4 ≤ 1 := pow_le_one₀ hd.le (by nlinarith [norm_nonneg z])
  rw [bracketSq_eq,Real.rpow_neg hd.le]
  norm_num only [Real.rpow_ofNat]
  rw [inv_eq_one_div]
  have hdiv : (1/(1-‖z‖)^2)^2 = 1/(1-‖z‖)^4 := by field_simp
  rw [hdiv] at hs
  have hh : 1 ≤ 1/(1-‖z‖)^4 := (le_div_iff₀ (pow_pos hd _)).mpr (by simpa using hδ)
  linarith

lemma continuousOn_smoothPower_comp {f : ℂ → ℂ} (hf : Schlicht f) (a : ℝ) :
    ContinuousOn (fun z => smoothPower a (f z)) disk :=
  (smoothPower_contDiff a 0).continuous.comp_continuousOn hf.1.1.continuousOn

lemma schlicht_function_area {f : ℂ → ℂ} (hf : Schlicht f) {a : ℝ} (ha : a < 1/2) :
    IntegrableOn (fun z => bracketSq (f z)^a) disk := by
  obtain ⟨q,hq0,hq4⟩ := exists_between (show max (0:ℝ) (a-1/4) < 1/4 by
    exact max_lt (by norm_num) (by linarith))
  have hq : 0 < q := (le_max_left _ _).trans_lt hq0
  have haq : a-q < 1/4 := by have hh := (le_max_right _ _).trans_lt hq0; linarith
  obtain ⟨C,hC,hmean⟩ := schlicht_smooth_means hf hq hq4
  have hc : ContinuousOn (fun z => bracketSq (f z)^a) disk := continuousOn_smoothPower_comp hf a
  have hm (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      IntervalIntegrable (fun θ => bracketSq (f (circlePoint r θ))^a) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf a r hr.le hr1).intervalIntegrable _ _
  have hqn (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
      IntervalIntegrable (fun θ => smoothPower q (f (circlePoint r θ))) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _
  by_cases haq0 : a ≤ q
  · apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := C) (a := 0) hC.le (by norm_num)
    intro r hr hr1
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z)^a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _),Real.rpow_zero,mul_one]
    apply ENNReal.ofReal_le_ofReal
    refine (intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]) (hm r hr hr1) (hqn r hr hr1) ?_).trans (hmean r hr hr1)
    intro θ _
    exact Real.rpow_le_rpow_of_exponent_le (by rw [bracketSq_eq]; nlinarith [sq_nonneg ‖f (circlePoint r θ)‖]) haq0
  · have haqp : 0 < a-q := by linarith
    apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := (2:ℝ)^(a-q)*C) (a := -4*(a-q)) (by positivity) (by linarith)
    intro r hr hr1
    have hd : 0 < 1-r := by linarith
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z)^a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _)]
    apply ENNReal.ofReal_le_ofReal
    have hi : (∫ θ in -Real.pi..Real.pi, bracketSq (f (circlePoint r θ))^a) ≤
        ∫ θ in -Real.pi..Real.pi, ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*smoothPower q (f (circlePoint r θ)) := by
      apply intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos]) (hm r hr hr1) ((hqn r hr hr1).const_mul _)
      intro θ _
      have hz : circlePoint r θ ∈ disk := by simpa [disk,circlePoint_norm,abs_of_pos hr] using hr1
      have hg := schlicht_bracketSq_growth hf hz
      rw [circlePoint_norm,abs_of_pos hr] at hg
      have hp := Real.rpow_le_rpow (bracketSq_pos _).le hg haqp.le
      rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _),← Real.rpow_mul hd.le] at hp
      calc
        _ = bracketSq (f (circlePoint r θ))^(a-q)*bracketSq (f (circlePoint r θ))^q := by
          rw [← Real.rpow_add (bracketSq_pos _),sub_add_cancel]
        _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (bracketSq_pos _).le _)
    rw [intervalIntegral.integral_const_mul] at hi
    calc
      _ ≤ ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*(∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ))) := hi
      _ ≤ ((2:ℝ)^(a-q)*(1-r)^(-4*(a-q)))*C := mul_le_mul_of_nonneg_left (hmean r hr hr1) (by positivity)
      _ = _ := by ring

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma bracketSq_negative_integrable {η : ℝ} (hη : 0 < η) :
    Integrable (fun z : ℂ => bracketSq z^(-1-η)) := by
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2+2*η)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring

lemma schlicht_weighted_derivative_integrable {f : ℂ → ℂ} (hf : Schlicht f) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk := by
  have hc : ContinuousOn (fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)) disk :=
    ((continuousOn_deriv_univalent hf.1).norm.pow 2).mul (continuousOn_smoothPower_comp hf _)
  have hn : ∀ z : ℂ, 0 ≤ ‖deriv f z‖^2*bracketSq (f z)^(-1-η) :=
    fun z => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  refine ⟨hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
  have hh := conformal_lintegral_le Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.1.2
    (fun w => ENNReal.ofReal (bracketSq w^(-1-η)))
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hh
  refine lt_of_le_of_lt hh ?_
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (bracketSq_pos z).le (-1-η)))).mp
      (bracketSq_negative_integrable hη).hasFiniteIntegral

lemma schlicht_positive_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : 0 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  let q := t/2
  let η := (1-3*q)/(4*q)
  let a := (1+η)*q/(1-q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq3 : q < 1/3 := by dsimp [q]; linarith
  have hq1 : q < 1 := by linarith
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have ha : a < 1/2 := by
    dsimp [a]
    apply (div_lt_iff₀ (by linarith : 0 < 1-q)).mpr
    have he : (1+η)*q = (1+q)/4 := by dsimp [η]; field_simp; ring
    rw [he]
    linarith
  let A : ℂ → ℝ := fun z => ‖deriv f z‖^2*bracketSq (f z)^(-1-η)
  let B : ℂ → ℝ := fun z => bracketSq (f z)^a
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (schlicht_weighted_derivative_integrable hf hη)
    (schlicht_function_area hf ha)
    ((continuousOn_deriv_norm_rpow hf.1 t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z _hz
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  · intro z _hz
    exact Real.rpow_nonneg (bracketSq_pos _).le _
  · intro z _hz
    dsimp [A,B]
    rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _),
      ← Real.rpow_natCast ‖deriv f z‖ 2,← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_mul (bracketSq_pos _).le,← Real.rpow_mul (bracketSq_pos _).le]
    have he : (-1-η)*q+a*(1-q) = 0 := by
      dsimp [a]
      rw [div_mul_cancel₀ _ (by linarith : 1-q ≠ 0)]
      ring
    have htq : (2:ℝ)*q = t := by dsimp [q]; ring
    norm_num only [Nat.cast_ofNat] at *
    rw [htq]
    calc
      _ = ‖deriv f z‖^t*1 := by ring
      _ = ‖deriv f z‖^t*(bracketSq (f z)^((-1-η)*q)*bracketSq (f z)^(a*(1-q))) := by
        rw [← Real.rpow_add (bracketSq_pos _),he,Real.rpow_zero]
      _ = _ := by ring

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.DomainArea
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma schlicht_area {f : ℂ → ℂ} (hf : Schlicht f) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  rcases lt_trichotomy t 0 with h | h | h
  · exact schlicht_negative_area hf ht h
  · subst t
    simp only [Real.rpow_zero]
    exact integrableOn_const (by
      apply ne_of_lt
      exact Metric.isBounded_ball.measure_lt_top)
  · exact schlicht_positive_area hf h ht2

lemma normalizeDisk_hasDeriv {f : ℂ → ℂ} (hf : UnivalentOn f disk) {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt (normalizeDisk f) (deriv f z/deriv f 0) z :=
  ((hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f 0)).div_const _

lemma normalizeDisk_schlicht {f : ℂ → ℂ} (hf : UnivalentOn f disk) : Schlicht (normalizeDisk f) := by
  have h0 : (0:ℂ) ∈ disk := by simp [disk]
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf h0
  refine ⟨⟨?_,?_⟩,?_,?_⟩
  · intro z hz
    exact (normalizeDisk_hasDeriv hf hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    have hh : f z-f 0 = f w-f 0 := (div_left_inj' hn).mp he
    exact hf.2 hz hw (sub_left_inj.mp hh)
  · simp [normalizeDisk]
  · rw [(normalizeDisk_hasDeriv hf h0).deriv,div_self hn]

lemma univalent_disk_area {f : ℂ → ℂ} (hf : UnivalentOn f disk) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2/3) : IntegrableOn (fun z => ‖deriv f z‖^t) disk := by
  have h0 : (0:ℂ) ∈ disk := by simp [disk]
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball hf h0
  have hg := schlicht_area (normalizeDisk_schlicht hf) ht ht2
  apply IntegrableOn.congr_fun (hg.const_mul (‖deriv f 0‖^t)) _ Metric.isOpen_ball.measurableSet
  intro z hz
  have he : deriv f z = deriv f 0 * deriv (normalizeDisk f) z := by
    rw [(normalizeDisk_hasDeriv hf hz).deriv]
    field_simp
  dsimp only
  rw [he,norm_mul,Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma univalent_inverse_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : UnivalentOn φ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (Function.invFunOn φ U) (deriv φ z)⁻¹ (φ z) := by
  have ha := hφ.1.analyticOnNhd hU z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse (univalent_deriv_ne_zero hU hφ hz) ?_).hasDerivAt
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hφ.2.leftInvOn_invFunOn hw

lemma bijOn_inverse_univalent {U V : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hb : BijOn φ U V) :
    UnivalentOn (Function.invFunOn φ U) V := by
  constructor
  · intro w hw
    obtain ⟨z,hz,rfl⟩ := hb.surjOn hw
    exact (univalent_inverse_hasDerivAt hU ⟨hφ,hb.injOn⟩ hz).differentiableAt.differentiableWithinAt
  · exact (Function.invFunOn_injOn_image φ U).mono hb.surjOn

lemma bijOn_inverse_image {U V : Set ℂ} {φ : ℂ → ℂ} (hb : BijOn φ U V) :
    Function.invFunOn φ U '' V = U := by
  rw [← hb.image_eq]
  exact hb.injOn.invFunOn_image (Subset.refl _)

lemma conformal_lintegral_eq {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, b w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2)*b (F z) := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b]
  apply setLIntegral_congr_fun hs
  intro z hz
  have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
  have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
  dsimp only
  have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := det_fderiv_complex (hF z hz)
  rw [hf,hd',abs_of_nonneg (sq_nonneg _)]

end Brennan

end

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

lemma conformal_domain_area {W : Set ℂ} (hW : IsOpen W) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ W) (hb : BijOn φ W disk) {s : ℝ}
    (hs : 4/3 < s) (hs4 : s < 4) : IntegrableOn (fun z => ‖deriv φ z‖^s) W := by
  let f := Function.invFunOn φ W
  have hf : UnivalentOn f disk := bijOn_inverse_univalent hW hφ hb
  have himage : f '' disk = W := bijOn_inverse_image hb
  have hfi : IntegrableOn (fun w => ‖deriv f w‖^(2-s)) disk := univalent_disk_area hf (by linarith) (by linarith)
  have hderiv (w : ℂ) (hw : w ∈ disk) : deriv φ (f w) = (deriv f w)⁻¹ := by
    have hz : f w ∈ W := hb.surjOn.mapsTo_invFunOn hw
    have hv : φ (f w) = w := hb.surjOn.rightInvOn_invFunOn hw
    have hd := (univalent_inverse_hasDerivAt hW ⟨hφ,hb.injOn⟩ hz).deriv
    change deriv f (φ (f w)) = (deriv φ (f w))⁻¹ at hd
    rw [hv] at hd
    rw [hd,inv_inv]
  have hc : ContinuousOn (fun z => ‖deriv φ z‖^s) W := by
    apply (hφ.deriv hW).continuousOn.norm.rpow_const
    intro z hz
    exact Or.inl (norm_ne_zero_iff.mpr (univalent_deriv_ne_zero hW ⟨hφ,hb.injOn⟩ hz))
  refine ⟨hc.aestronglyMeasurable hW.measurableSet,?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z : ℂ => Real.rpow_nonneg (norm_nonneg _) s))).mpr
  have he := conformal_lintegral_eq Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.2
    (fun z => ENNReal.ofReal (‖deriv φ z‖^s))
  change (∫⁻ z in f '' disk, ENNReal.ofReal (‖deriv φ z‖^s)) =
    ∫⁻ z in disk, ENNReal.ofReal (‖deriv f z‖^2)*ENNReal.ofReal (‖deriv φ (f z)‖^s) at he
  rw [himage] at he
  rw [he]
  have hp : (∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖^2)*ENNReal.ofReal (‖deriv φ (f w)‖^s)) =
      ∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖^(2-s)) := by
    apply setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
    intro w hw
    dsimp only
    rw [hderiv w hw,norm_inv,Real.inv_rpow (norm_nonneg _),← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    have hn : 0 < ‖deriv f w‖ := norm_pos_iff.mpr (univalent_deriv_ne_zero Metric.isOpen_ball hf hw)
    rw [← Real.rpow_natCast ‖deriv f w‖ 2,← Real.rpow_neg hn.le,← Real.rpow_add hn]
    rfl
  rw [hp]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun w : ℂ => Real.rpow_nonneg (norm_nonneg (deriv f w)) (2-s)))).mp hfi.hasFiniteIntegral

end Brennan

end

end OAI
end

section
-- module Solutions.OAIQW_Brennan.Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function
open scoped Topology ENNReal
namespace Brennan

theorem main_theorem_oai : MainStatement := by
  refine ⟨?_,inverse_spectrum_eq_one,?_,?_⟩
  · intro ε hε
    obtain ⟨C,_hC,hbound⟩ := uniform_inverse_square_bound ε hε
    exact ⟨C,hbound⟩
  · intro W hW _hconnected _hsimply _hboundary φ hφ hb s hs hs4
    exact conformal_domain_area hW hφ hb hs hs4
  · intro f hf t ht ht2
    exact univalent_disk_area hf ht ht2

end Brennan

end

end OAI
end

theorem solution : type_of% @OAI.Brennan.main_theorem_oai := @OAI.Brennan.main_theorem_oai
