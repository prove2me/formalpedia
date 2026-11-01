-- Prove2me | solution 1 for OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T05:43:29.850209+00:00
-- url     : https://prove2.me/submissions/b877ccd0-76b8-4127-ae19-15918c21d448

import Mathlib
import Definitions.Def_Q146C004
import Definitions.Def_Q146C005

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CollarExtension
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Smooth extension of the active filling coordinate

A real branch smooth on a collar can be retained on a smaller closed
collar and extended to be constant away from it. In a filling disk all
other branches are constant, so this is the only extension needed there.
-/

open Set Filter
open scoped Topology Manifold ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

/-- Multiplication by a smooth cutoff which vanishes near the complement
of `U` makes a branch smooth globally. No regularity of the branch is
required outside its original open domain. -/
theorem contDiff_collar_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set E} {f χ : E → ℝ} {n : ℕ∞} (hU : IsOpen U)
    (hf : ContDiffOn ℝ n f U) (hχ : ContDiff ℝ n χ)
    (hzero : ∀ᶠ x in 𝓝ˢ Uᶜ, χ x = 0) (c : ℝ) :
    ContDiff ℝ n (fun x => c + χ x * (f x - c)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ U
  · exact contDiffAt_const.add
      (hχ.contDiffAt.mul ((hf.contDiffAt (hU.mem_nhds hx)).sub contDiffAt_const))
  · have heq : (fun y => c + χ y * (f y - c)) =ᶠ[𝓝 x] (fun _ => c) := by
      filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq heq

/-- Retain an arbitrary smooth real branch near a closed collar inside
its domain, and make it constant off that domain. -/
theorem exists_smooth_collar_extension {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U A : Set E} (hU : IsOpen U) (hA : IsClosed A) (hAU : A ⊆ U)
    {f : E → ℝ} (hf : ContDiffOn ℝ ∞ f U) (c : ℝ) :
    ∃ F : E → ℝ, ContDiff ℝ ∞ F ∧ F =ᶠ[𝓝ˢ A] f ∧ ∀ x ∉ U, F x = c := by
  have hd : Disjoint Uᶜ A := Set.disjoint_left.mpr (fun x hx hxa => hx (hAU hxa))
  obtain ⟨χ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    (𝓘(ℝ, E)) hU.isClosed_compl hA hd (n := (⊤ : ℕ∞))
  have hχ : ContDiff ℝ ∞ (χ : E → ℝ) := contMDiff_iff_contDiff.mp χ.contMDiff
  refine ⟨fun x => c + χ x * (f x - c), contDiff_collar_cutoff hU hf hχ hzero c, ?_, ?_⟩
  · filter_upwards [hone] with x hx
    simp [hx]
  · intro x hx
    change c + χ x * (f x - c) = c
    rw [hzero.self_of_nhdsSet x hx]
    ring

end CircleDomainRigidity.FiniteTransfer

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarFormPullback
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual exterior derivative of a pulled-back smooth planar one-form.
This is a calculus identity used in the construction of Green's formula. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer


lemma pulledPlanarForm_contDiff {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (v : ℝ × ℝ) : ContDiff ℝ ∞ (pulledPlanarForm P Q F v) := by
  have hd := (hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    (contDiff_const (c := v))
  exact ((hP.comp hF).mul (Complex.reCLM.contDiff.comp hd)).add
    ((hQ.comp hF).mul (Complex.imCLM.contDiff.comp hd))

lemma pulledPlanarForm_fderiv {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (x v w : ℝ × ℝ) :
    (fderiv ℝ (pulledPlanarForm P Q F v) x) w =
      (fderiv ℝ P (F x)) ((fderiv ℝ F x) w) * ((fderiv ℝ F x) v).re +
      P (F x) * (((fderiv ℝ (fderiv ℝ F) x) w) v).re +
      ((fderiv ℝ Q (F x)) ((fderiv ℝ F x) w) * ((fderiv ℝ F x) v).im +
      Q (F x) * (((fderiv ℝ (fderiv ℝ F) x) w) v).im) := by
  have hFd : DifferentiableAt ℝ F x := hF.differentiable (by simp) x
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.contDiffAt.fderiv_right (m := 1) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).differentiableAt (by norm_num)
  have hv := hDF.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
  have hpr := (hP.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (F x)).hasFDerivAt.comp x hFd.hasFDerivAt
  have hqr := (hQ.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (F x)).hasFDerivAt.comp x hFd.hasFDerivAt
  have hre := Complex.reCLM.hasFDerivAt.comp x hv
  have him := Complex.imCLM.hasFDerivAt.comp x hv
  have hh := (hpr.mul hre).add (hqr.mul him)
  change HasFDerivAt (fun y => P (F y) * ((fderiv ℝ F y) v).re +
    Q (F y) * ((fderiv ℝ F y) v).im) _ x at hh
  change (fderiv ℝ (fun y => P (F y) * ((fderiv ℝ F y) v).re +
    Q (F y) * ((fderiv ℝ F y) v).im) x) w = _
  rw [hh.fderiv]
  simp only [_root_.add_apply,_root_.smul_apply,
    ContinuousLinearMap.comp_apply,_root_.zero_apply,Function.comp_apply,
    ContinuousLinearMap.flip_apply,map_zero,zero_add,
    Complex.reCLM_apply,Complex.imCLM_apply,smul_eq_mul]
  ring

lemma pulledPlanarForm_curl {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (x : ℝ × ℝ) :
    (fderiv ℝ (pulledPlanarForm P Q F (0,1)) x) (1,0) -
      (fderiv ℝ (pulledPlanarForm P Q F (1,0)) x) (0,1) =
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I)) := by
  rw [pulledPlanarForm_fderiv hP hQ hF,pulledPlanarForm_fderiv hP hQ hF]
  have hsym := (hF.contDiffAt (x := x)).isSymmSndFDerivAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (1,0) (0,1)
  rw [hsym]
  rw [complexCovector_apply (fderiv ℝ P (F x)) ((fderiv ℝ F x) (1,0)),
    complexCovector_apply (fderiv ℝ P (F x)) ((fderiv ℝ F x) (0,1)),
    complexCovector_apply (fderiv ℝ Q (F x)) ((fderiv ℝ F x) (1,0)),
    complexCovector_apply (fderiv ℝ Q (F x)) ((fderiv ℝ F x) (0,1))]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularCurveNormalStrip
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual normal-strip map of a regular smooth planar curve has
positive Jacobian at its central curve. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma curveNormalStrip_contDiff {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) :
    ContDiff ℝ ∞ (curveNormalStrip γ) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  exact (hγ.comp contDiff_fst).add
    (contDiff_snd.smul (contDiff_const.mul (hd.comp contDiff_fst)))

lemma curveNormalStrip_fderiv {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (t : ℝ) (v : ℝ × ℝ) :
    (fderiv ℝ (curveNormalStrip γ) (t,0)) v =
      v.1 • deriv γ t + v.2 • (Complex.I * deriv γ t) := by
  have hd : ContDiff ℝ ∞ (deriv γ) := (contDiff_infty_iff_deriv.mp hγ).2
  have hfst : HasFDerivAt (fun p : ℝ × ℝ => p.1) (ContinuousLinearMap.fst ℝ ℝ ℝ) (t,0) :=
    hasFDerivAt_fst
  have hγd : HasFDerivAt γ
      ((ContinuousLinearMap.id ℝ ℝ).smulRight (deriv γ t)) t :=
    (hγ.differentiable (by simp) t).hasDerivAt
  have h1 := hγd.comp (t,(0 : ℝ)) hfst
  have hN : DifferentiableAt ℝ (fun p : ℝ × ℝ => Complex.I * deriv γ p.1) (t,0) :=
    (contDiff_const.mul (hd.comp contDiff_fst)).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (t,0)
  have h2 := (hasFDerivAt_snd (𝕜 := ℝ) (p := (t,0))).smul hN.hasFDerivAt
  have h := h1.add h2
  change HasFDerivAt (curveNormalStrip γ) _ (t,0) at h
  rw [h.fderiv]
  simp

lemma curveNormalStrip_jacobian {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (t : ℝ) :
    ((fderiv ℝ (curveNormalStrip γ) (t,0)) (1,0)).re *
        ((fderiv ℝ (curveNormalStrip γ) (t,0)) (0,1)).im -
      ((fderiv ℝ (curveNormalStrip γ) (t,0)) (1,0)).im *
        ((fderiv ℝ (curveNormalStrip γ) (t,0)) (0,1)).re = ‖deriv γ t‖ ^ 2 := by
  simp only [curveNormalStrip_fderiv hγ,one_smul,zero_smul,add_zero,zero_add,
    Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,zero_sub]
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexTangentFrame
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The tangent and its quarter-turn form an invertible real planar frame. -/
open Function
noncomputable section
namespace CircleDomainRigidity

lemma complexTangentFrame_apply (k : ℂ) (v : ℝ × ℝ) :
    complexTangentFrame k v = v.1 • k + v.2 • (Complex.I * k) := rfl

lemma complexTangentFrame_eq_mul (k : ℂ) (v : ℝ × ℝ) :
    complexTangentFrame k v = Complex.equivRealProdCLM.symm v * k := by
  rw [complexTangentFrame_apply,Complex.equivRealProdCLM_symm_apply]
  simp only [Complex.real_smul]
  ring

lemma complexTangentFrame_bijective {k : ℂ} (hk : k ≠ 0) :
    Bijective (complexTangentFrame k) := by
  constructor
  · intro v w he
    rw [complexTangentFrame_eq_mul,complexTangentFrame_eq_mul] at he
    exact Complex.equivRealProdCLM.symm.injective (mul_right_cancel₀ hk he)
  · intro w
    refine ⟨Complex.equivRealProdCLM (w/k),?_⟩
    rw [complexTangentFrame_eq_mul,ContinuousLinearEquiv.symm_apply_apply,div_mul_cancel₀ _ hk]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularCurveNormalChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An actual smooth local normal chart around each regular curve point. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_regular_curve_normal_chart {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (t : ℝ) (ht : deriv γ t ≠ 0) :
    ∃ e : OpenPartialHomeomorph (ℝ × ℝ) ℂ,
      (t,0) ∈ e.source ∧ (∀ p, e p = curveNormalStrip γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (γ t) := by
  let L : (ℝ × ℝ) ≃L[ℝ] ℂ :=
    ContinuousLinearEquiv.ofBijective (complexTangentFrame (deriv γ t))
      (LinearMap.ker_eq_bot.mpr (complexTangentFrame_bijective ht).1)
      (LinearMap.range_eq_top.mpr (complexTangentFrame_bijective ht).2)
  have hc := curveNormalStrip_contDiff hγ
  have hdf : fderiv ℝ (curveNormalStrip γ) (t,0) = (L : (ℝ × ℝ) →L[ℝ] ℂ) := by
    apply ContinuousLinearMap.ext
    intro v
    exact curveNormalStrip_fderiv hγ t v
  have hd : HasFDerivAt (curveNormalStrip γ) (L : (ℝ × ℝ) →L[ℝ] ℂ) (t,0) := by
    rw [← hdf]
    exact (hc.differentiable (by simp) (t,0)).hasFDerivAt
  let e := hc.contDiffAt.toOpenPartialHomeomorph (curveNormalStrip γ) hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have he : ∀ p, e p = curveNormalStrip γ p := fun _ => rfl
  have hp : (t,0) ∈ e.source := hc.contDiffAt.mem_toOpenPartialHomeomorph_source hd (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  refine ⟨e,hp,he,hc,?_⟩
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  rw [← hval]
  apply e.contDiffAt_symm (e.map_source hp) (f₀' := L)
  · change HasFDerivAt (curveNormalStrip γ) _ (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hd
  · change ContDiffAt ℝ ∞ (curveNormalStrip γ) (e.symm (e (t,0)))
    rw [e.left_inv hp]
    exact hc.contDiffAt

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularJordanParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Regular Jordan circuits with either orientation. The absolute Stokes
estimate does not need a choice of orientation. -/

open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem RegularJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RegularCurveParameterIsolation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A small spatial neighborhood of a regular Jordan circuit sees only
one small parameter interval, modulo its period. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma RegularJordanParametrization.fract_value
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s : ℝ) :
    γ (Int.fract s) = γ s := by
  simpa only [Int.fract,mul_one] using hγ.periodic.sub_int_mul_eq (x := s) ⌊s⌋

lemma RegularJordanParametrization.eq_iff_fract
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s t : ℝ) :
    γ s = γ t ↔ Int.fract s = Int.fract t := by
  constructor
  · intro h
    exact hγ.injective ⟨Int.fract_nonneg s,Int.fract_lt_one s⟩
      ⟨Int.fract_nonneg t,Int.fract_lt_one t⟩
      ((hγ.fract_value s).trans (h.trans (hγ.fract_value t).symm))
  · intro h
    rw [← hγ.fract_value s,← hγ.fract_value t,h]

lemma RegularJordanParametrization.eq_of_eq_short
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    {s t : ℝ} (h : γ s = γ t) (hlo : -1 < s-t) (hhi : s-t < 1) : s = t := by
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp ((hγ.eq_iff_fract s t).mp h)
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (hn ▸ hlo)
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (hn ▸ hhi)
  have hn0 : n = 0 := by omega
  rw [hn0,Int.cast_zero] at hn
  exact sub_eq_zero.mp hn

lemma RegularJordanParametrization.centered_representative
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (s t : ℝ) :
    ∃ u ∈ Icc (t-1/2) (t+1/2), γ u = γ s := by
  let u := s - (⌊s-t+1/2⌋ : ℤ)
  have he : u = t + Int.fract (s-t+1/2) - 1/2 := by dsimp only [u,Int.fract] <;> ring
  refine ⟨u,?_,?_⟩
  · rw [he]
    exact ⟨by linarith [Int.fract_nonneg (s-t+1/2)],by linarith [Int.fract_lt_one (s-t+1/2)]⟩
  · simpa only [u,mul_one] using hγ.periodic.sub_int_mul_eq (x := s) ⌊s-t+1/2⌋

lemma RegularJordanParametrization.local_parameter_isolation
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (t : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε > 0, ∀ s : ℝ, dist (γ s) (γ t) < ε →
      ∃ u ∈ Ioo (t-δ) (t+δ), γ u = γ s := by
  let K := Icc (t-1/2) (t+1/2) \ Ioo (t-δ) (t+δ)
  have hK : IsCompact K := isCompact_Icc.diff isOpen_Ioo
  have him : IsClosed (γ '' K) := (hK.image hγ.smooth.continuous).isClosed
  have hnot : γ t ∉ γ '' K := by
    rintro ⟨s,hs,he⟩
    have hst : s = t := hγ.eq_of_eq_short he
      (by linarith [hs.1.1]) (by linarith [hs.1.2])
    exact hs.2 (hst ▸ ⟨by linarith,by linarith⟩)
  obtain ⟨ε,hε,hball⟩ := Metric.isOpen_iff.mp him.isOpen_compl (γ t) hnot
  refine ⟨ε,hε,?_⟩
  intro s hs
  obtain ⟨u,hu,he⟩ := hγ.centered_representative s t
  refine ⟨u,?_,he⟩
  by_contra hout
  exact hball hs ⟨u,⟨hu,hout⟩,he⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Reflection_RegularJordanBoundaryChart
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The local normal chart straightens the entire Jordan boundary, not
only the chosen parameter arc. Compact parameter isolation excludes other arcs. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_regular_jordan_boundary_chart
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (U : Set ℂ),
      (t,0) ∈ e.source ∧ (∀ p, e p = curveNormalStrip γ p) ∧
      ContDiff ℝ ∞ e ∧ ContDiffAt ℝ ∞ e.symm (γ t) ∧
      IsOpen U ∧ γ t ∈ U ∧ U ⊆ e.target ∧
      (∀ z ∈ U, z ∈ frontier (jordanInterior H) ↔ (e.symm z).2 = 0) := by
  obtain ⟨e,ht,he,hs,his⟩ := exists_regular_curve_normal_chart hγ.smooth t (hγ.regular t)
  have hopen : IsOpen {s : ℝ | (s,0) ∈ e.source} :=
    e.open_source.preimage (continuous_id.prodMk continuous_const)
  obtain ⟨δ,hδ,hδs⟩ := Metric.isOpen_iff.mp hopen t ht
  obtain ⟨ε,hε,hiso⟩ := hγ.local_parameter_isolation t hδ
  let U := ball (γ t) ε ∩ e.target
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  refine ⟨e,U,ht,he,hs,his,isOpen_ball.inter e.open_target,
    ⟨mem_ball_self hε,hval ▸ e.map_source ht⟩,inter_subset_right,?_⟩
  intro z hz
  constructor
  · intro hzf
    obtain ⟨s,_,hes⟩ := hγ.boundary.symm ▸ hzf
    have hdist : dist (γ s) (γ t) < ε := hes.symm ▸ hz.1
    obtain ⟨u,hu,hue⟩ := hiso s hdist
    have huS : (u,0) ∈ e.source := hδs (by
      rw [mem_ball,Real.dist_eq]
      exact abs_sub_lt_iff.mpr ⟨by linarith [hu.2],by linarith [hu.1]⟩)
    have hue' : e (u,0) = z := by simpa [he,curveNormalStrip] using hue.trans hes
    have hinv := e.left_inv huS
    rw [hue'] at hinv
    exact congrArg Prod.snd hinv
  · intro hz0
    have hinv := e.right_inv hz.2
    have hpair : e.symm z = ((e.symm z).1,0) := Prod.ext rfl hz0
    rw [hpair,he] at hinv
    have hzγ : γ (e.symm z).1 = z := by
      simpa only [curveNormalStrip,zero_smul,add_zero] using hinv
    rw [← hzγ]
    exact hγ.mem_frontier _

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanLocalSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Two connected local sides of a Jordan boundary lie on opposite
sides. The proof uses density and regular openness of the actual Jordan disk. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma connected_disjoint_jordan_boundary {S : Set ℂ} (hS : IsPreconnected S)
    (H : ℂ ≃ₜ ℂ) (hd : Disjoint S (frontier (jordanInterior H))) :
    S ⊆ jordanInterior H ∨ S ⊆ (closure (jordanInterior H))ᶜ := by
  apply hS.subset_or_subset (jordanInterior_isOpen H) isClosed_closure.isOpen_compl
  · exact Set.disjoint_left.mpr (fun z hz hz' => hz' (subset_closure hz))
  · intro z hz
    by_cases hzin : z ∈ jordanInterior H
    · exact Or.inl hzin
    · right
      intro hzc
      apply Set.disjoint_left.mp hd hz
      rw [frontier, (jordanInterior_isOpen H).interior_eq]
      exact ⟨hzc, hzin⟩

lemma jordan_local_sides (H : ℂ ≃ₜ ℂ) {N S T : Set ℂ} {x : ℂ}
    (hN : IsOpen N) (hxN : x ∈ N) (hx : x ∈ frontier (jordanInterior H))
    (hS : IsPreconnected S) (hT : IsPreconnected T)
    (hSf : Disjoint S (frontier (jordanInterior H)))
    (hTf : Disjoint T (frontier (jordanInterior H)))
    (hcover : N ⊆ closure (S ∪ T)) :
    (S ⊆ jordanInterior H ∧ T ⊆ (closure (jordanInterior H))ᶜ) ∨
      (T ⊆ jordanInterior H ∧ S ⊆ (closure (jordanInterior H))ᶜ) := by
  have hxin : x ∉ jordanInterior H := by
    intro hi
    exact hx.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hi)
  rcases connected_disjoint_jordan_boundary hS H hSf with hSi | hSo <;>
    rcases connected_disjoint_jordan_boundary hT H hTf with hTi | hTo
  · have hc : N ⊆ closure (jordanInterior H) :=
      hcover.trans (closure_mono (union_subset hSi hTi))
    have hi : x ∈ interior (closure (jordanInterior H)) :=
      mem_interior_iff_mem_nhds.mpr (Filter.mem_of_superset (hN.mem_nhds hxN) hc)
    rw [interior_closure_jordanInterior] at hi
    exact (hxin hi).elim
  · exact Or.inl ⟨hSi, hTo⟩
  · exact Or.inr ⟨hTi, hSo⟩
  · have hc : N ⊆ (jordanInterior H)ᶜ := by
      have hh := hcover.trans (closure_mono (union_subset hSo hTo))
      simpa only [closure_compl, interior_closure_jordanInterior] using hh
    obtain ⟨y, hyN, hyJ⟩ := mem_closure_iff.1 hx.1 N hN hxN
    exact (hc hyN hyJ).elim

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalChartJordanSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The two halves of a normal chart lie on the two different Jordan sides. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma normal_chart_jordan_sides (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (U : Set ℂ)
    (hstraight : ∀ z ∈ U, z ∈ frontier (jordanInterior H) ↔ (e.symm z).2 = 0)
    (t r : ℝ) (hr : 0 < r)
    (hbox : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ e.source)
    (hBU : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) ⊆ U)
    (ht : e (t,0) ∈ frontier (jordanInterior H)) :
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) ∨
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) := by
  let B := Ioo (t-r) (t+r) ×ˢ Ioo (-r) r
  let P := Ioo (t-r) (t+r) ×ˢ Ioo 0 r
  let M := Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0
  have hPB : P ⊆ B := fun q hq => ⟨hq.1,⟨by linarith [hq.2.1],hq.2.2⟩⟩
  have hMB : M ⊆ B := fun q hq => ⟨hq.1,⟨hq.2.1,by linarith [hq.2.2]⟩⟩
  have hN : IsOpen (e '' B) :=
    e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) hbox
  have hP : IsPreconnected (e '' P) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hPB.trans hbox))
  have hM : IsPreconnected (e '' M) :=
    (isPreconnected_Ioo.prod isPreconnected_Ioo).image e
      (e.continuousOn.mono (hMB.trans hbox))
  have hPf : Disjoint (e '' P) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q,hq,rfl⟩ hf
    have he := (hstraight (e q) (hBU ⟨q,hPB hq,rfl⟩)).mp hf
    rw [e.left_inv (hbox (hPB hq))] at he
    linarith [hq.2.1]
  have hMf : Disjoint (e '' M) (frontier (jordanInterior H)) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨q,hq,rfl⟩ hf
    have he := (hstraight (e q) (hBU ⟨q,hMB hq,rfl⟩)).mp hf
    rw [e.left_inv (hbox (hMB hq))] at he
    linarith [hq.2.2]
  have hcover : e '' B ⊆ closure ((e '' P) ∪ (e '' M)) := by
    rintro _ ⟨q,hq,rfl⟩
    have hc := e.continuousOn.continuousAt (e.open_source.mem_nhds (hbox hq))
    rcases le_total 0 q.2 with hpos | hneg
    · apply closure_mono subset_union_left
      apply mem_closure_image hc
      change q ∈ closure (Ioo (t-r) (t+r) ×ˢ Ioo 0 r)
      rw [closure_prod_eq,closure_Ioo (by linarith : t-r ≠ t+r),
        closure_Ioo (by linarith : (0 : ℝ) ≠ r)]
      exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,⟨hpos,hq.2.2.le⟩⟩
    · apply closure_mono subset_union_right
      apply mem_closure_image hc
      change q ∈ closure (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0)
      rw [closure_prod_eq,closure_Ioo (by linarith : t-r ≠ t+r),
        closure_Ioo (by linarith : -r ≠ (0 : ℝ))]
      exact ⟨⟨hq.1.1.le,hq.1.2.le⟩,⟨hq.2.1.le,hneg⟩⟩
  apply jordan_local_sides H hN _ ht hP hM hPf hMf hcover
  exact ⟨(t,0),⟨⟨by linarith,by linarith⟩,⟨by linarith,hr⟩⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexCoareaJacobian
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The scalar Jacobian identity in regular complex coordinates. -/
open Set Function
noncomputable section
namespace CircleDomainRigidity

lemma complex_real_det_columns (B : ℂ →L[ℝ] ℂ) :
    B.det = (B 1).re * (B Complex.I).im - (B Complex.I).re * (B 1).im := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ContinuousLinearMap.coe_coe, Matrix.cons_val_zero, Matrix.cons_val_one]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarMapChangeVariables
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Change of variables from real product parameters to the physical complex
plane, with the actual two-column Jacobian. -/
open Set Function MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma planarMapJacobian_det (A : (ℝ × ℝ) →L[ℝ] ℂ) :
    (A.comp (Complex.equivRealProdCLM : ℂ →L[ℝ] (ℝ × ℝ))).det =
      planarMapJacobian A := by
  rw [complex_real_det_columns]
  change (A (1,0)).re * (A (0,1)).im - (A (0,1)).re * (A (1,0)).im = _
  unfold planarMapJacobian
  ring

lemma integral_image_planarMap {S : Set (ℝ × ℝ)} (hS : MeasurableSet S)
    {F : (ℝ × ℝ) → ℂ} {A : (ℝ × ℝ) → ((ℝ × ℝ) →L[ℝ] ℂ)}
    (hF : ∀ p ∈ S, HasFDerivAt F (A p) p) (hi : InjOn F S) (q : ℂ → ℝ) :
    (∫ z in F '' S, q z) =
      ∫ p in S, |planarMapJacobian (A p)| * q (F p) := by
  let e := Complex.equivRealProdCLM
  let T : Set ℂ := e ⁻¹' S
  let G : ℂ → ℂ := F ∘ e
  have hT : MeasurableSet T := hS.preimage e.continuous.measurable
  have hG : ∀ z ∈ T, HasFDerivWithinAt G ((A (e z)).comp (e : ℂ →L[ℝ] (ℝ × ℝ))) T z := by
    intro z hz
    exact ((hF (e z) hz).comp z e.hasFDerivAt).hasFDerivWithinAt
  have hiG : InjOn G T := by
    intro x hx y hy h
    exact e.injective (hi hx hy h)
  have himage : G '' T = F '' S := by
    ext z
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact ⟨e x,hx,rfl⟩
    · rintro ⟨p,hp,rfl⟩
      exact ⟨e.symm p,by simpa [T] using hp,by simp [G]⟩
  have hc := integral_image_eq_integral_abs_det_fderiv_smul volume hT hG hiG q
  rw [himage] at hc
  dsimp only [e] at hc
  simp only [planarMapJacobian_det,smul_eq_mul] at hc
  have he := Complex.volume_preserving_equiv_real_prod.setIntegral_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p => |planarMapJacobian (A p)| * q (F p)) S
  exact hc.trans he

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularJordanNormalBox
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Compact normal-coordinate rectangles retain the full Jordan boundary
and have positive actual Jacobian throughout. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma continuous_planarMapJacobian {F : (ℝ × ℝ) → ℂ} (hF : ContDiff ℝ ∞ F) :
    Continuous (fun p => planarMapJacobian (fderiv ℝ F p)) := by
  have hd := hF.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have h1 := hd.clm_apply (continuous_const (y := (1,0)))
  have h2 := hd.clm_apply (continuous_const (y := (0,1)))
  exact ((Complex.continuous_re.comp h1).mul (Complex.continuous_im.comp h2)).sub
    ((Complex.continuous_im.comp h1).mul (Complex.continuous_re.comp h2))

lemma exists_regular_jordan_normal_box
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (r : ℝ), 0 < r ∧ r < 1/4 ∧
      (∀ p, e p = curveNormalStrip γ p) ∧ ContDiff ℝ ∞ e ∧
      Icc (t-r,-r) (t+r,r) ⊆ e.source ∧
      (∀ p ∈ Icc (t-r,-r) (t+r,r),
        e p ∈ frontier (jordanInterior H) ↔ p.2 = 0) ∧
      (∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p)) := by
  obtain ⟨e,U,ht,he,hs,_,hU,htU,_,hstraight⟩ :=
    exists_regular_jordan_boundary_chart hγ t
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  have hj : 0 < planarMapJacobian (fderiv ℝ e (t,0)) := by
    have hfe : (e : (ℝ × ℝ) → ℂ) = curveNormalStrip γ := funext he
    rw [hfe]
    change 0 < _
    rw [show planarMapJacobian (fderiv ℝ (curveNormalStrip γ) (t,0)) =
      ‖deriv γ t‖^2 from curveNormalStrip_jacobian hγ.smooth t]
    exact sq_pos_of_pos (norm_pos_iff.mpr (hγ.regular t))
  let V := (e.source ∩ e ⁻¹' U) ∩ {p | 0 < planarMapJacobian (fderiv ℝ e p)}
  have hV : IsOpen V := (e.open_source.inter (hU.preimage hs.continuous)).inter
    (isOpen_lt continuous_const (continuous_planarMapJacobian hs))
  have htV : (t,0) ∈ V := ⟨⟨ht,by simpa [hval] using htU⟩,hj⟩
  obtain ⟨δ,hδ,hδV⟩ := Metric.isOpen_iff.mp hV (t,0) htV
  let r : ℝ := min (δ/2) (1/8)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  have hrδ : r < δ := (min_le_left _ _).trans_lt (by linarith)
  have hsub : Icc (t-r,-r) (t+r,r) ⊆ V := by
    intro p hp
    apply hδV
    rw [mem_ball,Prod.dist_eq,max_lt_iff,Real.dist_eq,Real.dist_eq,sub_zero]
    have h1 : |p.1-t| ≤ r := abs_le.mpr ⟨by linarith [hp.1.1],by linarith [hp.2.1]⟩
    have h2 : |p.2| ≤ r := abs_le.mpr ⟨hp.1.2,hp.2.2⟩
    exact ⟨h1.trans_lt hrδ,h2.trans_lt hrδ⟩
  refine ⟨e,r,hr,(min_le_right _ _).trans_lt (by norm_num),he,hs,
    fun p hp => (hsub hp).1.1,?_,fun p hp => (hsub hp).2⟩
  intro p hp
  have h := hstraight (e p) (hsub hp).1.2
  rwa [e.left_inv (hsub hp).1.1] at h

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalBoxImage
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact interior halves and the outer boundary of a compact normal box. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma normal_box_boundary_not_image
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    {p : ℝ × ℝ} (hp : p ∈ Icc (t-r,-r) (t+r,r))
    (hedge : p.1 = t-r ∨ p.1 = t+r ∨ p.2 = -r ∨ p.2 = r) :
    e p ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) := by
  rintro ⟨q,hq,heq⟩
  have hqK : q ∈ Icc (t-r,-r) (t+r,r) :=
    ⟨⟨hq.1.1.le,hq.2.1.le⟩,⟨hq.1.2.le,hq.2.2.le⟩⟩
  have heqp : q = p := e.injOn (hK hqK) (hK hp) heq
  subst q
  rcases hedge with h | h | h | h
  · exact (ne_of_gt hq.1.1) h
  · exact (ne_of_lt hq.1.2) h
  · exact (ne_of_gt hq.2.1) h
  · exact (ne_of_lt hq.2.2) h

lemma normal_box_jordan_sides (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0) :
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) ∨
    (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) := by
  have hB : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ Icc (t-r,-r) (t+r,r) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  apply normal_chart_jordan_sides H e (e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    ?_ t r hr (hB.trans hK) (subset_refl _) ?_
  · rintro z ⟨p,hp,rfl⟩
    rw [e.left_inv (hK (hB hp))]
    exact hf p (hB hp)
  · exact (hf (t,0) ⟨⟨by linarith,by linarith⟩,⟨by linarith,hr.le⟩⟩).mpr rfl

lemma normal_box_upper_inter (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ) :
    jordanInterior H ∩ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) =
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) := by
  ext z
  constructor
  · rintro ⟨hz,⟨p,hpB,rfl⟩⟩
    have hpos : 0 < p.2 := by
      by_contra h
      rcases lt_or_eq_of_le (not_lt.mp h) with hneg | hzero
      · exact hn ⟨p,⟨hpB.1,⟨hpB.2.1,hneg⟩⟩,rfl⟩ (subset_closure hz)
      · have hfront := (hf p ⟨⟨hpB.1.1.le,hpB.2.1.le⟩,
            ⟨hpB.1.2.le,hpB.2.2.le⟩⟩).mpr hzero
        exact hfront.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hz)
    exact ⟨p,⟨hpB.1,⟨hpos,hpB.2.2⟩⟩,rfl⟩
  · rintro ⟨p,hpP,rfl⟩
    exact ⟨hp ⟨p,hpP,rfl⟩,p,⟨hpP.1,⟨by linarith [hpP.2.1,hpP.2.2],hpP.2.2⟩⟩,rfl⟩

lemma normal_box_lower_inter (H : ℂ ≃ₜ ℂ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ) :
    jordanInterior H ∩ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) =
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) := by
  ext z
  constructor
  · rintro ⟨hz,⟨p,hpB,rfl⟩⟩
    have hpos : p.2 < 0 := by
      by_contra h
      rcases lt_or_eq_of_le (not_lt.mp h) with hneg | hzero
      · exact hn ⟨p,⟨hpB.1,⟨hneg,hpB.2.2⟩⟩,rfl⟩ (subset_closure hz)
      · have hfront := (hf p ⟨⟨hpB.1.1.le,hpB.2.1.le⟩,
            ⟨hpB.1.2.le,hpB.2.2.le⟩⟩).mpr hzero.symm
        exact hfront.2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hz)
    exact ⟨p,⟨hpB.1,⟨hpB.2.1,hpos⟩⟩,rfl⟩
  · rintro ⟨p,hpP,rfl⟩
    exact ⟨hp ⟨p,hpP,rfl⟩,p,⟨hpP.1,⟨hpP.2.1,by linarith [hpP.2.1,hpP.2.2]⟩⟩,rfl⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PlanarRectangleGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green's formula for the pullback of an actual smooth planar form on a
parameter rectangle. The only input is the existing rectangular divergence theorem. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma integral_pulledPlanarForm_curl_rectangle
    {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hF : ContDiff ℝ ∞ F)
    (a b : ℝ × ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b,
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I))) =
      ((∫ s in a.1..b.1, pulledPlanarForm P Q F (1,0) (s,a.2)) +
        ∫ t in a.2..b.2, pulledPlanarForm P Q F (0,1) (b.1,t)) -
      (∫ s in a.1..b.1, pulledPlanarForm P Q F (1,0) (s,b.2)) -
        ∫ t in a.2..b.2, pulledPlanarForm P Q F (0,1) (a.1,t) := by
  let A := pulledPlanarForm P Q F (1,0)
  let B := pulledPlanarForm P Q F (0,1)
  have hA : ContDiff ℝ ∞ A := pulledPlanarForm_contDiff hP hQ hF _
  have hB : ContDiff ℝ ∞ B := pulledPlanarForm_contDiff hP hQ hF _
  have hder : Continuous (fun x => (fderiv ℝ B x) (1,0) + (fderiv ℝ (-A) x) (0,1)) :=
    ((hB.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const).add
      (((hA.neg).continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const)
  have hi : IntegrableOn (fun x => (fderiv ℝ B x) (1,0) +
      (fderiv ℝ (-A) x) (0,1)) (Icc a b) volume :=
    hder.continuousOn.integrableOn_compact isCompact_Icc
  have he := integral_divergence_prod_Icc_of_hasFDerivAt_of_le B (-A)
    (fderiv ℝ B) (fderiv ℝ (-A)) a b hab hB.continuous.continuousOn
    hA.neg.continuous.continuousOn
    (fun x _ => (hB.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) x).hasFDerivAt)
    (fun x _ => (hA.neg.differentiable (by simp) x).hasFDerivAt) hi
  have hcurl (x : ℝ × ℝ) :
      (fderiv ℝ B x) (1,0) + (fderiv ℝ (-A) x) (0,1) =
      ((((fderiv ℝ F x) (1,0)).re * ((fderiv ℝ F x) (0,1)).im -
        ((fderiv ℝ F x) (1,0)).im * ((fderiv ℝ F x) (0,1)).re) *
        ((fderiv ℝ Q (F x)) 1 - (fderiv ℝ P (F x)) Complex.I)) := by
    rw [fderiv_neg]
    change (fderiv ℝ B x) (1,0) - (fderiv ℝ A x) (0,1) = _
    exact pulledPlanarForm_curl hP hQ hF x
  simp_rw [hcurl] at he
  simp only [Pi.neg_apply,intervalIntegral.integral_neg] at he
  change _ = _ at he
  rw [he]
  ring

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalStripRectangleGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The rectangle identity on either side of a regular boundary arc.
Three sides vanish for forms localized inside the normal chart. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma normal_strip_base_form {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ)
    (P Q : ℂ → ℝ) (t : ℝ) :
    pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (t,0) =
      P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  simp only [pulledPlanarForm,curveNormalStrip_fderiv hγ,
    one_smul,zero_smul,add_zero,curveNormalStrip]

lemma pulledPlanarForm_eq_zero {P Q : ℂ → ℝ} {F : (ℝ × ℝ) → ℂ}
    {p v : ℝ × ℝ} (hP : P (F p) = 0) (hQ : Q (F p) = 0) :
    pulledPlanarForm P Q F v p = 0 := by
  simp only [pulledPlanarForm,hP,hQ,zero_mul,zero_add]

lemma normal_strip_upper_green {P Q : ℂ → ℝ} {γ : ℝ → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hγ : ContDiff ℝ ∞ γ)
    (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R)
    (hl : ∀ y ∈ uIcc 0 R, P (curveNormalStrip γ (a,y)) = 0 ∧
      Q (curveNormalStrip γ (a,y)) = 0)
    (hr : ∀ y ∈ uIcc 0 R, P (curveNormalStrip γ (b,y)) = 0 ∧
      Q (curveNormalStrip γ (b,y)) = 0)
    (ht : ∀ x ∈ uIcc a b, P (curveNormalStrip γ (x,R)) = 0 ∧
      Q (curveNormalStrip γ (x,R)) = 0) :
    (∫ p in Icc (a,0) (b,R), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
      ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
        (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) =
      ∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im := by
  have hh := integral_pulledPlanarForm_curl_rectangle hP hQ
    (curveNormalStrip_contDiff hγ) (a,0) (b,R) ⟨hab,hR⟩
  have hzright : (∫ y in 0..R,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (b,y)) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hr y hy).1 (hr y hy).2
      _ = 0 := by simp
  have hzleft : (∫ y in 0..R,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (a,y)) = 0 := by
    calc
      _ = ∫ _y in (0 : ℝ)..R, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hl y hy).1 (hl y hy).2
      _ = 0 := by simp
  have hztop : (∫ x in a..b,
      pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (x,R)) = 0 := by
    calc
      _ = ∫ _x in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact pulledPlanarForm_eq_zero (ht x hx).1 (ht x hx).2
      _ = 0 := by simp
  change (∫ p in Icc (a,0) (b,R), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
    ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
      (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) = _ at hh
  rw [hzright,hzleft,hztop,add_zero,sub_zero,sub_zero] at hh
  rw [hh]
  apply intervalIntegral.integral_congr
  intro t _
  exact normal_strip_base_form hγ P Q t

lemma normal_strip_lower_green {P Q : ℂ → ℝ} {γ : ℝ → ℂ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (hγ : ContDiff ℝ ∞ γ)
    (a b R : ℝ) (hab : a ≤ b) (hR : 0 ≤ R)
    (hl : ∀ y ∈ uIcc (-R) 0, P (curveNormalStrip γ (a,y)) = 0 ∧
      Q (curveNormalStrip γ (a,y)) = 0)
    (hr : ∀ y ∈ uIcc (-R) 0, P (curveNormalStrip γ (b,y)) = 0 ∧
      Q (curveNormalStrip γ (b,y)) = 0)
    (hb : ∀ x ∈ uIcc a b, P (curveNormalStrip γ (x,-R)) = 0 ∧
      Q (curveNormalStrip γ (x,-R)) = 0) :
    (∫ p in Icc (a,-R) (b,0), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
      ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
        (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) =
      -(∫ t in a..b, P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  have hh := integral_pulledPlanarForm_curl_rectangle hP hQ
    (curveNormalStrip_contDiff hγ) (a,-R) (b,0) ⟨hab,neg_nonpos.mpr hR⟩
  have hzright : (∫ y in (-R)..0,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (b,y)) = 0 := by
    calc
      _ = ∫ _y in (-R)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hr y hy).1 (hr y hy).2
      _ = 0 := by simp
  have hzleft : (∫ y in (-R)..0,
      pulledPlanarForm P Q (curveNormalStrip γ) (0,1) (a,y)) = 0 := by
    calc
      _ = ∫ _y in (-R)..(0 : ℝ), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro y hy
        exact pulledPlanarForm_eq_zero (hl y hy).1 (hl y hy).2
      _ = 0 := by simp
  have hzbottom : (∫ x in a..b,
      pulledPlanarForm P Q (curveNormalStrip γ) (1,0) (x,-R)) = 0 := by
    calc
      _ = ∫ _x in a..b, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro x hx
        exact pulledPlanarForm_eq_zero (hb x hx).1 (hb x hx).2
      _ = 0 := by simp
  change (∫ p in Icc (a,-R) (b,0), planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) *
    ((fderiv ℝ Q (curveNormalStrip γ p)) 1 -
      (fderiv ℝ P (curveNormalStrip γ p)) Complex.I)) = _ at hh
  rw [hzright,hzleft,hzbottom,add_zero,zero_sub,sub_zero] at hh
  rw [hh]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  exact normal_strip_base_form hγ P Q t

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_NormalStripImageGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green's identity on the physical image of a normal-coordinate half
rectangle, with its actual Euclidean area measure. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma integral_normal_strip_image_rectangle {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ ∞ γ) (a b c d : ℝ)
    (hi : InjOn (curveNormalStrip γ) (Icc (a,c) (b,d)))
    (hj : ∀ p ∈ Icc (a,c) (b,d),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p)) (q : ℂ → ℝ) :
    (∫ z in (curveNormalStrip γ) '' (Ioo a b ×ˢ Ioo c d), q z) =
      ∫ p in Icc (a,c) (b,d),
        planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) * q (curveNormalStrip γ p) := by
  have hsub : Ioo a b ×ˢ Ioo c d ⊆ Icc (a,c) (b,d) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  rw [integral_image_planarMap (measurableSet_Ioo.prod measurableSet_Ioo)
    (fun p _ => ((curveNormalStrip_contDiff hγ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) p).hasFDerivAt)
    (hi.mono hsub)]
  calc
    _ = ∫ p in Ioo a b ×ˢ Ioo c d,
        planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) * q (curveNormalStrip γ p) := by
      apply setIntegral_congr_fun (measurableSet_Ioo.prod measurableSet_Ioo)
      intro p hp
      dsimp only
      rw [abs_of_nonneg (hj p (hsub hp))]
    _ = _ := by
      rw [← Icc_prod_Icc,Measure.volume_eq_prod]
      exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_LocalizedJordanIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A form supported in one small normal chart contributes exactly the
integral over that parameter arc of the full periodic Jordan circuit. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma periodic_deriv_of_periodic {γ : ℝ → ℂ} {T : ℝ} (hγ : Periodic γ T) :
    Periodic (deriv γ) T := by
  intro t
  rw [← deriv_comp_add_const]
  have h : (fun s => γ (s+T)) = γ := funext hγ
  rw [h]

lemma planarFormIntegrand_continuous {γ : ℝ → ℂ} {P Q : ℂ → ℝ}
    (hγ : ContDiff ℝ ∞ γ) (hP : Continuous P) (hQ : Continuous Q) :
    Continuous (fun t => P (γ t) * (deriv γ t).re + Q (γ t) * (deriv γ t).im) := by
  have hd := (contDiff_infty_iff_deriv.mp hγ).2.continuous
  exact ((hP.comp hγ.continuous).mul (Complex.continuous_re.comp hd)).add
    ((hQ.comp hγ.continuous).mul (Complex.continuous_im.comp hd))

lemma planarFormIntegral_eq_shifted {γ : ℝ → ℂ} (hγ : Periodic γ 1)
    (P Q : ℂ → ℝ) (t : ℝ) :
    planarFormIntegral P Q γ =
      ∫ s in (t-1/2)..(t+1/2),
        P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  have hd := periodic_deriv_of_periodic hγ
  have hp : Periodic (fun s => P (γ s) * (deriv γ s).re +
      Q (γ s) * (deriv γ s).im) 1 := by
    intro s
    dsimp only
    rw [hγ s,hd s]
  have h := hp.intervalIntegral_add_eq 0 (t-1/2)
  simpa only [planarFormIntegral,zero_add,show t-1/2+1 = t+1/2 by ring] using h

lemma normal_box_parameter_mem {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    {s : ℝ} (hs : s ∈ Icc (t-1/2) (t+1/2))
    (hmem : γ s ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    s ∈ Ioo (t-r) (t+r) := by
  obtain ⟨p,hp,hep⟩ := hmem
  have hpK : p ∈ Icc (t-r,-r) (t+r,r) :=
    ⟨⟨hp.1.1.le,hp.2.1.le⟩,⟨hp.1.2.le,hp.2.2.le⟩⟩
  have hp0 : p.2 = 0 := (hf p hpK).mp (hep.symm ▸ hγ.mem_frontier s)
  have hps : γ p.1 = γ s := by simpa only [he,curveNormalStrip,hp0,zero_smul,add_zero] using hep
  have hst : p.1 = s := hγ.eq_of_eq_short hps
    (by linarith [hp.1.1,hs.2]) (by linarith [hp.1.2,hs.1])
  exact hst ▸ hp.1

lemma planarFormIntegral_localized {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    {P Q : ℂ → ℝ} (hP : Continuous P) (hQ : Continuous Q)
    (hzero : ∀ z ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r), P z = 0 ∧ Q z = 0) :
    planarFormIntegral P Q γ =
      ∫ s in (t-r)..(t+r), P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im := by
  let f := fun s => P (γ s) * (deriv γ s).re + Q (γ s) * (deriv γ s).im
  have hc : Continuous f := planarFormIntegrand_continuous hγ.smooth hP hQ
  have hz (s : ℝ) (hs : s ∈ Icc (t-1/2) (t+1/2))
      (hout : s ∉ Ioo (t-r) (t+r)) : f s = 0 := by
    have hn : γ s ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) :=
      fun h => hout (normal_box_parameter_mem hγ e t r hrsmall he hf hs h)
    simp only [f,(hzero _ hn).1,(hzero _ hn).2,zero_mul,zero_add]
  have hl : (∫ s in (t-1/2)..(t-r), f s) = 0 := by
    calc
      _ = ∫ _s in (t-1/2)..(t-r), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : t-1/2 ≤ t-r)] at hs
        exact hz s ⟨hs.1,by linarith [hs.2]⟩ (fun h => (not_lt_of_ge hs.2) h.1)
      _ = 0 := by simp
  have hu : (∫ s in (t+r)..(t+1/2), f s) = 0 := by
    calc
      _ = ∫ _s in (t+r)..(t+1/2), (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro s hs
        rw [uIcc_of_le (by linarith : t+r ≤ t+1/2)] at hs
        exact hz s ⟨by linarith [hs.1],hs.2⟩ (fun h => (not_lt_of_ge hs.1) h.2)
      _ = 0 := by simp
  rw [planarFormIntegral_eq_shifted hγ.periodic P Q t]
  change (∫ s in (t-1/2)..(t+1/2), f s) = _
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (t-1/2) (t-r)) (hc.intervalIntegrable (t-r) (t+1/2)),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (t-r) (t+r)) (hc.intervalIntegrable (t+r) (t+1/2)),hl,hu]
  simp only [zero_add,add_zero]
  rfl

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalizedNormalGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green's identity for a smooth form supported in one normal chart on
the inward-left side of a regular Jordan circuit. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma planar_curl_zero_off_support {P Q : ℂ → ℝ} {N : Set ℂ}
    (hP : tsupport P ⊆ N) (hQ : tsupport Q ⊆ N) {z : ℂ} (hz : z ∉ N) :
    (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I = 0 := by
  rw [fderiv_of_notMem_tsupport ℝ (fun h => hz (hQ h)),
    fderiv_of_notMem_tsupport ℝ (fun h => hz (hP h))]
  simp

lemma localized_normal_green_upper {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hj : ∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p))
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hPs : tsupport P ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    (hQs : tsupport Q ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hfe : (e : (ℝ × ℝ) → ℂ) = curveNormalStrip γ := funext he
  have hz : ∀ z ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r), P z = 0 ∧ Q z = 0 := by
    intro z hz
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hz (hPs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (hQs h))⟩
  have hedge (p : ℝ × ℝ) (hpK : p ∈ Icc (t-r,-r) (t+r,r))
      (hpe : p.1 = t-r ∨ p.1 = t+r ∨ p.2 = -r ∨ p.2 = r) :
      P (curveNormalStrip γ p) = 0 ∧ Q (curveNormalStrip γ p) = 0 := by
    rw [← he]
    exact hz _ (normal_box_boundary_not_image e t r hK hpK hpe)
  have hl (y : ℝ) (hy : y ∈ uIcc 0 r) :
      P (curveNormalStrip γ (t-r,y)) = 0 ∧ Q (curveNormalStrip γ (t-r,y)) = 0 := by
    rw [uIcc_of_le hr.le] at hy
    exact hedge _ ⟨⟨le_rfl,by linarith [hy.1]⟩,⟨by linarith,hy.2⟩⟩ (Or.inl rfl)
  have hright (y : ℝ) (hy : y ∈ uIcc 0 r) :
      P (curveNormalStrip γ (t+r,y)) = 0 ∧ Q (curveNormalStrip γ (t+r,y)) = 0 := by
    rw [uIcc_of_le hr.le] at hy
    exact hedge _ ⟨⟨by linarith,by linarith [hy.1]⟩,⟨le_rfl,hy.2⟩⟩ (Or.inr (Or.inl rfl))
  have ht (x : ℝ) (hx : x ∈ uIcc (t-r) (t+r)) :
      P (curveNormalStrip γ (x,r)) = 0 ∧ Q (curveNormalStrip γ (x,r)) = 0 := by
    rw [uIcc_of_le (by linarith : t-r ≤ t+r)] at hx
    exact hedge _ ⟨⟨hx.1,by linarith⟩,⟨hx.2,le_rfl⟩⟩ (Or.inr (Or.inr (Or.inr rfl)))
  have hsub : Icc (t-r,0) (t+r,r) ⊆ Icc (t-r,-r) (t+r,r) := by
    intro p hp
    exact ⟨⟨hp.1.1,by linarith [hp.1.2]⟩,hp.2⟩
  have hi : InjOn (curveNormalStrip γ) (Icc (t-r,0) (t+r,r)) := by
    rw [← hfe]
    exact e.injOn.mono (hsub.trans hK)
  have hj' : ∀ p ∈ Icc (t-r,0) (t+r,r),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) := by
    rw [← hfe]
    exact fun p hp => (hj p (hsub hp)).le
  have him := integral_normal_strip_image_rectangle hγ.smooth (t-r) (t+r) 0 r hi hj'
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)
  have harea : (∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z in e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r),
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    rw [← normal_box_upper_inter H e t r hf hp hn]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (jordanInterior_isOpen H).measurableSet inter_subset_left
    intro z hz'
    exact planar_curl_zero_off_support hPs hQs (fun h => hz'.2 ⟨hz'.1,h⟩)
  rw [planarFormIntegral_localized hγ e t r hr hrsmall he hf hP.continuous hQ.continuous hz]
  rw [harea,hfe,him]
  exact (normal_strip_upper_green hP hQ hγ.smooth (t-r) (t+r) r
    (by linarith) hr.le hl hright ht).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_LocalizedNormalGreenLower
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The inward-right counterpart, with the same unit orientation sign. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma localized_normal_green_lower {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ)
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r) (hrsmall : r < 1/4)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (hj : ∀ p ∈ Icc (t-r,-r) (t+r,r), 0 < planarMapJacobian (fderiv ℝ e p))
    (hp : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H)
    (hn : e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hPs : tsupport P ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r))
    (hQs : tsupport Q ⊆ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r)) :
    -planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hfe : (e : (ℝ × ℝ) → ℂ) = curveNormalStrip γ := funext he
  have hz : ∀ z ∉ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r), P z = 0 ∧ Q z = 0 := by
    intro z hz
    exact ⟨image_eq_zero_of_notMem_tsupport (fun h => hz (hPs h)),
      image_eq_zero_of_notMem_tsupport (fun h => hz (hQs h))⟩
  have hedge (p : ℝ × ℝ) (hpK : p ∈ Icc (t-r,-r) (t+r,r))
      (hpe : p.1 = t-r ∨ p.1 = t+r ∨ p.2 = -r ∨ p.2 = r) :
      P (curveNormalStrip γ p) = 0 ∧ Q (curveNormalStrip γ p) = 0 := by
    rw [← he]
    exact hz _ (normal_box_boundary_not_image e t r hK hpK hpe)
  have hl (y : ℝ) (hy : y ∈ uIcc (-r) 0) :
      P (curveNormalStrip γ (t-r,y)) = 0 ∧ Q (curveNormalStrip γ (t-r,y)) = 0 := by
    rw [uIcc_of_le (neg_nonpos.mpr hr.le)] at hy
    exact hedge _ ⟨⟨le_rfl,hy.1⟩,⟨by linarith,by linarith [hy.2]⟩⟩ (Or.inl rfl)
  have hright (y : ℝ) (hy : y ∈ uIcc (-r) 0) :
      P (curveNormalStrip γ (t+r,y)) = 0 ∧ Q (curveNormalStrip γ (t+r,y)) = 0 := by
    rw [uIcc_of_le (neg_nonpos.mpr hr.le)] at hy
    exact hedge _ ⟨⟨by linarith,hy.1⟩,⟨le_rfl,by linarith [hy.2]⟩⟩ (Or.inr (Or.inl rfl))
  have ht (x : ℝ) (hx : x ∈ uIcc (t-r) (t+r)) :
      P (curveNormalStrip γ (x,-r)) = 0 ∧ Q (curveNormalStrip γ (x,-r)) = 0 := by
    rw [uIcc_of_le (by linarith : t-r ≤ t+r)] at hx
    exact hedge _ ⟨⟨hx.1,le_rfl⟩,⟨hx.2,by linarith⟩⟩ (Or.inr (Or.inr (Or.inl rfl)))
  have hsub : Icc (t-r,-r) (t+r,0) ⊆ Icc (t-r,-r) (t+r,r) := by
    intro p hp
    exact ⟨hp.1,⟨hp.2.1,by linarith [hp.2.2]⟩⟩
  have hi : InjOn (curveNormalStrip γ) (Icc (t-r,-r) (t+r,0)) := by
    rw [← hfe]
    exact e.injOn.mono (hsub.trans hK)
  have hj' : ∀ p ∈ Icc (t-r,-r) (t+r,0),
      0 ≤ planarMapJacobian (fderiv ℝ (curveNormalStrip γ) p) := by
    rw [← hfe]
    exact fun p hp => (hj p (hsub hp)).le
  have him := integral_normal_strip_image_rectangle hγ.smooth (t-r) (t+r) (-r) 0 hi hj'
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)
  have harea : (∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z in e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0),
        (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    rw [← normal_box_lower_inter H e t r hf hp hn]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      (jordanInterior_isOpen H).measurableSet inter_subset_left
    intro z hz'
    exact planar_curl_zero_off_support hPs hQs (fun h => hz'.2 ⟨hz'.1,h⟩)
  rw [planarFormIntegral_localized hγ e t r hr hrsmall he hf hP.continuous hQ.continuous hz]
  rw [harea,hfe,him]
  exact (normal_strip_lower_green hP hQ hγ.smooth (t-r) (t+r) r
    (by linarith) hr.le hl hright ht).symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_LevelChartBox
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric coordinate boxes can be chosen inside any prescribed
ambient neighborhood of a regular level point. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma exists_openPartialHomeomorph_box
    (e : OpenPartialHomeomorph ℂ (ℝ × ℝ)) {x : ℂ} (hx : x ∈ e.source)
    {U : Set ℂ} (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ r > 0, Ioo ((e x).1-r) ((e x).1+r) ×ˢ Ioo ((e x).2-r) ((e x).2+r) ⊆
      e.target ∩ e.symm ⁻¹' U := by
  have hW := e.isOpen_inter_preimage_symm hU
  have hxW : e x ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hx, by simpa only [mem_preimage, e.left_inv hx] using hxU⟩
  obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hW _ hxW
  refine ⟨r, hr, ?_⟩
  intro q hq
  apply hsub
  rw [mem_ball, Prod.dist_eq, max_lt_iff, Real.dist_eq, Real.dist_eq]
  constructor <;> rw [abs_lt] <;> constructor <;> linarith [hq.1.1, hq.1.2, hq.2.1, hq.2.2]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularJordanNormalSides
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
attribute [-simp] _root_.OAI.CircleDomainRigidity.FiniteTransfer.coe_mem_sphericalDiskUnion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform local rectangles of the actual normal strip have one inward
and one outward half; no orientation is assumed. -/
open Set Function Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma exists_local_normal_side_pattern
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) (t : ℝ) :
    ∃ r > 0, NormalSidePattern H γ t r true ∨ NormalSidePattern H γ t r false := by
  obtain ⟨e,U,ht,he,_,_,hU,htU,hUt,hstraight⟩ := exists_regular_jordan_boundary_chart hγ t
  have hval : e (t,0) = γ t := by simp [he,curveNormalStrip]
  have htE : γ t ∈ e.target := hval ▸ e.map_source ht
  obtain ⟨r,hr,hbox⟩ := exists_openPartialHomeomorph_box e.symm htE hU htU
  have heinv : e.symm (γ t) = (t,0) := by rw [← hval,e.left_inv ht]
  rw [heinv] at hbox
  simp only [zero_sub,zero_add,
    OpenPartialHomeomorph.symm_target,OpenPartialHomeomorph.symm_symm] at hbox
  have hB : Ioo (t-r) (t+r) ×ˢ Ioo (-r) r ⊆ e.source := hbox.trans inter_subset_left
  have hBU : e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) r) ⊆ U := by
    rintro _ ⟨p,hp,rfl⟩
    exact (hbox hp).2
  have hside := normal_chart_jordan_sides H e U hstraight t r hr hB hBU
    (hval.symm ▸ hγ.mem_frontier t)
  refine ⟨r,hr,?_⟩
  rcases hside with h | h
  · left
    intro s hs ρ hρ
    exact ⟨he (s,ρ) ▸ h.1 ⟨(s,ρ),⟨hs,hρ⟩,rfl⟩,
      he (s,-ρ) ▸ h.2 ⟨(s,-ρ),⟨hs,by constructor <;> linarith [hρ.1,hρ.2]⟩,rfl⟩⟩
  · right
    intro s hs ρ hρ
    exact ⟨he (s,-ρ) ▸ h.1 ⟨(s,-ρ),⟨hs,by constructor <;> linarith [hρ.1,hρ.2]⟩,rfl⟩,
      he (s,ρ) ▸ h.2 ⟨(s,ρ),⟨hs,hρ⟩,rfl⟩⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_RegularJordanNormalOrientation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Connectedness makes the inward choice of the actual normal field
constant around a regular Jordan circuit. -/
open Set Function Metric Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_global_normal_side
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ) :
    ∃ positive : Bool, ∀ t : ℝ, ∃ r > 0, ∀ ρ ∈ Ioo (0 : ℝ) r,
      if positive then
        curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
      else
        curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ := by
  let S : Bool → Set ℝ := fun b => {x | ∃ t r, 0 < r ∧
    NormalSidePattern H γ t r b ∧ x ∈ Ioo (t-r) (t+r)}
  have ho (b : Bool) : IsOpen (S b) := by
    rw [isOpen_iff_mem_nhds]
    rintro x ⟨t,r,hr,hp,hx⟩
    exact Filter.mem_of_superset (isOpen_Ioo.mem_nhds hx)
      (fun y hy => ⟨t,r,hr,hp,hy⟩)
  have hd : Disjoint (S true) (S false) := by
    apply Set.disjoint_left.mpr
    rintro x ⟨t,r,hr,hp,hx⟩ ⟨u,s,hs,hn,hy⟩
    obtain ⟨ρ,hρ0,hρ⟩ := exists_between (lt_min hr hs)
    have hρr : ρ < r := hρ.trans_le (min_le_left _ _)
    have hρs : ρ < s := hρ.trans_le (min_le_right _ _)
    have hi : curveNormalStrip γ (x,ρ) ∈ jordanInterior H := (hp x hx ρ ⟨hρ0,hρr⟩).1
    have he : curveNormalStrip γ (x,ρ) ∈ (closure (jordanInterior H))ᶜ :=
      (hn x hy ρ ⟨hρ0,hρs⟩).2
    exact he (subset_closure hi)
  have hc : (univ : Set ℝ) ⊆ S true ∪ S false := by
    intro t _
    obtain ⟨r,hr,hp | hn⟩ := exists_local_normal_side_pattern hγ t
    · exact Or.inl ⟨t,r,hr,hp,by constructor <;> linarith⟩
    · exact Or.inr ⟨t,r,hr,hn,by constructor <;> linarith⟩
  have hall : (univ : Set ℝ) ⊆ S true ∨ (univ : Set ℝ) ⊆ S false :=
    isPreconnected_univ.subset_or_subset (ho true) (ho false) hd hc
  have hfinish (b : Bool) (hb : (univ : Set ℝ) ⊆ S b) :
      ∀ t : ℝ, ∃ r > 0, ∀ ρ ∈ Ioo (0 : ℝ) r,
        if b then
          curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
            curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
        else
          curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
            curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ := by
    intro t
    obtain ⟨u,r,hr,hp,ht⟩ := hb (mem_univ t)
    exact ⟨r,hr,hp t ht⟩
  rcases hall with h | h
  · exact ⟨true,hfinish true h⟩
  · exact ⟨false,hfinish false h⟩

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Modulus_FixedNormalOrientation
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! One sign works in every local boundary chart of the same Jordan
circuit, before any differential form is chosen. -/
open Set Function Metric Bornology
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma normal_box_sides_fixed {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (e : OpenPartialHomeomorph (ℝ × ℝ) ℂ) (t r : ℝ) (hr : 0 < r)
    (he : ∀ p, e p = curveNormalStrip γ p)
    (hK : Icc (t-r,-r) (t+r,r) ⊆ e.source)
    (hf : ∀ p ∈ Icc (t-r,-r) (t+r,r),
      e p ∈ frontier (jordanInterior H) ↔ p.2 = 0)
    (positive : Bool)
    (hglobal : ∃ δ > 0, ∀ ρ ∈ Ioo (0 : ℝ) δ,
      if positive then
        curveNormalStrip γ (t,ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,-ρ) ∈ (closure (jordanInterior H))ᶜ
      else
        curveNormalStrip γ (t,-ρ) ∈ jordanInterior H ∧
          curveNormalStrip γ (t,ρ) ∈ (closure (jordanInterior H))ᶜ) :
    if positive then
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ jordanInterior H ∧
        e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ (closure (jordanInterior H))ᶜ
    else
      e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) ⊆ jordanInterior H ∧
        e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) ⊆ (closure (jordanInterior H))ᶜ := by
  obtain ⟨δ,hδ,hg⟩ := hglobal
  obtain ⟨ρ,hρ0,hρ⟩ := exists_between (lt_min hr hδ)
  have hρr : ρ < r := hρ.trans_le (min_le_left _ _)
  have hρδ : ρ < δ := hρ.trans_le (min_le_right _ _)
  have hplus : e (t,ρ) ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo 0 r) :=
    ⟨(t,ρ),⟨⟨by linarith,by linarith⟩,⟨hρ0,hρr⟩⟩,rfl⟩
  have hminus : e (t,-ρ) ∈ e '' (Ioo (t-r) (t+r) ×ˢ Ioo (-r) 0) :=
    ⟨(t,-ρ),⟨⟨by linarith,by linarith⟩,⟨by linarith,by linarith⟩⟩,rfl⟩
  rcases normal_box_jordan_sides H e t r hr hK hf with hleft | hright
  · cases positive
    · have hx := (hg ρ ⟨hρ0,hρδ⟩).2
      exact False.elim (hx (subset_closure (he (t,ρ) ▸ hleft.1 hplus)))
    · exact hleft
  · cases positive
    · exact hright
    · have hx := (hg ρ ⟨hρ0,hρδ⟩).1
      exact False.elim ((he (t,ρ) ▸ hright.2 hplus) (subset_closure hx))

lemma regular_jordan_local_green_sign {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    ∃ ε : ℝ, |ε| = 1 ∧ ∀ t : ℝ, ∃ N : Set ℂ, IsOpen N ∧ γ t ∈ N ∧ IsBounded N ∧
      ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        tsupport P ⊆ N → tsupport Q ⊆ N →
        ε * planarFormIntegral P Q γ =
          ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  obtain ⟨positive,hglobal⟩ := regular_jordan_global_normal_side hγ
  refine ⟨if positive then 1 else -1,?_,?_⟩
  · cases positive <;> norm_num
  intro t
  obtain ⟨e,r,hr,hrs,he,hs,hK,hf,hj⟩ := exists_regular_jordan_normal_box hγ t
  let B := Ioo (t-r) (t+r) ×ˢ Ioo (-r) r
  have hBK : B ⊆ Icc (t-r,-r) (t+r,r) := by
    rintro p ⟨hp,hq⟩
    exact ⟨⟨hp.1.le,hq.1.le⟩,⟨hp.2.le,hq.2.le⟩⟩
  have hN : IsOpen (e '' B) :=
    e.isOpen_image_of_subset_source (isOpen_Ioo.prod isOpen_Ioo) (hBK.trans hK)
  have ht : γ t ∈ e '' B := by
    refine ⟨(t,0),⟨⟨by linarith,by linarith⟩,⟨by linarith,hr⟩⟩,?_⟩
    simp only [he,curveNormalStrip,zero_smul,add_zero]
  have hb : IsBounded (e '' B) :=
    ((isCompact_Icc.image hs.continuous).isBounded).subset (image_mono hBK)
  have hside := normal_box_sides_fixed e t r hr he hK hf positive (hglobal t)
  refine ⟨e '' B,hN,ht,hb,?_⟩
  intro P Q hP hQ hPs hQs
  cases positive
  · simpa using localized_normal_green_lower hγ e t r hr hrs he hK hf hj
      hside.1 hside.2 hP hQ hPs hQs
  · simpa using localized_normal_green_upper hγ e t r hr hrs he hK hf hj
      hside.1 hside.2 hP hQ hPs hQs

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ClosedDiskIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Outer circles have zero plane area; the source density integral is
unchanged when the outer disk is closed. -/
open Set Function Filter MeasureTheory Metric
noncomputable section
namespace CircleDomainRigidity

 theorem integral_inter_closedBall_eq_ball (U : Set ℂ) (c : ℂ) (r : ℝ) (q : ℂ → ℝ) :
    (∫ z in U ∩ closedBall c r, q z) = ∫ z in U ∩ ball c r, q z := by
  apply setIntegral_congr_set
  filter_upwards [(measure_eq_zero_iff_ae_notMem).mp (Measure.addHaar_sphere volume c r)] with z hz
  apply propext
  have hne : dist z c ≠ r := hz
  show (z ∈ U ∩ closedBall c r) ↔ (z ∈ U ∩ ball c r)
  simp only [mem_inter_iff,mem_closedBall,mem_ball]
  exact and_congr_right (fun _ => ⟨fun h => lt_of_le_of_ne h hne,fun h => h.le⟩)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_ComplexPolarDifferential
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Smoothness, differential, and oriented Jacobian of the actual complex
polar parametrization, including the radius-zero line. -/
open Set Function
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma contDiff_complexPolarSymm : ContDiff ℝ ∞ (fun p => Complex.polarCoord.symm p) := by
  simp_rw [Complex.polarCoord_symm_apply]
  exact (Complex.ofRealCLM.contDiff.comp contDiff_fst).mul
    (((Complex.ofRealCLM.contDiff.comp (Real.contDiff_cos.comp contDiff_snd))).add
      ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_sin.comp contDiff_snd)).mul (contDiff_const (c := Complex.I))))

lemma complexPolarSymm_fderiv (p v : ℝ × ℝ) :
    (fderiv ℝ (fun x => Complex.polarCoord.symm x) p) v =
      ((Real.cos p.2 * v.1 - p.1 * Real.sin p.2 * v.2 : ℝ) : ℂ) +
      ((Real.sin p.2 * v.1 + p.1 * Real.cos p.2 * v.2 : ℝ) : ℂ) * Complex.I := by
  have hd := Complex.equivRealProdCLM.symm.hasFDerivAt.comp p (hasFDerivAt_polarCoord_symm p)
  change HasFDerivAt (fun x => Complex.polarCoord.symm x) _ p at hd
  rw [hd.fderiv]
  simp [fderivPolarCoordSymm,Matrix.toLin_finTwoProd_toContinuousLinearMap,
    Complex.equivRealProdCLM_symm_apply,sub_eq_add_neg,mul_assoc]

lemma complexPolarSymm_jacobian (p : ℝ × ℝ) :
    ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (1,0)).re *
        ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (0,1)).im -
      ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (1,0)).im *
        ((fderiv ℝ (fun x => Complex.polarCoord.symm x) p) (0,1)).re = p.1 := by
  simp only [complexPolarSymm_fderiv,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    mul_zero,mul_one,mul_neg,sub_zero,zero_add,add_zero,zero_sub]
  linear_combination p.1 * Real.sin_sq_add_cos_sq p.2

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteGreenAssembly
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Finite additivity of the actual boundary integral and curl integral,
and assembly from a smooth partition on the closed Jordan disk. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma planarFormIntegral_finite_sum {ι : Type*} [Fintype ι]
    {γ : ℝ → ℂ} (hγ : ContDiff ℝ ∞ γ) (A B : ι → ℂ → ℝ)
    (hA : ∀ i, Continuous (A i)) (hB : ∀ i, Continuous (B i)) :
    planarFormIntegral (fun z => ∑ i, A i z) (fun z => ∑ i, B i z) γ =
      ∑ i, planarFormIntegral (A i) (B i) γ := by
  unfold planarFormIntegral
  rw [← intervalIntegral.integral_finsetSum (fun i _ =>
    (planarFormIntegrand_continuous hγ (hA i) (hB i)).intervalIntegrable 0 1)]
  apply intervalIntegral.integral_congr
  intro t _
  simp only [Finset.sum_add_distrib,Finset.sum_mul]

lemma integral_planar_curl_finite_sum {ι : Type*} [Fintype ι]
    (H : ℂ ≃ₜ ℂ) (A B : ι → ℂ → ℝ)
    (hA : ∀ i, ContDiff ℝ ∞ (A i)) (hB : ∀ i, ContDiff ℝ ∞ (B i)) :
    (∫ z in jordanInterior H,
      (fderiv ℝ (fun w => ∑ i, B i w) z) 1 -
        (fderiv ℝ (fun w => ∑ i, A i w) z) Complex.I) =
      ∑ i, ∫ z in jordanInterior H, (fderiv ℝ (B i) z) 1 - (fderiv ℝ (A i) z) Complex.I := by
  have hi (i : ι) : IntegrableOn
      (fun z => (fderiv ℝ (B i) z) 1 - (fderiv ℝ (A i) z) Complex.I) (jordanInterior H) := by
    have hc := ((hB i).continuous_fderiv (by simp)).clm_apply (continuous_const (y := (1 : ℂ)))
    have hd := ((hA i).continuous_fderiv (by simp)).clm_apply (continuous_const (y := Complex.I))
    exact ((hc.sub hd).continuousOn.integrableOn_compact
      (isCompact_closure_jordanInterior H)).mono_set subset_closure
  rw [← integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply setIntegral_congr_fun (jordanInterior_isOpen H).measurableSet
  intro z _
  dsimp only
  rw [fderiv_fun_sum (fun i _ => (hB i).differentiable (by simp) z),
    fderiv_fun_sum (fun i _ => (hA i).differentiable (by simp) z)]
  simp only [_root_.sum_apply,Finset.sum_sub_distrib]

lemma finite_green_assembly {ι : Type*} [Fintype ι]
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : RegularJordanParametrization H γ)
    (ρ : ι → ℂ → ℝ) (hρ : ∀ i, ContDiff ℝ ∞ (ρ i))
    (hsum : ∀ z ∈ closure (jordanInterior H), ∑ i, ρ i z = 1)
    (ε : ℝ) {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hlocal : ∀ i, ε * planarFormIntegral (fun z => ρ i z * P z) (fun z => ρ i z * Q z) γ =
      ∫ z in jordanInterior H,
        (fderiv ℝ (fun w => ρ i w * Q w) z) 1 -
          (fderiv ℝ (fun w => ρ i w * P w) z) Complex.I) :
    ε * planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  let A := fun i z => ρ i z * P z
  let B := fun i z => ρ i z * Q z
  have hA (i : ι) : ContDiff ℝ ∞ (A i) := (hρ i).mul hP
  have hB (i : ι) : ContDiff ℝ ∞ (B i) := (hρ i).mul hQ
  have hsumF (f : ℂ → ℝ) (z : ℂ) (hz : z ∈ closure (jordanInterior H)) :
      (∑ i, ρ i z * f z) = f z := by rw [← Finset.sum_mul,hsum z hz,one_mul]
  have hb : planarFormIntegral (fun z => ∑ i, A i z) (fun z => ∑ i, B i z) γ =
      planarFormIntegral P Q γ := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [hsumF P _ (hγ.mem_frontier t).1,hsumF Q _ (hγ.mem_frontier t).1]
  have heq (f : ℂ → ℝ) (z : ℂ) (hz : z ∈ jordanInterior H) :
      (fun w => ∑ i, ρ i w * f w) =ᶠ[𝓝 z] f := by
    filter_upwards [(jordanInterior_isOpen H).mem_nhds hz] with w hw
    exact hsumF f w (subset_closure hw)
  have ha : (∫ z in jordanInterior H,
      (fderiv ℝ (fun w => ∑ i, B i w) z) 1 -
        (fderiv ℝ (fun w => ∑ i, A i w) z) Complex.I) =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    apply setIntegral_congr_fun (jordanInterior_isOpen H).measurableSet
    intro z hz
    change (fderiv ℝ (fun w => ∑ i, ρ i w * Q w) z) 1 -
      (fderiv ℝ (fun w => ∑ i, ρ i w * P w) z) Complex.I = _
    rw [(heq Q z hz).fderiv_eq,(heq P z hz).fderiv_eq]
  rw [← hb,planarFormIntegral_finite_sum hγ.smooth A B
      (fun i => (hA i).continuous) (fun i => (hB i).continuous),Finset.mul_sum]
  change (∑ i, ε * planarFormIntegral (fun z => ρ i z * P z)
    (fun z => ρ i z * Q z) γ) = _
  simp_rw [hlocal]
  exact (integral_planar_curl_finite_sum H A B hA hB).symm.trans ha

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteHoleIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact subtraction of finitely many disjoint round holes from a
Jordan-domain area integral. -/
open Set Function MeasureTheory Metric
open scoped BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma integral_finite_round_holes (H : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H)
    {q : ℂ → ℝ} (hq : Continuous q) :
    (∫ z in jordanInterior H, q z) - ∑ i, ∫ z in ball (c i) (r i), q z =
      ∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i), q z := by
  have hj : IntegrableOn q (jordanInterior H) :=
    (hq.continuousOn.integrableOn_compact (isCompact_closure_jordanInterior H)).mono_set subset_closure
  have hcb (i : Fin n) : IntegrableOn q (closedBall (c i) (r i)) := hj.mono_set (hin i)
  have hsame (i : Fin n) : (∫ z in closedBall (c i) (r i), q z) =
      ∫ z in ball (c i) (r i), q z := by
    simpa only [univ_inter] using integral_inter_closedBall_eq_ball univ (c i) (r i) q
  rw [setIntegral_sdiff (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet)
    hj (iUnion_subset hin),integral_iUnion_fintype
      (fun _ => isClosed_closedBall.measurableSet) hd hcb]
  simp_rw [hsame]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_FiniteSmoothCover
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite smooth partition subordinate to bounded neighborhoods of a
compact planar set, retaining compact supports and exact sum one. -/
open Set Function Metric Bornology
open scoped Topology Manifold ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma exists_finite_smooth_cover {K : Set ℂ} (hK : IsCompact K)
    (U : K → Set ℂ) (hU : ∀ x, IsOpen (U x)) (hxU : ∀ x : K, (x : ℂ) ∈ U x)
    (hb : ∀ x, IsBounded (U x)) :
    ∃ (I : Finset K) (ρ : I → ℂ → ℝ),
      (∀ i, ContDiff ℝ ∞ (ρ i)) ∧ (∀ i, HasCompactSupport (ρ i)) ∧
      (∀ i, tsupport (ρ i) ⊆ U i.val) ∧
      (∀ z ∈ K, ∑ i, ρ i z = 1) := by
  classical
  have hcover : K ⊆ ⋃ x : K, U x := by
    intro z hz
    exact mem_iUnion.mpr ⟨⟨z,hz⟩,hxU ⟨z,hz⟩⟩
  obtain ⟨I,hI⟩ := hK.elim_finite_subcover U hU hcover
  have hcover' : K ⊆ ⋃ i : I, U i.val := by
    intro z hz
    obtain ⟨x,hx,hzx⟩ := mem_iUnion₂.mp (hI hz)
    exact mem_iUnion.mpr ⟨⟨x,hx⟩,hzx⟩
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate
    (𝓘(ℝ,ℂ)) hK.isClosed (fun i : I => U i.val) (fun i => hU i.val) hcover'
  refine ⟨I,fun i z => p i z,?_,?_,hp,?_⟩
  · intro i
    exact contMDiff_iff_contDiff.mp (p i).contMDiff
  · intro i
    exact isCompact_iff_isClosed_bounded.mpr ⟨isClosed_tsupport _,(hb i.val).subset (hp i)⟩
  · intro z hz
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hz

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_CompactPlanarCurl
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The integral of a compactly supported smooth derivative, and hence of
its planar curl, vanishes on the whole plane. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma integral_compact_fderiv_eq_zero {f : ℂ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) (v : ℂ) :
    (∫ z, (fderiv ℝ f z) v) = 0 := by
  have hd : Continuous (fun z => (fderiv ℝ f z) v) :=
    (hf.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply continuous_const
  have hi : Integrable (fun z => (fderiv ℝ f z) v) volume := hd.integrable_of_hasCompactSupport (hc.fderiv_apply ℝ v)
  have he := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) (f := fun _ : ℂ => (1 : ℝ)) (g := f) (v := v)
    (by
      simp only [fderiv_const_apply,zero_apply,zero_mul]
      exact integrable_zero _ _ _)
    (by simpa only [one_mul] using hi)
    (by simpa only [one_mul] using hf.continuous.integrable_of_hasCompactSupport hc)
    (fun _ _ => differentiableAt_const _)
    (fun z _ => hf.differentiable (by simp) z)
  simpa only [one_mul,fderiv_const_apply,zero_apply,zero_mul,integral_zero,neg_zero] using he

lemma integral_compact_planar_curl {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q) :
    (∫ z, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) = 0 := by
  have hiP : Integrable (fun z => (fderiv ℝ P z) Complex.I) volume := ((hP.continuous_fderiv (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).clm_apply
    (continuous_const (y := Complex.I))).integrable_of_hasCompactSupport (hcP.fderiv_apply ℝ _)
  have hiQ : Integrable (fun z => (fderiv ℝ Q z) 1) volume := ((hQ.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := (1 : ℂ)))).integrable_of_hasCompactSupport (hcQ.fderiv_apply ℝ _)
  rw [integral_sub hiQ hiP,integral_compact_fderiv_eq_zero hQ hcQ,
    integral_compact_fderiv_eq_zero hP hcP,sub_self]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_InteriorLocalGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A form supported strictly inside the Jordan domain has zero boundary
integral and zero total curl integral. -/
open Set Function Filter MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma interior_local_green {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) (ε : ℝ)
    {P Q : ℂ → ℝ} (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q)
    (hcP : HasCompactSupport P) (hcQ : HasCompactSupport Q)
    (hPs : tsupport P ⊆ jordanInterior H) (hQs : tsupport Q ⊆ jordanInterior H) :
    ε * planarFormIntegral P Q γ =
      ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have hb : planarFormIntegral P Q γ = 0 := by
    unfold planarFormIntegral
    calc
      _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t _
        have hn : γ t ∉ jordanInterior H := by
          intro ht
          exact (hγ.mem_frontier t).2 ((jordanInterior_isOpen H).interior_eq.symm ▸ ht)
        have hp := image_eq_zero_of_notMem_tsupport (f := P) (fun h => hn (hPs h))
        have hq := image_eq_zero_of_notMem_tsupport (f := Q) (fun h => hn (hQs h))
        dsimp only
        rw [hp,hq,zero_mul,zero_mul,zero_add]
      _ = 0 := by simp
  have hi : (∫ z in jordanInterior H,
      (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) =
      ∫ z, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [] with z hz
    exact planar_curl_zero_off_support hPs hQs hz
  rw [hb,mul_zero,hi,integral_compact_planar_curl hP hQ hcP hcQ]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PolarAnnulusIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polar integration on a bounded annulus, with nonnegative measurable
integrands. The angular interval is fixed to the standard polar chart. -/
open Set MeasureTheory Metric Real
open scoped ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma complex_polar_symm_circleMap (p : ℝ × ℝ) :
    Complex.polarCoord.symm p = circleMap 0 p.1 p.2 := by
  rw [Complex.polarCoord_symm_apply]
  apply Complex.ext <;> simp [circleMap_zero_re, circleMap_zero_im, Complex.cos_ofReal_re, Complex.sin_ofReal_re]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Sobolev_PolarDiskIntegral
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Signed real polar integration over a disk, on the closed parameter
rectangle needed for the elementary divergence theorem. -/
open Set Function MeasureTheory Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma integral_polar_disk (q : ℂ → ℝ) (R : ℝ) :
    (∫ z in ball (0 : ℂ) R, q z) =
      ∫ p in Icc (0, -Real.pi) (R, Real.pi), p.1 * q (Complex.polarCoord.symm p) := by
  let A := ball (0 : ℂ) R
  let S := Ioo (0 : ℝ) R
  let T := Ioo (-Real.pi) Real.pi
  let f : ℝ × ℝ → ℝ := fun p => p.1 * q (Complex.polarCoord.symm p)
  have hP : MeasurableSet polarCoord.target := polarCoord.open_target.measurableSet
  have hp := Complex.integral_comp_polarCoord_symm (A.indicator q)
  rw [integral_indicator isOpen_ball.measurableSet] at hp
  calc
    _ = ∫ p in polarCoord.target, p.1 * (A.indicator q) (Complex.polarCoord.symm p) := hp.symm
    _ = ∫ p, (S ×ˢ T).indicator f p := by
      rw [← integral_indicator hP]
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ polarCoord.target
      · have hp0 : 0 < p.1 := hp.1
        have hmem : Complex.polarCoord.symm p ∈ A ↔ p.1 ∈ S := by
          simp only [A,S,mem_ball_zero_iff,mem_Ioo,Complex.norm_polarCoord_symm,
            abs_of_pos hp0,and_iff_right hp0]
        by_cases hS : p.1 ∈ S
        · have hST : p ∈ S ×ˢ T := ⟨hS,hp.2⟩
          rw [indicator_of_mem hp,indicator_of_mem hST,indicator_of_mem (hmem.mpr hS)]
        · have hST : p ∉ S ×ˢ T := fun h => hS h.1
          rw [indicator_of_mem hp,indicator_of_notMem hST,
            indicator_of_notMem (fun h => hS (hmem.mp h)),mul_zero]
      · have hST : p ∉ S ×ˢ T := fun h => hp ⟨h.1.1,h.2⟩
        rw [indicator_of_notMem hp,indicator_of_notMem hST]
    _ = ∫ p in S ×ˢ T, f p := integral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)
    _ = _ := by
      rw [← Icc_prod_Icc,Measure.volume_eq_prod]
      exact setIntegral_congr_set (Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_JordanGreenProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The signed Green formula on a regular Jordan disk, proved by a finite
smooth partition and the actual local normal charts. -/
open Set Function MeasureTheory Metric Bornology
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity

lemma regular_jordan_green {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) :
    ∃ ε : ℝ, |ε| = 1 ∧ ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
      ε * planarFormIntegral P Q γ =
        ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  classical
  obtain ⟨ε,hε,hboundary⟩ := regular_jordan_local_green_sign hγ
  let K := closure (jordanInterior H)
  have hloc (x : K) : ∃ U : Set ℂ, IsOpen U ∧ (x : ℂ) ∈ U ∧ IsBounded U ∧
      ∀ P Q : ℂ → ℝ, ContDiff ℝ ∞ P → ContDiff ℝ ∞ Q →
        HasCompactSupport P → HasCompactSupport Q → tsupport P ⊆ U → tsupport Q ⊆ U →
        ε * planarFormIntegral P Q γ =
          ∫ z in jordanInterior H, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
    by_cases hx : (x : ℂ) ∈ jordanInterior H
    · refine ⟨jordanInterior H ∩ ball (x : ℂ) 1,
        (jordanInterior_isOpen H).inter isOpen_ball,⟨hx,mem_ball_self zero_lt_one⟩,
        isBounded_ball.subset inter_subset_right,?_⟩
      intro P Q hP hQ hcP hcQ hPs hQs
      exact interior_local_green hγ ε hP hQ hcP hcQ
        (hPs.trans inter_subset_left) (hQs.trans inter_subset_left)
    · have hxf : (x : ℂ) ∈ frontier (jordanInterior H) := by
        rw [frontier,(jordanInterior_isOpen H).interior_eq]
        exact ⟨x.property,hx⟩
      obtain ⟨t,_,ht⟩ := hγ.boundary.symm ▸ hxf
      obtain ⟨U,hU,htU,hUb,hh⟩ := hboundary t
      refine ⟨U,hU,ht ▸ htU,hUb,?_⟩
      intro P Q hP hQ _ _ hPs hQs
      exact hh P Q hP hQ hPs hQs
  choose U hU hxU hb hgreen using hloc
  obtain ⟨I,ρ,hρ,hρc,hρU,hρsum⟩ := exists_finite_smooth_cover
    (isCompact_closure_jordanInterior H) U hU hxU hb
  refine ⟨ε,hε,?_⟩
  intro P Q hP hQ
  apply finite_green_assembly hγ ρ hρ hρsum ε hP hQ
  intro i
  exact hgreen i.val (fun z => ρ i z * P z) (fun z => ρ i z * Q z)
    ((hρ i).mul hP) ((hρ i).mul hQ) (hρc i).mul_right (hρc i).mul_right
    (tsupport_mul_subset_left.trans (hρU i)) (tsupport_mul_subset_left.trans (hρU i))

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundCircleParametrization
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual positively sized round disk and its once-traversed regular
boundary, used to specialize the published Green identity to a disk. -/
open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 theorem unitCircleParam_hasDerivAt (R t : ℝ) :
    HasDerivAt (unitCircleParam 0 R)
      (circleMap 0 R (2*Real.pi*t) * Complex.I * (2*Real.pi)) t := by
  change HasDerivAt (fun s : ℝ => circleMap 0 R (2*Real.pi*s)) _ t
  convert (hasDerivAt_circleMap 0 R (2*Real.pi*t)).scomp t
    ((hasDerivAt_id t).const_mul (2*Real.pi)) using 1 <;>
    (try simp only [Function.comp_def, Complex.real_smul, Complex.ofReal_mul,
      Complex.ofReal_ofNat, mul_one]) <;>
    first | rfl | ring


end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_PolarFormBoundary
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The angular edge of a polar rectangle is the actual circle line
integral, with the normalization and orientation fixed explicitly. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma pulledPolarForm_periodic (P Q : ℂ → ℝ) (R : ℝ) :
    Periodic (fun θ => pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ))
      (2*Real.pi) := by
  intro θ
  simp only [pulledPlanarForm,complexPolarSymm_fderiv]
  simp only [Complex.polarCoord_symm_apply,Real.cos_add_two_pi,Real.sin_add_two_pi]

lemma pulledPolarForm_radius_zero (P Q : ℂ → ℝ) (θ : ℝ) :
    pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (0,θ) = 0 := by
  simp only [pulledPlanarForm,complexPolarSymm_fderiv]
  simp

lemma planarFormIntegral_circle_eq_polar (P Q : ℂ → ℝ) (R : ℝ) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ θ in (-Real.pi)..Real.pi,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ) := by
  let B : ℝ → ℝ := fun θ =>
    pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (0,1) (R,θ)
  have he : planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ t in (0 : ℝ)..1, (2*Real.pi) * B (2*Real.pi*t) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    dsimp only
    rw [(unitCircleParam_hasDerivAt R t).deriv]
    dsimp only [B,pulledPlanarForm]
    rw [complexPolarSymm_fderiv,complex_polar_symm_circleMap]
    dsimp only [unitCircleParam]
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,
      Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,
      circleMap_zero_re,circleMap_zero_im]
    rw [show (2 : ℂ).re = 2 from rfl,show (2 : ℂ).im = 0 from rfl]
    ring
  rw [he]
  have hn : (∫ t in (0 : ℝ)..1, (2*Real.pi) * B (2*Real.pi*t)) =
      ∫ θ in (0 : ℝ)..2*Real.pi, B θ := by
    rw [intervalIntegral.integral_const_mul]
    simpa only [smul_eq_mul,mul_zero,mul_one] using
      (intervalIntegral.smul_integral_comp_mul_left B (a := (0 : ℝ)) (b := 1) (2*Real.pi))
  rw [hn]
  have hp := (pulledPolarForm_periodic P Q R).intervalIntegral_add_eq (-Real.pi) 0
  have hbound : -Real.pi+2*Real.pi = Real.pi := by ring
  simpa only [hbound,zero_add] using hp.symm

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_RoundDiskGreenProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Green's formula on a round disk, proved by polar pullback and the
existing rectangular divergence theorem. No Green input is used. -/
open Set Function MeasureTheory
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma roundDiskGreen {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) {R : ℝ} (hR : 0 < R) :
    planarFormIntegral P Q (unitCircleParam 0 R) =
      ∫ z in Metric.ball (0 : ℂ) R, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  have he := integral_pulledPlanarForm_curl_rectangle hP hQ contDiff_complexPolarSymm
    (0,-Real.pi) (R,Real.pi) ⟨hR.le,by linarith [Real.pi_pos]⟩
  simp only [complexPolarSymm_jacobian] at he
  rw [← planarFormIntegral_circle_eq_polar P Q R] at he
  simp_rw [pulledPolarForm_radius_zero] at he
  simp only [intervalIntegral.integral_zero,sub_zero] at he
  have hseam :
      (∫ s in (0 : ℝ)..R,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (1,0) (s,Real.pi)) =
      ∫ s in (0 : ℝ)..R,
        pulledPlanarForm P Q (fun p => Complex.polarCoord.symm p) (1,0) (s,-Real.pi) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    simp only [pulledPlanarForm,complexPolarSymm_fderiv]
    simp [Complex.polarCoord_symm_apply]
  rw [hseam,← integral_polar_disk (fun z =>
    (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I) R] at he
  linarith

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_TranslatedDiskGreen
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Translation of the proved round-disk Green identity to any center. -/
open Set Function MeasureTheory Metric
open scoped Topology ContDiff
noncomputable section
namespace CircleDomainRigidity

lemma unitCircleParam_translate (c : ℂ) (R t : ℝ) :
    unitCircleParam c R t = c + unitCircleParam 0 R t := by
  simp only [unitCircleParam,circleMap,zero_add]

lemma planarFormIntegral_circle_translate (c : ℂ) (R : ℝ) (P Q : ℂ → ℝ) :
    planarFormIntegral P Q (unitCircleParam c R) =
      planarFormIntegral (fun z => P (c+z)) (fun z => Q (c+z)) (unitCircleParam 0 R) := by
  have heq : unitCircleParam c R = (fun t => c + unitCircleParam 0 R t) :=
    funext (unitCircleParam_translate c R)
  have hd (t : ℝ) : deriv (unitCircleParam c R) t = deriv (unitCircleParam 0 R) t := by
    rw [heq,deriv_const_add]
  unfold planarFormIntegral
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [unitCircleParam_translate,hd]

lemma integral_translated_ball (c : ℂ) (R : ℝ) (q : ℂ → ℝ) :
    (∫ z in ball c R, q z) = ∫ z in ball (0 : ℂ) R, q (c+z) := by
  have hm : MeasurePreserving (fun z : ℂ => c+z) volume volume :=
    measurePreserving_add_left volume c
  have he : MeasurableEmbedding (fun z : ℂ => c+z) :=
    (Homeomorph.addLeft c).measurableEmbedding
  have hb : (fun z : ℂ => c+z) ⁻¹' ball c R = ball 0 R := by
    ext z
    simp only [mem_preimage,mem_ball,dist_eq_norm,add_sub_cancel_left,sub_zero]
  have h := hm.setIntegral_preimage_emb he q (ball c R)
  rw [hb] at h
  exact h.symm

lemma translated_disk_green {P Q : ℂ → ℝ}
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    planarFormIntegral P Q (unitCircleParam c R) =
      ∫ z in ball c R, (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I := by
  rw [planarFormIntegral_circle_translate]
  have hPc : ContDiff ℝ ∞ (fun z => P (c+z)) := hP.comp (contDiff_const.add contDiff_id)
  have hQc : ContDiff ℝ ∞ (fun z => Q (c+z)) := hQ.comp (contDiff_const.add contDiff_id)
  rw [roundDiskGreen hPc hQc hR,integral_translated_ball c R
    (fun z => (fderiv ℝ Q z) 1 - (fderiv ℝ P z) Complex.I)]
  apply setIntegral_congr_fun isOpen_ball.measurableSet
  intro z _
  dsimp only
  rw [fderiv_comp_add_left,fderiv_comp_add_left]

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Transfer_FiniteHoleCore
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual compact region on which a finite-hole differential form
must be retained, including its outer and circular boundary curves. -/
open Set Function Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

lemma finite_hole_core_closed (H : ℂ ≃ₜ ℂ) {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    IsClosed (closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)) :=
  isClosed_closure.sdiff (isOpen_iUnion fun _ => isOpen_ball)

lemma jordan_boundary_mem_finite_hole_core {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ}
    (hγ : RegularJordanParametrization H γ) {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ)
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H) (t : ℝ) :
    γ t ∈ closure (jordanInterior H) \ ⋃ i, ball (c i) (r i) := by
  refine ⟨(hγ.mem_frontier t).1,?_⟩
  intro hm
  obtain ⟨i,hi⟩ := mem_iUnion.mp hm
  have hiJ := hin i (ball_subset_closedBall hi)
  exact (hγ.mem_frontier t).2 ((jordanInterior_isOpen H).interior_eq.symm ▸ hiJ)

lemma circle_mem_finite_hole_core (H : ℂ ≃ₜ ℂ) {n : ℕ}
    (c : Fin n → ℂ) (r : Fin n → ℝ) (hr : ∀ i, 0 < r i)
    (hd : Pairwise (Disjoint on fun i => closedBall (c i) (r i)))
    (hin : ∀ i, closedBall (c i) (r i) ⊆ jordanInterior H) (i : Fin n) (t : ℝ) :
    unitCircleParam (c i) (r i) t ∈ closure (jordanInterior H) \ ⋃ j, ball (c j) (r j) := by
  have hs : unitCircleParam (c i) (r i) t ∈ sphere (c i) (r i) := by
    simpa only [unitCircleParam,abs_of_pos (hr i)] using
      circleMap_mem_sphere' (c i) (r i) (2*Real.pi*t)
  have hc : unitCircleParam (c i) (r i) t ∈ closedBall (c i) (r i) :=
    sphere_subset_closedBall hs
  refine ⟨subset_closure (hin i hc),?_⟩
  intro hm
  obtain ⟨j,hj⟩ := mem_iUnion.mp hm
  by_cases hij : i = j
  · subst j
    have hdist : dist (unitCircleParam (c i) (r i) t) (c i) = r i := hs
    exact (not_lt_of_ge hdist.ge) hj
  · exact Set.disjoint_left.mp (hd hij) hc (ball_subset_closedBall hj)

end CircleDomainRigidity

end

end OAI
end

section
-- module Solutions.Q146_CD.CircleDomains_Topology_FiniteCircleGreenProof
attribute [-instance] _root_.ContinuousMap.measurableSpace _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Discharge of the signed finite-round-hole Green input. The sign is
chosen from the outer Jordan circuit before the holes or the form. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff BigOperators
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma unorientedFiniteCircleGreenFormula_oai : UnorientedFiniteCircleGreenFormula := by
  intro H γ hγ
  obtain ⟨ε,hε,hgreen⟩ := regular_jordan_green hγ
  refine ⟨ε,hε,?_⟩
  intro n c r hr hd hin O hO hsub P Q hP hQ
  let K := closure (jordanInterior H) \ ⋃ i, ball (c i) (r i)
  obtain ⟨p,hp,hep,_⟩ := exists_smooth_collar_extension hO
    (finite_hole_core_closed H c r) hsub hP 0
  obtain ⟨q,hq,heq,_⟩ := exists_smooth_collar_extension hO
    (finite_hole_core_closed H c r) hsub hQ 0
  have houter : planarFormIntegral p q γ = planarFormIntegral P Q γ := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have ht := jordan_boundary_mem_finite_hole_core hγ c r hin t
    dsimp only
    rw [hep.self_of_nhdsSet ht,heq.self_of_nhdsSet ht]
  have hcircle (i : Fin n) :
      planarFormIntegral p q (unitCircleParam (c i) (r i)) =
        planarFormIntegral P Q (unitCircleParam (c i) (r i)) := by
    unfold planarFormIntegral
    apply intervalIntegral.integral_congr
    intro t _
    have ht := circle_mem_finite_hole_core H c r hr hd hin i t
    dsimp only
    rw [hep.self_of_nhdsSet ht,heq.self_of_nhdsSet ht]
  have hsum : (∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i))) =
      ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) :=
    Finset.sum_congr rfl (fun i _ => hcircle i)
  have hcurl : Continuous (fun z => (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I) :=
    ((hq.continuous_fderiv (by simp)).clm_apply continuous_const).sub
      ((hp.continuous_fderiv (by simp)).clm_apply continuous_const)
  calc
    ε * planarFormIntegral P Q γ - ∑ i, planarFormIntegral P Q (unitCircleParam (c i) (r i)) =
        ε * planarFormIntegral p q γ - ∑ i, planarFormIntegral p q (unitCircleParam (c i) (r i)) := by
      rw [houter,hsum]
    _ = ∫ z in jordanInterior H \ ⋃ i, closedBall (c i) (r i),
        (fderiv ℝ q z) 1 - (fderiv ℝ p z) Complex.I := by
      rw [hgreen p q hp hq]
      simp_rw [translated_disk_green hp hq _ (hr _)]
      exact integral_finite_round_holes H c r hd hin hcurl
    _ = _ := by
      apply setIntegral_congr_fun ((jordanInterior_isOpen H).measurableSet.diff
        (MeasurableSet.iUnion fun _ => isClosed_closedBall.measurableSet))
      intro z hz
      have hzK : z ∈ K := by
        refine ⟨subset_closure hz.1,?_⟩
        intro hm
        obtain ⟨i,hi⟩ := mem_iUnion.mp hm
        exact hz.2 (mem_iUnion.mpr ⟨i,ball_subset_closedBall hi⟩)
      have hpz := hep.filter_mono (nhds_le_nhdsSet hzK)
      have hqz := heq.filter_mono (nhds_le_nhdsSet hzK)
      dsimp only
      rw [hpz.fderiv_eq,hqz.fderiv_eq]

end CircleDomainRigidity

end

end OAI
end

theorem solution : type_of% @OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula_oai := @OAI.CircleDomainRigidity.unorientedFiniteCircleGreenFormula_oai
