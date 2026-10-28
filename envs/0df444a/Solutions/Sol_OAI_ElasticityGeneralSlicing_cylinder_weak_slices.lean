-- Prove2me | solution 1 for OAI.ElasticityGeneralSlicing.cylinder_weak_slices
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:54:29.896072+00:00
-- url     : https://prove2.me/submissions/f3d4dbb9-7e4b-47fc-95dd-4dbe2fc8f802

import Mathlib
import Definitions.Def_OAIQ6El000
import Definitions.Def_OAIQ6El002

section
-- module Solutions.OAIQ6_Elast.Elasticity_WeakLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticitySlicing
/-! Measure-theoretic core of transverse slicing: a single exceptional null
set for all planar tests, obtained using the separable L2 value/derivative graph,
not an invalid interchange of an uncountable intersection with almost-everywhere. -/
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {T E F : Type*} [MeasurableSpace T] {μ : Measure T}
    [TopologicalSpace E] [SecondCountableTopology E]
    [TopologicalSpace F] [T2Space F] [Zero F]

lemma ae_all_on_of_continuous (s : Set E) (f : T → E → F)
    (hc : ∀ᵐ t ∂μ, Continuous (f t))
    (hz : ∀ x∈s, ∀ᵐ t ∂μ, f t x=0) :
    ∀ᵐ t ∂μ, ∀ x∈s, f t x=0 := by
  obtain ⟨d,hd,hdd⟩ := TopologicalSpace.exists_countable_dense s
  have hz' : ∀ᵐ t ∂μ, ∀ x∈d, f t (x:E)=0 := by
    rw [ae_ball_iff hd]
    exact fun x _ => hz x x.property
  filter_upwards [hc,hz'] with t hct hzt
  have hs : closure d ⊆ {x : s | f t x=0} :=
    closure_minimal hzt (isClosed_eq (hct.comp continuous_subtype_val) continuous_const)
  intro x hx
  exact hs (hdd ⟨x,hx⟩)

variable {A B G : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [NormedAddCommGroup G]
    {ν : Measure A} {κ : Measure B} [SFinite ν] [SFinite κ]

/-- An honest L2 function on the cylinder has L2 planar slices a.e. -/
lemma memLp_two_slices {u : A × B → G} (hu : MemLp u 2 (ν.prod κ)) :
    ∀ᵐ t ∂ν, MemLp (fun z => u (t,z)) 2 κ := by
  have hn := hu.integrable_norm_rpow (by norm_num) (by norm_num)
  filter_upwards [hu.aestronglyMeasurable.prodMk_left,hn.prod_right_ae] with t ht hnt
  exact (integrable_norm_rpow_iff ht (by norm_num : (2:ℝ≥0∞)≠0)
    (by norm_num : (2:ℝ≥0∞)≠⊤)).mp hnt

end ElasticitySlicing
namespace ElasticityGeneralSlicing
/-! Actual transverse slicing of weak planar equations. All planar tests share
one exceptional null set. No uncountable a.e. intersection is used. -/
open Set MeasureTheory Filter
open scoped SchwartzMap ENNReal InnerProductSpace
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma slicePair_continuous (u w : P × ℂ → ℂ) (t : P) :
    Continuous (slicePair u w t) := by
  exact (continuous_fst.inner continuous_const).sub (continuous_snd.inner continuous_const)

lemma L2_test_integral {w : ℂ → ℂ} (hw : MemLp w 2 volume) (φ : Test) :
    inner ℂ (L2 (cj φ)) (hw.toLp w)=∫ z, φ z*w z := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(toSchwartz (cj φ)).coeFn_toLp 2 volume,hw.coeFn_toLp] with z hz hwz
  change (L2 (cj φ) : ℂ → ℂ) z=cj φ z at hz
  rw [hz,hwz]
  simp only [cj_apply,RCLike.inner_apply',starRingEnd_apply,star_star,mul_comm]

omit [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma slicePair_graph {u w : P × ℂ → ℂ} {t : P}
    (hu : MemLp (fun z => u (t,z)) 2 volume)
    (hw : MemLp (fun z => w (t,z)) 2 volume) (φ : Test) :
    slicePair u w t (testGraph φ)=
      (∫ z, φ z*w (t,z))-(∫ z, testDbar φ z*u (t,z)) := by
  simp only [slicePair,testGraph,sliceLp,dite_eq_left hu,dite_eq_left hw,L2_test_integral]

omit [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma test_mul_integrable {w : P × ℂ → ℂ} (hw : Integrable w) (φ : Test) :
    Integrable (fun q : P × ℂ => φ q.2*w q) := by
  apply hw.bdd_mul ((toSchwartz φ).continuous.comp continuous_snd).aestronglyMeasurable
  exact Eventually.of_forall (fun q => (toSchwartz φ).norm_le_seminorm ℝ q.2)

/-- Fubini plus the fundamental lemma first gives a null set for one test. -/
lemma single_test_slice {u w : P × ℂ → ℂ}
    (hu : Integrable u) (hw : Integrable w) (φ : Test)
    (he : ∀ (η : P → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0) :
    ∀ᵐ t : P, ∫ z : ℂ, φ z*w (t,z)-testDbar φ z*u (t,z)=0 := by
  have hi := (test_mul_integrable hw φ).sub (test_mul_integrable hu (testDbar φ))
  apply ae_eq_zero_of_integral_contDiff_smul_eq_zero hi.integral_prod_left.locallyIntegrable
  intro η hη hcη
  obtain ⟨C,hC⟩ := (hcη.isCompact_range hη.continuous).isBounded.exists_norm_le
  have hηi : Integrable (fun q : P × ℂ => η q.1 •
      (φ q.2*w q-testDbar φ q.2*u q)) :=
    hi.bdd_smul C (hη.continuous.comp continuous_fst).aestronglyMeasurable
      (Eventually.of_forall (fun q => hC (η q.1) (mem_range_self q.1)))
  have hh := he η hη hcη
  change (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q)
    ∂(volume : Measure P).prod (volume : Measure ℂ))=0 at hh
  rw [integral_prod _ hηi] at hh
  simpa only [integral_smul,Pi.sub_apply] using hh

/-- The weak cylinder equation genuinely determines the planar weak equation
on a single full-measure subset of transverse parameters. -/
theorem weak_slice_from_product_tests {u w : P × ℂ → ℂ}
    (hu : Integrable u) (hw : Integrable w)
    (hu2 : MemLp u 2 volume) (hw2 : MemLp w 2 volume)
    (he : ∀ (η : P → ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      ∀ φ : Test, (∫ q : P × ℂ,
        η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0) :
    ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
      MemLp (fun z => w (t,z)) 2 volume ∧
      ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z)) := by
  have : Fact ((2 : ℝ≥0∞)≠⊤) := ⟨by norm_num⟩
  have hu' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hu2
  have hw' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hw2
  have hg : ∀ q∈range testGraph, ∀ᵐ t : P, slicePair u w t q=0 := by
    rintro q ⟨φ,rfl⟩
    have hzero := single_test_slice hu hw φ (fun η hη hcη => he η hη hcη φ)
    filter_upwards [hu',hw',hzero,(test_mul_integrable hw φ).prod_right_ae,
      (test_mul_integrable hu (testDbar φ)).prod_right_ae] with t hut hwt hzt h1 h2
    rw [slicePair_graph hut hwt,← integral_sub h1 h2]
    exact hzt
  have hcount := ae_all_on_of_continuous (range testGraph) (slicePair u w)
    (Eventually.of_forall (slicePair_continuous u w)) hg
  filter_upwards [hu',hw',hcount] with t hut hwt ht
  refine ⟨hut,hwt,fun φ => ?_⟩
  exact sub_eq_zero.mp ((slicePair_graph hut hwt φ).symm.trans (ht _ (mem_range_self φ)))

end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_apply (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) (q : P × ℂ) :
    productTest η hη hcη φ q=(η q.1 : ℂ)*φ q.2 := rfl

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_deriv (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) (v : ℂ) :
    ∂_{((0:P),v)} (productTest η hη hcη φ)=productTest η hη hcη (d v φ) := by
  ext q
  change fderiv ℝ (fun q : P × ℂ => (η q.1 : ℂ)*φ q.2) q (0,v)=
    (η q.1 : ℂ)*fderiv ℝ (φ : ℂ → ℂ) q.2 v
  have hηd := (Complex.ofRealCLM.contDiff.comp hη).differentiable (by simp)
  have hφd := (smooth φ).differentiable (by simp)
  have ha : DifferentiableAt ℝ (fun q : P × ℂ => (η q.1 : ℂ)) q :=
    (hηd.comp differentiable_fst) q
  have hb : DifferentiableAt ℝ (fun q : P × ℂ => φ q.2) q :=
    (hφd.comp differentiable_snd) q
  rw [fderiv_fun_mul ha hb]
  have hfa := fderiv_comp q (hηd q.1) (differentiableAt_fst (p := q))
  have hfb := fderiv_comp q (hφd q.2) (differentiableAt_snd (p := q))
  change fderiv ℝ (fun q : P × ℂ => (η q.1 : ℂ)) q = _ at hfa
  change fderiv ℝ (fun q : P × ℂ => φ q.2) q = _ at hfb
  rw [hfa,hfb]
  simp [fderiv_fst,fderiv_snd,smul_eq_mul]

omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_add (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ ψ : Test) :
    productTest η hη hcη (φ+ψ)=productTest η hη hcη φ+productTest η hη hcη ψ := by
  ext q
  change (η q.1 : ℂ)*(φ q.2+ψ q.2)=_
  exact mul_add _ _ _
omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_smul (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (c : ℂ) (φ : Test) :
    productTest η hη hcη (c • φ)=c • productTest η hη hcη φ := by
  ext q
  change (η q.1 : ℂ)*(c*φ q.2)=c*((η q.1 : ℂ)*φ q.2)
  ring
omit [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
  [Measure.IsAddHaarMeasure (volume : Measure P)] in
lemma productTest_dbar (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (φ : Test) :
    ∂_{((0:P),(1:ℂ))} (productTest η hη hcη φ)+
      Complex.I • ∂_{((0:P),Complex.I)} (productTest η hη hcη φ)=
      productTest η hη hcη (testDbar φ) := by
  simp only [testDbar,productTest_add,productTest_smul,productTest_deriv]

/-- The product-test premise of slicing is not an axiom: it follows from the
actual distributional cylinder equation by an exact directional derivative. -/
theorem cylinder_product_tests (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0)
    (η : P → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (φ : Test) :
    (∫ q : P × ℂ, η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=0 := by
  have hh := congrArg (fun D : 𝓢'(P × ℂ,ℂ) => D (productTest η hη hcη φ)) he
  have htest : (w : 𝓢'(P × ℂ,ℂ)) (productTest η hη hcη φ)=
      (u : 𝓢'(P × ℂ,ℂ)) (productTest η hη hcη (testDbar φ)) := by
    rw [← productTest_dbar]
    simp only [add_apply,smul_apply,TemperedDistribution.lineDerivOp_apply_apply,
      map_neg,zero_apply,smul_eq_mul] at hh
    simp only [map_add,map_smul,smul_eq_mul]
    linear_combination hh
  simp only [Lp.toTemperedDistribution_apply,productTest_apply,smul_eq_mul] at htest
  obtain ⟨C,hC⟩ := (hcη.isCompact_range hη.continuous).isBounded.exists_norm_le
  have hi (f : P × ℂ → ℂ) (hf : Integrable f) (ψ : Test) :
      Integrable (fun q : P × ℂ => (η q.1 : ℂ)*(ψ q.2*f q)) := by
    apply (test_mul_integrable hf ψ).bdd_mul (c := C)
      (Complex.continuous_ofReal.comp (hη.continuous.comp continuous_fst)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun q => by simpa only [Function.comp_apply,Complex.norm_real] using hC (η q.1) (mem_range_self q.1))
  have hrew : (fun q : P × ℂ => η q.1 • (φ q.2*w q-testDbar φ q.2*u q))=
      (fun q => (η q.1 : ℂ)*(φ q.2*w q))-(fun q => (η q.1 : ℂ)*(testDbar φ q.2*u q)) := by
    funext q
    simp only [Pi.sub_apply,Complex.real_smul,mul_sub]
  rw [hrew]
  change (∫ q : P × ℂ, (η q.1 : ℂ)*(φ q.2*w q)-(η q.1 : ℂ)*(testDbar φ q.2*u q))=0
  rw [integral_sub (hi w hw φ) (hi u hu (testDbar φ)),sub_eq_zero]
  simpa only [mul_assoc] using htest

/-- Actual weak distribution solutions on the cylinder slice to planar
solutions for every compact smooth test on one full-measure parameter set. -/
theorem cylinder_weak_slices_oai (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, MemLp (fun z => u (t,z)) 2 volume ∧
      MemLp (fun z => w (t,z)) 2 volume ∧
      ∀ φ : Test, (∫ z, φ z*w (t,z))=(∫ z, testDbar φ z*u (t,z)) :=
  weak_slice_from_product_tests hu hw (Lp.memLp u) (Lp.memLp w)
    (cylinder_product_tests u w hu hw he)

end ElasticityGeneralSlicing

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.ElasticityGeneralSlicing.cylinder_weak_slices_oai.{u_1} := @OAI.ElasticityGeneralSlicing.cylinder_weak_slices_oai.{u_1}
