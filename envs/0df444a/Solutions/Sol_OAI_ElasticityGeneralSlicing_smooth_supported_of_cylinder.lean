-- Prove2me | solution 1 for OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T11:19:19.458889+00:00
-- url     : https://prove2.me/submissions/ada84617-1392-470a-9469-96c14f2379a3

import Mathlib
import Definitions.Def_OAIQ6El005
import Theorems.Thm_OAI_ElasticityGeneralSlicing_cylinder_weak_slices
import Theorems.Thm_OAI_ElasticityPlanar_supported_parameter_inversion

section
-- module Solutions.OAIQ6_Elast.Elasticity_Extension
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open Set Filter Metric
open scoped Topology Manifold
namespace ElasticityBoundary
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma compact_smooth_cutoff {K U : Set E} (hK : IsCompact K) (hU : IsOpen U) (hKU : K⊆U) :
    ∃ χ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧ tsupport χ⊆U ∧
      (∀ᶠ x in 𝓝ˢ K, χ x=1) ∧ ∀ x, χ x∈Icc 0 1 := by
  obtain ⟨R,hR⟩ := hK.isBounded.subset_ball (0 : E)
  obtain ⟨V,hV,hKV,hVU⟩ := normal_exists_closure_subset hK.isClosed (hU.inter isOpen_ball)
    (show K⊆U∩ball (0 : E) R from fun x hx => ⟨hKU hx,hR hx⟩)
  obtain ⟨χ,hχ,hzero,hb⟩ := exists_contMDiffMap_one_nhds_of_subset_interior
    (𝓘(ℝ,E)) (n := (⊤ : ℕ∞)) hK.isClosed (by rwa [hV.interior_eq])
  have hs : tsupport (χ : E → ℝ)⊆closure V := by
    apply closure_mono
    intro x hx
    by_contra hn
    exact hx (hzero x hn)
  refine ⟨χ,χ.contMDiff.contDiff,?_,fun x hx => (hVU (hs hx)).1,hχ,hb⟩
  apply (isCompact_closedBall (0 : E) R).of_isClosed_subset (isClosed_tsupport χ)
  exact fun x hx => ball_subset_closedBall ((hVU (hs hx)).2)

end ElasticityBoundary

end
end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Parameters
attribute [-instance] _root_.OAI.ElasticityGeneralSlicing.cylinder_temperate _root_.OAI.ElasticityODE.instFactLeRealOfNat_solutions _root_.OAI.ElasticityPlanar.graphComplete
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityPlanar
open MeasureTheory TemperedDistribution Set
open scoped ENNReal SchwartzMap BigOperators LineDeriv Manifold
open ElasticityRegularity
variable {n : Type*} [Fintype n]

omit [Fintype n] in
lemma entryInjection_apply (i : n) (f : Hilbert n) : entryInjection i f=(f i : 𝓢'(ℂ,ℂ)) := rfl

lemma planarOperator_apply (a : n → n → ℂ → ℂ) (i : n) (f : Hilbert n) :
    planarOperator a i f=ElasticityPlanarDistribution.dbar (f i : 𝓢'(ℂ,ℂ))+
      ∑ j, smulLeftCLM ℂ (a i j) (f j : 𝓢'(ℂ,ℂ)) := by
  simp only [planarOperator,ContinuousLinearMap.comp_apply,add_apply,smul_apply,sum_apply,
    entryInjection_apply,LineDeriv.lineDerivOpCLM_apply,ElasticityPlanarDistribution.dbar]

end ElasticityPlanar

end

end OAI
end

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
lemma sliceLp_coe {u : P × ℂ → ℂ} {t : P}
    (h : MemLp (fun z => u (t,z)) 2 volume) :
    (sliceLp u t : ℂ → ℂ)=ᵐ[volume] fun z => u (t,z) := by
  simp only [sliceLp,dite_eq_left h]
  exact h.coeFn_toLp

end ElasticityGeneralSlicing

end

end OAI
end

section
-- module Solutions.OAIQ6_Elast.Elasticity_Supported
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

/- The exact extension proofs are reused from their canonical original module. -/

namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal LineDeriv Topology
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)

lemma tests_determine_supported (S : Set ℂ) (hS : IsCompact S) (u w : PL2)
    (hsu : ∀ᵐ z : ℂ, z∉S → u z=0) (hsw : ∀ᵐ z : ℂ, z∉S → w z=0)
    (he : ∀ φ : Test, (∫ z, φ z*w z)=(∫ z, testDbar φ z*u z)) :
    dbar (u : Dist)+(w : Dist)=0 := by
  obtain ⟨χ,hχ,hc,_,hχ1,_⟩ := ElasticityBoundary.compact_smooth_cutoff hS isOpen_univ (subset_univ S)
  ext φ
  let ψ : Test := ⟨fun z => (χ z : ℂ)*φ z,⟨
    (Complex.ofRealCLM.contDiff.comp hχ).mul (φ.smooth ⊤),hc.comp_left Complex.ofReal_zero |>.mul_right⟩⟩
  have hg (z : ℂ) (hz : z∈S) : (ψ : ℂ → ℂ)=ᶠ[𝓝 z] (φ : ℂ → ℂ) := by
    filter_upwards [hχ1.filter_mono (nhds_le_nhdsSet hz)] with y hy
    change (χ y : ℂ)*φ y=φ y
    simp only [hy,Complex.ofReal_one,one_mul]
  have hv (z : ℂ) (hz : z∈S) : ψ z=φ z := (hg z hz).eq_of_nhds
  have hd (z : ℂ) (hz : z∈S) : testDbar ψ z=schwartzDbar φ z := by
    change fderiv ℝ (ψ : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (ψ : ℂ → ℂ) z Complex.I=
      fderiv ℝ (φ : ℂ → ℂ) z 1+Complex.I*fderiv ℝ (φ : ℂ → ℂ) z Complex.I
    rw [(hg z hz).fderiv_eq]
  have h1 : (∫ z, ψ z*w z)=(∫ z, φ z*w z) := by
    apply integral_congr_ae
    filter_upwards [hsw] with z hz
    by_cases hm : z∈S
    · rw [hv z hm]
    · rw [hz hm,mul_zero,mul_zero]
  have h2 : (∫ z, testDbar ψ z*u z)=(∫ z, schwartzDbar φ z*u z) := by
    apply integral_congr_ae
    filter_upwards [hsu] with z hz
    by_cases hm : z∈S
    · rw [hd z hm]
    · rw [hz hm,mul_zero,mul_zero]
  have hh := h1.symm.trans ((he ψ).trans h2)
  have hh' : (w : Dist) φ=(u : Dist) (schwartzDbar φ) := by
    simpa only [Lp.toTemperedDistribution_apply,smul_eq_mul] using hh
  simp only [dbar,schwartzDbar,add_apply,smul_apply,
    TemperedDistribution.lineDerivOp_apply_apply,map_neg,zero_apply,smul_eq_mul] at *
  rw [hh',map_add,map_smul]
  ring

lemma supported_local_zero (S : Set ℂ) (u : PL2)
    (hsu : ∀ᵐ z : ℂ, z∉S → u z=0) : LocalEqual Sᶜ (u : Dist) 0 := by
  intro φ _ hs
  rw [Lp.toTemperedDistribution_apply]
  change (∫ z, φ z*u z)=0
  apply integral_eq_zero_of_ae
  filter_upwards [hsu] with z hz
  by_cases hm : z∈S
  · have hn : z∉tsupport (φ : ℂ → ℂ) := fun hh => hs hh hm
    simp only [image_eq_zero_of_notMem_tsupport hn,zero_mul,Pi.zero_apply]
  · simp only [hz hm,mul_zero,Pi.zero_apply]

omit [BorelSpace P] in
/-- Compact support passes through Fubini and through the chosen L2 representative. -/
lemma supported_slice (S : Set ℂ) (u : P × ℂ → ℂ)
    (hu : MemLp u 2 volume) (hs : ∀ᵐ q : P × ℂ, q.2∉S → u q=0) :
    ∀ᵐ t : P, ∀ᵐ z : ℂ, z∉S → sliceLp u t z=0 := by
  have hu' := memLp_two_slices (ν := (volume : Measure P)) (κ := (volume : Measure ℂ)) hu
  have hs' := Measure.ae_ae_of_ae_prod hs
  filter_upwards [hu',hs'] with t hut hst
  filter_upwards [sliceLp_coe hut,hst] with z hz hsz
  intro h
  rw [hz,hsz h]

/-- The slicing result is an actual global planar distribution equation,
not merely equality on a selected family of test functions. -/
theorem cylinder_supported_slices (S : Set ℂ) (hS : IsCompact S)
    (u w : Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : Integrable (u : P × ℂ → ℂ)) (hw : Integrable (w : P × ℂ → ℂ))
    (hsu : ∀ᵐ q : P × ℂ, q.2∉S → u q=0) (hsw : ∀ᵐ q : P × ℂ, q.2∉S → w q=0)
    (he : ∂_{((0:P),(1:ℂ))} (u : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u : 𝓢'(P × ℂ,ℂ))+(w : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P,
      dbar (sliceLp u t : Dist)+(sliceLp w t : Dist)=0 ∧
      LocalEqual Sᶜ (sliceLp u t : Dist) 0 := by
  have he' := cylinder_weak_slices u w hu hw he
  have hsu' := supported_slice S u (Lp.memLp u) hsu
  have hsw' := supported_slice S w (Lp.memLp w) hsw
  filter_upwards [he',hsu',hsw'] with t ht hut hwt
  refine ⟨tests_determine_supported S hS (sliceLp u t) (sliceLp w t) hut hwt ?_,
    supported_local_zero S (sliceLp u t) hut⟩
  intro φ
  convert ht.2.2 φ using 1
  · apply integral_congr_ae
    filter_upwards [sliceLp_coe ht.2.1] with z hz
    rw [hz]
  · apply integral_congr_ae
    filter_upwards [sliceLp_coe ht.1] with z hz
    rw [hz]

end ElasticityGeneralSlicing
namespace ElasticityGeneralSlicing
open Set MeasureTheory TemperedDistribution Filter
open scoped SchwartzMap ENNReal BigOperators Topology LineDeriv
open ElasticitySlicing
variable {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    [FiniteDimensional ℝ P] [MeasureSpace P] [BorelSpace P]
    [Measure.IsAddHaarMeasure (volume : Measure P)]
open ElasticityPlanar ElasticityRegularity
open ElasticityPlanarDistribution (Dist dbar)
variable {n : Type*} [Fintype n]

lemma sliced_coefficients (a : n → ℂ → ℂ) (ha : ∀ j,(a j).HasTemperateGrowth)
    (u : n → PL2) (w : PL2) (f : Test)
    (he : ∀ᵐ z : ℂ, w z=∑ j,a j z*u j z-f z) :
    (w : Dist)=∑ j,smulLeftCLM ℂ (a j) (u j : Dist)-(toSchwartz f : Dist) := by
  classical
  ext φ
  have hi (j : n) : Integrable (fun z => φ z*(a j z*u j z)) := by
    have hh := ((SchwartzMap.smulLeftCLM ℂ (a j) φ).memLp 2 volume).integrable_mul (Lp.memLp (u j))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    simp only [Pi.mul_apply,SchwartzMap.smulLeftCLM_apply_apply (ha j),smul_eq_mul]
    ring
  have hf : Integrable (fun z => φ z*f z) :=
    (φ.memLp 2 volume).integrable_mul ((toSchwartz f).memLp 2 volume)
  have he' : (fun z => φ z*w z)=ᵐ[volume] fun z => (∑ j,φ z*(a j z*u j z))-φ z*f z := by
    filter_upwards [he] with z hz
    simp only [hz,mul_sub,Finset.mul_sum]
  simp only [Lp.toTemperedDistribution_apply,sub_apply,sum_apply,
    smulLeftCLM_apply_apply,SchwartzMap.coe_apply,smul_eq_mul]
  rw [integral_congr_ae he',integral_sub (integrable_finsetSum _ (fun j _ => hi j)) hf,
    integral_finsetSum _ (fun j _ => hi j)]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  exact Eventually.of_forall (fun z => by
    change φ z*(a j z*u j z)=((SchwartzMap.smulLeftCLM ℂ (a j)) φ) z*u j z
    rw [SchwartzMap.smulLeftCLM_apply_apply (ha j)]
    simp only [smul_eq_mul]
    ring)

/-- Genuine cylinder weak solutions give supported weak planar solutions on a
single full-measure, hence dense, set of transverse parameters. -/
theorem coupled_slice_equations (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∀ᵐ t : P, ∀ i,
      planarOperator (fun i j z => a i j (t,z)) i
        (WithLp.toLp 2 (fun j => sliceLp (u j) t))=
        (toSchwartz ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
          compact_slice hK (f i) (hfs i) t⟩⟩ : Dist) ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
  classical
  have hsl : ∀ᵐ t : P, ∀ i,
      dbar (sliceLp (u i) t : Dist)+(sliceLp (w i) t : Dist)=0 ∧
      LocalEqual Sᶜ (sliceLp (u i) t : Dist) 0 := by
    rw [ae_all_iff]
    exact fun i => cylinder_supported_slices S hS (u i) (w i) (hu i) (hw i) (hsu i) (hsw i) (he i)
  have huc : ∀ᵐ t : P,∀ i, MemLp (fun z => u i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (u i))
  have hwc : ∀ᵐ t : P,∀ i, MemLp (fun z => w i (t,z)) 2 volume := by
    rw [ae_all_iff]
    exact fun i => memLp_two_slices (Lp.memLp (w i))
  have hcc : ∀ᵐ t : P,∀ i,∀ᵐ z : ℂ,w i (t,z)=∑ j,a i j (t,z)*u j (t,z)-f i (t,z) := by
    rw [ae_all_iff]
    exact fun i => Measure.ae_ae_of_ae_prod (hc i)
  filter_upwards [hsl,huc,hwc,hcc] with t ht hut hwt hct
  intro i
  refine ⟨?_,(ht i).2⟩
  let ft : Test := ⟨fun z => f i (t,z),⟨(hf i).comp (contDiff_const.prodMk contDiff_id),
    compact_slice hK (f i) (hfs i) t⟩⟩
  have hac (j : n) : (fun z => a i j (t,z)).HasTemperateGrowth :=
    (compact_slice hK (a i j) (hs i j) t).hasTemperateGrowth
      ((ha i j).comp (contDiff_const.prodMk contDiff_id))
  have hrel : ∀ᵐ z : ℂ,sliceLp (w i) t z=∑ j,a i j (t,z)*sliceLp (u j) t z-ft z := by
    have huall : ∀ᵐ z : ℂ,∀ j,sliceLp (u j) t z=u j (t,z) := by
      rw [ae_all_iff]
      exact fun j => sliceLp_coe (hut j)
    filter_upwards [sliceLp_coe (hwt i),huall,hct i] with z hwz huz hcz
    simpa only [hwz,huz] using hcz
  have hh := sliced_coefficients (fun j z => a i j (t,z)) hac
    (fun j => sliceLp (u j) t) (sliceLp (w i) t) ft hrel
  have hz := (ht i).1
  rw [hh] at hz
  rw [planarOperator_apply]
  change dbar (sliceLp (u i) t : Dist)+∑ j,smulLeftCLM ℂ (fun z => a i j (t,z))
    (sliceLp (u j) t : Dist)=(toSchwartz ft : Dist)
  exact sub_eq_zero.mp (by simpa only [add_sub_assoc] using hz)

/-- Completion of the almost-every-plane to every-plane step. No smooth weak
representative or nowhere-exceptional slicing has been assumed. -/
theorem smooth_supported_of_cylinder_oai (S K : Set ℂ) (hS : IsCompact S) (hK : IsCompact K)
    (a : n → n → P × ℂ → ℂ) (ha : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (hs : ∀ i j t z,z∉K → a i j (t,z)=0)
    (f : n → P × ℂ → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i t z,z∉K → f i (t,z)=0)
    (u w : n → Lp ℂ 2 (volume : Measure (P × ℂ)))
    (hu : ∀ i,Integrable (u i : P × ℂ → ℂ)) (hw : ∀ i,Integrable (w i : P × ℂ → ℂ))
    (hsu : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → u i q=0)
    (hsw : ∀ i,∀ᵐ q : P × ℂ,q.2∉S → w i q=0)
    (hc : ∀ i,∀ᵐ q : P × ℂ,w i q=∑ j,a i j q*u j q-f i q)
    (he : ∀ i, ∂_{((0:P),(1:ℂ))} (u i : 𝓢'(P × ℂ,ℂ))+
      Complex.I • ∂_{((0:P),Complex.I)} (u i : 𝓢'(P × ℂ,ℂ))+(w i : 𝓢'(P × ℂ,ℂ))=0) :
    ∃ v : P → n → Test,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (fun q : P × ℂ => v q.1 i q.2)) ∧
      (∀ t i,tsupport (v t i : ℂ → ℂ)⊆S) ∧
      ∀ t i z,schwartzDbar (toSchwartz (v t i)) z+∑ j,a i j (t,z)*v t j z=f i (t,z) := by
  have hh := coupled_slice_equations S K hS hK a ha hs f hf hfs u w hu hw hsu hsw hc he
  exact supported_parameter_inversion hS hK a ha hs f hf hfs (Measure.dense_of_ae hh)
    (fun t ht => ⟨WithLp.toLp 2 (fun i => sliceLp (u i) t),ht⟩)
end ElasticityGeneralSlicing

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder_oai.{u_1, u_2} := @OAI.ElasticityGeneralSlicing.smooth_supported_of_cylinder_oai.{u_1, u_2}
