-- Prove2me | solution 1 for OAI.ElasticityCoordinates.planar_smooth_representative
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:53:39.643763+00:00
-- url     : https://prove2.me/submissions/356be8ef-c6cb-4e59-9f9b-5f6f9ed387ec

import Mathlib
import Definitions.Def_OAIQ6El002
import Definitions.Def_OAIQ6El003
import Theorems.Thm_OAI_ElasticityGeneralSlicing_smooth_cylinder_representative

section
-- module Solutions.OAIQ6_Elast.Elasticity_Smoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace ElasticityCoordinates
/-! Actual Haar/L2 and tempered-distribution change of linear coordinates.
The Jacobian is derived from Haar uniqueness, not silently set equal to one. -/
open MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal NNReal LineDeriv
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]

variable [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_apply (L : F ≃L[ℝ] E) (D : 𝓢'(E,ℂ)) (φ : 𝓢(F,ℂ)) :
    linearPull L D φ=D (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm φ) := rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_add (L : F ≃L[ℝ] E) (D T : 𝓢'(E,ℂ)) :
    linearPull L (D+T)=linearPull L D+linearPull L T := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_smul (L : F ≃L[ℝ] E) (c : ℂ) (D : 𝓢'(E,ℂ)) :
    linearPull L (c • D)=c • linearPull L D := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_zero (L : F ≃L[ℝ] E) : linearPull L (0 : 𝓢'(E,ℂ))=0 := by ext φ; rfl
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma linearPull_deriv (L : F ≃L[ℝ] E) (v : F) (D : 𝓢'(E,ℂ)) :
    linearPull L (∂_{L v} D)=∂_{v} (linearPull L D) := by
  ext φ
  simp only [linearPull_apply,TemperedDistribution.lineDerivOp_apply_apply]
  congr 1
  rw [SchwartzMap.lineDerivOp_compCLMOfContinuousLinearEquiv,
    ContinuousLinearEquiv.symm_apply_apply,map_neg]

omit [FiniteDimensional ℝ F] [(volume : Measure E).HasTemperateGrowth] [(volume : Measure F).HasTemperateGrowth] in
lemma pullLp_coe (L : F ≃L[ℝ] E) (u : Lp ℂ 2 (volume : Measure E)) :
    (pullLp L u : F → ℂ)=ᵐ[volume] (u ∘ L) := (memLp_linear L (Lp.memLp u)).coeFn_toLp

omit [FiniteDimensional ℝ F] in
lemma pullLp_distribution (L : F ≃L[ℝ] E) (c : ℝ≥0)
    (hc : (volume : Measure F).map L=c • (volume : Measure E))
    (u : Lp ℂ 2 (volume : Measure E)) :
    (pullLp L u : 𝓢'(F,ℂ))=(c : ℂ) • linearPull L (u : 𝓢'(E,ℂ)) := by
  ext φ
  simp only [Lp.toTemperedDistribution_apply,smul_apply,linearPull_apply,smul_eq_mul]
  have he : (∫ q : F,φ q*pullLp L u q)=∫ q : F,φ q*u (L q) := by
    apply integral_congr_ae
    filter_upwards [pullLp_coe L u] with q hq
    rw [hq]
    rfl
  rw [he]
  have hh := integral_map_equiv (μ := (volume : Measure F)) (L.toHomeomorph.toMeasurableEquiv)
    (fun x : E => φ (L.symm x)*u x)
  change (∫ x : E, φ (L.symm x)*u x ∂((volume : Measure F).map L))=
    ∫ q : F, φ (L.symm (L q))*u (L q) at hh
  rw [hc,integral_smul_nnreal_measure] at hh
  simpa only [ContinuousLinearEquiv.symm_apply_apply,NNReal.smul_def,Complex.real_smul,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply,Function.comp_apply] using hh.symm

omit [FiniteDimensional ℝ F] in
lemma pullLp_equation (L : F ≃L[ℝ] E) (v w : F)
    (u f : Lp ℂ 2 (volume : Measure E))
    (he : ∂_{L v} (u : 𝓢'(E,ℂ))+Complex.I • ∂_{L w} (u : 𝓢'(E,ℂ))+
      (f : 𝓢'(E,ℂ))=0) :
    ∂_{v} (pullLp L u : 𝓢'(F,ℂ))+Complex.I • ∂_{w} (pullLp L u : 𝓢'(F,ℂ))+
      (pullLp L f : 𝓢'(F,ℂ))=0 := by
  obtain ⟨c,_,hc⟩ := linear_haar L
  have hh := congrArg (linearPull L) he
  simp only [linearPull_add,linearPull_smul,linearPull_deriv,linearPull_zero] at hh
  rw [pullLp_distribution L c hc u,pullLp_distribution L c hc f]
  simp only [LineDeriv.lineDerivOp_smul]
  rw [smul_comm Complex.I (c : ℂ),← smul_add,← smul_add,hh,smul_zero]

end ElasticityCoordinates
namespace ElasticityCoordinates
open MeasureTheory Set
open scoped ENNReal NNReal
variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]

lemma ae_linear (L : F ≃L[ℝ] E) {p : E → Prop} (hp : ∀ᵐ x,p x) : ∀ᵐ q,p (L q) := by
  obtain ⟨c,_hc,hm⟩ := linear_haar L
  have hh : ∀ᵐ x ∂((volume : Measure F).map L),p x := by
    rw [hm]
    exact Measure.ae_smul_measure hp c
  exact ae_of_ae_map L.continuous.measurable.aemeasurable hh

omit [FiniteDimensional ℝ E] [NormedSpace ℝ E] in
lemma lp_integrable_supported {K : Set E} (hK : IsCompact K)
    (u : Lp ℂ 2 (volume : Measure E)) (hu : ∀ᵐ x,x∉K → u x=0) : Integrable (u : E → ℂ) := by
  have hres : MemLp (u : E → ℂ) 2 (volume.restrict K) := (Lp.memLp u).restrict K
  have : IsFiniteMeasure (volume.restrict K) := ⟨by simpa only [Measure.restrict_apply_univ] using hK.measure_lt_top (μ := (volume : Measure E))⟩
  have hi : IntegrableOn (u : E → ℂ) K := hres.integrable (by norm_num)
  have he : K.indicator (u : E → ℂ)=ᵐ[volume] (u : E → ℂ) := by
    filter_upwards [hu] with x hx
    by_cases h : x∈K
    · exact indicator_of_mem h _
    · simp only [indicator_of_notMem h,hx h]
  exact (hi.integrable_indicator hK.measurableSet).congr he
end ElasticityCoordinates
namespace ElasticityCoordinates
open Set MeasureTheory TemperedDistribution
open scoped SchwartzMap ENNReal LineDeriv
variable {E P n : Type*} [Fintype n]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [NormedAddCommGroup P] [InnerProductSpace ℝ P] [FiniteDimensional ℝ P]
  [MeasureSpace P] [BorelSpace P] [Measure.IsAddHaarMeasure (volume : Measure P)]

/-- Smoothness of an actual compactly supported matrix transport weak solution
in arbitrary linear transverse coordinates. The representative equals the
original L2 function almost everywhere; no exceptional planes remain. -/
theorem planar_smooth_representative_oai (L : (P × ℂ) ≃L[ℝ] E)
    (T K : Set E) (hT : IsCompact T) (hK : IsCompact K)
    (a : n → n → E → ℂ) (ha : ∀ i j,ContDiff ℝ (⊤ : ℕ∞) (a i j))
    (has : ∀ i j x,x∉K → a i j x=0)
    (f : n → E → ℂ) (hf : ∀ i,ContDiff ℝ (⊤ : ℕ∞) (f i))
    (hfs : ∀ i x,x∉K → f i x=0)
    (u w : n → Lp ℂ 2 (volume : Measure E))
    (hus : ∀ i,∀ᵐ x,x∉T → u i x=0) (hws : ∀ i,∀ᵐ x,x∉T → w i x=0)
    (hc : ∀ i,∀ᵐ x,w i x=∑ j,a i j x*u j x-f i x)
    (he : ∀ i,∂_{L (0,1)} (u i : 𝓢'(E,ℂ))+
      Complex.I • ∂_{L (0,Complex.I)} (u i : 𝓢'(E,ℂ))+(w i : 𝓢'(E,ℂ))=0) :
    ∃ v : n → E → ℂ,(∀ i,ContDiff ℝ (⊤ : ℕ∞) (v i)) ∧
      (∀ i,(u i : E → ℂ)=ᵐ[volume] v i) := by
  classical
  have : (volume : Measure (P × ℂ)).HasTemperateGrowth := by
    change (volume.prod volume).HasTemperateGrowth
    infer_instance
  have : Measure.IsAddHaarMeasure (volume : Measure (P × ℂ)) := by
    change Measure.IsAddHaarMeasure (volume.prod volume)
    infer_instance
  let S := (fun x : E => (L.symm x).2) '' T
  let Q := (fun x : E => (L.symm x).2) '' K
  have hS : IsCompact S := hT.image (continuous_snd.comp L.symm.continuous)
  have hQ : IsCompact Q := hK.image (continuous_snd.comp L.symm.continuous)
  let U := fun i => pullLp L (u i)
  let W := fun i => pullLp L (w i)
  have hsU (i) : ∀ᵐ q : P × ℂ,q.2∉S → U i q=0 := by
    filter_upwards [pullLp_coe L (u i),ae_linear L (hus i)] with q hq hqu
    intro hqs
    rw [hq]
    apply hqu
    intro hqt
    exact hqs ⟨L q,hqt,by simp⟩
  have hsW (i) : ∀ᵐ q : P × ℂ,q.2∉S → W i q=0 := by
    filter_upwards [pullLp_coe L (w i),ae_linear L (hws i)] with q hq hqw
    intro hqs
    rw [hq]
    apply hqw
    intro hqt
    exact hqs ⟨L q,hqt,by simp⟩
  have compactU (i) : ∀ᵐ q : P × ℂ,q∉L.symm '' T → U i q=0 := by
    filter_upwards [pullLp_coe L (u i),ae_linear L (hus i)] with q hq hqu
    intro hqs
    rw [hq]
    exact hqu (fun hh => hqs ⟨L q,hh,L.symm_apply_apply q⟩)
  have compactW (i) : ∀ᵐ q : P × ℂ,q∉L.symm '' T → W i q=0 := by
    filter_upwards [pullLp_coe L (w i),ae_linear L (hws i)] with q hq hqw
    intro hqs
    rw [hq]
    exact hqw (fun hh => hqs ⟨L q,hh,L.symm_apply_apply q⟩)
  have huI (i) := lp_integrable_supported (hT.image L.symm.continuous) (U i) (compactU i)
  have hwI (i) := lp_integrable_supported (hT.image L.symm.continuous) (W i) (compactW i)
  have hcc (i) : ∀ᵐ q : P × ℂ,W i q=∑ j,a i j (L q)*U j q-f i (L q) := by
    have huall : ∀ᵐ q : P × ℂ,∀ j,U j q=u j (L q) := by
      rw [ae_all_iff]
      exact fun j => pullLp_coe L (u j)
    filter_upwards [pullLp_coe L (w i),huall,ae_linear L (hc i)] with q hwq huq hq
    change W i q=w i (L q) at hwq
    rw [hwq]
    simp_rw [huq]
    exact hq
  obtain ⟨v,hv,_hvs,_hve,hvu⟩ := ElasticityGeneralSlicing.smooth_cylinder_representative S Q hS hQ
    (fun i j q => a i j (L q)) (fun i j => (ha i j).comp L.contDiff)
    (fun i j t z hz => has i j _ (fun hh => hz ⟨L (t,z),hh,by simp⟩))
    (fun i q => f i (L q)) (fun i => (hf i).comp L.contDiff)
    (fun i t z hz => hfs i _ (fun hh => hz ⟨L (t,z),hh,by simp⟩))
    U W huI hwI hsU hsW hcc (fun i => pullLp_equation L (0,1) (0,Complex.I) (u i) (w i) (he i))
  refine ⟨fun i x => v (L.symm x).1 i (L.symm x).2,
    fun i => (hv i).comp L.symm.contDiff,fun i => ?_⟩
  have hq : ∀ᵐ q : P × ℂ,u i (L q)=v q.1 i q.2 := by
    filter_upwards [pullLp_coe L (u i),hvu i] with q huq hvq
    exact huq.symm.trans hvq
  have hh := ae_linear L.symm hq
  filter_upwards [hh] with x hx
  simpa only [L.apply_symm_apply] using hx

end ElasticityCoordinates
open Set Filter TemperedDistribution
open scoped SchwartzMap LineDeriv BigOperators Topology

end

end OAI
end

theorem solution.{u_1, u_2, u_3} : type_of% @OAI.ElasticityCoordinates.planar_smooth_representative_oai.{u_1, u_2, u_3} := @OAI.ElasticityCoordinates.planar_smooth_representative_oai.{u_1, u_2, u_3}
