-- Prove2me | solution 1 for OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T14:53:47.234664+00:00
-- url     : https://prove2.me/submissions/3d5ad7ef-ed4f-4cbe-818d-0aa4d5c3debc

import Mathlib
import Definitions.Def_OAIQ16Cd002

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Covering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section


noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators




noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
namespace SingleLatticeCovering.Sections

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma fiber_compact {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K) (y : F) :
    IsCompact (fiber K y) := by
  have he : fiber K y = Prod.fst '' (K ∩ Prod.snd ⁻¹' {y}) := by
    ext x; constructor
    · intro hx; exact ⟨(x,y),⟨hx,by simp⟩,rfl⟩
    · rintro ⟨⟨x',y'⟩,⟨hxy,hy⟩,hx⟩
      have hy' : y'=y := hy
      change x'=x at hx
      subst x'; subst y'; exact hxy
  rw [he]
  exact (hK.inter_right (isClosed_singleton.preimage continuous_snd)).image continuous_fst




end SingleLatticeCovering.Sections





end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Sections
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped ENNReal NNReal BigOperators
noncomputable section
open Set Metric MeasureTheory MeasureTheory.Measure Module
open scoped Pointwise ENNReal NNReal BigOperators
noncomputable section

noncomputable section

noncomputable section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]



lemma eventually_fiber_subset {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] {K : Set (E × F)} (hK : IsCompact K)
    {y : F} {U : Set E} (hU : IsOpen U) (hyU : fiber K y ⊆ U) :
    ∀ᶠ z in 𝓝 y, fiber K z ⊆ U := by
  let A : Set F := Prod.snd '' (K ∩ Prod.fst ⁻¹' Uᶜ)
  have hA : IsClosed A := ((hK.inter_right (hU.isClosed_compl.preimage continuous_fst)).image continuous_snd).isClosed
  have hy : y ∈ Aᶜ := by
    rintro ⟨⟨x,z⟩,⟨hx,hxU⟩,he⟩
    change z=y at he
    subst z
    exact hxU (hyU hx)
  filter_upwards [hA.isOpen_compl.mem_nhds hy] with z hz
  intro x hx
  by_contra hxU
  exact hz ⟨(x,z),⟨hx,hxU⟩,rfl⟩

lemma upperSemicontinuous_fiber_measure [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [OuterRegular μ] {K : Set (E × F)} (hK : IsCompact K) :
    UpperSemicontinuous (fun y : F => μ (fiber K y)) := by
  intro y r hyr
  obtain ⟨U,hfU,hU,hμU⟩ := (fiber K y).exists_isOpen_lt_of_lt r hyr
  filter_upwards [eventually_fiber_subset hK hU hfU] with z hz
  exact (measure_mono hz).trans_lt hμU



end SingleLatticeCovering.Sections

end
end
end
end
end
end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Isotropy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section



noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

lemma volume_pos {n : ℕ} {K : Set (E n)} (hi : (interior K).Nonempty) : 0 < volume K :=
  (isOpen_interior.measure_pos volume hi).trans_le (measure_mono interior_subset)

lemma uniform_probability {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) : IsProbabilityMeasure (uniformLaw K) :=
  cond_isProbabilityMeasure_of_finite (ne_of_gt (volume_pos hi)) hK.measure_ne_top

lemma continuous_memLp_uniform {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {F : Type*} [NormedAddCommGroup F] [SecondCountableTopology F]
    {f : E n → F} (hf : Continuous f) (p : ℝ≥0∞) : MemLp f p (uniformLaw K) := by
  let := uniform_probability hK hi
  obtain ⟨C,hC⟩ := (hK.image hf).isBounded.exists_norm_le
  apply MemLp.of_bound hf.aestronglyMeasurable C
  apply ae_smul_measure (c := (volume K)⁻¹)
  filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
  exact hC _ (mem_image_of_mem _ hx)

lemma continuous_eq_on_interior {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    {f g : E n → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[uniformLaw K] g) : EqOn f g (interior K) := by
  have h' : f =ᵐ[volume.restrict K] g :=
    (ae_ennreal_smul_measure_iff (ENNReal.inv_ne_zero.mpr hK.measure_ne_top)).mp h
  exact Measure.eqOn_open_of_ae_eq (μ := volume)
    (ae_restrict_of_ae_restrict_of_subset interior_subset h') isOpen_interior
    hf.continuousOn hg.continuousOn



lemma inner_not_constant_on_interior {n : ℕ} {K : Set (E n)}
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) (c : ℝ) :
    ¬EqOn (fun x => ⟪v,x⟫) (fun _ => c) (interior K) := by
  intro h
  obtain ⟨z,hz⟩ := hi
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  let t := r/(2*(‖v‖+1))
  have ht : 0 < t := by dsimp [t]; positivity
  have hdist : dist (z+t • v) z < r := by
    rw [dist_eq_norm,add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_pos ht]
    dsimp [t]
    rw [div_mul_eq_mul_div]
    apply (div_lt_iff₀ (by positivity : 0 < 2*(‖v‖+1))).mpr
    nlinarith [norm_nonneg v]
  have hz' := h (hball hdist)
  have hz0 := h hz
  simp only [inner_add_right,real_inner_smul_right] at hz'
  have hself : 0 < ⟪v,v⟫ := real_inner_self_pos.mpr hv
  nlinarith



lemma covariance_positive {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hi : (interior K).Nonempty) {v : E n} (hv : v ≠ 0) :
    0 < covarianceBilin (uniformLaw K) v v := by
  let := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hf : MemLp (fun x : E n => ⟪v,x⟫) 2 (uniformLaw K) :=
    continuous_memLp_uniform hK hi (by fun_prop) 2
  rw [covarianceBilin_self hμ]
  refine lt_of_le_of_ne (variance_nonneg _ _) ?_
  intro hzero
  have heq := ae_eq_integral_of_variance_eq_zero hf hzero.symm
  exact inner_not_constant_on_interior hi hv _
    (continuous_eq_on_interior hK (by fun_prop) continuous_const heq)





lemma positive_form_normalization {n : ℕ} (B : E n →L[ℝ] E n →L[ℝ] ℝ)
    (hs : ∀ x y, B x y=B y x) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ T : E n ≃L[ℝ] E n, ∀ x y, B (T x) (T y)=⟪x,y⟫ := by
  classical
  let Q := B.toBilinForm.toQuadraticMap
  obtain ⟨w,hw,⟨e⟩⟩ : ∃ w : Fin n → ℝ,
      (∀ i, w i = -1 ∨ w i = 0 ∨ w i = 1) ∧
      Q.Equivalent (QuadraticMap.weightedSumSquares ℝ w) := by
    have hdim : Module.finrank ℝ (E n)=n := finrank_euclideanSpace_fin
    have hh := QuadraticForm.equivalent_one_zero_neg_one_weighted_sum_squared Q
    rw [hdim] at hh
    exact hh
  have hw1 : ∀ i, w i=1 := by
    intro i
    have hz : e.symm (Pi.single i (1 : ℝ)) ≠ 0 := by
      intro h
      have hh := congrArg e h
      have : (Pi.single i (1 : ℝ) : Fin n → ℝ)=0 := by simp at hh
      have := congrFun this i
      simp at this
    have he := e.symm.map_app (Pi.single i (1 : ℝ))
    have hwp : 0 < w i := by
      have hq : 0 < Q (e.symm (Pi.single i (1 : ℝ))) := hp _ hz
      rw [he] at hq
      simpa [QuadraticMap.weightedSumSquares_apply,Pi.single_apply] using hq
    rcases hw i with h | h | h
    · linarith
    · linarith
    · exact h
  let T : E n ≃L[ℝ] E n :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans e.symm.toLinearEquiv).toContinuousLinearEquiv
  have hdiag : ∀ x : E n, B (T x) (T x)=⟪x,x⟫ := by
    intro x
    have he := e.symm.map_app (WithLp.ofLp x)
    change B (T x) (T x)=_ at he
    rw [he]
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [QuadraticMap.weightedSumSquares_apply,hw1,one_smul,star_trivial]
    rfl
  refine ⟨T,fun x y => ?_⟩
  have h := hdiag (x+y)
  simp only [map_add,_root_.add_apply,inner_add_left,inner_add_right] at h
  rw [hdiag x,hdiag y,hs (T y) (T x),real_inner_comm x y] at h
  linarith




lemma adjointEquiv_adjoint {n : ℕ} (T : E n ≃L[ℝ] E n) :
    (adjointEquiv T).toContinuousLinearMap.adjoint=T.toContinuousLinearMap :=
  ContinuousLinearMap.adjoint_adjoint _

end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




lemma map_centeredEquiv {n : ℕ} (μ : Measure (E n)) (A : E n ≃L[ℝ] E n) :
    μ.map (centeredEquiv μ A)=(μ.map (fun x => -(∫ x, x ∂μ)+x)).map A := by
  rw [Measure.map_map A.continuous.measurable (by fun_prop)]
  rfl

lemma memLp_translate {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (c : E n) : MemLp id 2 (μ.map (fun x => c+x)) := by
  have hc : MemLp (fun _ : E n => c) 2 μ := memLp_const c
  have hsum : MemLp (fun x : E n => c+x) 2 μ := hc.add hμ
  exact (measurableEmbedding_addLeft c).memLp_map_measure_iff.mpr hsum

lemma memLp_centered {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : MemLp id 2 (μ.map (fun x => -(∫ x, x ∂μ)+x)) :=
  memLp_translate hμ _

lemma centeredEquiv_mean {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) :
    (∫ x, x ∂μ.map (centeredEquiv μ A))=0 := by
  have hcent := memLp_centered hμ
  rw [map_centeredEquiv]
  change (∫ x, x ∂(μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap)=0
  rw [A.toContinuousLinearMap.integral_id_map (hcent.integrable (by simp)),
    integral_map (by fun_prop) (by fun_prop)]
  change A (∫ x, -(∫ z, z ∂μ)+x ∂μ)=0
  rw [integral_add (f := fun _ : E n => -(∫ z, z ∂μ)) (g := fun x : E n => x)
    (integrable_const _) (hμ.integrable (by simp))]
  simp

lemma centeredEquiv_covariance {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (A : E n ≃L[ℝ] E n) (u v : E n) :
    covarianceBilin (μ.map (centeredEquiv μ A)) u v=
      covarianceBilin μ (A.toContinuousLinearMap.adjoint u) (A.toContinuousLinearMap.adjoint v) := by
  rw [map_centeredEquiv]
  change covarianceBilin ((μ.map (fun x => -(∫ z, z ∂μ)+x)).map A.toContinuousLinearMap) u v=_
  rw [covarianceBilin_map (memLp_centered hμ) A.toContinuousLinearMap]
  rw [covarianceBilin_map_const_add]



theorem uniform_affine_isotropization {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂(uniformLaw K).map e)=0 ∧
      ∀ u v : E n, covarianceBilin ((uniformLaw K).map e) u v=⟪u,v⟫ := by
  let : IsProbabilityMeasure (uniformLaw K) := uniform_probability hK hi
  have hμ : MemLp id 2 (uniformLaw K) := continuous_memLp_uniform hK hi continuous_id 2
  have hs : ∀ x y : E n, covarianceBilin (uniformLaw K) x y=
      covarianceBilin (uniformLaw K) y x := fun x y => covarianceBilin_comm x y
  have hp : ∀ x : E n, x ≠ 0 → 0 < covarianceBilin (uniformLaw K) x x :=
    fun x hx => covariance_positive hK hi hx
  obtain ⟨T,hT⟩ := positive_form_normalization (covarianceBilin (uniformLaw K)) hs hp
  refine ⟨centeredEquiv (uniformLaw K) (adjointEquiv T),centeredEquiv_mean hμ _,?_⟩
  intro u v
  rw [centeredEquiv_covariance hμ,adjointEquiv_adjoint]
  exact hT u v



end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace




lemma affine_map_volume {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    volume.map e=ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| • volume := by
  have he : (e : E n → E n)=(fun x => x+e 0) ∘ (e.linear.toLinearMap : E n → E n) := by
    funext x
    simpa using e.map_vadd (0 : E n) x
  rw [he,←Measure.map_map (by fun_prop) e.linear.toLinearMap.continuous_of_finiteDimensional.measurable]
  rw [map_linearMap_addHaar_eq_smul_addHaar volume e.linear.isUnit_det'.ne_zero,
    Measure.map_smul,map_add_right_eq_self]

lemma affine_volume_factor_pos {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) :
    0 < ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹| := by
  apply ENNReal.ofReal_pos.mpr
  exact abs_pos.mpr (inv_ne_zero e.linear.isUnit_det'.ne_zero)



lemma map_uniformLaw {n : ℕ} (e : E n ≃ᵃ[ℝ] E n) (K : Set (E n)) :
    (uniformLaw K).map e=uniformLaw (e '' K) := by
  let em := affineMeasurableEquiv e
  let c := ENNReal.ofReal |(LinearMap.det e.linear.toLinearMap)⁻¹|
  have hc : c ≠ 0 := ne_of_gt (affine_volume_factor_pos e)
  have hct : c ≠ ∞ := ENNReal.ofReal_ne_top
  have hmap : volume.map em=c • volume := affine_map_volume e
  have hpre : em ⁻¹' (e '' K)=K := by
    change e ⁻¹' (e '' K)=K
    exact Set.preimage_image_eq _ e.injective
  have hval : volume K=c*volume (e '' K) := by
    have h := congrArg (fun μ : Measure (E n) => μ (e '' K)) hmap
    rw [em.map_apply,hpre] at h
    exact h
  have hrestr : (volume.restrict K).map em=c • volume.restrict (e '' K) := by
    have h := em.restrict_map volume (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at h
    exact h.symm
  change ((volume K)⁻¹ • volume.restrict K).map em= _
  rw [Measure.map_smul,hrestr,smul_smul]
  unfold uniformLaw
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(volume (e '' K))⁻¹*c=(c⁻¹*c)*(volume (e '' K))⁻¹ := by ac_rfl
    _ = (volume (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]



theorem isotropic_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      (∫ x, x ∂uniformLaw (e '' K))=0 ∧
      ∀ u v : E n, covarianceBilin (uniformLaw (e '' K)) u v=⟪u,v⟫ := by
  obtain ⟨e,hmean,hcov⟩ := uniform_affine_isotropization hK hi
  rw [map_uniformLaw] at hmean hcov
  exact ⟨e,hmean,hcov⟩






lemma uniformPdf_measurable {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K) :
    Measurable (uniformPdf K) := measurable_const.indicator hK

lemma uniformPdf_nonneg {n : ℕ} (K : Set (E n)) (x : E n) : 0 ≤ uniformPdf K x := by
  exact Set.indicator_nonneg (fun _ _ => ENNReal.toReal_nonneg) x

lemma uniformPdf_logConcave {n : ℕ} {K : Set (E n)} (hK : IsCompact K)
    (hc : Convex ℝ K) (hi : (interior K).Nonempty) : LogConcave (uniformPdf K) := by
  have hvol : volume K ≠ 0 := ne_of_gt (volume_pos hi)
  have hC : 0 < ((volume K)⁻¹).toReal := ENNReal.toReal_pos
    (ENNReal.inv_ne_zero.mpr hK.measure_ne_top) (ENNReal.inv_ne_top.mpr hvol)
  refine ⟨uniformPdf_nonneg K,fun x y a b ha hb hab => ?_⟩
  by_cases hx : x ∈ K
  · by_cases hy : y ∈ K
    · have hz := hc hx hy (le_of_lt ha) (le_of_lt hb) hab
      simp only [uniformPdf,Set.indicator_of_mem hx,Set.indicator_of_mem hy,Set.indicator_of_mem hz]
      rw [←Real.rpow_add hC,hab,Real.rpow_one]
    · simp only [uniformPdf,Set.indicator_of_notMem hy,Real.zero_rpow (ne_of_gt hb),mul_zero]
      exact uniformPdf_nonneg K _
  · simp only [uniformPdf,Set.indicator_of_notMem hx,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact uniformPdf_nonneg K _

lemma uniformLaw_eq_withDensity {n : ℕ} {K : Set (E n)} (hK : MeasurableSet K)
    (hi : (interior K).Nonempty) :
    uniformLaw K=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf K x)) := by
  have hct : (volume K)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr (ne_of_gt (volume_pos hi))
  have he : (fun x => ENNReal.ofReal (uniformPdf K x))=
      K.indicator (fun _ => (volume K)⁻¹) := by
    funext x
    by_cases hx : x ∈ K
    · simp only [uniformPdf,Set.indicator_of_mem hx]
      exact ENNReal.ofReal_toReal hct
    · simp [uniformPdf,hx]
  rw [he,withDensity_indicator hK,withDensity_const]
  rfl



lemma covariance_isotropy {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hmean : (∫ x, x ∂μ)=0)
    (hcov : ∀ u v : E n, covarianceBilin μ u v=⟪u,v⟫) : IsIsotropic μ := by
  refine ⟨hmean,fun u v => ?_⟩
  have h := hcov u v
  rw [covarianceBilin_apply hμ] at h
  simp only [id_eq] at h
  rw [hmean] at h
  simpa using h




end SingleLatticeCovering.Isotropization

end
end

section
noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace

lemma affine_body_properties {n : ℕ} (e : E n ≃ᵃ[ℝ] E n)
    {K : Set (E n)} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H : E n ≃ₜ E n :=
    { toEquiv := e.toEquiv
      continuous_toFun := e.toAffineMap.continuous_of_finiteDimensional
      continuous_invFun := e.symm.toAffineMap.continuous_of_finiteDimensional }
  refine ⟨hK.image H.continuous,hc.affine_image e.toAffineMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H




theorem isotropic_logConcave_affine_body {n : ℕ} {K : Set (E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    ∃ e : E n ≃ᵃ[ℝ] E n,
      IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty ∧
      IsProbabilityMeasure (uniformLaw (e '' K)) ∧ MemLp id 2 (uniformLaw (e '' K)) ∧
      IsIsotropic (uniformLaw (e '' K)) ∧
      Measurable (uniformPdf (e '' K)) ∧ LogConcave (uniformPdf (e '' K)) ∧
      uniformLaw (e '' K)=volume.withDensity (fun x => ENNReal.ofReal (uniformPdf (e '' K) x)) := by
  obtain ⟨e,hmean,hcov⟩ := isotropic_affine_body hK hi
  obtain ⟨hK',hc',hi'⟩ := affine_body_properties e hK hc hi
  have hprob := uniform_probability hK' hi'
  let := hprob
  have hmem : MemLp id 2 (uniformLaw (e '' K)) :=
    continuous_memLp_uniform hK' hi' continuous_id 2
  exact ⟨e,hK',hc',hi',hprob,hmem,covariance_isotropy hmem hmean hcov,
    uniformPdf_measurable hK'.measurableSet,uniformPdf_logConcave hK' hc' hi',
    uniformLaw_eq_withDensity hK'.measurableSet hi'⟩



end SingleLatticeCovering.Isotropization

end
end

section

noncomputable section
namespace SingleLatticeCovering.Sections
open Set MeasureTheory MeasureTheory.Measure Filter Topology
open scoped ENNReal

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]



lemma map_snd_restrict {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd ((μ.prod ν).restrict K)=ν.withDensity (fun y => μ (fiber K y)) := by
  ext U hU
  rw [Measure.map_apply measurable_snd hU,Measure.restrict_apply (measurable_snd hU),
    Measure.prod_apply_symm ((measurable_snd hU).inter hK),withDensity_apply _ hU,
    ←lintegral_indicator hU]
  apply lintegral_congr
  intro y
  by_cases hy : y ∈ U
  · simp only [Set.indicator_of_mem hy]
    congr 1
    ext x
    simp [fiber,hy]
  · simp only [Set.indicator_of_notMem hy]
    have he : (fun x : E => (x,y)) ⁻¹' (Prod.snd ⁻¹' U ∩ K)=∅ := by ext x; simp [hy]
    rw [he,measure_empty]

lemma measurable_fiber_measure {E : Type*} {F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] (μ : Measure E) [SFinite μ]
    {K : Set (E × F)} (hK : MeasurableSet K) : Measurable (fun y => μ (fiber K y)) :=
  measurable_measure_prodMk_right hK




lemma map_snd_uniform (μ : Measure E) [SFinite μ] (ν : Measure F) [SFinite ν]
    {K : Set (E × F)} (hK : MeasurableSet K) :
    Measure.map Prod.snd (((μ.prod ν) K)⁻¹ • (μ.prod ν).restrict K)=
      ν.withDensity (fun y => ((μ.prod ν) K)⁻¹*μ (fiber K y)) := by
  rw [Measure.map_smul,map_snd_restrict μ ν hK]
  exact (withDensity_smul _ (measurable_fiber_measure μ hK)).symm




end SingleLatticeCovering.Sections

end
end

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Transport
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.SharpYoung

lemma densityCDF_transport (f g : PositiveDensity) (x : ℝ) :
    densityCDF g (densityTransport f g x) = densityCDF f x := by
  change ((densityCDFIso g) ((densityCDFIso g).symm (densityCDFIso f x)) : ℝ) = _
  simp

lemma densityTransport_hasDerivAt (f g : PositiveDensity) (x : ℝ) :
    HasDerivAt (densityTransport f g) (f x / g (densityTransport f g x)) x := by
  apply HasDerivAt.of_comp_left (densityTransport f g).continuous.continuousAt
    (densityCDF_hasDerivAt g _) (densityCDF_hasDerivAt f x) (ne_of_gt (g.positive _))
  exact Filter.Eventually.of_forall (densityCDF_transport f g)



end SingleLatticeCovering.SharpYoung


open MeasureTheory Filter Set
open scoped Topology ENNReal
end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section




noncomputable section
namespace SingleLatticeCovering.Isotropization
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace BigOperators


lemma coordinate_memLp {n : ℕ} {μ : Measure (E n)} {p : ℝ≥0∞}
    (hμ : MemLp id p μ) (i : Fin n) : MemLp (fun x : E n => x i) p μ := by
  simpa only [Function.comp_def,id_eq,EuclideanSpace.proj,PiLp.proj_apply] using
    hμ.continuousLinearMap_comp (EuclideanSpace.proj i : E n →L[ℝ] ℝ)

lemma isotropic_coordinate_second {n : ℕ} {μ : Measure (E n)}
    (hiso : IsIsotropic μ) (i : Fin n) : (∫ x, (x i)^2 ∂μ)=1 := by
  have h := hiso.2 (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
  simpa only [EuclideanSpace.inner_single_left,one_mul,EuclideanSpace.inner_single_right,
    PiLp.single_apply,mul_one,one_pow,←sq,map_one,ite_true] using h

lemma isotropic_norm_sq {n : ℕ} {μ : Measure (E n)}
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) : (∫ x, ‖x‖^2 ∂μ)=(n : ℝ) := by
  have hi (i : Fin n) : Integrable (fun x : E n => (x i)^2) μ :=
    (coordinate_memLp hμ i).integrable_sq
  have he (x : E n) : ‖x‖^2=∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  simp only [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [isotropic_coordinate_second hiso,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,mul_one]

end SingleLatticeCovering.Isotropization

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators

lemma integral_norm_le_sqrt_second {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {f : α → ℝ} (hf : MemLp f 2 μ) :
    (∫ x, |f x| ∂μ) ≤ Real.sqrt (∫ x, (f x)^2 ∂μ) := by
  have H := variance_nonneg (fun x => |f x|) μ
  rw [variance_eq_sub (by simpa only [Real.norm_eq_abs] using hf.norm)] at H
  simp only [Pi.pow_apply,sq_abs] at H
  exact (Real.le_sqrt (integral_nonneg (fun _ => abs_nonneg _))
    (integral_nonneg (fun _ => sq_nonneg _))).mpr (by linarith)

lemma inner_memLp_two {n : ℕ} {μ : Measure (E n)} (hμ : MemLp id 2 μ) (x : E n) :
    MemLp (fun y : E n => ⟪x,y⟫) 2 μ := by
  simpa only [Function.comp_def,id_eq,innerSL_apply_apply] using
    hμ.continuousLinearMap_comp (innerSL ℝ x : E n →L[ℝ] ℝ)

lemma isotropic_abs_inner_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (x : E n) :
    (∫ y, |⟪x,y⟫| ∂μ) ≤ ‖x‖ := by
  have H := integral_norm_le_sqrt_second (inner_memLp_two hμ x)
  have he : (∫ y, ⟪x,y⟫^2 ∂μ)=‖x‖^2 := by
    simpa only [pow_two,real_inner_self_eq_norm_sq] using hiso.2 x x
  rw [he,Real.sqrt_sq (norm_nonneg x)] at H
  exact H

lemma isotropic_norm_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    (∫ x, ‖x‖ ∂μ) ≤ Real.sqrt (n : ℝ) := by
  have H := integral_norm_le_sqrt_second hμ.norm
  simpa only [id_eq,abs_norm,isotropic_norm_sq hμ hiso] using H

lemma exp_negative_lipschitz {u v : ℝ} (hu : u ≤ 0) (hv : v ≤ 0) :
    |Real.exp u-Real.exp v| ≤ |u-v| := by
  wlog huv : u ≤ v generalizing u v
  · rw [abs_sub_comm (Real.exp u),abs_sub_comm u]
    exact this hv hu (le_of_not_ge huv)
  rw [abs_of_nonpos (sub_nonpos.mpr (Real.exp_le_exp.mpr huv)),
    abs_of_nonpos (sub_nonpos.mpr huv)]
  have hlow := Real.add_one_le_exp (u-v)
  have hpos : 0 ≤ 1-Real.exp (u-v) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr (sub_nonpos.mpr huv))
  have hmul : Real.exp v*(1-Real.exp (u-v)) ≤ 1-Real.exp (u-v) :=
    mul_le_of_le_one_left hpos (Real.exp_le_one_iff.mpr hv)
  rw [mul_sub,mul_one,←Real.exp_add] at hmul
  rw [show v+(u-v)=u by ring] at hmul
  linarith

lemma gaussianKernel_bounded {n : ℕ} (s : ℝ) (x : E n) :
    |Real.exp (-s^2*‖x‖^2/2)| ≤ 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (sq_nonneg _)) (by norm_num))

lemma gaussianKernel_integrable {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun x => Real.exp (-s^2*‖x‖^2/2)) μ := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s x)

lemma gaussianKernel_covariance_bound {n : ℕ} (s : ℝ) (x y : E n) :
    |Real.exp (-s^2*‖x-y‖^2/2)-Real.exp (-s^2*‖x‖^2/2)*Real.exp (-s^2*‖y‖^2/2)|
      ≤ s^2*|⟪x,y⟫| := by
  rw [←Real.exp_add]
  have hn (z : E n) : -s^2*‖z‖^2/2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg s)) (sq_nonneg _)) (by norm_num)
  have H := exp_negative_lipschitz (hn (x-y)) (add_nonpos (hn x) (hn y))
  have he : -s^2*‖x-y‖^2/2-(-s^2*‖x‖^2/2+ -s^2*‖y‖^2/2)=s^2*⟪x,y⟫ := by
    rw [norm_sub_sq_real]
    ring
  simpa only [he,abs_mul,abs_of_nonneg (sq_nonneg s)] using H



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma norm_phase {n : ℕ} (s : ℝ) (x g : E n) : ‖phase s x g‖=1 := by
  simp [phase,Complex.norm_exp]

lemma charFun_phase {n : ℕ} (μ : Measure (E n)) (s : ℝ) (g : E n) :
    charFun μ (s•g) = ∫ x, phase s x g ∂μ := by
  simp only [charFun_apply,phase,inner_smul_right,Complex.ofReal_mul]

lemma phase_gaussian_integral {n : ℕ} (s : ℝ) (x : E n) :
    (∫ g, phase s x g ∂stdGaussian (E n))=(Real.exp (-s^2*‖x‖^2/2) : ℂ) := by
  have H := charFun_stdGaussian (s•x)
  rw [charFun_apply] at H
  have he : (fun g : E n => Complex.exp ((⟪g,s•x⟫ : ℝ)*Complex.I))=phase s x := by
    funext g
    simp only [phase,inner_smul_right,real_inner_comm]
  rw [he] at H
  rw [norm_smul,Real.norm_eq_abs,←Complex.ofReal_pow,mul_pow,sq_abs] at H
  simpa only [Complex.ofReal_exp,Complex.ofReal_div,Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_ofNat,neg_mul] using H

lemma phase_product_integrable {n : ℕ} (μ ν : Measure (E n))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : ℝ) :
    Integrable (fun p : E n × E n => phase s p.1 p.2) (μ.prod ν) := by
  apply (integrable_const (1:ℝ)).mono' (by unfold phase; fun_prop)
  exact Filter.Eventually.of_forall (fun p => (norm_phase s p.1 p.2).le)

lemma gaussian_char_average {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    (∫ g, charFun μ (s•g) ∂stdGaussian (E n))=(radialGaussianAverage μ s : ℂ) := by
  simp only [charFun_phase]
  rw [integral_integral_swap (phase_product_integrable (stdGaussian (E n)) μ s |>.congr (by
    exact Filter.Eventually.of_forall (fun p => by change phase s p.1 p.2 = phase s p.2 p.1; simp only [phase,real_inner_comm])))]
  simp only [phase_gaussian_integral]
  rw [integral_complex_ofReal]
  rfl

lemma phase_sub {n : ℕ} (s : ℝ) (x y g : E n) :
    phase s (x-y) g=phase s x g*conj (phase s y g) := by
  simp only [phase,inner_sub_left,mul_sub,Complex.ofReal_sub,sub_mul,Complex.exp_sub,
    ←Complex.exp_conj,map_mul,Complex.conj_ofReal,Complex.conj_I,mul_neg,Complex.exp_neg]
  exact div_eq_mul_inv _ _

lemma charFun_differenceLaw {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (t : E n) :
    charFun ((μ.prod μ).map (fun p : E n × E n => p.1-p.2)) t = (‖charFun μ t‖^2 : ℝ) := by
  rw [charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have hint : Integrable (fun p : E n × E n => Complex.exp ((⟪p.1-p.2,t⟫ : ℝ)*Complex.I)) (μ.prod μ) := by
    apply (integrable_const (1:ℝ)).mono' (by fun_prop)
    exact Filter.Eventually.of_forall (fun p => by simp [Complex.norm_exp])
  rw [integral_prod _ hint]
  have he (x y : E n) : Complex.exp ((⟪x-y,t⟫ : ℝ)*Complex.I) =
      Complex.exp ((⟪x,t⟫ : ℝ)*Complex.I)*conj (Complex.exp ((⟪y,t⟫ : ℝ)*Complex.I)) := by
    simpa only [phase,one_mul] using phase_sub 1 x y t
  simp only [he,integral_const_mul,integral_mul_const,integral_conj,←charFun_apply]
  rw [Complex.mul_conj,Complex.normSq_eq_norm_sq]

lemma gaussian_char_secondMoment {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))=
      ∫ x, ∫ y, Real.exp (-s^2*‖x-y‖^2/2) ∂μ ∂μ := by
  let ν := (μ.prod μ).map (fun p : E n × E n => p.1-p.2)
  have : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map (measurable_fst.sub measurable_snd).aemeasurable
  have H := gaussian_char_average ν s
  simp only [ν,charFun_differenceLaw,integral_complex_ofReal] at H
  have H' : (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))=radialGaussianAverage ν s :=
    Complex.ofReal_injective H
  rw [H',radialGaussianAverage,integral_map (by fun_prop) (by fun_prop)]
  apply integral_prod
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s (p.1-p.2))



end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma charFun_gaussian_integrable {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun g => charFun μ (s•g)) (stdGaussian (E n)) := by
  apply (integrable_const (1:ℝ)).mono' ((continuous_charFun.comp (by fun_prop)).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun _ => norm_charFun_le_one _)

lemma charFun_gaussian_sq_integrable {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    Integrable (fun g => ‖charFun μ (s•g)‖^2) (stdGaussian (E n)) := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun _ => by
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
    exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _))

lemma complex_center_sq (z : ℂ) (a : ℝ) :
    ‖z-(a:ℂ)‖^2=‖z‖^2-2*a*z.re+a^2 := by
  simp only [Complex.sq_norm,Complex.normSq_apply,Complex.sub_re,Complex.sub_im,
    Complex.ofReal_re,Complex.ofReal_im,sub_zero]
  ring

lemma gaussian_char_variance_identity {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))=
      (∫ g, ‖charFun μ (s•g)‖^2 ∂stdGaussian (E n))-(radialGaussianAverage μ s)^2 := by
  have hr : Integrable (fun g => (charFun μ (s•g)).re) (stdGaussian (E n)) :=
    (charFun_gaussian_integrable μ s).re
  have hc := hr.const_mul (2*radialGaussianAverage μ s)
  simp only [complex_center_sq]
  rw [integral_add (f := fun g => ‖charFun μ (s•g)‖^2-2*radialGaussianAverage μ s*(charFun μ (s•g)).re)
      (g := fun _ => (radialGaussianAverage μ s)^2)
      ((charFun_gaussian_sq_integrable μ s).sub hc) (integrable_const _),
    integral_sub (f := fun g => ‖charFun μ (s•g)‖^2)
      (g := fun g => 2*radialGaussianAverage μ s*(charFun μ (s•g)).re)
      (charFun_gaussian_sq_integrable μ s) hc,
    integral_const_mul]
  have H : (∫ g, (charFun μ (s•g)).re ∂stdGaussian (E n))=radialGaussianAverage μ s := by
    have HH := integral_re (charFun_gaussian_integrable μ s)
    change (∫ g, (charFun μ (s•g)).re ∂stdGaussian (E n)) =
      (∫ g, charFun μ (s•g) ∂stdGaussian (E n)).re at HH
    rw [HH,gaussian_char_average,Complex.ofReal_re]
  rw [H,integral_const,probReal_univ,one_smul]
  ring

lemma gaussianKernel_prod_integrable {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] (s : ℝ) :
    Integrable (fun p : E n × E n => Real.exp (-s^2*‖p.1-p.2‖^2/2)) (μ.prod μ) := by
  apply (integrable_const (1:ℝ)).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s (p.1-p.2))

lemma gaussian_char_variance_kernel {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))=
      ∫ p : E n × E n, (Real.exp (-s^2*‖p.1-p.2‖^2/2)-
        Real.exp (-s^2*‖p.1‖^2/2)*Real.exp (-s^2*‖p.2‖^2/2)) ∂μ.prod μ := by
  rw [gaussian_char_variance_identity,gaussian_char_secondMoment,
    integral_sub (gaussianKernel_prod_integrable μ s)
      ((gaussianKernel_integrable μ s).mul_prod (gaussianKernel_integrable μ s)),
    integral_prod _ (gaussianKernel_prod_integrable μ s),
    integral_prod_mul (fun x : E n => Real.exp (-s^2*‖x‖^2/2))
      (fun x : E n => Real.exp (-s^2*‖x‖^2/2))]
  simp only [radialGaussianAverage,pow_two]

lemma abs_inner_prod_integrable {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) : Integrable (fun p : E n × E n => |⟪p.1,p.2⟫|) (μ.prod μ) := by
  have hn : Integrable (fun x : E n => ‖x‖) μ := by
    simpa only [id_eq] using (hμ.integrable (by norm_num)).norm
  apply (hn.mul_prod hn).mono' (by fun_prop)
  exact Filter.Eventually.of_forall (fun p => by simpa only [Real.norm_eq_abs,abs_abs] using abs_real_inner_le_norm p.1 p.2)

lemma isotropic_abs_inner_prod_integral {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    (∫ p : E n × E n, |⟪p.1,p.2⟫| ∂μ.prod μ) ≤ Real.sqrt (n : ℝ) := by
  have hi := abs_inner_prod_integrable hμ
  rw [integral_prod _ hi]
  exact (integral_mono hi.integral_prod_left
    (by simpa only [id_eq] using (hμ.integrable (by norm_num)).norm)
    (isotropic_abs_inner_integral hμ hiso)).trans (isotropic_norm_integral hμ hiso)



lemma gaussian_char_variance_bound {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖^2 ∂stdGaussian (E n))
      ≤ s^2*Real.sqrt (n : ℝ) := by
  rw [gaussian_char_variance_kernel]
  have hi := (gaussianKernel_prod_integrable μ s).sub
    ((gaussianKernel_integrable μ s).mul_prod (gaussianKernel_integrable μ s))
  calc
    _ ≤ ∫ p : E n × E n, s^2*|⟪p.1,p.2⟫| ∂μ.prod μ :=
      integral_mono hi ((abs_inner_prod_integrable hμ).const_mul _)
        (fun p => (le_abs_self _).trans (gaussianKernel_covariance_bound s p.1 p.2))
    _ = s^2*(∫ p : E n × E n, |⟪p.1,p.2⟫| ∂μ.prod μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (isotropic_abs_inner_prod_integral hμ hiso) (sq_nonneg s)


end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma continuous_rowApply {n k : ℕ} : Continuous (fun p : MatrixSpace n k × E k => rowApply p.1 p.2) := by
  unfold rowApply
  fun_prop

lemma continuous_colApply {n k : ℕ} : Continuous (fun p : MatrixSpace n k × E n => colApply p.1 p.2) := by
  unfold colApply
  fun_prop

lemma inner_colApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) (t : E k) :
    ⟪colApply g x,t⟫=⟪x,rowApply g t⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    colApply,rowApply,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma inner_rowApply {n k : ℕ} (g : MatrixSpace n k) (x : E n) (t : E k) :
    ⟪rowApply g t,x⟫=⟪g,tensor x t⟫ := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial,
    rowApply,tensor,Finset.mul_sum,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma norm_tensor_sq {n k : ℕ} (x : E n) (t : E k) : ‖tensor x t‖^2=‖x‖^2*‖t‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq,tensor,Real.norm_eq_abs,
    sq_abs,mul_pow,Fintype.sum_prod_type,Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]

lemma rowApply_gaussian_law {n k : ℕ} (t : E k) :
    (stdGaussian (MatrixSpace n k)).map (fun g => rowApply g t)=
      (stdGaussian (E n)).map (fun x => ‖t‖•x) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  apply Measure.ext_of_charFun
  funext x
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop),
    charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  simp only [inner_rowApply,inner_smul_left,conj_trivial]
  have he (z : E n) : (‖t‖*⟪z,x⟫ : ℝ)=⟪z,‖t‖•x⟫ := by rw [inner_smul_right]
  simp only [he,←charFun_apply,charFun_stdGaussian]
  congr 1
  rw [←Complex.ofReal_pow,←Complex.ofReal_pow,norm_tensor_sq,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]
  push_cast
  ring

lemma radialGaussianAverage_nonneg {n : ℕ} (μ : Measure (E n)) (s : ℝ) :
    0 ≤ radialGaussianAverage μ s := integral_nonneg (fun _ => (Real.exp_pos _).le)

lemma radialGaussianAverage_le_one {n : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ] (s : ℝ) :
    radialGaussianAverage μ s ≤ 1 := by
  unfold radialGaussianAverage
  calc
    _ ≤ ∫ _ : E n, (1:ℝ) ∂μ := integral_mono (gaussianKernel_integrable μ s)
      (integrable_const _) (fun x => (le_abs_self _).trans (gaussianKernel_bounded s x))
    _ = 1 := by simp

lemma gaussian_char_mean_deviation {n : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) :
    (∫ g, ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖ ∂stdGaussian (E n))
      ≤ Real.sqrt (s^2*Real.sqrt (n : ℝ)) := by
  have hb (g : E n) : ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖ ≤ 2 := by
    calc
      _ ≤ ‖charFun μ (s•g)‖+‖(radialGaussianAverage μ s : ℂ)‖ := norm_sub_le _ _
      _ ≤ 1+1 := add_le_add (norm_charFun_le_one _) (by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (radialGaussianAverage_nonneg μ s)]
          using radialGaussianAverage_le_one μ s)
      _ = 2 := by norm_num
  have hlp : MemLp (fun g => ‖charFun μ (s•g)-(radialGaussianAverage μ s : ℂ)‖) 2 (stdGaussian (E n)) :=
    MemLp.of_bound (by fun_prop) 2 (Filter.Eventually.of_forall (fun g => by simpa only [norm_norm] using hb g))
  have H := integral_norm_le_sqrt_second hlp
  simp only [abs_norm] at H
  exact H.trans (Real.sqrt_le_sqrt (gaussian_char_variance_bound hμ hiso s))

lemma gaussian_matrix_char_deviation {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) (t : E k) :
    (∫ g : MatrixSpace n k, ‖charFun μ (s•rowApply g t)-
      (radialGaussianAverage μ (s*‖t‖) : ℂ)‖ ∂stdGaussian (MatrixSpace n k))
      ≤ Real.sqrt ((s*‖t‖)^2*Real.sqrt (n : ℝ)) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  have hi := integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable
    (f := fun x : E n => ‖charFun μ (s•x)-(radialGaussianAverage μ (s*‖t‖) : ℂ)‖) (by fun_prop)
  rw [←hi,rowApply_gaussian_law,
    integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_char_mean_deviation hμ hiso _


end SingleLatticeCovering.GaussianProjection

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma isotropic_stdGaussian (n : ℕ) : IsIsotropic (stdGaussian (E n)) := by
  refine ⟨integral_id_stdGaussian,fun u v => ?_⟩
  have H := covarianceBilin_apply (μ := stdGaussian (E n)) IsGaussian.memLp_two_id u v
  simp only [id_eq,integral_id_stdGaussian,sub_zero,covarianceBilin_stdGaussian
    ] at H
  exact H.symm

lemma continuous_radialGaussianAverage {n : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ] :
    Continuous (radialGaussianAverage μ) := by
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
  · intro s; fun_prop
  · intro s
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded s x)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun x => by fun_prop)

lemma matrix_char_deviation_bound {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (a : ℝ) (g : MatrixSpace n k) (t : E k) :
    ‖charFun μ (a•rowApply g t)-(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ ≤ 2 := by
  calc
    _ ≤ ‖charFun μ (a•rowApply g t)‖+‖(radialGaussianAverage μ (a*‖t‖) : ℂ)‖ := norm_sub_le _ _
    _ ≤ 1+1 := add_le_add (norm_charFun_le_one _) (by
      simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (radialGaussianAverage_nonneg μ _)]
        using radialGaussianAverage_le_one μ (a*‖t‖))
    _ = 2 := by norm_num

lemma continuous_matrix_char_deviation {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Continuous (fun p : MatrixSpace n k × E k =>
      ‖charFun μ (a•rowApply p.1 p.2)-(radialGaussianAverage μ (a*‖p.2‖) : ℂ)‖) := by
  have hr := continuous_radialGaussianAverage μ
  have hc := continuous_rowApply (n := n) (k := k)
  exact ((continuous_charFun.comp (hc.const_smul a)).sub
    (Complex.continuous_ofReal.comp (hr.comp (continuous_snd.norm.const_mul a)))).norm

lemma matrix_char_deviation_integrable {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable (fun p : MatrixSpace n k × E k =>
      ‖charFun μ (a•rowApply p.1 p.2)-(radialGaussianAverage μ (a*‖p.2‖) : ℂ)‖)
      ((stdGaussian (MatrixSpace n k)).prod (stdGaussian (E k))) := by
  apply (integrable_const (2:ℝ)).mono' (continuous_matrix_char_deviation a).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p => by simpa only [norm_norm] using matrix_char_deviation_bound a p.1 p.2)

lemma matrixSmoothingError_integrable {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ] (a : ℝ) :
    Integrable (matrixSmoothingError (k := k) μ a) (stdGaussian (MatrixSpace n k)) :=
  (matrix_char_deviation_integrable a).integral_prod_left

lemma matrixSmoothingError_mean {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (a : ℝ) :
    (∫ g : MatrixSpace n k, matrixSmoothingError μ a g ∂stdGaussian (MatrixSpace n k)) ≤
      |a| *Real.sqrt (Real.sqrt (n : ℝ))*Real.sqrt (k : ℝ) := by
  unfold matrixSmoothingError
  rw [integral_integral_swap (matrix_char_deviation_integrable a)]
  have he (t : E k) : Real.sqrt ((a*‖t‖)^2*Real.sqrt (n : ℝ))=
      (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*‖t‖ := by
    rw [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq_eq_abs,abs_mul,abs_norm]
    ring
  calc
    _ ≤ ∫ t : E k, (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*‖t‖ ∂stdGaussian (E k) := by
      apply integral_mono (matrix_char_deviation_integrable a).integral_prod_right
        (IsGaussian.integrable_id.norm.const_mul _)
      intro t
      simpa only [he,id_eq] using gaussian_matrix_char_deviation hμ hiso a t
    _ = (|a| *Real.sqrt (Real.sqrt (n : ℝ)))*(∫ t : E k, ‖t‖ ∂stdGaussian (E k)) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (isotropic_norm_integral IsGaussian.memLp_two_id (isotropic_stdGaussian k)) (by positivity)

lemma phase_projected_sub {n k : ℕ} (s r : ℝ) (g : MatrixSpace n k) (y t : E k) (x : E n) :
    phase r (y-s•colApply g x) t=phase r y t*phase (-r*s) x (rowApply g t) := by
  simp only [phase,inner_sub_left,inner_smul_left,conj_trivial,inner_colApply,←Complex.exp_add]
  congr 1
  push_cast
  ring

lemma projected_phase_integrable {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    Integrable (fun p : E n × E k => phase r (y-s•colApply g p.1) p.2)
      (μ.prod (stdGaussian (E k))) := by
  have hc : Continuous (fun x : E n => colApply g x) :=
    continuous_colApply.comp (continuous_const.prodMk continuous_id)
  apply (integrable_const (1:ℝ)).mono' (by unfold phase; fun_prop)
  exact Filter.Eventually.of_forall (fun p => (norm_phase _ _ _).le)

lemma smoothedProjection_fourier {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    (smoothedProjection μ s r g y : ℂ)=
      ∫ t, phase r y t*charFun μ ((-r*s)•rowApply g t) ∂stdGaussian (E k) := by
  unfold smoothedProjection
  rw [←integral_complex_ofReal]
  simp_rw [←phase_gaussian_integral]
  rw [integral_integral_swap (projected_phase_integrable μ s r g y)]
  simp only [phase_projected_sub,integral_const_mul,←charFun_phase]

lemma smoothedProjection_uniform_error {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) (y : E k) :
    ‖(smoothedProjection μ s r g y : ℂ)-radialSmoothedModel μ s r y‖ ≤
      matrixSmoothingError μ (-r*s) g := by
  rw [smoothedProjection_fourier,radialSmoothedModel]
  have hr : Integrable (fun t : E k => phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)) (stdGaussian (E k)) := by
    apply (integrable_const (1:ℝ)).mono' ((by
      have hh := continuous_radialGaussianAverage μ
      unfold phase
      fun_prop) : AEStronglyMeasurable _ _)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [norm_mul,norm_phase,one_mul,Complex.norm_real,Real.norm_eq_abs,
        abs_of_nonneg (radialGaussianAverage_nonneg μ _)]
      exact radialGaussianAverage_le_one μ _)
  have hf : Integrable (fun t : E k => phase r y t*charFun μ ((-r*s)•rowApply g t)) (stdGaussian (E k)) := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc : Continuous (fun t : E k => rowApply g t) := continuous_rowApply.comp (continuous_const.prodMk continuous_id)
      unfold phase
      fun_prop)
    exact Filter.Eventually.of_forall (fun t => by simpa only [norm_mul,norm_phase,one_mul] using norm_charFun_le_one ((-r*s)•rowApply g t))
  rw [←integral_sub hf hr]
  calc
    _ ≤ ∫ t : E k, ‖phase r y t*charFun μ ((-r*s)•rowApply g t)-phase r y t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)‖ ∂stdGaussian (E k) := norm_integral_le_integral_norm _
    _ = matrixSmoothingError μ (-r*s) g := by simp only [←mul_sub,norm_mul,norm_phase,one_mul,matrixSmoothingError]



theorem exists_uniform_smoothed_projection {n k : ℕ} {μ : Measure (E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s r : ℝ) :
    ∃ g : MatrixSpace n k, ∀ y : E k,
      ‖(smoothedProjection μ s r g y : ℂ)-radialSmoothedModel μ s r y‖ ≤
        |r*s| *Real.sqrt (Real.sqrt (n : ℝ))*Real.sqrt (k : ℝ) := by
  obtain ⟨g,hg⟩ := exists_le_integral (matrixSmoothingError_integrable (k := k) (μ := μ) (-r*s))
  refine ⟨g,fun y => (smoothedProjection_uniform_error μ s r g y).trans (hg.trans ?_)⟩
  simpa only [neg_mul,abs_neg] using matrixSmoothingError_mean (k := k) hμ hiso (-r*s)




end SingleLatticeCovering.GaussianProjection


end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianSmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace BigOperators ComplexConjugate

lemma gaussian_matrix_char_average {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (a : ℝ) (t : E k) :
    (∫ g : MatrixSpace n k, charFun μ (a•rowApply g t) ∂stdGaussian (MatrixSpace n k))=
      (radialGaussianAverage μ (a*‖t‖) : ℂ) := by
  have hm : Measurable (fun g : MatrixSpace n k => rowApply g t) :=
    (continuous_rowApply.comp (continuous_id.prodMk continuous_const)).measurable
  have hi := integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable
    (f := fun x : E n => charFun μ (a•x)) (by fun_prop)
  rw [←hi,rowApply_gaussian_law,integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_char_average μ _

lemma matrix_phase_char_integrable {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) :
    Integrable (fun p : MatrixSpace n k × E k => phase r y p.2*charFun μ ((-r*s)•rowApply p.1 p.2))
      ((stdGaussian (MatrixSpace n k)).prod (stdGaussian (E k))) := by
  apply (integrable_const (1:ℝ)).mono' (by
    have hc := continuous_rowApply (n := n) (k := k)
    unfold phase
    fun_prop)
  exact Filter.Eventually.of_forall (fun p => by
    simpa only [norm_mul,norm_phase,one_mul] using norm_charFun_le_one ((-r*s)•rowApply p.1 p.2))

lemma radialSmoothedModel_eq_average {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) : radialSmoothedModel μ s r y=
      Complex.ofReal (∫ g : MatrixSpace n k, smoothedProjection μ s r g y ∂stdGaussian (MatrixSpace n k)) := by
  have H := integral_integral_swap (f := fun g t => phase r y t*charFun μ ((-r*s)•rowApply g t)) (matrix_phase_char_integrable μ s r y)
  simp only [←smoothedProjection_fourier,integral_const_mul,gaussian_matrix_char_average,
    integral_complex_ofReal] at H
  exact H.symm

lemma radialSmoothedDensity_cast {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (y : E k) : (radialSmoothedDensity μ s r y : ℂ)=radialSmoothedModel μ s r y := by
  simp only [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]

lemma radialSmoothedModel_invariant {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) (U : E k ≃ₗᵢ[ℝ] E k) (y : E k) :
    radialSmoothedModel μ s r (U y)=radialSmoothedModel μ s r y := by
  have hm : Measurable U := U.continuous.measurable
  have H := integral_map (μ := stdGaussian (E k)) hm.aemeasurable
    (f := fun t : E k => phase r (U y) t*(radialGaussianAverage μ ((-r*s)*‖t‖) : ℂ)) (by
      have hc := continuous_radialGaussianAverage μ
      unfold phase
      fun_prop)
  rw [stdGaussian_map U] at H
  have he (t : E k) : phase r (U y) (U t)=phase r y t := by
    simp only [phase,U.inner_map_map]
  simp only [he,U.norm_map] at H
  exact H

lemma radialSmoothedDensity_norm_eq {n k : ℕ} (μ : Measure (E n)) [IsProbabilityMeasure μ]
    (s r : ℝ) {y z : E k} (h : ‖y‖=‖z‖) :
    radialSmoothedDensity μ s r y=radialSmoothedDensity μ s r z := by
  have H := radialSmoothedModel_invariant μ s r (Submodule.reflection (ℝ ∙ (y-z))ᗮ) y
  rw [Submodule.reflection_sub h] at H
  exact congrArg Complex.re H.symm

lemma continuous_smoothedProjection {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) : Continuous (fun p : MatrixSpace n k × E k => smoothedProjection μ s r p.1 p.2) := by
  apply continuous_of_dominated (bound := fun _ => (1:ℝ))
  · intro p
    have hc : Continuous (fun x : E n => colApply p.1 x) := continuous_colApply.comp (continuous_const.prodMk continuous_id)
    fun_prop
  · intro p
    exact Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (p.2-s•colApply p.1 x))
  · exact integrable_const _
  · apply Filter.Eventually.of_forall
    intro x
    have hc : Continuous (fun g : MatrixSpace n k => colApply g x) := continuous_colApply.comp (continuous_id.prodMk continuous_const)
    fun_prop

section ContinuousProjection
attribute [local irreducible] smoothedProjection

lemma continuous_smoothedProjection_y {n k : ℕ} (μ : Measure (E n)) [IsFiniteMeasure μ]
    (s r : ℝ) (g : MatrixSpace n k) : Continuous (smoothedProjection μ s r g) := by
  have hp : Continuous (fun y : E k => (g,y)) := continuous_const.prodMk continuous_id
  exact (continuous_smoothedProjection μ s r).comp hp

end ContinuousProjection



end SingleLatticeCovering.GaussianProjection
noncomputable section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace ComplexConjugate

lemma normalizer_pos (k : ℕ) {b : ℝ} (hb : 0 < b) : 0 < normalizer k b := by
  unfold normalizer
  positivity
lemma density_pos {k : ℕ} {b : ℝ} (hb : 0 < b) (y : E k) : 0 < density b y := by
  unfold density
  exact mul_pos (inv_pos.mpr (normalizer_pos k hb)) (Real.exp_pos _)
lemma continuous_density (k : ℕ) (b : ℝ) : Continuous (density (k := k) b) := by
  unfold density
  fun_prop
lemma integrable_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : E k => Real.exp (-b*‖y‖^2)) volume := by
  have H := integrable_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb 0 (0:E k)
  have H' := H.re
  simpa only [zero_mul,add_zero,←Complex.ofReal_pow,←Complex.ofReal_mul,←Complex.ofReal_neg,
    RCLike.re_to_complex, Complex.exp_ofReal_re] using H'
lemma integral_kernel {k : ℕ} {b : ℝ} (hb : 0 < b) :
    (∫ y : E k, Real.exp (-b*‖y‖^2))=normalizer k b := by
  simpa only [normalizer,finrank_euclideanSpace_fin] using integral_rexp_neg_mul_sq_norm (V := E k) hb
lemma integrable_density {k : ℕ} {b : ℝ} (hb : 0 < b) : Integrable (density (k := k) b) volume :=
  (integrable_kernel hb).const_mul _
lemma integral_density {k : ℕ} {b : ℝ} (hb : 0 < b) : (∫ y : E k, density b y)=1 := by
  unfold density
  rw [integral_const_mul,integral_kernel hb,inv_mul_cancel₀ (ne_of_gt (normalizer_pos k hb))]
lemma law_probability (k : ℕ) {b : ℝ} (hb : 0 < b) : IsProbabilityMeasure (law k b) := by
  constructor
  rw [law,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ]
  rw [←ofReal_integral_eq_lintegral_ofReal (integrable_density hb)
    (Filter.Eventually.of_forall (fun y => (density_pos hb y).le)),integral_density hb]
  norm_num

lemma integral_law {k : ℕ} {b : ℝ} (hb : 0 < b) {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E k → F) :
    (∫ y, f y ∂law k b) = ∫ y, density b y • f y := by
  have H := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (E k)))
    (f := fun y => ENNReal.ofReal (density b y)) (g := f)
    ((ENNReal.continuous_ofReal.comp (continuous_density k b)).measurable)
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  simpa only [law,ENNReal.toReal_ofReal (density_pos hb _).le] using H

lemma charFun_law {k : ℕ} {b : ℝ} (hb : 0 < b) (t : E k) :
    charFun (law k b) t=Complex.exp (-(‖t‖:ℂ)^2/(4*b)) := by
  rw [charFun_apply,integral_law hb]
  have he (y : E k) : density b y • Complex.exp (⟪y,t⟫*Complex.I)=
      ((normalizer k b)⁻¹:ℂ)*Complex.exp (-(b:ℂ)*‖y‖^2+Complex.I*⟪t,y⟫) := by
    rw [density,Complex.real_smul]
    push_cast
    rw [mul_assoc,←Complex.exp_add,real_inner_comm y t]
    congr 2
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb Complex.I t]
  have hc : (Real.pi/(b:ℂ))^((Module.finrank ℝ (E k):ℂ)/2)=(normalizer k b:ℂ) := by
    rw [normalizer,finrank_euclideanSpace_fin,←Complex.ofReal_div,Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  have hn : (normalizer k b:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (normalizer_pos k hb)
  rw [hc,←mul_assoc,inv_mul_cancel₀ hn,one_mul]
  congr 1
  rw [Complex.I_sq]
  ring

lemma stdGaussian_eq_law (k : ℕ) : stdGaussian (E k)=law k (1/2) := by
  let := law_probability k (show (0:ℝ) < 1/2 by norm_num)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_stdGaussian,charFun_law (by norm_num)]
  congr 1
  push_cast
  ring


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace

lemma density_mul_exp {k : ℕ} (b t : ℝ) (y : E k) :
    density b y*Real.exp (t*‖y‖^2)=(normalizer k b)⁻¹*Real.exp (-(b-t)*‖y‖^2) := by
  unfold density
  rw [mul_assoc,←Real.exp_add]
  congr 2
  ring

lemma integrable_exp_norm_sq {k : ℕ} {b t : ℝ} (hb : 0 < b) (ht : t < b) :
    Integrable (fun y : E k => Real.exp (t*‖y‖^2)) (law k b) := by
  have H := integrable_withDensity_iff_integrable_smul' (μ := (volume : Measure (E k)))
    (f := fun y => ENNReal.ofReal (density b y)) (g := fun y => Real.exp (t*‖y‖^2))
    ((ENNReal.continuous_ofReal.comp (continuous_density k b)).measurable)
    (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  apply H.mpr
  simp only [ENNReal.toReal_ofReal (density_pos hb _).le,smul_eq_mul,density_mul_exp]
  exact (integrable_kernel (sub_pos.mpr ht)).const_mul _

lemma integral_exp_norm_sq {k : ℕ} {b t : ℝ} (hb : 0 < b) (ht : t < b) :
    (∫ y : E k, Real.exp (t*‖y‖^2) ∂law k b)=(normalizer k b)⁻¹*normalizer k (b-t) := by
  rw [integral_law hb]
  simp only [smul_eq_mul,density_mul_exp]
  rw [integral_const_mul,integral_kernel (sub_pos.mpr ht)]

lemma normalizer_eq_exp (k : ℕ) {b : ℝ} (hb : 0 < b) :
    normalizer k b=Real.exp (((k:ℝ)/2)*(Real.log Real.pi-Real.log b)) := by
  unfold normalizer
  rw [Real.rpow_def_of_pos (div_pos Real.pi_pos hb),Real.log_div Real.pi_ne_zero (ne_of_gt hb)]
  congr 1
  ring

lemma stdGaussian_laplace_norm_sq {k : ℕ} {a : ℝ} (ha : a < 1) :
    (∫ y : E k, Real.exp (a*‖y‖^2/2) ∂stdGaussian (E k))=
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)) := by
  rw [stdGaussian_eq_law]
  have he (y : E k) : a*‖y‖^2/2=(a/2)*‖y‖^2 := by ring
  simp_rw [he]
  rw [integral_exp_norm_sq (by norm_num) (by linarith),
    normalizer_eq_exp k (by norm_num),normalizer_eq_exp k (by linarith),
    ←Real.exp_neg,←Real.exp_add]
  have hl : Real.log ((1:ℝ)/2-a/2)=Real.log ((1:ℝ)/2)+Real.log (1-a) := by
    rw [show (1:ℝ)/2-a/2=(1/2)*(1-a) by ring,Real.log_mul (by norm_num) (by linarith)]
  rw [hl]
  congr 1
  ring

lemma stdGaussian_integrable_exp_norm_sq {k : ℕ} {a : ℝ} (ha : a < 1) :
    Integrable (fun y : E k => Real.exp (a*‖y‖^2/2)) (stdGaussian (E k)) := by
  rw [stdGaussian_eq_law]
  have he (y : E k) : a*‖y‖^2/2=(a/2)*‖y‖^2 := by ring
  simp_rw [he]
  exact integrable_exp_norm_sq (by norm_num) (by linarith)


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter GaussianFourier
open scoped ENNReal RealInnerProductSpace Topology

lemma integral_real_quadratic {k : ℕ} {b : ℝ} (hb : 0 < b) (c : ℝ) (w : E k) :
    (∫ y : E k, Real.exp (-b*‖y‖^2+c*⟪w,y⟫))=
      normalizer k b*Real.exp (c^2*‖w‖^2/(4*b)) := by
  have H := integral_cexp_neg_mul_sq_norm_add (V := E k) (b := (b:ℂ)) hb (c:ℂ) w
  have hc : (Real.pi/(b:ℂ))^((Module.finrank ℝ (E k):ℂ)/2)=(normalizer k b:ℂ) := by
    rw [normalizer,finrank_euclideanSpace_fin,←Complex.ofReal_div,Complex.ofReal_cpow (by positivity)]
    push_cast
    rfl
  rw [hc] at H
  apply Complex.ofReal_injective
  rw [←integral_complex_ofReal]
  convert H using 1 <;> push_cast <;> rfl

lemma normalizer_ratio_half (k : ℕ) {v : ℝ} (hv : 0 < v) :
    (normalizer k (1/2))⁻¹*normalizer k (v/2)=Real.exp (-((k:ℝ)/2)*Real.log v) := by
  rw [normalizer_eq_exp k (by norm_num),normalizer_eq_exp k (by positivity),←Real.exp_neg,←Real.exp_add]
  have hh : Real.log (v/2)= Real.log ((1:ℝ)/2)+Real.log v := by
    rw [show v/2=(1/2)*v by ring,Real.log_mul (by norm_num) (ne_of_gt hv)]
  rw [hh]
  congr 1
  ring

lemma gaussian_convolution_kernel {k : ℕ} (a r : ℝ) (y : E k) :
    (∫ z : E k, Real.exp (-r^2*‖y-a•z‖^2/2) ∂stdGaussian (E k))=
      Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*a^2)-r^2*‖y‖^2/(2*(1+r^2*a^2))) := by
  have hv : 0 < 1+r^2*a^2 := by positivity
  rw [stdGaussian_eq_law,integral_law (by norm_num)]
  have he (z : E k) : density (1/2) z • Real.exp (-r^2*‖y-a•z‖^2/2)=
      ((normalizer k (1/2))⁻¹*Real.exp (-r^2*‖y‖^2/2))*
        Real.exp (-((1+r^2*a^2)/2)*‖z‖^2+(r^2*a)*⟪y,z⟫) := by
    rw [density,smul_eq_mul,mul_assoc,←Real.exp_add,mul_assoc,←Real.exp_add]
    congr 2
    rw [norm_sub_sq_real,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,inner_smul_right]
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_real_quadratic (show 0 < (1+r^2*a^2)/2 by positivity)]
  have hre : ((normalizer k (1/2))⁻¹*Real.exp (-r^2*‖y‖^2/2))*
      (normalizer k ((1+r^2*a^2)/2)*Real.exp ((r^2*a)^2*‖y‖^2/(4*((1+r^2*a^2)/2))))=
      ((normalizer k (1/2))⁻¹*normalizer k ((1+r^2*a^2)/2))*
        (Real.exp (-r^2*‖y‖^2/2)*Real.exp ((r^2*a)^2*‖y‖^2/(4*((1+r^2*a^2)/2)))) := by ring
  rw [hre,normalizer_ratio_half k hv,←Real.exp_add,←Real.exp_add]
  congr 1
  field_simp
  ring


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter GaussianDensity
open SingleLatticeCovering.Isotropization
open scoped ENNReal RealInnerProductSpace Topology

lemma colApply_gaussian_law {n k : ℕ} (x : Isotropization.E n) :
    (stdGaussian (MatrixSpace n k)).map (fun g => colApply g x)=
      (stdGaussian (Isotropization.E k)).map (fun y => ‖x‖•y) := by
  have hm : Measurable (fun g : MatrixSpace n k => colApply g x) :=
    (continuous_colApply.comp (continuous_id.prodMk continuous_const)).measurable
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,integral_map hm.aemeasurable (by fun_prop),
    charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have he (g : MatrixSpace n k) : ⟪colApply g x,t⟫=⟪g,tensor x t⟫ := by
    rw [inner_colApply]
    exact (real_inner_comm _ _).trans (inner_rowApply g x t)
  have he' (y : Isotropization.E k) : (‖x‖*⟪y,t⟫ : ℝ)=⟪y,‖x‖•t⟫ := by rw [inner_smul_right]
  simp only [he,inner_smul_left,conj_trivial,he',←charFun_apply,charFun_stdGaussian]
  congr 1
  rw [←Complex.ofReal_pow,←Complex.ofReal_pow,norm_tensor_sq,norm_smul,
    Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),mul_pow]

lemma kernel_normalization {k : ℕ} {r : ℝ} (hr : r ≠ 0) (a : ℝ) (y : Isotropization.E k) :
    (normalizer k (r^2/2))⁻¹*
      Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*a^2)-r^2*‖y‖^2/(2*(1+r^2*a^2)))=
      density (1/(2*(a^2+1/r^2))) y := by
  have hr2 : 0 < r^2 := sq_pos_of_ne_zero hr
  have hv : 0 < a^2+1/r^2 := by positivity
  have hv' : 0 < 1+r^2*a^2 := by positivity
  have hb : 0 < 1/(2*(a^2+1/r^2)) := by positivity
  have hlog : Real.log (1/(2*(a^2+1/r^2)))=
      Real.log (r^2/2)-Real.log (1+r^2*a^2) := by
    rw [←Real.log_div (by positivity) (ne_of_gt hv')]
    congr 1
    field_simp
    ring
  rw [density,normalizer_eq_exp k (by positivity),normalizer_eq_exp k hb,
    ←Real.exp_neg,←Real.exp_neg,←Real.exp_add,←Real.exp_add,hlog]
  congr 1
  field_simp
  ring

lemma radialSmoothedDensity_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s r : ℝ) (y : Isotropization.E k) :
    radialSmoothedDensity μ s r y=
      ∫ x, Real.exp (-((k:ℝ)/2)*Real.log (1+r^2*(s*‖x‖)^2)-
        r^2*‖y‖^2/(2*(1+r^2*(s*‖x‖)^2))) ∂μ := by
  have hj : Integrable (fun p : MatrixSpace n k × Isotropization.E n =>
      Real.exp (-r^2*‖y-s•colApply p.1 p.2‖^2/2)) ((stdGaussian (MatrixSpace n k)).prod μ) := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc := continuous_colApply (n := n) (k := k)
      fun_prop)
    exact Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (y-s•colApply p.1 p.2))
  rw [radialSmoothedDensity,radialSmoothedModel_eq_average,Complex.ofReal_re]
  unfold smoothedProjection
  rw [integral_integral_swap hj]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hm : Measurable (fun g : MatrixSpace n k => colApply g x) :=
    (continuous_colApply.comp (continuous_id.prodMk continuous_const)).measurable
  dsimp only
  rw [←integral_map (μ := stdGaussian (MatrixSpace n k)) hm.aemeasurable (f := fun z => Real.exp (-r^2*‖y-s•z‖^2/2)) (by fun_prop),
    colApply_gaussian_law,integral_map (by fun_prop) (by fun_prop)]
  simp only [smul_smul]
  exact gaussian_convolution_kernel _ _ _

lemma normalized_radialSmoothedDensity_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Isotropization.E k) :
    (normalizer k (r^2/2))⁻¹*radialSmoothedDensity μ s r y=
      ∫ x, density (1/(2*((s*‖x‖)^2+1/r^2))) y ∂μ := by
  rw [radialSmoothedDensity_mixture,←integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun x => kernel_normalization hr _ _)


end SingleLatticeCovering.GaussianProjection





open MeasureTheory Filter Set
open scoped Topology
noncomputable section



namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung
open scoped ENNReal

lemma weighted_transport_inequality {u v a b : ℝ}
    (hu : 0 < u) (hv : 0 < v) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    u ≤ (a+b*(u/v))*(u^a*v^b) := by
  have hgm : (u/v)^b ≤ a+b*(u/v) := by
    simpa only [Real.one_rpow,one_mul,mul_one] using
      Real.geom_mean_le_arith_mean2_weighted ha hb (show (0:ℝ) ≤ 1 by norm_num)
        (div_pos hu hv).le hab
  have he : (u/v)^b*(u^a*v^b)=u := by
    rw [Real.div_rpow hu.le hv.le]
    have hpow : v^b ≠ 0 := (Real.rpow_pos_of_pos hv _).ne'
    calc
      u^b/v^b*(u^a*v^b) = u^a*u^b := by field_simp
      _ = u^(a+b) := (Real.rpow_add hu _ _).symm
      _ = u := by rw [hab,Real.rpow_one]
  calc
    u = (u/v)^b*(u^a*v^b) := he.symm
    _ ≤ (a+b*(u/v))*(u^a*v^b) := mul_le_mul_of_nonneg_right hgm (by positivity)




theorem positive_probability_lintegral (f g : PositiveDensity) {h : ℝ → ℝ}
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hh : ∀ x y, f x ^ a * g y ^ b ≤ h (a*x+b*y)) :
    1 ≤ ∫⁻ z, ENNReal.ofReal (h z) := by
  let T : ℝ → ℝ := densityTransport f g
  let W : ℝ → ℝ := fun x => a*x+b*T x
  let W' : ℝ → ℝ := fun x => a+b*(f x/g (T x))
  have hT : StrictMono T := (densityTransport f g).strictMono
  have hW : StrictMono W := by
    intro x y hxy
    exact add_lt_add (mul_lt_mul_of_pos_left hxy ha)
      (mul_lt_mul_of_pos_left (hT hxy) hb)
  have hd (x : ℝ) : HasDerivAt W (W' x) x := by
    simpa only [W,W',T,id_eq,Pi.add_def,mul_one] using
      ((hasDerivAt_id x).const_mul a).add ((densityTransport_hasDerivAt f g x).const_mul b)
  have hp (x : ℝ) : 0 < W' x := by
    dsimp [W']; exact add_pos ha (mul_pos hb (div_pos (f.positive x) (g.positive _)))
  have hi : (∫⁻ x, ENNReal.ofReal (f x))=1 := by
    rw [←ofReal_integral_eq_lintegral_ofReal f.integrable
      (Filter.Eventually.of_forall fun x => (f.positive x).le),f.integral_one]
    norm_num
  calc
    1 = ∫⁻ x, ENNReal.ofReal (f x) := hi.symm
    _ ≤ ∫⁻ x, ENNReal.ofReal |W' x| *ENNReal.ofReal (h (W x)) := by
      apply lintegral_mono
      intro x
      change ENNReal.ofReal (f x) ≤ ENNReal.ofReal |W' x| * ENNReal.ofReal (h (W x))
      rw [abs_of_pos (hp x),←ENNReal.ofReal_mul (hp x).le]
      apply ENNReal.ofReal_le_ofReal
      exact (weighted_transport_inequality (f.positive x) (g.positive (T x)) ha.le hb.le hab).trans
        (mul_le_mul_of_nonneg_left (hh x (T x)) (hp x).le)
    _ = ∫⁻ z in W '' univ, ENNReal.ofReal (h z) := by
      symm
      simpa using lintegral_image_eq_lintegral_abs_deriv_mul MeasurableSet.univ
        (fun x _ => (hd x).hasDerivWithinAt) hW.injective.injOn (fun z => ENNReal.ofReal (h z))
    _ ≤ ∫⁻ z, ENNReal.ofReal (h z) :=
      lintegral_mono' Measure.restrict_le_self (le_refl _)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open SingleLatticeCovering.SharpYoung SingleLatticeCovering.SimplexYoung
open scoped ENNReal



theorem positive_integral {f g h : ℝ → ℝ}
    (fc : Continuous f) (gc : Continuous g) (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x)
    (fi : Integrable f volume) (gi : Integrable g volume) (hi : Integrable h volume)
    (hn : ∀ x, 0 ≤ h x) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a*x+b*y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  let F := normalizePositiveDensity f fc fp fi
  let G := normalizePositiveDensity g gc gp gi
  let M := (∫ x, f x)^a*(∫ y, g y)^b
  have hfpos := integral_pos_of_continuous_density fp fi
  have hgpos := integral_pos_of_continuous_density gp gi
  have hM : 0 < M := mul_pos (Real.rpow_pos_of_pos hfpos _) (Real.rpow_pos_of_pos hgpos _)
  have hh : ∀ x y, F x^a*G y^b ≤ (h (a*x+b*y))/M := by
    intro x y
    dsimp [F,G,normalizePositiveDensity,M]
    rw [Real.div_rpow (fp x).le hfpos.le,Real.div_rpow (gp y).le hgpos.le,
      div_mul_div_comm]
    exact div_le_div_of_nonneg_right (hfg x y) hM.le
  have hineq := positive_probability_lintegral F G (h := fun z => h z/M) ha hb hab hh
  rw [←ofReal_integral_eq_lintegral_ofReal (hi.div_const M)
    (Filter.Eventually.of_forall (fun z => div_nonneg (hn z) hM.le)),integral_div] at hineq
  have ht : (1:ℝ) ≤ (∫ z, h z)/M := by
    exact (ENNReal.ofReal_le_ofReal_iff (div_nonneg (integral_nonneg hn) hM.le)).mp (by simpa using hineq)
  have := (le_div_iff₀ hM).mp ht
  simpa only [one_mul] using this


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma gaussianKernel_prod (d : ℕ) (c : ℝ) (x : RV d) :
    gaussianKernel d c x = ∏ i, Real.exp (-c*(x i)^2) := by
  rw [gaussianKernel,Finset.mul_sum,Real.exp_sum]

lemma gaussianKernel_le_one (d : ℕ) {c : ℝ} (hc : 0 ≤ c) (x : RV d) :
    gaussianKernel d c x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc) (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma integrable_gaussianKernel (d : ℕ) {c : ℝ} (hc : 0 < c) :
    Integrable (gaussianKernel d c) volume := by
  have H : Integrable (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) volume :=
    Integrable.fintype_prod (fun _ : Fin d => integrable_exp_neg_mul_sq hc)
  have he : gaussianKernel d c = (fun x : RV d => ∏ i, Real.exp (-c*(x i)^2)) :=
    funext (gaussianKernel_prod d c)
  rw [he]
  exact H

lemma gaussianKernel_cons (d : ℕ) (c t : ℝ) (y : RV d) :
    gaussianKernel (d+1) c (Fin.cons t y)=Real.exp (-c*t^2)*gaussianKernel d c y := by
  simp only [gaussianKernel,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,mul_add,Real.exp_add]



lemma GaussianBound.integrable {d : ℕ} {f : RV d → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Integrable f volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_gaussianKernel d hc').const_mul A).mono' hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hb x)

lemma gaussian_slice_dominant {d : ℕ} {f : RV (d+1) → ℝ} {A c : ℝ}
    (hA : 0 ≤ A) (hc : 0 ≤ c) (hbound : ∀ x, |f x| ≤ A*gaussianKernel (d+1) c x)
    (y : RV d) (t : ℝ) : |f (Fin.cons t y)| ≤ A*Real.exp (-c*t^2) := by
  calc
    _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hbound _
    _ = (A*Real.exp (-c*t^2))*gaussianKernel d c y := by rw [gaussianKernel_cons,mul_assoc]
    _ ≤ A*Real.exp (-c*t^2) := mul_le_of_le_one_right (by positivity) (gaussianKernel_le_one d hc y)

lemma GaussianBound.integrable_slice {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (y : RV d) :
    Integrable (fun t : ℝ => f (Fin.cons t y)) volume := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply ((integrable_exp_neg_mul_sq hc').const_mul A).mono'
    (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun t => by
    simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)

lemma GaussianBound.continuous_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : Continuous (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  apply continuous_of_dominated
      (bound := fun t : ℝ => A*Real.exp (-c*t^2))
  · intro y
    exact (hc.comp (continuous_id.finCons continuous_const)).aestronglyMeasurable
  · intro y
    exact Filter.Eventually.of_forall (fun t => by
      simpa only [Real.norm_eq_abs,Function.comp_def,id_eq] using gaussian_slice_dominant hA.le hc'.le hb y t)
  · exact (integrable_exp_neg_mul_sq hc').const_mul A
  · exact Filter.Eventually.of_forall (fun t => hc.comp (continuous_const.finCons continuous_id))

lemma marginalOne_positive {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) (hp : ∀ x, 0 < f x) (y : RV d) :
    0 < marginalOne f y :=
  SingleLatticeCovering.SimplexYoung.integral_pos_of_continuous_density
    (fun t => hp (Fin.cons t y)) (hf.integrable_slice hc y)

lemma GaussianBound.for_marginalOne {d : ℕ} {f : RV (d+1) → ℝ}
    (hf : GaussianBound f) (hc : Continuous f) : GaussianBound (marginalOne f) := by
  obtain ⟨A,c,hA,hc',hb⟩ := hf
  have hg : GaussianBound f := ⟨A,c,hA,hc',hb⟩
  refine ⟨A*Real.sqrt (Real.pi/c),c,mul_pos hA (Real.sqrt_pos.mpr (div_pos Real.pi_pos hc')),hc',?_⟩
  intro y
  have hi := hg.integrable_slice hc y
  calc
    |marginalOne f y| ≤ ∫ t, |f (Fin.cons t y)| := by
      simpa only [Real.norm_eq_abs,marginalOne] using norm_integral_le_integral_norm (fun t => f (Fin.cons t y))
    _ ≤ ∫ t, (A*gaussianKernel d c y)*Real.exp (-c*t^2) := by
      apply integral_mono hi.norm ((integrable_exp_neg_mul_sq hc').const_mul _)
      intro t
      calc
        _ ≤ A*gaussianKernel (d+1) c (Fin.cons t y) := hb _
        _ = _ := by rw [gaussianKernel_cons]; ring
    _ = (A*Real.sqrt (Real.pi/c))*gaussianKernel d c y := by
      rw [integral_const_mul,integral_gaussian]
      ring

lemma integral_marginalOne {d : ℕ} {f : RV (d+1) → ℝ} (hi : Integrable f volume) :
    (∫ y, marginalOne f y) = ∫ x, f x := by
  have hm := (volume_preserving_piFinSuccAbove (fun _ : Fin (d+1) => ℝ) 0).symm
  have he := hm.integral_comp' f
  have hj := (hm.integrable_comp hi.aestronglyMeasurable).mpr hi
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv_zero,Function.comp_def] at he hj
  rw [←he]
  exact (integral_prod_symm (fun p : ℝ × RV d => f (Fin.cons p.1 p.2)) hj).symm


end SingleLatticeCovering.Prekopa


end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_LogConcavity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators

lemma integral_RV_zero (f : RV 0 → ℝ) : (∫ x, f x)=f 0 := by
  rw [Measure.volume_pi_eq_dirac (0 : RV 0), integral_dirac]

lemma cons_weighted {d : ℕ} (a b x y : ℝ) (u v : RV d) :
    Fin.cons (a*x+b*y) (a•u+b•v) = a•Fin.cons x u+b•Fin.cons y v := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl




theorem gaussian_dominated_integral (d : ℕ) {f g h : RV d → ℝ}
    (fc : Continuous f) (gc : Continuous g) (hc : Continuous h)
    (fp : ∀ x, 0 < f x) (gp : ∀ x, 0 < g x) (hp : ∀ x, 0 < h x)
    (fb : GaussianBound f) (gb : GaussianBound g) (hb : GaussianBound h)
    {a b : ℝ} (ha : 0 < a) (hb' : 0 < b) (hab : a+b=1)
    (hfg : ∀ x y, f x^a*g y^b ≤ h (a•x+b•y)) :
    (∫ x, f x)^a*(∫ y, g y)^b ≤ ∫ z, h z := by
  induction d with
  | zero =>
    simp only [integral_RV_zero]
    have H := hfg 0 0
    simpa only [smul_zero,add_zero] using H
  | succ d ih =>
    have hm : ∀ y z : RV d,
        (marginalOne f y)^a*(marginalOne g z)^b ≤ marginalOne h (a•y+b•z) := by
      intro y z
      apply positive_integral
        (fc.comp (show Continuous (fun t : ℝ => Fin.cons t y) by fun_prop))
        (gc.comp (show Continuous (fun t : ℝ => Fin.cons t z) by fun_prop))
        (fun t => fp (Fin.cons t y)) (fun t => gp (Fin.cons t z))
        (fb.integrable_slice fc _) (gb.integrable_slice gc _) (hb.integrable_slice hc _)
        (fun t => (hp _).le) ha hb' hab
      intro t u
      simpa only [cons_weighted,Function.comp_def,id_eq] using hfg (Fin.cons t y) (Fin.cons u z)
    have H := ih (fb.continuous_marginalOne fc) (gb.continuous_marginalOne gc)
      (hb.continuous_marginalOne hc) (marginalOne_positive fb fc fp)
      (marginalOne_positive gb gc gp) (marginalOne_positive hb hc hp)
      (fb.for_marginalOne fc) (gb.for_marginalOne gc) (hb.for_marginalOne hc) hm
    simpa only [integral_marginalOne (fb.integrable fc),integral_marginalOne (gb.integrable gc),
      integral_marginalOne (hb.integrable hc)] using H


end SingleLatticeCovering.Prekopa

noncomputable section
namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma sum_sq_le_norm_sq (d : ℕ) (x : RV d) :
    (∑ i, (x i)^2) ≤ (d : ℝ)*‖x‖^2 := by
  calc
    _ ≤ ∑ _ : Fin d, ‖x‖^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hi := norm_le_pi_norm x i
      simpa only [Real.norm_eq_abs,sq_abs] using pow_le_pow_left₀ (norm_nonneg (x i)) hi 2
    _ = _ := by simp

lemma softIndicator_positive {d : ℕ} (K : Set (RV d)) (t : ℝ) (x : RV d) :
    0 < softIndicator K t x := Real.exp_pos _

lemma continuous_softIndicator {d : ℕ} (K : Set (RV d)) (t : ℝ) :
    Continuous (softIndicator K t) := by
  unfold softIndicator
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_infDist_pt K).pow 2))

lemma softIndicator_gaussianBound {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) {t : ℝ} (ht : 0 < t) : GaussianBound (softIndicator K t) := by
  obtain ⟨R,hR,hb⟩ := hK.isBounded.exists_pos_norm_le
  refine ⟨Real.exp (t*R^2),t/(2*((d : ℝ)+1)),Real.exp_pos _,by positivity,?_⟩
  intro x
  obtain ⟨u,hu,he⟩ := hK.exists_infDist_eq_dist hne x
  have hn : ‖x‖ ≤ infDist x K+R := by
    calc
      ‖x‖ ≤ ‖x-u‖+‖u‖ := by simpa only [add_comm] using norm_le_insert' x u
      _ ≤ infDist x K+R := by rw [he,dist_eq_norm]; exact add_le_add_right (hb u hu) _
  have hs : ‖x‖^2 ≤ 2*((infDist x K)^2+R^2) := by
    have hn' := pow_le_pow_left₀ (norm_nonneg x) hn 2
    nlinarith [sq_nonneg (infDist x K-R)]
  have hs' : (∑ i, (x i)^2) ≤ 2*((d : ℝ)+1)*((infDist x K)^2+R^2) := by
    calc
      _ ≤ (d : ℝ)*‖x‖^2 := sum_sq_le_norm_sq d x
      _ ≤ (d : ℝ)*(2*((infDist x K)^2+R^2)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ _ := by nlinarith [sq_nonneg (infDist x K),sq_nonneg R]
  rw [abs_of_pos (softIndicator_positive K t x),softIndicator,gaussianKernel,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hd : 0 < 2*((d : ℝ)+1) := by positivity
  have hm := mul_le_mul_of_nonneg_left hs' (div_nonneg ht.le hd.le)
  field_simp at hm ⊢
  nlinarith

lemma infDist_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    infDist (a•x+b•y) C ≤ a*infDist x A+b*infDist y B := by
  obtain ⟨u,hu,heu⟩ := hA.exists_infDist_eq_dist hneA x
  obtain ⟨v,hv,hev⟩ := hB.exists_infDist_eq_dist hneB y
  calc
    _ ≤ dist (a•x+b•y) (a•u+b•v) := infDist_le_dist_of_mem (hABC u hu v hv)
    _ = ‖a•(x-u)+b•(y-v)‖ := by rw [dist_eq_norm]; congr 1; module
    _ ≤ ‖a•(x-u)‖+‖b•(y-v)‖ := norm_add_le _ _
    _ = _ := by rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
      abs_of_nonneg ha,abs_of_nonneg hb,heu,hev,dist_eq_norm,dist_eq_norm]

lemma softIndicator_weighted {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hneA : A.Nonempty) (hneB : B.Nonempty)
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) (ht : 0 ≤ t)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) (x y : RV d) :
    (softIndicator A t x)^a*(softIndicator B t y)^b ≤ softIndicator C t (a•x+b•y) := by
  have H := infDist_weighted hA hB hneA hneB ha hb hABC x y
  have hsq : (infDist (a•x+b•y) C)^2 ≤ a*(infDist x A)^2+b*(infDist y B)^2 := by
    have HH := pow_le_pow_left₀ (infDist_nonneg : 0 ≤ infDist (a•x+b•y) C) H 2
    have hm := mul_nonneg (mul_nonneg ha hb) (sq_nonneg (infDist x A-infDist y B))
    nlinarith [sq_nonneg (a*infDist x A+b*infDist y B),sq_nonneg (infDist x A),sq_nonneg (infDist y B)]
  simp only [softIndicator,←Real.exp_mul,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_nonneg ht (sub_nonneg.mpr hsq)]



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric
open scoped ENNReal Topology BigOperators

lemma softIndicator_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsClosed K)
    (hne : K.Nonempty) (x : RV d) :
    Tendsto (fun n : ℕ => softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (K.indicator (fun _ => (1:ℝ)) x)) := by
  by_cases hx : x ∈ K
  · simp only [softIndicator,infDist_zero_of_mem hx,zero_pow (by omega : 2 ≠ 0),
      mul_zero,Real.exp_zero,Set.indicator_of_mem hx]
    exact tendsto_const_nhds
  · rw [Set.indicator_of_notMem hx]
    have hd : 0 < (infDist x K)^2 := sq_pos_of_pos ((hK.notMem_iff_infDist_pos hne).mp hx)
    have hq : Real.exp (-(infDist x K)^2)<1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hd)
    have H := (tendsto_pow_atTop_nhds_zero_of_lt_one (Real.exp_pos (-(infDist x K)^2)).le hq).mul_const
      (Real.exp (-(infDist x K)^2))
    simp only [zero_mul] at H
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    ext n
    rw [softIndicator,←Real.exp_nat_mul,←Real.exp_add]
    congr 1
    ring

lemma softIndicator_antitone {d : ℕ} (K : Set (RV d)) (x : RV d) :
    Antitone (fun t : ℝ => softIndicator K t x) := by
  intro t u htu
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonneg_right (neg_le_neg htu) (sq_nonneg _)

lemma softIndicator_integral_tendsto {d : ℕ} {K : Set (RV d)} (hK : IsCompact K)
    (hne : K.Nonempty) :
    Tendsto (fun n : ℕ => ∫ x, softIndicator K ((n : ℝ)+1) x) atTop
      (𝓝 (volume K).toReal) := by
  have H := tendsto_integral_of_dominated_convergence (softIndicator K 1)
    (fun n => (continuous_softIndicator K ((n : ℝ)+1)).aestronglyMeasurable)
    ((softIndicator_gaussianBound hK hne zero_lt_one).integrable (continuous_softIndicator K 1))
    (fun n => Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (softIndicator_positive K _ x)]
      exact softIndicator_antitone K x (by nlinarith [Nat.cast_nonneg (α := ℝ) n] : (1:ℝ) ≤ (n : ℝ)+1)))
    (Filter.Eventually.of_forall (softIndicator_tendsto hK.isClosed hne))
  simpa only [integral_indicator hK.measurableSet,integral_const,smul_eq_mul,mul_one,measureReal_def,Measure.restrict_apply_univ] using H




theorem compact_volume {d : ℕ} {A B C : Set (RV d)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hABC : ∀ u ∈ A, ∀ v ∈ B, a•u+b•v ∈ C) :
    ((volume A).toReal)^a*((volume B).toReal)^b ≤ (volume C).toReal := by
  rcases A.eq_empty_or_nonempty with rfl | hneA
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt ha),zero_mul]
    exact ENNReal.toReal_nonneg
  rcases B.eq_empty_or_nonempty with rfl | hneB
  · simp only [measure_empty,ENNReal.toReal_zero,Real.zero_rpow (ne_of_gt hb),mul_zero]
    exact ENNReal.toReal_nonneg
  have hneC : C.Nonempty := by
    obtain ⟨u,hu⟩ := hneA
    obtain ⟨v,hv⟩ := hneB
    exact ⟨a•u+b•v,hABC u hu v hv⟩
  have hpoint : ∀ n : ℕ,
      (∫ x, softIndicator A ((n : ℝ)+1) x)^a*
      (∫ x, softIndicator B ((n : ℝ)+1) x)^b ≤ ∫ x, softIndicator C ((n : ℝ)+1) x := by
    intro n
    have hn : 0 < (n : ℝ)+1 := by positivity
    apply gaussian_dominated_integral d (continuous_softIndicator _ _) (continuous_softIndicator _ _)
      (continuous_softIndicator _ _) (softIndicator_positive _ _) (softIndicator_positive _ _)
      (softIndicator_positive _ _) (softIndicator_gaussianBound hA hneA hn)
      (softIndicator_gaussianBound hB hneB hn) (softIndicator_gaussianBound hC hneC hn) ha hb hab
    exact softIndicator_weighted hA hB hneA hneB ha.le hb.le hab hn.le hABC
  exact le_of_tendsto_of_tendsto
    (((Real.continuous_rpow_const ha.le).tendsto _).comp (softIndicator_integral_tendsto hA hneA) |>.mul
      (((Real.continuous_rpow_const hb.le).tendsto _).comp (softIndicator_integral_tendsto hB hneB)))
    (softIndicator_integral_tendsto hC hneC) (Filter.Eventually.of_forall hpoint)


end SingleLatticeCovering.Prekopa




namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators




theorem logConcave_section_volume {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => (volume (fiber K y)).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun x y a b ha hb hab => ?_⟩
  apply compact_volume (fiber_compact hK x) (fiber_compact hK y)
    (fiber_compact hK (a•x+b•y)) ha hb hab
  intro u hu v hv
  have H := hconv hu hv ha.le hb.le hab
  exact H

lemma LogConcave.const_mul {D : ℕ} {f : E D → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : LogConcave (fun x => c*f x) := by
  refine ⟨fun x => mul_nonneg hc (hf.1 x),fun x y a b ha hb hab => ?_⟩
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul,Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb),le_refl]
  · rw [Real.mul_rpow hc.le (hf.1 x),Real.mul_rpow hc.le (hf.1 y)]
    calc
      c^a*f x^a*(c^b*f y^b) = (c^a*c^b)*(f x^a*f y^b) := by ring
      _ = c*(f x^a*f y^b) := by rw [←Real.rpow_add hc,hab,Real.rpow_one]
      _ ≤ c*f (a•x+b•y) := mul_le_mul_of_nonneg_left (hf.2 x y a b ha hb hab) hc.le



theorem logConcave_canonical_density {m D : ℕ} {K : Set (RV m × E D)}
    (hK : IsCompact K) (hconv : Convex ℝ K) :
    LogConcave (fun y => ((volume K)⁻¹).toReal*(volume (fiber K y)).toReal) :=
  LogConcave.const_mul (logConcave_section_volume hK hconv) ENNReal.toReal_nonneg



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma ScalarLogConcave.const_mul {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    {c : ℝ} (hc : 0 ≤ c) : ScalarLogConcave (fun t => c*f t) := by
  refine ⟨fun t => mul_nonneg hc (hf.1 t),fun u v a b ha hb hab => ?_⟩
  rcases hc.eq_or_lt with rfl | hc
  · simp only [zero_mul,Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb),le_refl]
  rw [Real.mul_rpow hc.le (hf.1 u),Real.mul_rpow hc.le (hf.1 v)]
  calc
    c^a*f u^a*(c^b*f v^b) = (c^a*c^b)*(f u^a*f v^b) := by ring
    _ = c*(f u^a*f v^b) := by rw [←Real.rpow_add hc,hab,Real.rpow_one]
    _ ≤ c*f (a*u+b*v) := mul_le_mul_of_nonneg_left (hf.2 u v a b ha hb hab) hc.le

lemma ScalarLogConcave.log_interpolation {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    {u v a b : ℝ} (hu : 0 < f u) (hv : 0 < f v)
    (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    a*Real.log (f u)+b*Real.log (f v) ≤ Real.log (f (a*u+b*v)) := by
  have hp : 0 < f u^a*f v^b := mul_pos (Real.rpow_pos_of_pos hu _) (Real.rpow_pos_of_pos hv _)
  have H := Real.log_le_log hp (hf.2 u v a b ha hb hab)
  rwa [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hu _)) (ne_of_gt (Real.rpow_pos_of_pos hv _)),
    Real.log_rpow hu,Real.log_rpow hv] at H



theorem ScalarLogConcave.exponential_tail {f : ℝ → ℝ} (hf : ScalarLogConcave f)
    (hle : ∀ t, f t ≤ 1) (hleft : (3:ℝ)/4 ≤ f (-2)) (hright : f 2 ≤ (1:ℝ)/4)
    {t : ℝ} (ht : 0 ≤ t) : f t ≤ Real.exp (1-t/16) := by
  have _ := ht
  by_cases ht2 : t ≤ 2
  · exact (hle t).trans (Real.one_le_exp (by linarith))
  have ht2 : 2 < t := lt_of_not_ge ht2
  rcases (hf.1 t).eq_or_lt with hzero | hpos
  · rw [←hzero]; exact (Real.exp_pos _).le
  have hleftpos : 0 < f (-2) := by linarith
  let a := (t-2)/(t+2)
  let b := 4/(t+2)
  have htp : 0 < t+2 := by linarith
  have ha : 0 < a := div_pos (by linarith) htp
  have hb : 0 < b := div_pos (by norm_num) htp
  have hab : a+b=1 := by dsimp [a,b]; field_simp; ring
  have hinter : a*(-2)+b*t=2 := by dsimp [a,b]; field_simp; ring
  have H := hf.log_interpolation hleftpos hpos ha hb hab
  rw [hinter] at H
  have hl : -(1:ℝ)/2 ≤ Real.log (f (-2)) := by
    have A := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 3/4 by norm_num)
    have B := Real.log_le_log (show (0:ℝ) < 3/4 by norm_num) hleft
    norm_num at A
    linarith
  have h2pos : 0 < f 2 := by
    have HH := hf.2 (-2) t a b ha hb hab
    rw [hinter] at HH
    exact (mul_pos (Real.rpow_pos_of_pos hleftpos _) (Real.rpow_pos_of_pos hpos _)).trans_le HH
  have hr : Real.log (f 2) ≤ -(3:ℝ)/4 := by
    have A := Real.log_le_log h2pos hright
    have B := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1/4 by norm_num)
    linarith
  have H' : a*(-(1:ℝ)/2)+b*Real.log (f t) ≤ -(3:ℝ)/4 := by
    have A := mul_le_mul_of_nonneg_left hl ha.le
    linarith
  have H'' := mul_le_mul_of_nonneg_right H' htp.le
  have haeq : a*(t+2)=t-2 := div_mul_cancel₀ _ (ne_of_gt htp)
  have hbeq : b*(t+2)=4 := div_mul_cancel₀ _ (ne_of_gt htp)
  have hcalc : (a*(-(1:ℝ)/2)+b*Real.log (f t))*(t+2)=
      (t-2)*(-(1:ℝ)/2)+4*Real.log (f t) := by
    calc
      _ = (a*(t+2))*(-(1:ℝ)/2)+(b*(t+2))*Real.log (f t) := by ring
      _ = _ := by rw [haeq,hbeq]
  rw [hcalc] at H''
  have hlog : Real.log (f t) ≤ 1-t/16 := by linarith
  simpa only [Real.exp_log hpos] using Real.exp_le_exp.mpr hlog



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma right_derivative_nonpos_of_max {F : ℝ → ℝ} {A : ℝ}
    (hF : HasDerivAt F A 0) (hmax : ∀ t ∈ Ioo (0:ℝ) 1, F t ≤ F 0) : A ≤ 0 := by
  apply le_of_tendsto hF.tendsto_slope_zero_right
  have hnear : ∀ᶠ t : ℝ in 𝓝[>] 0, t < 1 := nhdsWithin_le_nhds (Iio_mem_nhds (show (0:ℝ) < 1 by norm_num))
  filter_upwards [self_mem_nhdsWithin,hnear] with t ht ht1
  simp only [zero_add,smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (le_of_lt ht)) (sub_nonpos.mpr (hmax t ⟨ht,ht1⟩))



theorem ScalarLogConcave.log_bound_at_weighted_mode {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 < r)
    (hφ₀ : 0 < φ r₀) (hφr : 0 < φ r)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀) :
    Real.log (φ r)-Real.log (φ r₀) ≤ -(m:ℝ)*(r-r₀)/r₀ := by
  let F : ℝ → ℝ := fun t => (m:ℝ)*Real.log ((1-t)*r₀+t*r)+
    (1-t)*Real.log (φ r₀)+t*Real.log (φ r)
  have hdlin : HasDerivAt (fun t : ℝ => (1-t)*r₀+t*r) (r-r₀) 0 := by
    convert! (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).mul_const r₀).add
      ((hasDerivAt_id (0:ℝ)).mul_const r) using 1 ;       simp only [zero_sub,neg_one_mul,one_mul] ; ring
  have hdlog := hdlin.log (by simpa using ne_of_gt hr₀)
  have hd : HasDerivAt F ((m:ℝ)*(r-r₀)/r₀-Real.log (φ r₀)+Real.log (φ r)) 0 := by
    convert! ((hdlog.const_mul (m:ℝ)).add
      (((hasDerivAt_const (0:ℝ) (1:ℝ)).sub (hasDerivAt_id (0:ℝ))).mul_const (Real.log (φ r₀)))).add
      ((hasDerivAt_id (0:ℝ)).mul_const (Real.log (φ r))) using 1 ;       simp only [sub_zero,one_mul,zero_mul,add_zero,zero_sub,neg_one_mul] ; ring
  have hFmax : ∀ t ∈ Ioo (0:ℝ) 1, F t ≤ F 0 := by
    intro t ht
    let z := (1-t)*r₀+t*r
    have hz : 0 < z := add_pos (mul_pos (by linarith [ht.2]) hr₀) (mul_pos ht.1 hr)
    have hinter := hφ.log_interpolation hφ₀ hφr (show 0 < 1-t by linarith [ht.2]) ht.1 (by ring)
    change (1-t)*Real.log (φ r₀)+t*Real.log (φ r) ≤ Real.log (φ z) at hinter
    have hφz : 0 < φ z := by
      have H := hφ.2 r₀ r (1-t) t (by linarith [ht.2]) ht.1 (by ring)
      exact (mul_pos (Real.rpow_pos_of_pos hφ₀ _) (Real.rpow_pos_of_pos hφr _)).trans_le H
    have H := Real.log_le_log (mul_pos (pow_pos hz _) hφz) (hmax z hz)
    rw [Real.log_mul (ne_of_gt (pow_pos hz _)) (ne_of_gt hφz),
      Real.log_mul (ne_of_gt (pow_pos hr₀ _)) (ne_of_gt hφ₀),Real.log_pow,Real.log_pow] at H
    dsimp [F]
    simp only [sub_zero,one_mul,zero_mul,add_zero]
    change (m:ℝ)*Real.log z+((1-t)*Real.log (φ r₀))+t*Real.log (φ r) ≤ _
    linarith
  have H := right_derivative_nonpos_of_max hd hFmax
  rw [neg_mul,neg_div]
  linarith



theorem ScalarLogConcave.weighted_mode_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ r : ℝ} (hr₀ : 0 < r₀) (hr : 0 < r)
    (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀) :
    r^m*φ r ≤ (r₀^m*φ r₀)*Real.exp (-(m:ℝ)*shellRate (r/r₀)) := by
  rcases (hφ.1 r).eq_or_lt with hz | hp
  · rw [←hz,mul_zero]; positivity
  have H := hφ.log_bound_at_weighted_mode hr₀ hr hφ₀ hp hmax
  have hlog : Real.log (r^m*φ r) ≤ Real.log (r₀^m*φ r₀)-(m:ℝ)*shellRate (r/r₀) := by
    rw [Real.log_mul (ne_of_gt (pow_pos hr _)) (ne_of_gt hp),
      Real.log_mul (ne_of_gt (pow_pos hr₀ _)) (ne_of_gt hφ₀),Real.log_pow,Real.log_pow]
    rw [shellRate,Real.log_div (ne_of_gt hr) (ne_of_gt hr₀)]
    have he : (r-r₀)/r₀=r/r₀-1 := by field_simp
    rw [neg_mul,neg_div,mul_div_assoc,he] at H
    nlinarith
  have HE := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log (mul_pos (pow_pos hr _) hp),Real.exp_sub,
    Real.exp_log (mul_pos (pow_pos hr₀ _) hφ₀),div_eq_mul_inv,←Real.exp_neg] at HE
  simpa only [neg_mul] using HE


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma shellRate_ge_sqrt_sq {u : ℝ} (hu : 0 < u) : (Real.sqrt u-1)^2 ≤ shellRate u := by
  have H := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hu)
  rw [Real.log_sqrt hu.le] at H
  dsimp [shellRate]
  nlinarith [Real.sq_sqrt hu.le]

lemma shellRate_ge_sq_div_nine {u : ℝ} (hu : 0 < u) (hu2 : u ≤ 2) :
    (u-1)^2/9 ≤ shellRate u := by
  have hs := Real.sqrt_nonneg u
  have hs2 : Real.sqrt u ≤ 2 := by nlinarith [Real.sq_sqrt hu.le]
  have he : (u-1)^2=(Real.sqrt u-1)^2*(Real.sqrt u+1)^2 := by
    calc
      _ = ((Real.sqrt u)^2-1)^2 := by rw [Real.sq_sqrt hu.le]
      _ = _ := by ring
  have hsq : (Real.sqrt u+1)^2 ≤ 9 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hsq (sq_nonneg (Real.sqrt u-1))
  rw [←he] at hm
  nlinarith [shellRate_ge_sqrt_sq hu]

lemma shellRate_support {u a : ℝ} (hu : 0 < u) (ha : 0 < a) :
    shellRate a+(1-a⁻¹)*(u-a) ≤ shellRate u := by
  have H := Real.log_le_sub_one_of_pos (div_pos hu ha)
  rw [Real.log_div (ne_of_gt hu) (ne_of_gt ha)] at H
  have he : (1-a⁻¹)*(u-a)=u-a-u/a+1 := by field_simp; ring
  rw [he]
  dsimp [shellRate]
  linarith

lemma shellRate_upper_tail {ε u : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hu : 1+ε ≤ u) :
    ε^2/9+(ε/2)*(u-(1+ε)) ≤ shellRate u := by
  have ha : 0 < 1+ε := by linarith
  have hs := shellRate_support (show 0 < u by linarith) ha
  have hb := shellRate_ge_sq_div_nine ha (show 1+ε ≤ 2 by linarith)
  have hc : ε/2 ≤ 1-(1+ε)⁻¹ := by
    have he : (1-(1+ε)⁻¹)*(1+ε)=ε := by
      rw [sub_mul,one_mul,inv_mul_cancel₀ (ne_of_gt ha)]
      ring
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hc (sub_nonneg.mpr hu)
  nlinarith

lemma shellRate_lower_tail {ε u : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (hu : 0 < u) (hu1 : u ≤ 1-ε) :
    ε^2/9+(ε/2)*((1-ε)-u) ≤ shellRate u := by
  have ha : 0 < 1-ε := by linarith
  have hs := shellRate_support hu ha
  have hb := shellRate_ge_sq_div_nine ha (show 1-ε ≤ 2 by linarith)
  have hc : 1-(1-ε)⁻¹ ≤ -ε/2 := by
    have he : (1-(1-ε)⁻¹)*(1-ε) = -ε := by
      rw [sub_mul,one_mul,inv_mul_cancel₀ (ne_of_gt ha)]
      ring
    apply (mul_le_mul_iff_left₀ ha).mp
    nlinarith
  have hm := mul_le_mul_of_nonpos_right hc (sub_nonpos.mpr hu1)
  nlinarith



end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped Topology

lemma integral_exp_shift_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ r : ℝ in Ioi c, Real.exp (-a*(r-c)))=a⁻¹ := by
  have he (r : ℝ) : Real.exp (-a*(r-c))=Real.exp (a*c)*Real.exp (-a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_Ioi (by linarith)]
  rw [neg_div_neg_eq,div_eq_mul_inv,←mul_assoc,←Real.exp_add]
  simp

lemma integral_exp_shift_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    (∫ r : ℝ in Iic c, Real.exp (a*(r-c)))=a⁻¹ := by
  have he (r : ℝ) : Real.exp (a*(r-c))=Real.exp (-a*c)*Real.exp (a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  rw [integral_const_mul,integral_exp_mul_Iic ha]
  rw [div_eq_mul_inv,←mul_assoc,←Real.exp_add]
  simp

lemma integrableOn_exp_shift_Ioi {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (-a*(r-c))) (Ioi c) volume := by
  have he (r : ℝ) : Real.exp (-a*(r-c))=Real.exp (a*c)*Real.exp (-a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Ioi (by linarith) c).const_mul _

lemma integrableOn_exp_shift_Iic {a : ℝ} (ha : 0 < a) (c : ℝ) :
    IntegrableOn (fun r : ℝ => Real.exp (a*(r-c))) (Iic c) volume := by
  have he (r : ℝ) : Real.exp (a*(r-c))=Real.exp (-a*c)*Real.exp (a*r) := by
    rw [←Real.exp_add]; congr 1; ring
  simp_rw [he]
  exact (integrableOn_exp_mul_Iic ha c).const_mul _

lemma ScalarLogConcave.upper_shell_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ ε r : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hr : (1+ε)*r₀ ≤ r) :
    r^m*φ r ≤ (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
      Real.exp (-((m:ℝ)*ε/(2*r₀))*(r-(1+ε)*r₀)) := by
  have hrp : 0 < r := (mul_pos (by linarith) hr₀).trans_le hr
  have hu : 1+ε ≤ r/r₀ := (le_div_iff₀ hr₀).mpr hr
  have H := mul_le_mul_of_nonpos_left (shellRate_upper_tail hε hε1 hu)
    (neg_nonpos.mpr (Nat.cast_nonneg m))
  have E := hφ.weighted_mode_envelope hr₀ hrp hφ₀ hmax
  apply E.trans
  rw [mul_assoc (r₀^m*φ r₀),←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hr₀.le _) hφ₀.le)
  apply Real.exp_le_exp.mpr
  exact H.trans_eq (by field_simp; ring)

lemma ScalarLogConcave.lower_shell_envelope {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} {r₀ ε r : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hr : 0 < r) (hr1 : r ≤ (1-ε)*r₀) :
    r^m*φ r ≤ (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
      Real.exp (((m:ℝ)*ε/(2*r₀))*(r-(1-ε)*r₀)) := by
  have hu : r/r₀ ≤ 1-ε := (div_le_iff₀ hr₀).mpr hr1
  have H := mul_le_mul_of_nonpos_left (shellRate_lower_tail hε hε1 (div_pos hr hr₀) hu)
    (neg_nonpos.mpr (Nat.cast_nonneg m))
  have E := hφ.weighted_mode_envelope hr₀ hr hφ₀ hmax
  apply E.trans
  rw [mul_assoc (r₀^m*φ r₀),←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (pow_nonneg hr₀.le _) hφ₀.le)
  apply Real.exp_le_exp.mpr
  exact H.trans_eq (by field_simp; ring)

lemma ScalarLogConcave.upper_shell_integral {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε ≤ 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioi ((1+ε)*r₀), r^m*φ r) ≤
      (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹ := by
  have ha : 0 < (m:ℝ)*ε/(2*r₀) := by positivity
  calc
    _ ≤ ∫ r in Ioi ((1+ε)*r₀),
        (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*Real.exp (-((m:ℝ)*ε/(2*r₀))*(r-(1+ε)*r₀)) := by
      have hs : Ioi ((1+ε)*r₀) ⊆ Ioi 0 := by
        intro r hr
        exact ((mul_pos (by linarith) hr₀).trans hr)
      apply integral_mono_ae (hi.mono_set hs) ((integrableOn_exp_shift_Ioi ha _).const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      exact hφ.upper_shell_envelope hr₀ hε hε1 hφ₀ hmax (le_of_lt hr)
    _ = _ := by rw [integral_const_mul,integral_exp_shift_Ioi ha]


lemma ScalarLogConcave.lower_shell_integral {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioc 0 ((1-ε)*r₀), r^m*φ r) ≤
      (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹ := by
  have ha : 0 < (m:ℝ)*ε/(2*r₀) := by positivity
  let F : ℝ → ℝ := fun r => (r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*
    Real.exp (((m:ℝ)*ε/(2*r₀))*(r-(1-ε)*r₀))
  have hF : IntegrableOn F (Iic ((1-ε)*r₀)) volume :=
    (integrableOn_exp_shift_Iic ha _).const_mul _
  calc
    _ ≤ ∫ r in Ioc 0 ((1-ε)*r₀), F r := by
      apply integral_mono_ae (hi.mono_set Ioc_subset_Ioi_self) (hF.mono_set Ioc_subset_Iic_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hφ.lower_shell_envelope hr₀ hε hε1 hφ₀ hmax hr.1 hr.2
    _ ≤ ∫ r in Iic ((1-ε)*r₀), F r := by
      apply setIntegral_mono_set hF
      · exact Filter.Eventually.of_forall (fun r => by dsimp [F]; positivity)
      · exact Filter.Eventually.of_forall Ioc_subset_Iic_self
    _ = _ := by dsimp [F]; rw [integral_const_mul,integral_exp_shift_Iic ha]

lemma radial_integral_lower {φ : ℝ → ℝ} {m : ℕ} {r₀ : ℝ}
    (hr₀ : 0 < r₀) (hφ : ∀ r, 0 ≤ φ r)
    (hmono : ∀ r ∈ Ioc 0 r₀, φ r₀ ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    r₀^m*φ r₀*r₀/(m+1:ℝ) ≤ ∫ r in Ioi 0, r^m*φ r := by
  have hpoly : IntegrableOn (fun r : ℝ => r^m*φ r₀) (Ioc 0 r₀) volume :=
    (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
  have hcalc : (∫ r in Ioc 0 r₀, r^m*φ r₀)=r₀^m*φ r₀*r₀/(m+1:ℝ) := by
    rw [←intervalIntegral.integral_of_le hr₀.le,intervalIntegral.integral_mul_const,integral_pow]
    simp only [zero_pow (Nat.succ_ne_zero m),sub_zero,pow_succ]
    ring
  rw [←hcalc]
  calc
    _ ≤ ∫ r in Ioc 0 r₀, r^m*φ r := by
      apply integral_mono_ae hpoly (hi.mono_set Ioc_subset_Ioi_self)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact mul_le_mul_of_nonneg_left (hmono r hr) (pow_nonneg hr.1.le _)
    _ ≤ _ := by
      apply setIntegral_mono_set hi
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        exact mul_nonneg (pow_nonneg hr.le _) (hφ r)
      · exact Filter.Eventually.of_forall Ioc_subset_Ioi_self


theorem ScalarLogConcave.shell_integral_bound {φ : ℝ → ℝ}
    (hφ : ScalarLogConcave φ) {m : ℕ} (hm : 0 < m) {r₀ ε : ℝ}
    (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1) (hφ₀ : 0 < φ r₀)
    (hmax : ∀ s : ℝ, 0 < s → s^m*φ s ≤ r₀^m*φ r₀)
    (hmono : ∀ r ∈ Ioc 0 r₀, φ r₀ ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    (∫ r in Ioc 0 ((1-ε)*r₀), r^m*φ r)+
      (∫ r in Ioi ((1+ε)*r₀), r^m*φ r) ≤
      (4*((m:ℝ)+1)/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9))*(∫ r in Ioi 0, r^m*φ r) := by
  have HL := hφ.lower_shell_integral hm hr₀ hε hε1 hφ₀ hmax hi
  have HU := hφ.upper_shell_integral hm hr₀ hε hε1.le hφ₀ hmax hi
  have HN := radial_integral_lower hr₀ hφ.1 hmono hi
  have hm' : 0 < (m:ℝ) := Nat.cast_pos.mpr hm
  have HN' : r₀^m*φ r₀*r₀ ≤ ((m:ℝ)+1)*(∫ r in Ioi 0, r^m*φ r) := by
    have H := (div_le_iff₀ (show 0 < (m:ℝ)+1 by positivity)).mp HN
    linarith
  have he : 2*((r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹)=
      (4/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9))*(r₀^m*φ r₀*r₀) := by field_simp; ring
  have HE := mul_le_mul_of_nonneg_left HN' (show 0 ≤ 4/((m:ℝ)*ε)*Real.exp (-(m:ℝ)*ε^2/9) by positivity)
  calc
    _ ≤ 2*((r₀^m*φ r₀*Real.exp (-(m:ℝ)*ε^2/9))*((m:ℝ)*ε/(2*r₀))⁻¹) := by linarith
    _ = _ := he
    _ ≤ _ := HE
    _ = _ := by ring

lemma exists_weighted_mode {φ : ℝ → ℝ} {m : ℕ} (hm : 0 < m)
    (hc : Continuous φ) (hp : 0 < φ 1)
    (ht : Tendsto (fun r : ℝ => r^m*φ r) atTop (𝓝 0)) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ 0 < φ r₀ ∧
      ∀ r : ℝ, 0 < r → r^m*φ r ≤ r₀^m*φ r₀ := by
  have hev : ∀ᶠ r : ℝ in atTop, r^m*φ r < φ 1 := ht (Iio_mem_nhds hp)
  obtain ⟨R,hR⟩ := eventually_atTop.mp hev
  let B := max R 1
  have hB : (1:ℝ) ≤ B := le_max_right _ _
  have hcont : Continuous (fun r : ℝ => r^m*φ r) := by fun_prop
  obtain ⟨r₀,hr₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr (by linarith : (0:ℝ) ≤ B)) hcont.continuousOn
  have hbase : φ 1 ≤ r₀^m*φ r₀ := by
    simpa only [Set.mem_ofPred_eq,one_pow,one_mul] using hmax (show (1:ℝ) ∈ Icc 0 B from ⟨by norm_num,hB⟩)
  have hpos : 0 < r₀ := by
    rcases hr₀.1.eq_or_lt with hz | hz
    · subst r₀
      simp only [zero_pow (Nat.ne_of_gt hm),zero_mul] at hbase
      linarith
    · exact hz
  have hφpos : 0 < φ r₀ := (mul_pos_iff_of_pos_left (pow_pos hpos m)).mp (hp.trans_le hbase)
  refine ⟨r₀,hpos,hφpos,fun r hr => ?_⟩
  by_cases hrB : r ≤ B
  · exact hmax ⟨hr.le,hrB⟩
  · exact (hR r ((le_max_left R 1).trans (le_of_not_ge hrB))).le.trans hbase







end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_RadialBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Isotropization
open scoped Topology

lemma radial_integral_set {k : ℕ} [Nontrivial (E k)] (φ : ℝ → ℝ)
    {A : Set ℝ} (hA : MeasurableSet A) :
    (∫ x : E k in norm ⁻¹' A, φ ‖x‖)=
      ((k:ℝ)*volume.real (Metric.ball (0:E k) 1))*(∫ r in Ioi 0 ∩ A, r^(k-1)*φ r) := by
  rw [←integral_indicator (hA.preimage measurable_norm)]
  have he : (norm ⁻¹' A).indicator (fun x : E k => φ ‖x‖)=fun x => (A.indicator φ) ‖x‖ := by
    ext x
    by_cases hx : ‖x‖ ∈ A <;> simp [hx]
  rw [he,integral_fun_norm_addHaar (volume : Measure (E k))]
  simp only [finrank_euclideanSpace_fin,nsmul_eq_mul,smul_eq_mul]
  rw [mul_assoc]
  congr 1
  have he' : (fun r : ℝ => r^(k-1)*A.indicator φ r)=A.indicator (fun r => r^(k-1)*φ r) := by
    ext r
    by_cases hr : r ∈ A <;> simp [hr]
  rw [he',integral_indicator hA,Measure.restrict_restrict hA,inter_comm]

lemma weighted_profile_tendsto_zero {φ : ℝ → ℝ} {m : ℕ}
    (hn : ∀ r, 0 ≤ φ r)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r)
    (hi : IntegrableOn (fun r => r^m*φ r) (Ioi 0) volume) :
    Tendsto (fun r : ℝ => r^m*φ r) atTop (𝓝 0) := by
  have hupper : ∀ r : ℝ, 0 < r → r^m*φ r ≤
      (((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))/r := by
    intro r hr
    have H := radial_integral_lower (m := m) hr hn
      (fun t ht => hmono t r ht.1 ht.2) hi
    apply (le_div_iff₀ hr).mpr
    have HH := (div_le_iff₀ (show 0 < (m:ℝ)+1 by positivity)).mp H
    linarith
  have ht : Tendsto (fun r : ℝ => (((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))/r) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero] using
      (tendsto_const_nhds (x := ((m:ℝ)+1)*(∫ t in Ioi 0, t^m*φ t))).mul tendsto_inv_atTop_zero
  apply squeeze_zero' _ _ ht
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact mul_nonneg (pow_nonneg hr.le _) (hn r)
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with r hr
    exact hupper r hr



theorem ScalarLogConcave.exists_shell_radius {k : ℕ} (hk : 2 ≤ k)
    {φ : ℝ → ℝ} (hφ : ScalarLogConcave φ) (hc : Continuous φ) (hp : 0 < φ 1)
    (hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r)
    (hi : Integrable (fun x : E k => φ ‖x‖) volume) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, φ ‖x‖)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, φ ‖x‖) ≤
        (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))*
          (∫ x : E k, φ ‖x‖) := by
  have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simpa only [finrank_euclideanSpace_fin] using (show 0 < k by omega))
  have hw : IntegrableOn (fun r : ℝ => r^(k-1)*φ r) (Ioi 0) volume := by
    simpa only [finrank_euclideanSpace_fin,smul_eq_mul] using
      (integrable_fun_norm_addHaar (volume : Measure (E k))).mp hi
  obtain ⟨r₀,hr₀,hφ₀,hmax⟩ := exists_weighted_mode (m := k-1) (by omega) hc hp
    (weighted_profile_tendsto_zero hφ.1 hmono hw)
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have H := hφ.shell_integral_bound (m := k-1) (by omega) hr₀ hε hε1 hφ₀ hmax
    (fun r hr => hmono r r₀ hr.1 hr.2) hw
  have heL : Ioi 0 ∩ Iic ((1-ε)*r₀)=Ioc 0 ((1-ε)*r₀) := by ext r; simp
  have heU : Ioi 0 ∩ Ioi ((1+ε)*r₀)=Ioi ((1+ε)*r₀) := inter_eq_right.mpr (by
    intro r hr
    exact (show (0:ℝ) < (1+ε)*r₀ by positivity).trans hr)
  rw [show {x : E k | ‖x‖ ≤ (1-ε)*r₀} = norm ⁻¹' Iic ((1-ε)*r₀) from rfl,
    show {x : E k | (1+ε)*r₀ < ‖x‖} = norm ⁻¹' Ioi ((1+ε)*r₀) from rfl,
    radial_integral_set φ measurableSet_Iic,radial_integral_set φ measurableSet_Ioi,
    heL,heU,integral_fun_norm_addHaar (volume : Measure (E k)) φ]
  simp only [finrank_euclideanSpace_fin,nsmul_eq_mul,smul_eq_mul]
  have HV := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)*volume.real (Metric.ball (0:E k) 1) by positivity)
  ring_nf at HV ⊢
  exact HV


end SingleLatticeCovering.Prekopa
namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization
open scoped RealInnerProductSpace Topology

lemma radialInf_bddBelow {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    BddBelow (Set.range (fun U : E k ≃ₗᵢ[ℝ] E k => f (U y))) :=
  ⟨0,by rintro _ ⟨U,rfl⟩; exact hf _⟩

lemma radialInf_nonneg {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    0 ≤ radialInf f y := by
  unfold radialInf
  exact le_ciInf (fun U => hf (U y))

lemma radialInf_le {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k)
    (U : E k ≃ₗᵢ[ℝ] E k) : radialInf f y ≤ f (U y) :=
  ciInf_le (radialInf_bddBelow hf y) U

lemma radialInf_le_self {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y) (y : E k) :
    radialInf f y ≤ f y := radialInf_le hf y (LinearIsometryEquiv.refl ℝ (E k))

lemma radialInf_invariant {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    (U : E k ≃ₗᵢ[ℝ] E k) (y : E k) : radialInf f (U y)=radialInf f y := by
  apply le_antisymm
  · apply le_ciInf
    intro V
    have H := radialInf_le hf (U y) (U.symm.trans V)
    simpa only [LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply] using H
  · apply le_ciInf
    intro V
    exact radialInf_le hf y (U.trans V)

lemma radialInf_norm_eq {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {y z : E k} (h : ‖y‖=‖z‖) : radialInf f y=radialInf f z := by
  have H := radialInf_invariant hf (Submodule.reflection (ℝ ∙ (y-z))ᗮ) y
  rw [Submodule.reflection_sub h] at H
  exact H.symm

lemma radialInf_logConcave {k : ℕ} {f : E k → ℝ} (hf : LogConcave f) :
    LogConcave (radialInf f) := by
  refine ⟨radialInf_nonneg hf.1,fun y z a b ha hb hab => ?_⟩
  apply le_ciInf
  intro U
  calc
    _ ≤ (f (U y))^a*(f (U z))^b := mul_le_mul
      (Real.rpow_le_rpow (radialInf_nonneg hf.1 y) (radialInf_le hf.1 y U) ha.le)
      (Real.rpow_le_rpow (radialInf_nonneg hf.1 z) (radialInf_le hf.1 z U) hb.le)
      (Real.rpow_nonneg (radialInf_nonneg hf.1 z) b) (Real.rpow_nonneg (hf.1 _) a)
    _ ≤ f (a•U y+b•U z) := hf.2 _ _ _ _ ha hb hab
    _ = _ := by rw [map_add,map_smul,map_smul]

lemma radialInf_approximation {k : ℕ} {f M : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {ε : ℝ} (hrad : ∀ y z, ‖y‖=‖z‖ → M y=M z)
    (herr : ∀ y, |f y-M y| ≤ ε) (y : E k) : |radialInf f y-M y| ≤ ε := by
  apply abs_le.mpr
  constructor
  · have H : M y-ε ≤ radialInf f y := by
      apply le_ciInf
      intro U
      have HH := (abs_le.mp (herr (U y))).1
      rw [hrad (U y) y (U.norm_map y)] at HH
      linarith
    linarith
  · exact (sub_le_sub_right (radialInf_le_self hf y) (M y)).trans (abs_le.mp (herr y)).2

lemma logConcave_min {k : ℕ} {f : E k → ℝ} (hf : LogConcave f)
    (y z : E k) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1) :
    min (f y) (f z) ≤ f (a•y+b•z) := by
  have hn : 0 ≤ min (f y) (f z) := le_min (hf.1 _) (hf.1 _)
  calc
    _ = (min (f y) (f z))^a*(min (f y) (f z))^b := by
      by_cases h0 : min (f y) (f z)=0
      · simp [h0,Real.zero_rpow (ne_of_gt ha)]
      rw [←Real.rpow_add (lt_of_le_of_ne hn (Ne.symm h0)),hab,Real.rpow_one]
    _ ≤ (f y)^a*(f z)^b := mul_le_mul
      (Real.rpow_le_rpow hn (min_le_left _ _) ha.le)
      (Real.rpow_le_rpow hn (min_le_right _ _) hb.le)
      (Real.rpow_nonneg hn _) (Real.rpow_nonneg (hf.1 _) _)
    _ ≤ _ := hf.2 _ _ _ _ ha hb hab

lemma radialInf_smul_mono {k : ℕ} {f : E k → ℝ} (hf : LogConcave f)
    (y : E k) {a : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1) : radialInf f y ≤ radialInf f (a•y) := by
  rcases eq_or_lt_of_le ha1 with rfl | ha1
  · simp
  have hn : radialInf f (-y)=radialInf f y := radialInf_norm_eq hf.1 (norm_neg y)
  have H := logConcave_min (radialInf_logConcave hf) y (-y)
    (a := (1+a)/2) (b := (1-a)/2) (by linarith) (by linarith) (by ring)
  rw [hn,min_self] at H
  convert H using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  module




end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization
open scoped RealInnerProductSpace Topology

lemma radialInf_abs_sub_le {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    {y z : E k} {ε : ℝ}
    (h : ∀ U : E k ≃ₗᵢ[ℝ] E k, |f (U y)-f (U z)| ≤ ε) :
    |radialInf f y-radialInf f z| ≤ ε := by
  have hyn : radialInf f y-ε ≤ radialInf f z := by
    apply le_ciInf
    intro U
    have H := (abs_le.mp (h U)).2
    linarith [radialInf_le hf y U]
  have hzn : radialInf f z-ε ≤ radialInf f y := by
    apply le_ciInf
    intro U
    have H := (abs_le.mp (h U)).1
    linarith [radialInf_le hf z U]
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma continuous_radialInf {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 ≤ f y)
    (hc : Continuous f) : Continuous (radialInf f) := by
  apply continuous_iff_continuousAt.mpr
  intro y
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  have hu := (isCompact_closedBall (0:E k) (‖y‖+1)).uniformContinuousOn_of_continuous hc.continuousOn
  obtain ⟨δ,hδ,hclose⟩ := Metric.uniformContinuousOn_iff.mp hu (ε/2) (by linarith)
  refine ⟨min δ 1,lt_min hδ (by norm_num),fun z hz => ?_⟩
  have hzd : dist z y < δ := hz.trans_le (min_le_left _ _)
  have hz1 : dist z y < 1 := hz.trans_le (min_le_right _ _)
  have hzn : ‖z‖ ≤ ‖y‖+1 := by
    exact norm_le_norm_add_const_of_dist_le hz1.le
  have H : |radialInf f z-radialInf f y| ≤ ε/2 := by
    apply radialInf_abs_sub_le hf
    intro U
    have hzy : U z ∈ Metric.closedBall (0:E k) (‖y‖+1) := by
      simpa only [Metric.mem_closedBall,dist_zero_right,U.norm_map] using hzn
    have hyy : U y ∈ Metric.closedBall (0:E k) (‖y‖+1) := by
      simp only [Metric.mem_closedBall,dist_zero_right,U.norm_map]
      linarith
    have HH := hclose (U z) hzy (U y) hyy (by simpa only [U.dist_map] using hzd)
    exact le_of_lt (by simpa only [Real.dist_eq] using HH)
  rw [Real.dist_eq]
  linarith

lemma radialInf_pos {k : ℕ} {f : E k → ℝ} (hf : ∀ y, 0 < f y)
    (hc : Continuous f) (y : E k) : 0 < radialInf f y := by
  have hne : (Metric.sphere (0:E k) ‖y‖).Nonempty := ⟨y,by simp⟩
  obtain ⟨z,hz,hmin⟩ := (isCompact_sphere (0:E k) ‖y‖).exists_isMinOn hne hc.continuousOn
  apply (hf z).trans_le
  apply le_ciInf
  intro U
  exact hmin (by simp)



end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization Prekopa
open scoped RealInnerProductSpace Topology

lemma radialInf_integrable {k : ℕ} {f : E k → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hc : Continuous f) (hi : Integrable f volume) : Integrable (radialInf f) volume := by
  apply hi.mono' (continuous_radialInf hf hc).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (radialInf_nonneg hf x)] using radialInf_le_self hf x)

lemma scalarLogConcave_profile {k : ℕ} {f : E k → ℝ} (hf : LogConcave f) (e : E k) :
    ScalarLogConcave (fun r : ℝ => radialInf f (r•e)) := by
  refine ⟨fun r => radialInf_nonneg hf.1 _,fun r s a b ha hb hab => ?_⟩
  have H := (radialInf_logConcave hf).2 (r•e) (s•e) a b ha hb hab
  simpa only [add_smul,mul_smul] using H


theorem radialInf_shell_radius {k : ℕ} (hk : 2 ≤ k) {f : E k → ℝ}
    (hf : LogConcave f) (hp : ∀ x, 0 < f x) (hc : Continuous f) (hi : Integrable f volume) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, radialInf f x)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, radialInf f x) ≤
        (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))*
          (∫ x : E k, radialInf f x) := by
  have : Nontrivial (E k) := Module.nontrivial_of_finrank_pos (R := ℝ)
    (by simpa only [finrank_euclideanSpace_fin] using (show 0 < k by omega))
  obtain ⟨e,he⟩ := exists_norm_eq (E k) (show (0:ℝ) ≤ 1 by norm_num)
  let φ : ℝ → ℝ := fun r => radialInf f (r•e)
  have hre (x : E k) : radialInf f (‖x‖•e)=radialInf f x := by
    apply radialInf_norm_eq hf.1
    simp only [norm_smul,Real.norm_eq_abs,abs_norm,he,mul_one]
  have hcont : Continuous φ := (continuous_radialInf hf.1 hc).comp (by fun_prop)
  have hpos : 0 < φ 1 := radialInf_pos hp hc _
  have hmono : ∀ r s : ℝ, 0 < r → r ≤ s → φ s ≤ φ r := by
    intro r s hr hrs
    have hs : 0 < s := hr.trans_le hrs
    have H := radialInf_smul_mono hf (s•e) (a := r/s) (by positivity)
      ((div_le_one hs).mpr hrs)
    dsimp only [φ]
    convert H using 1
    all_goals try with_reducible_and_instances rfl
    rw [smul_smul,div_mul_cancel₀ r (ne_of_gt hs)]
  have hint : Integrable (fun x : E k => φ ‖x‖) volume := by
    simp only [φ,hre]
    exact radialInf_integrable hf.1 hc hi
  obtain ⟨r₀,hr₀,H⟩ := (scalarLogConcave_profile hf e).exists_shell_radius hk hcont hpos hmono hint
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  simpa only [hre] using H ε hε hε1


end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Radial
open Set MeasureTheory Isotropization Prekopa
open scoped ENNReal RealInnerProductSpace Topology

lemma setIntegral_transfer_error {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfn : ∀ x, 0 ≤ f x) (hgn : ∀ x, 0 ≤ g x) {B A : Set Ω}
    (hB : MeasurableSet B) (hA : MeasurableSet A) (hvB : μ B ≠ ∞)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ x ∈ B, g x ≤ f x+δ) :
    (∫ x in A, g x ∂μ) ≤ (∫ x in A, f x ∂μ)+δ*μ.real B+(∫ x in Bᶜ, g x ∂μ) := by
  classical
  have hd : Integrable (B.indicator (fun _ : Ω => δ)) μ :=
    (integrable_indicator_iff hB).mpr (integrableOn_const hvB)
  have hsum : Integrable (fun x => A.indicator f x+B.indicator (fun _ => δ) x) μ := (hf.indicator hA).add hd
  have hpoint (x : Ω) : A.indicator g x ≤
      A.indicator f x+B.indicator (fun _ => δ) x+Bᶜ.indicator g x := by
    by_cases ha : x ∈ A <;> by_cases hb : x ∈ B
    · simp only [indicator_of_mem ha,indicator_of_mem hb,indicator_of_notMem (show x ∉ Bᶜ from fun h => h hb),add_zero]
      exact hclose x hb
    · simp only [indicator_of_mem ha,indicator_of_notMem hb,indicator_of_mem (show x ∈ Bᶜ from hb),add_zero]
      linarith [hfn x]
    · simp only [indicator_of_notMem ha,indicator_of_mem hb,indicator_of_notMem (show x ∉ Bᶜ from fun h => h hb),zero_add,add_zero]
      exact hδ
    · simp only [indicator_of_notMem ha,indicator_of_notMem hb,indicator_of_mem (show x ∈ Bᶜ from hb),zero_add]
      exact hgn x
  have H := integral_mono (hg.indicator hA) (hsum.add (hg.indicator hB.compl)) hpoint
  change (∫ x, A.indicator g x ∂μ) ≤ ∫ x, A.indicator f x+B.indicator (fun _ => δ) x+Bᶜ.indicator g x ∂μ at H
  rw [integral_add hsum (hg.indicator hB.compl),integral_add (hf.indicator hA) hd,
    integral_indicator hA,integral_indicator hA,integral_indicator hB,integral_indicator hB.compl,
    integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H ⊢
  rw [mul_comm _ δ] at H
  exact H

lemma radialInf_integral_le {k : ℕ} {f : E k → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hc : Continuous f) (hi : Integrable f volume) :
    (∫ x : E k, radialInf f x) ≤ ∫ x : E k, f x :=
  integral_mono (radialInf_integrable hf hc hi) hi (radialInf_le_self hf)




theorem radial_model_shell {k : ℕ} (hk : 2 ≤ k) {f M : E k → ℝ}
    (hf : LogConcave f) (hp : ∀ x, 0 < f x) (hc : Continuous f)
    (hi : Integrable f volume) (hmass : ∫ x, f x=1)
    (hMi : Integrable M volume) (hMn : ∀ x, 0 ≤ M x)
    (hMr : ∀ x y, ‖x‖=‖y‖ → M x=M y)
    {δ : ℝ} (hδ : 0 ≤ δ) (hclose : ∀ x, |f x-M x| ≤ δ)
    (T : ℝ) : ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ x : E k in {x | ‖x‖ ≤ (1-ε)*r₀}, M x)+
        (∫ x : E k in {x | (1+ε)*r₀ < ‖x‖}, M x) ≤
      (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
        2*(δ*volume.real (Metric.closedBall (0:E k) T)+
          (∫ x : E k in (Metric.closedBall (0:E k) T)ᶜ, M x)) := by
  obtain ⟨r₀,hr₀,H⟩ := radialInf_shell_radius hk hf hp hc hi
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have hq : Integrable (radialInf f) volume := radialInf_integrable hf.1 hc hi
  have hq1 : (∫ x : E k, radialInf f x) ≤ 1 := by
    rw [←hmass]; exact radialInf_integral_le hf.1 hc hi
  have happ := radialInf_approximation hf.1 hMr hclose
  have hcl : ∀ x ∈ Metric.closedBall (0:E k) T, M x ≤ radialInf f x+δ := by
    intro x _
    have hh := (abs_le.mp (happ x)).1
    linarith
  have hb : MeasurableSet (Metric.closedBall (0:E k) T) := Metric.isClosed_closedBall.measurableSet
  have hvb : volume (Metric.closedBall (0:E k) T) ≠ ∞ := (isCompact_closedBall _ _).measure_ne_top
  have hlo := setIntegral_transfer_error volume (A := {x : E k | ‖x‖ ≤ (1-ε)*r₀}) hq hMi (radialInf_nonneg hf.1) hMn hb
    (measurableSet_le measurable_norm measurable_const) hvb hδ hcl
  have hhi := setIntegral_transfer_error volume (A := {x : E k | (1+ε)*r₀ < ‖x‖}) hq hMi (radialInf_nonneg hf.1) hMn hb
    (measurableSet_lt measurable_const measurable_norm) hvb hδ hcl
  have hcoeff : 0 ≤ 4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9) := by positivity
  have HH := (H ε hε hε1).trans (mul_le_of_le_one_right hcoeff hq1)
  linarith [hlo,hhi]


end SingleLatticeCovering.Radial

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Metric Sections Isotropization
open scoped ENNReal Topology BigOperators RealInnerProductSpace

lemma euclidean_sq_weighted {D : ℕ} (u v : E D) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    ‖a•u+b•v‖^2 ≤ a*‖u‖^2+b*‖v‖^2 := by
  rw [norm_add_sq_real,norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,
    abs_of_nonneg ha,abs_of_nonneg hb,real_inner_smul_left,real_inner_smul_right]
  have H := mul_nonneg (mul_nonneg ha hb) (sq_nonneg ‖u-v‖)
  rw [norm_sub_sq_real] at H
  have he : b=1-a := by linarith
  subst b
  nlinarith [H]

lemma smoothingKernel_positive {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) (x : RV n) :
    0 < smoothingKernel A c y x := Real.exp_pos _

lemma smoothingKernel_le_one {n D : ℕ} (A : RV n →ₗ[ℝ] E D) {c : ℝ} (hc : 0 ≤ c) (y : E D) (x : RV n) :
    smoothingKernel A c y x ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  nlinarith [sq_nonneg ‖y-A x‖]

lemma continuous_smoothingKernel_right {n D : ℕ} (A : RV n →ₗ[ℝ] E D) (c : ℝ) (y : E D) :
    Continuous (smoothingKernel A c y) := by
  unfold smoothingKernel
  fun_prop

lemma smoothingKernel_weighted {n D : ℕ} (A : RV n →ₗ[ℝ] E D) {c a b : ℝ}
    (hc : 0 ≤ c) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1)
    (y z : E D) (u v : RV n) :
    (smoothingKernel A c y u)^a*(smoothingKernel A c z v)^b ≤
      smoothingKernel A c (a•y+b•z) (a•u+b•v) := by
  have he : (a•y+b•z)-A (a•u+b•v)=a•(y-A u)+b•(z-A v) := by
    simp only [map_add,map_smul]
    module
  simp only [smoothingKernel,←Real.exp_mul,←Real.exp_add,he]
  apply Real.exp_le_exp.mpr
  have H := mul_le_mul_of_nonneg_left (euclidean_sq_weighted (y-A u) (z-A v) ha hb hab) hc
  nlinarith

lemma soft_smoothing_gaussianBound {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D) {c t : ℝ}
    (hc : 0 ≤ c) (ht : 0 < t) (y : E D) :
    GaussianBound (fun x => softIndicator K t x*smoothingKernel A c y x) := by
  obtain ⟨B,r,hB,hr,hbound⟩ := softIndicator_gaussianBound hK hne ht
  refine ⟨B,r,hB,hr,fun x => ?_⟩
  rw [abs_of_pos (mul_pos (softIndicator_positive K t x) (smoothingKernel_positive A c y x))]
  exact (mul_le_of_le_one_right (softIndicator_positive K t x).le (smoothingKernel_le_one A hc y x)).trans
    (by simpa only [abs_of_pos (softIndicator_positive K t x)] using hbound x)

lemma soft_smoothing_integral_tendsto {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D) {c : ℝ}
    (hc : 0 ≤ c) (y : E D) :
    Tendsto (fun j : ℕ => ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)
      atTop (𝓝 (∫ x in K, smoothingKernel A c y x)) := by
  have hcont : Continuous (smoothingKernel A c y) := continuous_smoothingKernel_right A c y
  have H := tendsto_integral_of_dominated_convergence (softIndicator K 1)
    (fun j => ((continuous_softIndicator K ((j : ℝ)+1)).mul hcont).aestronglyMeasurable)
    ((softIndicator_gaussianBound hK hne zero_lt_one).integrable (continuous_softIndicator K 1))
    (fun j => Filter.Eventually.of_forall (fun x => by
      simp only [Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_pos (mul_pos (softIndicator_positive K _ x) (smoothingKernel_positive A c y x))]
      exact (mul_le_of_le_one_right (softIndicator_positive K _ x).le (smoothingKernel_le_one A hc y x)).trans
        (softIndicator_antitone K x (by nlinarith [Nat.cast_nonneg (α := ℝ) j] : (1:ℝ) ≤ (j : ℝ)+1))))
    (Filter.Eventually.of_forall (fun x => (softIndicator_tendsto hK.isClosed hne x).mul_const (smoothingKernel A c y x)))
  have he : (fun x => K.indicator (fun _ => (1:ℝ)) x*smoothingKernel A c y x)=
      K.indicator (smoothingKernel A c y) := by
    ext x
    by_cases hx : x ∈ K <;> simp [hx]
  rw [he,integral_indicator hK.measurableSet] at H
  exact H

lemma soft_smoothing_integral_inequality {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (hne : K.Nonempty) (A : RV n →ₗ[ℝ] E D)
    {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (y z : E D) (j : ℕ) :
    (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)^a*
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c z x)^b ≤
      ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c (a•y+b•z) x := by
  have hj : 0 < (j : ℝ)+1 := by positivity
  have hcont (v : E D) : Continuous (fun x => softIndicator K ((j : ℝ)+1) x*smoothingKernel A c v x) :=
    (continuous_softIndicator K _).mul (continuous_smoothingKernel_right A c v)
  have hpos (v : E D) (x : RV n) : 0 < softIndicator K ((j : ℝ)+1) x*smoothingKernel A c v x :=
    mul_pos (softIndicator_positive K _ x) (smoothingKernel_positive A c v x)
  apply gaussian_dominated_integral n (hcont y) (hcont z) (hcont _) (hpos y) (hpos z) (hpos _)
    (soft_smoothing_gaussianBound hK hne A hc hj y) (soft_smoothing_gaussianBound hK hne A hc hj z)
    (soft_smoothing_gaussianBound hK hne A hc hj _) ha hb hab
  intro u v
  rw [Real.mul_rpow (softIndicator_positive K _ u).le (smoothingKernel_positive A c y u).le,
    Real.mul_rpow (softIndicator_positive K _ v).le (smoothingKernel_positive A c z v).le]
  calc
    _ = (softIndicator K ((j : ℝ)+1) u^a*softIndicator K ((j : ℝ)+1) v^b)*
          (smoothingKernel A c y u^a*smoothingKernel A c z v^b) := by ring
    _ ≤ _ := mul_le_mul
      (softIndicator_weighted hK hK hne hne ha.le hb.le hab hj.le
        (fun u hu v hv => hconv hu hv ha.le hb.le hab) u v)
      (smoothingKernel_weighted A hc ha.le hb.le hab y z u v)
      (mul_nonneg (Real.rpow_nonneg (smoothingKernel_positive A c y u).le _)
        (Real.rpow_nonneg (smoothingKernel_positive A c z v).le _))
      (softIndicator_positive K _ _).le




theorem logConcave_smoothed_volume {n D : ℕ} {K : Set (RV n)}
    (hK : IsCompact K) (hconv : Convex ℝ K) (A : RV n →ₗ[ℝ] E D)
    {c : ℝ} (hc : 0 ≤ c) :
    LogConcave (fun y => ∫ x in K, smoothingKernel A c y x) := by
  refine ⟨fun y => integral_nonneg (fun x => (smoothingKernel_positive A c y x).le),?_⟩
  intro y z a b ha hb hab
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp [Real.zero_rpow (ne_of_gt ha),Real.zero_rpow (ne_of_gt hb)]
  have hpoint : ∀ j : ℕ,
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c y x)^a*
      (∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c z x)^b ≤
      ∫ x, softIndicator K ((j : ℝ)+1) x*smoothingKernel A c (a•y+b•z) x := by
    exact soft_smoothing_integral_inequality hK hconv hne A hc ha hb hab y z
  exact le_of_tendsto_of_tendsto
    (((Real.continuous_rpow_const ha.le).tendsto _).comp (soft_smoothing_integral_tendsto hK hne A hc y) |>.mul
      (((Real.continuous_rpow_const hb.le).tendsto _).comp (soft_smoothing_integral_tendsto hK hne A hc z)))
    (soft_smoothing_integral_tendsto hK hne A hc _) (Filter.Eventually.of_forall hpoint)


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter
open scoped ENNReal Topology

lemma tail_quantiles_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1) :
    (3:ℝ)/4 ≤ μ.real {x | -2 ≤ X x} ∧ μ.real {x | 2 ≤ X x} ≤ (1:ℝ)/4 := by
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun x => sq_nonneg (X x))) hi (4:ℝ)
  have htail : μ.real {x | 4 ≤ (X x)^2} ≤ (1:ℝ)/4 := by linarith
  constructor
  · have hc : {x | -2 ≤ X x}ᶜ ⊆ {x | 4 ≤ (X x)^2} := by
      intro x hx
      have hh : X x < -2 := lt_of_not_ge hx
      change 4 ≤ (X x)^2
      nlinarith [sq_nonneg (X x+2)]
    have hh := measureReal_mono (μ := μ) hc
    rw [probReal_compl_eq_one_sub (measurableSet_le measurable_const hX)] at hh
    linarith
  · apply le_trans (measureReal_mono ?_) htail
    intro x hx
    change 4 ≤ (X x)^2
    change 2 ≤ X x at hx
    nlinarith [sq_nonneg (X x-2)]

lemma scalar_tail_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hlc : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    {t : ℝ} (ht : 0 ≤ t) : μ.real {x | t ≤ X x} ≤ Real.exp (1-t/16) := by
  obtain ⟨hl,hr⟩ := tail_quantiles_of_second_moment μ hX hi h2
  exact hlc.exponential_tail (fun _ => measureReal_le_one) hl hr ht

lemma scalar_abs_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hp : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    (hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -X x}))
    {t : ℝ} (ht : 0 ≤ t) : μ.real {x | t ≤ |X x|} ≤ 2*Real.exp (1-t/16) := by
  have hp' := scalar_tail_of_second_moment μ hX hi h2 hp ht
  have hn' := scalar_tail_of_second_moment μ hX.neg
    (by simpa only [Pi.neg_apply, neg_sq] using hi) (by simpa only [Pi.neg_apply, neg_sq] using h2) hn ht
  simp only [Pi.neg_apply] at hn'
  have hh : {x | t ≤ |X x|} = {x | t ≤ X x} ∪ {x | t ≤ -X x} := by
    ext x
    simp only [mem_ofPred_eq,mem_union,le_abs]
  rw [hh]
  exact (measureReal_union_le _ _).trans (by linarith)


lemma lintegral_fourth_eq_tails {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {X : Ω → ℝ} (hX : Measurable X) :
    (∫⁻ x, ENNReal.ofReal ((X x)^4) ∂μ)=
      ∫⁻ t in Ioi (0:ℝ), μ {x | t ≤ |X x|}*ENNReal.ofReal (4*t^3) := by
  have H := lintegral_comp_eq_lintegral_meas_le_mul μ
    (Filter.Eventually.of_forall (fun x => abs_nonneg (X x))) hX.abs.aemeasurable
    (g := fun t : ℝ => 4*t^3) (fun t ht => (by fun_prop : Continuous (fun t : ℝ => 4*t^3)).intervalIntegrable 0 t)
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht; exact mul_nonneg (by norm_num) (pow_nonneg (le_of_lt ht) _))
  have he (x : Ω) : (∫ t in (0:ℝ)..|X x|, 4*t^3)=(X x)^4 := by
    rw [intervalIntegral.integral_const_mul,integral_pow]
    norm_num
    rw [Even.pow_abs (by decide : Even (4:ℕ)) (X x)]
    ring
  simpa only [he] using H

lemma fourth_weight_integrable : IntegrableOn (fun t : ℝ => t^3*Real.exp (-(1/16:ℝ)*t)) (Ioi 0) volume := by
  have H := integrableOn_rpow_mul_exp_neg_mul_rpow
    (show (-1:ℝ) < 3 by norm_num) (show (0:ℝ) < 1 by norm_num) (show (0:ℝ) < 1/16 by norm_num)
  simpa only [Real.rpow_one,Real.rpow_ofNat] using H

lemma fourth_weight_integral :
    (∫ t : ℝ in Ioi 0, t^3*Real.exp (-(1/16:ℝ)*t))=(16:ℝ)^4*6 := by
  have H := Real.integral_rpow_mul_exp_neg_mul_Ioi (show (0:ℝ) < 4 by norm_num) (show (0:ℝ) < 1/16 by norm_num)
  have hg : Real.Gamma 4=6 := by norm_num
  norm_num only [show (4:ℝ)-1=3 by norm_num,Real.rpow_ofNat,hg,show (1:ℝ)/(1/16)=16 by norm_num] at H
  simpa only [neg_mul,show (16:ℝ)^4*6=393216 by norm_num] using H

lemma lintegral_fourth_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (htail : ∀ t : ℝ, 0 ≤ t → μ.real {x | t ≤ |X x|} ≤ 2*Real.exp (1-t/16)) :
    (∫⁻ x, ENNReal.ofReal ((X x)^4) ∂μ) ≤ ENNReal.ofReal fourthMomentConstant := by
  rw [lintegral_fourth_eq_tails μ hX]
  have he (t : ℝ) : (2*Real.exp (1-t/16))*(4*t^3)=(8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t)) := by
    rw [show 1-t/16=1+(-(1/16:ℝ)*t) by ring,Real.exp_add]
    ring
  calc
    _ ≤ ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal ((8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t))) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [←he]
      rw [ENNReal.ofReal_mul (show 0 ≤ 2*Real.exp (1-t/16) by positivity)]
      apply mul_le_mul_left
      rw [←ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (htail t (le_of_lt ht))
    _ = ENNReal.ofReal (∫ t in Ioi (0:ℝ), (8*Real.exp 1)*(t^3*Real.exp (-(1/16:ℝ)*t))) := by
      symm
      apply ofReal_integral_eq_lintegral_ofReal (fourth_weight_integrable.const_mul _)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact mul_nonneg (by positivity) (mul_nonneg (pow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le)
    _ = _ := by rw [integral_const_mul,fourth_weight_integral]; congr 1; unfold fourthMomentConstant; ring

lemma fourth_moment_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    (hi : Integrable (fun x => (X x)^2) μ) (h2 : (∫ x, (X x)^2 ∂μ) ≤ 1)
    (hp : ScalarLogConcave (fun t => μ.real {x | t ≤ X x}))
    (hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -X x})) :
    Integrable (fun x => (X x)^4) μ ∧ (∫ x, (X x)^4 ∂μ) ≤ fourthMomentConstant := by
  have H := lintegral_fourth_le μ hX (fun t ht => scalar_abs_tail μ hX hi h2 hp hn ht)
  have hint : Integrable (fun x => (X x)^4) μ := by
    refine ⟨(hX.pow_const 4).aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => (show 0 ≤ (X x)^4 by positivity)))]
    exact H.trans_lt ENNReal.ofReal_lt_top
  refine ⟨hint,?_⟩
  rw [←ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall (fun x => by positivity))] at H
  exact (ENNReal.ofReal_le_ofReal_iff (by unfold fourthMomentConstant; positivity)).mp H



end SingleLatticeCovering.Prekopa


end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Marginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
noncomputable section
noncomputable section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Isotropization
open scoped ENNReal RealInnerProductSpace Topology BigOperators

lemma compact_volume_E {d : ℕ} {A B C : Set (E d)}
    (hA : IsCompact A) (hB : IsCompact B) (hC : IsCompact C)
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a+b=1)
    (hadd : ∀ x ∈ A, ∀ y ∈ B, a•x+b•y ∈ C) :
    (volume A).toReal^a*(volume B).toReal^b ≤ (volume C).toReal := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin d)
  have hv (S : Set (E d)) : volume (e '' S)=volume S := by
    have H := congrArg (fun μ : Measure (RV d) => μ (e '' S)) hp.map_eq
    change (Measure.map e.toHomeomorph.toMeasurableEquiv volume) (e '' S)=volume (e '' S) at H
    rw [e.toHomeomorph.toMeasurableEquiv.map_apply] at H
    change volume (e ⁻¹' (e '' S))=volume (e '' S) at H
    rw [Set.preimage_image_eq _ e.injective] at H
    exact H.symm
  rw [←hv A,←hv B,←hv C]
  apply compact_volume (hA.image e.continuous) (hB.image e.continuous) (hC.image e.continuous) ha hb hab
  rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩
  exact ⟨a•x+b•y,hadd x hx y hy,by simp⟩

lemma scalarLogConcave_cap_volume_E {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (L : E d →L[ℝ] ℝ) :
    ScalarLogConcave (fun t => (volume (K ∩ {x | t ≤ L x})).toReal) := by
  refine ⟨fun _ => ENNReal.toReal_nonneg,fun u v a b ha hb hab => ?_⟩
  apply compact_volume_E (hK.inter_right (isClosed_le continuous_const L.continuous))
    (hK.inter_right (isClosed_le continuous_const L.continuous))
    (hK.inter_right (isClosed_le continuous_const L.continuous)) ha hb hab
  intro x hx y hy
  refine ⟨hc hx.1 hy.1 ha.le hb.le hab,?_⟩
  change a*u+b*v ≤ L (a•x+b•y)
  simp only [map_add,map_smul,smul_eq_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left hx.2 ha.le) (mul_le_mul_of_nonneg_left hy.2 hb.le)

lemma scalarLogConcave_uniform_cap {d : ℕ} {K : Set (E d)}
    (hK : IsCompact K) (hc : Convex ℝ K) (L : E d →L[ℝ] ℝ) :
    ScalarLogConcave (fun t => (((volume K)⁻¹ • volume.restrict K) : Measure (E d)).real {x | t ≤ L x}) := by
  have he (t : ℝ) : (((volume K)⁻¹ • volume.restrict K) : Measure (E d)).real {x | t ≤ L x}=
      ((volume K)⁻¹).toReal*(volume (K ∩ {x | t ≤ L x})).toReal := by
    rw [measureReal_def,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply
      (measurableSet_le measurable_const L.measurable),ENNReal.toReal_mul,inter_comm]
  simp_rw [he]
  exact (scalarLogConcave_cap_volume_E hK hc L).const_mul ENNReal.toReal_nonneg

lemma norm_fourth_le_sum {d : ℕ} (x : E d) : ‖x‖^4 ≤ (d:ℝ)*(∑ i, (x i)^4) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin d => (1:ℝ)) (fun i => (x i)^2)
  simp only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at h
  have he : ‖x‖^2=∑ i, (x i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  rw [show ‖x‖^4=(‖x‖^2)^2 by ring,he]
  simpa only [←pow_mul] using h

lemma fourth_norm_of_coordinates {d : ℕ} {μ : Measure (E d)} [IsFiniteMeasure μ]
    (hint : ∀ i : Fin d, Integrable (fun x : E d => (x i)^4) μ)
    (hb : ∀ i : Fin d, (∫ x, (x i)^4 ∂μ) ≤ fourthMomentConstant) :
    Integrable (fun x : E d => ‖x‖^4) μ ∧
      (∫ x : E d, ‖x‖^4 ∂μ) ≤ fourthMomentConstant*(d:ℝ)^2 := by
  have hi : Integrable (fun x : E d => (d:ℝ)*(∑ i, (x i)^4)) μ :=
    (integrable_finsetSum _ (fun i _ => hint i)).const_mul _
  have hn : Integrable (fun x : E d => ‖x‖^4) μ := hi.mono' (by fun_prop)
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ ‖x‖^4)] using norm_fourth_le_sum x))
  refine ⟨hn,?_⟩
  calc
    _ ≤ ∫ x : E d, (d:ℝ)*(∑ i, (x i)^4) ∂μ := integral_mono hn hi norm_fourth_le_sum
    _ = (d:ℝ)*(∑ i, ∫ x : E d, (x i)^4 ∂μ) := by rw [integral_const_mul,integral_finsetSum _ (fun i _ => hint i)]
    _ ≤ (d:ℝ)*(∑ _i : Fin d, fourthMomentConstant) := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

lemma paley_zygmund_quarter {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {Y : Ω → ℝ} (hm : Measurable Y)
    (hi : Integrable Y μ) (hy : ∀ x, 0 ≤ Y x) (hmean : ∫ x, Y x ∂μ=1)
    {C : ℝ} (hC : 0 < C) (h2i : Integrable (fun x => (Y x)^2) μ)
    (hsecond : (∫ x, (Y x)^2 ∂μ) ≤ C) : 1/(4*C) ≤ μ.real {x | 1/2 ≤ Y x} := by
  have _ := hy
  classical
  let A := {x | (1:ℝ)/2 ≤ Y x}
  have hA : MeasurableSet A := measurableSet_le measurable_const hm
  have hpoint (x : Ω) : Y x ≤ 1/2+(Y x)^2/(4*C)+A.indicator (fun _ => C) x := by
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      have hsq := sq_nonneg (Y x-2*C)
      apply (mul_le_mul_iff_left₀ (show 0 < 4*C by positivity)).mp
      have he : (1/2+(Y x)^2/(4*C)+C)*(4*C)=2*C+(Y x)^2+4*C^2 := by field_simp; ring
      rw [he]
      nlinarith
    · rw [indicator_of_notMem hx]
      have hh : Y x < 1/2 := lt_of_not_ge hx
      have hh' : 0 ≤ (Y x)^2/(4*C) := by positivity
      linarith
  have hb := integral_mono hi (((integrable_const (1/2:ℝ)).add (h2i.div_const (4*C))).add
    ((integrable_const C).indicator hA)) hpoint
  change (∫ x, Y x ∂μ) ≤ ∫ x, 1/2+(Y x)^2/(4*C)+A.indicator (fun _ => C) x ∂μ at hb
  have hsum : Integrable (fun x => (1/2:ℝ)+(Y x)^2/(4*C)) μ := (integrable_const _).add (h2i.div_const _)
  rw [integral_add hsum ((integrable_const C).indicator hA),
    integral_add (integrable_const (1/2:ℝ)) (h2i.div_const (4*C)),integral_div (4*C),
    integral_indicator hA,integral_const,integral_const,hmean] at hb
  simp only [measureReal_def,Measure.restrict_apply_univ,measure_univ,ENNReal.toReal_one,smul_eq_mul,one_mul] at hb
  change 1 ≤ 1/2+(∫ x, (Y x)^2 ∂μ)/(4*C)+μ.real A*C at hb
  have hdiv := (div_le_div_iff_of_pos_right (show 0 < 4*C by positivity)).mpr hsecond
  have hcan : C/(4*C)=(1:ℝ)/4 := by field_simp
  rw [hcan] at hdiv
  apply (div_le_iff₀ (show 0 < 4*C by positivity)).mpr
  change 1 ≤ μ.real A*(4*C)
  nlinarith



end SingleLatticeCovering.Prekopa
namespace SingleLatticeCovering.Prekopa
open MeasureTheory ProbabilityTheory Set Filter Isotropization
open scoped ENNReal RealInnerProductSpace Topology

lemma uniform_body_fourth {d : ℕ} {K : Set (E d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hlp : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    Integrable (fun x : E d => ‖x‖^4) μ ∧
      (∫ x : E d, ‖x‖^4 ∂μ) ≤ fourthMomentConstant*(d:ℝ)^2 := by
  have H (i : Fin d) : Integrable (fun x : E d => (x i)^4) μ ∧
      (∫ x : E d, (x i)^4 ∂μ) ≤ fourthMomentConstant := by
    have hp : ScalarLogConcave (fun t => μ.real {x | t ≤ x i}) := by
      rw [hdef]
      exact scalarLogConcave_uniform_cap hK hc (EuclideanSpace.proj i)
    have hn : ScalarLogConcave (fun t => μ.real {x | t ≤ -(x i)}) := by
      rw [hdef]
      exact scalarLogConcave_uniform_cap hK hc (-EuclideanSpace.proj i)
    exact fourth_moment_bound μ (by fun_prop) (coordinate_memLp hlp i).integrable_sq
      (isotropic_coordinate_second hiso i).le hp hn
  exact fourth_norm_of_coordinates (fun i => (H i).1) (fun i => (H i).2)

lemma fourthMomentConstant_pos : 0 < fourthMomentConstant := by
  unfold fourthMomentConstant
  positivity

lemma uniform_body_radius_lower {d : ℕ} (hd : 0 < d) {K : Set (E d)} (hK : IsCompact K)
    (hc : Convex ℝ K) (μ : Measure (E d)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hlp : MemLp id 2 μ) (hiso : IsIsotropic μ) :
    1/(4*fourthMomentConstant) ≤ μ.real {x | (d:ℝ)/2 ≤ ‖x‖^2} := by
  have hdp : (0:ℝ) < d := Nat.cast_pos.mpr hd
  obtain ⟨hi,h4⟩ := uniform_body_fourth hK hc μ hdef hlp hiso
  have ht : Integrable (fun x : E d => (‖x‖^2/(d:ℝ))^2) μ := by
    simpa only [div_pow,←pow_mul] using hi.div_const ((d:ℝ)^2)
  have hmean : (∫ x : E d, ‖x‖^2/(d:ℝ) ∂μ)=1 := by
    rw [integral_div,isotropic_norm_sq hlp hiso,div_self (ne_of_gt hdp)]
  have hsecond : (∫ x : E d, (‖x‖^2/(d:ℝ))^2 ∂μ) ≤ fourthMomentConstant := by
    simp only [div_pow,←pow_mul]
    rw [integral_div]
    exact (div_le_iff₀ (sq_pos_of_pos hdp)).mpr h4
  have H := paley_zygmund_quarter μ (by fun_prop : Measurable (fun x : E d => ‖x‖^2/(d:ℝ)))
    (hlp.norm.integrable_sq.div_const _) (fun x => by positivity) hmean fourthMomentConstant_pos ht hsecond
  have he : {x : E d | (1:ℝ)/2 ≤ ‖x‖^2/(d:ℝ)}={x | (d:ℝ)/2 ≤ ‖x‖^2} := by
    ext x
    simp only [mem_ofPred_eq,le_div_iff₀ hdp]
    ring_nf
  rwa [he] at H


end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma scaled_gaussian_law {k : ℕ} {v : ℝ} (hv : 0 < v) :
    (stdGaussian (E k)).map (fun z => Real.sqrt v • z)=law k (1/(2*v)) := by
  let := law_probability k (show 0 < 1/(2*v) by positivity)
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_apply,integral_map (by fun_prop) (by fun_prop)]
  have he (y : E k) : ⟪Real.sqrt v • y,t⟫=⟪y,Real.sqrt v • t⟫ := by
    simp only [inner_smul_left,inner_smul_right,conj_trivial]
  simp only [he,←charFun_apply,charFun_stdGaussian,charFun_law (show 0 < 1/(2*v) by positivity)]
  congr 1
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),←Complex.ofReal_pow,mul_pow,
    Real.sq_sqrt hv.le]
  have hvC : (v:ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hv
  push_cast
  field_simp
  ring

lemma measurable_mixture_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    {v : Ω → ℝ} (hv : Measurable v) :
    Measurable (fun p : Ω × E k => density (1/(2*v p.1)) p.2) := by
  unfold density normalizer
  fun_prop

section Integrable
attribute [local irreducible] density normalizer

lemma integrable_mixture_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x) :
    Integrable (fun p : Ω × E k => density (1/(2*v p.1)) p.2) (μ.prod volume) := by
  apply (integrable_prod_iff (measurable_mixture_kernel hm).aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => integrable_density (div_pos zero_lt_one (mul_pos (by norm_num) (hv x)))),?_⟩
  have he (x : Ω) : (∫ y : E k, ‖density (1/(2*v x)) y‖)=1 := by
    have hvx : 0 < 1/(2*v x) := div_pos zero_lt_one (mul_pos (by norm_num) (hv x))
    simp only [Real.norm_eq_abs,abs_of_nonneg (density_pos hvx _).le]
    exact integral_density hvx
  simp only [he]
  exact integrable_const _

lemma mixture_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x) :
    Integrable (fun y : E k => ∫ x, density (1/(2*v x)) y ∂μ) volume :=
  (integrable_mixture_kernel μ hm hv).integral_prod_right

lemma mixture_set_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] [SFinite μ] {v : Ω → ℝ}
    (hm : Measurable v) (hv : ∀ x, 0 < v x) (A : Set (E k)) :
    (∫ y : E k in A, ∫ x, density (1/(2*v x)) y ∂μ)=
      ∫ x, (∫ y : E k in A, density (1/(2*v x)) y) ∂μ := by
  have hj : Integrable (fun p : E k × Ω => density (1/(2*v p.2)) p.1) ((volume.restrict A).prod μ) :=
    ((integrable_mixture_kernel μ hm hv).mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)).swap
  exact integral_integral_swap hj

end Integrable

lemma density_set_integral {k : ℕ} {v : ℝ} (hv : 0 < v) {A : Set (E k)} (hA : MeasurableSet A) :
    (∫ y : E k in A, density (1/(2*v)) y)=
      (stdGaussian (E k)).real {z | Real.sqrt v • z ∈ A} := by
  have hprob := law_probability k (show 0 < 1/(2*v) by positivity)
  have he : (law k (1/(2*v))).real A=∫ y : E k in A, density (1/(2*v)) y := by
    rw [measureReal_def,law,withDensity_apply _ hA,←ofReal_integral_eq_lintegral_ofReal
      (integrable_density (show 0 < 1/(2*v) by positivity)).integrableOn
      (Filter.Eventually.of_forall (fun y => (density_pos (by positivity) y).le)),
      ENNReal.toReal_ofReal (integral_nonneg (fun y => (density_pos (by positivity) y).le))]
  rw [←he,←scaled_gaussian_law hv,measureReal_def,Measure.map_apply (by fun_prop) hA]
  rfl



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma integrable_translated_density {k : ℕ} {b : ℝ} (hb : 0 < b) (w : E k) :
    Integrable (fun y => density b (y-w)) volume := by
  exact ((measurePreserving_sub_right volume w).integrable_comp
    (continuous_density k b).aestronglyMeasurable).mpr (integrable_density hb)

lemma integral_translated_density {k : ℕ} {b : ℝ} (hb : 0 < b) (w : E k) :
    (∫ y, density b (y-w))=1 := by
  rw [integral_sub_right_eq_self,integral_density hb]

attribute [local irreducible] density normalizer

lemma integrable_convolution_kernel {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : Ω × E k => density b (z.2-p z.1)) (μ.prod volume) := by
  have hmm : Measurable (fun z : Ω × E k => density b (z.2-p z.1)) :=
    (continuous_density k b).measurable.comp (measurable_snd.sub (hp.comp measurable_fst))
  apply (integrable_prod_iff hmm.aestronglyMeasurable).mpr
  refine ⟨Filter.Eventually.of_forall (fun x => integrable_translated_density hb (p x)),?_⟩
  have he (x : Ω) : (∫ y : E k, ‖density b (y-p x)‖)=1 := by
    simp only [Real.norm_eq_abs,abs_of_nonneg (density_pos hb _).le]
    exact integral_translated_density hb _
  simp only [he]
  exact integrable_const _

lemma convolution_integrable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    Integrable (fun y : E k => ∫ x, density b (y-p x) ∂μ) volume :=
  (integrable_convolution_kernel μ hp hb).integral_prod_right

lemma convolution_integral {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : Ω → E k} (hp : Measurable p)
    {b : ℝ} (hb : 0 < b) :
    (∫ y : E k, ∫ x, density b (y-p x) ∂μ)=1 := by
  have hj : Integrable (fun z : E k × Ω => density b (z.1-p z.2)) (volume.prod μ) :=
    (integrable_convolution_kernel μ hp hb).swap
  rw [integral_integral_swap hj]
  simp only [integral_translated_density hb]
  simp


end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology

lemma neg_log_one_sub_le {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1/2) :
    -Real.log (1-u) ≤ u+2*u^2 := by
  have _ := hu
  have hp : 0 < 1-u := by linarith
  have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at H
  apply (mul_le_mul_iff_right₀ hp).mp
  have HH := mul_le_mul_of_nonneg_right H hp.le
  rw [sub_mul,inv_mul_cancel₀ (ne_of_gt hp),one_mul] at HH
  have hcube : 0 ≤ u^2*(1-2*u) := mul_nonneg (sq_nonneg _) (by linarith)
  nlinarith

lemma log_one_add_ge {u : ℝ} (hu : 0 ≤ u) : u-u^2 ≤ Real.log (1+u) := by
  have hp : 0 < 1+u := by linarith
  have H := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at H
  apply (mul_le_mul_iff_right₀ hp).mp
  have HH := mul_le_mul_of_nonneg_right H hp.le
  rw [sub_mul,inv_mul_cancel₀ (ne_of_gt hp),one_mul] at HH
  nlinarith [pow_nonneg hu 3]

lemma gaussian_chernoff_upper {k : ℕ} {a : ℝ} (ha : 0 < a) (ha1 : a < 1) (B : ℝ) :
    (stdGaussian (E k)).real {y | B ≤ ‖y‖^2} ≤
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)-a*B/2) := by
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun y : E k => (Real.exp_pos (a*‖y‖^2/2)).le))
    (stdGaussian_integrable_exp_norm_sq (k := k) ha1) (Real.exp (a*B/2))
  have hs : {y : E k | Real.exp (a*B/2) ≤ Real.exp (a*‖y‖^2/2)}={y | B ≤ ‖y‖^2} := by
    ext y
    simp only [mem_ofPred_eq,Real.exp_le_exp]
    exact div_le_div_iff_of_pos_right (by norm_num) |>.trans (mul_le_mul_iff_right₀ ha)
  rw [hs,stdGaussian_laplace_norm_sq ha1] at H
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using H

lemma gaussian_chernoff_lower {k : ℕ} {a : ℝ} (ha : a < 0) (B : ℝ) :
    (stdGaussian (E k)).real {y | ‖y‖^2 ≤ B} ≤
      Real.exp (-((k:ℝ)/2)*Real.log (1-a)-a*B/2) := by
  have ha1 : a < 1 := by linarith
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun y : E k => (Real.exp_pos (a*‖y‖^2/2)).le))
    (stdGaussian_integrable_exp_norm_sq (k := k) ha1) (Real.exp (a*B/2))
  have hs : {y : E k | Real.exp (a*B/2) ≤ Real.exp (a*‖y‖^2/2)}={y | ‖y‖^2 ≤ B} := by
    ext y
    simp only [mem_ofPred_eq,Real.exp_le_exp]
    rw [div_le_div_iff_of_pos_right (by norm_num),mul_le_mul_left_of_neg ha]
  rw [hs,stdGaussian_laplace_norm_sq ha1] at H
  rw [Real.exp_sub]
  apply (le_div_iff₀ (Real.exp_pos _)).mpr
  simpa only [mul_comm] using H

lemma gaussian_norm_sq_upper {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (stdGaussian (E k)).real {y | (1+ε)*(k:ℝ) ≤ ‖y‖^2} ≤ Real.exp (-(k:ℝ)*ε^2/16) := by
  apply (gaussian_chernoff_upper (k := k) (a := ε/4) (by positivity) (by linarith) _).trans
  apply Real.exp_le_exp.mpr
  have H := neg_log_one_sub_le (show (0:ℝ) ≤ ε/4 by positivity) (show ε/4 ≤ 1/2 by linarith)
  have HH := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)/2 by positivity)
  nlinarith

lemma gaussian_norm_sq_lower {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) :
    (stdGaussian (E k)).real {y | ‖y‖^2 ≤ (1-ε)*(k:ℝ)} ≤ Real.exp (-(k:ℝ)*ε^2/16) := by
  have _ := hε1
  apply (gaussian_chernoff_lower (k := k) (a := -ε/4) (by linarith) _).trans
  apply Real.exp_le_exp.mpr
  have H := log_one_add_ge (show (0:ℝ) ≤ ε/4 by positivity)
  have HH := mul_le_mul_of_nonneg_left H (show 0 ≤ (k:ℝ)/2 by positivity)
  rw [show 1-(-ε/4)=1+ε/4 by ring]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ k by positivity) (sq_nonneg ε)]



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology

lemma norm_scaled_sq {k : ℕ} {v : ℝ} (hv : 0 ≤ v) (z : E k) :
    ‖Real.sqrt v • z‖^2=v*‖z‖^2 := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,Real.sq_sqrt hv]

lemma density_small_ball_lower {k : ℕ} {v a ε : ℝ} (hv : 0 < v) (ha : 0 ≤ a)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : v*(1+ε)*(k:ℝ) ≤ a^2) :
    1-Real.exp (-(k:ℝ)*ε^2/16) ≤ ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v)) y := by
  rw [density_set_integral hv (measurableSet_le measurable_norm measurable_const)]
  let A := {z : E k | ‖Real.sqrt v • z‖ ≤ a}
  have hA : MeasurableSet A := measurableSet_le (by fun_prop) measurable_const
  have hs : Aᶜ ⊆ {z : E k | (1+ε)*(k:ℝ) ≤ ‖z‖^2} := by
    intro z hz
    have hz' : a < ‖Real.sqrt v • z‖ := lt_of_not_ge hz
    have hh : a^2 ≤ ‖Real.sqrt v • z‖^2 := pow_le_pow_left₀ ha hz'.le 2
    rw [norm_scaled_sq hv.le] at hh
    change (1+ε)*(k:ℝ) ≤ ‖z‖^2
    nlinarith
  have H := (measureReal_mono (μ := stdGaussian (E k)) hs).trans (gaussian_norm_sq_upper hε hε1)
  rw [probReal_compl_eq_one_sub hA] at H
  change 1-Real.exp (-(k:ℝ)*ε^2/16) ≤ (stdGaussian (E k)).real A
  linarith

lemma density_large_ball_lower {k : ℕ} {v b ε : ℝ} (hv : 0 < v) (hb : 0 ≤ b)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : b^2 ≤ v*(1-ε)*(k:ℝ)) :
    1-Real.exp (-(k:ℝ)*ε^2/16) ≤ ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v)) y := by
  have _ := hb
  rw [density_set_integral hv (measurableSet_lt measurable_const measurable_norm)]
  let A := {z : E k | b < ‖Real.sqrt v • z‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const (by fun_prop)
  have hs : Aᶜ ⊆ {z : E k | ‖z‖^2 ≤ (1-ε)*(k:ℝ)} := by
    intro z hz
    have hz' : ‖Real.sqrt v • z‖ ≤ b := le_of_not_gt hz
    have hh : ‖Real.sqrt v • z‖^2 ≤ b^2 := pow_le_pow_left₀ (norm_nonneg _) hz' 2
    rw [norm_scaled_sq hv.le] at hh
    change ‖z‖^2 ≤ (1-ε)*(k:ℝ)
    nlinarith
  have H := (measureReal_mono (μ := stdGaussian (E k)) hs).trans (gaussian_norm_sq_lower hε hε1)
  rw [probReal_compl_eq_one_sub hA] at H
  change 1-Real.exp (-(k:ℝ)*ε^2/16) ≤ (stdGaussian (E k)).real A
  linarith

lemma mixture_scale_small {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {a ε : ℝ} (ha : 0 ≤ a) (hε : 0 < ε) (hε1 : ε < 1) :
    (1-Real.exp (-(k:ℝ)*ε^2/16))*μ.real {x | v x*(1+ε)*(k:ℝ) ≤ a^2} ≤
      ∫ y : E k in {y | ‖y‖ ≤ a}, ∫ x, density (1/(2*v x)) y ∂μ := by
  classical
  let B := {x | v x*(1+ε)*(k:ℝ) ≤ a^2}
  have hB : MeasurableSet B := measurableSet_le (by fun_prop) measurable_const
  have hkernel : Integrable (fun x => ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v x)) y) μ := by
    exact ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have hpoint (x : Ω) : B.indicator (fun _ => 1-Real.exp (-(k:ℝ)*ε^2/16)) x ≤
      ∫ y : E k in {y | ‖y‖ ≤ a}, density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_small_ball_lower (hv x) ha hε hε1 hx
    · rw [indicator_of_notMem hx]
      exact integral_nonneg (fun y => (density_pos (by have := hv x; positivity) y).le)
  have H := integral_mono ((integrable_const _).indicator hB) hkernel hpoint
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  rw [mixture_set_integral μ hm hv]
  simpa only [B,measureReal_def,mul_comm] using H

lemma mixture_scale_large {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {b ε : ℝ} (hb : 0 ≤ b) (hε : 0 < ε) (hε1 : ε < 1) :
    (1-Real.exp (-(k:ℝ)*ε^2/16))*μ.real {x | b^2 ≤ v x*(1-ε)*(k:ℝ)} ≤
      ∫ y : E k in {y | b < ‖y‖}, ∫ x, density (1/(2*v x)) y ∂μ := by
  classical
  let B := {x | b^2 ≤ v x*(1-ε)*(k:ℝ)}
  have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  have hkernel : Integrable (fun x => ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v x)) y) μ := by
    exact ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have hpoint (x : Ω) : B.indicator (fun _ => 1-Real.exp (-(k:ℝ)*ε^2/16)) x ≤
      ∫ y : E k in {y | b < ‖y‖}, density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_large_ball_lower (hv x) hb hε hε1 hx
    · rw [indicator_of_notMem hx]
      exact integral_nonneg (fun y => (density_pos (by have := hv x; positivity) y).le)
  have H := integral_mono ((integrable_const _).indicator hB) hkernel hpoint
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  rw [mixture_set_integral μ hm hv]
  simpa only [B,measureReal_def,mul_comm] using H



end SingleLatticeCovering.GaussianDensity

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace Topology BigOperators

lemma stdGaussian_norm_second (k : ℕ) :
    (∫ z : E k, ‖z‖^2 ∂stdGaussian (E k))=(k:ℝ) := by
  have hi (i : Fin k) : Integrable (fun x : E k => (x i)^2) (stdGaussian (E k)) := by
    have H := (IsGaussian.memLp_two_id (μ := stdGaussian (E k))).continuousLinearMap_comp (EuclideanSpace.proj i : E k →L[ℝ] ℝ)
    exact H.integrable_sq
  have hinner (u v : E k) : (∫ z : E k, ⟪u,z⟫*⟪v,z⟫ ∂stdGaussian (E k))=⟪u,v⟫ := by
    have H := covarianceBilin_apply (μ := stdGaussian (E k)) IsGaussian.memLp_two_id u v
    simp only [id_eq,integral_id_stdGaussian,sub_zero,covarianceBilin_stdGaussian
      ] at H
    exact H.symm
  have hh (i : Fin k) : (∫ z : E k, (z i)^2 ∂stdGaussian (E k))=1 := by
    have H := hinner (EuclideanSpace.single i 1) (EuclideanSpace.single i 1)
    simpa only [EuclideanSpace.inner_single_left,one_mul,EuclideanSpace.inner_single_right,
      PiLp.single_apply,mul_one,one_pow,←sq,map_one,ite_true] using H
  have he (z : E k) : ‖z‖^2=∑ i, (z i)^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs,sq_abs]
  simp only [he]
  rw [integral_finsetSum _ (fun i _ => hi i)]
  simp only [hh,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

lemma density_tail_markov {k : ℕ} {v T : ℝ} (hv : 0 < v) (hT : 0 < T) :
    (∫ y : E k in {y | T < ‖y‖}, density (1/(2*v)) y) ≤ (k:ℝ)*v/T^2 := by
  rw [density_set_integral hv (measurableSet_lt measurable_const measurable_norm)]
  have hm : Integrable (fun z : E k => ‖Real.sqrt v • z‖^2) (stdGaussian (E k)) := by
    simp only [norm_scaled_sq hv.le]
    exact ((IsGaussian.memLp_two_id (μ := stdGaussian (E k))).norm.integrable_sq).const_mul _
  have H := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun z : E k => sq_nonneg ‖Real.sqrt v • z‖)) hm (T^2)
  have hs : {z : E k | T < ‖Real.sqrt v • z‖} ⊆ {z | T^2 ≤ ‖Real.sqrt v • z‖^2} := by
    intro z hz
    exact pow_le_pow_left₀ hT.le hz.le 2
  have hb := measureReal_mono (μ := stdGaussian (E k)) hs
  simp only [norm_scaled_sq hv.le] at H hb
  change (stdGaussian (E k)).real {z | T < ‖Real.sqrt v • z‖} ≤ (k:ℝ)*v/T^2
  rw [integral_const_mul,stdGaussian_norm_second] at H
  apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
  nlinarith

lemma mixture_tail_markov {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    (hv : ∀ x, 0 < v x) (hi : Integrable v μ) {T : ℝ} (hT : 0 < T) :
    (∫ y : E k in (Metric.closedBall (0:E k) T)ᶜ,
      ∫ x, density (1/(2*v x)) y ∂μ) ≤ (k:ℝ)*(∫ x, v x ∂μ)/T^2 := by
  have he : (Metric.closedBall (0:E k) T)ᶜ={y : E k | T < ‖y‖} := by
    ext y
    simp only [Set.mem_compl_iff,Metric.mem_closedBall,dist_zero_right,not_le,mem_ofPred_eq]
  rw [he,mixture_set_integral μ hm hv]
  have hi' : Integrable (fun x => ∫ y : E k in {y | T < ‖y‖}, density (1/(2*v x)) y) μ :=
    ((integrable_mixture_kernel μ hm hv).mono_measure
      (Measure.prod_mono le_rfl Measure.restrict_le_self)).integral_prod_left
  have H := integral_mono hi' ((hi.const_mul (k:ℝ)).div_const (T^2))
    (fun x => density_tail_markov (hv x) hT)
  simpa only [integral_div,integral_const_mul] using H


end SingleLatticeCovering.GaussianDensity

end
end
end
end
end

section

namespace SingleLatticeCovering.Prekopa
open MeasureTheory Set Filter Sections Isotropization
open scoped ENNReal Topology RealInnerProductSpace

lemma logConcave_smoothed_volume_E {n D : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (A : Isotropization.E n →ₗ[ℝ] Isotropization.E D)
    {c : ℝ} (hcn : 0 ≤ c) :
    LogConcave (fun y => ∫ x in K, Real.exp (-c*‖y-A x‖^2)) := by
  let e := (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toContinuousLinearEquiv
  have hp : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hK' : IsCompact (e '' K) := hK.image e.continuous
  have he (y : Isotropization.E D) : (∫ x in K, Real.exp (-c*‖y-A x‖^2))=
      ∫ z in e '' K, smoothingKernel (A.comp e.symm.toLinearMap) c y z := by
    have H := (hp.restrict_preimage hK'.measurableSet).integral_comp
      e.toHomeomorph.toMeasurableEquiv.measurableEmbedding
      (smoothingKernel (A.comp e.symm.toLinearMap) c y)
    rw [Set.preimage_image_eq _ e.injective] at H
    change (∫ x in K, Real.exp (-c*‖y-A (e.symm (e x))‖^2))=
      ∫ z in e '' K, smoothingKernel (A.comp e.symm.toLinearMap) c y z at H
    simpa only [e.symm_apply_apply] using H
  simp_rw [he]
  exact logConcave_smoothed_volume hK' (hc.linear_image e.toLinearMap) _ hcn

lemma logConcave_smoothed_uniform {n D : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (A : Isotropization.E n →ₗ[ℝ] Isotropization.E D)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    {c : ℝ} (hcn : 0 ≤ c) :
    LogConcave (fun y => ∫ x, Real.exp (-c*‖y-A x‖^2) ∂μ) := by
  rw [hdef]
  simp only [integral_smul_measure,smul_eq_mul]
  exact LogConcave.const_mul (logConcave_smoothed_volume_E hK hc A hcn) ENNReal.toReal_nonneg
end SingleLatticeCovering.Prekopa

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma normalizedProjection_kernel {n k : ℕ} (μ : Measure (Isotropization.E n)) (s r : ℝ)
    (g : MatrixSpace n k) (y : Isotropization.E k) :
    normalizedProjection μ s r g y=∫ x, density (r^2/2) (y-s•colApply g x) ∂μ := by
  rw [normalizedProjection,smoothedProjection,←integral_const_mul]
  congr 1
  funext x
  unfold density
  congr 2
  ring

lemma logConcave_normalizedProjection {n k : ℕ} {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (μ : Measure (Isotropization.E n))
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (s r : ℝ) (g : MatrixSpace n k) :
    LogConcave (normalizedProjection μ s r g) := by
  have H := logConcave_smoothed_uniform hK hc (s • colLinear g) μ hdef (c := r^2/2) (by positivity)
  have he : (fun y => ∫ x, Real.exp (-(r^2/2)*‖y-(s • colLinear g) x‖^2) ∂μ)=
      smoothedProjection μ s r g := by
    funext y
    unfold smoothedProjection
    congr 1
    funext x
    change Real.exp (-(r^2/2)*‖y-s•colApply g x‖^2)=_
    congr 1
    ring
  rw [he] at H
  exact Prekopa.LogConcave.const_mul H (inv_nonneg.mpr (Real.rpow_nonneg (by positivity) _))


end SingleLatticeCovering.GaussianProjection


end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_ProjectionBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma integrable_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsFiniteMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) :
    Integrable (normalizedProjection μ s r g) volume := by
  change Integrable (fun y => normalizedProjection μ s r g y) volume
  simp_rw [normalizedProjection_kernel]
  exact convolution_integrable μ ((s • colLinear g).continuous_of_finiteDimensional.measurable)
    (by have := sq_pos_of_ne_zero hr; positivity)

lemma integral_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) :
    (∫ y, normalizedProjection μ s r g y)=1 := by
  simp_rw [normalizedProjection_kernel]
  exact convolution_integral μ ((s • colLinear g).continuous_of_finiteDimensional.measurable)
    (by have := sq_pos_of_ne_zero hr; positivity)

lemma continuous_normalizedProjection {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsFiniteMeasure μ] (s r : ℝ) (g : MatrixSpace n k) :
    Continuous (normalizedProjection μ s r g) :=
  (continuous_smoothedProjection_y μ s r g).const_mul _

lemma normalizedProjection_pos {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (g : MatrixSpace n k) (y : Isotropization.E k) :
    0 < normalizedProjection μ s r g y := by
  rw [normalizedProjection]
  apply mul_pos (inv_pos.mpr (normalizer_pos k (by have := sq_pos_of_ne_zero hr; positivity)))
  have hi : Integrable (fun x : Isotropization.E n => Real.exp (-r^2*‖y-s•colApply g x‖^2/2)) μ := by
    apply (integrable_const (1:ℝ)).mono' (by
      have hc : Continuous (fun x : Isotropization.E n => colApply g x) := continuous_colApply.comp (continuous_const.prodMk continuous_id)
      fun_prop)
    exact Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using gaussianKernel_bounded r (y-s•colApply g x))
  exact integral_pos_iff_support_of_nonneg (fun x => (Real.exp_pos _).le) hi |>.mpr (by simp [Function.support,ne_of_gt (Real.exp_pos _)])

end SingleLatticeCovering.GaussianProjection

end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma scaleVariance_pos {n : ℕ} (s : ℝ) {r : ℝ} (hr : r ≠ 0) (x : Isotropization.E n) :
    0 < scaleVariance s r x := by
  unfold scaleVariance
  have := sq_pos_of_ne_zero hr
  positivity

lemma scaleVariance_integrable {n : ℕ} {μ : Measure (Isotropization.E n)}
    [IsFiniteMeasure μ] (hμ : MemLp id 2 μ) (s r : ℝ) :
    Integrable (scaleVariance s r) μ := by
  change Integrable (fun x => (s*‖x‖)^2+1/r^2) μ
  simp only [mul_pow]
  exact (hμ.norm.integrable_sq.const_mul _).add (integrable_const _)

lemma scaleVariance_mean {n : ℕ} {μ : Measure (Isotropization.E n)}
    [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s r : ℝ) :
    (∫ x, scaleVariance s r x ∂μ)=s^2*(n:ℝ)+1/r^2 := by
  unfold scaleVariance
  simp only [mul_pow]
  have hi : Integrable (fun x : Isotropization.E n => s^2*‖x‖^2) μ := hμ.norm.integrable_sq.const_mul _
  rw [integral_add hi (integrable_const _),integral_const_mul,
    isotropic_norm_sq hμ hiso]
  simp

lemma normalizedModel_mixture {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (s : ℝ) {r : ℝ} (hr : r ≠ 0) (y : Isotropization.E k) :
    normalizedModel μ s r y=∫ x, density (1/(2*scaleVariance s r x)) y ∂μ :=
  normalized_radialSmoothedDensity_mixture μ s hr y

lemma projectionError_nonneg (n k : ℕ) (s r : ℝ) : 0 ≤ projectionError n k s r := by
  dsimp [projectionError,normalizer]
  positivity

lemma exists_normalized_projection {n k : ℕ} {μ : Measure (Isotropization.E n)} [IsProbabilityMeasure μ]
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) {r : ℝ} (hr : r ≠ 0) :
    ∃ g : MatrixSpace n k, ∀ y : Isotropization.E k,
      |normalizedProjection μ s r g y-normalizedModel μ s r y| ≤ projectionError n k s r := by
  obtain ⟨g,hg⟩ := exists_uniform_smoothed_projection (k := k) hμ hiso s r
  refine ⟨g,fun y => ?_⟩
  have hN : 0 < normalizer k (r^2/2) := normalizer_pos k (by have := sq_pos_of_ne_zero hr; positivity)
  have H := hg y
  rw [←radialSmoothedDensity_cast,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] at H
  unfold normalizedProjection normalizedModel
  rw [←mul_sub,abs_mul,abs_of_nonneg (inv_nonneg.mpr hN.le)]
  have HH := mul_le_mul_of_nonneg_left H (inv_nonneg.mpr hN.le)
  exact HH.trans_eq (by dsimp [projectionError]; ring)



theorem actual_model_shell {n k : ℕ} (hk : 2 ≤ k) {K : Set (Isotropization.E n)}
    (hK : IsCompact K) (hc : Convex ℝ K) (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ) (s : ℝ) {r T : ℝ}
    (hr : r ≠ 0) (hT : 0 < T) :
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      (∫ y : Isotropization.E k in {y | ‖y‖ ≤ (1-ε)*r₀}, normalizedModel μ s r y)+
        (∫ y : Isotropization.E k in {y | (1+ε)*r₀ < ‖y‖}, normalizedModel μ s r y) ≤
      (4*((k-1:ℕ)+1:ℝ)/((k-1:ℕ)*ε)*Real.exp (-((k-1:ℕ):ℝ)*ε^2/9))+
        2*(projectionError n k s r*volume.real (Metric.closedBall (0:Isotropization.E k) T)+
          (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2) := by
  obtain ⟨g,hg⟩ := exists_normalized_projection (k := k) hμ hiso s hr
  have hmod : (normalizedModel μ s r : Isotropization.E k → ℝ)=
      fun y => ∫ x, density (1/(2*scaleVariance s r x)) y ∂μ := by
    funext y; exact normalizedModel_mixture μ s hr y
  have hm : Measurable (scaleVariance (n := n) s r) := by unfold scaleVariance; fun_prop
  have hMi : Integrable (normalizedModel μ s r : Isotropization.E k → ℝ) volume := by
    rw [hmod]; exact mixture_integrable μ hm (scaleVariance_pos s hr)
  have hMn (y : Isotropization.E k) : 0 ≤ normalizedModel μ s r y := by
    rw [hmod]
    exact integral_nonneg (fun x => (density_pos (by have := scaleVariance_pos s hr x; positivity) y).le)
  have hMr (x y : Isotropization.E k) (hxy : ‖x‖=‖y‖) : normalizedModel μ s r x=normalizedModel μ s r y := by
    unfold normalizedModel
    rw [radialSmoothedDensity_norm_eq μ s r hxy]
  obtain ⟨r₀,hr₀,H⟩ := radial_model_shell hk (logConcave_normalizedProjection hK hc μ hdef s r g)
    (normalizedProjection_pos μ s hr g) (continuous_normalizedProjection μ s r g)
    (integrable_normalizedProjection μ s hr g) (integral_normalizedProjection μ s hr g)
    hMi hMn hMr (projectionError_nonneg n k s r) hg T
  refine ⟨r₀,hr₀,fun ε hε hε1 => ?_⟩
  have ht : (∫ y : Isotropization.E k in (Metric.closedBall (0:Isotropization.E k) T)ᶜ,
      normalizedModel μ s r y) ≤ (k:ℝ)*(s^2*(n:ℝ)+1/r^2)/T^2 := by
    simp_rw [normalizedModel_mixture μ s hr]
    have HH := mixture_tail_markov (k := k) μ hm (scaleVariance_pos s hr) (scaleVariance_integrable hμ s r) hT
    rwa [scaleVariance_mean hμ hiso] at HH
  linarith [H ε hε hε1]


end SingleLatticeCovering.GaussianProjection

end

section

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

lemma probability_interval_lower {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {v : Ω → ℝ} (hm : Measurable v) (a b : ℝ) :
    1-μ.real {x | v x ≤ a}-μ.real {x | b ≤ v x} ≤ μ.real {x | a ≤ v x ∧ v x ≤ b} := by
  let B := {x | a ≤ v x ∧ v x ≤ b}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hs : Bᶜ ⊆ {x | v x ≤ a} ∪ {x | b ≤ v x} := by
    intro x hx
    by_cases hxa : a ≤ v x
    · exact Or.inr (le_of_lt (lt_of_not_ge (fun hxb => hx ⟨hxa,hxb⟩)))
    · exact Or.inl (le_of_lt (lt_of_not_ge hxa))
  have H := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le _ _)
  rw [probReal_compl_eq_one_sub hB] at H
  change 1-μ.real {x | v x ≤ a}-μ.real {x | b ≤ v x} ≤ μ.real B
  linarith



theorem mixture_shell_scales {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hk : 0 < k)
    {v : Ω → ℝ} (hm : Measurable v) (hv : ∀ x, 0 < v x)
    {r₀ ε S : ℝ} (hr₀ : 0 < r₀) (hε : 0 < ε) (hε1 : ε < 1)
    (hshell : (∫ y : E k in {y | ‖y‖ ≤ (1-ε)*r₀}, ∫ x, density (1/(2*v x)) y ∂μ)+
      (∫ y : E k in {y | (1+ε)*r₀ < ‖y‖}, ∫ x, density (1/(2*v x)) y ∂μ) ≤ S) :
    1-S/(1-Real.exp (-(k:ℝ)*ε^2/16)) ≤
      μ.real {x | ((1-ε)*r₀)^2/((1+ε)*(k:ℝ)) ≤ v x ∧
        v x ≤ ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))} := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  have hc : 0 < 1-Real.exp (-(k:ℝ)*ε^2/16) := by
    have hh : -(k:ℝ)*ε^2/16 < 0 := by nlinarith [sq_pos_of_pos hε]
    linarith [Real.exp_lt_one_iff.mpr hh]
  let a := ((1-ε)*r₀)^2/((1+ε)*(k:ℝ))
  let b := ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))
  have heA : {x | v x*(1+ε)*(k:ℝ) ≤ ((1-ε)*r₀)^2}={x | v x ≤ a} := by
    ext x
    simp only [mem_ofPred_eq,a,le_div_iff₀ (mul_pos (show 0 < 1+ε by linarith) hkR)]
    ring_nf
  have heB : {x | ((1+ε)*r₀)^2 ≤ v x*(1-ε)*(k:ℝ)}={x | b ≤ v x} := by
    ext x
    simp only [mem_ofPred_eq,b,div_le_iff₀ (mul_pos (show 0 < 1-ε by linarith) hkR)]
    ring_nf
  have HA := mixture_scale_small (k := k) μ hm hv (show 0 ≤ (1-ε)*r₀ by positivity) hε hε1
  have HB := mixture_scale_large (k := k) μ hm hv (show 0 ≤ (1+ε)*r₀ by positivity) hε hε1
  rw [heA] at HA
  rw [heB] at HB
  have Hsum : μ.real {x | v x ≤ a}+μ.real {x | b ≤ v x} ≤ S/(1-Real.exp (-(k:ℝ)*ε^2/16)) := by
    apply (le_div_iff₀ hc).mpr
    nlinarith
  exact le_trans (by linarith) (probability_interval_lower μ hm a b)


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

lemma good_scale_anchors {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {v : Ω → ℝ} (hm : Measurable v) (hi : Integrable v μ) (hn : ∀ x, 0 ≤ v x)
    (hmean : (∫ x, v x ∂μ) ≤ 2) {p u w : ℝ}
    (hbig : p ≤ μ.real {x | 1/2 ≤ v x})
    (hgood : 1-p < μ.real {x | u ≤ v x ∧ v x ≤ w})
    (hhalf : 1/2 ≤ μ.real {x | u ≤ v x ∧ v x ≤ w})
    (huw : w ≤ 2*u) : 1/4 ≤ u ∧ u ≤ 4 := by
  let B := {x | u ≤ v x ∧ v x ≤ w}
  let A := {x | (1:ℝ)/2 ≤ v x}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  have hsum := measureReal_union_add_inter (μ := μ) (s := A) hB
  have hunion : μ.real (A ∪ B) ≤ 1 := by
    simpa only [probReal_univ] using measureReal_mono (μ := μ) (subset_univ (A ∪ B))
  have hp : 0 < μ.real (A ∩ B) := by change p ≤ μ.real A at hbig; change 1-p < μ.real B at hgood; linarith
  have hne : (A ∩ B).Nonempty := by
    by_contra h
    have he : A ∩ B=∅ := Set.not_nonempty_iff_eq_empty.mp h
    rw [he,measureReal_empty] at hp
    exact (lt_irrefl (0:ℝ)) hp
  obtain ⟨x,hxA,hxB⟩ := hne
  have hul : 1/4 ≤ u := by
    change 1/2 ≤ v x at hxA
    change u ≤ v x ∧ v x ≤ w at hxB
    linarith
  have H := mul_meas_ge_le_integral_of_nonneg (μ := μ) (Filter.Eventually.of_forall hn) hi u
  have hmono : μ.real B ≤ μ.real {x | u ≤ v x} := measureReal_mono (fun x hx => hx.1)
  have hh : 1/2 ≤ μ.real {x | u ≤ v x} := hhalf.trans hmono
  constructor
  · exact hul
  · nlinarith

lemma scale_interval_ratio {k : ℕ} (hk : 0 < k) {r ε : ℝ} (hr : 0 < r)
    (hε : 0 ≤ ε) (hε1 : ε < 1) :
    let u := ((1-ε)*r)^2/((1+ε)*(k:ℝ))
    let w := ((1+ε)*r)^2/((1-ε)*(k:ℝ))
    0 < u ∧ u ≤ w ∧ w/u=((1+ε)/(1-ε))^3 := by
  have hkR : (0:ℝ) < k := by exact_mod_cast hk
  dsimp only
  have hp : 0 < 1-ε := by linarith
  have hq : 0 < 1+ε := by linarith
  have hu : 0 < ((1-ε)*r)^2/((1+ε)*(k:ℝ)) := by positivity
  refine ⟨hu,?_,?_⟩
  · apply (div_le_div_iff₀ (mul_pos hq hkR) (mul_pos hp hkR)).mpr
    have H : (1-ε)^3 ≤ (1+ε)^3 := pow_le_pow_left₀ hp.le (by linarith) 3
    have HH := mul_le_mul_of_nonneg_right H (mul_nonneg (sq_nonneg r) hkR.le)
    nlinarith
  · field_simp

lemma scale_ratio_le_two {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) :
    ((1+ε)/(1-ε))^3 ≤ 2 := by
  have hp : 0 < 1-ε := by linarith
  have hh : (1+ε)/(1-ε) ≤ 11/9 := (div_le_iff₀ hp).mpr (by linarith)
  have H := pow_le_pow_left₀ (by positivity : 0 ≤ (1+ε)/(1-ε)) hh 3
  norm_num at H ⊢
  linarith


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma scaleVariance_measurable {n : ℕ} (s r : ℝ) : Measurable (scaleVariance (n := n) s r) := by
  unfold scaleVariance
  fun_prop




theorem actual_good_scales {n k : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10)
    (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
    ∃ u w : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ u ≤ w ∧
      w/u=((1+ε)/(1-ε))^3 ∧
      1-shellLoss n k s r T ε ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} := by
  have hr0 : r ≠ 0 := by linarith
  have hk0 : 0 < k := by omega
  obtain ⟨r₀,hr₀,hsh⟩ := actual_model_shell hk hK hc μ hdef hμ hiso s hr0 hT
  have hshell := hsh ε hε (by linarith)
  simp_rw [normalizedModel_mixture μ s hr0] at hshell
  have hv := scaleVariance_pos (n := n) s hr0
  have hvm := scaleVariance_measurable (n := n) s r
  have hgood := mixture_shell_scales μ hk0 hvm hv hr₀ hε (by linarith) hshell
  let u := ((1-ε)*r₀)^2/((1+ε)*(k:ℝ))
  let w := ((1+ε)*r₀)^2/((1-ε)*(k:ℝ))
  change 1-shellLoss n k s r T ε ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} at hgood
  obtain ⟨hu,huw,hratio⟩ := scale_interval_ratio hk0 hr₀ hε.le (show ε < 1 by linarith)
  change 0 < u at hu
  change u ≤ w at huw
  change w/u=((1+ε)/(1-ε))^3 at hratio
  have ratio2 : w ≤ 2*u := (div_le_iff₀ hu).mp (hratio ▸ scale_ratio_le_two hε.le hε1)
  have hbig : 1/(4*fourthMomentConstant) ≤ μ.real {x | 1/2 ≤ scaleVariance s r x} := by
    apply le_trans (uniform_body_radius_lower hn hK hc μ hdef hμ hiso)
    refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
    change (n:ℝ)/2 ≤ ‖x‖^2 at hx
    change 1/2 ≤ (s*‖x‖)^2+1/r^2
    have H := mul_le_mul_of_nonneg_left hx (sq_nonneg s)
    have hq : 0 ≤ 1/r^2 := by positivity
    nlinarith
  have hmean : (∫ x, scaleVariance s r x ∂μ) ≤ 2 := by
    rw [scaleVariance_mean hμ hiso,hs]
    have hh : 1 ≤ r^2 := by nlinarith
    have hq : 1/r^2 ≤ 1 := (div_le_one (by positivity : 0 < r^2)).mpr hh
    linarith
  obtain ⟨hulo,huhi⟩ := good_scale_anchors μ hvm (scaleVariance_integrable hμ s r)
    (fun x => (hv x).le) hmean hbig (lt_of_lt_of_le (by linarith : 1-1/(4*fourthMomentConstant) < 1-shellLoss n k s r T ε) hgood)
    (le_trans (by linarith : (1:ℝ)/2 ≤ 1-shellLoss n k s r T ε) hgood) ratio2
  exact ⟨u,w,hulo,huhi,huw,hratio,hgood⟩


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal

lemma normalizer_ratio {k : ℕ} {u w : ℝ} (hu : 0 < u) (hw : 0 < w) :
    normalizer k (1/(2*u))/normalizer k (1/(2*w))=(u/w)^((k:ℝ)/2) := by
  unfold normalizer
  have hp : (0:ℝ) < Real.pi := Real.pi_pos
  simp only [one_div,div_inv_eq_mul]
  rw [←Real.div_rpow (by positivity) (by positivity)]
  congr 1
  field_simp

lemma inverse_scale_ratio_lower {u w ε : ℝ} (hu : 0 < u) (hw : 0 < w)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (hratio : w/u=((1+ε)/(1-ε))^3) :
    1-6*ε ≤ u/w := by
  have _ := hu
  have _ := hw
  have hp : 0 < 1-ε := by linarith
  have hq : 0 < 1+ε := by linarith
  have he : u/w=((1-ε)/(1+ε))^3 := by
    have H := congrArg (fun x : ℝ => x⁻¹) hratio
    rw [inv_div,←inv_pow,inv_div] at H
    exact H
  rw [he]
  have hh : 1-2*ε ≤ (1-ε)/(1+ε) := (le_div_iff₀ hq).mpr (by nlinarith)
  have H := pow_le_pow_left₀ (by linarith : 0 ≤ 1-2*ε) hh 3
  have HB := one_add_mul_le_pow (a := -2*ε) (by linarith : -2 ≤ -2*ε) 3
  norm_num only [Nat.cast_ofNat] at HB
  nlinarith

lemma normalizer_ratio_lower {k : ℕ} {u w ε : ℝ} (hu : 0 < u) (huw : u ≤ w)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1/10) (hratio : w/u=((1+ε)/(1-ε))^3)
    (hsmall : (k:ℝ)*ε ≤ 1/48) :
    7/8 ≤ normalizer k (1/(2*u))/normalizer k (1/(2*w)) := by
  have hw : 0 < w := hu.trans_le huw
  rw [normalizer_ratio hu hw]
  have hr0 : 0 < u/w := div_pos hu hw
  have hr1 : u/w ≤ 1 := (div_le_one hw).mpr huw
  have HB := one_add_mul_le_pow (a := -6*ε) (by linarith : -2 ≤ -6*ε) k
  have HP := pow_le_pow_left₀ (by linarith : 0 ≤ 1-6*ε)
    (inverse_scale_ratio_lower hu hw hε hε1 hratio) k
  have HR := Real.rpow_le_rpow_of_exponent_ge hr0 hr1 (show (k:ℝ)/2 ≤ k by have := Nat.cast_nonneg (α := ℝ) k; linarith)
  rw [Real.rpow_natCast] at HR
  have HBB : 1-6*(k:ℝ)*ε ≤ (1-6*ε)^k := by
    calc
      1-6*(k:ℝ)*ε=1+(k:ℝ)*(-6*ε) := by ring
      _ ≤ (1+(-6*ε))^k := HB
      _ = (1-6*ε)^k := by congr 1; ring
  exact le_trans (by nlinarith) (HBB.trans (HP.trans HR))


end SingleLatticeCovering.GaussianDensity

end

section

namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology RealInnerProductSpace

lemma normalizer_variance_mono {k : ℕ} {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normalizer k (1/(2*u)) ≤ normalizer k (1/(2*v)) := by
  unfold normalizer
  have he (a : ℝ) : Real.pi/(1/(2*a))=Real.pi*(2*a) := by simp only [one_div,div_inv_eq_mul]
  simp only [he]
  apply Real.rpow_le_rpow (by positivity) _ (by positivity)
  exact mul_le_mul_of_nonneg_left (by linarith) Real.pi_pos.le

lemma density_variance_le_peak {k : ℕ} {a v : ℝ} (ha : 0 < a) (hav : a ≤ v) (y : E k) :
    density (1/(2*v)) y ≤ (normalizer k (1/(2*a)))⁻¹ := by
  have hv : 0 < v := ha.trans_le hav
  apply le_trans _ (inv_anti₀ (normalizer_pos k (by positivity)) (normalizer_variance_mono ha hav))
  unfold density
  apply mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k (by positivity)).le)
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) (sq_nonneg _)

lemma integrable_mixture_at {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    {a : ℝ} (ha : 0 < a) (hav : ∀ x, a ≤ v x) (y : E k) :
    Integrable (fun x => density (1/(2*v x)) y) μ := by
  apply (integrable_const ((normalizer k (1/(2*a)))⁻¹)).mono' (by
    have H := (measurable_mixture_kernel (k := k) hm).comp (measurable_id.prodMk (measurable_const (a := y)))
    exact H.aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun x => by
    have hvx : 0 < 1/(2*v x) := by have := ha.trans_le (hav x); positivity
    simpa only [Real.norm_eq_abs,abs_of_nonneg (density_pos hvx y).le] using density_variance_le_peak ha (hav x) y)

lemma density_scales_lower {k : ℕ} {u v w : ℝ} (hu : 0 < u) (huv : u ≤ v) (hvw : v ≤ w) (y : E k) :
    (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y ≤
      density (1/(2*v)) y := by
  have hv : 0 < v := hu.trans_le huv
  have hw : 0 < w := hv.trans_le hvw
  have hNu : 0 < normalizer k (1/(2*u)) := normalizer_pos k (by positivity)
  have hNv : 0 < normalizer k (1/(2*v)) := normalizer_pos k (by positivity)
  have hNw : 0 < normalizer k (1/(2*w)) := normalizer_pos k (by positivity)
  have he : (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*(normalizer k (1/(2*u)))⁻¹=
      (normalizer k (1/(2*w)))⁻¹ := by field_simp
  unfold density
  rw [←mul_assoc,he]
  apply mul_le_mul (inv_anti₀ hNv (normalizer_variance_mono hv hvw)) _
    (Real.exp_pos _).le (inv_nonneg.mpr hNv.le)
  apply Real.exp_le_exp.mpr
  have hh : 1/(2*v) ≤ 1/(2*u) := one_div_le_one_div_of_le (by positivity) (by linarith)
  nlinarith [mul_le_mul_of_nonneg_right hh (sq_nonneg ‖y‖)]



theorem mixture_lower {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {v : Ω → ℝ} (hm : Measurable v)
    {a u w : ℝ} (ha : 0 < a) (hav : ∀ x, a ≤ v x) (hu : 0 < u) (huw : u ≤ w)
    (y : E k) :
    μ.real {x | u ≤ v x ∧ v x ≤ w}*
      (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y ≤
      ∫ x, density (1/(2*v x)) y ∂μ := by
  have _ := huw
  classical
  let B := {x | u ≤ v x ∧ v x ≤ w}
  have hB : MeasurableSet B := (measurableSet_le measurable_const hm).inter (measurableSet_le hm measurable_const)
  let c := (normalizer k (1/(2*u))/normalizer k (1/(2*w)))*density (1/(2*u)) y
  have hh (x : Ω) : B.indicator (fun _ => c) x ≤ density (1/(2*v x)) y := by
    by_cases hx : x ∈ B
    · rw [indicator_of_mem hx]
      exact density_scales_lower hu hx.1 hx.2 y
    · rw [indicator_of_notMem hx]
      exact (density_pos (by have := ha.trans_le (hav x); positivity) y).le
  have H := integral_mono ((integrable_const c).indicator hB) (integrable_mixture_at μ hm ha hav y) hh
  rw [integral_indicator hB,integral_const,smul_eq_mul] at H
  simp only [measureReal_def,Measure.restrict_apply_univ] at H
  change μ.real B*c ≤ _ at H
  simpa only [B,c,mul_assoc] using H


end SingleLatticeCovering.GaussianDensity

end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial
open scoped ENNReal Topology RealInnerProductSpace BigOperators



theorem actual_smoothed_lower {n k D : ℕ} (hn : 0 < n) (hk : 2 ≤ k)
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hc : Convex ℝ K)
    (μ : Measure (Isotropization.E n)) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε : ℝ} (hs : s^2*(n:ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48)
    (hloss : shellLoss n k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss n k s r T ε ≤ 1/8) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧ ∃ g : MatrixSpace n D, ∀ y : Isotropization.E D,
      (3/4)*density (1/(2*u)) y-projectionError n D s r ≤ normalizedProjection μ s r g y := by
  have hr0 : r ≠ 0 := by linarith
  obtain ⟨u,w,hulo,huhi,huw,hratio,hgood⟩ := actual_good_scales hn hk hK hc μ hdef hμ hiso hs hr hT hε hε1 hloss hloss8
  have hu : 0 < u := by linarith
  have hratio' := normalizer_ratio_lower hu huw hε.le hε1 hratio hDε
  have hmass : 7/8 ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w} := by linarith
  have hm : Measurable (scaleVariance (n := n) s r) := scaleVariance_measurable s r
  have ha : 0 < 1/r^2 := by positivity
  have hav (x : Isotropization.E n) : 1/r^2 ≤ scaleVariance s r x := by unfold scaleVariance; nlinarith [sq_nonneg (s*‖x‖)]
  have hmodel (y : Isotropization.E D) : (3/4)*density (1/(2*u)) y ≤ normalizedModel μ s r y := by
    rw [normalizedModel_mixture μ s hr0]
    apply le_trans _ (mixture_lower μ hm ha hav hu huw y)
    have hmul := mul_le_mul hmass hratio' (by norm_num : (0:ℝ) ≤ 7/8) (measureReal_nonneg)
    have hp : (3/4:ℝ) ≤ μ.real {x | u ≤ scaleVariance s r x ∧ scaleVariance s r x ≤ w}*
      (normalizer D (1/(2*u))/normalizer D (1/(2*w))) := by nlinarith
    exact mul_le_mul_of_nonneg_right hp (density_pos (by positivity) y).le
  obtain ⟨g,hg⟩ := exists_normalized_projection (k := D) hμ hiso s hr0
  refine ⟨u,hulo,huhi,g,fun y => ?_⟩
  have H := (abs_le.mp (hg y)).1
  linarith [hmodel y]


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal RealInnerProductSpace

lemma densityFloor_pos (k : ℕ) (R : ℝ) : 0 < densityFloor k R := by
  unfold densityFloor
  exact mul_pos (inv_pos.mpr (normalizer_pos k (by norm_num))) (Real.exp_pos _)

lemma variance_density_floor {k : ℕ} {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    {y : E k} (hy : ‖y‖ ≤ 2*(R+1)) : densityFloor k R ≤ density (1/(2*u)) y := by
  have _ := hR
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hN : normalizer k (1/(2*u)) ≤ normalizer k (1/8) := by
    convert normalizer_variance_mono hu0 hu4 using 1 ; norm_num
  unfold densityFloor density
  apply mul_le_mul (inv_anti₀ (normalizer_pos k hb) hN) _ (Real.exp_pos _).le
    (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hy2 := pow_le_pow_left₀ (norm_nonneg y) hy 2
  nlinarith [mul_le_mul_of_nonneg_right hbu (sq_nonneg ‖y‖)]

lemma variance_density_nearby {k : ℕ} {u R δ : ℝ} (hu : 1/4 ≤ u) (hR : 0 ≤ R)
    (hδ : 0 ≤ δ) (hδsmall : δ ≤ 1/(100*(R+1))) {y w : E k}
    (hy : ‖y‖ ≤ 2*R) (hw : ‖w-y‖ ≤ δ) :
    (3/4)*density (1/(2*u)) y ≤ density (1/(2*u)) w := by
  have hu0 : 0 < u := by linarith
  have hb : 0 < 1/(2*u) := by positivity
  have hbu : 1/(2*u) ≤ 2 := (div_le_iff₀ (by positivity)).mpr (by linarith)
  have hδ1 : δ ≤ 1/100 := by
    apply hδsmall.trans
    apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  have hδR : δ*(R+1) ≤ 1/100 := by
    have H := (le_div_iff₀ (by positivity : 0 < 100*(R+1))).mp hδsmall
    nlinarith
  have hwN : ‖w‖ ≤ ‖y‖+δ := by
    have H := norm_add_le (w-y) y
    rw [sub_add_cancel] at H
    linarith
  have hw2 := pow_le_pow_left₀ (norm_nonneg w) hwN 2
  have hdq : δ^2 ≤ δ/100 := by nlinarith
  have hxy : ‖w‖^2-‖y‖^2 ≤ 1/10 := by
    have H := mul_le_mul_of_nonneg_right hy hδ
    nlinarith
  have he : -(1/(2*u))*‖y‖^2-1/4 ≤ -(1/(2*u))*‖w‖^2 := by
    have H := mul_le_mul_of_nonneg_left hxy hb.le
    nlinarith
  have hexp : (3/4)*Real.exp (-(1/(2*u))*‖y‖^2) ≤ Real.exp (-(1/(2*u))*‖w‖^2) := by
    have hl : (3/4:ℝ) ≤ Real.exp (-(1/4:ℝ)) := by linarith [Real.add_one_le_exp (-(1/4:ℝ))]
    calc
      _ ≤ Real.exp (-(1/4:ℝ))*Real.exp (-(1/(2*u))*‖y‖^2) := mul_le_mul_of_nonneg_right hl (Real.exp_pos _).le
      _ = Real.exp (-(1/(2*u))*‖y‖^2-1/4) := by rw [←Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr he
  unfold density
  nlinarith [mul_le_mul_of_nonneg_left hexp (inv_nonneg.mpr (normalizer_pos k hb).le)]


end SingleLatticeCovering.GaussianDensity

end

section

namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma surjective_of_smoothed_lower {n k : ℕ} (μ : Measure (Isotropization.E n))
    [IsProbabilityMeasure μ] (A : Isotropization.E n →ₗ[ℝ] Isotropization.E k)
    {b : ℝ} (hb : 0 < b)
    (hlower : ∀ y : Isotropization.E k, ‖y‖=1 →
      (normalizer k b)⁻¹*Real.exp (-b) < ∫ x, density b (y-A x) ∂μ) : Function.Surjective A := by
  by_contra h
  have hr : A.range ≠ ⊤ := fun htop => h (LinearMap.range_eq_top.mp htop)
  have ho : A.rangeᗮ ≠ ⊥ := fun hbot => hr (Submodule.orthogonal_eq_bot_iff.mp hbot)
  obtain ⟨z,hz,hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ho
  let u := ‖z‖⁻¹ • z
  have hu : ‖u‖=1 := norm_smul_inv_norm hz0
  have huo : u ∈ A.rangeᗮ := A.rangeᗮ.smul_mem _ hz
  have hfar (x : Isotropization.E n) : 1 ≤ ‖u-A x‖^2 := by
    have hh : ⟪u,A x⟫=0 := by
      rw [real_inner_comm]
      exact (Submodule.mem_orthogonal _ _).mp huo (A x) (LinearMap.mem_range_self _ _)
    rw [norm_sub_sq_real,hu,hh]
    nlinarith [sq_nonneg ‖A x‖]
  have hi : Integrable (fun x => density b (u-A x)) μ := by
    apply (integrable_const ((normalizer k b)⁻¹)).mono' (by
      exact ((continuous_density k b).comp (continuous_const.sub A.continuous_of_finiteDimensional)).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_nonneg (density_pos hb _).le]
      unfold density
      apply mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hb.le) (sq_nonneg _)))
  have hp (x : Isotropization.E n) : density b (u-A x) ≤ (normalizer k b)⁻¹*Real.exp (-b) := by
    unfold density
    apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
    apply Real.exp_le_exp.mpr
    nlinarith [hfar x]
  have H := integral_mono hi (integrable_const ((normalizer k b)⁻¹*Real.exp (-b))) hp
  simp only [integral_const,probReal_univ,smul_eq_mul,one_mul] at H
  exact (not_lt_of_ge H) (hlower u hu)


end SingleLatticeCovering.GaussianProjection

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_Desmoothing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section

namespace SingleLatticeCovering.Desmoothing
open Set
open scoped RealInnerProductSpace

lemma convex_escape {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {S : Set E} (hS : Convex ℝ S) (hc : IsClosed S)
    {y : E} (hy : y ∉ S) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ w : E, ‖w-y‖ ≤ δ ∧ ∀ x ∈ S, δ ≤ ‖w-x‖ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨x₀,hx₀⟩
  · exact ⟨y,by simpa using hδ,by simp⟩
  obtain ⟨L,a,hL,ha⟩ := geometric_hahn_banach_closed_point hS hc hy
  have hLne : L ≠ 0 := by
    intro he
    have hh := (hL x₀ hx₀).trans ha
    simp only [he,zero_apply] at hh
    exact lt_irrefl _ hh
  let v := (InnerProductSpace.toDual ℝ E).symm L
  have hv : v ≠ 0 := by
    intro he
    have h := congrArg (InnerProductSpace.toDual ℝ E) he
    apply hLne
    simpa only [v,LinearIsometryEquiv.apply_symm_apply,map_zero] using h
  let u := ‖v‖⁻¹ • v
  have hu : ‖u‖=1 := norm_smul_inv_norm hv
  have hvp : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ⟨y+δ•u,?_,?_⟩
  · simp only [add_sub_cancel_left,norm_smul,Real.norm_eq_abs,abs_of_nonneg hδ,hu,mul_one,le_refl]
  · intro x hx
    have hpos : 0 < ⟪u,y-x⟫ := by
      have he : ⟪v,y-x⟫=L y-L x := by
        rw [inner_sub_right]
        simp only [v,InnerProductSpace.toDual_symm_apply]
      change 0 < ⟪‖v‖⁻¹ • v,y-x⟫
      rw [inner_smul_left,conj_trivial,he]
      exact mul_pos (inv_pos.mpr hvp) (sub_pos.mpr ((hL x hx).trans ha))
    have he : ⟪u,y+δ•u-x⟫=⟪u,y-x⟫+δ := by
      rw [show y+δ•u-x=(y-x)+δ•u by abel,inner_add_right,inner_smul_right,real_inner_self_eq_norm_sq,hu]
      ring
    have H := real_inner_le_norm u (y+δ•u-x)
    rw [he,hu,one_mul] at H
    linarith


end SingleLatticeCovering.Desmoothing

end
end

section

namespace SingleLatticeCovering.Desmoothing
open Set MeasureTheory Isotropization GaussianDensity
open scoped ENNReal RealInnerProductSpace Topology

lemma logConcave_superlevel {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    {c : ℝ} (hc : 0 < c) : Convex ℝ {x | c ≤ f x} := by
  intro x hx y hy a b ha hb hab
  by_cases ha0 : a=0
  · have hb1 : b=1 := by linarith
    simpa only [ha0,hb1,zero_smul,one_smul,zero_add] using hy
  by_cases hb0 : b=0
  · have ha1 : a=1 := by linarith
    simpa only [hb0,ha1,zero_smul,one_smul,add_zero] using hx
  have H := hf.2 x y a b (lt_of_le_of_ne ha (Ne.symm ha0)) (lt_of_le_of_ne hb (Ne.symm hb0)) hab
  have hprod : c^a*c^b ≤ (f x)^a*(f y)^b :=
    mul_le_mul (Real.rpow_le_rpow hc.le hx ha) (Real.rpow_le_rpow hc.le hy hb)
      (Real.rpow_nonneg hc.le _) (Real.rpow_nonneg (hf.1 x) _)
  rw [←Real.rpow_add hc a b,hab,Real.rpow_one] at hprod
  exact hprod.trans H

lemma density_le_peak {k : ℕ} {b : ℝ} (hb : 0 < b) (z : Isotropization.E k) :
    density b z ≤ (normalizer k b)⁻¹ := by
  unfold density
  exact mul_le_of_le_one_right (inv_nonneg.mpr (normalizer_pos k hb).le)
    (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg ‖z‖]))

lemma density_le_tail {k : ℕ} {b δ : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ)
    {z : Isotropization.E k} (hz : δ ≤ ‖z‖) :
    density b z ≤ (normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  unfold density
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos k hb).le)
  apply Real.exp_le_exp.mpr
  have hh := pow_le_pow_left₀ hδ hz 2
  nlinarith

lemma integrable_density_mul {k : ℕ} {f : Isotropization.E k → ℝ} (hi : Integrable f volume)
    {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x => density b (w-x)*f x) volume := by
  apply hi.bdd_mul (c := (normalizer k b)⁻¹) ((continuous_density k b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖density b (w-x)‖ ≤ (normalizer k b)⁻¹
    simpa only [Real.norm_eq_abs,abs_of_nonneg (density_pos hb (w-x)).le] using density_le_peak hb (w-x))

lemma integral_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    (∫ x : Isotropization.E k, density b (w-x))=1 := by
  rw [integral_sub_left_eq_self,integral_density hb]

lemma integrable_density_sub_left {k : ℕ} {b : ℝ} (hb : 0 < b) (w : Isotropization.E k) :
    Integrable (fun x : Isotropization.E k => density b (w-x)) volume := by
  have he (x : Isotropization.E k) : density b (w-x)=density b (x-w) := by
    unfold density
    rw [norm_sub_rev]
  simp only [he]
  exact integrable_translated_density hb w

lemma convolution_upper_of_far_superlevel {k : ℕ} {f : Isotropization.E k → ℝ}
    (hi : Integrable f volume) (hn : ∀ x, 0 ≤ f x) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 ≤ c) (w : Isotropization.E k)
    (hfar : ∀ x, c ≤ f x → δ ≤ ‖w-x‖) :
    (∫ x : Isotropization.E k, density b (w-x)*f x) ≤ c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) := by
  let q := (normalizer k b)⁻¹*Real.exp (-b*δ^2)
  have hq : 0 ≤ q := mul_nonneg (inv_nonneg.mpr (normalizer_pos k hb).le) (Real.exp_pos _).le
  have hpoint (x : Isotropization.E k) : density b (w-x)*f x ≤ c*density b (w-x)+q*f x := by
    by_cases hx : f x ≤ c
    · have H := mul_le_mul_of_nonneg_left hx (density_pos hb (w-x)).le
      nlinarith [mul_nonneg hq (hn x)]
    · have H := mul_le_mul_of_nonneg_right (density_le_tail hb hδ (hfar x (le_of_not_ge hx))) (hn x)
      change density b (w-x)*f x ≤ c*density b (w-x)+q*f x
      linarith [mul_nonneg hc (density_pos hb (w-x)).le]
  have H := integral_mono (integrable_density_mul hi hb w)
    (((integrable_density_sub_left hb w).const_mul c).add (hi.const_mul q)) hpoint
  change (∫ x, density b (w-x)*f x) ≤ ∫ x, c*density b (w-x)+q*f x at H
  rw [integral_add ((integrable_density_sub_left hb w).const_mul c) (hi.const_mul q),
    integral_const_mul,integral_const_mul,integral_density_sub_left hb w,hmass,mul_one,mul_one] at H
  exact H



theorem logConcave_desmoothing {k : ℕ} {f : Isotropization.E k → ℝ} (hf : LogConcave f)
    (hus : UpperSemicontinuous f) (hi : Integrable f volume) (hmass : ∫ x, f x=1)
    {b δ c : ℝ} (hb : 0 < b) (hδ : 0 ≤ δ) (hc : 0 < c) (y : Isotropization.E k)
    (hlower : ∀ w : Isotropization.E k, ‖w-y‖ ≤ δ →
      c+(normalizer k b)⁻¹*Real.exp (-b*δ^2) < ∫ x : Isotropization.E k, density b (w-x)*f x) :
    c ≤ f y := by
  by_contra h
  obtain ⟨w,hw,hfar⟩ := convex_escape (logConcave_superlevel hf hc)
    (hus.isClosed_preimage c) h hδ
  exact (not_lt_of_ge (convolution_upper_of_far_superlevel hi hf.1 hmass hb hδ hc.le w hfar)) (hlower w hw)


end SingleLatticeCovering.Desmoothing

end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal

lemma canonical_nonneg {m D : ℕ} (K : Set ((Fin m → ℝ) × E D)) (y : E D) :
    0 ≤ canonical K y := mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg

lemma canonical_measurable {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    Measurable (canonical K) :=
  ((measurable_fiber_measure volume hK.measurableSet).ennreal_toReal).const_mul _

lemma canonical_usc {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K) :
    UpperSemicontinuous (canonical K) := by
  let C := ((volume K)⁻¹).toReal
  have hC : 0 ≤ C := ENNReal.toReal_nonneg
  intro y t ht
  by_cases hC0 : C=0
  · have hf : canonical K=fun _ => (0 : ℝ) := by funext z; simp [canonical,←show C=((volume K)⁻¹).toReal from rfl,hC0]
    rw [hf] at ht ⊢
    exact Filter.Eventually.of_forall (fun _ => ht)
  have hCp : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
  have hyt : (volume (fiber K y)).toReal < t/C := (lt_div_iff₀ hCp).mpr (by simpa [canonical,mul_comm,C] using ht)
  have H := upperSemicontinuous_fiber_measure volume hK y (ENNReal.ofReal (t/C))
    ((ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK y).measure_ne_top).mpr hyt)
  filter_upwards [H] with z hz
  have hz' := (ENNReal.lt_ofReal_iff_toReal_lt (fiber_compact hK z).measure_ne_top).mp hz
  simpa [canonical,C,mul_comm] using (lt_div_iff₀ hCp).mp hz'

lemma canonical_map {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) :
    Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
      volume.withDensity (fun y => ENNReal.ofReal (canonical K y)) := by
  have hct : (volume K)⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hK0
  have hf (y : E D) : ENNReal.ofReal (canonical K y)= (volume K)⁻¹*volume (fiber K y) := by
    rw [canonical,ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal hct,
      ENNReal.ofReal_toReal (fiber_compact hK y).measure_ne_top]
  have H := map_snd_uniform (volume : Measure (Fin m → ℝ)) (volume : Measure (E D)) hK.measurableSet
  change Measure.map Prod.snd ((volume K)⁻¹ • volume.restrict K)=
    volume.withDensity (fun y => (volume K)⁻¹*volume (fiber K y)) at H
  simpa only [←hf] using H

lemma canonical_mass {m D : ℕ} {K : Set ((Fin m → ℝ) × E D)} (hK : IsCompact K)
    (hK0 : volume K ≠ 0) : Integrable (canonical K) volume ∧ (∫ y, canonical K y)=1 := by
  have hmap := canonical_map hK hK0
  have H := congrArg (fun μ : Measure (E D) => μ univ) hmap
  rw [Measure.map_apply measurable_snd MeasurableSet.univ,Set.preimage_univ,
    Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul,
    ENNReal.inv_mul_cancel hK0 hK.measure_ne_top,withDensity_apply _ MeasurableSet.univ] at H
  simp only [Measure.restrict_univ] at H
  have hm : AEMeasurable (fun y => ENNReal.ofReal (canonical K y)) volume :=
    (canonical_measurable hK).ennreal_ofReal.aemeasurable
  have hi := integrable_toReal_of_lintegral_ne_top hm (H.symm ▸ ENNReal.one_ne_top)
  have he := integral_toReal hm (Filter.Eventually.of_forall (fun y => ENNReal.ofReal_lt_top))
  simp only [ENNReal.toReal_ofReal (canonical_nonneg K _)] at hi he
  exact ⟨hi,by rw [←H,ENNReal.toReal_one] at he; exact he⟩



end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open MeasureTheory MeasureTheory.Measure Set
open scoped ENNReal

lemma map_uniform_coordinates {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
    (μ : Measure E) [IsAddHaarMeasure μ] (ν : Measure F) [IsAddHaarMeasure ν]
    (e : E ≃ₗ[ℝ] F) (K : Set E) :
    Measure.map e ((μ K)⁻¹ • μ.restrict K)=(ν (e '' K))⁻¹ • ν.restrict (e '' K) := by
  let em : E ≃ᵐ F := e.toContinuousLinearEquiv.toHomeomorph.toMeasurableEquiv
  let c : ℝ≥0∞ := addHaarScalarFactor (μ.map e) ν
  have hc : c ≠ 0 := by
    dsimp [c]
    exact_mod_cast (addHaarScalarFactor_pos_of_isAddHaarMeasure (μ.map e) ν).ne'
  have hct : c ≠ ∞ := ENNReal.coe_ne_top
  have hmap : μ.map em=c • ν := isAddLeftInvariant_eq_smul (μ.map e) ν
  have hpre : em ⁻¹' (e '' K)=K := Set.preimage_image_eq _ e.injective
  have hval : μ K=c*ν (e '' K) := by
    have H := congrArg (fun γ : Measure F => γ (e '' K)) hmap
    rw [em.map_apply,hpre] at H
    exact H
  have hrestr : (μ.restrict K).map em=c • ν.restrict (e '' K) := by
    have H := em.restrict_map μ (e '' K)
    rw [hmap,Measure.restrict_smul,hpre] at H
    exact H.symm
  change ((μ K)⁻¹ • μ.restrict K).map em=_
  rw [Measure.map_smul,hrestr,smul_smul]
  congr 1
  rw [hval,ENNReal.mul_inv (Or.inl hc) (Or.inl hct)]
  calc
    c⁻¹*(ν (e '' K))⁻¹*c=(c⁻¹*c)*(ν (e '' K))⁻¹ := by ac_rfl
    _ = (ν (e '' K))⁻¹ := by rw [ENNReal.inv_mul_cancel hc hct,one_mul]


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter Topology Isotropization Sections Prekopa
open scoped ENNReal RealInnerProductSpace

lemma linear_body_properties {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
    (e : E ≃ₗ[ℝ] F) {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K) (hi : (interior K).Nonempty) :
    IsCompact (e '' K) ∧ Convex ℝ (e '' K) ∧ (interior (e '' K)).Nonempty := by
  let H := e.toContinuousLinearEquiv.toHomeomorph
  refine ⟨hK.image H.continuous,hc.linear_image e.toLinearMap,?_⟩
  change (interior (H '' K)).Nonempty
  rw [←H.image_interior]
  exact hi.image H

lemma image_volume_ne_zero {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hi : (interior K).Nonempty) : volume (e '' K) ≠ 0 := by
  have hJ : (interior (e '' K)).Nonempty := by
    change (interior (e.toContinuousLinearEquiv.toHomeomorph '' K)).Nonempty
    rw [←e.toContinuousLinearEquiv.toHomeomorph.image_interior]
    exact hi.image e
  exact ne_of_gt ((isOpen_interior.measure_pos volume hJ).trans_le (measure_mono interior_subset))

lemma projected_uniform_density {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K) :
    μ.map (fun x => (e x).2)=volume.withDensity (fun y => ENNReal.ofReal (canonical (e '' K) y)) := by
  let : IsAddHaarMeasure (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) := by
    change IsAddHaarMeasure ((volume : Measure (Fin m → ℝ)).prod (volume : Measure (Isotropization.E D)))
    exact Measure.prod.instIsAddHaarMeasure _ _
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  rw [hdef]
  change Measure.map (Prod.snd ∘ e.toContinuousLinearEquiv) _ = _
  rw [←Measure.map_map measurable_snd e.toContinuousLinearEquiv.continuous.measurable]
  change Measure.map Prod.snd (Measure.map e _) = _
  rw [LinearCoordinates.map_uniform_coordinates (volume : Measure (Isotropization.E n))
    (volume : Measure ((Fin m → ℝ) × Isotropization.E D)) e K]
  exact canonical_map hJ (image_volume_ne_zero e hi)

lemma projected_convolution {m D n : ℕ}
    (e : Isotropization.E n ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D))
    {K : Set (Isotropization.E n)} (hK : IsCompact K) (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E n)) (hdef : μ=(volume K)⁻¹ • volume.restrict K)
    (b : ℝ) (y : Isotropization.E D) :
    (∫ x, GaussianDensity.density b (y-(e x).2) ∂μ)=
      ∫ z, GaussianDensity.density b (y-z)*canonical (e '' K) z := by
  have H := integral_map (μ := μ) (φ := fun x => (e x).2)
    (f := fun z => GaussianDensity.density b (y-z))
    ((continuous_snd.comp e.toContinuousLinearEquiv.continuous).measurable.aemeasurable)
    (((GaussianDensity.continuous_density D b).comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  rw [projected_uniform_density e hK hi μ hdef] at H
  rw [←H]
  have hJ : IsCompact (e '' K) := hK.image e.toContinuousLinearEquiv.continuous
  have HH := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure (Isotropization.E D)))
    (f := fun z => ENNReal.ofReal (canonical (e '' K) z))
    (g := fun z => GaussianDensity.density b (y-z))
    ((canonical_measurable hJ).ennreal_ofReal)
    (Filter.Eventually.of_forall (fun z => ENNReal.ofReal_lt_top))
  simpa only [ENNReal.toReal_ofReal (canonical_nonneg _ _),smul_eq_mul,mul_comm] using HH


end SingleLatticeCovering.CanonicalDensity

end

section
noncomputable section
namespace SingleLatticeCovering.LinearCoordinates
open LinearMap Module



theorem exists_coordinates {m D : ℕ}
    (A : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] EuclideanSpace ℝ (Fin D))
    (hA : Function.Surjective A) :
    ∃ e : EuclideanSpace ℝ (Fin (m+D)) ≃ₗ[ℝ] ((Fin m → ℝ) × EuclideanSpace ℝ (Fin D)),
      ∀ x, (e x).2=A x := by
  obtain ⟨R,hR⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hA)
  have hR' (y : EuclideanSpace ℝ (Fin D)) : A (R y)=y := by
    have H := LinearMap.congr_fun hR y
    simpa only [LinearMap.comp_apply,LinearMap.id_apply] using H
  let p : EuclideanSpace ℝ (Fin (m+D)) →ₗ[ℝ] A.ker :=
    { toFun := fun x => ⟨x-R (A x),by simp only [LinearMap.mem_ker,map_sub,hR',sub_self]⟩
      map_add' := by intro x y; ext; simp only [map_add,Submodule.coe_add]; abel_nf
      map_smul' := by intro a x; ext; simp only [map_smul,Submodule.coe_smul,smul_sub,RingHom.id_apply] }
  have hbi : Function.Bijective (p.prod A) := by
    constructor
    · intro x y hxy
      have h1 := congrArg (fun z : A.ker × EuclideanSpace ℝ (Fin D) => (z.1 : EuclideanSpace ℝ (Fin (m+D)))) hxy
      have h2 := congrArg Prod.snd hxy
      change A x=A y at h2
      change x-R (A x)=y-R (A y) at h1
      rw [h2] at h1
      exact sub_left_injective h1
    · rintro ⟨z,y⟩
      refine ⟨(z : EuclideanSpace ℝ (Fin (m+D)))+R y,?_⟩
      have he : A (z+R y)=y := by simp only [map_add,hR',LinearMap.mem_ker.mp z.property,zero_add]
      apply Prod.ext
      · apply Subtype.ext
        change z+R y-R (A (z+R y))=z
        rw [he]
        abel
      · exact he
  let e₀ := LinearEquiv.ofBijective (p.prod A) hbi
  have hker : Module.finrank ℝ A.ker=m := by
    have H := A.finrank_range_add_finrank_ker
    rw [LinearMap.range_eq_top.mpr hA,finrank_top,finrank_euclideanSpace_fin,finrank_euclideanSpace_fin] at H
    omega
  let e₁ : A.ker ≃ₗ[ℝ] (Fin m → ℝ) := LinearEquiv.ofFinrankEq _ _ (by simpa only [Module.finrank_fin_fun] using hker)
  refine ⟨e₀.trans (e₁.prodCongr (LinearEquiv.refl ℝ _)),fun x => rfl⟩


end SingleLatticeCovering.LinearCoordinates

end
end

section
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory ProbabilityTheory Set Filter Isotropization GaussianDensity Prekopa Radial CanonicalDensity
open scoped ENNReal Topology RealInnerProductSpace BigOperators

lemma localStep_pos {R : ℝ} (hR : 0 ≤ R) : 0 < localStep R := by unfold localStep; positivity
lemma localStep_le_one {R : ℝ} (hR : 0 ≤ R) : localStep R ≤ 1 := by
  unfold localStep
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith



theorem actual_canonical_lower {m k D : ℕ} (hn : 0 < m+D) (hk : 2 ≤ k)
    {K : Set (Isotropization.E (m+D))} (hK : IsCompact K) (hc : Convex ℝ K)
    (hi : (interior K).Nonempty)
    (μ : Measure (Isotropization.E (m+D))) [IsProbabilityMeasure μ]
    (hdef : μ=(volume K)⁻¹ • volume.restrict K) (hμ : MemLp id 2 μ) (hiso : IsIsotropic μ)
    {s r T ε R : ℝ} (hs : s^2*((m+D : ℕ):ℝ)=1) (hr : 1 ≤ r) (hT : 0 < T)
    (hε : 0 < ε) (hε1 : ε ≤ 1/10) (hDε : (D:ℝ)*ε ≤ 1/48) (hR : 0 ≤ R)
    (hloss : shellLoss (m+D) k s r T ε < 1/(4*fourthMomentConstant))
    (hloss8 : shellLoss (m+D) k s r T ε ≤ 1/8)
    (herr : projectionError (m+D) D s r ≤ densityFloor D R/128)
    (htail : tailError D r R ≤ densityFloor D R/128) :
    ∃ u : ℝ, 1/4 ≤ u ∧ u ≤ 4 ∧
      ∃ e : Isotropization.E (m+D) ≃ₗ[ℝ] ((Fin m → ℝ) × Isotropization.E D),
        ∀ y : Isotropization.E D, ‖y‖ ≤ 2*R →
          density (1/(2*u)) y/2 ≤ canonical (e '' K) y := by
  obtain ⟨u,hu,hu4,g,hg⟩ := actual_smoothed_lower hn hk hK hc μ hdef hμ hiso hs hr hT hε hε1 hDε hloss hloss8
  have hu0 : 0 < u := by linarith
  have hr0 : r ≠ 0 := by linarith
  have hb : 0 < r^2/2 := by positivity
  have hδ : 0 ≤ localStep R := (localStep_pos hR).le
  have hδ1 := localStep_le_one hR
  have hfloor := densityFloor_pos D R
  let A : Isotropization.E (m+D) →ₗ[ℝ] Isotropization.E D := s • colLinear g
  have hconv (y : Isotropization.E D) :
      normalizedProjection μ s r g y = ∫ x, density (r^2/2) (y-A x) ∂μ := by
    exact normalizedProjection_kernel μ s r g y
  have hsurj : Function.Surjective A := by
    apply surjective_of_smoothed_lower μ A hb
    intro y hy
    have hyd : ‖y‖ ≤ 2*(R+1) := by rw [hy]; linarith
    have hl := variance_density_floor hu hu4 hR hyd
    have ht : (normalizer D (r^2/2))⁻¹*Real.exp (-(r^2/2)) ≤ tailError D r R := by
      unfold tailError
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (normalizer_pos D hb).le)
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (localStep R),sq_le_sq₀ hδ (by norm_num : (0:ℝ) ≤ 1) |>.mpr hδ1]
    have H := hg y
    rw [hconv] at H
    linarith
  obtain ⟨e,he⟩ := LinearCoordinates.exists_coordinates A hsurj
  obtain ⟨hJ,hJc,hJi⟩ := linear_body_properties e hK hc hi
  have hmass := canonical_mass hJ (image_volume_ne_zero e hi)
  have heconv (w : Isotropization.E D) : normalizedProjection μ s r g w =
      ∫ z, density (r^2/2) (w-z)*canonical (e '' K) z := by
    rw [hconv]
    simp_rw [←he]
    exact projected_convolution e hK hi μ hdef (r^2/2) w
  refine ⟨u,hu,hu4,e,fun y hy => ?_⟩
  apply Desmoothing.logConcave_desmoothing (f := canonical (e '' K)) (logConcave_canonical_density hJ hJc)
    (canonical_usc hJ) hmass.1 hmass.2 hb hδ (half_pos (density_pos (by positivity) y)) y
  intro w hw
  have hl := variance_density_nearby hu hR hδ (show localStep R ≤ 1/(100*(R+1)) from le_rfl) hy hw
  have hy' : ‖y‖ ≤ 2*(R+1) := by linarith
  have hf := variance_density_floor hu hu4 hR hy'
  have H := hg w
  rw [heconv] at H
  change density (1/(2*u)) y/2+tailError D r R < _
  linarith


end SingleLatticeCovering.GaussianProjection

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal RealInnerProductSpace

lemma normalizer_scaling (D : ℕ) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    normalizer D (b/a^2)=a^D*normalizer D b := by
  unfold normalizer
  rw [show Real.pi/(b/a^2)=a^2*(Real.pi/b) by field_simp,
    Real.mul_rpow (sq_nonneg a) (by positivity),←Real.rpow_natCast a 2,
    ←Real.rpow_mul ha.le]
  norm_num only [Nat.cast_ofNat]
  rw [show (2:ℝ)*((D:ℝ)/2)=(D:ℝ) by ring,Real.rpow_natCast]

lemma density_scaling {D : ℕ} {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (y : E D) :
    a^D*density (b/a^2) (a•y)=density b y := by
  rw [density,density,normalizer_scaling D ha hb,norm_smul,Real.norm_eq_abs,abs_of_pos ha]
  have hpow : a^D ≠ 0 := pow_ne_zero _ (ne_of_gt ha)
  have hN := ne_of_gt (normalizer_pos D hb)
  have he : -(b/a^2)*(a*‖y‖)^2=-b*‖y‖^2 := by field_simp
  rw [he,mul_inv_rev]
  field_simp

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.CanonicalDensity
open MeasureTheory MeasureTheory.Measure Set Isotropization Sections
open scoped ENNReal

lemma verticalScale_fiber {m D : ℕ} {a : ℝ} (ha : a ≠ 0)
    (J : Set ((Fin m → ℝ) × E D)) (y : E D) :
    fiber (verticalScale m D ha '' J) y=fiber J (a⁻¹•y) := by
  ext x
  change (x,y) ∈ verticalScale m D ha '' J ↔ (x,a⁻¹•y) ∈ J
  change (x,y) ∈ (verticalScale m D ha).toEquiv '' J ↔ (x,a⁻¹•y) ∈ J
  rw [(verticalScale m D ha).toEquiv.image_eq_preimage_symm]
  rfl

lemma verticalScale_volume {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) :
    volume (verticalScale m D (ne_of_gt ha) '' J)=ENNReal.ofReal (a^D)*volume J := by
  let S := verticalScale m D (ne_of_gt ha)
  have hm : Measurable (fun y : E D => a⁻¹•y) := by fun_prop
  have H := Measure.map_prod_map (volume : Measure (Fin m → ℝ)) (volume : Measure (E D))
    measurable_id hm
  rw [Measure.map_id,Measure.map_addHaar_smul _ (inv_ne_zero (ne_of_gt ha)),
    finrank_euclideanSpace_fin,inv_pow,inv_inv,abs_of_pos (pow_pos ha D),Measure.prod_smul_right] at H
  change ENNReal.ofReal (a^D) • (volume : Measure ((Fin m → ℝ) × E D)) = Measure.map S.symm volume at H
  have HJ := congrArg (fun μ : Measure ((Fin m → ℝ) × E D) => μ J) H
  rw [Measure.smul_apply,smul_eq_mul,Measure.map_apply (show Measurable S.symm from S.symm.toContinuousLinearEquiv.continuous.measurable) hJ.measurableSet] at HJ
  have he : S.symm ⁻¹' J=S '' J := by
    change S.toEquiv.symm ⁻¹' J=S.toEquiv '' J
    exact S.toEquiv.image_eq_preimage_symm J |>.symm
  rw [he] at HJ
  exact HJ.symm

lemma canonical_verticalScale {m D : ℕ} {a : ℝ} (ha : 0 < a)
    {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J) (y : E D) :
    canonical (verticalScale m D (ne_of_gt ha) '' J) y=(a^D)⁻¹*canonical J (a⁻¹•y) := by
  rw [canonical,verticalScale_fiber,verticalScale_volume ha hJ,
    ENNReal.toReal_inv,ENNReal.toReal_mul,ENNReal.toReal_ofReal (pow_pos ha D).le,mul_inv_rev]
  unfold canonical
  rw [ENNReal.toReal_inv]
  ring

lemma standardize_lower {m D : ℕ} {J : Set ((Fin m → ℝ) × E D)} (hJ : IsCompact J)
    {u R : ℝ} (hu : 1/4 ≤ u) (hu4 : u ≤ 4) (hR : 0 ≤ R)
    (hlow : ∀ y : E D, ‖y‖ ≤ 2*R → GaussianDensity.density (1/(2*u)) y/2 ≤ canonical J y) :
    ∃ S : ((Fin m → ℝ) × E D) ≃ₗ[ℝ] ((Fin m → ℝ) × E D),
      ∀ y : E D, ‖y‖ ≤ R → GaussianDensity.density (1/2) y/2 ≤ canonical (S '' J) y := by
  have hu0 : 0 < u := by linarith
  have ha := Real.sqrt_pos.mpr hu0
  have ha0 := ne_of_gt ha
  refine ⟨verticalScale m D (inv_ne_zero ha0),fun y hy => ?_⟩
  have ha2 : Real.sqrt u ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
  have hy' : ‖Real.sqrt u•y‖ ≤ 2*R := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ha]
    exact (mul_le_mul_of_nonneg_left hy ha.le).trans (mul_le_mul_of_nonneg_right ha2 hR)
  have H := mul_le_mul_of_nonneg_left (hlow _ hy') (pow_pos ha D).le
  rw [canonical_verticalScale (inv_pos.mpr ha) hJ,inv_inv,inv_pow,inv_inv]
  have hd := GaussianDensity.density_scaling (b := (1:ℝ)/2) ha (by norm_num) y
  rw [Real.sq_sqrt hu0.le,show (1/2:ℝ)/u=1/(2*u) by ring] at hd
  rw [←mul_div_assoc,hd] at H
  exact H


end SingleLatticeCovering.CanonicalDensity

end

section
namespace SingleLatticeCovering.GaussianDensity
open MeasureTheory Set
open scoped ENNReal

lemma normalizer_inv_bound (D : ℕ) {r : ℝ} (hr : 0 < r) :
    (normalizer D (r^2/2))⁻¹ ≤ r^D := by
  have H := normalizer_scaling D (inv_pos.mpr hr) (by norm_num : (0:ℝ) < 1/2)
  have he : (1/2:ℝ)/(r⁻¹)^2=r^2/2 := by field_simp
  rw [he,inv_pow] at H
  have hN : 1 ≤ normalizer D (1/2) := by
    unfold normalizer
    apply Real.one_le_rpow (by have hp := Real.pi_gt_three; linarith) (by positivity)
  rw [H,mul_inv_rev,inv_inv]
  exact mul_le_of_le_one_left (pow_pos hr D).le ((inv_le_one₀ (normalizer_pos D (by norm_num))).mpr hN)

lemma volume_closedBall_bound (D : ℕ) {T : ℝ} (hT : 0 ≤ T) :
    volume.real (Metric.closedBall (0:E D) T) ≤ Real.exp (T^2)*normalizer D 1 := by
  have _ := hT
  let B : Set (E D) := Metric.closedBall 0 T
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hkernel := integrable_kernel (k := D) (by norm_num : (0:ℝ) < 1)
  have H := setIntegral_mono_on (integrableOn_const (C := Real.exp (-T^2)) hBc.measure_lt_top.ne)
    hkernel.integrableOn hBc.measurableSet (fun y hy => by
      have hn : ‖y‖ ≤ T := by simpa only [B,Metric.mem_closedBall,dist_zero_right] using hy
      change Real.exp (-T^2) ≤ Real.exp (-1*‖y‖^2)
      apply Real.exp_le_exp.mpr
      nlinarith [pow_le_pow_left₀ (norm_nonneg y) hn 2])
  have hle : (∫ y : E D in B, Real.exp (-1*‖y‖^2)) ≤ normalizer D 1 := by
    rw [←integral_kernel (k := D) (by norm_num : (0:ℝ) < 1)]
    exact setIntegral_le_integral hkernel (Filter.Eventually.of_forall (fun y => (Real.exp_pos _).le))
  rw [setIntegral_const,smul_eq_mul] at H
  have Hm := mul_le_mul_of_nonneg_right (H.trans hle) (Real.exp_pos (T^2)).le
  rw [mul_assoc,←Real.exp_add,neg_add_cancel,Real.exp_zero,mul_one] at Hm
  simpa only [mul_comm] using Hm

lemma normalizer_dimension_mono {D k : ℕ} (hD : D ≤ k) : normalizer D (1/8) ≤ normalizer k (1/8) := by
  unfold normalizer
  apply Real.rpow_le_rpow_of_exponent_le (by have hp := Real.pi_gt_three; linarith)
  exact div_le_div_of_nonneg_right (by exact_mod_cast hD) (by norm_num)

lemma densityFloor_dimension_mono {D k : ℕ} (hD : D ≤ k) (R : ℝ) : densityFloor k R ≤ densityFloor D R := by
  unfold densityFloor
  exact mul_le_mul_of_nonneg_right (inv_anti₀ (normalizer_pos D (by norm_num)) (normalizer_dimension_mono hD))
    (Real.exp_pos _).le

end SingleLatticeCovering.GaussianDensity
namespace SingleLatticeCovering.GaussianProjection
open MeasureTheory Set Isotropization GaussianDensity
open scoped ENNReal

lemma root_error_identity {n k : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 ≤ r) :
    projectionError n k (1/Real.sqrt (n:ℝ)) r =
      (normalizer k (r^2/2))⁻¹*r*Real.sqrt (k:ℝ)/Real.sqrt (Real.sqrt (n:ℝ)) := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  have hsq := Real.sq_sqrt (Real.sqrt_nonneg (n:ℝ))
  have hpos := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hn0)
  unfold projectionError
  rw [abs_of_nonneg (by positivity)]
  have hs := Real.sqrt_pos.mpr hn0
  field_simp
  nlinarith only [congrArg (fun z : ℝ => r*z*Real.sqrt (k:ℝ)/(normalizer k (r^2/2))) hsq]

lemma normalization_second {n : ℕ} (hn : 0 < n) : (1/Real.sqrt (n:ℝ))^2*(n:ℝ)=1 := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast hn
  rw [div_pow,Real.sq_sqrt hn0.le,one_pow,one_div,inv_mul_cancel₀ hn0.ne']

end SingleLatticeCovering.GaussianProjection

end

end OAI
end

section
-- module Solutions.OAIQ16_CD.LatticeCovering_GaussianRates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection Asymptotics
open scoped Topology

lemma A_pos : 0 < A := by unfold A; positivity

lemma normalizer_log (D : ℕ) {b : ℝ} (hb : 0 < b) :
    normalizer D b=Real.exp ((D:ℝ)/2*Real.log (Real.pi/b)) := by
  rw [normalizer,Real.rpow_def_of_pos (by positivity),mul_comm]

lemma floor_inv_bound {l : ℕ} (hl : 1 ≤ l) :
    (densityFloor (l^4) (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hlog : Real.log (8*Real.pi) ≤ 2*(A-392) := by
    have := le_abs_self (Real.log (8*Real.pi))
    unfold A
    linarith [abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  have hN := normalizer_pos (l^4) (by norm_num : (0:ℝ) < 1/8)
  rw [densityFloor,mul_inv_rev,inv_inv,←Real.exp_neg,normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  have hm := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  rw [show Real.pi/(1/8:ℝ)=8*Real.pi by ring]

  nlinarith

lemma polynomial_exp_decay {p q : ℕ} (hpq : p < q) {a b : ℝ} (hb : 0 < b) :
    Tendsto (fun t : ℝ => Real.exp (a*t^p-b*t^q)) atTop (𝓝 0) := by
  have H := (isLittleO_pow_pow_atTop_of_lt (𝕜 := ℝ) hpq).const_mul_left a
  have ht : Tendsto (fun t : ℝ => Real.exp (-(b/2)*t^q)) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    have hh := (tendsto_pow_atTop (by omega : q ≠ 0) : Tendsto (fun t : ℝ => t^q) atTop atTop).const_mul_atTop (half_pos hb)
    simpa only [neg_mul,Function.comp_def] using tendsto_neg_atTop_atBot.comp hh
  apply squeeze_zero' (Filter.Eventually.of_forall (fun t => (Real.exp_pos _).le)) ?_ ht
  filter_upwards [H.bound (half_pos hb),eventually_ge_atTop (0:ℝ)] with t h ht
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (pow_nonneg ht q)] at h
  apply Real.exp_le_exp.mpr
  linarith [le_abs_self (a*t^p)]

lemma errBound_tendsto : Tendsto errBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp (B*t^20-t^30)) atTop (𝓝 0)
  simpa only [one_mul] using (polynomial_exp_decay (a := B) (p := 20) (q := 30) (by omega) (b := 1) (by norm_num))
lemma tailBound_tendsto : Tendsto tailBound atTop (𝓝 0) := by
  change Tendsto (fun t : ℝ => Real.exp ((A+10)*t^6-t^16/980000)) atTop (𝓝 0)
  convert (polynomial_exp_decay (a := A+10) (p := 6) (q := 16) (by omega) (b := 1/980000) (by norm_num)) using 1
  all_goals try with_reducible_and_instances rfl
  ext t
  congr 1
  ring

lemma gaussian_prefactor_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹*(l:ℝ)^10*Real.sqrt (D:ℝ) ≤ Real.exp (22*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hr : 1 ≤ (l:ℝ)^10 := one_le_pow₀ ht
  have hp := normalizer_inv_bound D (pow_pos ht0 10)
  have hpd : ((l:ℝ)^10)^D ≤ ((l:ℝ)^10)^(l^4) := pow_le_pow_right₀ hr hD
  have hs : Real.sqrt (D:ℝ) ≤ (l:ℝ)^2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by simpa only [←pow_mul,Nat.reduceMul] using (show (D:ℝ) ≤ (l:ℝ)^4 by exact_mod_cast hD)⟩
  calc
    _ ≤ (((l:ℝ)^10)^(l^4))*(l:ℝ)^10*(l:ℝ)^2 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_right (hp.trans hpd) (by positivity)) hs (Real.sqrt_nonneg _) (by positivity)
    _ = Real.exp (((l:ℝ)^4*10+12)*Real.log (l:ℝ)) := by
      rw [show (((l:ℝ)^4*10+12)*Real.log (l:ℝ))=
        (l^4:ℕ)*(10*Real.log (l:ℝ))+10*Real.log (l:ℝ)+2*Real.log (l:ℝ) by push_cast; ring,
        Real.exp_add,Real.exp_add,Real.exp_nat_mul]
      rw [show Real.exp (10*Real.log (l:ℝ))=(l:ℝ)^10 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 10,
        show Real.exp (2*Real.log (l:ℝ))=(l:ℝ)^2 by simpa only [Nat.cast_ofNat,Real.exp_log ht0] using Real.exp_nat_mul (Real.log (l:ℝ)) 2]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      have ht4 : 1 ≤ (l:ℝ)^4 := one_le_pow₀ ht
      have hlog := Real.log_le_sub_one_of_pos ht0
      have hh := mul_le_mul_of_nonneg_left (show Real.log (l:ℝ) ≤ l by linarith) (show 0 ≤ (l:ℝ)^4*10+12 by positivity)
      nlinarith [mul_le_mul_of_nonneg_right ht4 ht0.le]

lemma volume_parameter_bound {l : ℕ} (hl : 1 ≤ l) :
    volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤
      Real.exp ((l:ℝ)^20+A*(l:ℝ)^4) := by
  have hlog : Real.log Real.pi ≤ 2*A := by
    unfold A
    linarith [le_abs_self (Real.log Real.pi),abs_nonneg (Real.log (8*Real.pi)),abs_nonneg (Real.log Real.pi)]
  apply (volume_closedBall_bound (l^4) (by positivity : 0 ≤ (l:ℝ)^10)).trans
  rw [normalizer_log _ (by norm_num),←Real.exp_add]
  push_cast
  apply Real.exp_le_exp.mpr
  simp only [div_one]
  have := mul_le_mul_of_nonneg_left hlog (show 0 ≤ (l:ℝ)^4/2 by positivity)
  nlinarith [show ((l:ℝ)^10)^2=(l:ℝ)^20 by ring]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

lemma powerCoeff_bound {l : ℕ} (hl : 1 ≤ l) :
    22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20 ≤ B*(l:ℝ)^20 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have h5 : (l:ℝ)^5 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have h4 : (l:ℝ)^4 ≤ (l:ℝ)^20 := pow_le_pow_right₀ ht (by omega)
  have hh := mul_le_mul_of_nonneg_left h4 A_pos.le
  dsimp [B]
  nlinarith [pow_nonneg (Nat.cast_nonneg l : (0:ℝ) ≤ l) 20,A_pos]

lemma uniform_error_bound {n l D : ℕ} (hn : 0 < n) (hl : 1 ≤ l) (hD : D ≤ l^4)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n D (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ≤
      densityFloor D (6*(l:ℝ)^2)*errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_div,div_eq_mul_inv, mul_inv_rev]
  calc
    _ ≤ Real.exp (22*(l:ℝ)^5)* Real.exp (A*(l:ℝ)^4)*(Real.exp ((l:ℝ)^30))⁻¹ := by
      have hi := inv_anti₀ (Real.exp_pos ((l:ℝ)^30)) hroot
      have hp := gaussian_prefactor_bound hl hD
      rw [←mul_assoc]
      exact mul_le_mul (mul_le_mul hp hinv (inv_pos.mpr hf).le (Real.exp_pos _).le) hi (inv_pos.mpr hq).le (by positivity)
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^30) := by rw [←Real.exp_neg,←Real.exp_add,←Real.exp_add]; rfl
    _ ≤ errBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have hh := powerCoeff_bound hl
      linarith [pow_nonneg ht.le 20]

lemma uniform_ball_error {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ))) :
    projectionError n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10)*
        volume.real (Metric.closedBall (0:Isotropization.E (l^4)) ((l:ℝ)^10)) ≤ errBound (l:ℝ) := by
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  have hq := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn))
  rw [root_error_identity hn (pow_nonneg ht.le 10),div_mul_eq_mul_div]
  calc
    _ ≤ (Real.exp (22*(l:ℝ)^5)*Real.exp ((l:ℝ)^20+A*(l:ℝ)^4))/Real.exp ((l:ℝ)^30) := by
      apply div_le_div₀ (by positivity) (by gcongr; exact gaussian_prefactor_bound hl le_rfl; exact volume_parameter_bound hl)
        (Real.exp_pos _) hroot
    _ = Real.exp (22*(l:ℝ)^5+A*(l:ℝ)^4+(l:ℝ)^20-(l:ℝ)^30) := by
      rw [div_eq_mul_inv,←Real.exp_neg,←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ errBound (l:ℝ) := Real.exp_le_exp.mpr (sub_le_sub_right (powerCoeff_bound hl) _)

lemma kernel_normalizer_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    (normalizer D (((l:ℝ)^10)^2/2))⁻¹ ≤ Real.exp (10*(l:ℝ)^5) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  apply (normalizer_inv_bound D (pow_pos ht0 10)).trans
  apply (pow_le_pow_right₀ (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) hD).trans
  rw [←Real.exp_log (pow_pos (pow_pos ht0 10) (l^4)),Real.log_pow,Real.log_pow]
  apply Real.exp_le_exp.mpr
  push_cast
  have hh := mul_le_mul_of_nonneg_left (le_trans (Real.log_le_sub_one_of_pos ht0) (by linarith : (l:ℝ)-1 ≤ l))
    (show 0 ≤ 10*(l:ℝ)^4 by positivity)
  nlinarith

lemma tail_exponent_bound {l : ℕ} (hl : 1 ≤ l) :
    (l:ℝ)^16/980000 ≤ (((l:ℝ)^10)^2/2)*(localStep (6*(l:ℝ)^2))^2 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht2 : 1 ≤ (l:ℝ)^2 := one_le_pow₀ ht
  have hR : (6*(l:ℝ)^2+1)^2 ≤ 49*(l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-1)]
  unfold localStep
  have hd : 0 < 6*(l:ℝ)^2+1 := by positivity
  field_simp
  nlinarith [mul_le_mul_of_nonneg_left hR (show 0 ≤ (l:ℝ)^16 by positivity),
    show ((l:ℝ)^10)^2=(l:ℝ)^16*(l:ℝ)^4 by ring]

lemma uniform_tail_bound {l D : ℕ} (hl : 1 ≤ l) (hD : D ≤ l^4) :
    tailError D ((l:ℝ)^10) (6*(l:ℝ)^2) ≤ densityFloor D (6*(l:ℝ)^2)*tailBound (l:ℝ) := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  rw [mul_comm (densityFloor D (6*(l:ℝ)^2))]
  apply (div_le_iff₀ hf).mp
  have hinv : (densityFloor D (6*(l:ℝ)^2))⁻¹ ≤ Real.exp (A*(l:ℝ)^4) :=
    (inv_anti₀ (densityFloor_pos (l^4) _) (densityFloor_dimension_mono hD _)).trans (floor_inv_bound hl)
  unfold tailError
  rw [div_eq_mul_inv]
  calc
    _ ≤ Real.exp (10*(l:ℝ)^5)*Real.exp (-(l:ℝ)^16/980000)*Real.exp (A*(l:ℝ)^4) := by
      apply mul_le_mul (mul_le_mul (kernel_normalizer_bound hl hD) (Real.exp_le_exp.mpr (by linarith [tail_exponent_bound hl]))
        (Real.exp_pos _).le (Real.exp_pos _).le) hinv (inv_pos.mpr hf).le (by positivity)
    _ = Real.exp (10*(l:ℝ)^5+A*(l:ℝ)^4-(l:ℝ)^16/980000) := by
      rw [←Real.exp_add,←Real.exp_add]; congr 1; ring
    _ ≤ tailBound (l:ℝ) := by
      apply Real.exp_le_exp.mpr
      have h5 : (l:ℝ)^5 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      have h4 : (l:ℝ)^4 ≤ (l:ℝ)^6 := pow_le_pow_right₀ ht (by omega)
      nlinarith [mul_le_mul_of_nonneg_left h4 A_pos.le]

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter GaussianDensity GaussianProjection
open scoped Topology

lemma shellRate_tendsto : Tendsto shellRate atTop (𝓝 0) := by
  have H := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (1:ℝ) (1/180000) (by norm_num)
  have H' : Tendsto (fun t : ℝ => 800*(t*Real.exp (-(1/180000)*t))) atTop (𝓝 0) := by
    simpa only [Real.rpow_one,mul_zero] using H.const_mul 800
  change Tendsto (fun t : ℝ => 800*t*Real.exp (-t^2/180000)) atTop (𝓝 0)
  apply squeeze_zero' ?_ ?_ H'
  · filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
    exact mul_nonneg (mul_nonneg (by norm_num) ht) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with t ht
    have ht0 : 0 ≤ t := by linarith
    rw [←mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.exp_le_exp.mpr
    nlinarith

lemma denRate_tendsto : Tendsto denRate atTop (𝓝 0) := by
  have H : Tendsto (fun t : ℝ => t^2/160000) atTop atTop :=
    (tendsto_pow_atTop (by omega : (2:ℕ) ≠ 0)).atTop_div_const (by norm_num)
  change Tendsto (fun t : ℝ => Real.exp (-t^2/160000)) atTop (𝓝 0)
  simpa only [Function.comp_def,neg_div] using Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp H)

lemma shellBound_tendsto : Tendsto shellBound atTop (𝓝 0) := by
  have HP : Tendsto (fun t : ℝ => t^16) atTop atTop := tendsto_pow_atTop (by omega)
  have H : Tendsto (fun t : ℝ => 2/t^16) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      ((tendsto_inv_atTop_zero.comp HP).const_mul (2:ℝ))
  change Tendsto (fun t : ℝ => 2*(shellRate t+2*(errBound t+2/t^16))) atTop (𝓝 0)
  simpa only [zero_add,add_zero,mul_zero] using
    (shellRate_tendsto.add ((errBound_tendsto.add H).const_mul 2)).const_mul 2

lemma shell_term_bound {l : ℕ} (hl : 2 ≤ l) :
    (4*((l^4-1:ℕ)+1:ℝ)/((l^4-1:ℕ)*(1/(100*(l:ℝ))))*
      Real.exp (-((l^4-1:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/9)) ≤ shellRate (l:ℝ) := by
  have ht : (2:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := by linarith
  have h4 : (2:ℝ) ≤ (l:ℝ)^4 := by nlinarith [sq_nonneg ((l:ℝ)^2-2),sq_nonneg ((l:ℝ)-2)]
  have hk : 1 ≤ l^4 := by exact_mod_cast (show (1:ℝ) ≤ (l:ℝ)^4 by linarith)
  have hm : ((l^4-1:ℕ):ℝ)=(l:ℝ)^4-1 := by rw [Nat.cast_sub hk,Nat.cast_pow,Nat.cast_one]
  rw [hm]
  have hp : 4*((l:ℝ)^4-1+1)/(((l:ℝ)^4-1)*(1/(100*(l:ℝ)))) ≤ 800*(l:ℝ) := by
    apply (div_le_iff₀ (mul_pos (by linarith : 0 < (l:ℝ)^4-1) (by positivity))).mpr
    have he : 800*(l:ℝ)*(((l:ℝ)^4-1)*(1/(100*(l:ℝ))))=8*((l:ℝ)^4-1) := by field_simp; ring
    rw [he]
    linarith
  have he : -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9 ≤ -(l:ℝ)^2/180000 := by
    rw [show -((l:ℝ)^4-1)*(1/(100*(l:ℝ)))^2/9=-(((l:ℝ)^4-1)/(90000*(l:ℝ)^2)) by field_simp; ring,
      neg_div,neg_le_neg_iff]
    apply (le_div_iff₀ (by positivity : 0 < 90000*(l:ℝ)^2)).mpr
    nlinarith
  exact mul_le_mul hp (Real.exp_le_exp.mpr he) (Real.exp_pos _).le (by positivity)

lemma denominator_identity {l : ℕ} (hl : 1 ≤ l) :
    Real.exp (-((l^4:ℕ):ℝ)*(1/(100*(l:ℝ)))^2/16)=denRate (l:ℝ) := by
  have ht0 : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold denRate
  congr 1
  push_cast
  field_simp
  ring

lemma markov_term_bound {n l : ℕ} (hn : 0 < n) (hl : 1 ≤ l) :
    ((l^4:ℕ):ℝ)*((1/Real.sqrt (n:ℝ))^2*(n:ℝ)+1/((l:ℝ)^10)^2)/((l:ℝ)^10)^2 ≤ 2/(l:ℝ)^16 := by
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  rw [normalization_second hn,Nat.cast_pow]
  have h1 : 1/((l:ℝ)^10)^2 ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (one_le_pow₀ ht))
  calc
    _ ≤ (l:ℝ)^4*2/((l:ℝ)^10)^2 := by gcongr; linarith
    _ = _ := by field_simp

lemma uniform_shell_bound {n l : ℕ} (hn : 0 < n) (hl : 2 ≤ l)
    (hroot : Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt (n:ℝ)))
    (hden : denRate (l:ℝ) ≤ 1/2) :
    shellLoss n (l^4) (1/Real.sqrt (n:ℝ)) ((l:ℝ)^10) ((l:ℝ)^10) (1/(100*(l:ℝ))) ≤ shellBound (l:ℝ) := by
  have hl1 : 1 ≤ l := by omega
  have ht : (0:ℝ) < l := by exact_mod_cast (show 0 < l by omega)
  unfold shellLoss shellError
  rw [denominator_identity hl1]
  have hd : 0 < 1-denRate (l:ℝ) := by linarith
  apply (div_le_iff₀ hd).mpr
  have H := shell_term_bound hl
  have HE := uniform_ball_error hn hl1 hroot
  have HM := markov_term_bound hn hl1
  have hh : 0 ≤ shellRate (l:ℝ)+2*(errBound (l:ℝ)+2/(l:ℝ)^16) := by
    dsimp [shellRate,errBound]; positivity
  dsimp [shellBound]
  nlinarith

lemma uniform_numeric_conditions : ∀ᶠ l : ℕ in atTop,
    2 ≤ l ∧ denRate (l:ℝ) ≤ 1/2 ∧ errBound (l:ℝ) ≤ 1/128 ∧ tailBound (l:ℝ) ≤ 1/128 ∧
    shellBound (l:ℝ) < 1/(4*Prekopa.fourthMomentConstant) ∧ shellBound (l:ℝ) ≤ 1/8 := by
  have hfourth : 0 < Prekopa.fourthMomentConstant := Prekopa.fourthMomentConstant_pos
  have hnat : Tendsto (fun l : ℕ => (l:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (2:ℕ),
    (denRate_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/2)),
    (errBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (tailBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/128)),
    (shellBound_tendsto.comp hnat).eventually (eventually_lt_nhds (by positivity : (0:ℝ) < 1/(4*Prekopa.fourthMomentConstant))),
    (shellBound_tendsto.comp hnat).eventually (eventually_le_nhds (by norm_num : (0:ℝ) < 1/8))]
    with l h1 h2 h3 h4 h5 h6
  exact ⟨h1,h2,h3,h4,h5,h6⟩

end SingleLatticeCovering.GaussianNumerics

end

section
namespace SingleLatticeCovering.GaussianNumerics
open MeasureTheory Filter Set GaussianDensity GaussianProjection CanonicalDensity
open scoped Topology ENNReal




theorem eventually_local_position_oai : ∀ᶠ l : ℕ in atTop,
    ∀ m D : ℕ, D ≤ l → 0 < m+D →
      Real.exp ((l:ℝ)^30) ≤ Real.sqrt (Real.sqrt ((m+D : ℕ):ℝ)) →
      ∀ K : Set (E (m+D)), IsCompact K → Convex ℝ K → (interior K).Nonempty →
        ∃ e : E (m+D) ≃ᵃ[ℝ] ((Fin m → ℝ) × E D),
          ∀ y : E D, ‖y‖ ≤ 6*(l:ℝ)^2 → density (1/2) y/2 ≤ canonical (e '' K) y := by
  filter_upwards [uniform_numeric_conditions] with l hl
  obtain ⟨hl2,hden,herr,htail,hloss,hloss8⟩ := hl
  have hl1 : 1 ≤ l := by omega
  have ht : (1:ℝ) ≤ l := by exact_mod_cast hl1
  have ht0 : (0:ℝ) < l := lt_of_lt_of_le zero_lt_one ht
  have hl4 : l ≤ l^4 := Nat.le_self_pow (by omega) l
  have hk : 2 ≤ l^4 := hl2.trans hl4
  intro m D hD hn hroot K hK hc hi
  have hDk : D ≤ l^4 := hD.trans hl4
  obtain ⟨g,hJ,hJc,hJi,hprob,hmem,hiso,_,_,_⟩ := Isotropization.isotropic_logConcave_affine_body hK hc hi
  let := hprob
  have hε : (0:ℝ) < 1/(100*(l:ℝ)) := by positivity
  have hε1 : (1:ℝ)/(100*(l:ℝ)) ≤ 1/10 := by
    apply (div_le_iff₀ (by positivity)).mpr
    linarith
  have hDε : (D:ℝ)*(1/(100*(l:ℝ))) ≤ 1/48 := by
    have hd : (D:ℝ) ≤ l := by exact_mod_cast hD
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    nlinarith
  have hShell := uniform_shell_bound hn hl2 hroot hden
  have hErr := uniform_error_bound hn hl1 hDk hroot
  have hTail := uniform_tail_bound hl1 hDk
  have hf := densityFloor_pos D (6*(l:ℝ)^2)
  obtain ⟨u,hu,hu4,e,he⟩ := actual_canonical_lower hn hk hJ hJc hJi
    (Isotropization.uniformLaw (g '' K)) rfl hmem hiso (normalization_second hn)
    (one_le_pow₀ ht : 1 ≤ (l:ℝ)^10) (pow_pos ht0 10) hε hε1 hDε
    (show 0 ≤ 6*(l:ℝ)^2 by positivity) (hShell.trans_lt hloss) (hShell.trans hloss8)
    (hErr.trans (by nlinarith [mul_le_mul_of_nonneg_left herr hf.le]))
    (hTail.trans (by nlinarith [mul_le_mul_of_nonneg_left htail hf.le]))
  have hcomp : IsCompact (e '' (g '' K)) := hJ.image e.toContinuousLinearEquiv.continuous
  obtain ⟨S,hS⟩ := standardize_lower hcomp hu hu4 (show 0 ≤ 6*(l:ℝ)^2 by positivity) he
  refine ⟨g.trans (e.trans S).toAffineEquiv,fun y hy => ?_⟩
  have himage : (g.trans (e.trans S).toAffineEquiv) '' K=S '' (e '' (g '' K)) := by
    rw [Set.image_image,Set.image_image]
    rfl
  rw [himage]
  exact hS y hy


end SingleLatticeCovering.GaussianNumerics

end




end OAI
end

theorem solution : type_of% @OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position_oai := @OAI.SingleLatticeCovering.GaussianNumerics.eventually_local_position_oai
