-- Prove2me | solution 1 for OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T01:06:22.547943+00:00
-- url     : https://prove2.me/submissions/2b4c9eb2-d948-499f-882f-9b5b9b0bfc0d

import Mathlib
import Definitions.Def_OAIQ240Bp017
import Definitions.Def_OAIQ240Bp019
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_ProperIndexZeroPath_cylinder_supplement_bp240
import Theorems.Thm_OAI_HigherDimensionalBallPacking_Rigidity_augment_fredholm_bp240

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_HomotopyFlux
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Filter MeasureTheory
variable {m : ℕ}

lemma formFlux_differentiable
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (i : Fin (m+1)) : Differentiable ℝ (formFlux w i) := by
  exact ((ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth coordinateVector)).differentiable.comp hw).const_smul ((-1:ℝ)^i.val)

lemma formFlux_divergence
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : Differentiable ℝ w) (x : CoordinateSpace (m+1)) :
    (∑ i, fderiv ℝ (formFlux w i) x (coordinateVector i))=extDeriv w x coordinateVector := by
  rw [extDeriv_apply (hw x)]
  apply Finset.sum_congr rfl
  intro i hi
  have he : DifferentiableAt ℝ (fun y => w y (i.removeNth coordinateVector)) x :=
    (ContinuousAlternatingMap.apply ℝ _ ℝ (i.removeNth coordinateVector)).differentiableAt.comp x (hw x)
  change fderiv ℝ (fun y => (-1:ℝ)^i.val • w y (i.removeNth coordinateVector)) x
    (coordinateVector i)=_
  rw [fderiv_fun_const_smul he]
  simp only [smul_apply,smul_eq_mul,zsmul_eq_mul,Int.cast_pow,Int.cast_neg,Int.cast_one]

lemma coordinateVolume_basis : coordinateVolume m coordinateVector=1 := by
  change (Pi.basisFun ℝ (Fin m)).det _=1
  have he : (coordinateVector : Fin m → CoordinateSpace m)=Pi.basisFun ℝ (Fin m) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin m) i).symm
  rw [he]
  exact Module.Basis.det_self _


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {d : ℕ}

lemma topForm_evaluation (w : CoordinateSpace d [⋀^Fin d]→L[ℝ] ℝ)
    (A : CoordinateSpace d →L[ℝ] CoordinateSpace d) :
    w (fun i => A (coordinateVector i))=A.det*w coordinateVector := by
  have hb : (coordinateVector : Fin d → CoordinateSpace d)=Pi.basisFun ℝ (Fin d) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin d) i).symm
  change w.toAlternatingMap (A ∘ coordinateVector)=_
  have he := w.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin d))
  conv_lhs => rw [he]
  simp only [AlternatingMap.smul_apply,smul_eq_mul,hb]
  change w (Pi.basisFun ℝ (Fin d)) *
    (Pi.basisFun ℝ (Fin d)).det (A.toLinearMap ∘ Pi.basisFun ℝ (Fin d))=_
  rw [Module.Basis.det_comp,Module.Basis.det_self,mul_one]
  exact mul_comm _ _

variable {M : Type*} [TopologicalSpace M]

theorem topForm_chartMass_change [T2Space M]
    (c b : OpenPartialHomeomorph M (CoordinateSpace d)) {K : Set M}
    (hK : IsCompact K) (hKb : K⊆b.source) (hKc : K⊆c.source)
    (hg : ContDiffOn ℝ ∞ (c ∘ b.symm) (b.symm ≫ₕ c).source)
    (ωb ωc : CoordinateSpace d → CoordinateSpace d [⋀^Fin d]→L[ℝ] ℝ)
    (σb σc : ℝ)
    (hω : ∀ y∈b '' K,ωb y=(ωc (c (b.symm y))).compContinuousLinearMap
      (fderiv ℝ (c ∘ b.symm) y))
    (hσ : ∀ y∈b '' K,σb*(fderiv ℝ (c ∘ b.symm) y).det=
      σc*|(fderiv ℝ (c ∘ b.symm) y).det|) :
    (∫ y in b '' K,σb*ωb y coordinateVector)=
      ∫ y in c '' K,σc*ωc y coordinateVector := by
  let g := c ∘ b.symm
  have hyb {y : CoordinateSpace d} (hy : y∈b '' K) : y∈b.target := by
    rcases hy with ⟨x,hx,rfl⟩
    exact b.map_source (hKb hx)
  have hyK {y : CoordinateSpace d} (hy : y∈b '' K) : b.symm y∈K := by
    rcases hy with ⟨x,hx,rfl⟩
    simpa only [b.left_inv (hKb hx)] using hx
  have hys {y : CoordinateSpace d} (hy : y∈b '' K) : y∈(b.symm ≫ₕ c).source :=
    ⟨hyb hy,hKc (hyK hy)⟩
  have hgs {y : CoordinateSpace d} (hy : y∈b '' K) : ContDiffAt ℝ ∞ g y :=
    hg.contDiffAt ((b.symm ≫ₕ c).open_source.mem_nhds (hys hy))
  have hgi : InjOn g (b '' K) := by
    intro y hy z hz he
    exact b.symm.injOn (hyb hy) (hyb hz) (c.injOn (hKc (hyK hy)) (hKc (hyK hz)) he)
  have him : g '' (b '' K)=c '' K := by
    ext y
    constructor
    · rintro ⟨z,hz,rfl⟩
      exact ⟨b.symm z,hyK hz,rfl⟩
    · rintro ⟨x,hx,rfl⟩
      refine ⟨b x,⟨x,hx,rfl⟩,?_⟩
      exact congrArg c (b.left_inv (hKb hx))
  have hm : MeasurableSet (b '' K) :=
    (hK.image_of_continuousOn (b.continuousOn.mono hKb)).measurableSet
  have hi := integral_image_eq_integral_abs_det_fderiv_smul volume hm
    (f' := fderiv ℝ g)
    (fun y hy => ((hgs hy).differentiableAt (by simp)).hasFDerivAt.hasFDerivWithinAt)
    hgi (fun y => σc*ωc y coordinateVector)
  rw [him] at hi
  rw [hi]
  apply setIntegral_congr_fun hm
  intro y hy
  dsimp only
  rw [hω y hy]
  change σb*ωc (g y) (fun i => fderiv ℝ g y (coordinateVector i))=
    |(fderiv ℝ g y).det| • (σc*ωc (g y) coordinateVector)
  rw [topForm_evaluation,←mul_assoc,hσ y hy]
  simp only [smul_eq_mul]
  ring


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] {d k : ℕ}

namespace AtlasForm
variable {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

lemma exterior_supported {K : Set M} (hK : IsClosed K) (hα : α.SupportedIn K) :
    α.exterior.SupportedIn K := by
  intro i q hq hn
  have he : α.form i =ᶠ[𝓝 q] fun _ => 0 := by
    have hg : ∀ᶠ y in 𝓝 q,(a.chart i).symm y∉K :=
      ((a.chart i).continuousOn_symm.continuousAt ((a.chart i).open_target.mem_nhds hq))
        (hK.isOpen_compl.mem_nhds hn)
    filter_upwards [(a.chart i).open_target.mem_nhds hq,hg] with y hy hyn
    exact hα i y hy hyn
  change extDeriv (α.form i) q=0
  rw [he.extDeriv_eq]
  ext v
  rw [extDeriv_apply (differentiableAt_const _)]
  simp

lemma smul_supported (f : M → ℝ) (hf) {K : Set M} (hα : α.SupportedIn K) :
    (α.smul f hf).SupportedIn (K∩tsupport f) := by
  intro i q hq hn
  change f ((a.chart i).symm q) • α.form i q=0
  by_cases hk : (a.chart i).symm q∈K
  · rw [image_eq_zero_of_notMem_tsupport (fun hh => hn ⟨hk,hh⟩),zero_smul]
  · rw [hα i q hq hk,smul_zero]

end AtlasForm

end
open scoped ContDiff Topology
open Set Filter Function MeasureTheory
variable {m : ℕ}

lemma extDeriv_eq_zero_off_tsupport
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    {x : CoordinateSpace (m+1)} (hx : x∉tsupport w) : extDeriv w x=0 := by
  have he : w =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.mp hx
  rw [he.extDeriv_eq]
  simp only [extDeriv, fderiv_zero]
  exact map_zero (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ)

lemma continuous_extDeriv_coefficient
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : ContDiff ℝ 1 w) : Continuous (fun x => extDeriv w x coordinateVector) := by
  have hd : Continuous (fderiv ℝ w) := hw.continuous_fderiv (by norm_num)
  exact (ContinuousAlternatingMap.apply ℝ _ ℝ coordinateVector).continuous.comp
    ((ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ).continuous.comp hd)

theorem compact_euclidean_stokes
    {w : CoordinateSpace (m+1) → CoordinateSpace (m+1) [⋀^Fin m]→L[ℝ] ℝ}
    (hw : ContDiff ℝ 1 w) (hc : HasCompactSupport w) :
    (∫ x,extDeriv w x coordinateVector)=0 := by
  classical
  obtain ⟨R,hR⟩ := hc.isBounded.exists_norm_le
  let A : ℝ := max R 0+1
  have hAR : R<A := by dsimp [A] <;> linarith [le_max_left R 0]
  have hA : 0<A := by dsimp [A] <;> linarith [le_max_right R 0]
  let a : CoordinateSpace (m+1) := fun _ => -A
  let b : CoordinateSpace (m+1) := fun _ => A
  have hab : a≤b := fun _ => by dsimp [a,b] <;> linarith
  have hbound (x : CoordinateSpace (m+1)) (hx : x∈tsupport w) (i : Fin (m+1)) :
      |x i|<A := by
    exact (show |x i|≤‖x‖ by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i).trans_lt
      ((hR x hx).trans_lt hAR)
  have hz (x : CoordinateSpace (m+1)) (i : Fin (m+1)) (he : x i=A ∨ x i= -A) : w x=0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro hx
    have hb := hbound x hx i
    rcases he with he|he
    · rw [he,abs_of_pos hA] at hb; exact (lt_irrefl A) hb
    · rw [he,abs_neg,abs_of_pos hA] at hb; exact (lt_irrefl A) hb
  have hd : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hi : IntegrableOn (fun x => ∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1)) (Icc a b) := by
    have he : (fun x => ∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1))=
        fun x => extDeriv w x coordinateVector := funext (formFlux_divergence hd)
    rw [he]
    exact (continuous_extDeriv_coefficient hw).continuousOn.integrableOn_compact isCompact_Icc
  have hdiv := integral_divergence_of_hasFDerivAt_off_countable' a b hab (formFlux w)
    (fun i x => fderiv ℝ (formFlux w i) x) ∅ countable_empty
    (fun i => (formFlux_differentiable hd i).continuous.continuousOn)
    (fun x hx i => (formFlux_differentiable hd i x).hasFDerivAt) hi
  have hface (i : Fin (m+1)) (c : ℝ) (he : c=A ∨ c= -A) :
      (∫ y in Icc (a ∘ i.succAbove) (b ∘ i.succAbove),formFlux w i (i.insertNth c y))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro y hy
    have h0 := hz (i.insertNth c y) i (by simpa using he)
    rw [formFlux,h0]
    change (-1:ℝ)^i.val • (0:ℝ)=0
    exact smul_zero _
  have hbox : (∫ x in Icc a b,extDeriv w x coordinateVector)=0 := by
    calc
      _=(∫ x in Icc a b,∑ i,fderiv ℝ (formFlux w i) x (Pi.single i 1)) := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x => (formFlux_divergence hd x).symm)
      _=_ := hdiv
      _=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [hface i (b i) (Or.inl rfl),hface i (a i) (Or.inr rfl),sub_self]
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a b)]
  · exact hbox
  · intro x hx
    have hxs : x∉tsupport w := by
      intro hxs
      apply hx
      exact ⟨fun i => (abs_lt.mp (hbound x hxs i)).1.le,
        fun i => (abs_lt.mp (hbound x hxs i)).2.le⟩
    rw [extDeriv_eq_zero_off_tsupport hxs]
    rfl



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_ChartFormZeroExtension
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {d k : ℕ}

lemma supported_indicator_smooth {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {S K : Set (CoordinateSpace d)} (hS : IsOpen S) (hK : IsClosed K) (hKS : K⊆S)
    {f : CoordinateSpace d → Z} (hf : ContDiffOn ℝ ∞ f S)
    (hz : ∀ x∈S,x∉K →f x=0) : ContDiff ℝ ∞ (S.indicator f) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x∈S
  · apply (hf.contDiffAt (hS.mem_nhds hx)).congr_of_eventuallyEq
    filter_upwards [hS.mem_nhds hx] with y hy
    exact indicator_of_mem hy _
  · apply (contDiffAt_const (c := (0:Z))).congr_of_eventuallyEq
    filter_upwards [hK.isOpen_compl.mem_nhds (fun h => hx (hKS h))] with y hy
    by_cases hys : y∈S
    · rw [indicator_of_mem hys,hz y hys hy]
    · exact indicator_of_notMem hys _

lemma extDeriv_supported_indicator
    {S K : Set (CoordinateSpace d)} (hS : IsOpen S) (hK : IsClosed K) (hKS : K⊆S)
    {w : CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ}
    (hz : ∀ x∈S,x∉K →w x=0) : extDeriv (S.indicator w)=S.indicator (extDeriv w) := by
  classical
  funext x
  by_cases hx : x∈S
  · have he : S.indicator w =ᶠ[𝓝 x] w := by
      filter_upwards [hS.mem_nhds hx] with y hy
      exact indicator_of_mem hy _
    rw [he.extDeriv_eq,indicator_of_mem hx]
  · have he : S.indicator w =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hK.isOpen_compl.mem_nhds (fun h => hx (hKS h))] with y hy
      by_cases hys : y∈S
      · rw [indicator_of_mem hys,hz y hys hy]
      · exact indicator_of_notMem hys _
    rw [he.extDeriv_eq,indicator_of_notMem hx]
    ext v
    rw [extDeriv_apply (differentiableAt_const _)]
    simp

variable {M I : Type*} [TopologicalSpace M] [T2Space M]
  {a : SignedSmoothAtlas M I d} (α : AtlasForm a k)

omit [T2Space M] in
lemma AtlasForm.supporting_chart_compact [T2Space M] {K : Set M} (hK : IsCompact K)
    (i : I) (hi : K⊆(a.chart i).source) : IsCompact (a.chart i '' K) :=
  hK.image_of_continuousOn ((a.chart i).continuousOn.mono hi)

omit [T2Space M] in
lemma AtlasForm.supporting_chart_zero [T2Space M] {K : Set M} (hα : α.SupportedIn K)
    (i : I) {q : CoordinateSpace d} (hq : q∈(a.chart i).target) (hqn : q∉a.chart i '' K) :
    α.form i q=0 :=
  hα i q hq (fun hk => hqn ⟨_,hk,(a.chart i).right_inv hq⟩)

lemma AtlasForm.chartExtension_zero {K : Set M} (hα : α.SupportedIn K)
    (i : I) {q : CoordinateSpace d} (hqn : q∉a.chart i '' K) : α.chartExtension i q=0 := by
  classical
  by_cases hq : q∈(a.chart i).target
  · rw [chartExtension,indicator_of_mem hq]
    exact α.supporting_chart_zero hα i hq hqn
  · exact indicator_of_notMem hq _

lemma AtlasForm.chartExtension_smooth {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    ContDiff ℝ ∞ (α.chartExtension i) := by
  apply supported_indicator_smooth (a.chart i).open_target (AtlasForm.supporting_chart_compact (a := a) hK i hi).isClosed
  · rintro _ ⟨x,hx,rfl⟩
    exact (a.chart i).map_source (hi hx)
  · exact α.smooth i
  · exact fun q hq hn => α.supporting_chart_zero hα i hq hn

lemma AtlasForm.chartExtension_support {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    HasCompactSupport (α.chartExtension i) :=
  HasCompactSupport.intro (AtlasForm.supporting_chart_compact (a := a) hK i hi) (fun _ h => α.chartExtension_zero hα i h)

lemma AtlasForm.exterior_chartExtension {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.exterior.chartExtension i=extDeriv (α.chartExtension i) := by
  symm
  apply extDeriv_supported_indicator (a.chart i).open_target (AtlasForm.supporting_chart_compact (a := a) hK i hi).isClosed
  · rintro _ ⟨x,hx,rfl⟩
    exact (a.chart i).map_source (hi hx)
  · exact fun q hq hn => α.supporting_chart_zero hα i hq hn

lemma AtlasForm.chart_coefficient_integrable {a : SignedSmoothAtlas M I d}
    (α : AtlasForm a d) {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    Integrable (fun q => a.sign i*α.chartExtension i q coordinateVector) := by
  have hc : Continuous (fun q => a.sign i*α.chartExtension i q coordinateVector) :=
    continuous_const.mul ((ContinuousAlternatingMap.apply ℝ _ ℝ coordinateVector).continuous.comp
      (α.chartExtension_smooth hK hα i hi).continuous)
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (AtlasForm.supporting_chart_compact (a := a) hK i hi)
  intro q hq
  rw [α.chartExtension_zero hα i hq]
  exact mul_zero _

lemma AtlasForm.chartMass_exterior_zero {a : SignedSmoothAtlas M I (k+1)}
    (α : AtlasForm a k) {K : Set M} (hK : IsCompact K)
    (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.exterior.chartMass i=0 := by
  unfold chartMass
  rw [α.exterior_chartExtension hK hα i hi,integral_const_mul,
    compact_euclidean_stokes ((α.chartExtension_smooth hK hα i hi).of_le (by
      exact WithTop.coe_le_coe.mpr le_top)) (α.chartExtension_support hK hα i hi),mul_zero]


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] [T2Space M] {d k : ℕ}
  {a : SignedSmoothAtlas M I d}

lemma AtlasForm.chartMass_eq_compact_integral (α : AtlasForm a d)
    {K : Set M} (hK : IsCompact K) (hα : α.SupportedIn K) (i : I) (hi : K⊆(a.chart i).source) :
    α.chartMass i=∫q in a.chart i '' K,a.sign i*α.form i q coordinateVector := by
  unfold chartMass
  rw [←setIntegral_eq_integral_of_forall_compl_eq_zero (s := a.chart i '' K)]
  · apply setIntegral_congr_fun
    · exact (hK.image_of_continuousOn ((a.chart i).continuousOn.mono hi)).measurableSet
    · intro q hq
      obtain ⟨x,hx,rfl⟩ := hq
      dsimp only
      rw [chartExtension,indicator_of_mem ((a.chart i).map_source (hi hx))]
  · intro q hq
    rw [α.chartExtension_zero hα i hq]
    exact mul_zero _

lemma AtlasForm.chartMass_change (α : AtlasForm a d)
    {K : Set M} (hK : IsCompact K) (hα : α.SupportedIn K)
    (i j : I) (hi : K⊆(a.chart i).source) (hj : K⊆(a.chart j).source) :
    α.chartMass i=α.chartMass j := by
  rw [α.chartMass_eq_compact_integral hK hα i hi,α.chartMass_eq_compact_integral hK hα j hj]
  apply topForm_chartMass_change (a.chart j) (a.chart i) hK hi hj (a.transition_smooth i j)
  · rintro q ⟨x,hx,rfl⟩
    apply α.compatible i j
    exact ⟨(a.chart i).map_source (hi hx),by
      change (a.chart i).symm ((a.chart i) x)∈(a.chart j).source
      rw [(a.chart i).left_inv (hi hx)]; exact hj hx⟩
  · rintro q ⟨x,hx,rfl⟩
    apply a.orientation i j
    exact ⟨(a.chart i).map_source (hi hx),by
      change (a.chart i).symm ((a.chart i) x)∈(a.chart j).source
      rw [(a.chart i).left_inv (hi hx)]; exact hj hx⟩

omit [T2Space M] in
lemma AtlasForm.chartMass_sum [T2Space M] {J : Type*} [Fintype J]
    (Ω : AtlasForm a d) (β : J → AtlasForm a d) (i : I)
    (he : ∀ q∈(a.chart i).target,Ω.form i q=∑j,(β j).form i q)
    (hi : ∀ j,Integrable (fun q => a.sign i*(β j).chartExtension i q coordinateVector)) :
    Ω.chartMass i=∑j,(β j).chartMass i := by
  classical
  change (∫q,a.sign i*Ω.chartExtension i q coordinateVector)=∑j,∫q,a.sign i*(β j).chartExtension i q coordinateVector
  rw [←integral_finsetSum _ (fun j _ => hi j)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  by_cases hq : q∈(a.chart i).target
  · simp only [AtlasForm.chartExtension,indicator_of_mem hq,he q hq]
    rw [ContinuousAlternatingMap.sum_apply,Finset.mul_sum]
  · simp only [AtlasForm.chartExtension,indicator_of_notMem hq]
    change a.sign i*0=∑j,a.sign i*0
    simp

variable [Fintype I]

namespace AtlasPartition
variable {K : Set M} (p : AtlasPartition a K)

omit [T2Space M] in
lemma smul_sum [T2Space M] (Ω : AtlasForm a k) (hΩ : Ω.SupportedIn K) (i : I) {q : CoordinateSpace d}
    (hq : q∈(a.chart i).target) :
    ∑j,(Ω.smul (p.weight j) (p.smooth j)).form i q=Ω.form i q := by
  change (∑j,p.weight j ((a.chart i).symm q) • Ω.form i q)=Ω.form i q
  rw [←Finset.sum_smul]
  by_cases hx : (a.chart i).symm q∈K
  · rw [p.sum_one _ hx,one_smul]
  · rw [hΩ i q hq hx,smul_zero]

lemma mass_eq_chartMass {L : Set M} (hL : IsCompact L) (hLK : L⊆K)
    (Ω : AtlasForm a d) (hΩ : Ω.SupportedIn L)
    (j : I) (hj : L⊆(a.chart j).source) : p.mass Ω=Ω.chartMass j := by
  classical
  let D : I → AtlasForm a d := fun i => Ω.smul (p.weight i) (p.smooth i)
  let C : I → Set M := fun i => L∩tsupport (p.weight i)
  have hC (i : I) : IsCompact (C i) := hL.inter_right (isClosed_tsupport _)
  have hD (i : I) : (D i).SupportedIn (C i) := Ω.smul_supported _ _ hΩ
  have hci (i : I) : C i⊆(a.chart i).source := fun _ h => p.subordinate i h.2
  have hcj (i : I) : C i⊆(a.chart j).source := fun _ h => hj h.1
  have hm (i : I) : (D i).chartMass i=(D i).chartMass j :=
    (D i).chartMass_change (hC i) (hD i) i j (hci i) (hcj i)
  change (∑i,(D i).chartMass i)=_
  simp_rw [hm]
  symm
  apply Ω.chartMass_sum D j
  · intro q hq
    have hΩK : Ω.SupportedIn K := fun i q hq hn => hΩ i q hq (fun hx => hn (hLK hx))
    exact (p.smul_sum Ω hΩK j hq).symm
  · exact fun i => (D i).chart_coefficient_integrable (hC i) (hD i) j (hcj i)

end AtlasPartition

end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory
variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I] {d k : ℕ}
  {a : SignedSmoothAtlas M I d} {K : Set M}

lemma AtlasPartition.mass_sum (p : AtlasPartition a K) (hK : IsCompact K)
    {J : Type*} [Fintype J] (Ω : AtlasForm a d) (β : J → AtlasForm a d)
    (hβ : ∀ j,(β j).SupportedIn K)
    (he : ∀ i q,q∈(a.chart i).target → Ω.form i q=∑j,(β j).form i q) :
    p.mass Ω=∑j,p.mass (β j) := by
  classical
  unfold mass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply AtlasForm.chartMass_sum _ (fun j => (β j).smul (p.weight i) (p.smooth i)) i
  · intro q hq
    change p.weight i ((a.chart i).symm q) • Ω.form i q=
      ∑j,p.weight i ((a.chart i).symm q) • (β j).form i q
    rw [he i q hq,Finset.smul_sum]
  · intro j
    exact ((β j).smul (p.weight i) (p.smooth i)).chart_coefficient_integrable
      (hK.inter_right (isClosed_tsupport _)) ((β j).smul_supported _ _ (hβ j)) i
      (fun _ h => p.subordinate i h.2)

lemma extDeriv_fintype_sum {J : Type*} [Fintype J]
    (β : J → CoordinateSpace d → CoordinateSpace d [⋀^Fin k]→L[ℝ] ℝ)
    (q : CoordinateSpace d) (hβ : ∀ j,DifferentiableAt ℝ (β j) q) :
    extDeriv (fun y => ∑j,β j y) q=∑j,extDeriv (β j) q := by
  classical
  simp only [extDeriv,fderiv_fun_sum (fun j _ => hβ j)]
  exact map_sum (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ _ ℝ) _ _

theorem AtlasPartition.compact_stokes {a : SignedSmoothAtlas M I (k+1)}
    (p : AtlasPartition a K) (hK : IsCompact K)
    (α : AtlasForm a k) (hα : α.SupportedIn K) : p.mass α.exterior=0 := by
  classical
  let β : I → AtlasForm a k := fun i => α.smul (p.weight i) (p.smooth i)
  let L : I → Set M := fun i => K∩tsupport (p.weight i)
  have hL (i : I) : IsCompact (L i) := hK.inter_right (isClosed_tsupport _)
  have hβ (i : I) : (β i).SupportedIn (L i) := α.smul_supported _ _ hα
  have hLi (i : I) : L i⊆(a.chart i).source := fun _ h => p.subordinate i h.2
  have hdβ (i : I) : (β i).exterior.SupportedIn K := by
    have hs := (β i).exterior_supported (hL i).isClosed (hβ i)
    exact fun j q hq hn => hs j q hq (fun h => hn h.1)
  have hsum (i : I) (q : CoordinateSpace (k+1)) (hq : q∈(a.chart i).target) :
      α.exterior.form i q=∑j,(β j).exterior.form i q := by
    have he : α.form i =ᶠ[𝓝 q] fun y => ∑j,(β j).form i y := by
      filter_upwards [(a.chart i).open_target.mem_nhds hq] with y hy
      exact (p.smul_sum α hα i hy).symm
    change extDeriv (α.form i) q=∑j,extDeriv ((β j).form i) q
    rw [he.extDeriv_eq]
    apply extDeriv_fintype_sum
    intro j
    exact (((β j).smooth i).contDiffAt ((a.chart i).open_target.mem_nhds hq)).differentiableAt (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  rw [p.mass_sum hK α.exterior (fun j => (β j).exterior) hdβ hsum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [p.mass_eq_chartMass (hL i) inter_subset_left (β i).exterior
    ((β i).exterior_supported (hL i).isClosed (hβ i)) i (hLi i)]
  exact (β i).chartMass_exterior_zero (hL i) (hβ i) i (hLi i)


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter
variable {M I P : Type*} [TopologicalSpace M]
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  {d k : ℕ} {a : SignedSmoothAtlas M I d}

namespace AtlasSmoothMap
variable (f : AtlasSmoothMap a P)

lemma pullback_exterior (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w)
    (i : I) {q : CoordinateSpace d} (hq : q∈(a.chart i).target) :
    (f.pullback w hw).exterior.form i q=
      (extDeriv w (f.map ((a.chart i).symm q))).compContinuousLinearMap
        (fderiv ℝ (f.map ∘ (a.chart i).symm) q) := by
  exact extDeriv_pullback (hw.differentiable (by simp) _)
    ((f.smooth i).contDiffAt ((a.chart i).open_target.mem_nhds hq)) (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)

lemma pullback_supported (w : P → P [⋀^Fin k]→L[ℝ] ℝ) (hw : ContDiff ℝ ∞ w)
    {K : Set M} (hK : ∀ x : M,x∉K →w (f.map x)=0) : (f.pullback w hw).SupportedIn K := by
  intro i q hq hn
  change (w (f.map ((a.chart i).symm q))).compContinuousLinearMap _=0
  rw [hK _ hn]
  ext v
  rfl

end AtlasSmoothMap

end
open scoped ContDiff Topology
open Set Filter MeasureTheory



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_BoxContinuation
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Function Filter
variable {m : ℕ}

lemma tail_coordinate_zero : tailCLM m (coordinateVector 0)=0 := by
  ext i
  simp [tailCLM,coordinateVector]
lemma tail_coordinate_succ (i : Fin m) : tailCLM m (coordinateVector i.succ)=coordinateVector i := by
  ext j
  simp [tailCLM,coordinateVector,Pi.single_apply]

lemma collarVolumeForm_flux_zero (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ)
    (v : CoordinateSpace (m+1)) :
    formFlux (collarVolumeForm θ ρ) 0 v=θ (v 0)*ρ (Fin.tail v) := by
  change (-1:ℝ)^0 • ((θ (v 0)*ρ (Fin.tail v)) •
    (coordinateVolume m) (fun i => tailCLM m (coordinateVector ((0:Fin (m+1)).succAbove i))))=_
  simp only [Fin.zero_succAbove,tail_coordinate_succ,coordinateVolume_basis,pow_zero,smul_eq_mul,mul_one,one_mul]

lemma collarVolumeForm_flux_other (θ : ℝ → ℝ) (ρ : CoordinateSpace m → ℝ)
    (i : Fin (m+1)) (hi : i≠0) (v : CoordinateSpace (m+1)) :
    formFlux (collarVolumeForm θ ρ) i v=0 := by
  obtain ⟨j,hj⟩ := Fin.exists_succAbove_eq hi.symm
  have hz : (coordinateVolume m) (fun k => tailCLM m (coordinateVector (i.succAbove k)))=0 := by
    apply (coordinateVolume m).toAlternatingMap.map_coord_zero j
    rw [hj,tail_coordinate_zero]
  change (-1:ℝ)^i.val • ((θ (v 0)*ρ (Fin.tail v)) •
    (coordinateVolume m) (fun k => tailCLM m (coordinateVector (i.succAbove k))))=0
  rw [hz,smul_zero,smul_zero]

lemma collarVolumeForm_exterior_basis {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) (v : CoordinateSpace (m+1)) :
    extDeriv (collarVolumeForm θ ρ) v coordinateVector=deriv θ (v 0)*ρ (Fin.tail v) := by
  rw [←formFlux_divergence ((collarVolumeForm_smooth hθ hρ).differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top))]
  rw [Finset.sum_eq_single (0:Fin (m+1))]
  · have he : formFlux (collarVolumeForm θ ρ) 0=(fun y => θ (y 0)*ρ (Fin.tail y)) :=
      funext (collarVolumeForm_flux_zero θ ρ)
    rw [he]
    have ht := ((hθ.differentiable (by simp) (v 0)).hasDerivAt.hasFDerivAt).comp v
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m+1) => ℝ) 0).hasFDerivAt (x := v))
    have hr := ((hρ.differentiable (by simp) (Fin.tail v)).hasFDerivAt).comp v (tailCLM m).hasFDerivAt
    have hh := (ht.mul hr).fderiv
    simp only [Function.comp_def,Pi.mul_def,ContinuousLinearMap.proj_apply] at hh
    rw [hh]
    have hz : tailCLM m (Pi.single 0 1)=0 := tail_coordinate_zero
    simp [coordinateVector,hz,mul_comm]
  · intro i hi hi0
    have he : formFlux (collarVolumeForm θ ρ) i=(fun _ => 0) :=
      funext (collarVolumeForm_flux_other θ ρ i hi0)
    rw [he]
    simp
  · simp

lemma collarVolumeForm_zero_of_time {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    {v : CoordinateSpace (m+1)} (h : θ (v 0)=0) : collarVolumeForm θ ρ v=0 := by
  simp [collarVolumeForm,h]
lemma collarVolumeForm_zero_of_space {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    {v : CoordinateSpace (m+1)} (h : ρ (Fin.tail v)=0) : collarVolumeForm θ ρ v=0 := by
  simp [collarVolumeForm,h]


end
section
open scoped ContDiff Topology
open Set Function Filter

lemma collarRise_initial {a b t : ℝ} (hab : a<b) (ht : t≤a) : collarRise a b t=0 :=
  Real.smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) (sub_pos.mpr hab).le)
lemma collarRise_final {a b t : ℝ} (hab : a<b) (ht : b≤t) : collarRise a b t=1 :=
  Real.smoothTransition.one_of_one_le ((le_div_iff₀ (sub_pos.mpr hab)).mpr (by linarith))
lemma collarRise_monotone {a b : ℝ} (hab : a<b) : Monotone (collarRise a b) := by
  intro x y hxy
  exact Real.smoothTransition.monotone (div_le_div_of_nonneg_right (sub_le_sub_right hxy _) (sub_pos.mpr hab).le)
lemma collarRise_deriv_nonneg {a b : ℝ} (hab : a<b) (t : ℝ) : 0≤deriv (collarRise a b) t :=
  (collarRise_monotone hab).deriv_nonneg
lemma collarRise_deriv_zero {a b t : ℝ} (hab : a<b) (ht : t∉Icc a b) : deriv (collarRise a b) t=0 := by
  simp only [mem_Icc,not_and_or,not_le] at ht
  rcases ht with ht|ht
  · have he : collarRise a b =ᶠ[𝓝 t] fun _ => 0 := by
      filter_upwards [gt_mem_nhds ht] with s hs
      exact collarRise_initial hab hs.le
    rw [he.deriv_eq]
    simp
  · have he : collarRise a b =ᶠ[𝓝 t] fun _ => 1 := by
      filter_upwards [lt_mem_nhds ht] with s hs
      exact collarRise_final hab hs.le
    rw [he.deriv_eq]
    simp
lemma collarRise_deriv_positive {a b : ℝ} (hab : a<b) : ∃ t∈Ioo a b,0<deriv (collarRise a b) t := by
  obtain ⟨t,ht,he⟩ := exists_deriv_eq_slope (collarRise a b) hab
    (collarRise_smooth a b).continuous.continuousOn ((collarRise_smooth a b).differentiable (by simp)).differentiableOn
  refine ⟨t,ht,?_⟩
  rw [he,collarRise_initial hab le_rfl,collarRise_final hab le_rfl,sub_zero]
  exact div_pos zero_lt_one (sub_pos.mpr hab)

lemma collarCutoff_deriv (a b c d t : ℝ) :
    deriv (collarCutoff a b c d) t=deriv (collarRise a b) t-deriv (collarRise c d) t := by
  exact deriv_sub ((collarRise_smooth a b).differentiable (by simp) t)
    ((collarRise_smooth c d).differentiable (by simp) t)
lemma collarCutoff_zero {a b c d t : ℝ} (hab : a<b) (hbc : b < c) (hcd : c<d)
    (ht : t∉Icc a d) : collarCutoff a b c d t=0 := by
  simp only [mem_Icc,not_and_or,not_le] at ht
  rcases ht with ht|ht
  · rw [collarCutoff,collarRise_initial hab ht.le,collarRise_initial hcd (ht.le.trans (hab.trans hbc).le),sub_self]
  · rw [collarCutoff,collarRise_final hab ((hbc.trans hcd).le.trans ht.le),collarRise_final hcd ht.le,sub_self]
lemma collarCutoff_deriv_initial {a b c d t : ℝ} (hcd : c<d) (ht : t < c) :
    deriv (collarCutoff a b c d) t=deriv (collarRise a b) t := by
  rw [collarCutoff_deriv,collarRise_deriv_zero hcd (fun h => (not_le.mpr ht) h.1),sub_zero]
lemma collarCutoff_deriv_support {a b c d : ℝ} (hab : a<b) (hcd : c<d) :
    tsupport (deriv (collarCutoff a b c d))⊆Icc a b ∪ Icc c d := by
  apply closure_minimal _ (isClosed_Icc.union isClosed_Icc)
  intro t ht
  by_contra hn
  have ha : t∉Icc a b := fun h => hn (Or.inl h)
  have hb : t∉Icc c d := fun h => hn (Or.inr h)
  apply ht
  rw [collarCutoff_deriv,collarRise_deriv_zero hab ha,collarRise_deriv_zero hcd hb,sub_self]


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {m : ℕ}

lemma topForm_eq_zero_of_basis (w : CoordinateSpace m [⋀^Fin m]→L[ℝ] ℝ)
    (hw : w coordinateVector=0) : w=0 := by
  have he := w.toAlternatingMap.eq_smul_basis_det (Pi.basisFun ℝ (Fin m))
  have hb : (coordinateVector : Fin m → CoordinateSpace m)=Pi.basisFun ℝ (Fin m) := by
    funext i
    exact (Pi.basisFun_apply ℝ (Fin m) i).symm
  rw [←hb] at he
  change w.toAlternatingMap coordinateVector=0 at hw
  rw [hw,zero_smul] at he
  ext v
  exact congrArg (fun A : AlternatingMap ℝ (CoordinateSpace m) ℝ (Fin m) => A v) he

lemma collarVolumeForm_exterior_zero {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
    (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ) {v : CoordinateSpace (m+1)}
    (hz : deriv θ (v 0)=0 ∨ ρ (Fin.tail v)=0) : extDeriv (collarVolumeForm θ ρ) v=0 := by
  apply topForm_eq_zero_of_basis
  rw [collarVolumeForm_exterior_basis hθ hρ]
  exact mul_eq_zero.mpr hz

variable {M I : Type*} [TopologicalSpace M] {a : SignedSmoothAtlas M I (m+1)}
  (f : AtlasSmoothMap a (CoordinateSpace (m+1)))
  {θ : ℝ → ℝ} {ρ : CoordinateSpace m → ℝ}
  (hθ : ContDiff ℝ ∞ θ) (hρ : ContDiff ℝ ∞ ρ)

lemma collar_pullback_density (i : I) {q : CoordinateSpace (m+1)} (hq : q∈(a.chart i).target) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.form i q coordinateVector=
      (fderiv ℝ (f.map ∘ (a.chart i).symm) q).det *
        (deriv θ (f.map ((a.chart i).symm q) 0)*ρ (Fin.tail (f.map ((a.chart i).symm q)))) := by
  rw [f.pullback_exterior _ _ i hq]
  change (extDeriv (collarVolumeForm θ ρ) (f.map ((a.chart i).symm q)))
    (fun j => fderiv ℝ (f.map ∘ (a.chart i).symm) q (coordinateVector j))=_
  rw [topForm_evaluation,collarVolumeForm_exterior_basis hθ hρ]

lemma collar_pullback_exterior_supported {K : Set M}
    (hK : ∀ x : M,x∉K →deriv θ (f.map x 0)=0 ∨ ρ (Fin.tail (f.map x))=0) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.SupportedIn K := by
  intro i q hq hn
  rw [f.pullback_exterior _ _ i hq,collarVolumeForm_exterior_zero hθ hρ (hK _ hn)]
  ext v
  rfl

lemma collar_pullback_identity_density (i : I)
    (he : EqOn (f.map ∘ (a.chart i).symm) id (a.chart i).target)
    {q : CoordinateSpace (m+1)} (hq : q∈(a.chart i).target) :
    (f.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.form i q coordinateVector=
      deriv θ (q 0)*ρ (Fin.tail q) := by
  have heg : (f.map ∘ (a.chart i).symm)=ᶠ[𝓝 q] id :=
    Filter.eventually_of_mem ((a.chart i).open_target.mem_nhds hq) he
  rw [collar_pullback_density f hθ hρ i hq,heg.fderiv_eq]
  have hp : f.map ((a.chart i).symm q)=q := he hq
  rw [hp,fderiv_id]
  simp [ContinuousLinearMap.det,LinearMap.det_id]


end
section
open scoped ContDiff Topology Manifold
open Set Function Filter MeasureTheory Manifold
variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I] {d : ℕ}
  (a : SignedSmoothAtlas M I d)

omit [T2Space M] [Fintype I] in
lemma SignedSmoothAtlas.isManifold [T2Space M] [Fintype I] :
    @IsManifold ℝ _ (CoordinateSpace d) _ _ (CoordinateSpace d) _
      (𝓘(ℝ,CoordinateSpace d)) ∞ M _ a.chartedSpace := by
  let := a.chartedSpace
  apply isManifold_of_contDiffOn
  rintro e e' ⟨i,rfl⟩ ⟨j,rfl⟩
  simpa only [modelWithCornersSelf_coe,modelWithCornersSelf_coe_symm,Function.id_comp,
    Function.comp_id,Set.preimage_id,Set.range_id,Set.inter_univ,OpenPartialHomeomorph.coe_trans] using a.transition_smooth i j

include a in
omit [T2Space M] in
lemma SignedSmoothAtlas.secondCountable [T2Space M] : SecondCountableTopology M := by
  let (i : I) : SecondCountableTopology (a.chart i).source := (a.chart i).secondCountableTopology_source
  apply TopologicalSpace.secondCountableTopology_of_countable_cover (fun i => (a.chart i).open_source)
  exact eq_univ_iff_forall.mpr (fun x => mem_iUnion.mpr (a.cover x))

theorem SignedSmoothAtlas.partition_exists {K : Set M} (hK : IsCompact K) :
    Nonempty (AtlasPartition a K) := by
  let := a.chartedSpace
  let := a.isManifold
  let := a.secondCountable
  let : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace (CoordinateSpace d) M
  obtain ⟨p,hp⟩ := SmoothPartitionOfUnity.exists_isSubordinate (𝓘(ℝ,CoordinateSpace d)) hK.isClosed
    (fun i => (a.chart i).source) (fun i => (a.chart i).open_source)
    (fun x hx => mem_iUnion.mpr (a.cover x))
  refine ⟨{weight := fun i => p i,smooth := ?_,sum_one := ?_,subordinate := hp}⟩
  · intro i j
    have hj : a.chart j∈IsManifold.maximalAtlas (𝓘(ℝ,CoordinateSpace d)) ∞ M :=
      IsManifold.subset_maximalAtlas (mem_range_self j)
    exact ((p i).contMDiff.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas hj)).contDiffOn
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using p.sum_eq_one hx


end
open scoped ContDiff Topology Manifold
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Degree_EuclideanAtlasTransport
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity.Degree

section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

lemma timeSpaceCoordinates_apply (e : E ≃L[ℝ] CoordinateSpace m) (v : ℝ × E) :
    timeSpaceCoordinates e v=Fin.cons v.1 (e v.2) := rfl


end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {m : ℕ}

lemma initialCollarDensity_continuous (a b : ℝ) {ρ : CoordinateSpace m → ℝ}
    (hρ : Continuous ρ) : Continuous (initialCollarDensity a b ρ) :=
  (((collarRise_smooth a b).continuous_deriv (by simp)).comp (continuous_apply 0)).mul
    (hρ.comp tail_smooth.continuous)

lemma initialCollarDensity_support {a b : ℝ} (hab : a<b) (ρ : CoordinateSpace m → ℝ) :
    tsupport (initialCollarDensity a b ρ)⊆{v | v 0∈Icc a b ∧ Fin.tail v∈tsupport ρ} := by
  apply closure_minimal _ ((isClosed_Icc.preimage (continuous_apply 0)).inter
    ((isClosed_tsupport ρ).preimage tail_smooth.continuous))
  intro v hv
  constructor
  · by_contra hn
    exact hv (by simp [initialCollarDensity,collarRise_deriv_zero hab hn])
  · by_contra hn
    exact hv (by simp [initialCollarDensity,image_eq_zero_of_notMem_tsupport hn])

lemma initialCollarDensity_compact {a b : ℝ} (hab : a<b) {ρ : CoordinateSpace m → ℝ}
    (hρ : HasCompactSupport ρ) : HasCompactSupport (initialCollarDensity a b ρ) := by
  let e := timeSpaceCoordinates (ContinuousLinearEquiv.refl ℝ (CoordinateSpace m))
  have hK : IsCompact (e '' (Icc a b ×ˢ tsupport ρ)) := (isCompact_Icc.prod hρ).image e.continuous
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  intro v hv
  have hh := initialCollarDensity_support hab ρ hv
  refine ⟨(v 0,Fin.tail v),hh,?_⟩
  exact Fin.cons_self_tail v

lemma initialCollarDensity_integral_pos {a b : ℝ} (hab : a<b) {ρ : CoordinateSpace m → ℝ}
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ) (hρn : ∀ x,0≤ρ x) (hρ0 : 0<ρ 0) :
    0<∫v,initialCollarDensity a b ρ v := by
  obtain ⟨t,ht,hpos⟩ := collarRise_deriv_positive hab
  apply (initialCollarDensity_continuous a b hρ).integral_pos_of_hasCompactSupport_nonneg_nonzero
    (x := Fin.cons t 0) (initialCollarDensity_compact hab hρc)
  · intro v
    exact mul_nonneg (collarRise_deriv_nonneg hab _) (hρn _)
  · exact (show 0 < initialCollarDensity a b ρ (Fin.cons t 0) by
      simpa only [initialCollarDensity,Fin.cons_zero,Fin.tail_cons] using mul_pos hpos hρ0).ne'

variable {M I : Type*} [TopologicalSpace M] [T2Space M] [Fintype I]
  {atlas : SignedSmoothAtlas M I (m+1)} {K T : Set M}
  (p : AtlasPartition atlas K) (f : AtlasSmoothMap atlas (CoordinateSpace (m+1)))
  {a b c d : ℝ} {ρ : CoordinateSpace m → ℝ}

include p in

theorem collar_stokes_contradiction (hab : a<b) (hcd : c<d)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) (hρn : ∀ x,0≤ρ x) (hρ0 : 0<ρ 0)
    (hK : IsCompact K) (hT : IsCompact T) (hTK : T⊆K)
    (hα : (f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
      (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)).SupportedIn K)
    (hdα : (f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
      (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)).exterior.SupportedIn T)
    (i : I) (hTi : T⊆(atlas.chart i).source)
    (hidentity : EqOn (f.map ∘ (atlas.chart i).symm) id (atlas.chart i).target)
    (hinitial : ∀ q∈(atlas.chart i).target,q 0 < c)
    (hcover : tsupport (initialCollarDensity a b ρ)⊆(atlas.chart i).target) : False := by
  let α := f.pullback (collarVolumeForm (collarCutoff a b c d) ρ)
    (collarVolumeForm_smooth (collarCutoff_smooth a b c d) hρ)
  have hz := p.compact_stokes hK α hα
  rw [p.mass_eq_chartMass hT hTK α.exterior hdα i hTi] at hz
  have he : α.exterior.chartMass i=atlas.sign i*(∫q,initialCollarDensity a b ρ q) := by
    rw [AtlasForm.chartMass,←integral_const_mul]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro q
    dsimp only
    by_cases hq : q∈(atlas.chart i).target
    · rw [AtlasForm.chartExtension,indicator_of_mem hq]
      change atlas.sign i*(f.pullback _ _).exterior.form i q coordinateVector=_
      rw [collar_pullback_identity_density f (collarCutoff_smooth a b c d) hρ i hidentity hq,
        collarCutoff_deriv_initial hcd (hinitial q hq)]
      rfl
    · rw [AtlasForm.chartExtension,indicator_of_notMem hq]
      have hn : q∉tsupport (initialCollarDensity a b ρ) := fun hh => hq (hcover hh)
      rw [image_eq_zero_of_notMem_tsupport hn]
      rfl
  rw [he] at hz
  have hs : atlas.sign i≠0 := by
    intro h
    have hh := atlas.sign_sq i
    rw [h,zero_mul] at hh
    exact zero_ne_one hh
  exact (mul_ne_zero hs (initialCollarDensity_integral_pos hab hρ.continuous hρc hρn hρ0).ne') hz


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {M I : Type*} [TopologicalSpace M] {d : ℕ}
lemma SignedSmoothAtlas.finite_inside (a : SignedSmoothAtlas M I d)
    {K N : Set M} (hK : IsCompact K) (hN : IsOpen N) (hKN : K⊆N)
    (p : M) (hp : p∈K) (i : I) (_hpi : p∈(a.chart i).source) :
    ∃ J : Finset I,i∈J ∧ ∃ W : TopologicalSpace.Opens M,
      K⊆W ∧ (W:Set M)⊆N ∧ ∃ _hW : Nonempty W,
        ∀ x : W,∃ j∈(J:Set I),x.val∈(a.chart j).source := by
  classical
  obtain ⟨J,hJ⟩ := hK.elim_finite_subcover (fun j => (a.chart j).source)
    (fun j => (a.chart j).open_source) (fun x hx => mem_iUnion.mpr (a.cover x))
  let A := insert i J
  let W : TopologicalSpace.Opens M := ⟨N∩⋃j∈A,(a.chart j).source,
    hN.inter (isOpen_biUnion (fun j hj => (a.chart j).open_source))⟩
  have hKW : K⊆W := by
    intro x hx
    refine ⟨hKN hx,?_⟩
    obtain ⟨j,hj,hxj⟩ := mem_iUnion₂.mp (hJ hx)
    exact mem_iUnion₂.mpr ⟨j,Finset.mem_insert_of_mem hj,hxj⟩
  refine ⟨A,Finset.mem_insert_self _ _,W,hKW,fun _ h => h.1,⟨⟨p,hKW hp⟩⟩,?_⟩
  intro x
  obtain ⟨j,hj,hx⟩ := mem_iUnion₂.mp x.property.2
  exact ⟨j,hj,hx⟩

end
section
open scoped ContDiff Topology
open Set Function Filter
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}
lemma small_inverse_bump (e : E ≃L[ℝ] CoordinateSpace m) {δ : ℝ} (hδ : 0<δ) :
    ∃ b : ContDiffBump (0:CoordinateSpace m),∀ z∈tsupport (b : CoordinateSpace m → ℝ),‖e.symm z‖≤δ := by
  have ho : IsOpen {z : CoordinateSpace m | ‖e.symm z‖<δ} :=
    isOpen_lt e.symm.continuous.norm continuous_const
  have h0 : (0:CoordinateSpace m)∈{z | ‖e.symm z‖<δ} := by simpa only [mem_ofPred_eq,map_zero,norm_zero] using hδ
  obtain ⟨r,hr,hrd⟩ := Metric.isOpen_iff.mp ho 0 h0
  let b : ContDiffBump (0:CoordinateSpace m) := ⟨r/4,r/2,by positivity,by linarith⟩
  refine ⟨b,?_⟩
  intro z hz
  rw [b.tsupport_eq,Metric.mem_closedBall,dist_zero_right] at hz
  exact (hrd (show z∈Metric.ball 0 r from by
    rw [Metric.mem_ball,dist_zero_right]
    exact hz.trans_lt (half_lt_self hr))).le

end
section
open scoped ContDiff Topology
open Set Function Filter MeasureTheory
variable {M I E : Type*} [TopologicalSpace M] [T2Space M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem isolated_collar_impossible
    (a : SignedModelAtlas M I (ℝ × E)) (f : ModelAtlasSmoothMap a (ℝ × E))
    (hf : Continuous f.map) (i : I) (p : M) (hpi : p∈(a.chart i).source)
    (hp : f.map p=((1:ℝ)/8,0))
    (hidentity : EqOn (f.map ∘ (a.chart i).symm) id (a.chart i).target)
    (hinit : ∀ q∈(a.chart i).target,q.1<1/4)
    (hinj : ∀ x y : M,(f.map x).1<1/4 →(f.map y).1<1/4 →f.map x=f.map y →x=y)
    (N : Set M) (hN : IsOpen N) (hpN : p∈N)
    (δ₀ : ℝ) (hδ₀ : 0<δ₀)
    (hcompact : ∀ δ : ℝ,0<δ →δ≤δ₀ →IsCompact {x : M | x∈N ∧
      (f.map x).1∈Icc (0:ℝ) 1 ∧ ‖(f.map x).2‖≤δ})
    (hfinal : ∀ x∈N,3/4≤(f.map x).1 →‖(f.map x).2‖≤δ₀ →False) : False := by
  classical
  let m := Module.finrank ℝ E
  let e : E ≃L[ℝ] CoordinateSpace m := (Module.finBasis ℝ E).equivFunL
  let c := a.chart i
  have hpchart : c p=((1:ℝ)/8,0) := by
    have hh : f.map (c.symm (c p))=c p := hidentity (c.map_source hpi)
    rw [c.left_inv hpi,hp] at hh
    exact hh.symm
  let O := c.target∩c.symm ⁻¹' N
  have hO : IsOpen O := c.continuousOn_symm.isOpen_inter_preimage c.open_target hN
  have hpO : ((1:ℝ)/8,(0:E))∈O := by
    rw [←hpchart]
    exact ⟨c.map_source hpi,by simpa only [mem_preimage,c.left_inv hpi] using hpN⟩
  obtain ⟨r,hr,hrO⟩ := Metric.isOpen_iff.mp hO _ hpO
  let s := min r ((1:ℝ)/16)/4
  have hs : 0 < s := div_pos (lt_min hr (by norm_num)) (by norm_num)
  have hsm : s < min r ((1:ℝ)/16) := by dsimp [s] <;> linarith [lt_min hr (by norm_num : (0:ℝ)<1/16)]
  have hsr : s < r := hsm.trans_le (min_le_left _ _)
  have hs16 : s<1/16 := hsm.trans_le (min_le_right _ _)
  let δ := min δ₀ s/2
  have hδ : 0<δ := half_pos (lt_min hδ₀ hs)
  have hδ₀' : δ≤δ₀ := (half_le_self (lt_min hδ₀ hs).le).trans (min_le_left _ _)
  have hδs : δ < s := (half_lt_self (lt_min hδ₀ hs)).trans_le (min_le_right _ _)
  let A := (1:ℝ)/8-s/2
  let B := (1:ℝ)/8+s/2
  have hAB : A<B := by dsimp [A,B] <;> linarith
  have hA : 0<A := by dsimp [A] <;> linarith
  have hB : B<1/4 := by dsimp [B] <;> linarith
  have hbox (t : ℝ) (ht : t∈Icc A B) (y : E) (hy : ‖y‖≤δ) : (t,y)∈O := by
    apply hrO
    rw [Metric.mem_ball,Prod.dist_eq,dist_zero_right,Real.dist_eq,max_lt_iff,abs_lt]
    dsimp only [Prod.fst,Prod.snd]
    dsimp [A,B] at ht
    constructor
    · constructor <;> linarith [ht.1,ht.2]
    · exact hy.trans_lt (hδs.trans hsr)
  let K : Set M := {x | x∈N ∧ (f.map x).1∈Icc (0:ℝ) 1 ∧ ‖(f.map x).2‖≤δ}
  have hK : IsCompact K := hcompact δ hδ hδ₀'
  have hpK : p∈K := by
    refine ⟨hpN,?_,?_⟩ <;> simp only [hp,norm_zero]
    · constructor <;> norm_num
    · exact hδ.le
  let eco := timeSpaceCoordinates e
  let atlas := a.toCoordinates eco
  let fco := (f.toCoordinates eco).comp eco eco.contDiff
  have hpic : p∈(atlas.chart i).source := ⟨hpi,mem_univ _⟩
  obtain ⟨J,hiJ,W,hKW,hWN,hW,hcover⟩ := atlas.finite_inside hK hN (fun _ h => h.1) p hpK i hpic
  let af := atlas.restrict (J:Set I) W hW hcover
  let ff := fco.restrict (J:Set I) W hW hcover
  let j : (J:Set I) := ⟨i,hiJ⟩
  let KW : Set W := Subtype.val ⁻¹' K
  have hKWc : IsCompact KW := (Topology.IsEmbedding.subtypeVal.isCompact_preimage_iff
    (show K⊆range (Subtype.val : W → M) from fun x hx => ⟨⟨x,hKW hx⟩,rfl⟩)).mpr hK
  let T : Set W := KW∩{x | (f.map x.val).1∈Icc A B}
  have hT : IsCompact T := hKWc.inter_right (isClosed_Icc.preimage (continuous_fst.comp (hf.comp continuous_subtype_val)))
  have hTi : T⊆(af.chart j).source := by
    intro x hx
    have hxO := hbox _ hx.2 _ hx.1.2.2
    have hz := c.map_target hxO.1
    have he : f.map (c.symm (f.map x.val))=f.map x.val := hidentity hxO.1
    have hxx : c.symm (f.map x.val)=x.val := hinj _ _ (by rw [he]; exact hinit _ hxO.1)
      (hx.2.2.trans_lt hB) he
    have hsource : x.val∈c.source := hxx ▸ hz
    simpa only [af,SignedSmoothAtlas.restrict,OpenPartialHomeomorph.subtypeRestr_source,Set.mem_preimage] using
      (show x.val∈(atlas.chart i).source from ⟨hsource,mem_univ _⟩)
  obtain ⟨bump,hbump⟩ := small_inverse_bump e hδ
  let ρ : CoordinateSpace m → ℝ := bump
  have hρ : ContDiff ℝ ∞ ρ := bump.contDiff
  have hsmall (x : W) (hx : ρ (Fin.tail (ff.map x))≠0) : ‖(f.map x.val).2‖≤δ := by
    have hh := hbump (Fin.tail (ff.map x)) (subset_tsupport _ (show Fin.tail (ff.map x)∈support ρ from hx))
    simpa only [ff,AtlasSmoothMap.restrict,fco,AtlasSmoothMap.comp,ModelAtlasSmoothMap.toCoordinates,
      Function.comp_apply,eco,timeSpaceCoordinates_apply,Fin.tail_cons,e.symm_apply_apply] using hh
  have htime (x : W) : ff.map x 0=(f.map x.val).1 := rfl
  have hit (q : CoordinateSpace (m+1)) (hq : q∈(af.chart j).target) : eco.symm q∈c.target :=
    ((atlas.chart i).subtypeRestr_target_subset hW hq).2
  have hid : EqOn (ff.map ∘ (af.chart j).symm) id (af.chart j).target := by
    intro q hq
    have he := (atlas.chart i).subtypeRestr_symm_apply hW hq
    change ((af.chart j).symm q).val=(atlas.chart i).symm q at he
    change eco (f.map (((af.chart j).symm q).val))=q
    rw [he]
    change eco (f.map (c.symm (eco.symm q)))=q
    rw [show f.map (c.symm (eco.symm q))=eco.symm q from hidentity (hit q hq)]
    exact eco.apply_symm_apply q
  have hind (q : CoordinateSpace (m+1)) (hq : q∈(af.chart j).target) : q 0<(13:ℝ)/16 := by
    have hh := hinit _ (hit q hq)
    change q 0<1/4 at hh
    linarith
  have hden : tsupport (initialCollarDensity A B ρ)⊆(af.chart j).target := by
    intro q hq
    have hh := initialCollarDensity_support hAB ρ hq
    have hqO := hbox (q 0) hh.1 (e.symm (Fin.tail q)) (hbump _ hh.2)
    have hqOc : eco.symm q∈O := hqO
    let z := c.symm (eco.symm q)
    have hzmap : f.map z=eco.symm q := hidentity hqOc.1
    have hzK : z∈K := by
      refine ⟨hqOc.2,?_,?_⟩
      · rw [hzmap]
        change q 0∈Icc (0:ℝ) 1
        exact ⟨hA.le.trans hh.1.1,hh.1.2.trans (hB.le.trans (by norm_num))⟩
      · rw [hzmap]
        exact hbump _ hh.2
    let zw : W := ⟨z,hKW hzK⟩
    have hzc : z∈(atlas.chart i).source := ⟨c.map_target hqOc.1,mem_univ _⟩
    have hztarget := (atlas.chart i).map_subtype_source hW (x := zw) hzc
    have he : atlas.chart i z=q := by
      change eco (c (c.symm (eco.symm q)))=q
      rw [c.right_inv hqOc.1,eco.apply_symm_apply]
    exact he ▸ hztarget
  obtain ⟨partition⟩ := af.partition_exists hKWc
  let θ := collarCutoff A B ((13:ℝ)/16) ((7:ℝ)/8)
  have hθ : ContDiff ℝ ∞ θ := collarCutoff_smooth _ _ _ _
  have hα : (ff.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).SupportedIn KW := by
    apply ff.pullback_supported
    intro x hx
    by_cases hz : ρ (Fin.tail (ff.map x))=0
    · exact collarVolumeForm_zero_of_space hz
    have hsx := hsmall x hz
    have ht : (f.map x.val).1∉Icc (0:ℝ) 1 := by
      intro hh
      exact hx ⟨hWN x.property,hh,hsx⟩
    apply collarVolumeForm_zero_of_time
    apply collarCutoff_zero hAB (by linarith) (by norm_num)
    rw [htime]
    intro hh
    exact ht ⟨hA.le.trans hh.1,hh.2.trans (by norm_num)⟩
  have hdα : (ff.pullback (collarVolumeForm θ ρ) (collarVolumeForm_smooth hθ hρ)).exterior.SupportedIn T := by
    apply collar_pullback_exterior_supported ff hθ hρ
    intro x hx
    by_cases hz : ρ (Fin.tail (ff.map x))=0
    · exact Or.inr hz
    refine Or.inl ?_
    by_contra ht
    have hsx := hsmall x hz
    have hts := collarCutoff_deriv_support hAB (by norm_num : (13:ℝ)/16<7/8)
      (subset_tsupport _ (show ff.map x 0∈support (deriv θ) from ht))
    rw [htime] at hts
    rcases hts with hh|hh
    · apply hx
      refine ⟨⟨hWN x.property,?_,hsx⟩,hh⟩
      exact ⟨hA.le.trans hh.1,hh.2.trans (hB.le.trans (by norm_num))⟩
    · exact hfinal x.val (hWN x.property) (le_trans (by norm_num) hh.1) (hsx.trans hδ₀')
  have hρ0 : 0<ρ 0 := by
    change 0<bump 0
    rw [bump.one_of_mem_closedBall (Metric.mem_closedBall_self bump.rIn_pos.le)]
    norm_num
  exact collar_stokes_contradiction partition ff hAB (by norm_num) hρ bump.hasCompactSupport
    (fun _ => bump.nonneg) hρ0 hKWc hT inter_subset_left
    hα hdα j hTi hid hind hden


end

end HigherDimensionalBallPacking.Rigidity.Degree
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_NonlinearReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section

namespace HigherDimensionalBallPacking.Rigidity
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
section
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
lemma pathSpatialDerivative_continuous [CompleteSpace X] [CompleteSpace Y] {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) :
    Continuous (pathSpatialDerivative F) :=
  ((hF.fderiv_right (m := ∞) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)).continuous).clm_comp continuous_const

end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_SurjectiveParametricReduction
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma finiteZeroGerm_of_surjective {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {D : X →L[ℝ] Y} (hD : HasFDerivAt (fun y => F (t,y)) D x)
    (hFred : D.IsFredholm) (hs : Surjective D) (hz : F (t,x)=0) :
    Nonempty (FiniteZeroGerm F t x (Module.finrank ℝ D.ker)) := by
  obtain ⟨pkg⟩ := hFred.nonempty_fredholmPackage
  let : FiniteDimensional ℝ pkg.decDom.X₀ := pkg.decDom.finite_X₀
  let P : X →L[ℝ] pkg.decDom.X₀ :=
    (ContinuousLinearMap.snd ℝ pkg.decDom.X₁ pkg.decDom.X₀).comp (domCoords pkg).toContinuousLinearMap
  refine ⟨⟨pkg.decDom.X₀,inferInstance,?_,P,parametricSolution pkg hF hD,
    parametricSolution_base pkg hF hD,parametricSolution_smooth pkg hF hD,
    parametricSolution_kernel_coordinate pkg hF hD,
    surjective_parametricSolution_zero pkg hF hD hs hz,parametric_zero_is_solution pkg hF hD hz⟩⟩
  rw [pkg.ker_eq]


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma surjective_fredholm_right_inverse {D : X →L[ℝ] Y}
    (hD : D.IsFredholm) (hs : Surjective D) : D.HasRightInverse := by
  obtain ⟨pkg⟩ := hD.nonempty_fredholmPackage
  let := surjective_package_coker_subsingleton pkg hs
  let R : Y →L[ℝ] X := (domCoords pkg).symm.toContinuousLinearMap.comp
    ((pkg.equiv.symm.toContinuousLinearMap.comp
      ((ContinuousLinearMap.fst ℝ pkg.decCodom.X₁ pkg.decCodom.X₀).comp
        (codCoords pkg).toContinuousLinearMap)).prod 0)
  refine ⟨R,?_⟩
  intro y
  apply (codCoords pkg).injective
  change (codCoords pkg) (D ((domCoords pkg).symm (pkg.equiv.symm ((codCoords pkg) y).1,0)))=(codCoords pkg) y
  rw [fredholm_original_coords,(domCoords pkg).apply_symm_apply,pkg.equiv.apply_symm_apply]
  exact Prod.ext rfl (Subsingleton.elim _ _)

omit [CompleteSpace X] in
lemma local_continuous_right_inverse [CompleteSpace X] {Z : Type*} [TopologicalSpace Z]
    {A : Z → X →L[ℝ] Y} (hA : Continuous A) {z : Z}
    (hs : (A z).HasRightInverse) :
    ∃ V : Set Z,IsOpen V ∧ z∈V ∧ ∃ R : Z → Y →L[ℝ] X,
      ContinuousOn R V ∧ ∀ v∈V,(A v).comp (R v)=ContinuousLinearMap.id ℝ Y := by
  obtain ⟨R₀,hR₀⟩ := hs
  let B : Z → Y →L[ℝ] Y := fun v => (A v).comp R₀
  have hB : Continuous B := hA.clm_comp continuous_const
  have hBz : B z=ContinuousLinearMap.id ℝ Y := ContinuousLinearMap.ext hR₀
  let V := {v : Z | (B v).IsInvertible}
  have hV : IsOpen V := ContinuousLinearEquiv.isOpen.preimage hB
  refine ⟨V,hV,?_,fun v => R₀.comp (B v).inverse,?_,?_⟩
  · change (B z).IsInvertible
    rw [hBz]
    exact ⟨ContinuousLinearEquiv.refl ℝ Y,rfl⟩
  · intro v hv
    exact (continuousAt_const.clm_comp
      ((hv.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hB.continuousAt)).continuousWithinAt
  · intro v hv
    rw [←ContinuousLinearMap.comp_assoc]
    exact hv.self_comp_inverse

lemma compact_continuous_right_inverse {Z : Type*} [MetricSpace Z]
    {A : Z → X →L[ℝ] Y} (hA : Continuous A) {K : Set Z} (hK : IsCompact K)
    (hs : ∀ z∈K,(A z).HasRightInverse) :
    ∃ V : Set Z,IsOpen V ∧ K⊆V ∧ ∃ R : Z → Y →L[ℝ] X,
      ContinuousOn R V ∧ ∀ v∈V,(A v).comp (R v)=ContinuousLinearMap.id ℝ Y := by
  classical
  choose O hO hz R hR hAR using fun z : K => local_continuous_right_inverse hA (hs z.val z.property)
  obtain ⟨s,hsO⟩ := hK.elim_finite_subcover O hO (by
    intro z hzK
    exact mem_iUnion.mpr ⟨⟨z,hzK⟩,hz ⟨z,hzK⟩⟩)
  let I := {z : K // z∈s}
  let : Fintype I := inferInstance
  obtain ⟨ρ,hρ⟩ := PartitionOfUnity.exists_isSubordinate hK.isClosed
    (fun i : I => O i.val) (fun i => hO i.val) (by
      intro z hzk
      obtain ⟨i,hi,hzi⟩ := mem_iUnion₂.mp (hsO hzk)
      exact mem_iUnion.mpr ⟨⟨i,hi⟩,hzi⟩)
  let R₁ : Z → Y →L[ℝ] X := fun z => ∑ i : I,ρ i z • R i.val z
  have hR₁ : Continuous R₁ := by
    simpa only [finsum_eq_sum_of_fintype] using
      (PartitionOfUnity.IsSubordinate.continuous_finsum_smul (fun i : I => hO i.val) hρ
        (fun i : I => hR i.val))
  have hAR₁ : ∀ z∈K,(A z).comp (R₁ z)=ContinuousLinearMap.id ℝ Y := by
    intro z hzk
    have hsum : ∑ i : I,ρ i z=1 := by
      simpa only [finsum_eq_sum_of_fintype] using ρ.sum_eq_one hzk
    calc
      (A z).comp (R₁ z) = ∑ i : I,ρ i z • ((A z).comp (R i.val z)) := by
        apply ContinuousLinearMap.ext
        intro y
        simp [R₁]
      _ = ∑ i : I,ρ i z • ContinuousLinearMap.id ℝ Y := by
        apply Finset.sum_congr rfl
        intro i hi
        by_cases hzi : ρ i z=0
        · simp [hzi]
        · rw [hAR i.val z (hρ i (subset_closure hzi))]
      _ = ContinuousLinearMap.id ℝ Y := by rw [←Finset.sum_smul,hsum,one_smul]
  let B : Z → Y →L[ℝ] Y := fun z => (A z).comp (R₁ z)
  have hB : Continuous B := hA.clm_comp hR₁
  let V := {z : Z | (B z).IsInvertible}
  refine ⟨V,ContinuousLinearEquiv.isOpen.preimage hB,?_,
    fun z => (R₁ z).comp (B z).inverse,?_,?_⟩
  · intro z hzK
    change (B z).IsInvertible
    rw [show B z=ContinuousLinearMap.id ℝ Y from hAR₁ z hzK]
    exact ⟨ContinuousLinearEquiv.refl ℝ Y,rfl⟩
  · intro z hzV
    exact (hR₁.continuousAt.clm_comp
      ((hzV.contDiffAt_map_inverse (n := ∞)).continuousAt.comp hB.continuousAt)).continuousWithinAt
  · intro z hzV
    rw [←ContinuousLinearMap.comp_assoc]
    exact hzV.self_comp_inverse


end
section
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_apply [CompleteSpace X] [CompleteSpace Y]
    (A : X →L[ℝ] Y) (R : Y →L[ℝ] X) (x : X) :
    splitKernelProjection A R x=x-R (A x) := rfl

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_mem_ker [CompleteSpace X] [CompleteSpace Y]
    {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) (x : X) :
    A (splitKernelProjection A R x)=0 := by
  change A (x-R (A x))=0
  rw [map_sub,show A (R (A x))=A x from congrArg (fun T : Y →L[ℝ] Y => T (A x)) h,sub_self]

omit [CompleteSpace X] [CompleteSpace Y] in
lemma splitKernelProjection_fixed [CompleteSpace X] [CompleteSpace Y]
    {A : X →L[ℝ] Y} {R : Y →L[ℝ] X} {x : X}
    (hx : A x=0) : splitKernelProjection A R x=x := by
  simp only [splitKernelProjection_apply,hx,map_zero,sub_zero]

lemma splitKernelProjection_idempotent {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) :
    (splitKernelProjection A R).comp (splitKernelProjection A R)=splitKernelProjection A R := by
  apply ContinuousLinearMap.ext
  intro x
  exact splitKernelProjection_fixed (splitKernelProjection_mem_ker h x)

lemma splitKernelProjection_range {A : X →L[ℝ] Y} {R : Y →L[ℝ] X}
    (h : A.comp R=ContinuousLinearMap.id ℝ Y) :
    (splitKernelProjection A R).range=A.ker := by
  apply le_antisymm
  · rintro _ ⟨x,rfl⟩
    exact splitKernelProjection_mem_ker h x
  · intro x hx
    exact ⟨x,splitKernelProjection_fixed hx⟩

lemma ProperIndexZeroPath.cylinder_kernel_projection {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧ (0:X)∈K ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          ∃ P : (ℝ × X) → (X × E) →L[ℝ] (X × E),ContinuousOn P V ∧
            ∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL) ∧
              (P v).comp (P v)=P v ∧ (P v).range=((pathSpatialDerivative F v).coprod E.subtypeL).ker := by
  obtain ⟨K,hK,hKU,hZ,E,hE,V,hVo,hKV,hVs⟩ := h.cylinder_supplement_bp240
  let := hE
  let A : ℝ × X → (X × E) →L[ℝ] Y := fun v => (pathSpatialDerivative F v).coprod E.subtypeL
  have heA : A=(fun v => (pathSpatialDerivative F v).comp (ContinuousLinearMap.fst ℝ X E)+
      E.subtypeL.comp (ContinuousLinearMap.snd ℝ X E)) := by
    funext v
    apply ContinuousLinearMap.ext
    intro w
    rfl
  have hA : Continuous A := by
    rw [heA]
    exact ((pathSpatialDerivative_continuous h.smooth).clm_comp continuous_const).add continuous_const
  have hs : ∀ v∈Icc (0:ℝ) 1 ×ˢ K,(A v).HasRightInverse := by
    intro v hv
    have hf : IsIndexZeroFredholm (pathSpatialDerivative F v) := by
      rw [pathSpatialDerivative_eq h.smooth]
      exact h.fredholm v.1 hv.1 v.2 (hKU hv.2)
    exact surjective_fredholm_right_inverse (augment_fredholm_bp240 hf.1 E (hVs v (hKV hv))) (hVs v (hKV hv))
  obtain ⟨W,hWo,hKW,R,hR,hAR⟩ := compact_continuous_right_inverse hA (isCompact_Icc.prod hK) hs
  have h0 : (0:X)∈K := by
    obtain ⟨L,hL⟩ := h.initial
    exact hZ 0 (by constructor <;> norm_num) 0 h.origin_mem ((hL 0).trans (map_zero L))
  refine ⟨K,hK,hKU,h0,hZ,E,hE,W,hWo,hKW,fun v => splitKernelProjection (A v) (R v),?_,?_⟩
  · exact continuousOn_const.sub (hR.clm_comp hA.continuousOn)
  · intro v hv
    refine ⟨?_,splitKernelProjection_idempotent (hAR v hv),splitKernelProjection_range (hAR v hv)⟩
    intro y
    exact ⟨R v y,congrArg (fun L : Y →L[ℝ] Y => L y) (hAR v hv)⟩


end
open scoped Topology
open Set Function Filter
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

omit [CompleteSpace X] in
lemma projectionTransport_self [CompleteSpace X] {P : X →L[ℝ] X} (hP : P*P=P) :
    projectionTransport P P=1 := by
  unfold projectionTransport
  calc
    P*P+(1-P)*(1-P)=1+(P*P-P)+(P*P-P) := by noncomm_ring
    _ = 1 := by rw [hP,sub_self]; simp

omit [CompleteSpace X] in
lemma projectionTransport_comp [CompleteSpace X] {P Q : X →L[ℝ] X} (hP : P*P=P) :
    projectionTransport P Q*P=Q*P := by
  unfold projectionTransport
  calc
    (Q*P+(1-Q)*(1-P))*P=Q*(P*P)+(1-Q)*(P-P*P) := by noncomm_ring
    _ = Q*P := by rw [hP,sub_self,mul_zero,add_zero]

omit [CompleteSpace X] in
lemma comp_projectionTransport [CompleteSpace X] {P Q : X →L[ℝ] X} (hQ : Q*Q=Q) :
    Q*projectionTransport P Q=Q*P := by
  unfold projectionTransport
  calc
    Q*(Q*P+(1-Q)*(1-P))=(Q*Q)*P+(Q-Q*Q)*(1-P) := by noncomm_ring
    _ = Q*P := by rw [hQ,sub_self,zero_mul,add_zero]

lemma projectionTransport_intertwines {P Q : X →L[ℝ] X} (hP : P*P=P) (hQ : Q*Q=Q) :
    projectionTransport P Q*P=Q*projectionTransport P Q :=
  (projectionTransport_comp hP).trans (comp_projectionTransport hQ).symm

omit [CompleteSpace X] in
lemma projectionTransport_continuousOn [CompleteSpace X] {Z : Type*} [TopologicalSpace Z]
    {P Q : Z → X →L[ℝ] X} {S : Set Z} (hP : ContinuousOn P S) (hQ : ContinuousOn Q S) :
    ContinuousOn (fun z => projectionTransport (P z) (Q z)) S :=
  (hQ.mul hP).add ((continuousOn_const.sub hQ).mul (continuousOn_const.sub hP))

lemma compact_projection_transport {Z : Type*} [MetricSpace Z]
    {P : Z → X →L[ℝ] X} {K : Set Z} (hK : IsCompact K) (hP : ContinuousOn P K)
    (hp : ∀ z∈K,P z*P z=P z) :
    ∃ δ : ℝ,0<δ ∧ ∀ z∈K,∀ w∈K,dist z w<δ →(projectionTransport (P z) (P w)).IsInvertible := by
  have h1 : (1:X →L[ℝ] X).IsInvertible := ⟨ContinuousLinearEquiv.refl ℝ X,rfl⟩
  have ho : IsOpen {A : X →L[ℝ] X | A.IsInvertible} := ContinuousLinearEquiv.isOpen
  obtain ⟨ε,hε,hεi⟩ := Metric.isOpen_iff.mp ho 1 h1
  let H : Z × Z → X →L[ℝ] X := fun v => projectionTransport (P v.1) (P v.2)
  have hH : ContinuousOn H (K ×ˢ K) := projectionTransport_continuousOn
    (hP.comp continuous_fst.continuousOn (fun v hv => hv.1))
    (hP.comp continuous_snd.continuousOn (fun v hv => hv.2))
  obtain ⟨δ,hδ,hδH⟩ := Metric.uniformContinuousOn_iff.mp
    ((hK.prod hK).uniformContinuousOn_of_continuous hH) ε hε
  refine ⟨δ,hδ,?_⟩
  intro z hz w hw hzw
  apply hεi
  rw [Metric.mem_ball]
  have hd : dist (z,w) (z,z)<δ := by simpa [dist_comm] using hzw
  have hh := hδH (z,w) ⟨hz,hw⟩ (z,z) ⟨hz,hz⟩ hd
  simpa only [H,projectionTransport_self (hp z hz)] using hh



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Fredholm_ProjectionTimeGrid
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped Topology
open Set Function Filter
variable {X Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [MetricSpace Z]

lemma cappedTime_continuous (N j : ℕ) : Continuous (cappedTime N j) :=
  continuous_id.min continuous_const

lemma cappedTime_mem (N j : ℕ) {t : ℝ} (ht : t∈Icc (0:ℝ) 1) :
    cappedTime N j t∈Icc (0:ℝ) 1 :=
  ⟨le_min ht.1 (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),(min_le_left _ _).trans ht.2⟩

lemma cappedTime_zero (N : ℕ) {t : ℝ} (ht : 0≤t) : cappedTime N 0 t=0 := by
  simp only [cappedTime,Nat.cast_zero,zero_div,min_eq_right ht]

lemma cappedTime_last {N : ℕ} (hN : 0<N) {t : ℝ} (ht : t≤1) : cappedTime N N t=t := by
  have hNr : (N:ℝ)≠0 := by exact_mod_cast hN.ne'
  simp only [cappedTime,div_self hNr,min_eq_left ht]

lemma cappedTime_step (N j : ℕ) (t : ℝ) :
    dist (cappedTime N j t) (cappedTime N (j+1) t)≤1/(N:ℝ) := by
  have hN : (0:ℝ)≤N := Nat.cast_nonneg N
  have hi : (j:ℝ)/(N:ℝ)≤(j+1:ℕ)/(N:ℝ) := div_le_div_of_nonneg_right (by norm_num) hN
  have hmono : cappedTime N j t ≤ cappedTime N (j+1) t := min_le_min_left t hi
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hmono)]
  change -(min t ((j:ℝ)/N)-min t ((j+1:ℕ)/N))≤_
  have hg : (j+1:ℕ)/(N:ℝ)=(j:ℝ)/(N:ℝ)+1/(N:ℝ) := by rw [Nat.cast_add,Nat.cast_one,add_div]
  rw [hg]
  have hnon : 0≤1/(N:ℝ) := div_nonneg zero_le_one hN
  by_cases hj : t≤(j:ℝ)/(N:ℝ)
  · rw [min_eq_left hj,min_eq_left (hj.trans (le_add_of_nonneg_right hnon))]
    linarith
  · have hj' := le_of_not_ge hj
    rw [min_eq_right hj']
    have hh := min_le_right t ((j:ℝ)/N+1/(N:ℝ))
    linarith

omit [CompleteSpace X] in
lemma projectionTimeChain_invertible [CompleteSpace X] {P : ℝ × Z → X →L[ℝ] X} {K : Set Z} {δ : ℝ}
    (hs : ∀ z∈Icc (0:ℝ) 1 ×ˢ K,∀ w∈Icc (0:ℝ) 1 ×ˢ K,dist z w<δ →
      (projectionTransport (P z) (P w)).IsInvertible)
    {N : ℕ} (hN : 1/(N:ℝ)<δ) (j : ℕ) {v : ℝ × Z} (hv : v∈Icc (0:ℝ) 1 ×ˢ K) :
    (projectionTimeChain P N j v).IsInvertible := by
  induction j with
  | zero => exact ⟨ContinuousLinearEquiv.refl ℝ X,rfl⟩
  | succ j ih =>
    change (projectionTransport _ _ * _).IsInvertible
    apply ContinuousLinearMap.IsInvertible.comp _ ih
    apply hs (cappedTime N j v.1,v.2) ⟨cappedTime_mem N j hv.1,hv.2⟩
      (cappedTime N (j+1) v.1,v.2) ⟨cappedTime_mem N (j+1) hv.1,hv.2⟩
    simpa only [Prod.dist_eq,dist_self,max_eq_left (dist_nonneg)] using (cappedTime_step N j v.1).trans_lt hN

lemma cappedTimeMap_continuous (N j : ℕ) : Continuous (cappedTimeMap (Z := Z) N j) :=
  ((cappedTime_continuous N j).comp continuous_fst).prodMk continuous_snd

lemma gridDomain_open {V : Set (ℝ × Z)} (hV : IsOpen V) (N : ℕ) : IsOpen (gridDomain V N) :=
  (hV.inter (hV.preimage (continuous_const.prodMk continuous_snd))).inter
    (isOpen_iInter_of_finite (fun j => hV.preimage (cappedTimeMap_continuous N j.val)))

omit [MetricSpace Z] in
lemma gridDomain_time_mem [MetricSpace Z] {V : Set (ℝ × Z)} {N j : ℕ} (hj : j≤N)
    {v : ℝ × Z} (hv : v∈gridDomain V N) : cappedTimeMap N j v∈V :=
  mem_iInter.mp hv.2 ⟨j,Nat.lt_succ_of_le hj⟩

omit [MetricSpace Z] in
lemma gridDomain_contains [MetricSpace Z] {V : Set (ℝ × Z)} {K : Set Z}
    (hVK : Icc (0:ℝ) 1 ×ˢ K⊆V) (N : ℕ) :
    Icc (0:ℝ) 1 ×ˢ K⊆gridDomain V N := by
  intro v hv
  refine ⟨⟨hVK hv,hVK ⟨by constructor <;> norm_num,hv.2⟩⟩,mem_iInter.mpr ?_⟩
  intro j
  exact hVK ⟨cappedTime_mem N j.val hv.1,hv.2⟩

lemma projectionTimeChain_continuousOn_grid {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hP : ContinuousOn P V) (N j : ℕ) (hj : j≤N) :
    ContinuousOn (projectionTimeChain P N j) (gridDomain V N) := by
  induction j with
  | zero => exact continuousOn_const
  | succ j ih =>
    apply ContinuousOn.mul _ (ih (Nat.le_trans (Nat.le_succ j) hj))
    apply projectionTransport_continuousOn
    · exact hP.comp (cappedTimeMap_continuous N j).continuousOn
        (fun v hv => gridDomain_time_mem (Nat.le_trans (Nat.le_succ j) hj) hv)
    · exact hP.comp (cappedTimeMap_continuous N (j+1)).continuousOn
        (fun v hv => gridDomain_time_mem hj hv)

lemma projectionTimeChain_intertwines_grid {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) (N j : ℕ) (hj : j≤N)
    {v : ℝ × Z} (hv : v∈gridDomain V N) :
    projectionTimeChain P N j v*P (cappedTimeMap N 0 v)=
      P (cappedTimeMap N j v)*projectionTimeChain P N j v := by
  induction j with
  | zero => simp only [projectionTimeChain,one_mul,mul_one]
  | succ j ih =>
    have hj' : j≤N := Nat.le_trans (Nat.le_succ j) hj
    change (projectionTransport (P (cappedTimeMap N j v)) (P (cappedTimeMap N (j+1) v))*
      projectionTimeChain P N j v)*P (cappedTimeMap N 0 v)=_
    rw [mul_assoc,ih hj',←mul_assoc,
      projectionTransport_intertwines (hp _ (gridDomain_time_mem hj' hv))
        (hp _ (gridDomain_time_mem hj hv)),mul_assoc]
    rfl

lemma extendedTimeTransport_continuousOn {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hP : ContinuousOn P V) (N : ℕ) : ContinuousOn (extendedTimeTransport P N) (gridDomain V N) := by
  apply ContinuousOn.mul
  · apply ContinuousOn.mul
    · exact projectionTransport_continuousOn
        (hP.comp (cappedTimeMap_continuous N N).continuousOn (fun v hv => gridDomain_time_mem le_rfl hv))
        (hP.mono (fun v hv => hv.1.1))
    · exact projectionTimeChain_continuousOn_grid hP N N le_rfl
  · exact projectionTransport_continuousOn
      (hP.comp (continuous_const.prodMk continuous_snd).continuousOn (fun v hv => hv.1.2))
      (hP.comp (cappedTimeMap_continuous N 0).continuousOn (fun v hv => gridDomain_time_mem (Nat.zero_le N) hv))

lemma extendedTimeTransport_intertwines {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) (N : ℕ) {v : ℝ × Z} (hv : v∈gridDomain V N) :
    extendedTimeTransport P N v*P (0,v.2)=P v*extendedTimeTransport P N v := by
  have h0 : P (0,v.2)*P (0,v.2)=P (0,v.2) := hp _ hv.1.2
  have hvp := hp v hv.1.1
  have hs := hp _ (gridDomain_time_mem (Nat.zero_le N) hv)
  have hf := hp _ (gridDomain_time_mem (N := N) le_rfl hv)
  unfold extendedTimeTransport
  rw [mul_assoc,projectionTransport_intertwines h0 hs,←mul_assoc, mul_assoc
    (projectionTransport _ _) (projectionTimeChain P N N v),
    projectionTimeChain_intertwines_grid hp N N le_rfl hv,←mul_assoc
      (projectionTransport _ _),projectionTransport_intertwines hf hvp]
  simp only [mul_assoc]

omit [MetricSpace Z] in
lemma extendedTimeTransport_eq_chain [MetricSpace Z] {V : Set (ℝ × Z)} {P : ℝ × Z → X →L[ℝ] X}
    (hp : ∀ v∈V,P v*P v=P v) {N : ℕ} (hN : 0<N) {v : ℝ × Z}
    (ht : v.1∈Icc (0:ℝ) 1) (hv : v∈gridDomain V N) :
    extendedTimeTransport P N v=projectionTimeChain P N N v := by
  have h0 : P (0,v.2)*P (0,v.2)=P (0,v.2) := hp _ hv.1.2
  have hvp := hp v hv.1.1
  simp only [extendedTimeTransport,cappedTimeMap,cappedTime_last hN ht.2,
    cappedTime_zero N ht.1,Prod.mk.eta,projectionTransport_self hvp,projectionTransport_self h0,one_mul,mul_one]

lemma compact_kernel_transport_neighborhood {V : Set (ℝ × Z)} {K : Set Z}
    {P : ℝ × Z → X →L[ℝ] X} (hK : IsCompact K) (hV : IsOpen V)
    (hVK : Icc (0:ℝ) 1 ×ˢ K⊆V) (hP : ContinuousOn P V) (hp : ∀ v∈V,P v*P v=P v) :
    ∃ W : Set (ℝ × Z),IsOpen W ∧ Icc (0:ℝ) 1 ×ˢ K⊆W ∧ W⊆V ∧
      (∀ v∈W,(0,v.2)∈V) ∧ ∃ T : ℝ × Z → X →L[ℝ] X,ContinuousOn T W ∧
        ∀ v∈W,(T v).IsInvertible ∧ T v*P (0,v.2)=P v*T v := by
  obtain ⟨δ,hδ,hstep⟩ := compact_projection_transport (isCompact_Icc.prod hK) (hP.mono hVK)
    (fun v hv => hp v (hVK hv))
  obtain ⟨N,hN⟩ := exists_nat_one_div_lt hδ
  let M := N+1
  have hM : 0<M := Nat.succ_pos N
  have hNM : 1/(M:ℝ)<δ := by simpa only [M,Nat.cast_add,Nat.cast_one] using hN
  let T := extendedTimeTransport P M
  let G := gridDomain V M
  have hGs : IsOpen G := gridDomain_open hV M
  have hGc : Icc (0:ℝ) 1 ×ˢ K⊆G := gridDomain_contains hVK M
  have hT : ContinuousOn T G := extendedTimeTransport_continuousOn hP M
  let W := G ∩ T ⁻¹' {L : X →L[ℝ] X | L.IsInvertible}
  have hW : IsOpen W := hT.isOpen_inter_preimage hGs ContinuousLinearEquiv.isOpen
  refine ⟨W,hW,?_,(fun v hv => hv.1.1.1),(fun v hv => hv.1.1.2),T,hT.mono inter_subset_left,?_⟩
  · intro v hv
    refine ⟨hGc hv,?_⟩
    change (extendedTimeTransport P M v).IsInvertible
    rw [extendedTimeTransport_eq_chain hp hM hv.1 (hGc hv)]
    exact projectionTimeChain_invertible hstep hNM M hv
  · intro v hv
    exact ⟨hv.2,extendedTimeTransport_intertwines hp M hv.1⟩


end
open scoped ContDiff Topology
open Set Function Filter
open HolderCompletion
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma pathSpatialDerivative_initial {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F)
    {L : X ≃L[ℝ] Y} (hL : ∀ x,F (0,x)=L x) (x : X) :
    pathSpatialDerivative F (0,x)=L.toContinuousLinearMap := by
  rw [pathSpatialDerivative_eq hF]
  have he : (fun y => F (0,y))=L := funext hL
  rw [he]
  exact L.hasFDerivAt.fderiv

omit [CompleteSpace X] in
lemma projection_fixed_iff_range [CompleteSpace X] {Q : X →L[ℝ] X} (hQ : Q.comp Q=Q) (x : X) :
    Q x=x ↔ x∈Q.range := by
  constructor
  · intro hx; exact ⟨x,hx⟩
  · rintro ⟨y,rfl⟩
    exact congrArg (fun A : X →L[ℝ] X => A y) hQ

lemma ProperIndexZeroPath.stabilized_kernel_frame {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) :
    ∃ K : Set X,IsCompact K ∧ K⊆U ∧ (0:X)∈K ∧
      (∀ t∈Icc (0:ℝ) 1,∀ x∈U,F (t,x)=0 →x∈K) ∧
      ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
        ∃ V : Set (ℝ × X),IsOpen V ∧ Icc (0:ℝ) 1 ×ˢ K⊆V ∧
          (∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) ∧
          Nonempty (StabilizedKernelFrame F E V) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hVo,hKV,P,hP,hproj⟩ := h.cylinder_kernel_projection
  let := hE
  have hp : ∀ v∈V,P v*P v=P v := fun v hv => (hproj v hv).2.1
  obtain ⟨W,hWo,hKW,hWV,hW0,T,hT,hTi⟩ := compact_kernel_transport_neighborhood hK hVo hKV hP hp
  obtain ⟨L,hL⟩ := h.initial
  let B := initialKernelGraph L E
  have hB (e : E) : L (B e).1+((B e).2:Y)=0 := by
    simp only [B,initialKernelGraph_apply,map_neg,L.apply_symm_apply,neg_add_cancel]
  have hPf {v : ℝ × X} (hv : v∈V) (w : X × E) :
      P v w=w ↔ ((pathSpatialDerivative F v).coprod E.subtypeL) w=0 := by
    rw [projection_fixed_iff_range (hproj v hv).2.1,(hproj v hv).2.2]
    rfl
  have hP0 {v : ℝ × X} (hv : v∈W) (e : E) : P (0,v.2) (B e)=B e := by
    apply (hPf (hW0 v hv) (B e)).mpr
    rw [pathSpatialDerivative_initial h.smooth hL]
    exact hB e
  let Q : (ℝ × X) → E →L[ℝ] (X × E) := fun v => (T v).comp B
  let C : (ℝ × X) → (X × E) →L[ℝ] E := fun v =>
    (ContinuousLinearMap.snd ℝ X E).comp (T v).inverse
  have hcT : ContinuousOn (fun v => (T v).inverse) W := by
    intro v hv
    exact ((hTi v hv).1.contDiffAt_map_inverse (n := ∞)).continuousAt.comp_continuousWithinAt (hT v hv)
  refine ⟨K,hK,hKU,h0K,hZ,E,hE,W,hWo,hKW,(fun v hv => (hproj v (hWV hv)).1),⟨{
    frame := Q
    coordinate := C
    frame_continuous := hT.clm_comp continuousOn_const
    coordinate_continuous := continuousOn_const.clm_comp hcT
    kernel := ?_
    left_inv := ?_
    right_inv := ?_ }⟩⟩
  · intro v hv e
    apply (hPf (hWV hv) (Q v e)).mp
    have hh := congrArg (fun A : (X × E) →L[ℝ] (X × E) => A (B e)) (hTi v hv).2
    change T v (P (0,v.2) (B e))=P v (T v (B e)) at hh
    rw [hP0 hv e] at hh
    exact hh.symm
  · intro v hv e
    change ((T v).inverse (T v (B e))).2=e
    rw [(hTi v hv).1.inverse_apply_self]
    rfl
  · intro v hv w hw
    have hPw := (hPf (hWV hv) w).mpr hw
    have hTiw := (hTi v hv).1.self_apply_inverse w
    have hh := congrArg (fun A : (X × E) →L[ℝ] (X × E) => A ((T v).inverse w)) (hTi v hv).2
    change T v (P (0,v.2) ((T v).inverse w))=P v (T v ((T v).inverse w)) at hh
    rw [hTiw,hPw] at hh
    have hp0 : P (0,v.2) ((T v).inverse w)=(T v).inverse w :=
      (hTi v hv).1.injective (hh.trans hTiw.symm)
    have hk0 := (hPf (hW0 v hv) ((T v).inverse w)).mp hp0
    rw [pathSpatialDerivative_initial h.smooth hL] at hk0
    have hb0 := (initialKernelGraph_kernel ((T v).inverse w)).mp hk0
    change T v (B (((T v).inverse w).2))=w
    rw [show B (((T v).inverse w).2)=(T v).inverse w from hb0]
    exact hTiw



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_ZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)

include fr in
lemma StabilizedKernelFrame.zero_germ (hF : ContDiff ℝ ∞ F)
    {t : ℝ} {x : X} {e : E} (hv : (t,x)∈V)
    (hs : Surjective ((pathSpatialDerivative F (t,x)).coprod E.subtypeL))
    (hz : finiteTargetAugment F E (t,(x,e))=0) :
    Nonempty (FiniteZeroGerm (finiteTargetAugment F E) t (x,e) (Module.finrank ℝ E)) := by
  let A := (pathSpatialDerivative F (t,x)).coprod E.subtypeL
  have hd : HasFDerivAt (fun w : X × E => finiteTargetAugment F E (t,w)) A (x,e) := by
    have hsl : ContDiff ℝ ∞ (fun w : X × E => finiteTargetAugment F E (t,w)) :=
      (finiteTargetAugment_smooth hF E).comp (contDiff_const.prodMk contDiff_id)
    have h := (hsl.differentiable (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (x,e)).hasFDerivAt
    rwa [finiteTargetAugment_spatial_derivative hF E t x e] at h
  have hdim : Module.finrank ℝ E=Module.finrank ℝ A.ker := (fr.kernelEquiv hv).finrank_eq
  rw [hdim]
  exact finiteZeroGerm_of_surjective (finiteTargetAugment_smooth hF E) hd (fr.fredholm hv hs) hs hz


end
open scoped ContDiff Topology
open Set Function Filter



end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Moduli_SmoothZeroCharts
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open _root_.OAI.ContinuousLinearMap.FredholmPackage

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

omit [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y] in
lemma FiniteZeroGerm.compact_zero_neighborhood [CompleteSpace X] [NormedSpace ℝ Y] [CompleteSpace Y]
    {F : ℝ × X → Y} {t : ℝ} {x : X} {m : ℕ}
    (g : FiniteZeroGerm F t x m) {W : Set (ℝ × X)} (hW : IsOpen W) (hw : (t,x)∈W) :
    ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ (t,x)∈O ∧ ∀ v∈O,F v=0 →v∈C := by
  let : FiniteDimensional ℝ g.kernelSpace := g.finite_kernel
  let a : ℝ × g.kernelSpace := (t,g.coordinate x)
  let ψ : ℝ × g.kernelSpace → ℝ × X := fun v => (v.1,g.reconstruct v)
  let P : ℝ × X → ℝ × g.kernelSpace := fun v => (v.1,g.coordinate v.2)
  have hP : Continuous P := continuous_fst.prodMk (g.coordinate.continuous.comp continuous_snd)
  have hψ : ContDiffAt ℝ ∞ ψ a := contDiffAt_fst.prodMk g.smooth
  have hψa : ψ a=(t,x) := Prod.ext rfl g.base
  have hWa : ∀ᶠ v in 𝓝 a,ψ v∈W := hψ.continuousAt (hψa.symm ▸ hW.mem_nhds hw)
  obtain ⟨S,hS,hψS⟩ := hψ.contDiffOn (m := 0) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top) (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨r,hr,hrS⟩ := Metric.mem_nhds_iff.mp (inter_mem hS (inter_mem g.zero hWa))
  have hrb : Metric.closedBall a (r/2)⊆Metric.ball a r :=
    Metric.closedBall_subset_ball (half_lt_self hr)
  let C := ψ '' Metric.closedBall a (r/2)
  have hC : IsCompact C := (isCompact_closedBall a (r/2)).image_of_continuousOn
    (hψS.continuousOn.mono (fun v hv => (hrS (hrb hv)).1))
  have hCW : C⊆W := by rintro _ ⟨v,hv,rfl⟩; exact (hrS (hrb hv)).2.2
  have hCz : C⊆{v | F v=0} := by rintro _ ⟨v,hv,rfl⟩; exact (hrS (hrb hv)).2.1
  have hnear : ∀ᶠ v in 𝓝 (t,x),F v=0 →v∈C := by
    filter_upwards [g.complete,hP.continuousAt (Metric.ball_mem_nhds a (half_pos hr))] with v hv hp hz
    have he : ψ (P v)=v := Prod.ext rfl (hv hz)
    exact ⟨P v,Metric.ball_subset_closedBall hp,he⟩
  let O := interior {v : ℝ × X | F v=0 →v∈C}
  refine ⟨C,O,hC,hCW,hCz,isOpen_interior,mem_interior_iff_mem_nhds.mpr hnear,?_⟩
  intro v hv hz
  exact interior_subset hv hz

lemma compact_zero_reservoir {F : ℝ × X → Y} {K W : Set (ℝ × X)}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K⊆W)
    (hcharts : ∀ v∈K,∃ m,Nonempty (FiniteZeroGerm F v.1 v.2 m)) :
    ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ K⊆O ∧ ∀ v∈O,F v=0 →v∈C := by
  classical
  have hl (v : K) : ∃ C O : Set (ℝ × X),IsCompact C ∧ C⊆W ∧ C⊆{v | F v=0} ∧
      IsOpen O ∧ v.val∈O ∧ ∀ y∈O,F y=0 →y∈C := by
    obtain ⟨m,⟨g⟩⟩ := hcharts v.val v.property
    exact g.compact_zero_neighborhood hW (hKW v.property)
  choose C O hC hCW hCz hO hv hOz using hl
  have hcover : K⊆⋃ v : K,O v := by
    intro v hvK
    exact mem_iUnion.mpr ⟨⟨v,hvK⟩,hv ⟨v,hvK⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover O hO hcover
  refine ⟨⋃ v∈s,C v,⋃ v∈s,O v,s.isCompact_biUnion (fun v _ => hC v),?_,?_,
    isOpen_biUnion (fun v hv => hO v),hs,?_⟩
  · exact iUnion₂_subset (fun v _ => hCW v)
  · exact iUnion₂_subset (fun v _ => hCz v)
  · intro y hy hz
    obtain ⟨v,hv,hy⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion₂.mpr ⟨v,hv,hOz v y hy hz⟩


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma compact_zero_isolating_neighborhood {F : ℝ × X → Y} (hF : Continuous F)
    {K W : Set (ℝ × X)} (hK : IsCompact K) (hW : IsOpen W) (hKW : K⊆W)
    (hcharts : ∀ v∈K,∃ m,Nonempty (FiniteZeroGerm F v.1 v.2 m)) :
    ∃ N : Set (ℝ × X),IsOpen N ∧ K⊆N ∧
      IsCompact (closure N ∩ {v | F v=0}) ∧ (closure N ∩ {v | F v=0})⊆W := by
  obtain ⟨C,O,hC,hCW,hCz,hO,hKO,hnear⟩ := compact_zero_reservoir hK hW hKW hcharts
  obtain ⟨r,hr,hrO⟩ := hK.exists_cthickening_subset_open hO hKO
  let N := Metric.thickening r K
  have hcl : closure N⊆O :=
    (closure_minimal (Metric.thickening_subset_cthickening r K) Metric.isClosed_cthickening).trans hrO
  have hres : (closure N ∩ {v | F v=0})⊆C := fun v hv => hnear v (hcl hv.1) hv.2
  refine ⟨N,Metric.isOpen_thickening,Metric.self_subset_thickening hr K,?_,hres.trans hCW⟩
  exact hC.of_isClosed_subset (isClosed_closure.inter (isClosed_eq hF continuous_const)) hres


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {U : Set X} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {N : Set (ℝ × (X × E))}

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_target_boundary_avoid [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N) :
    ∃ δ : ℝ,0<δ ∧ ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →finiteTargetAugment F E v≠0 := by
  let C := (closure N ∩ {v | finiteTargetAugment F E v=0}) ∩
    (frontier N ∩ {v | v.1∈Icc (0:ℝ) 1})
  have hC : IsCompact C := h.compact.inter_right
    (isClosed_frontier.inter (isClosed_Icc.preimage continuous_fst))
  let B := (fun v : ℝ × (X × E) => v.2.2) '' C
  have hB : IsCompact B := hC.image (continuous_snd.comp continuous_snd)
  have hB0 : (0:E)∉B := by
    rintro ⟨⟨t,x,e⟩,⟨⟨hcl,hz⟩,hf,ht⟩,he⟩
    have he0 : e=0 := he
    subst e
    have hx := h.domain (t,(x,0)) hcl hz
    have hz' : F (t,x)=0 := by simpa only [Set.mem_ofPred_eq,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hz
    have hn := h.contains t ht x hx hz'
    rw [h.isOpen.frontier_eq] at hf
    exact hf.2 hn
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 0 hB0
  refine ⟨r/2,half_pos hr,?_⟩
  intro v hv ht he hz
  have hm : v.2.2∈B := ⟨v,⟨⟨frontier_subset_closure hv,hz⟩,hv,ht⟩,rfl⟩
  apply hrB (show v.2.2∈Metric.ball 0 r from ?_) hm
  simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

section
-- module Solutions.OAIQ240_BP.BallPacking_Continuation_ProperPaths
attribute [-instance] _root_.OAI.PackingSufficiencySupport.Hamiltonian.flatProduct_chartedSpace
attribute [-simp] _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.infinity_end_count _root_.OAI.PackingSufficiencySupport.DiagonalQuadrics.sqrt_sq_complex
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace HigherDimensionalBallPacking.Rigidity

section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

lemma freezeTime_smooth : ContDiff ℝ ∞ freezeTime :=
  (show ContDiff ℝ ∞ Real.smoothTransition from contDiff_infty.mpr (fun _ => Real.smoothTransition.contDiff)).comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
lemma freezeTime_mem (t : ℝ) : freezeTime t∈Icc (0:ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩
lemma freezeTime_final {t : ℝ} (ht : 3/4≤t) : freezeTime t=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)
lemma frozenPath_smooth {F : ℝ × X → Y} (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (frozenPath F) :=
  hF.comp ((freezeTime_smooth.comp contDiff_fst).prodMk contDiff_snd)

lemma ProperIndexZeroPath.frozen {F : ℝ × X → Y} {U : Set X} (h : ProperIndexZeroPath F U) :
    ProperIndexZeroPath (frozenPath F) U := by
  let K := Prod.snd '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  have hK : IsCompact K := h.zeroSet_compact.image continuous_snd
  have hKU : K⊆U := by rintro x ⟨v,hv,rfl⟩; exact hv.2.1
  have he : {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ frozenPath F v=0} =
      (Icc (0:ℝ) 1 ×ˢ K) ∩ {v | frozenPath F v=0} := by
    ext v
    constructor
    · rintro ⟨ht,hx,hz⟩
      exact ⟨⟨ht,⟨(freezeTime v.1,v.2),⟨freezeTime_mem _,hx,hz⟩,rfl⟩⟩,hz⟩
    · rintro ⟨⟨ht,hx⟩,hz⟩
      exact ⟨ht,hKU hx,hz⟩
  refine ⟨h.domain_open,h.origin_mem,frozenPath_smooth h.smooth,?_,?_,?_⟩
  · obtain ⟨L,hL⟩ := h.initial
    refine ⟨L,fun x => ?_⟩
    change F (freezeTime 0,x)=L x
    rw [freezeTime_initial (by norm_num)]
    exact hL x
  · rw [he]
    exact (isCompact_Icc.prod hK).inter_right (isClosed_eq (frozenPath_smooth h.smooth).continuous continuous_const)
  · intro t ht x hx
    exact h.fredholm _ (freezeTime_mem t) x hx


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  (L : X ≃L[ℝ] Y) (hL : ∀ x,F (0,x)=L x)

omit [FiniteDimensional ℝ E] in
lemma frozenInitialChart_smooth [FiniteDimensional ℝ E] : ContDiff ℝ ∞ (frozenInitialChart L hL (E := E)).reconstruct :=
  (initialKernelGraph L E).contDiff.comp contDiff_snd

omit [FiniteDimensional ℝ E] in
lemma frozenInitialChart_source [FiniteDimensional ℝ E]
    (v : {v : ℝ × (X × E) // finiteTargetAugment (frozenPath F) E v=0}) :
    v∈(frozenInitialChart L hL).partialHomeomorph.source ↔ v.val.1<1/4 := by
  change (v.val.1<1/4 ∧ v.val.1<1/4) ↔ _
  simp


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

theorem ProperIndexZeroPath.smooth_framed_isolating_stabilization
    {F : ℝ × X → Y} {U : Set X} (h : ProperIndexZeroPath F U) :
    ∃ E : Submodule ℝ Y,∃ _ : FiniteDimensional ℝ E,
      ∃ V : Set (ℝ × X),IsOpen V ∧
        ∃ _ : StabilizedKernelFrame F E V,
          ∃ N : Set (ℝ × (X × E)),IsolatingStabilization F U E N ∧
            (∀ v∈closure N,finiteTargetAugment F E v=0 →(v.1,v.2.1)∈V) ∧
            (∀ v∈V,Surjective ((pathSpatialDerivative F v).coprod E.subtypeL)) := by
  obtain ⟨K,hK,hKU,h0K,hZ,E,hE,V,hVo,hKV,hs,⟨fr⟩⟩ := h.stabilized_kernel_frame
  let := hE
  let B : ℝ × X → ℝ × (X × E) := fun v => (v.1,(v.2,0))
  have hB : Continuous B := continuous_fst.prodMk (continuous_snd.prodMk continuous_const)
  let Z := B '' {v : ℝ × X | v.1∈Icc (0:ℝ) 1 ∧ v.2∈U ∧ F v=0}
  let W : Set (ℝ × (X × E)) := {v | v.2.1∈U ∧ (v.1,v.2.1)∈V}
  have hZc : IsCompact Z := h.zeroSet_compact.image hB
  have hWo : IsOpen W := (h.domain_open.preimage (continuous_fst.comp continuous_snd)).inter
    (hVo.preimage (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))
  have hZW : Z⊆W := by
    rintro _ ⟨⟨t,x⟩,hv,rfl⟩
    exact ⟨hv.2.1,hKV ⟨hv.1,hZ t hv.1 x hv.2.1 hv.2.2⟩⟩
  have hg (v : ℝ × (X × E)) (hv : v∈W) (hz : finiteTargetAugment F E v=0) :
      Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 (Module.finrank ℝ E)) :=
    fr.zero_germ h.smooth hv.2 (hs _ hv.2) hz
  have hcharts : ∀ v∈Z,∃ m,Nonempty (FiniteZeroGerm (finiteTargetAugment F E) v.1 v.2 m) := by
    intro v hv
    refine ⟨Module.finrank ℝ E,hg v (hZW hv) ?_⟩
    rcases hv with ⟨⟨t,x⟩,hv,rfl⟩
    simpa only [B,finiteTargetAugment,ZeroMemClass.coe_zero,add_zero] using hv.2.2
  obtain ⟨N,hNo,hZN,hNc,hNW⟩ := compact_zero_isolating_neighborhood
    (finiteTargetAugment_smooth h.smooth E).continuous hZc hWo hZW hcharts
  refine ⟨E,hE,V,hVo,fr,N,⟨hNo,?_,hNc,?_,?_⟩,?_,?_⟩
  · intro t ht x hx hz
    exact hZN ⟨(t,x),⟨ht,hx,hz⟩,rfl⟩
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).1
  · intro v hv ht hz
    exact hg v (hNW ⟨hv,hz⟩) hz
  · intro v hv hz
    exact (hNW ⟨hv,hz⟩).2
  · exact hs


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
variable {F : ℝ × X → Y} {U : Set X} {E : Submodule ℝ Y} [FiniteDimensional ℝ E]
  {N : Set (ℝ × (X × E))}

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_frozen_final_collar [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization (frozenPath F) U E N) (hn : ∀ x∈U,F (1,x)≠0) :
    ∃ δ : ℝ,0<δ ∧ ∀ v∈closure N,3/4≤v.1 →‖v.2.2‖≤δ →
      finiteTargetAugment (frozenPath F) E v≠0 := by
  let C := (closure N ∩ {v | finiteTargetAugment (frozenPath F) E v=0}) ∩ {v | 3/4≤v.1}
  have hC : IsCompact C := h.compact.inter_right (isClosed_le continuous_const continuous_fst)
  let B := (fun v : ℝ × (X × E) => v.2.2) '' C
  have hB : IsCompact B := hC.image (continuous_snd.comp continuous_snd)
  have hB0 : (0:E)∉B := by
    rintro ⟨⟨t,x,e⟩,⟨⟨hcl,hz⟩,ht⟩,he⟩
    have he0 : e=0 := he
    subst e
    have hx := h.domain (t,(x,0)) hcl hz
    change F (freezeTime t,x)+(0:Y)=0 at hz
    rw [freezeTime_final ht,add_zero] at hz
    exact hn x hx hz
  obtain ⟨r,hr,hrB⟩ := Metric.isOpen_iff.mp hB.isClosed.isOpen_compl 0 hB0
  refine ⟨r/2,half_pos hr,?_⟩
  intro v hv ht he hz
  apply hrB (show v.2.2∈Metric.ball 0 r from ?_) ⟨v,⟨⟨hv,hz⟩,ht⟩,rfl⟩
  simpa only [Metric.mem_ball,dist_zero_right] using he.trans_lt (half_lt_self hr)

omit [CompleteSpace X] [CompleteSpace Y] in
lemma IsolatingStabilization.small_target_reservoir [CompleteSpace X] [CompleteSpace Y]
    (h : IsolatingStabilization F U E N) {δ : ℝ}
    (hδ : ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →finiteTargetAugment F E v≠0) :
    let K := (closure N ∩ {v | finiteTargetAugment F E v=0}) ∩
      {v | v.1∈Icc (0:ℝ) 1 ∧ ‖v.2.2‖≤δ}
    IsCompact K ∧ K⊆N := by
  dsimp only
  refine ⟨h.compact.inter_right ?_,?_⟩
  · exact (isClosed_Icc.preimage continuous_fst).inter
      (isClosed_le ((continuous_snd.comp continuous_snd).norm) continuous_const)
  · intro v hv
    by_contra hn
    have hf : v∈frontier N := by
      rw [h.isOpen.frontier_eq]
      exact ⟨hv.1.1,hn⟩
    exact hδ v hf hv.2.1 hv.2.2 hv.1.2


end
section
open scoped ContDiff Topology
open Set Function Filter
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]

lemma orientedZeroAtlas_self_source {F : ℝ × X → Y} {E : Submodule ℝ Y}
    [FiniteDimensional ℝ E] {V : Set (ℝ × X)} (fr : StabilizedKernelFrame F E V)
    (hF : ContDiff ℝ ∞ F) (hV : IsOpen V)
    (a : SmoothZeroAtlas (finiteTargetAugment F E) E (framedZeroOpen F E V hV))
    (x : framedZeroOpen F E V hV) : x∈((fr.orientedZeroAtlas hF hV a).chart x).source := by
  change x∈(((a.localChart x).symm.restrOpen _ _).symm).source
  refine ⟨a.chartedSpace.mem_chart_source x,?_⟩
  exact (framedChart_orientation_neighborhood fr (a.chart x) hF hV
    (a.localChart_target x (framedLocalChart_base_target hV a x))
    (framedLocalChart_V hV a x (framedLocalChart_base_target hV a x))).choose_spec.2.1

 theorem ProperIndexZeroPath.endpoint_exists_bp240_oai {F : ℝ × X → Y} {U : Set X}
    (h : ProperIndexZeroPath F U) : ∃ x∈U,F (1,x)=0 := by
  classical
  by_contra hn
  push Not at hn
  obtain ⟨E,hE,V,hV,fr,N,hN,hNV,hs⟩ := h.frozen.smooth_framed_isolating_stabilization
  let := hE
  obtain ⟨L,hL⟩ := h.initial
  let A := finiteTargetAugment (frozenPath F) E
  let M := framedZeroOpen (frozenPath F) E V hV
  let base : ℝ × (X × E) := ((1:ℝ)/8,(0,0))
  have hbz : A base=0 := by
    change F (freezeTime (1/8),0)+(0:Y)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero,add_zero]
  have hbN : base∈N := by
    apply hN.contains (1/8) (by constructor <;> norm_num) 0 h.origin_mem
    change F (freezeTime (1/8),0)=0
    rw [freezeTime_initial (by norm_num),hL,map_zero]
  let p : M := ⟨⟨base,hbz⟩,hNV base (subset_closure hbN) hbz⟩
  let c := frozenInitialChart L hL (E := E)
  have hpC : p.val∈c.partialHomeomorph.source := by
    apply (frozenInitialChart_source L hL p.val).mpr
    norm_num [p,base]
  let a₀ := fr.smoothZeroAtlas (frozenPath_smooth h.smooth) hV hs
  let a := a₀.prescribe p c hpC (frozenInitialChart_smooth L hL).contDiffOn
  let atlas := fr.orientedZeroAtlas (frozenPath_smooth h.smooth) hV a
  let π := fr.physicalProjection (frozenPath_smooth h.smooth) hV a
  have hπ (z : M) : π.map z=(z.val.val.1,z.val.val.2.2) := rfl
  have hπc : Continuous π.map := (continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)).prodMk
    (continuous_snd.comp (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))
  have hpi : p∈(atlas.chart p).source := orientedZeroAtlas_self_source fr (frozenPath_smooth h.smooth) hV a p
  have hπp : π.map p=((1:ℝ)/8,0) := rfl
  have hac : a.chart p=c.rebase p.val hpC := a₀.prescribe_at p c hpC (frozenInitialChart_smooth L hL).contDiffOn
  have hid : EqOn (π.map ∘ (atlas.chart p).symm) id (atlas.chart p).target := by
    intro q hq
    change ((((a.localChart p).symm q).val.val).1,(((a.localChart p).symm q).val.val).2.2)=q
    rw [a.localChart_symm_val p (orientedZeroAtlas_target fr (frozenPath_smooth h.smooth) hV a p hq),hac]
    rfl
  have hint : ∀ q∈(atlas.chart p).target,q.1<1/4 := by
    intro q hq
    have hh := a.localChart_target p (orientedZeroAtlas_target fr (frozenPath_smooth h.smooth) hV a p hq)
    rw [hac] at hh
    exact hh
  have hinj : ∀ x y : M,(π.map x).1<1/4 →(π.map y).1<1/4 →π.map x=π.map y →x=y := by
    intro x y hx hy he
    have hxx : initialKernelGraph L E x.val.val.2.2=x.val.val.2 := c.complete x.val.val hx x.val.property
    have hyy : initialKernelGraph L E y.val.val.2.2=y.val.val.2 := c.complete y.val.val hy y.val.property
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact congrArg (fun v : ℝ × E => v.1) he
    · exact hxx.symm.trans ((congrArg (initialKernelGraph L E) (congrArg Prod.snd he)).trans hyy)
  let N₀ : Set M := {z | z.val.val∈N}
  have hN₀ : IsOpen N₀ := hN.isOpen.preimage (continuous_subtype_val.comp continuous_subtype_val)
  have hpN₀ : p∈N₀ := hbN
  obtain ⟨δB,hδB,havoid⟩ := hN.small_target_boundary_avoid
  obtain ⟨δF,hδF,hfinal⟩ := hN.small_frozen_final_collar hn
  let δ₀ := min δB δF
  have hδ₀ : 0<δ₀ := lt_min hδB hδF
  have hcompact : ∀ δ : ℝ,0<δ →δ≤δ₀ →IsCompact {z : M | z∈N₀ ∧
      (π.map z).1∈Icc (0:ℝ) 1 ∧ ‖(π.map z).2‖≤δ} := by
    intro δ hδ hd
    have hsmall : ∀ v∈frontier N,v.1∈Icc (0:ℝ) 1 →‖v.2.2‖≤δ →A v≠0 := by
      intro v hv ht he
      exact havoid v hv ht (he.trans (hd.trans (min_le_left _ _)))
    have hc := hN.small_target_reservoir hsmall
    let C : Set (ℝ × (X × E)) := (closure N ∩ {v | A v=0}) ∩
      {v | v.1∈Icc (0:ℝ) 1 ∧ ‖v.2.2‖≤δ}
    have hCc : IsCompact C := hc.1
    have hCN : C⊆N := hc.2
    let val : M → ℝ × (X × E) := fun z => z.val.val
    have hval : Topology.IsEmbedding val := Topology.IsEmbedding.subtypeVal.comp Topology.IsEmbedding.subtypeVal
    have hCrange : C⊆range val := by
      intro v hv
      exact ⟨⟨⟨v,hv.1.2⟩,hNV v hv.1.1 hv.1.2⟩,rfl⟩
    have hpre := (hval.isCompact_preimage_iff hCrange).mpr hCc
    have he : val ⁻¹' C={z : M | z∈N₀ ∧ (π.map z).1∈Icc (0:ℝ) 1 ∧ ‖(π.map z).2‖≤δ} := by
      ext z
      constructor
      · intro hz
        exact ⟨hCN hz,hz.2⟩
      · rintro ⟨hz,ht,he⟩
        exact ⟨⟨subset_closure hz,z.val.property⟩,ht,he⟩
    rwa [he] at hpre
  have hfinal₀ : ∀ z∈N₀,3/4≤(π.map z).1 →‖(π.map z).2‖≤δ₀ →False := by
    intro z hz ht he
    exact hfinal z.val.val (subset_closure hz) ht (he.trans (min_le_right _ _)) z.val.property
  exact Degree.isolated_collar_impossible atlas π hπc p p hpi hπp hid hint hinj N₀ hN₀ hpN₀
    δ₀ hδ₀ hcompact hfinal₀


end

end HigherDimensionalBallPacking.Rigidity
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240_oai.{u_1, u_2} := @OAI.HigherDimensionalBallPacking.Rigidity.ProperIndexZeroPath.endpoint_exists_bp240_oai.{u_1, u_2}
