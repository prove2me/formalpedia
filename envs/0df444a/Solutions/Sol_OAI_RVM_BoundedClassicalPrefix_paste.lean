-- Prove2me | solution 1 for OAI.RVM.BoundedClassicalPrefix.paste
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:35:09.246589+00:00
-- url     : https://prove2.me/submissions/2c475ba8-b761-4006-9b7e-9de20dee7693

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000

section
-- module Solutions.OAIQ073_VM.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeMotion
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Elementary relativistic geometry needed by the retarded-force identity. -/

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM

lemma q_pos (v : Vec) : 0 < q v := by
  exact Real.sqrt_pos.2 (by positivity)

open scoped Topology

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ExtendedLorentz
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma contDiff_q {k : ℕ∞ω} : ContDiff ℝ k q := by
  exact ((contDiff_const : ContDiff ℝ k (fun _ : Vec => (1 : ℝ))).add
    (contDiff_id.norm_sq ℝ)).sqrt (fun v => by positivity)

lemma contDiff_velocity {k : ℕ∞ω} : ContDiff ℝ k velocity := by
  exact (contDiff_q.inv (fun v => ne_of_gt (q_pos v))).smul contDiff_id

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeRadius
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
open Set


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma fderiv_phase_split {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : Phase → H} {y v u K : Vec} (hg : DifferentiableAt ℝ g (y,v)) :
    fderiv ℝ (fun z => g (z,v)) y u+fderiv ℝ (fun w => g (y,w)) v K =
      fderiv ℝ g (y,v) (u,K) := by
  have hiy : HasFDerivAt (fun z : Vec => (z,v))
      ((ContinuousLinearMap.id ℝ Vec).prod (0 : Vec →L[ℝ] Vec)) y :=
    (hasFDerivAt_id y).prodMk (hasFDerivAt_const v y)
  have hiv : HasFDerivAt (fun w : Vec => (y,w))
      ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec)) v :=
    (hasFDerivAt_const y v).prodMk (hasFDerivAt_id v)
  have hy := hg.hasFDerivAt.comp y hiy
  have hv := hg.hasFDerivAt.comp v hiv
  have hy' : fderiv ℝ (fun z => g (z,v)) y u=fderiv ℝ g (y,v) (u,0) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L u) hy.fderiv using 1 <;> rfl
  have hv' : fderiv ℝ (fun w => g (y,w)) v K=fderiv ℝ g (y,v) (0,K) := by
    convert congrArg (fun L : Vec →L[ℝ] H => L K) hv.fderiv using 1 <;> rfl
  rw [hy',hv']
  rw [← map_add]
  congr 1
  ext <;> simp

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SmoothIntegral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

section SpatialDerivatives
variable {A E W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma contDiff_iteratedFDeriv_slice {F : A × E → W} (hF : ContDiff ℝ ∞ F) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : A × E => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2) := by
  induction n with
  | zero =>
    exact (continuousMultilinearCurryFin0 ℝ E W).symm.contDiff.comp hF
  | succ n ih =>
    let G : A × E → (E [×n]→L[ℝ] W) := fun p => iteratedFDeriv ℝ n (fun x => F (p.1,x)) p.2
    change ContDiff ℝ ∞ G at ih
    have he (p : A × E) : fderiv ℝ (fun x => G (p.1,x)) p.2 =
        (fderiv ℝ G p).comp (ContinuousLinearMap.inr ℝ A E) := by
      have hin : HasFDerivAt (fun x : E => (p.1,x)) (ContinuousLinearMap.inr ℝ A E) p.2 := by
        convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
      exact ((ih.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
    simp only [iteratedFDeriv_succ_eq_comp_left,Function.comp_apply]
    change ContDiff ℝ ∞ (fun p : A × E =>
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm (fderiv ℝ (fun x => G (p.1,x)) p.2))
    simp_rw [he]
    exact (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n+1) => E) W).symm.contDiff.comp
      ((ih.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const)

end SpatialDerivatives

section CompactFamily
variable {α : Type v} {E : Type u} [TopologicalSpace α]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]

lemma SmoothCompactFamily.ofJoint {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    {G : A × E → W} (hG : ContDiff ℝ ∞ G) {ι : α → A} (hι : Continuous ι) :
    SmoothCompactFamily (fun a x => G (ι a,x)) := by
  refine ⟨fun a => hG.comp (contDiff_const.prodMk contDiff_id),fun n => ?_⟩
  exact (contDiff_iteratedFDeriv_slice hG n).continuous.comp
    ((hι.comp continuous_snd).prodMk continuous_fst)

lemma SmoothCompactFamily.continuous {F : α → E → W} (hF : SmoothCompactFamily F) :
    Continuous (fun p : E × α => F p.2 p.1) := by
  have h := (continuousMultilinearCurryFin0 ℝ E W).continuous.comp (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply] using h

lemma SmoothCompactFamily.derivFamily {F : α → E → W} (hF : SmoothCompactFamily F) :
    SmoothCompactFamily (fun a => fderiv ℝ (F a)) := by
  refine ⟨fun a => (hF.1 a).fderiv_right (m:=∞) (by simp),fun n => ?_⟩
  have he (p : E × α) : iteratedFDeriv ℝ n (fderiv ℝ (F p.2)) p.1 =
      continuousMultilinearCurryRightEquiv' ℝ n E W (iteratedFDeriv ℝ (n+1) (F p.2) p.1) := by
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply,LinearIsometryEquiv.apply_symm_apply]
  simp_rw [he]
  exact (continuousMultilinearCurryRightEquiv' ℝ n E W).continuous.comp (hF.2 (n+1))

variable [MeasurableSpace α] [BorelSpace α] [CompactSpace α] [SecondCountableTopology α]
  [ProperSpace E] [CompleteSpace W]

omit [CompleteSpace W] in
lemma hasFDerivAt_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) (x : E) :
    HasFDerivAt (fun y => ∫ a, F a y ∂μ) (∫ a, fderiv ℝ (F a) x ∂μ) x := by
  have hD := hF.derivFamily.continuous
  obtain ⟨C,hC⟩ := ((isCompact_closedBall x 1).prod isCompact_univ).image hD |>.isBounded |>.exists_norm_le
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (s:=closedBall x 1) (bound:=fun _ => C) (F':=fun y a => fderiv ℝ (F a) y)
    (closedBall_mem_nhds x (by norm_num))
  · exact Eventually.of_forall (fun y => (hF.continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  · exact (hF.continuous.comp (continuous_const.prodMk continuous_id)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact (hD.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact ae_of_all _ (fun a y hy => hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩)
  · exact integrable_const _
  · exact ae_of_all _ (fun a y _ => ((hF.1 a).differentiable (by simp) y).hasFDerivAt)

lemma contDiff_integral_smoothFamily_nat (μ : Measure α) [IsFiniteMeasure μ] (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : α → E → W}, SmoothCompactFamily F → ContDiff ℝ n (fun x => ∫ a, F a x ∂μ) := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiff_zero.mpr
    apply continuousOn_univ.mp
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ hF.continuous.continuousOn
    intro x a _ ha
    exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    rw [show (↑(n+1) : ℕ∞ω) = ↑n+1 by simp,contDiff_succ_iff_fderiv]
    refine ⟨fun x => (hasFDerivAt_integral_smoothFamily μ hF x).differentiableAt,by simp,?_⟩
    have he : fderiv ℝ (fun x => ∫ a, F a x ∂μ) = (fun x => ∫ a, fderiv ℝ (F a) x ∂μ) := by
      funext x
      exact (hasFDerivAt_integral_smoothFamily μ hF x).fderiv
    rw [he]
    exact ih hF.derivFamily

lemma contDiff_integral_smoothFamily (μ : Measure α) [IsFiniteMeasure μ]
    {F : α → E → W} (hF : SmoothCompactFamily F) : ContDiff ℝ ∞ (fun x => ∫ a, F a x ∂μ) := by
  rw [contDiff_infty]
  exact fun n => contDiff_integral_smoothFamily_nat μ n hF

end CompactFamily

variable {E W : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

attribute [local instance] Measure.Subtype.measureSpace in
lemma contDiff_spatial_intervalIntegral {F : ℝ × E → W} (hF : ContDiff ℝ ∞ F)
    {a b : ℝ} (hab : a≤b) : ContDiff ℝ ∞ (fun y => ∫ r in a..b, F (r,y)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := contDiff_integral_smoothFamily (volume : Measure (Icc a b))
    (SmoothCompactFamily.ofJoint (α:=Icc a b) hF continuous_subtype_val)
  have he (y : E) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  simpa only [he] using hh

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardCurvature
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma curl_eq_curlMap {g : Vec → Vec} (hg : Differentiable ℝ g) (x : Vec) :
    curl g x=curlMap (fderiv ℝ g x) := by
  have hi (i j : Fin 3) : spatialPartial (fun y => g y i) x j=(fderiv ℝ g x (basis j)) i := by
    have hh := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).hasFDerivAt.comp x (hg x).hasFDerivAt
    change HasFDerivAt (fun y => g y i) _ x at hh
    rw [spatialPartial,hh.fderiv]
    rfl
  ext i
  fin_cases i <;> simp [curl,curlMap,hi]

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma derivWithin_Ici_eq_Icc_of_lt {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) {t T : ℝ} (ht : t<T) :
    derivWithin f (Ici 0) t=derivWithin f (Icc 0 T) t := by
  apply derivWithin_congr_set
  filter_upwards [Iio_mem_nhds ht] with r hr
  change (0 ≤ r) = (0 ≤ r ∧ r≤T)
  exact propext ⟨fun h => ⟨h,hr.le⟩,fun h => h.1⟩

lemma SlabEquations.equationsBefore {s : Solution} {T : ℝ} (h : SlabEquations s T) :
    EquationsBefore s T := by
  intro t ht htT
  simpa only [derivWithin_Ici_eq_Icc_of_lt _ htT] using h t ⟨ht,htT.le⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SpatialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

universe u

variable {U V W Z : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {n : ℕ∞} {J : Set ℝ}

lemma SpatiallySmoothSlab.spatialJetRegular {F : ℝ × U → W} {T : ℝ}
    (hF : SpatiallySmoothSlab T F) : SpatialJetRegular 0 (Icc 0 T) F :=
  ⟨hF.1,fun j => contDiffOn_zero.mpr (hF.2 j)⟩

lemma SpatialJetRegular.regular {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    ContDiffOn ℝ n F {p | p.1∈J} := by
  have h := (continuousMultilinearCurryFin0 ℝ U W).contDiff.comp_contDiffOn (hF.2 0)
  simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,LinearIsometryEquiv.apply_symm_apply,Prod.mk.eta] using h

lemma SpatialJetRegular.deriv {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    SpatialJetRegular n J (fun p : ℝ × U => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  refine ⟨fun t ht => (hF.1 t ht).fderiv_right (m:=∞) (by simp),fun j => ?_⟩
  let A : (U [×(j+1)]→L[ℝ] W) →L[ℝ] (U [×j]→L[ℝ] U →L[ℝ] W) :=
    (continuousMultilinearCurryRightEquiv' ℝ j U W).toContinuousLinearEquiv.toContinuousLinearMap
  have he := ContinuousLinearMap.contDiff (𝕜:=ℝ) (E:=U [×(j+1)]→L[ℝ] W)
    (F:=U [×j]→L[ℝ] U →L[ℝ] W) (n:=(n:ℕ∞ω)) A
  have h := he.comp_contDiffOn (hF.2 (j+1))
  simpa [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def] using h

lemma SpatialJetRegular.clm {F : ℝ × U → V} (hF : SpatialJetRegular n J F) (L : V →L[ℝ] W) :
    SpatialJetRegular n J (fun p => L (F p)) := by
  refine ⟨fun t ht => L.contDiff.comp (hF.1 t ht),fun j => ?_⟩
  let A := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin j => U) V W) L
  have h := A.contDiff.comp_contDiffOn (hF.2 j)
  apply h.congr
  intro p hp
  exact L.iteratedFDeriv_comp_left (hF.1 p.1 hp).contDiffAt (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))

lemma SpatialJetRegular.add {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (hG : SpatialJetRegular n J G) : SpatialJetRegular n J (fun p => F p+G p) := by
  refine ⟨fun t ht => (hF.1 t ht).add (hG.1 t ht),fun j => ?_⟩
  apply ((hF.2 j).add (hG.2 j)).congr
  intro p hp
  exact congrFun (iteratedFDeriv_add
    ((hF.1 p.1 hp).of_le (show (j:ℕ∞ω)≤∞ by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))) ((hG.1 p.1 hp).of_le (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)))) p.2

lemma SpatialJetRegular.congr {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (he : ∀ p : ℝ × U, p.1∈J → G p=F p) : SpatialJetRegular n J G := by
  have hs (t : ℝ) (ht : t∈J) : (fun x => G (t,x))=(fun x => F (t,x)) := funext fun x => he (t,x) ht
  refine ⟨fun t ht => by rw [hs t ht]; exact hF.1 t ht,fun j => ?_⟩
  apply (hF.2 j).congr
  intro p hp
  rw [hs p.1 hp]

lemma spatialJetRegular_bilinear_jet (j : ℕ) :
    ∀ {V W Z : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      (B : V →L[ℝ] W →L[ℝ] Z) {F : ℝ × U → V} {G : ℝ × U → W},
      SpatialJetRegular n J F → SpatialJetRegular n J G →
      ContDiffOn ℝ n (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => B (F (p.1,x)) (G (p.1,x))) p.2)
        {p | p.1∈J} := by
  induction j with
  | zero =>
    intro V W Z _ _ _ _ _ _ B F G hF hG
    have h := ((B.contDiff.comp_contDiffOn hF.regular).clm_apply hG.regular)
    simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
      (continuousMultilinearCurryFin0 ℝ U Z).symm.contDiff.comp_contDiffOn h
  | succ j ih =>
    intro V W Z _ _ _ _ _ _ B F G hF hG
    let DF := fun p : ℝ × U => fderiv ℝ (fun x => F (p.1,x)) p.2
    let DG := fun p : ℝ × U => fderiv ℝ (fun x => G (p.1,x)) p.2
    have h1 := ih (B.precompR U) hF hG.deriv
    have h2 := ih (B.precompL U) hF.deriv hG
    have h := (continuousMultilinearCurryRightEquiv' ℝ j U Z).symm.contDiff.comp_contDiffOn (h1.add h2)
    apply h.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
    congr 1
    have he : fderiv ℝ (fun x => B (F (p.1,x)) (G (p.1,x))) =
        fun x => B.precompR U (F (p.1,x)) (DG (p.1,x)) + B.precompL U (DF (p.1,x)) (G (p.1,x)) := by
      funext x
      exact B.fderiv_of_bilinear ((hF.1 p.1 hp).differentiable (by simp) x)
        ((hG.1 p.1 hp).differentiable (by simp) x)
    rw [he]
    have hR : ContDiff ℝ ∞ (fun x => B.precompR U (F (p.1,x)) (DG (p.1,x))) :=
      by
        have hB : ContDiff ℝ ∞ (B.precompR U) := ContinuousLinearMap.contDiff _
        exact (hB.comp (hF.1 p.1 hp)).clm_apply (hG.deriv.1 p.1 hp)
    have hL : ContDiff ℝ ∞ (fun x => B.precompL U (DF (p.1,x)) (G (p.1,x))) :=
      by
        have hB : ContDiff ℝ ∞ (B.precompL U) := ContinuousLinearMap.contDiff _
        exact (hB.comp (hF.deriv.1 p.1 hp)).clm_apply (hG.1 p.1 hp)
    have hj : (j:ℕ∞ω)≤∞ := by exact_mod_cast (le_top : (j:ℕ∞)≤⊤)
    exact congrFun (iteratedFDeriv_add (hR.of_le hj) (hL.of_le hj)) p.2

lemma SpatialJetRegular.bilinear {F : ℝ × U → V} {G : ℝ × U → W}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) (B : V →L[ℝ] W →L[ℝ] Z) :
    SpatialJetRegular n J (fun p => B (F p) (G p)) := by
  exact ⟨fun t ht => (B.contDiff.comp (hF.1 t ht)).clm_apply (hG.1 t ht),
    fun j => spatialJetRegular_bilinear_jet j B hF hG⟩

end

section
universe u
variable {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] {n : ℕ∞} {J : Set ℝ}

lemma spatialJetRegular_iterated (j : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × U → W},
      SpatialJetRegular n J F → SpatialJetRegular n J
        (fun p : ℝ × U => iteratedFDeriv ℝ j (fun x => F (p.1,x)) p.2) := by
  induction j with
  | zero =>
    intro W _ _ F hF
    let A : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using hF.clm A
  | succ j ih =>
    intro W _ _ F hF
    let A : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using (ih hF.deriv).clm A

lemma SpatialJetRegular.mono_order {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : ℝ × U → W} {m : ℕ∞} (hF : SpatialJetRegular n J F) (h : m≤n) : SpatialJetRegular m J F :=
  ⟨hF.1,fun j => (hF.2 j).of_le (by exact_mod_cast h)⟩

end

universe u
variable {U V W Z : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z] {n : ℕ∞} {J : Set ℝ}

lemma SpatialJetRegular.precomp {F : ℝ × V → W} (hF : SpatialJetRegular n J F) (L : U →L[ℝ] V) :
    SpatialJetRegular n J (fun p : ℝ × U => F (p.1,L p.2)) := by
  refine ⟨fun t ht => (hF.1 t ht).comp L.contDiff,fun j => ?_⟩
  let A : (V [×j]→L[ℝ] W) →L[ℝ] (U [×j]→L[ℝ] W) :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ : Fin j => L)
  have h := A.contDiff.comp_contDiffOn ((hF.2 j).comp
    (contDiffOn_fst.prodMk (L.contDiff.comp_contDiffOn contDiffOn_snd)) (fun p hp => hp))
  apply h.congr
  intro p hp
  exact L.iteratedFDeriv_comp_right (hF.1 p.1 hp) p.2
    (by exact_mod_cast (le_top : (j:ℕ∞)≤⊤))

lemma spatialJetRegular_fixed {F : U → W} (hF : ContDiff ℝ ∞ F) :
    SpatialJetRegular n J (fun p : ℝ × U => F p.2) := by
  refine ⟨fun _ _ => hF,fun j => ?_⟩
  exact ((hF.iteratedFDeriv_right (m:=∞) (i:=j) (by exact_mod_cast (le_top : (⊤:ℕ∞)+(j:ℕ∞)≤⊤))).of_le
    (by exact_mod_cast (le_top : n≤⊤))).comp_contDiffOn contDiffOn_snd

lemma SpatialJetRegular.neg {F : ℝ × U → W} (hF : SpatialJetRegular n J F) :
    SpatialJetRegular n J (fun p => -F p) := by
  simpa using hF.clm (-(ContinuousLinearMap.id ℝ W))

lemma SpatialJetRegular.sub {F G : ℝ × U → W} (hF : SpatialJetRegular n J F)
    (hG : SpatialJetRegular n J G) : SpatialJetRegular n J (fun p => F p-G p) := by
  simpa only [sub_eq_add_neg] using hF.add hG.neg

lemma SpatialJetRegular.prodMk {F : ℝ × U → V} {G : ℝ × U → W}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) :
    SpatialJetRegular n J (fun p => (F p,G p)) := by
  convert (hF.clm (ContinuousLinearMap.inl ℝ V W)).add
    (hG.clm (ContinuousLinearMap.inr ℝ V W)) using 1
  all_goals try with_reducible_and_instances rfl
  simp

lemma SpatialJetRegular.clm_comp_const {F : ℝ × U → (V →L[ℝ] W)}
    (hF : SpatialJetRegular n J F) (L : Z →L[ℝ] V) :
    SpatialJetRegular n J (fun p => (F p).comp L) := by
  exact hF.clm ((ContinuousLinearMap.compL ℝ Z V W).flip L)

lemma SpatialJetRegular.clm_apply {F : ℝ × U → (V →L[ℝ] W)} {G : ℝ × U → V}
    (hF : SpatialJetRegular n J F) (hG : SpatialJetRegular n J G) :
    SpatialJetRegular n J (fun p => F p (G p)) :=
  hF.bilinear hG (ContinuousLinearMap.id ℝ (V →L[ℝ] W))

end


open Set Filter Metric MeasureTheory
open scoped Topology

lemma hasFDerivWithinAt_integral_dominated
    {A H E : Type*} [MeasurableSpace A] {μ : Measure A}
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F : H → A → E} {F' : A → H →L[ℝ] E} {s : Set H} {x₀ : H} {b : A → ℝ}
    (hF : ∀ᶠ x in 𝓝[s] x₀, Integrable (F x) μ) (hF₀ : Integrable (F x₀) μ)
    (hF' : Integrable F' μ) (hb : Integrable b μ) (hbn : ∀ a, 0 ≤ b a)
    (hlip : ∀ᶠ x in 𝓝[s] x₀, ∀ᵐ a ∂μ, ‖F x a-F x₀ a‖ ≤ b a*‖x-x₀‖)
    (hd : ∀ᵐ a ∂μ, HasFDerivWithinAt (F · a) (F' a) s x₀) :
    HasFDerivWithinAt (fun x => ∫ a, F x a ∂μ) (∫ a, F' a ∂μ) s x₀ := by
  have hn (x : H) : 0 ≤ ‖x-x₀‖⁻¹ := inv_nonneg.mpr (norm_nonneg _)
  have he : ∀ᶠ x in 𝓝[s] x₀,
      ‖x-x₀‖⁻¹ * ‖((∫ a, F x a ∂μ)-(∫ a, F x₀ a ∂μ))-(∫ a, F' a ∂μ) (x-x₀)‖ =
      ‖∫ a, ‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀)) ∂μ‖ := by
    filter_upwards [hF] with x hx
    rw [← norm_smul_of_nonneg (hn _), integral_smul, integral_sub,
      integral_sub, ← ContinuousLinearMap.integral_apply hF']
    exacts [hx, hF₀, hx.sub hF₀, hF'.apply_continuousLinearMap _]
  rw [hasFDerivWithinAt_iff_tendsto, tendsto_congr' he,
    ← tendsto_zero_iff_norm_tendsto_zero,
    ← show (∫ a : A, ‖x₀-x₀‖⁻¹ • (F x₀ a-F x₀ a-F' a (x₀-x₀)) ∂μ)=0 by simp]
  apply tendsto_integral_filter_of_dominated_convergence (bound := fun a => b a+‖F' a‖)
  · filter_upwards [hF] with x hx
    exact ((hx.aestronglyMeasurable.sub hF₀.aestronglyMeasurable).sub
      (hF'.aestronglyMeasurable.apply_continuousLinearMap _)).const_smul _
  · filter_upwards [hlip] with x hx
    filter_upwards [hx] with a ha
    calc
      ‖‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀))‖
        ≤ ‖x-x₀‖⁻¹ * (‖F x a-F x₀ a‖+‖F' a (x-x₀)‖) := by
          rw [norm_smul_of_nonneg (hn _)]; gcongr; exact norm_sub_le _ _
      _ ≤ ‖x-x₀‖⁻¹ * (b a*‖x-x₀‖+‖F' a‖*‖x-x₀‖) := by
          gcongr; exact (F' a).le_opNorm _
      _ ≤ b a+‖F' a‖ := by
          rw [← add_mul, ← div_eq_inv_mul]
          have hab := hbn a
          apply div_le_of_le_mul₀ <;> first | rfl | positivity
  · exact hb.add hF'.norm
  · filter_upwards [hd] with a ha
    suffices Tendsto (fun x => ‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀)))
        (𝓝[s] x₀) (𝓝 0) by simpa
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have heq : (fun x => ‖x-x₀‖⁻¹ * ‖F x a-F x₀ a-F' a (x-x₀)‖) =
        (fun x => ‖‖x-x₀‖⁻¹ • (F x a-F x₀ a-F' a (x-x₀))‖) := by
      funext x; rw [norm_smul_of_nonneg (hn x)]
    rwa [hasFDerivWithinAt_iff_tendsto,heq] at ha


section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section
universe u
section Differentiation
variable {H A W : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {S : Set H} {F : H → A → W} {D : H → A → H →L[ℝ] W}

lemma hasFDerivWithinAt_integral_compactFamily (hSc : IsClosed S) (hSv : Convex ℝ S)
    (hF : ContinuousOn F.uncurry (S ×ˢ univ)) (hD : ContinuousOn D.uncurry (S ×ˢ univ))
    (hd : ∀ x∈S, ∀ a, HasFDerivWithinAt (fun y => F y a) (D x a) S x)
    {x : H} (hx : x∈S) :
    HasFDerivWithinAt (fun y => ∫ a, F y a ∂μ) (∫ a, D x a ∂μ) S x := by
  have hc {Z : Type u} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
      {G : H → A → Z} (hG : ContinuousOn G.uncurry (S ×ˢ univ)) {y : H} (hy : y∈S) :
      Continuous (G y) := by
    apply continuousOn_univ.mp
    exact hG.comp ((continuous_const.prodMk continuous_id).continuousOn) (fun a _ => ⟨hy,mem_univ a⟩)
  have hi (y : H) (hy : y∈S) : Integrable (F y) μ :=
    (hc hF hy).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hiD : Integrable (D x) μ :=
    (hc hD hx).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let K := S ∩ closedBall x 1
  have hK : IsCompact K := (isCompact_closedBall x 1).inter_left hSc
  obtain ⟨C,hC⟩ := ((hK.prod isCompact_univ).image_of_continuousOn
    (hD.mono (fun p hp => ⟨hp.1.1,hp.2⟩))).isBounded.exists_norm_le
  let B := max C 0
  have hB : 0≤B := le_max_right _ _
  have hb (y : H) (hy : y∈K) (a : A) : ‖D y a‖≤B :=
    (hC _ ⟨(y,a),⟨hy,mem_univ a⟩,rfl⟩).trans (le_max_left _ _)
  have hxl : x∈K := ⟨hx,mem_closedBall_self (by norm_num)⟩
  have hnear : ∀ᶠ y in 𝓝[S] x, y∈K :=
    Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds (closedBall_mem_nhds x (by norm_num)))
  apply hasFDerivWithinAt_integral_dominated
    (hF:=Filter.Eventually.mono (self_mem_nhdsWithin : ∀ᶠ y in 𝓝[S] x, y∈S) (fun y hy => hi y hy)) (hF₀:=hi x hx)
    (hF':=hiD) (b:=fun _ => B) (hb:=integrable_const _) (hbn:=fun _ => hB)
  · filter_upwards [hnear] with y hy
    exact ae_of_all _ fun a => Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le
      (fun z hz => (hd z hz.1 a).mono inter_subset_left) (fun z hz => hb z hz a)
      (hSv.inter (convex_closedBall x 1)) hxl hy
  · exact ae_of_all _ (hd x hx)
end Differentiation

variable {H V A : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [ProperSpace H]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] [CompactSpace A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ] {v : A → V} (hv : Continuous v)
  {S : Set H} (hSc : IsClosed S) (hSv : Convex ℝ S) (hSu : UniqueDiffOn ℝ S)

include hv hSc hSv hSu in

lemma contDiffOn_integral_compact_parameter_nat (n : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : H × V → W}, ContDiffOn ℝ n F (S ×ˢ univ) →
      ContDiffOn ℝ n (fun x => ∫ a, F (x,v a) ∂μ) S := by
  induction n with
  | zero =>
    intro W _ _ _ F hF
    apply contDiffOn_zero.mpr
    apply continuousOn_integral_of_compact_support (k:=univ) isCompact_univ
    · exact hF.continuousOn.comp
        ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn) (fun p hp => ⟨hp.1,mem_univ _⟩)
    · intro x a _ ha; exact (ha (mem_univ a)).elim
  | succ n ih =>
    intro W _ _ _ F hF
    have hu := hSu.prod (uniqueDiffOn_univ (𝕜:=ℝ) (E:=V))
    have hn : (↑(n+1) : ℕ∞ω)=(n:ℕ∞ω)+1 := by simp
    rw [hn] at hF ⊢
    let D := fderivWithin ℝ F (S ×ˢ univ)
    have hD : ContDiffOn ℝ n D (S ×ˢ univ) := hF.fderivWithin hu le_rfl
    let L : H →L[ℝ] H × V := ContinuousLinearMap.inl ℝ H V
    have hd (x : H) (hx : x∈S) : HasFDerivWithinAt
        (fun y => ∫ a, F (y,v a) ∂μ) (∫ a, (D (x,v a)).comp L ∂μ) S x := by
      refine hasFDerivWithinAt_integral_compactFamily (μ:=μ)
        (F:=fun y a => F (y,v a)) (D:=fun y a => (D (y,v a)).comp L) hSc hSv ?_ ?_ ?_ hx
      · exact hF.continuousOn.comp
          ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn) (fun p hp => ⟨hp.1,mem_univ _⟩)
      · exact (hD.continuousOn.comp
          ((continuous_fst.prodMk (hv.comp continuous_snd)).continuousOn)
          (fun p hp => ⟨hp.1,mem_univ _⟩)).clm_comp continuousOn_const
      · intro y hy a
        have hi : HasFDerivWithinAt (fun z : H => (z,v a)) L S y := by
          convert ((hasFDerivAt_id y).prodMk (hasFDerivAt_const (v a) y)).hasFDerivWithinAt (s:=S) using 1 <;> rfl
        have ho : HasFDerivWithinAt F (D (y,v a)) (S ×ˢ univ) (y,v a) :=
          (hF.differentiableOn (by simp) (y,v a) ⟨hy,mem_univ _⟩).hasFDerivWithinAt
        exact ho.comp y hi (show MapsTo (fun z : H => (z,v a)) S (S ×ˢ (univ : Set V)) from fun z hz => ⟨hz,mem_univ _⟩)
    rw [contDiffOn_succ_iff_fderivWithin hSu]
    refine ⟨fun x hx => (hd x hx).differentiableWithinAt,by simp,?_⟩
    have he (x : H) (hx : x∈S) : fderivWithin ℝ (fun y => ∫ a, F (y,v a) ∂μ) S x =
        ∫ a, (D (x,v a)).comp L ∂μ := (hd x hx).fderivWithin (hSu x hx)
    exact (ih (hD.clm_comp contDiffOn_const)).congr he

end

universe u
variable {U V A : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace A] [CompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A]
  {μ : Measure A} [IsFiniteMeasure μ] {v : A → V} (hv : Continuous v)
  {T : ℝ} (hT : 0<T) (n : ℕ)

omit [SecondCountableTopology A] in
include hv hT in
lemma contDiffOn_integral_spatialJet
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F) :
    ContDiffOn ℝ n (fun p : ℝ × U => ∫ a, F (p.1,p.2,v a) ∂μ) {p | p.1∈Icc 0 T} := by
  have hs : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
  apply contDiffOn_integral_compact_parameter_nat (μ:=μ)
    (F:=fun p : (ℝ × U) × V => F (p.1.1,p.1.2,p.2)) hv
    (isClosed_Icc.preimage continuous_fst)
    (by simpa only [Set.preimage,hs] using (convex_Icc (𝕜:=ℝ) 0 T).prod (convex_univ (𝕜:=ℝ) (E:=U)))
    (by simpa only [Set.preimage,hs] using (uniqueDiffOn_Icc hT).prod (uniqueDiffOn_univ (𝕜:=ℝ) (E:=U))) n
  exact hF.regular.comp
    (contDiffOn_fst.fst.prodMk (contDiffOn_fst.snd.prodMk contDiffOn_snd)) (fun p hp => hp.1)

omit [ProperSpace U] [CompactSpace A] [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] in
include hv in
lemma spatialJet_compactFamily
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F)
    {t : ℝ} (ht : t∈Icc 0 T) :
    SmoothCompactFamily (fun a x => F (t,x,v a)) := by
  apply SmoothCompactFamily.ofJoint (G:=fun p : V × U => F (t,p.2,p.1))
  · exact (hF.1 t ht).comp (contDiff_snd.prodMk contDiff_fst)
  · exact hv

include hv in
lemma fderiv_integral_spatialJet
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F)
    {t : ℝ} (ht : t∈Icc 0 T) (x : U) :
    fderiv ℝ (fun y => ∫ a, F (t,y,v a) ∂μ) x =
      ∫ a, (fderiv ℝ (fun z => F (t,z)) (x,v a)).comp (ContinuousLinearMap.inl ℝ U V) ∂μ := by
  rw [(hasFDerivAt_integral_smoothFamily μ (spatialJet_compactFamily hv n hF ht) x).fderiv]
  apply integral_congr_ae
  apply ae_of_all
  intro a
  have hi : HasFDerivAt (fun y : U => (y,v a)) (ContinuousLinearMap.inl ℝ U V) x := by
    convert ((hasFDerivAt_id (𝕜:=ℝ) x).prodMk (hasFDerivAt_const (v a) x)) using 1 <;> rfl
  exact (((hF.1 t ht).differentiable (by simp) (x,v a)).hasFDerivAt.comp x hi).fderiv

include hv hT in
lemma spatialJetRegular_integral_jet (j : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : ℝ × (U × V) → W}, SpatialJetRegular n (Icc 0 T) F →
      ContDiffOn ℝ n (fun p : ℝ × U =>
        iteratedFDeriv ℝ j (fun x => ∫ a, F (p.1,x,v a) ∂μ) p.2) {p | p.1∈Icc 0 T} := by
  induction j with
  | zero =>
    intro W _ _ _ F hF
    let C : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [C,iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      C.contDiff.comp_contDiffOn (contDiffOn_integral_spatialJet hv hT n hF)
  | succ j ih =>
    intro W _ _ _ F hF
    let G := fun p : ℝ × (U × V) =>
      (fderiv ℝ (fun z => F (p.1,z)) p.2).comp (ContinuousLinearMap.inl ℝ U V)
    have hG : SpatialJetRegular n (Icc 0 T) G := hF.deriv.clm_comp_const _
    let C : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    have hh := C.contDiff.comp_contDiffOn (ih hG)
    apply hh.congr
    intro p hp
    rw [iteratedFDeriv_succ_eq_comp_right,Function.comp_apply]
    change _=C _
    have he : fderiv ℝ (fun x => ∫ a, F (p.1,x,v a) ∂μ) =
        (fun x => ∫ a, G (p.1,x,v a) ∂μ) := by
      funext x; exact fderiv_integral_spatialJet hv n hF hp x
    rw [he]
    rfl

include hv hT in
lemma SpatialJetRegular.integral_compact
    {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℝ × (U × V) → W} (hF : SpatialJetRegular n (Icc 0 T) F) :
    SpatialJetRegular n (Icc 0 T) (fun p : ℝ × U => ∫ a, F (p.1,p.2,v a) ∂μ) := by
  refine ⟨fun t ht => contDiff_integral_smoothFamily μ (spatialJet_compactFamily hv n hF ht),?_⟩
  exact fun j => spatialJetRegular_integral_jet hv hT n j hF

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

universe u
variable {U W : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
  {J : Set ℝ} {F G : ℝ × U → W}

omit [ProperSpace U] [CompleteSpace W] in
lemma SpatialJetRegular.compactTimeFamily (hF : SpatialJetRegular 0 J F)
    {a b : ℝ} (hsub : Icc a b ⊆ J) :
    SmoothCompactFamily (fun t : Icc a b => fun x => F (t,x)) := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  refine ⟨fun t => hF.1 t (hsub t.property),fun j => ?_⟩
  exact (hF.2 j).continuousOn.comp_continuous
    ((continuous_subtype_val.comp continuous_snd).prodMk continuous_fst)
    (fun p => hsub p.2.property)

omit [CompleteSpace W] in
attribute [local instance] Measure.Subtype.measureSpace in
lemma SpatialJetRegular.hasFDerivAt_timeIntegral (hF : SpatialJetRegular 0 J F)
    {a b : ℝ} (hab : a≤b) (hsub : Icc a b ⊆ J) (x : U) :
    HasFDerivAt (fun y => ∫ r in a..b, F (r,y))
      (∫ r in a..b, fderiv ℝ (fun y => F (r,y)) x) x := by
  let : CompactSpace (Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  let : IsFiniteMeasure (volume : Measure (Icc a b)) := ⟨by
    rw [Measure.Subtype.volume_univ measurableSet_Icc.nullMeasurableSet]
    exact isCompact_Icc.measure_lt_top⟩
  have hh := hasFDerivAt_integral_smoothFamily (volume : Measure (Icc a b))
    (hF.compactTimeFamily hsub) x
  have he (y : U) : (∫ r : Icc a b, F ((r:ℝ),y)) = ∫ r in a..b, F (r,y) := by
    rw [integral_subtype measurableSet_Icc (fun r => F (r,y)),integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le hab]
  have he' : (∫ r : Icc a b, fderiv ℝ (fun y => F ((r:ℝ),y)) x) =
      ∫ r in a..b, fderiv ℝ (fun y => F (r,y)) x := by
    rw [integral_subtype measurableSet_Icc (fun r => fderiv ℝ (fun y => F (r,y)) x),
      integral_Icc_eq_integral_Ioc,intervalIntegral.integral_of_le hab]
  simpa only [he,he'] using hh

lemma space_time_derivative_slab {T : ℝ} (hT : 0<T)
    (hF : SpatialJetRegular 0 (Icc 0 T) F) (hG : SpatialJetRegular 0 (Icc 0 T) G)
    (htime : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t)
    {t : ℝ} (ht : t∈Icc 0 T) (x : U) :
    HasDerivWithinAt (fun r => fderiv ℝ (fun y => F (r,y)) x)
      (fderiv ℝ (fun y => G (t,y)) x) (Icc 0 T) t := by
  let DF := fun r => fderiv ℝ (fun y => F (r,y)) x
  let DG := fun r => fderiv ℝ (fun y => G (r,y)) x
  have hcG (y : U) : ContinuousOn (fun r => G (r,y)) (Icc 0 T) :=
    hG.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have hcF (y : U) : ContinuousOn (fun r => F (r,y)) (Icc 0 T) :=
    hF.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have hcDG : ContinuousOn DG (Icc 0 T) :=
    hG.deriv.regular.continuousOn.comp ((continuous_id.prodMk continuous_const).continuousOn) (fun _ hr => hr)
  have he (r : ℝ) (hr : r∈Icc 0 T) : DF r = DF 0+∫ u in 0..r, DG u := by
    have hsub : Icc 0 r ⊆ Icc 0 T := Icc_subset_Icc_right hr.2
    have hgi (y : U) : IntervalIntegrable (fun u => G (u,y)) volume 0 r :=
      ContinuousOn.intervalIntegrable_of_Icc hr.1 ((hcG y).mono hsub)
    have heq : (fun y => ∫ u in 0..r, G (u,y)) = (fun y => F (r,y)-F (0,y)) := by
      funext y
      apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hr.1 ((hcF y).mono hsub) _ (hgi y)
      intro u hu
      exact (htime u ⟨hu.1.le,hu.2.le.trans hr.2⟩ y).hasDerivAt
        (Icc_mem_nhds hu.1 (hu.2.trans_le hr.2))
    have hd := hG.hasFDerivAt_timeIntegral hr.1 hsub x
    rw [heq] at hd
    have hdf := (((hF.1 r hr).differentiable (by simp) x).hasFDerivAt.sub
      (((hF.1 0 ⟨le_rfl,hT.le⟩).differentiable (by simp) x).hasFDerivAt))
    have hh := hd.unique hdf
    change (∫ u in 0..r, DG u)=DF r-DF 0 at hh
    rw [hh]
    abel
  have hgi : IntervalIntegrable DG volume 0 t :=
    ContinuousOn.intervalIntegrable_of_Icc ht.1 (hcDG.mono (Icc_subset_Icc_right ht.2))
  let : Fact (t∈Icc (0:ℝ) T) := ⟨ht⟩
  have hd := intervalIntegral.integral_hasDerivWithinAt_right (s:=Icc 0 T) (t:=Icc 0 T) hgi
    (hcDG.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc t) (hcDG t ht)
  exact (hd.const_add (DF 0)).congr he (he t ht)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_WithinPartial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory Asymptotics
open scoped Topology ContDiff Convex

namespace RVM

lemma time_space_isLittleO_sub_sub_fderiv
    {α 𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [IsRCLikeNormedField 𝕜] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {u : E} {v w : α → E} {l : Filter α} (hv : Tendsto v l (𝓝 u)) (hw : Tendsto w l (𝓝 u))
    (s : Set E := Set.univ) (seg : ∀ᶠ χ in l, [w χ -[ℝ] v χ] ⊆ s := by simp)
    {f : α → E → F} {f' : α → E → E →L[𝕜] F}
    (df' : ∀ᶠ p in l ×ˢ 𝓝[s] u, HasFDerivWithinAt (f p.1) (f' p.1 p.2) s p.2)
    {φ : E →L[𝕜] F} (cf' : Tendsto ↿f' (l ×ˢ 𝓝[s] u) (𝓝 φ)) :
    (fun χ => f χ (v χ) - f χ (w χ) - φ (v χ - w χ)) =o[l] (fun χ => v χ - w χ) := by
  rw [isLittleO_iff]
  intro ε hε
  replace df' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], HasFDerivWithinAt (f χ) (f' χ z) s z :=
    df'.segment_of_prod_nhdsWithin hw hv seg
  replace cf' : ∀ᶠ χ in l, ∀ z ∈ [w χ -[ℝ] v χ], ‖f' χ z - φ‖ < ε := by
    simp_rw [Metric.tendsto_nhds, dist_eq_norm_sub] at cf'
    exact (cf' ε hε).segment_of_prod_nhdsWithin hw hv seg
  filter_upwards [seg, df', cf'] with χ seg df' cf'
  exact Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le'
    (fun z hz => (df' z hz).mono seg) (fun z hz => (cf' z hz).le)
    (convex_segment ..) (left_mem_segment ..) (right_mem_segment ..)

lemma hasFDerivWithinAt_of_time_space {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {J : Set ℝ} {F : ℝ × U → W} {D : ℝ × U → (U →L[ℝ] W)} {t : ℝ} {x : U} {g : W}
    (ht : t∈J) (hD : ∀ r∈J, ∀ y, HasFDerivAt (fun z => F (r,z)) (D (r,y)) y)
    (hcD : ContinuousOn D {p | p.1∈J})
    (hT : HasDerivWithinAt (fun r => F (r,x)) g J t) :
    HasFDerivWithinAt F (assembleDerivative g (D (t,x))) {p | p.1∈J} (t,x) := by
  let S : Set (ℝ × U) := {p | p.1∈J}
  let l := 𝓝[S] (t,x)
  have hq : Tendsto (fun p : ℝ × U => p) l (𝓝 (t,x)) := nhdsWithin_le_nhds
  have hqt : Tendsto (fun p : ℝ × U => p.1) l (𝓝 t) := continuous_fst.continuousAt.tendsto.comp hq
  have hqx : Tendsto (fun p : ℝ × U => p.2) l (𝓝 x) := continuous_snd.continuousAt.tendsto.comp hq
  have hqtJ : Tendsto (fun p : ℝ × U => p.1) l (𝓝[J] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hqt,by exact eventually_mem_nhdsWithin⟩
  have hp : Tendsto (fun q : (ℝ × U) × U => (q.1.1,q.2)) (l ×ˢ 𝓝 x) (𝓝[S] (t,x)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(hqt.comp tendsto_fst).prodMk_nhds tendsto_snd,?_⟩
    exact (eventually_mem_nhdsWithin : ∀ᶠ p in l, p∈S).prod_mk (Eventually.of_forall fun _ => True.intro) |>.mono (fun q h => h.1)
  have heS : (fun q : ℝ × U => F (q.1,q.2)-F (q.1,x)-(D (t,x)) (q.2-x)) =o[l] (fun q => q.2-x) := by
    apply time_space_isLittleO_sub_sub_fderiv (f:=fun q : ℝ × U => fun y => F (q.1,y))
      (f':=fun q : ℝ × U => fun y => D (q.1,y)) hqx tendsto_const_nhds
    · exact ((eventually_mem_nhdsWithin : ∀ᶠ p in l, p∈S).prod_mk (Eventually.of_forall fun _ => True.intro)).mono
        (fun q h => (hD q.1.1 h.1 q.2).hasFDerivWithinAt)
    · exact (hcD (t,x) ht).tendsto.comp (by simpa only [nhdsWithin_univ] using hp)
  have hbS : (fun q : ℝ × U => q.2-x) =O[l] (fun q => q-(t,x)) := by
    apply isBigO_of_le l
    intro q
    exact norm_snd_le (q-(t,x))
  have heT := hT.hasFDerivWithinAt.isLittleO.comp_tendsto hqtJ
  have hbT : (fun q : ℝ × U => q.1-t) =O[l] (fun q => q-(t,x)) := by
    apply isBigO_of_le l
    intro q
    exact norm_fst_le (q-(t,x))
  rw [hasFDerivWithinAt_iff_isLittleO]
  convert (heS.trans_isBigO hbS).add (heT.trans_isBigO hbT) using 1
  all_goals try with_reducible_and_instances rfl
  ext q
  change F q-F (t,x)-((q.1-t) • g+(D (t,x)) (q.2-x)) =
    (F (q.1,q.2)-F (q.1,x)-(D (t,x)) (q.2-x)) +
      (F (q.1,x)-F (t,x)-(q.1-t) • g)
  abel

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_SlabSmoothBootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u
variable {U : Type u} [NormedAddCommGroup U] [NormedSpace ℝ U] [ProperSpace U]

lemma iterated_spatial_time_derivative (j : ℕ) {T : ℝ} (hT : 0<T) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F G : ℝ × U → W}, SpatialJetRegular 0 (Icc 0 T) F → SpatialJetRegular 0 (Icc 0 T) G →
      (∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t) →
      ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt
        (fun r => iteratedFDeriv ℝ j (fun y => F (r,y)) x)
        (iteratedFDeriv ℝ j (fun y => G (t,y)) x) (Icc 0 T) t := by
  induction j with
  | zero =>
    intro W _ _ _ F G hF hG htime t ht x
    let A : W →L[ℝ] (U [×0]→L[ℝ] W) :=
      (continuousMultilinearCurryFin0 ℝ U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    simpa [A,iteratedFDeriv_zero_eq_comp,Function.comp_def] using
      A.hasFDerivAt.comp_hasDerivWithinAt t (htime t ht x)
  | succ j ih =>
    intro W _ _ _ F G hF hG htime t ht x
    have hdtime := fun (t : ℝ) (ht : t ∈ Icc 0 T) (x : U) => space_time_derivative_slab hT hF hG htime ht x
    have hd := ih hF.deriv hG.deriv hdtime t ht x
    let A : (U [×j]→L[ℝ] U →L[ℝ] W) →L[ℝ] (U [×(j+1)]→L[ℝ] W) :=
      (continuousMultilinearCurryRightEquiv' ℝ j U W).symm.toContinuousLinearEquiv.toContinuousLinearMap
    convert! A.hasFDerivAt.comp_hasDerivWithinAt t hd using 1 <;>
      simp only [A,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,
        LinearIsometryEquiv.coe_toContinuousLinearEquiv,ContinuousLinearEquiv.coe_coe]

omit [ProperSpace U] in
lemma contDiffOn_assembleDerivative {W X : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedAddCommGroup X] [NormedSpace ℝ X] {n : ℕ∞ω} {S : Set X}
    {G : X → W} {D : X → (U →L[ℝ] W)} (hG : ContDiffOn ℝ n G S) (hD : ContDiffOn ℝ n D S) :
    ContDiffOn ℝ n (fun p => assembleDerivative (G p) (D p)) S := by
  let A : W →L[ℝ] ((ℝ × U) →L[ℝ] W) :=
    ContinuousLinearMap.smulRightL ℝ (ℝ × U) W (ContinuousLinearMap.fst ℝ ℝ U)
  exact (A.contDiff.comp_contDiffOn hG).add (hD.clm_comp contDiffOn_const)

lemma spatialJetRegular_succ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F G : ℝ × U → W} {T : ℝ} (hT : 0<T) (n : ℕ)
    (hF : SpatialJetRegular n (Icc 0 T) F) (hG : SpatialJetRegular n (Icc 0 T) G)
    (htime : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (G (t,x)) (Icc 0 T) t) :
    SpatialJetRegular (n+1) (Icc 0 T) F := by
  have hu : UniqueDiffOn ℝ {p : ℝ × U | p.1∈Icc 0 T} := by
    have he : {p : ℝ × U | p.1∈Icc 0 T}=Icc 0 T ×ˢ (univ : Set U) := by ext p; simp
    rw [he]
    exact (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine ⟨hF.1,fun j => ?_⟩
  let Fj := fun p : ℝ × U => iteratedFDeriv ℝ j (fun y => F (p.1,y)) p.2
  let Gj := fun p : ℝ × U => iteratedFDeriv ℝ j (fun y => G (p.1,y)) p.2
  let Dj := fun p : ℝ × U => fderiv ℝ (fun y => Fj (p.1,y)) p.2
  have hFj : SpatialJetRegular n (Icc 0 T) Fj := spatialJetRegular_iterated j hF
  have hGj : ContDiffOn ℝ n Gj {p | p.1∈Icc 0 T} := hG.2 j
  have hDj : ContDiffOn ℝ n Dj {p | p.1∈Icc 0 T} := hFj.deriv.regular
  have htimej := iterated_spatial_time_derivative j hT
    (hF.mono_order (by simp)) (hG.mono_order (by simp)) htime
  have hd (p : ℝ × U) (hp : p.1∈Icc 0 T) : HasFDerivWithinAt Fj
      (assembleDerivative (Gj p) (Dj p)) {p | p.1∈Icc 0 T} p := by
    apply hasFDerivWithinAt_of_time_space hp _ hDj.continuousOn (htimej p.1 hp p.2)
    intro r hr y
    exact ((hFj.1 r hr).differentiable (by simp) y).hasFDerivAt
  have he (p : ℝ × U) (hp : p.1∈Icc 0 T) :
      fderivWithin ℝ Fj {p | p.1∈Icc 0 T} p=assembleDerivative (Gj p) (Dj p) :=
    (hd p hp).fderivWithin (hu p hp)
  have hn : ((n+1:ℕ∞):ℕ∞ω)=(n:ℕ∞ω)+1 := by simp
  rw [hn,contDiffOn_succ_iff_fderivWithin hu]
  refine ⟨fun p hp => (hd p hp).differentiableWithinAt,by simp,?_⟩
  exact (contDiffOn_assembleDerivative hGj hDj).congr he

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabRHS
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma spatialJetRegular_lorentz {n : ℕ∞} {J : Set ℝ} {E B : Field}
    (hE : SpatialJetRegular n J E) (hB : SpatialJetRegular n J B) :
    SpatialJetRegular n J (lorentzField E B) := by
  have hv : SpatialJetRegular n J (fun p : ℝ × Phase => velocity p.2.2) :=
    spatialJetRegular_fixed (contDiff_velocity.comp contDiff_snd)
  have he := hE.precomp (ContinuousLinearMap.fst ℝ Vec Vec)
  have hb := hB.precomp (ContinuousLinearMap.fst ℝ Vec Vec)
  exact hv.prodMk (he.add (hv.bilinear hb crossBilinearCLM))

lemma slabParticleRHS_regular {n : ℕ∞} {J : Set ℝ} {s : Solution}
    (hf : SpatialJetRegular n J s.f) (hE : SpatialJetRegular n J s.E) (hB : SpatialJetRegular n J s.B) :
    SpatialJetRegular n J (slabParticleRHS s) :=
  (hf.deriv.clm_apply (spatialJetRegular_lorentz hE hB)).neg

lemma slabMagneticRHS_regular {n : ℕ∞} {J : Set ℝ} {s : Solution}
    (hE : SpatialJetRegular n J s.E) : SpatialJetRegular n J (slabMagneticRHS s) :=
  (hE.deriv.clm curlMap).neg

lemma compact_particle_velocity_bound {T : ℝ} {s : Solution}
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    ∃ P : ℝ, 0<P ∧ ∀ t∈Icc 0 T, ∀ x v, P<‖v‖ → s.f (t,x,v)=0 := by
  obtain ⟨K,hK,hKf⟩ := hc
  obtain ⟨C,hC⟩ := hK.isBounded.exists_norm_le
  refine ⟨max C 1,lt_of_lt_of_le zero_lt_one (le_max_right _ _),?_⟩
  intro t ht x v hv
  by_contra hf
  have hb := hC (x,v) (hKf t ht (subset_tsupport _ hf))
  have hn : ‖v‖≤‖(x,v)‖ := by
    change ‖v‖ ≤ max ‖x‖ ‖v‖
    exact le_max_right _ _
  exact (not_lt_of_ge (hn.trans (hb.trans (le_max_left _ _)))) hv

attribute [local instance] Measure.Subtype.measureSpace in
lemma spatialJetRegular_current {T : ℝ} (hT : 0<T) (n : ℕ) {s : Solution}
    (hf : SpatialJetRegular n (Icc 0 T) s.f)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    SpatialJetRegular n (Icc 0 T) (fun p : ℝ × Vec => current (fun z => s.f (p.1,z)) p.2) := by
  obtain ⟨P,hP,hzero⟩ := compact_particle_velocity_bound hc
  let K := closedBall (0:Vec) P
  let : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let : IsFiniteMeasure (volume : Measure K) := ⟨by
    rw [Measure.Subtype.volume_univ isClosed_closedBall.measurableSet.nullMeasurableSet]
    exact (isCompact_closedBall (0:Vec) P).measure_lt_top⟩
  have hv : SpatialJetRegular n (Icc 0 T) (fun p : ℝ × Phase => velocity p.2.2) :=
    spatialJetRegular_fixed (contDiff_velocity.comp contDiff_snd)
  have hG := hf.bilinear hv (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] Vec →L[ℝ] Vec)
  have hi := hG.integral_compact (μ:=(volume : Measure K)) continuous_subtype_val hT n
  apply hi.congr
  intro p hp
  change current (fun z => s.f (p.1,z)) p.2=∫ a : K, s.f (p.1,p.2,(a:Vec)) • velocity a
  rw [integral_subtype (show MeasurableSet K from isClosed_closedBall.measurableSet)
    (f:=fun v : Vec => s.f (p.1,p.2,v) • velocity v)]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hv' : P<‖v‖ := by simpa only [K,mem_closedBall,dist_zero_right,not_le] using hv
  simp only [hzero p.1 hp p.2 v hv',zero_smul]

lemma slabElectricRHS_regular {T : ℝ} (hT : 0<T) (n : ℕ) {s : Solution}
    (hf : SpatialJetRegular n (Icc 0 T) s.f) (hB : SpatialJetRegular n (Icc 0 T) s.B)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K) :
    SpatialJetRegular n (Icc 0 T) (slabElectricRHS s) :=
  (hB.deriv.clm curlMap).sub (spatialJetRegular_current hT n hf hc)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_StrongLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma timePaste_left {U W : Type*} (T : ℝ) (F G : ℝ × U → W) {t : ℝ} (ht : t≤T) :
    (fun x => timePaste T F G (t,x))=(fun x => F (t,x)) := by
  funext x; simp [timePaste,ht]

lemma timePaste_right {U W : Type*} (T : ℝ) (F G : ℝ × U → W)
    (hjoin : ∀ x, F (T,x)=G (0,x)) {t : ℝ} (ht : T≤t) :
    (fun x => timePaste T F G (t,x))=(fun x => G (t-T,x)) := by
  funext x
  by_cases hh : t≤T
  · have he : t=T := le_antisymm hh ht
    subst t; simp [timePaste,hjoin]
  · simp [timePaste,hh]

lemma continuousOn_timePaste {U W : Type*} [TopologicalSpace U] [TopologicalSpace W]
    {T S : ℝ} (_ : 0≤T) (_ : 0≤S) {F G : ℝ × U → W}
    (hF : ContinuousOn F {p | p.1∈Icc 0 T}) (hG : ContinuousOn G {p | p.1∈Icc 0 S})
    (hjoin : ∀ x, F (T,x)=G (0,x)) :
    ContinuousOn (timePaste T F G) {p | p.1∈Icc 0 (T+S)} := by
  let A : Set (ℝ × U) := {p | p.1≤T}
  have hA : IsClosed A := isClosed_le continuous_fst continuous_const
  have hF' : ContinuousOn F ({p | p.1∈Icc 0 (T+S)}∩A) :=
    hF.mono (fun p hp => ⟨hp.1.1,hp.2⟩)
  have hG' : ContinuousOn (fun p : ℝ × U => G (p.1-T,p.2))
      ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) := by
    apply hG.comp ((continuous_fst.sub continuous_const).prodMk continuous_snd).continuousOn
    intro p hp
    change p.1-T∈Icc 0 S
    exact ⟨sub_nonneg.mpr hp.2,by linarith [hp.1.2]⟩
  have hleft : IsClosed ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩A) :=
    ((isClosed_Icc).preimage continuous_fst).inter hA
  have hright : IsClosed ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) :=
    ((isClosed_Icc).preimage continuous_fst).inter (isClosed_le continuous_const continuous_fst)
  have h1 : ContinuousOn (timePaste T F G) ({p | p.1∈Icc 0 (T+S)}∩A) :=
    hF'.congr (fun p hp => by change (if p.1≤T then F p else G (p.1-T,p.2))=F p; exact ite_eq_left hp.2)
  have h2 : ContinuousOn (timePaste T F G) ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1}) :=
    hG'.congr (fun p hp => congrFun (timePaste_right T F G hjoin hp.2) p.2)
  have hu := h1.union_of_isClosed h2 hleft hright
  have he : ({p : ℝ × U | p.1∈Icc 0 (T+S)}∩A)∪
      ({p | p.1∈Icc 0 (T+S)}∩{p | T≤p.1})={p | p.1∈Icc 0 (T+S)} := by
    ext p
    simp only [mem_union,mem_inter_iff,mem_ofPred_eq,A]
    exact ⟨fun h => h.elim And.left And.left,fun h => (le_total p.1 T).elim
      (fun hh => Or.inl ⟨h,hh⟩) (fun hh => Or.inr ⟨h,hh⟩)⟩
  rwa [he] at hu

lemma spatiallySmoothSlab_timePaste {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : ℝ × U → W} (hF : SpatiallySmoothSlab T F) (hG : SpatiallySmoothSlab S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : SpatiallySmoothSlab (T+S) (timePaste T F G) := by
  have he (t : ℝ) : (fun x => timePaste T F G (t,x))=
      if t≤T then (fun x => F (t,x)) else (fun x => G (t-T,x)) := by
    split_ifs <;> funext x <;> simp_all [timePaste]
  refine ⟨?_,?_⟩
  · intro t ht
    rw [he]
    split_ifs with hh
    · exact hF.1 t ⟨ht.1,hh⟩
    · exact hG.1 (t-T) ⟨by linarith,by linarith [ht.2]⟩
  · intro k
    have hj : ∀ x, iteratedFDeriv ℝ k (fun y => F (T,y)) x=
        iteratedFDeriv ℝ k (fun y => G (0,y)) x := by
      intro x; rw [show (fun y => F (T,y))=(fun y => G (0,y)) from funext hjoin]
    have hh := continuousOn_timePaste hT hS (hF.2 k) (hG.2 k) hj
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    funext p
    rw [he]
    simp only [timePaste]
    split_ifs <;> rfl

lemma boundedSpatiallySmoothSlab_timePaste {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : ℝ × U → W} (hF : BoundedSpatiallySmoothSlab T F) (hG : BoundedSpatiallySmoothSlab S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : BoundedSpatiallySmoothSlab (T+S) (timePaste T F G) := by
  refine ⟨spatiallySmoothSlab_timePaste hT hS hF.1 hG.1 hjoin,?_⟩
  intro k
  obtain ⟨A,hA,hAb⟩ := hF.2 k
  obtain ⟨B,hB,hBb⟩ := hG.2 k
  refine ⟨max A B,hA.trans (le_max_left _ _),?_⟩
  intro t ht x
  by_cases hh : t≤T
  · rw [timePaste_left T F G hh]
    exact (hAb t ⟨ht.1,hh⟩ x).trans (le_max_left _ _)
  · rw [timePaste_right T F G hjoin (le_of_not_ge hh)]
    exact (hBb (t-T) ⟨by linarith,by linarith [ht.2]⟩ x).trans (le_max_right _ _)

lemma hasDerivWithinAt_timePaste {U W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {T S : ℝ} (hT : 0≤T) (hS : 0≤S) {F G P Q : ℝ × U → W}
    (hF : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => F (r,x)) (P (t,x)) (Icc 0 T) t)
    (hG : ∀ t∈Icc 0 S, ∀ x, HasDerivWithinAt (fun r => G (r,x)) (Q (t,x)) (Icc 0 S) t)
    (hjoin : ∀ x, F (T,x)=G (0,x)) (hDjoin : ∀ x, P (T,x)=Q (0,x))
    {t : ℝ} (ht : t∈Icc 0 (T+S)) (x : U) :
    HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (t,x)) (Icc 0 (T+S)) t := by
  have hleft (u : ℝ) (hu : u∈Icc 0 T) :
      HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (u,x)) (Icc 0 T) u := by
    rw [congrFun (timePaste_left T P Q hu.2) x]
    exact (hF u hu x).congr (fun r hr => congrFun (timePaste_left T F G hr.2) x)
      (congrFun (timePaste_left T F G hu.2) x)
  have hright (u : ℝ) (hu : u∈Icc T (T+S)) :
      HasDerivWithinAt (fun r => timePaste T F G (r,x)) (timePaste T P Q (u,x)) (Icc T (T+S)) u := by
    have hv : u-T∈Icc 0 S := ⟨sub_nonneg.mpr hu.1,by linarith [hu.2]⟩
    have hh := (hG (u-T) hv x).scomp u ((hasDerivAt_id u).sub_const T).hasDerivWithinAt
      (show MapsTo (fun r => r-T) (Icc T (T+S)) (Icc 0 S) from
        fun r hr => ⟨sub_nonneg.mpr hr.1,by linarith [hr.2]⟩)
    simp only [one_smul] at hh
    rw [congrFun (timePaste_right T P Q hDjoin hu.1) x]
    exact hh.congr (fun r hr => congrFun (timePaste_right T F G hjoin hr.1) x)
      (congrFun (timePaste_right T F G hjoin hu.1) x)
  rcases lt_trichotomy t T with hlt|heq|hgt
  · apply (hleft t ⟨ht.1,hlt.le⟩).congr_set
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact propext ⟨fun h => ⟨h.1,by linarith [h.2]⟩,fun h => ⟨h.1,hr.le⟩⟩
  · subst t
    have hh := (hleft T ⟨hT,le_rfl⟩).union (hright T ⟨le_rfl,by linarith⟩)
    have he : Icc (0:ℝ) T∪Icc T (T+S)=Icc 0 (T+S) := by
      ext r
      simp only [mem_union,mem_Icc]
      constructor
      · rintro (hr|hr) <;> constructor <;> linarith [hr.1,hr.2]
      · intro hr
        exact (le_total r T).elim (fun h => Or.inl ⟨hr.1,h⟩) (fun h => Or.inr ⟨h,hr.2⟩)
    rwa [he] at hh
  · apply (hright t ⟨hgt.le,ht.2⟩).congr_set
    filter_upwards [Ioi_mem_nhds hgt] with r hr
    exact propext ⟨fun h => ⟨by linarith [h.1],h.2⟩,fun h => ⟨hr.le,h.2⟩⟩

lemma slabTimeContinuousL2_timePaste {T S : ℝ} (hT : 0≤T) (hS : 0≤S)
    {F G : Field} (hF : SlabTimeContinuousL2 T F) (hG : SlabTimeContinuousL2 S G)
    (hjoin : ∀ x, F (T,x)=G (0,x)) : SlabTimeContinuousL2 (T+S) (timePaste T F G) := by
  obtain ⟨F₂,hFc,hFe⟩ := hF
  obtain ⟨G₂,hGc,hGe⟩ := hG
  have hj : F₂ T=G₂ 0 := by
    apply Lp.ext
    filter_upwards [hFe T ⟨hT,le_rfl⟩,hGe 0 ⟨le_rfl,hS⟩] with x hf hg
    exact hf.trans ((hjoin x).trans hg.symm)
  let U := timePaste T (fun p : ℝ × Unit => F₂ p.1) (fun p => G₂ p.1)
  have hc : ContinuousOn U {p | p.1∈Icc 0 (T+S)} :=
    continuousOn_timePaste hT hS (hFc.comp continuous_fst.continuousOn (fun _ h => h))
      (hGc.comp continuous_fst.continuousOn (fun _ h => h)) (fun _ => hj)
  refine ⟨fun t => U (t,()),hc.comp (continuous_id.prodMk continuous_const).continuousOn (fun _ h => h),?_⟩
  intro t ht
  by_cases hh : t≤T
  · dsimp only [U,timePaste]
    simp only [hh,ite_true]
    exact hFe t ⟨ht.1,hh⟩
  · dsimp only [U,timePaste]
    simp only [hh,ite_false]
    exact hGe (t-T) ⟨by linarith,by linarith [ht.2]⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SlabEvolutionRegularity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma differentiableWithinAt_slab_time {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {F : ℝ × U → W} {T t : ℝ}
    (hF : ContDiffOn ℝ 1 F {p | p.1∈Icc 0 T}) (ht : t∈Icc 0 T) (x : U) :
    DifferentiableWithinAt ℝ (fun r => F (r,x)) (Icc 0 T) t := by
  exact (hF.differentiableOn (by norm_num) (t,x) ht).comp t
    ((differentiableAt_id.prodMk (differentiableAt_const x)).differentiableWithinAt)
    (fun r hr => hr)

lemma C1ClassicalPrefix.hasDerivWithinAt_particle {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hf : SpatiallySmoothSlab T s.f) {t : ℝ} (ht : t∈Icc 0 T) (z : Phase) :
    HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t := by
  have he := (heq t ht).1 z.1 z.2
  have hdiff := (hf.1 t ht).differentiable (by simp) z
  simp only [spatialPartial] at he
  rw [← clm_sum_basis,← clm_sum_basis,add_assoc,fderiv_phase_split hdiff] at he
  have hderiv := (differentiableWithinAt_slab_time hs.f_c1 ht z).hasDerivWithinAt
  have hv : derivWithin (fun r => s.f (r,z)) (Icc 0 T) t=slabParticleRHS s (t,z) := by
    change derivWithin (fun r => s.f (r,z)) (Icc 0 T) t =
      -(fderiv ℝ (fun w => s.f (t,w)) z) (lorentzField s.E s.B (t,z))
    exact eq_neg_of_add_eq_zero_left he
  rwa [hv] at hderiv

lemma C1ClassicalPrefix.hasDerivWithinAt_electric {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hB : SpatiallySmoothSlab T s.B) {t : ℝ} (ht : t∈Icc 0 T) (x : Vec) :
    HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t := by
  have he := (heq t ht).2.1 x
  rw [curl_eq_curlMap ((hB.1 t ht).differentiable (by simp))] at he
  have hderiv := (differentiableWithinAt_slab_time hs.E_c1 ht x).hasDerivWithinAt
  have hv : derivWithin (fun r => s.E (r,x)) (Icc 0 T) t=slabElectricRHS s (t,x) := by
    change _=curlMap (fderiv ℝ (fun y => s.B (t,y)) x)-current (fun z => s.f (t,z)) x
    rw [sub_eq_iff_eq_add] at he
    rw [he]; abel
  rwa [hv] at hderiv

lemma C1ClassicalPrefix.hasDerivWithinAt_magnetic {d : Datum} {s : Solution} {T : ℝ}
    (hs : C1ClassicalPrefix d s T) (heq : SlabEquations s T)
    (hE : SpatiallySmoothSlab T s.E) {t : ℝ} (ht : t∈Icc 0 T) (x : Vec) :
    HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t := by
  have he := (heq t ht).2.2.1 x
  rw [curl_eq_curlMap ((hE.1 t ht).differentiable (by simp))] at he
  have hderiv := (differentiableWithinAt_slab_time hs.B_c1 ht x).hasDerivWithinAt
  have hv : derivWithin (fun r => s.B (r,x)) (Icc 0 T) t=slabMagneticRHS s (t,x) :=
    eq_neg_of_add_eq_zero_left he
  rwa [hv] at hderiv

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma SmoothClassicalPrefix.toC1 {d : Datum} {s : Solution} {T : ℝ}
    (hs : SmoothClassicalPrefix d s T) : C1ClassicalPrefix d s T :=
  ⟨hs.f_smooth.of_le (by simp),hs.E_smooth.of_le (by simp),hs.B_smooth.of_le (by simp),
    hs.nonnegative,hs.E_L2,hs.B_L2,hs.compact,hs.equations,hs.initial_f,hs.initial_E,hs.initial_B⟩

lemma slabRHS_congr {s a : Solution} {t r : ℝ}
    (hf : (fun z => s.f (t,z))=(fun z => a.f (r,z)))
    (hE : (fun x => s.E (t,x))=(fun x => a.E (r,x)))
    (hB : (fun x => s.B (t,x))=(fun x => a.B (r,x))) :
    (∀ z, slabParticleRHS s (t,z)=slabParticleRHS a (r,z)) ∧
    (∀ x, slabElectricRHS s (t,x)=slabElectricRHS a (r,x)) ∧
    (∀ x, slabMagneticRHS s (t,x)=slabMagneticRHS a (r,x)) := by
  have hEv := congrFun hE
  have hBv := congrFun hB
  refine ⟨?_,?_,?_⟩
  · intro z
    simp only [slabParticleRHS,lorentzField,hf,hEv,hBv]
  · intro x
    simp only [slabElectricRHS,hf,hB]
  · intro x
    simp only [slabMagneticRHS,hE]

lemma pasteSolution_rhs (T : ℝ) (s a : Solution) :
    slabParticleRHS (pasteSolution T s a)=timePaste T (slabParticleRHS s) (slabParticleRHS a) ∧
    slabElectricRHS (pasteSolution T s a)=timePaste T (slabElectricRHS s) (slabElectricRHS a) ∧
    slabMagneticRHS (pasteSolution T s a)=timePaste T (slabMagneticRHS s) (slabMagneticRHS a) := by
  have hh (t : ℝ) :
      (∀ z, slabParticleRHS (pasteSolution T s a) (t,z)=timePaste T (slabParticleRHS s) (slabParticleRHS a) (t,z)) ∧
      (∀ x, slabElectricRHS (pasteSolution T s a) (t,x)=timePaste T (slabElectricRHS s) (slabElectricRHS a) (t,x)) ∧
      (∀ x, slabMagneticRHS (pasteSolution T s a) (t,x)=timePaste T (slabMagneticRHS s) (slabMagneticRHS a) (t,x)) := by
    by_cases ht : t≤T
    · have he := slabRHS_congr (s:=pasteSolution T s a) (a:=s)
        (timePaste_left T s.f a.f ht) (timePaste_left T s.E a.E ht) (timePaste_left T s.B a.B ht)
      simpa only [timePaste,ht,ite_true] using he
    · have hf : (fun z => (pasteSolution T s a).f (t,z))=(fun z => a.f (t-T,z)) := by
        funext z; simp [pasteSolution,timePaste,ht]
      have hE : (fun x => (pasteSolution T s a).E (t,x))=(fun x => a.E (t-T,x)) := by
        funext x; simp [pasteSolution,timePaste,ht]
      have hB : (fun x => (pasteSolution T s a).B (t,x))=(fun x => a.B (t-T,x)) := by
        funext x; simp [pasteSolution,timePaste,ht]
      simpa only [timePaste,ht,ite_false] using slabRHS_congr hf hE hB
  exact ⟨funext fun p => (hh p.1).1 p.2,funext fun p => (hh p.1).2.1 p.2,
    funext fun p => (hh p.1).2.2 p.2⟩

lemma spatiallySmooth_time_derivatives_smooth {s : Solution} {T : ℝ} (hT : 0<T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => s.f (t,z)) ⊆ K)
    (hft : ∀ t∈Icc 0 T, ∀ z, HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t)
    (hEt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t)
    (hBt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t) :
    ContDiffOn ℝ ∞ s.f (particleSlab T) ∧ ContDiffOn ℝ ∞ s.E (fieldSlab T) ∧
      ContDiffOn ℝ ∞ s.B (fieldSlab T) := by
  have hh (n : ℕ) : SpatialJetRegular n (Icc 0 T) s.f ∧
      SpatialJetRegular n (Icc 0 T) s.E ∧ SpatialJetRegular n (Icc 0 T) s.B := by
    induction n with
    | zero => exact ⟨hf.spatialJetRegular,hE.spatialJetRegular,hB.spatialJetRegular⟩
    | succ n ih =>
      exact ⟨spatialJetRegular_succ hT n ih.1 (slabParticleRHS_regular ih.1 ih.2.1 ih.2.2) hft,
        spatialJetRegular_succ hT n ih.2.1 (slabElectricRHS_regular hT n ih.1 ih.2.2 hc) hEt,
        spatialJetRegular_succ hT n ih.2.2 (slabMagneticRHS_regular ih.2.1) hBt⟩
  refine ⟨?_,?_,?_⟩ <;> rw [contDiffOn_infty]
  · exact fun n => (hh n).1.regular
  · exact fun n => (hh n).2.1.regular
  · exact fun n => (hh n).2.2.regular

lemma slabEquations_of_time_derivatives {s : Solution} {T : ℝ} (hT : 0<T)
    (hf : SpatiallySmoothSlab T s.f) (hE : SpatiallySmoothSlab T s.E) (hB : SpatiallySmoothSlab T s.B)
    (hft : ∀ t∈Icc 0 T, ∀ z, HasDerivWithinAt (fun r => s.f (r,z)) (slabParticleRHS s (t,z)) (Icc 0 T) t)
    (hEt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.E (r,x)) (slabElectricRHS s (t,x)) (Icc 0 T) t)
    (hBt : ∀ t∈Icc 0 T, ∀ x, HasDerivWithinAt (fun r => s.B (r,x)) (slabMagneticRHS s (t,x)) (Icc 0 T) t)
    (hgauss : ∀ t∈Icc 0 T, (∀ x, divergence (fun y => s.E (t,y)) x=rho (fun z => s.f (t,z)) x) ∧
      (∀ x, divergence (fun y => s.B (t,y)) x=0)) : SlabEquations s T := by
  intro t ht
  refine ⟨?_,?_,?_,(hgauss t ht).1,(hgauss t ht).2⟩
  · intro x v
    rw [(hft t ht (x,v)).derivWithin (uniqueDiffOn_Icc hT t ht)]
    simp only [spatialPartial]
    rw [←clm_sum_basis,←clm_sum_basis,add_assoc,fderiv_phase_split ((hf.1 t ht).differentiable (by simp) (x,v))]
    exact neg_add_cancel _
  · intro x
    rw [(hEt t ht x).derivWithin (uniqueDiffOn_Icc hT t ht),
      curl_eq_curlMap ((hB.1 t ht).differentiable (by simp))]
    dsimp only [slabElectricRHS]; abel
  · intro x
    rw [(hBt t ht x).derivWithin (uniqueDiffOn_Icc hT t ht),
      curl_eq_curlMap ((hE.1 t ht).differentiable (by simp))]
    exact neg_add_cancel _

lemma BoundedClassicalPrefix.paste_oai {d : Datum} {s a : Solution} {T S : ℝ}
    (hT : 0<T) (hS : 0<S) (hs : BoundedClassicalPrefix d s T)
    (ha : BoundedClassicalPrefix (timeSliceDatum s T) a S) :
    BoundedClassicalPrefix d (pasteSolution T s a) (T+S) := by
  have hjf (z : Phase) : s.f (T,z)=a.f (0,z) := (ha.classical.initial_f z).symm
  have hjE (x : Vec) : s.E (T,x)=a.E (0,x) := (ha.classical.initial_E x).symm
  have hjB (x : Vec) : s.B (T,x)=a.B (0,x) := (ha.classical.initial_B x).symm
  have hf := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.f_jets ha.f_jets hjf
  have hE := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.E_jets ha.E_jets hjE
  have hB := boundedSpatiallySmoothSlab_timePaste hT.le hS.le hs.B_jets ha.B_jets hjB
  have hjR := slabRHS_congr (funext hjf) (funext hjE) (funext hjB)
  have hR := pasteSolution_rhs T s a
  have hft (t : ℝ) (ht : t∈Icc 0 (T+S)) (z : Phase) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).f (r,z))
        (slabParticleRHS (pasteSolution T s a) (t,z)) (Icc 0 (T+S)) t := by
    rw [hR.1]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu w => hs.classical.toC1.hasDerivWithinAt_particle hs.closed_equations hs.f_jets.1 hu w)
      (fun u hu w => ha.classical.toC1.hasDerivWithinAt_particle ha.closed_equations ha.f_jets.1 hu w)
      hjf hjR.1 ht z
  have hEt (t : ℝ) (ht : t∈Icc 0 (T+S)) (x : Vec) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).E (r,x))
        (slabElectricRHS (pasteSolution T s a) (t,x)) (Icc 0 (T+S)) t := by
    rw [hR.2.1]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu y => hs.classical.toC1.hasDerivWithinAt_electric hs.closed_equations hs.B_jets.1 hu y)
      (fun u hu y => ha.classical.toC1.hasDerivWithinAt_electric ha.closed_equations ha.B_jets.1 hu y)
      hjE hjR.2.1 ht x
  have hBt (t : ℝ) (ht : t∈Icc 0 (T+S)) (x : Vec) :
      HasDerivWithinAt (fun r => (pasteSolution T s a).B (r,x))
        (slabMagneticRHS (pasteSolution T s a) (t,x)) (Icc 0 (T+S)) t := by
    rw [hR.2.2]
    exact hasDerivWithinAt_timePaste hT.le hS.le
      (fun u hu y => hs.classical.toC1.hasDerivWithinAt_magnetic hs.closed_equations hs.E_jets.1 hu y)
      (fun u hu y => ha.classical.toC1.hasDerivWithinAt_magnetic ha.closed_equations ha.E_jets.1 hu y)
      hjB hjR.2.2 ht x
  have hc : ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 (T+S),
      tsupport (fun z => (pasteSolution T s a).f (t,z)) ⊆ K := by
    obtain ⟨K,hK,hKb⟩ := hs.classical.compact
    obtain ⟨L,hL,hLb⟩ := ha.classical.compact
    refine ⟨K∪L,hK.union hL,?_⟩
    intro t ht
    change tsupport (fun z => timePaste T s.f a.f (t,z)) ⊆ K∪L
    by_cases hh : t≤T
    · rw [timePaste_left T s.f a.f hh]
      exact (hKb t ⟨ht.1,hh⟩).trans subset_union_left
    · rw [timePaste_right T s.f a.f hjf (le_of_not_ge hh)]
      exact (hLb (t-T) ⟨by linarith,by linarith [ht.2]⟩).trans subset_union_right
  have heq : SlabEquations (pasteSolution T s a) (T+S) := by
    apply slabEquations_of_time_derivatives (add_pos hT hS) hf.1 hE.1 hB.1 hft hEt hBt
    intro t ht
    change (∀ x, divergence (fun y => timePaste T s.E a.E (t,y)) x=
      rho (fun z => timePaste T s.f a.f (t,z)) x) ∧
      (∀ x, divergence (fun y => timePaste T s.B a.B (t,y)) x=0)
    by_cases hh : t≤T
    · rw [timePaste_left T s.E a.E hh,timePaste_left T s.f a.f hh,timePaste_left T s.B a.B hh]
      exact ⟨(hs.closed_equations t ⟨ht.1,hh⟩).2.2.2.1,(hs.closed_equations t ⟨ht.1,hh⟩).2.2.2.2⟩
    · rw [timePaste_right T s.E a.E hjE (le_of_not_ge hh),timePaste_right T s.f a.f hjf (le_of_not_ge hh),
        timePaste_right T s.B a.B hjB (le_of_not_ge hh)]
      have hu : t-T∈Icc 0 S := ⟨by linarith,by linarith [ht.2]⟩
      exact ⟨(ha.closed_equations (t-T) hu).2.2.2.1,(ha.closed_equations (t-T) hu).2.2.2.2⟩
  obtain ⟨hfs,hEs,hBs⟩ := spatiallySmooth_time_derivatives_smooth (add_pos hT hS)
    hf.1 hE.1 hB.1 hc hft hEt hBt
  refine ⟨⟨hfs,hEs,hBs,?_,slabTimeContinuousL2_timePaste hT.le hS.le hs.classical.E_L2 ha.classical.E_L2 hjE,
    slabTimeContinuousL2_timePaste hT.le hS.le hs.classical.B_L2 ha.classical.B_L2 hjB,hc,heq.equationsBefore,?_,?_,?_⟩,
    heq,hf,hE,hB⟩
  · intro t ht z
    change 0≤timePaste T s.f a.f (t,z)
    by_cases hh : t≤T
    · rw [congrFun (timePaste_left T s.f a.f hh) z]
      exact hs.classical.nonnegative t ⟨ht.1,hh⟩ z
    · rw [congrFun (timePaste_right T s.f a.f hjf (le_of_not_ge hh)) z]
      exact ha.classical.nonnegative (t-T) ⟨by linarith,by linarith [ht.2]⟩ z
  · intro z; exact (congrFun (timePaste_left T s.f a.f hT.le) z).trans (hs.classical.initial_f z)
  · intro x; exact (congrFun (timePaste_left T s.E a.E hT.le) x).trans (hs.classical.initial_E x)
  · intro x; exact (congrFun (timePaste_left T s.B a.B hT.le) x).trans (hs.classical.initial_B x)

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.BoundedClassicalPrefix.paste_oai := @OAI.RVM.BoundedClassicalPrefix.paste_oai
