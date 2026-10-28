-- Prove2me | solution 1 for OAI.EuclideanFiveColor.triangle_boundary_one_orbit
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:13:32.455786+00:00
-- url     : https://prove2.me/submissions/0fd60edf-47a0-4bad-8005-fbef06ff95fe

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_triangleState_flip
import Theorems.Thm_OAI_EuclideanFiveColor_triangleState_local

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
lemma ae_density_actual {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) :
    ∀ᵐ x ∂(volume : Measure ℂ), DensityOne {z | c z=c x} x := by
  have hh : ∀ᵐ x ∂(volume : Measure ℂ), ∀ i : Fin k,
      Tendsto (fun r : ℝ => volume ({z | c z=i} ∩ Metric.closedBall x r) / volume (Metric.closedBall x r))
        (𝓝[>] 0) (𝓝 (({z | c z=i} : Set ℂ).indicator (1 : ℂ → ENNReal) x)) :=
    ae_all_iff.mpr fun i => Besicovitch.ae_tendsto_measure_inter_div_of_measurableSet volume
      (measurableSet_eq_fun hc measurable_const)
  filter_upwards [hh] with x hx
  simpa only [DensityOne,Set.indicator_of_mem (show x ∈ {z | c z=c x} from rfl),Pi.one_apply] using hx (c x)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Compactness
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsFiniteMeasure μ]
lemma oneL2_ae : oneL2 μ =ᵐ[μ] (fun _ => (1 : ℝ)) := by
  simpa only [oneL2,Set.indicator_univ] using (indicatorConstLp_coeFn (p := 2) (hs := MeasurableSet.univ)
    (hμs := measure_ne_top μ Set.univ) (c := (1 : ℝ)))
lemma weak_limit_nonneg {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, 0 ≤ᵐ[μ] f n) : 0 ≤ᵐ[μ] b := by
  apply ae_nonneg_of_forall_setIntegral_nonneg (MemLp.integrable (by norm_num) (Lp.memLp b))
  intro s hs hμs
  have h := ht (indicatorConstLp 2 hs hμs.ne 1)
  have he (v : RealL2 μ) : ⟪v,indicatorConstLp 2 hs hμs.ne 1⟫ = ∫ x in s, v x ∂μ := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp_rw [he] at h
  exact ge_of_tendsto h (Eventually.of_forall fun n => integral_nonneg_of_ae (ae_restrict_of_ae (hf n)))
lemma weak_limit_le_one {f : ℕ → RealL2 μ} {b : RealL2 μ}
    (ht : ∀ v, Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hf : ∀ n, f n ≤ᵐ[μ] (fun _ => (1 : ℝ))) : b ≤ᵐ[μ] (fun _ => (1 : ℝ)) := by
  have hh : 0 ≤ᵐ[μ] (oneL2 μ-b) := weak_limit_nonneg μ
    (f := fun n => oneL2 μ-f n) (fun v => by simpa only [inner_sub_left] using tendsto_const_nhds.sub (ht v)) (fun n => by
      filter_upwards [Lp.coeFn_sub (oneL2 μ) (f n),oneL2_ae μ,hf n] with x hx h1 hn
      simpa only [hx,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hn)
  filter_upwards [hh,Lp.coeFn_sub (oneL2 μ) b,oneL2_ae μ] with x hx he h1
  simpa only [he,Pi.sub_apply,Pi.zero_apply,h1,sub_nonneg] using hx
lemma weak_limit_sum {ι : Type*} [Fintype ι] {f : ℕ → ι → RealL2 μ} {b : ι → RealL2 μ}
    (ht : ∀ i v, Tendsto (fun n => ⟪f n i,v⟫) atTop (𝓝 ⟪b i,v⟫))
    (hf : ∀ n, ∑ i, f n i = oneL2 μ) : ∑ i, b i = oneL2 μ := by
  apply ext_inner_right ℝ
  intro v
  have hh := tendsto_finsetSum Finset.univ (fun i _ => ht i v)
  simp_rw [← sum_inner,hf] at hh
  exact tendsto_nhds_unique hh tendsto_const_nhds
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma ae_typicalSampling (hc : Measurable c) {r : ℝ} (hr : 0 < r) :
    ∀ᵐ y ∂(volume : Measure ℂ), TypicalSampling c y r := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  have hh : ∀ᵐ p ∂((volume : Measure ℂ).prod angularMeasure), Typical c (p.1+(r : ℂ)*direction p.2) :=
    hq.ae (ae_density_actual c hc)
  exact (Measure.ae_ae_of_ae_prod hh).mono fun y hy => ⟨hr,hy⟩
lemma sample_sum (hc : Measurable c) (y : ℂ) (r : ℝ) :
    ∑ i, sample c hc y r i = oneL2 angularMeasure := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i => sample c hc y r i),
    ae_all_iff.mpr (sample_ae c hc y r),oneL2_ae angularMeasure] with t ht ha h1
  rw [ht,h1]
  simp only [ha,sampleFn]
  simp
end EuclideanFiveColor
end

noncomputable section
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor.WeakBall
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
omit [TopologicalSpace.SeparableSpace E] in
lemma value_eval (a : Space E) (v : E) : ⟪value E a,v⟫ = a.1 v := by
  simp only [value,InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply]
omit [TopologicalSpace.SeparableSpace E] in
lemma tendsto_iff {I : Type*} {l : Filter I} {f : I → Space E} {b : Space E} :
    Tendsto f l (𝓝 b) ↔ ∀ v : E, Tendsto (fun n => ⟪value E (f n),v⟫) l (𝓝 ⟪value E b,v⟫) := by
  simp only [value_eval]
  rw [tendsto_subtype_rng, tendsto_iff_forall_eval_tendsto_topDualPairing]
  rfl
end EuclideanFiveColor.WeakBall
end

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma trace_realization {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    ∃ y : ℕ → ℂ, ∃ r : ℕ → ℝ, (∀ n, TypicalSampling c (y n) (r n)) ∧
      Tendsto y atTop (𝓝 x) ∧ Tendsto r atTop (𝓝 1) ∧
      Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b) := by
  obtain ⟨p,hp,ht⟩ := mem_closure_iff_seq_limit.mp hb
  simp only [nhds_prod_eq] at ht
  refine ⟨fun n => (p n).1,fun n => (p n).2.1,fun n => (hp n).1,ht.fst,ht.snd.fst,?_⟩
  simpa only [show (fun n => (p n).2.2) = (fun n => sampleCode c hc (p n).1 (p n).2.1) from
    funext fun n => (hp n).2] using ht.snd.snd
lemma trace_of_realization {x : ℂ} {b : TraceVector k} {y : ℕ → ℂ} {r : ℕ → ℝ}
    (htr : ∀ n, TypicalSampling c (y n) (r n)) (hy : Tendsto y atTop (𝓝 x))
    (hr : Tendsto r atTop (𝓝 1))
    (hb : Tendsto (fun n => sampleCode c hc (y n) (r n)) atTop (𝓝 b)) : IsTrace c hc x b := by
  exact mem_closure_of_tendsto (hy.prodMk_nhds (hr.prodMk_nhds hb))
    (Eventually.of_forall fun n => show (y n,r n,sampleCode c hc (y n) (r n)) ∈ sampleSet c hc from ⟨htr n,rfl⟩)
lemma traceCode_tendsto_iff {I : Type*} {l : Filter I} {f : I → TraceVector k} {b : TraceVector k} :
    Tendsto f l (𝓝 b) ↔ ∀ i v, Tendsto (fun n => ⟪traceValue (f n) i,v⟫) l (𝓝 ⟪traceValue b i,v⟫) := by
  rw [tendsto_pi_nhds]
  exact forall_congr' fun i => WeakBall.tendsto_iff _
lemma trace_bounds {x : ℂ} {b : TraceVector k} (hb : IsTrace c hc x b) :
    (∀ i, 0 ≤ᵐ[angularMeasure] traceValue b i) ∧
    (∀ i, traceValue b i ≤ᵐ[angularMeasure] (fun _ => (1 : ℝ))) ∧
    ∑ i, traceValue b i = oneL2 angularMeasure := by
  obtain ⟨y,r,_,_,_,ht⟩ := trace_realization c hc hb
  have hw := traceCode_tendsto_iff.mp ht
  simp only [traceValue_sampleCode] at hw
  refine ⟨?_,?_,?_⟩
  · intro i
    apply weak_limit_nonneg angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he,Pi.zero_apply] using sampleFn_nonneg c (y n) (r n) i t
  · intro i
    apply weak_limit_le_one angularMeasure (hw i)
    intro n
    filter_upwards [sample_ae c hc (y n) (r n) i] with t he
    simpa only [he] using sampleFn_le_one c (y n) (r n) i t
  · exact weak_limit_sum angularMeasure hw (fun n => sample_sum c hc (y n) (r n))
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Palettes
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma tracePositive_le_palette (x : ℂ) (i : Fin k) (b : Traces c hc x) :
    tracePositive c hc x i b ≤ᵐ[angularMeasure] paletteSet c hc x i :=
  (exists_countable_essential_union angularMeasure (tracePositive c hc x i) (tracePositive_measurable c hc x i)).choose_spec.2 b
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteTransport
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma ae_of_locally_ae {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] (μ : Measure X) {S : Set X} {P : X → Prop}
    (h : ∀x∈S,∃U : Set X,IsOpen U ∧ x∈U ∧ ∀ᵐy∂μ,y∈U → P y) :
    ∀ᵐx∂μ,x∈S → P x := by
  choose U ho hm ha using fun x : S => h x x.2
  obtain ⟨T,hT,hcov⟩ := (HereditarilyLindelofSpace.isLindelof S).elim_countable_subcover U ho
    (by intro x hx; exact mem_iUnion.mpr ⟨⟨x,hx⟩,hm ⟨x,hx⟩⟩)
  have hh : ∀ᵐy∂μ,∀x∈T,y∈U x → P y := (ae_ball_iff hT).mpr (fun x _ => ha x)
  filter_upwards [hh] with y hy hs
  obtain ⟨x,hx,hyU⟩ := mem_iUnion₂.mp (hcov hs)
  exact hy x hx hyU
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_States
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma complex_unit_orthogonal {e v : ℂ} (he : ‖e‖=1) (hv : ‖v‖=1) (h : ⟪e,v⟫=0) :
    e=Complex.I*v ∨ e= -Complex.I*v := by
  have hr : (e*star v).re=0 := by
    rw [real_inner_comm,Complex.inner] at h
    exact h
  have hn : ‖e*star v‖=1 := by rw [norm_mul,norm_star,he,hv,one_mul]
  have hs : (e*star v).im^2=1 := by
    have hh := Complex.normSq_eq_norm_sq (e*star v)
    rw [hn] at hh
    simp only [Complex.normSq_apply,hr,zero_mul,zero_add,one_pow] at hh
    nlinarith
  have him : (e*star v).im=1 ∨ (e*star v).im= -1 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.mp (by simpa only [one_pow] using hs)
  have hmul : star v*v=1 := by
    change (starRingEnd ℂ) v*v=1
    rw [Complex.conj_mul']
    simp only [hv,one_pow,Complex.ofReal_one]
  rcases him with him|him
  · left
    have hz : e*star v=Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = Complex.I*v := congrArg (·*v) hz
  · right
    have hz : e*star v= -Complex.I := Complex.ext (by simpa using hr) (by simpa using him)
    calc e = (e*star v)*v := by rw [mul_assoc,hmul,mul_one]
         _ = -Complex.I*v := congrArg (·*v) hz
lemma ae_direction_nonorthogonal {v : ℂ} (hv : ‖v‖=1) :
    ∀ᵐt∂angularMeasure,⟪direction t,v⟫≠0 := by
  have hd : Function.Injective direction := fun _ _ h =>
    AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) (Subtype.ext h)
  have hf : {t | ⟪direction t,v⟫=0}.Finite := by
    apply ((Set.toFinite {Complex.I*v,-Complex.I*v}).preimage (f := direction) hd.injOn).subset
    intro t ht
    rcases complex_unit_orthogonal (direction_norm t) hv ht with ht|ht <;> simp [ht]
  exact measure_eq_zero_iff_ae_notMem.mp (hf.measure_zero angularMeasure)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_BoundaryTrace
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory MeasureTheory.Measure
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma sample_region_ae (r : ℝ) {W : Set ℂ} {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) :
    ∀ᵐy : ℂ∂volume,∀ᵐt∂angularMeasure,y+(r : ℂ)*direction t∈W →
      c (y+(r : ℂ)*direction t)∈J := by
  have hq : QuasiMeasurePreserving (fun p : ℂ × Angles => p.1+(r : ℂ)*direction p.2)
      ((volume : Measure ℂ).prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (measurable_const.mul (direction_continuous.measurable.comp measurable_snd)))
      (Eventually.of_forall fun t => (measurePreserving_add_right (volume : Measure ℂ)
        ((r : ℂ)*direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hW)
include hc in
lemma sampling_near_region {x : ℂ} {r : ℝ} (hr : 0 < r) {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hmem : ∀t∈K,x+(r : ℂ)*direction t∈W) {δ : ℝ} (hδ : 0<δ) :
    ∃y : ℂ,dist y x<δ ∧ TypicalSampling c y r ∧
      ∀ᵐt∂angularMeasure,t∈K → c (y+(r : ℂ)*direction t)∈J := by
  let U : Set (ℂ × Angles) := {p | p.1+(r : ℂ)*direction p.2∈W}
  have hU : IsOpen U := ho.preimage (continuous_fst.add (continuous_const.mul (direction_continuous.comp continuous_snd)))
  obtain ⟨V,T,hV,_,hxV,hKT,hVT⟩ := generalized_tube_lemma (isCompact_singleton (x := x)) hK hU
    (by rintro ⟨y,t⟩ ⟨hy,ht⟩; change y=x at hy; subst y; exact hmem t ht)
  have hv : x∈V := hxV (mem_singleton x)
  have hpos : 0<volume (V∩Metric.ball x δ) := (hV.inter Metric.isOpen_ball).measure_pos volume
    ⟨x,hv,Metric.mem_ball_self hδ⟩
  obtain ⟨y,hy,hyp,hyW⟩ := ((frequently_ae_mem_iff.mpr hpos.ne').and_eventually
    ((ae_typicalSampling c hc hr).and (sample_region_ae c r hW))).exists
  refine ⟨y,hy.2,hyp,hyW.mono fun t ht htK => ht ?_⟩
  exact hVT (show (y,t)∈V×ˢT from ⟨hy.1,hKT htK⟩)
lemma weak_limit_zero_on {f : ℕ → RealL2 angularMeasure} {b : RealL2 angularMeasure}
    {K : Set Angles} (hK : MeasurableSet K)
    (ht : ∀v,Tendsto (fun n => ⟪f n,v⟫) atTop (𝓝 ⟪b,v⟫))
    (hb : 0≤ᵐ[angularMeasure] b)
    (hf : ∀n,∀ᵐt∂angularMeasure,t∈K → f n t=0) :
    ∀ᵐt∂angularMeasure,t∈K → b t=0 := by
  have ht' := ht (indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1)
  have he (v : RealL2 angularMeasure) :
      ⟪v,indicatorConstLp 2 hK (measure_ne_top angularMeasure K) 1⟫=∫t in K,v t∂angularMeasure := by
    rw [real_inner_comm,L2.inner_indicatorConstLp_one]
  simp only [he] at ht'
  have hf0 (n) : ∫t in K,f n t∂angularMeasure=0 := by
    apply integral_eq_zero_of_ae
    exact (ae_restrict_iff' hK).mpr (hf n)
  simp only [hf0] at ht'
  have hzero : ∫t in K,b t∂angularMeasure=0 := (tendsto_nhds_unique tendsto_const_nhds ht').symm
  have hz := (integral_eq_zero_iff_of_nonneg_ae (ae_restrict_of_ae hb)
    ((Lp.memLp b).integrable (by norm_num)).integrableOn).mp hzero
  exact (ae_restrict_iff' hK).mp hz
lemma trace_region_palette {x : ℂ} {K : Set Angles} (hK : IsCompact K)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J) {r : ℕ → ℝ}
    (hr : ∀n,0 < r n) (hrt : Tendsto r atTop (𝓝 1))
    (hmem : ∀n,∀t∈K,x+(r n : ℂ)*direction t∈W) :
    ∀ᵐt∂angularMeasure,t∈K → (palette c hc x t∩J).Nonempty := by
  have hex (n : ℕ) := sampling_near_region c hc (hr n) hK ho hW (hmem n)
    (δ := 1/((n:ℝ)+1)) (by positivity)
  choose y hy hyt hyJ using hex
  have hyl : Tendsto y atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hy n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (y n) (r n))))
  have htrace := trace_of_realization c hc (fun n => hyt (φ n)) (hyl.comp hφ.tendsto_atTop)
    (hrt.comp hφ.tendsto_atTop) hb
  have hz (i : Fin k) (hi : i∉J) : ∀ᵐt∂angularMeasure,t∈K → traceValue b i t=0 := by
    apply weak_limit_zero_on hK.measurableSet
      (by simpa only [traceValue_sampleCode] using traceCode_tendsto_iff.mp hb i)
      ((trace_bounds c hc htrace).1 i)
    intro n
    filter_upwards [hyJ (φ n),sample_ae c hc (y (φ n)) (r (φ n)) i] with t ht he htK
    simp only [Function.comp_apply,traceValue_sampleCode]
    rw [he]
    unfold sampleFn
    split_ifs with htcol
    · exact (hi (htcol ▸ ht htK)).elim
    · rfl
  have hs : (fun t => ∑i,traceValue b i t)=ᵐ[angularMeasure](fun _ => (1:ℝ)) := by
    have hh := Lp.coeFn_fun_finsetSum Finset.univ (traceValue b)
    rw [(trace_bounds c hc htrace).2.2] at hh
    exact hh.symm.trans (oneL2_ae angularMeasure)
  filter_upwards [hs,ae_all_iff.mpr (fun i => ae_all_iff.mpr (hz i)),
    ae_all_iff.mpr (fun i => tracePositive_le_palette c hc x i ⟨b,htrace⟩)] with t hs hz hp htK
  by_contra! hn
  have hn' : ∀i,traceValue b i t≤0 := by
    intro i
    by_contra! hpos
    have hi : i∈palette c hc x t := (mem_palette c hc x t i).mpr (hp i hpos)
    by_cases hiJ : i∈J
    · have hh := Finset.mem_inter.mpr ⟨hi,hiJ⟩
      rw [hn] at hh
      exact Finset.notMem_empty i hh
    · linarith [hz i hiJ htK]
  have hh := Finset.sum_nonpos (s := Finset.univ) (fun i _ => hn' i)
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma outer_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      1 < r → r<1+δ → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let r : ℕ → ℝ := fun n => 1+(δ/2)/(n+1)
  have hr (n) : 0 < r n := by dsimp [r]; positivity
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,add_zero] using (tendsto_const_nhds (x := (1:ℝ))).add
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (δ/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith)
    · dsimp [r]
      have : 0<(δ/2)/((n:ℝ)+1) := by positivity
      linarith
    · have hn : (1:ℝ)≤(n:ℝ)+1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hb := div_le_self (by positivity : (0:ℝ)≤δ/2) hn
      dsimp [r]
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
lemma inner_strip_trace {x : ℂ} {t : Angles} {δ : ℝ} (hδ : 0<δ)
    {W : Set ℂ} (ho : IsOpen W) {J : Finset (Fin k)}
    (hW : ∀ᵐz : ℂ∂volume,z∈W → c z∈J)
    (hstrip : ∀u : Angles,dist (direction u) (direction t)<δ → ∀r : ℝ,
      0 < r → 1-δ < r → r<1 → x+(r : ℂ)*direction u∈W) :
    ∃U : Set Angles,IsOpen U ∧ t∈U ∧
      ∀ᵐu∂angularMeasure,u∈U → (palette c hc x u∩J).Nonempty := by
  let K : Set Angles := {u | dist (direction u) (direction t)≤δ/2}
  let U : Set Angles := {u | dist (direction u) (direction t)<δ/2}
  have hK : IsCompact K := (isClosed_le (direction_continuous.dist continuous_const) continuous_const).isCompact
  let ε := min δ (1/2)
  have he : 0<ε := lt_min hδ (by norm_num)
  have heδ : ε≤δ := min_le_left _ _
  have he1 : ε≤1/2 := min_le_right _ _
  let r : ℕ → ℝ := fun n => 1-(ε/2)/(n+1)
  have hb (n : ℕ) : (ε/2)/(n+1)≤ε/2 := div_le_self (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  have hr (n) : 0 < r n := by dsimp [r]; linarith [hb n]
  have hrt : Tendsto r atTop (𝓝 1) := by
    simpa only [r,div_eq_mul_inv,one_mul,mul_zero,sub_zero] using (tendsto_const_nhds (x := (1:ℝ))).sub
      (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ε/2))
  have hh := trace_region_palette c hc hK ho hW hr hrt (fun n u hu => by
    apply hstrip u (by dsimp [K] at hu; linarith) (r n) (hr n)
    · dsimp [r]; linarith [hb n]
    · dsimp [r]
      have : 0<(ε/2)/((n:ℝ)+1) := by positivity
      linarith)
  refine ⟨U,isOpen_lt (direction_continuous.dist continuous_const) continuous_const,?_,?_⟩
  · change dist (direction t) (direction t)<δ/2
    simp only [dist_self]; positivity
  · exact hh.mono fun u hu hU => hu (show u∈K from (show dist (direction u) (direction t)<δ/2 from hU).le)
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_AngularBoundary
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma sixty_three : (3 : ℕ) • (sixty : Angles)=(Real.pi : Angles) := by
  rw [← AddCircle.coe_nsmul]
  congr 1
  simp only [nsmul_eq_mul,sixty]
  ring
lemma sixAngle_half (j : Fin 6) : sixAngle (j+3)=sixAngle j+(Real.pi : Angles) := by
  rw [show j+3=(j+1+1)+1 from (by decide : ∀j : Fin 6,j+3=(j+1+1)+1) j,sixAngle_step,sixAngle_step,sixAngle_step,← sixty_three]
  simp only [succ_nsmul,zero_nsmul,zero_add]
  abel
lemma direction_add_pi (t : Angles) : direction (t+(Real.pi : Angles))= -direction t := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [← AddCircle.coe_add,direction_real,direction_real,Circle.exp_add]
  simp
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma straddle_isOpen (K : Set ℂ) : IsOpen (Straddle K) := by
  have he : Straddle K=⋃p∈K,⋃q∈K,{z | dist z p<1 ∧ 1<dist z q} := by
    ext z
    simp only [Straddle,mem_iUnion,mem_ofPred_eq,exists_prop]
  rw [he]
  exact isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_iUnion fun _ =>
    (isOpen_lt (continuous_id.dist continuous_const) continuous_const).inter
      (isOpen_lt continuous_const (continuous_id.dist continuous_const))
lemma approaching_direction_inside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∀ᶠn in atTop,‖e-(r n : ℂ)*w n‖<1 := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (lt_mem_nhds (by positivity : (0:ℝ)<2*⟪e,v⟫))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hpos := mul_pos (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma approaching_direction_outside {r : ℕ → ℝ} {w : ℕ → ℂ} {v e : ℂ}
    (hr : ∀n,0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) (hw : ∀n,‖w n‖=1)
    (hwv : Tendsto w atTop (𝓝 v)) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∀ᶠn in atTop,1<‖e-(r n : ℂ)*w n‖ := by
  have ht : Tendsto (fun n => 2*⟪e,w n⟫-r n) atTop (𝓝 (2*⟪e,v⟫)) := by
    simpa only [sub_zero] using ((tendsto_const_nhds.inner hwv).const_mul 2).sub hr0
  filter_upwards [ht.eventually (gt_mem_nhds (by linarith : 2*⟪e,v⟫<(0:ℝ)))] with n hn
  have heq : ‖e-(r n : ℂ)*w n‖^2=1-2*r n*⟪e,w n⟫+(r n)^2 := by
    change ‖e-r n • w n‖^2= _
    rw [norm_sub_sq_real,inner_smul_right,norm_smul,Real.norm_eq_abs,abs_of_pos (hr n),he,hw]
    ring
  have hneg := mul_neg_of_pos_of_neg (hr n) hn
  nlinarith [norm_nonneg (e-(r n : ℂ)*w n)]
lemma outer_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : dist (x+e) q<1) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1 < r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),dist (x+(p.1 : ℂ)*p.2) q<1 :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (gt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ => ⟨q,hq,x,hx,?_,?_⟩⟩
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_pos (by linarith : 0 < r-1)]; linarith,heδ⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by linarith : 0 < r),he',mul_one]
    exact hr
lemma inner_straddle_strip {K : Set ℂ} {x e q : ℂ} (hx : x∈K) (hq : q∈K)
    (_he : ‖e‖=1) (hed : 1<dist (x+e) q) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0 < r → 1-δ < r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  have hn : ∀ᶠp : ℝ × ℂ in 𝓝 (1,e),1<dist (x+(p.1 : ℂ)*p.2) q :=
    (show Continuous (fun p : ℝ × ℂ => dist (x+(p.1 : ℂ)*p.2) q) by fun_prop).continuousAt.eventually
      (lt_mem_nhds (by simpa only [Complex.ofReal_one,one_mul] using hed))
  obtain ⟨δ,hδ,hsub⟩ := Metric.mem_nhds_iff.mp hn
  refine ⟨δ,hδ,fun e' he' heδ r hr hrδ hr1 => ⟨x,hx,q,hq,?_,?_⟩⟩
  · rw [dist_eq_norm,add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,he',mul_one]
    exact hr1
  · apply hsub (a := (r,e'))
    rw [Metric.mem_ball,Prod.dist_eq,max_lt_iff]
    exact ⟨by rw [Real.dist_eq,abs_of_neg (by linarith : r-1<0)]; linarith,heδ⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma finite_positive_lower_bound {ι : Type*} (E : Finset ι) (d : ι → ℝ)
    (hd : ∀i∈E,0<d i) : ∃δ>0,δ≤1 ∧ ∀i∈E,δ≤d i := by
  classical
  induction E using Finset.induction_on with
  | empty => exact ⟨1,by norm_num,le_rfl,by simp⟩
  | @insert a E ha ih =>
    obtain ⟨δ,hδ,hδ1,hδd⟩ := ih (fun i hi => hd i (Finset.mem_insert_of_mem hi))
    refine ⟨min δ (d a),lt_min hδ (hd a (Finset.mem_insert_self _ _)),(min_le_left _ _).trans hδ1,?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact min_le_right _ _
    · exact (min_le_left _ _).trans (hδd i hi)
lemma ApproachingContinuum.outer_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : 0<⟪e,v⟫) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,1 < r → r<1+δ →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_inside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply outer_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
lemma ApproachingContinuum.inner_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hv : ⟪e,v⟫<0) :
    ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,0 < r → 1-δ < r → r<1 →
      x+(r : ℂ)*e'∈Straddle K := by
  obtain ⟨n,hn⟩ := (approaching_direction_outside h.r_pos h.r_tendsto h.w_unit h.w_tendsto he hv).exists
  apply inner_straddle_strip h.center_mem (h.point_mem n) he
  simpa only [dist_eq_norm,add_sub_add_left_eq_sub] using hn
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma mem_spatialSupport_ae (hc : Measurable c) (i : Fin k) :
    ∀ᵐz : ℂ∂volume,c z=i → z∈spatialSupport c i :=
  (ae_restrict_iff' (measurableSet_eq_fun hc measurable_const)).mp
    (volume.restrict {z | c z=i}).support_mem_ae
lemma support_exclusion_ae (hc : Measurable c) {i : Fin k} {W : Set ℂ}
    (h : Disjoint (spatialSupport c i) W) : ∀ᵐz : ℂ∂volume,z∈W → c z≠i := by
  filter_upwards [mem_spatialSupport_ae c hc i] with z hz hzW hzcol
  exact Set.disjoint_left.mp h (hz hzcol) hzW
lemma finite_support_exclusion_ae (hc : Measurable c) {ι : Type*} [Fintype ι]
    (K : ι → Set ℂ) (F : ι → Finset (Fin k))
    (h : ∀i,∀j∈F i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∀ᵐz : ℂ∂volume,∀i,z∈Straddle (K i) → c z∉F i := by
  have hh : ∀i,∀j,∀ᵐz : ℂ∂volume,j∈F i → z∈Straddle (K i) → c z≠j := by
    intro i j
    by_cases hj : j∈F i
    · exact (support_exclusion_ae c hc (h i j hj)).mono fun z hz _ => hz
    · exact Eventually.of_forall fun _ h => (hj h).elim
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hh i))] with z hz i hi hj
  exact hz i (c z) hj hi rfl
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma angleEssential_open (s : Angles → Bool) (b : Bool) : IsOpen (angleEssential s b) := by
  apply isOpen_iff_forall_mem_open.mpr
  rintro t ⟨U,hU,ht,ha⟩
  exact ⟨U,fun u hu => ⟨U,hU,hu,ha⟩,hU,ht⟩
lemma angleEssential_ae (s : Angles → Bool) (b : Bool) :
    ∀ᵐt∂angularMeasure,t∈angleEssential s b → s t=b := ae_of_locally_ae angularMeasure (fun _ h => h)
lemma angleEssential_disjoint (s : Angles → Bool) {a b : Bool} (hab : a≠b) :
    Disjoint (angleEssential s a) (angleEssential s b) := by
  apply disjoint_left.mpr
  rintro t ⟨U,hU,ht,ha⟩ ⟨V,hV,ht',hb⟩
  have hpos := (hU.inter hV).measure_pos angularMeasure ⟨t,ht,ht'⟩
  obtain ⟨u,hu,huab⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae hpos.ne' (ae_restrict_of_ae (ha.and hb))
  exact hab ((huab.1 hu.1).symm.trans (huab.2 hu.2))
lemma angleEssential_shift {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (t : Angles) (b : Bool) :
    t+(sixty : Angles)∈angleEssential s (!b) ↔ t∈angleEssential s b := by
  constructor
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q+(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.add continuous_const),ht,?_⟩
    filter_upwards [(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae ha,hf] with q hq hqf hqU
    have hh := hq hqU
    rw [hqf] at hh
    exact Bool.not_injective hh
  · rintro ⟨U,hU,ht,ha⟩
    refine ⟨(fun q : Angles => q-(sixty : Angles)) ⁻¹' U,hU.preimage (continuous_id.sub continuous_const),by simpa,?_⟩
    have hh := (measurePreserving_add_right angularMeasure (-(sixty : Angles))).quasiMeasurePreserving.ae (ha.and hf)
    filter_upwards [hh] with q hq hqU
    have hcol := hq.1 hqU
    have hflip := hq.2
    change s (q-(sixty : Angles))=b at hcol
    simpa only [←sub_eq_add_neg,sub_add_cancel,hcol] using hflip
lemma angleBoundary_shift {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (t : Angles) :
    t+(sixty : Angles)∈angleBoundary s ↔ t∈angleBoundary s := by
  simp only [angleBoundary,mem_compl_iff,mem_iUnion,not_exists]
  constructor
  · intro h b hb
    exact h (!b) ((angleEssential_shift hf t b).mpr hb)
  · intro h b hb
    apply h (!b)
    apply (angleEssential_shift hf t (!b)).mp
    simpa only [Bool.not_not] using hb
lemma angleBoundary_nonempty {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) : (angleBoundary s).Nonempty := by
  by_contra hn
  have hcov : (univ : Set Angles)⊆angleEssential s false∪angleEssential s true := by
    intro t _
    have ht : t∉angleBoundary s := fun h => hn ⟨t,h⟩
    simp only [angleBoundary,mem_compl_iff,not_not,mem_iUnion] at ht
    obtain ⟨b,hb⟩ := ht
    cases b
    · exact Or.inl hb
    · exact Or.inr hb
  have hzero := hcov (mem_univ (0:Angles))
  have hconst : ∃b,∀ᵐt∂angularMeasure,s t=b := by
    rcases hzero with h0|h0
    · have hs := isPreconnected_univ.subset_left_of_subset_union (angleEssential_open s false)
        (angleEssential_open s true) (angleEssential_disjoint s (by decide)) hcov ⟨0,mem_univ _,h0⟩
      exact ⟨false,(angleEssential_ae s false).mono fun t ht => ht (hs (mem_univ _))⟩
    · have hs := isPreconnected_univ.subset_left_of_subset_union (angleEssential_open s true)
        (angleEssential_open s false) (angleEssential_disjoint s (by decide))
        (by simpa only [union_comm] using hcov) ⟨0,mem_univ _,h0⟩
      exact ⟨true,(angleEssential_ae s true).mono fun t ht => ht (hs (mem_univ _))⟩
  obtain ⟨b,hb⟩ := hconst
  have hh : ∀ᵐt∂angularMeasure,False := by
    filter_upwards [hb,(measurePreserving_add_right angularMeasure (sixty : Angles)).quasiMeasurePreserving.ae hb,hf] with t ht ht' he
    rw [ht,ht'] at he
    cases b <;> cases he
  exact hh.exists.choose_spec
lemma sixty_order : addOrderOf (sixty : Angles)=6 := by
  convert (AddCircle.addOrderOf_period_div (p:=2*Real.pi) (by norm_num : 0<(6:ℕ))) using 1
  all_goals try with_reducible_and_instances rfl
  congr 2
  dsimp [sixty]
  ring
lemma sixAngle_injective : Function.Injective sixAngle := by
  intro i j hij
  apply Fin.ext
  apply nsmul_injOn_Iio_addOrderOf (x := (sixty : Angles))
  · simpa only [sixty_order,mem_Iio] using i.isLt
  · simpa only [sixty_order,mem_Iio] using j.isLt
  · exact hij
lemma sixAngle_sub (i j : Fin 6) : sixAngle (i-j)=sixAngle i-sixAngle j := sixAngleHom.map_sub i j
lemma angleBoundary_six {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) {t : Angles} (ht : t∈angleBoundary s)
    (j : Fin 6) : t+sixAngle j∈angleBoundary s := by
  have hh (n : ℕ) : t+n•(sixty : Angles)∈angleBoundary s := by
    induction n with
    | zero => simpa using ht
    | succ n ih =>
      simpa only [add_nsmul,one_nsmul,←add_assoc] using (angleBoundary_shift hf (t+n•(sixty : Angles))).mpr ih
  exact hh j.val
lemma six_antipodal_vertex_cover : ∀b : Fin 6 → Bool,
    (∀j,b (j+3)=b j) → (∀j,b j=true ∨ b (j+1)=true) →
      4≤(Finset.univ.filter fun j => b j=true).card := by decide
/-- Core finite obstruction behind the one-orbit boundary theorem. -/
lemma angleBoundary_one_orbit {s : Angles → Bool}
    (hf : ∀ᵐt∂angularMeasure,s (t+(sixty : Angles))= !(s t)) (B : Finset Angles)
    (hB : B.card≤6) (hanti : ∀t,t+(Real.pi : Angles)∈B ↔ t∈B)
    (hl : ∀t,t∉B → t+(sixty : Angles)∉B → ∃b,t∈angleEssential s b) :
    ∃t,angleBoundary s={u | ∃j : Fin 6,u=t+sixAngle j} := by
  classical
  obtain ⟨t,ht⟩ := angleBoundary_nonempty hf
  let O (q : Angles) : Finset Angles := Finset.univ.image (fun j : Fin 6 => q+sixAngle j)
  have hcard (q : Angles) (hq : q∈angleBoundary s) : 4≤(B∩O q).card := by
    let b : Fin 6 → Bool := fun j => decide (q+sixAngle j∈B)
    have ha (j) : b (j+3)=b j := by
      simp only [b,sixAngle_half,←add_assoc,hanti]
    have hc (j) : b j=true ∨ b (j+1)=true := by
      by_contra hn
      have hh : q+sixAngle j∉B ∧ q+sixAngle (j+1)∉B := by simpa only [b,decide_eq_true_eq,not_or] using hn
      obtain ⟨v,hv⟩ := hl (q+sixAngle j) hh.1 (by simpa only [sixAngle_step,←add_assoc] using hh.2)
      exact (angleBoundary_six hf hq j) (mem_iUnion.mpr ⟨v,hv⟩)
    have hcount := six_antipodal_vertex_cover b ha hc
    have hi : Function.Injective (fun j : Fin 6 => q+sixAngle j) := (add_right_injective q).comp sixAngle_injective
    have him : (Finset.univ.filter fun j => b j=true).image (fun j : Fin 6 => q+sixAngle j)=B∩O q := by
      ext u
      simp only [Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,b,decide_eq_true_eq,
        Finset.mem_inter,O]
      constructor
      · rintro ⟨j,hj,rfl⟩; exact ⟨hj,j,rfl⟩
      · rintro ⟨hu,j,rfl⟩; exact ⟨j,hu,rfl⟩
    rw [←him,Finset.card_image_of_injective _ hi]
    exact hcount
  refine ⟨t,Set.ext fun u => ?_⟩
  constructor
  · intro hu
    by_contra hn
    have hd : Disjoint (O t) (O u) := by
      apply Finset.disjoint_left.mpr
      intro q hqt hqu
      obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hqt
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hqu
      apply hn
      refine ⟨i-j,?_⟩
      rw [sixAngle_sub]
      have he : t+sixAngle i=u+sixAngle j := hi.trans hj.symm
      calc u = (u+sixAngle j)-sixAngle j := by abel
           _ = (t+sixAngle i)-sixAngle j := by rw [he]
           _ = t+(sixAngle i-sixAngle j) := by abel
    have hd' : Disjoint (B∩O t) (B∩O u) := hd.mono Finset.inter_subset_right Finset.inter_subset_right
    have hh := Finset.card_le_card (show (B∩O t)∪(B∩O u)⊆B from Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
    rw [Finset.card_union_of_disjoint hd'] at hh
    have hct := hcard t ht
    have hcu := hcard u hu
    omega
  · rintro ⟨j,rfl⟩
    exact angleBoundary_six hf ht j
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Sectors
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma triangle_majority_cover : ∀s : Fin 3 → Bool,∃b : Bool,
    ∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i := by decide
lemma triangle_outsider : ∀s : Fin 3 → Bool,∀b : Bool,
    (∀j∈({0,1,2} : Finset (Fin 5)),∃i : Fin 3,s i=b ∧ j∈triangleEdge i) →
    ∀j : Fin 5,(∀i : Fin 3,s i=b → j∉triangleEdge i) → j=3 ∨ j=4 := by decide
lemma ApproachingContinuum.side_strip {x : ℂ} {K : Set ℂ} {v e : ℂ}
    (h : ApproachingContinuum x K v) (he : ‖e‖=1) (hn : ⟪e,v⟫≠0) (b : Bool)
    (hs : decide (0<⟪e,v⟫)=b) : ∃δ>0,∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
      0 < r → |r-1|<δ → (if b then 1 < r else r<1) → x+(r:ℂ)*e'∈Straddle K := by
  cases b
  · have hneg : ⟪e,v⟫<0 := lt_of_le_of_ne (le_of_not_gt (of_decide_eq_false hs)) hn
    obtain ⟨δ,hδ,hh⟩ := h.inner_strip he hneg
    refine ⟨δ,hδ,fun e' he' hd r hr hab hr1 => hh e' he' hd r hr ?_ hr1⟩
    have := (abs_lt.mp hab).1
    linarith
  · obtain ⟨δ,hδ,hh⟩ := h.outer_strip he (of_decide_eq_true hs)
    refine ⟨δ,hδ,fun e' he' hd r _ hab hr1 => hh e' he' hd r hr1 ?_⟩
    have := (abs_lt.mp hab).2
    linarith
/-- Three interface edges supply an actual outsider-only open strip in every
nonexceptional direction, with the radial side chosen by the majority sign. -/
lemma triangle_outsider_strip {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ}
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i)))
    {e : ℂ} (he : ‖e‖=1) (hn : ∀i,⟪e,v i⟫≠0) :
    ∃b : Bool,∃δ>0,∃W : Set ℂ,IsOpen W ∧
      (∀ᵐz : ℂ∂volume,z∈W → c z=3 ∨ c z=4) ∧
      ∀e' : ℂ,‖e'‖=1 → dist e' e<δ → ∀r : ℝ,
        0 < r → |r-1|<δ → (if b then 1 < r else r<1) → x+(r:ℂ)*e'∈W := by
  classical
  let s : Fin 3 → Bool := fun i => decide (0<⟪e,v i⟫)
  obtain ⟨b,hb⟩ := triangle_majority_cover s
  let E : Finset (Fin 3) := Finset.univ.filter fun i => s i=b
  have hex (i : E) := (hK i).side_strip he (hn i) b ((Finset.mem_filter.mp i.2).2)
  choose d hd hs using hex
  obtain ⟨δ,hδ,_,hδd⟩ := finite_positive_lower_bound Finset.univ d (fun i _ => hd i)
  let W : Set ℂ := ⋂i : E,Straddle (K i)
  refine ⟨b,δ,hδ,W,isOpen_iInter_of_finite (fun i => straddle_isOpen (K i)),?_,?_⟩
  · filter_upwards [finite_support_exclusion_ae c hc K triangleEdge hH] with z hz hzW
    apply triangle_outsider s b hb (c z)
    intro i hi
    exact hz i (mem_iInter.mp hzW ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩)
  · intro e' he' heδ r hr hrδ hside
    apply mem_iInter.mpr
    intro i
    exact hs i e' he' (heδ.trans_le (hδd i (Finset.mem_univ _))) r hr
      (hrδ.trans_le (hδd i (Finset.mem_univ _))) hside
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma triangle_binary_from_continua {c : ℂ → Fin 5} (hc : Measurable c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    BinaryCenter c hc x 3 4 := by
  have hh : ∀ᵐt∂angularMeasure,(∀i,⟪direction t,v i⟫≠0) →
      t∈paletteSet c hc x 3 ∨ t∈paletteSet c hc x 4 := by
    apply ae_of_locally_ae angularMeasure
    intro t ht
    obtain ⟨b,δ,hδ,W,hW,hWc,hs⟩ := triangle_outsider_strip hc hK hH (direction_norm t) ht
    have hcols : ∀ᵐz : ℂ∂volume,z∈W → c z∈({3,4} : Finset (Fin 5)) :=
      hWc.mono fun z hz hzw => by simpa only [Finset.mem_insert,Finset.mem_singleton] using hz hzw
    have hex : ∃A : Set Angles,IsOpen A ∧ t∈A ∧
        ∀ᵐu∂angularMeasure,u∈A → (palette c hc x u∩{3,4}).Nonempty := by
      cases b
      · apply inner_strip_trace c hc hδ hW hcols
        intro u hu r hr hrδ hr1
        apply hs (direction u) (direction_norm u) hu r hr _ hr1
        rw [abs_lt]; constructor <;> linarith
      · apply outer_strip_trace c hc hδ hW hcols
        intro u hu r hr1 hrδ
        apply hs (direction u) (direction_norm u) hu r (by linarith) _ hr1
        rw [abs_lt]; constructor <;> linarith
    obtain ⟨A,hA,htA,hae⟩ := hex
    refine ⟨A,hA,htA,hae.mono fun u hu hAu => ?_⟩
    obtain ⟨i,hi⟩ := hu hAu
    rcases Finset.mem_inter.mp hi with ⟨hip,hi⟩
    rcases Finset.mem_insert.mp hi with rfl|hi
    · exact Or.inl ((mem_palette c hc x u 3).mp hip)
    · rw [Finset.mem_singleton] at hi
      subst i
      exact Or.inr ((mem_palette c hc x u 4).mp hip)
  filter_upwards [hh,ae_all_iff.mpr (fun i => ae_direction_nonorthogonal (hv i))] with t ht hn
  exact ht hn
lemma direction_injective : Function.Injective direction := fun _ _ h =>
  AddCircle.injective_toCircle (by positivity : (2*Real.pi:ℝ)≠0) (Subtype.ext h)
lemma direction_plus_sixty (t : Angles) :
    direction (t+(sixty : Angles))=direction t*(Circle.exp (Real.pi/3) : ℂ) := by
  obtain ⟨a,rfl⟩ := QuotientAddGroup.mk_surjective t
  rw [←AddCircle.coe_add,direction_real,direction_real,Circle.exp_add]
  rfl
lemma triple_orthogonal_cover (v : Fin 3 → ℂ) (hv : ∀i,‖v i‖=1) :
    ∃B : Finset Angles,B.card≤6 ∧ (∀t,t+(Real.pi : Angles)∈B ↔ t∈B) ∧
      ∀t,t∉B → ∀i,⟪direction t,v i⟫≠0 := by
  classical
  have hex (i : Fin 3) : ∃t : Angles,direction t=Complex.I*v i := direction_exists
    (by rw [norm_mul,Complex.norm_I,hv,one_mul])
  choose a ha using hex
  let B : Finset Angles := Finset.univ.biUnion fun i : Fin 3 => {a i,a i+(Real.pi : Angles)}
  have hmem (t : Angles) : t∈B ↔ ∃i : Fin 3,t=a i ∨ t=a i+(Real.pi : Angles) := by
    simp only [B,Finset.mem_biUnion,Finset.mem_univ,true_and,Finset.mem_insert,Finset.mem_singleton]
  have hdouble (t : Angles) : t+(Real.pi : Angles)+(Real.pi : Angles)=t := by
    apply direction_injective
    simp only [direction_add_pi,neg_neg]
  refine ⟨B,?_,?_,?_⟩
  · calc B.card ≤ ∑i : Fin 3,({a i,a i+(Real.pi : Angles)} : Finset Angles).card := Finset.card_biUnion_le
         _ ≤ ∑_i : Fin 3,2 := Finset.sum_le_sum fun _ _ => by simpa using (Finset.card_insert_le (a _) ({a _+(Real.pi : Angles)} : Finset Angles))
         _ = 6 := by norm_num
  · intro t
    rw [hmem,hmem]
    constructor
    · rintro ⟨i,hi|hi⟩
      · exact ⟨i,Or.inr (by rw [←hi,hdouble])⟩
      · exact ⟨i,Or.inl (add_right_cancel hi)⟩
    · rintro ⟨i,rfl|rfl⟩
      · exact ⟨i,Or.inr rfl⟩
      · exact ⟨i,Or.inl (hdouble _)⟩
  · intro t ht i hinner
    apply ht
    rw [hmem]
    rcases complex_unit_orthogonal (direction_norm t) (hv i) hinner with he|he
    · exact ⟨i,Or.inl (direction_injective (he.trans (ha i).symm))⟩
    · refine ⟨i,Or.inr (direction_injective ?_)⟩
      rw [direction_add_pi,ha,he]
      ring
/-- The actual three-interface data force the source's unique six-position
boundary orbit. This theorem does not assume local rigidity or orbit finiteness. -/
lemma triangle_boundary_one_orbit_oai {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {x : ℂ} {K : Fin 3 → Set ℂ} {v : Fin 3 → ℂ} (hv : ∀i,‖v i‖=1)
    (hK : ∀i,ApproachingContinuum x (K i) (v i))
    (hH : ∀i,∀j∈triangleEdge i,Disjoint (spatialSupport c j) (Straddle (K i))) :
    ∃t,angleBoundary (triangleState c hc x)={u | ∃j : Fin 6,u=t+sixAngle j} := by
  obtain ⟨B,hB,ha,hn⟩ := triple_orthogonal_cover v hv
  apply angleBoundary_one_orbit (triangleState_flip hc hw (triangle_binary_from_continua hc hv hK hH)) B hB ha
  intro t ht htR
  apply triangleState_local hc hw hv hK hH (hn t ht)
  simpa only [direction_plus_sixty] using hn (t+(sixty : Angles)) htR
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.triangle_boundary_one_orbit_oai := @OAI.EuclideanFiveColor.triangle_boundary_one_orbit_oai
