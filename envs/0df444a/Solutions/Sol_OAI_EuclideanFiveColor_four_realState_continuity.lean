-- Prove2me | solution 1 for OAI.EuclideanFiveColor.four_realState_continuity
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:03:41.071579+00:00
-- url     : https://prove2.me/submissions/c01fb613-7c82-4716-88ea-3757a66d63ba

import Mathlib
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_four_weak_limit_identify

section
-- module Solutions.OAIQ5_T4.Compat
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_WeakColoring
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma shiftL2_ae (z : ℂ) (f : PlaneL2) : shiftL2 z f =ᵐ[volume] fun x => f (x+z) :=
  Lp.coeFn_compMeasurePreserving f _
lemma shiftL2_continuous (f : PlaneL2) : Continuous (fun z => shiftL2 z f) := by
  let g : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp g.continuous (fun z => measurePreserving_add_right volume z) (by simp)
lemma product_zero_of_inner_zero (f g : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (hg : ∀ᵐ x ∂volume, 0 ≤ g x) (h : ⟪f,g⟫ = 0) :
    ∀ᵐ x ∂volume, f x*g x=0 := by
  have hi : Integrable (fun x : ℂ => f x*g x) volume := by
    simpa [RCLike.inner_apply,mul_comm] using (L2.integrable_inner (𝕜 := ℝ) f g)
  have hn : ∀ᵐ x ∂volume, 0 ≤ f x*g x := by
    filter_upwards [hf,hg] with x hx hy
    exact mul_nonneg hx hy
  rw [L2.inner_def] at h
  apply (integral_eq_zero_iff_of_nonneg_ae hn hi).mp
  simpa [RCLike.inner_apply,mul_comm] using h
/-- AE exclusions over any full-support parameter measure upgrade to every parameter. -/
lemma all_parameters_product_zero {T : Type*} [TopologicalSpace T] [MeasurableSpace T]
    (μ : Measure T) [μ.IsOpenPosMeasure] (d : T → ℂ) (hd : Continuous d)
    (f : PlaneL2) (hf : ∀ᵐ x ∂volume, 0 ≤ f x)
    (ho : ∀ᵐ t ∂μ, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0) :
    ∀ t : T, ∀ᵐ x ∂(volume : Measure ℂ), f x*f (x+d t)=0 := by
  have hc : Continuous (fun t : T => ⟪f,shiftL2 (d t) f⟫) :=
    continuous_const.inner ((shiftL2_continuous f).comp hd)
  have hz : (fun t : T => ⟪f,shiftL2 (d t) f⟫) =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ho] with t ht
    rw [L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [shiftL2_ae (d t) f,ht] with x hx hh
    simpa [RCLike.inner_apply,mul_comm,hx] using hh
  have he := (hc.ae_eq_iff_eq μ continuous_const).mp hz
  intro t
  have hg : ∀ᵐ x ∂volume, 0 ≤ shiftL2 (d t) f x := by
    filter_upwards [shiftL2_ae (d t) f,
      (measurePreserving_add_right volume (d t)).quasiMeasurePreserving.ae hf] with x hx hh
    simpa only [hx] using hh
  have h0 := product_zero_of_inner_zero f (shiftL2 (d t) f) hf hg (congrFun he t)
  filter_upwards [h0,shiftL2_ae (d t) f] with x hx hh
  simpa only [hh] using hx
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
include hc
lemma truncatedVector_ae (i : Fin k) (n : ℕ) :
    truncatedVector c hc i n =ᵐ[volume] (truncatedClass c i n).indicator (fun _ => (1 : ℝ)) :=
  MemLp.coeFn_toLp _
lemma weak_all_directions (hweak : WeakColoring k c) :
    ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
  have ho : ∀ᵐ t ∂angularMeasure, ∀ᵐ z ∂(volume : Measure ℂ), c z ≠ c (z+direction t) := by
    apply (Measure.ae_ae_comm ?_).mp (Measure.ae_ae_of_ae_prod hweak.2)
    exact (measurableSet_eq_fun (hc.comp measurable_fst)
      (hc.comp (measurable_fst.add (direction_continuous.measurable.comp measurable_snd)))).compl
  have hz (i : Fin k) (n : ℕ) : ∀ t : Angles, ∀ᵐ z ∂(volume : Measure ℂ),
      truncatedVector c hc i n z*truncatedVector c hc i n (z+direction t)=0 := by
    apply all_parameters_product_zero angularMeasure direction direction_continuous
    · filter_upwards [truncatedVector_ae c hc i n] with z hz
      rw [hz]
      exact Set.indicator_nonneg (fun _ _ => zero_le_one) _
    · filter_upwards [ho] with t ht
      filter_upwards [ht,truncatedVector_ae c hc i n,
        (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z hne h1 h2
      rw [h1,h2]
      by_cases h : z ∈ truncatedClass c i n
      · have hh : z+direction t ∉ truncatedClass c i n := fun hh => hne (h.1.trans hh.1.symm)
        simp [Set.indicator_of_notMem hh]
      · simp [Set.indicator_of_notMem h]
  intro t
  have hi : ∀ᵐ z ∂(volume : Measure ℂ), ∀ i : Fin k, ∀ n : ℕ,
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) z)*
      ((truncatedClass c i n).indicator (fun _ => (1 : ℝ)) (z+direction t))=0 := by
    apply ae_all_iff.mpr
    intro i
    apply ae_all_iff.mpr
    intro n
    filter_upwards [hz i n t,truncatedVector_ae c hc i n,
      (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving.ae (truncatedVector_ae c hc i n)] with z h0 h1 h2
    simpa only [h1,h2] using h0
  filter_upwards [hi] with z hz
  intro he
  obtain ⟨n,hn⟩ := exists_nat_gt (max ‖z‖ ‖z+direction t‖)
  have h1 : z ∈ truncatedClass c (c z) n := ⟨rfl,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_left _ _) hn).le⟩
  have h2 : z+direction t ∈ truncatedClass c (c z) n := ⟨he.symm,by
    simpa only [Metric.mem_closedBall,dist_zero_right] using (lt_of_le_of_lt (le_max_right _ _) hn).le⟩
  have h0 := hz (c z) n
  simp [Set.indicator_of_mem h1,Set.indicator_of_mem h2] at h0
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology Set
namespace EuclideanFiveColor
lemma densityOne_disjoint {A B : Set ℂ} (hB : MeasurableSet B)
    (hd : AEDisjoint volume A B) {x : ℂ} (hA : DensityOne A x) : ¬ DensityOne B x := by
  intro hb
  have hh := hA.add hb
  have hle : (1 : ENNReal)+1 ≤ 1 := le_of_tendsto hh (by
    filter_upwards [self_mem_nhdsWithin] with r hr
    rw [← ENNReal.add_div,← measure_union₀ (hB.inter measurableSet_closedBall).nullMeasurableSet
      (hd.mono inter_subset_left inter_subset_left)]
    apply (ENNReal.div_le_iff (Metric.measure_closedBall_pos volume x hr).ne'
      ((isCompact_closedBall x r).measure_ne_top)).mpr
    simpa only [one_mul] using measure_mono (union_subset inter_subset_right inter_subset_right))
  norm_num at hle
lemma densityOne_translate {A : Set ℂ} {x u : ℂ} :
    DensityOne ((fun z : ℂ => z+u) ⁻¹' A) x ↔ DensityOne A (x+u) := by
  have he (r : ℝ) : (fun z : ℂ => z+u) ⁻¹' (Metric.closedBall (x+u) r) = Metric.closedBall x r := by
    ext z
    simp only [Set.mem_preimage,Metric.mem_closedBall,dist_eq_norm,add_sub_add_right_eq_sub]
  have h1 (r : ℝ) : volume (((fun z : ℂ => z+u) ⁻¹' A) ∩ Metric.closedBall x r) =
      volume (A ∩ Metric.closedBall (x+u) r) := by
    rw [← he,← Set.preimage_inter,measure_preimage_add_right]
  have h2 (r : ℝ) : volume (Metric.closedBall x r) = volume (Metric.closedBall (x+u) r) := by
    rw [← he,measure_preimage_add_right]
  simp only [DensityOne,h1,h2]
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
lemma weak_density_proper {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (hw : WeakColoring k c)
    (i : Fin k) {x y : ℂ} (hxy : ‖x-y‖=1) (hx : DensityOne {z | c z=i} x) :
    ¬ DensityOne {z | c z=i} y := by
  let u := y-x
  obtain ⟨t,ht⟩ := direction_exists (u := u) (by simpa only [u,norm_sub_rev] using hxy)
  have hd : AEDisjoint volume {z | c z=i} ((fun z : ℂ => z+u) ⁻¹' {z | c z=i}) := by
    apply (measure_eq_zero_iff_ae_notMem).mpr
    filter_upwards [weak_all_directions c hc hw t] with z hz
    rintro ⟨h1,h2⟩
    exact hz (by simpa only [ht] using h1.trans h2.symm)
  have hh := densityOne_disjoint ((measurableSet_eq_fun hc measurable_const).preimage
    (measurable_id.add_const u)) hd hx
  simp only [id_eq] at hh
  rw [densityOne_translate] at hh
  simpa only [u,add_sub_cancel] using hh
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
open Filter Topology
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [TopologicalSpace.SeparableSpace E]
lemma exists_finite_weak_subseq {ι : Type*} [Finite ι] (f : ℕ → ι → E) (C : ℝ)
    (hf : ∀ n i, ‖f n i‖ ≤ C) :
    ∃ b : ι → E, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i, ‖b i‖ ≤ C) ∧ ∀ i v, Tendsto (fun n => ⟪f (φ n) i,v⟫) atTop (𝓝 ⟪b i,v⟫) := by
  let K : Set (WeakDual ℝ E) := WeakDual.toStrongDual ⁻¹' Metric.closedBall 0 C
  have hK : IsCompact K := WeakDual.isCompact_closedBall 0 C
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : TopologicalSpace.MetrizableSpace K := WeakDual.metrizable_of_isCompact ℝ E K hK
  let u : ℕ → ι → K := fun n i => ⟨weakHilbert (f n i), by
    simpa only [K,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right,weakHilbert,
      StrongDual.toStrongDual_toWeakDual,LinearIsometryEquiv.norm_map] using hf n i⟩
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (ι → K))).isSeqCompact.subseq_of_frequently_in
    (Filter.Eventually.frequently (Filter.Eventually.of_forall (fun n => Set.mem_univ (u n))))
  refine ⟨fun i => (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual (b i).1),φ,hφ,?_,?_⟩
  · intro i
    simpa only [LinearIsometryEquiv.norm_map,K,Set.mem_preimage,Metric.mem_closedBall,dist_zero_right] using (b i).2
  · intro i v
    have ht := ((WeakDual.eval_continuous v).comp continuous_subtype_val).tendsto (b i)
      |>.comp ((continuous_apply i).tendsto b |>.comp hb)
    change Tendsto (fun n => ⟪f (φ n) i,v⟫) atTop (𝓝 ((b i).1 v)) at ht
    simpa only [InnerProductSpace.toDual_symm_apply,WeakDual.toStrongDual_apply] using ht
end EuclideanFiveColor
end

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
-- module Solutions.OAIQ5_T4.PlaneColoring_Expansion
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology
open scoped NNReal
namespace EuclideanFiveColor
variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [NormalSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {μ : Measure X} {ν : Measure Y}
omit [TopologicalSpace Y] [NormalSpace Y] [BorelSpace Y] in
lemma integral_norm_comp_le {T : X → Y} (hT : Measurable T) {C : ℝ≥0}
    (hmap : μ.map T ≤ (C : ENNReal) • ν) {f : Y → ℝ} (hf : Integrable f ν) :
    (∫ x, ‖f (T x)‖ ∂μ) ≤ (C : ℝ)*(∫ y, ‖f y‖ ∂ν) := by
  have hh := (hf.smul_measure (by simp : (C : ENNReal) ≠ ⊤)).mono_measure hmap
  rw [← integral_map hT.aemeasurable hh.norm.aestronglyMeasurable]
  calc
    _ ≤ ∫ y, ‖f y‖ ∂((C : ENNReal) • ν) :=
      integral_mono_measure hmap (Eventually.of_forall fun y => norm_nonneg _) (hf.norm.smul_measure (by simp))
    _ = _ := by rw [integral_smul_measure]; simp
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_Fourier
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglePeriodPositive _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
namespace Multiplier
variable {X : Type*} [MeasurableSpace X] (μ : Measure X)
lemma clm_ae (f : X → ℂ) (hf : AEStronglyMeasurable f μ) {C : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖≤C)
    (g : Lp ℂ 2 μ) : clm μ f hf hbound g =ᵐ[μ] fun x => f x*g x := apply_ae μ f hf hbound g
end Multiplier
lemma planeTranslate_ae (h : ℂ) (g : ComplexPlaneL2) :
    planeTranslate h g =ᵐ[volume] fun x => g (x+h) :=
  Lp.coeFn_compMeasurePreserving g (measurePreserving_add_right volume h)
lemma phaseMultiplier_ae (h : ℂ) (g : ComplexPlaneL2) :
    phaseMultiplier h g =ᵐ[volume] fun ξ => planePhase h ξ*g ξ := Multiplier.clm_ae _ _ _ _ _
lemma schwartzTranslate_apply (h : ℂ) (f : SchwartzMap ℂ ℂ) (x : ℂ) :
    schwartzTranslate h f x = f (x+h) := rfl
lemma schwartzTranslate_toLp (h : ℂ) (f : SchwartzMap ℂ ℂ) :
    (schwartzTranslate h f).toLp 2 = planeTranslate h (f.toLp 2) := by
  apply Lp.ext
  filter_upwards [(schwartzTranslate h f).coeFn_toLp 2,planeTranslate_ae h (f.toLp 2),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (f.coeFn_toLp 2 volume)] with x hx hy hz
  exact hx.trans ((schwartzTranslate_apply h f x).trans (hz.symm.trans hy.symm))
lemma fourier_schwartzTranslate (h : ℂ) (f : SchwartzMap ℂ ℂ) (ξ : ℂ) :
    𝓕 (schwartzTranslate h f) ξ = planePhase h ξ * 𝓕 f ξ := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right Real.fourierChar volume
    (innerₗ ℂ) (f : ℂ → ℂ) h) ξ
  simpa only [SchwartzMap.fourier_coe,Real.fourier_eq,schwartzTranslate_apply,
    planePhase,Circle.smul_def,smul_eq_mul,VectorFourier.fourierIntegral,Function.comp_def,innerₗ_apply_apply] using hh
lemma fourier_planeTranslate (h : ℂ) (g : ComplexPlaneL2) :
    𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g) := by
  apply DenseRange.induction_on (p := fun g : ComplexPlaneL2 => 𝓕 (planeTranslate h g) = phaseMultiplier h (𝓕 g))
    (SchwartzMap.denseRange_toLpCLM (E := ℂ) (F := ℂ) (p := 2) ENNReal.ofNat_ne_top) g
  · exact isClosed_eq ((Lp.fourierTransformₗᵢ ℂ ℂ).continuous.comp (planeTranslate h).continuous)
      ((phaseMultiplier h).continuous.comp (Lp.fourierTransformₗᵢ ℂ ℂ).continuous)
  intro f
  change 𝓕 (planeTranslate h (f.toLp 2)) = phaseMultiplier h (𝓕 (f.toLp 2))
  rw [← schwartzTranslate_toLp,SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzTranslate h f)).coeFn_toLp 2,phaseMultiplier_ae h ((𝓕 f).toLp 2),
    (𝓕 f).coeFn_toLp 2] with ξ hξ hmul hf
  rw [hξ,hmul,hf]
  exact fourier_schwartzTranslate h f ξ
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter
namespace EuclideanFiveColor.ProbabilityL2
variable {X Ω : Type*} [MeasurableSpace X] [MeasurableSpace Ω]

variable (μ : Measure X) [SFinite μ] (ν : Measure Ω) [IsProbabilityMeasure ν]
lemma average_toLp_integral {F : X × Ω → ℂ} (hF : StronglyMeasurable F)
    (hF2 : Integrable (fun z => ‖F z‖^2) (μ.prod ν)) (G : Ω → Lp ℂ 2 μ)
    (hG : Integrable G ν) (hrep : ∀ᵐ ω ∂ν, G ω =ᵐ[μ] fun x => F (x,ω)) :
    (average_memLp μ ν hF hF2).toLp (average ν F) = ∫ ω, G ω ∂ν := by
  apply ext_inner_left ℂ
  intro g
  have hg2 : Integrable (fun z : X × Ω => ‖g z.1‖^2) (μ.prod ν) :=
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)).comp_fst ν
  have hpair : Integrable (fun z : X × Ω => inner ℂ (g z.1) (F z)) (μ.prod ν) := by
    apply (hg2.add hF2).mono'
      (((Lp.stronglyMeasurable g).comp_measurable measurable_fst).inner hF).aestronglyMeasurable
    exact Eventually.of_forall fun z => (norm_inner_le_norm _ _).trans
      (by dsimp only [Pi.add_apply]; nlinarith [sq_nonneg (‖g z.1‖-‖F z‖)])
  rw [L2.inner_def,← integral_inner hG g]
  calc
    _ = ∫ x, inner ℂ (g x) (average ν F x) ∂μ := integral_congr_ae (by
      filter_upwards [MemLp.coeFn_toLp (average_memLp μ ν hF hF2)] with x hx
      rw [hx])
    _ = ∫ x, ∫ ω, inner ℂ (g x) (F (x,ω)) ∂ν ∂μ := integral_congr_ae (by
      filter_upwards [fiber_memLp μ ν hF hF2] with x hx
      exact (integral_inner (hx.integrable (by norm_num)) (g x)).symm)
    _ = ∫ ω, ∫ x, inner ℂ (g x) (F (x,ω)) ∂μ ∂ν := integral_integral_swap hpair
    _ = _ := integral_congr_ae (by
      filter_upwards [hrep] with ω hω
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hω] with x hx
      rw [hx])
end EuclideanFiveColor.ProbabilityL2
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleDecay
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton _root_.OAI.EuclideanFiveColor.instFactNeENNRealOfNatTop_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma oscillatory_integral_bound {a b : ℝ} (hab : a ≤ b)
    {g g' : ℝ → ℂ} {w w' : ℝ → ℝ}
    (hg : ∀ t ∈ Icc a b, HasDerivAt g (g' t) t)
    (hw : ∀ t ∈ Icc a b, HasDerivAt w (w' t) t)
    (hgi : IntervalIntegrable g' volume a b) (hwi : IntervalIntegrable w' volume a b)
    (hn : ∀ t ∈ Icc a b, ‖g t‖=1) (hwpos : ∀ t ∈ Icc a b, 0 ≤ w t)
    (hwneg : ∀ t ∈ Icc a b, w' t ≤ 0)
    (he : ∀ t ∈ Icc a b, ((w t : ℂ)*Complex.I)*g' t=g t) :
    ‖∫ t in a..b, g t‖ ≤ 2*w a := by
  have hwu : ∀ t ∈ uIcc a b, HasDerivAt (fun t => (w t : ℂ)*Complex.I) ((w' t : ℂ)*Complex.I) t := by
    intro t ht
    exact ((hw t (by simpa [uIcc_of_le hab] using ht)).ofReal_comp).mul_const _
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul hwu
    (fun t ht => hg t (by simpa [uIcc_of_le hab] using ht)) ((show IntervalIntegrable (fun t => (w' t : ℂ)) volume a b from
      ⟨Complex.ofRealCLM.integrable_comp hwi.1,Complex.ofRealCLM.integrable_comp hwi.2⟩).mul_const _) hgi
  have hleft : (∫ t in a..b, ((w t : ℂ)*Complex.I)*g' t) = ∫ t in a..b, g t :=
    intervalIntegral.integral_congr (fun t ht => he t (by simpa [uIcc_of_le hab] using ht))
  rw [hleft] at hs
  have hint : ‖∫ t in a..b, (w' t : ℂ)*Complex.I*g t‖ ≤ ∫ t in a..b, -w' t := by
    apply intervalIntegral.norm_integral_le_of_norm_le hab _ hwi.neg
    filter_upwards with t ht
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_I,hn t ⟨ht.1.le,ht.2⟩,mul_one,mul_one,
      abs_of_nonpos (hwneg t ⟨ht.1.le,ht.2⟩)]
    rfl
  have hiw : (∫ t in a..b, -w' t)=w a-w b := by
    rw [intervalIntegral.integral_neg,intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hw t (by simpa [uIcc_of_le hab] using ht)) hwi]
    ring
  have hna : ‖(w a : ℂ)*Complex.I*g a‖=w a := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos a ⟨le_rfl,hab⟩),
      Complex.norm_I,hn a ⟨le_rfl,hab⟩,mul_one,mul_one]
  have hnb : ‖(w b : ℂ)*Complex.I*g b‖=w b := by
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hwpos b ⟨hab,le_rfl⟩),
      Complex.norm_I,hn b ⟨hab,le_rfl⟩,mul_one,mul_one]
  rw [hs]
  have hh := norm_sub_le ((w b : ℂ)*Complex.I*g b-(w a : ℂ)*Complex.I*g a)
    (∫ t in a..b, (w' t : ℂ)*Complex.I*g t)
  have hh' := norm_sub_le ((w b : ℂ)*Complex.I*g b) ((w a : ℂ)*Complex.I*g a)
  rw [hna,hnb] at hh'
  rw [hiw] at hint
  linarith
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma circleOscillation_norm (r t : ℝ) : ‖circleOscillation r t‖=1 := Complex.norm_exp_ofReal_mul_I _
lemma circleOscillation_continuous (r : ℝ) : Continuous (circleOscillation r) := by unfold circleOscillation; fun_prop
lemma circleOscillation_hasDeriv (r t : ℝ) :
    HasDerivAt (circleOscillation r) ((-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) t := by
  unfold circleOscillation
  convert (((Real.hasDerivAt_cos t).const_mul r).ofReal_comp.mul_const Complex.I).cexp using 1
  all_goals try with_reducible_and_instances rfl
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_tail {r a : ℝ} (hr : 0 < r) (ha : 0<a) (hab : a≤Real.pi/2) :
    ‖∫ t in a..Real.pi/2, circleOscillation r t‖ ≤ 2/(r*Real.sin a) := by
  have hsin (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0<Real.sin t :=
    Real.sin_pos_of_pos_of_lt_pi (ha.trans_le ht.1) (by linarith [ht.2,Real.pi_pos])
  have hcos (t : ℝ) (ht : t ∈ Icc a (Real.pi/2)) : 0≤Real.cos t :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1,Real.pi_pos],ht.2⟩
  let w := fun t => 1/(r*Real.sin t)
  let w' := fun t => -Real.cos t/(r*(Real.sin t)^2)
  have hw : ∀ t ∈ Icc a (Real.pi/2), HasDerivAt w (w' t) t := by
    intro t ht
    convert ((Real.hasDerivAt_sin t).const_mul r).inv (mul_ne_zero hr.ne' (hsin t ht).ne') using 1 <;> first
    | rfl
    | (change w = (fun y => r * Real.sin y)⁻¹; funext s; simp only [w,Pi.inv_apply,one_div])
    | (change -Real.cos t/(r*(Real.sin t)^2) = -(r*Real.cos t)/(r*Real.sin t)^2; field_simp)
  have hwi : IntervalIntegrable w' volume a (Real.pi/2) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div (Real.continuous_cos.neg.continuousOn) (continuous_const.mul (Real.continuous_sin.pow 2)).continuousOn
    intro t ht
    have ht' : t ∈ Icc a (Real.pi/2) := by simpa [uIcc_of_le hab] using ht
    exact mul_ne_zero hr.ne' (pow_ne_zero _ (hsin t ht').ne')
  have hi : IntervalIntegrable (fun t => (-r*Real.sin t : ℝ)*Complex.I*circleOscillation r t) volume a (Real.pi/2) := by
    apply Continuous.intervalIntegrable
    unfold circleOscillation
    fun_prop
  have h := oscillatory_integral_bound hab (fun t _ => circleOscillation_hasDeriv r t) hw hi hwi
    (fun t _ => circleOscillation_norm r t) (fun t ht => (one_div_pos.mpr (mul_pos hr (hsin t ht))).le)
    (fun t ht => by dsimp [w']; exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hcos t ht)) (by positivity))
    (fun t ht => by
      dsimp [w]
      have hrC : (r : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hr.ne'
      have hsC : (Real.sin t : ℂ)≠0 := Complex.ofReal_ne_zero.mpr (hsin t ht).ne'
      simp only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_neg]
      field_simp
      simp only [Complex.I_sq]
      ring)
  simpa only [w,mul_one_div] using h
lemma circleOscillation_quarter {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t‖ ≤ (1+Real.pi)/Real.sqrt r := by
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hs : 0<Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs1 : 1≤Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr
  let a := 1/Real.sqrt r
  have ha : 0<a := one_div_pos.mpr hs
  have ha1 : a≤1 := (div_le_one hs).mpr hs1
  have hab : a≤Real.pi/2 := by linarith [Real.pi_gt_three]
  have hi := circleOscillation_continuous r
  have hhead : ‖∫ t in (0:ℝ)..a, circleOscillation r t‖ ≤ a := by
    simpa [abs_of_nonneg ha.le] using intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0:ℝ)) (b := a) (C := (1:ℝ)) (fun t _ => (circleOscillation_norm r t).le)
  have htail := circleOscillation_tail hr0 ha hab
  have hsin := Real.mul_le_sin ha.le hab
  have hden : 0 < r*(2/Real.pi*a) := by positivity
  have hh : 2/(r*Real.sin a) ≤ Real.pi/Real.sqrt r := by
    calc
      _ ≤ 2/(r*(2/Real.pi*a)) := div_le_div_of_nonneg_left (by norm_num) hden
        (mul_le_mul_of_nonneg_left hsin hr0.le)
      _ = Real.pi/Real.sqrt r := by
        dsimp [a]
        field_simp
        nlinarith [Real.sq_sqrt hr0.le]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := a))
    (hi.intervalIntegrable (a := a) (b := Real.pi/2))]
  have hn := norm_add_le (∫ t in (0:ℝ)..a, circleOscillation r t)
    (∫ t in a..Real.pi/2, circleOscillation r t)
  have hea : a + Real.pi/Real.sqrt r = (1+Real.pi)/Real.sqrt r := by dsimp [a]; ring
  linarith
lemma circleOscillation_pi_sub (r t : ℝ) :
    circleOscillation r (Real.pi-t) = (starRingEnd ℂ) (circleOscillation r t) := by
  simp only [circleOscillation,Real.cos_pi_sub,← Complex.exp_conj,map_mul,
    Complex.conj_ofReal,Complex.conj_I]
  congr 1
  simp only [Complex.ofReal_mul,Complex.ofReal_neg]
  ring
lemma circleOscillation_two_pi_sub (r t : ℝ) :
    circleOscillation r (2*Real.pi-t) = circleOscillation r t := by
  simp only [circleOscillation,Real.cos_two_pi_sub]
lemma circleOscillation_full {r : ℝ} (hr : 1 ≤ r) :
    ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation r t‖ ≤ 4*(1+Real.pi)/Real.sqrt r := by
  have hi := circleOscillation_continuous r
  have hq : (∫ t in Real.pi/2..Real.pi, circleOscillation r t) =
      (starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t) := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi/2, circleOscillation r (Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_pi_sub,intervalIntegral.intervalIntegral_conj]
  have hhalf : ‖∫ t in (0:ℝ)..Real.pi, circleOscillation r t‖ ≤
      2*((1+Real.pi)/Real.sqrt r) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi/2))
      (hi.intervalIntegrable (a := Real.pi/2) (b := Real.pi)),hq]
    have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t)
      ((starRingEnd ℂ) (∫ t in (0:ℝ)..Real.pi/2, circleOscillation r t))
    rw [Complex.norm_conj] at hn
    linarith [circleOscillation_quarter hr]
  have hs : (∫ t in Real.pi..2*Real.pi, circleOscillation r t) =
      ∫ t in (0:ℝ)..Real.pi, circleOscillation r t := by
    calc
      _ = ∫ t in (0:ℝ)..Real.pi, circleOscillation r (2*Real.pi-t) := by
        rw [intervalIntegral.integral_comp_sub_left]; congr 2 <;> ring
      _ = _ := by simp only [circleOscillation_two_pi_sub]
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi.intervalIntegrable (a := 0) (b := Real.pi))
    (hi.intervalIntegrable (a := Real.pi) (b := 2*Real.pi)),hs]
  have hn := norm_add_le (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
    (∫ t in (0:ℝ)..Real.pi, circleOscillation r t)
  rw [mul_div_assoc]
  linarith
end EuclideanFiveColor

end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma circlePhase_real (ξ : ℂ) (t : ℝ) :
    planePhase (direction (t:Angles)) ξ = circleOscillation (2*Real.pi*‖ξ‖) (t-Complex.arg ξ) := by
  have hinner : inner ℝ (direction (t:Angles)) ξ = ‖ξ‖*Real.cos (t-Complex.arg ξ) := by
    rw [Complex.inner,direction_real,Circle.coe_exp,Complex.exp_ofReal_mul_I]
    simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.add_im,Complex.mul_im]
    rw [Real.cos_sub]
    have hr := Complex.norm_mul_cos_arg ξ
    have hi := Complex.norm_mul_sin_arg ξ
    rw [← hr,← hi]
    ring
  rw [planePhase,hinner,Real.fourierChar_apply]
  simp only [circleOscillation]
  congr 1
  push_cast
  ring
lemma circleSymbol_integral (ξ : ℂ) :
    circleSymbol ξ = (2*Real.pi)⁻¹ • ∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t := by
  have hp : Function.Periodic (circleOscillation (2*Real.pi*‖ξ‖)) (2*Real.pi) := by
    intro t
    simp only [circleOscillation,Real.cos_add_two_pi]
  rw [circleSymbol,angularMeasure,AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage (2*Real.pi) 0]
  congr 1
  simp_rw [circlePhase_real]
  rw [intervalIntegral.integral_comp_sub_right]
  simpa [sub_eq_add_neg,add_comm] using hp.intervalIntegral_add_eq (-(Complex.arg ξ)) 0
lemma circleSymbol_sq_bound (ξ : ℂ) : ‖circleSymbol ξ‖^2 ≤ 400/(1+‖ξ‖) := by
  have hn : 0≤‖ξ‖ := norm_nonneg _
  by_cases hs : ‖ξ‖≤1
  · have hb := circleSymbol_norm_le_one ξ
    apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
    nlinarith [norm_nonneg (circleSymbol ξ)]
  have hr : 1≤2*Real.pi*‖ξ‖ := by nlinarith [Real.pi_gt_three]
  have hb := circleOscillation_full hr
  rw [circleSymbol_integral,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (by positivity))]
  have hsqr := Real.sq_sqrt (by positivity : 0≤2*Real.pi*‖ξ‖)
  have hsqrt : 0<Real.sqrt (2*Real.pi*‖ξ‖) := Real.sqrt_pos.mpr (by positivity)
  have hlow : 0<2*Real.pi := by positivity
  have hq := (le_div_iff₀ hsqrt).mp hb
  have hpos := norm_nonneg (∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t)
  have hq2 : (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖ * Real.sqrt (2*Real.pi*‖ξ‖))^2 ≤ (4*(1+Real.pi))^2 :=
    pow_le_pow_left₀ (mul_nonneg hpos hsqrt.le) hq 2
  apply (le_div_iff₀ (by positivity : 0<1+‖ξ‖)).mpr
  rw [mul_pow,hsqr] at hq2
  have hpi : Real.pi<4 := Real.pi_lt_four
  have hN : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 * ‖ξ‖ ≤ 100 := by
    have hmul := mul_nonneg (sub_nonneg.mpr Real.pi_gt_three.le)
      (mul_nonneg (sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)) hn)
    nlinarith [Real.pi_gt_three]
  rw [mul_pow,inv_pow]
  have hN' : ‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖^2 ≤ 100 := by
    nlinarith [sq_nonneg (‖∫ t in (0:ℝ)..(2*Real.pi), circleOscillation (2*Real.pi*‖ξ‖) t‖)]
  rw [← div_eq_inv_mul,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hlow)]
  nlinarith [Real.pi_gt_three]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneSpectrum_CircleOperator
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeTranslate_continuous (g : ComplexPlaneL2) : Continuous (fun h => planeTranslate h g) := by
  let f : C(ℂ,C(ℂ,ℂ)) := (ContinuousMap.mk (fun p : ℂ × ℂ => p.2+p.1) (by fun_prop)).curry
  exact continuous_const.compMeasurePreservingLp f.continuous (fun h => measurePreserving_add_right volume h) (by simp)
lemma circleTranslate_integrable (g : ComplexPlaneL2) : Integrable (fun t => planeTranslate (direction t) g) angularMeasure :=
  Integrable.of_bound ((planeTranslate_continuous g).comp direction_continuous).aestronglyMeasurable ‖g‖
    (Eventually.of_forall fun t => (planeTranslate (direction t)).norm_map g |>.le)
lemma circleOperator_ae (g : ComplexPlaneL2) :
    circleOperator g =ᵐ[volume] fun x => ∫ t, g (x+direction t) ∂angularMeasure := by
  let F : ℂ × Angles → ℂ := fun p => g (p.1+direction p.2)
  have hF : StronglyMeasurable F := (Lp.stronglyMeasurable g).comp_measurable
    (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
  have hg2 : Integrable (fun x => ‖g x‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable g)).mp (Lp.memLp g)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    apply (integrable_prod_iff' (hF.norm.pow 2).aestronglyMeasurable).mpr
    constructor
    · exact Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).integrable_comp_of_integrable hg2
    · have he : (fun t => ∫ x, ‖‖F (x,t)‖^2‖ ∂volume) = fun _ => ∫ x, ‖g x‖^2 ∂volume := by
        funext t
        simp only [Real.norm_eq_abs,abs_sq,F]
        change (∫ x : ℂ, (fun y => ‖g y‖^2) (x+direction t)) = _
        exact (measurePreserving_add_right volume (direction t)).integral_comp
          (Homeomorph.addRight (direction t)).measurableEmbedding (fun y : ℂ => ‖g y‖^2)
      simp only [Pi.pow_apply]
      rw [he]
      exact integrable_const _
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => planeTranslate (direction t) g) (circleTranslate_integrable g)
    (Eventually.of_forall fun t => planeTranslate_ae (direction t) g)
  have ha : circleOperator g = (ProbabilityL2.average_memLp volume angularMeasure hF hi).toLp (ProbabilityL2.average angularMeasure F) := h.symm
  rw [ha]
  exact MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi)
lemma circleMultiplier_ae (g : ComplexPlaneL2) :
    circleMultiplier g =ᵐ[volume] fun x => circleSymbol x*g x := Multiplier.clm_ae _ _ _ _ _
lemma fourier_circleOperator (g : ComplexPlaneL2) : 𝓕 (circleOperator g) = circleMultiplier (𝓕 g) := by
  let F : ℂ × Angles → ℂ := fun p => planePhase (direction p.2) p.1 * 𝓕 g p.1
  have hF : StronglyMeasurable F := by
    have h : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h.stronglyMeasurable.mul ((Lp.stronglyMeasurable (𝓕 g)).comp_measurable measurable_fst)
  have hi : Integrable (fun p => ‖F p‖^2) (volume.prod angularMeasure) := by
    have he : (fun p => ‖F p‖^2) = fun p => ‖𝓕 g p.1‖^2 := by
      funext p
      simp only [F,norm_mul,planePhase_norm,one_mul]
    rw [he]
    exact ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp
      (Lp.memLp (𝓕 g))).comp_fst angularMeasure
  have hG : Integrable (fun t => 𝓕 (planeTranslate (direction t) g)) angularMeasure :=
    (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integrable_comp
      (circleTranslate_integrable g)
  have h := ProbabilityL2.average_toLp_integral volume angularMeasure hF hi
    (fun t => 𝓕 (planeTranslate (direction t) g)) hG (Eventually.of_forall fun t => by
      rw [fourier_planeTranslate]
      exact phaseMultiplier_ae (direction t) (𝓕 g))
  have hc := (Lp.fourierTransformₗᵢ ℂ ℂ).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
    (circleTranslate_integrable g)
  change (∫ t, 𝓕 (planeTranslate (direction t) g) ∂angularMeasure) = 𝓕 (circleOperator g) at hc
  rw [← hc,← h]
  apply Lp.ext
  filter_upwards [MemLp.coeFn_toLp (ProbabilityL2.average_memLp volume angularMeasure hF hi),
    circleMultiplier_ae (𝓕 g)] with x hx hy
  rw [hx,hy]
  exact integral_mul_const (𝓕 g x) (fun t => planePhase (direction t) x)
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology
namespace EuclideanFiveColor
lemma planePhase_sub_bound (h ξ : ℂ) : ‖1-planePhase h ξ‖ ≤ 8*‖h‖*‖ξ‖ := by
  have he : planePhase h ξ = Complex.exp (Complex.I * (2*Real.pi*inner ℝ h ξ : ℝ)) := by
    rw [planePhase,Real.fourierChar_apply,mul_comm Complex.I]
  rw [he,norm_sub_rev]
  apply (Real.norm_exp_I_mul_ofReal_sub_one_le (x := 2*Real.pi*inner ℝ h ξ)).trans
  rw [Real.norm_eq_abs,abs_mul,abs_of_pos (by positivity : 0<2*Real.pi)]
  have hi := abs_real_inner_le_norm h ξ
  have hp := mul_nonneg (norm_nonneg h) (norm_nonneg ξ)
  calc
    _ ≤ 2*Real.pi*(‖h‖*‖ξ‖) := mul_le_mul_of_nonneg_left hi (by positivity)
    _ ≤ 8*‖h‖*‖ξ‖ := by nlinarith [Real.pi_lt_four]
lemma planePhase_sub_bound_two (h ξ : ℂ) : ‖1-planePhase h ξ‖≤2 := by
  have hi := norm_sub_le (1:ℂ) (planePhase h ξ)
  simpa only [norm_one,planePhase_norm,one_add_one_eq_two] using hi

lemma circleDifferenceRatio_nonneg (h ξ : ℂ) : 0 ≤ circleDifferenceRatio h ξ := by
  unfold circleDifferenceRatio
  positivity
lemma circleDifferenceRatio_small (h ξ : ℂ) :
    circleDifferenceRatio h ξ ≤ 64*‖h‖*‖ξ‖^2 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hb := planePhase_sub_bound h ξ
  have hc := circleSymbol_norm_le_one ξ
  have hc2 : ‖circleSymbol ξ‖^2 ≤ 1 := by nlinarith [norm_nonneg (circleSymbol ξ)]
  have hb2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  unfold circleDifferenceRatio
  apply (div_le_iff₀ hh0).mpr
  calc
    _ ≤ ‖1-planePhase h ξ‖^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hc2) (sq_nonneg ‖1-planePhase h ξ‖)]
    _ ≤ (8*‖h‖*‖ξ‖)^2 := hb2
    _ = _ := by ring
lemma circleDifferenceRatio_bound (h ξ : ℂ) : circleDifferenceRatio h ξ ≤ 25600 := by
  by_cases hh : h=0
  · simp [hh,circleDifferenceRatio]
  have hh0 : 0<‖h‖ := norm_pos_iff.mpr hh
  have hn : 0<1+‖ξ‖ := by positivity
  have hc := (le_div_iff₀ hn).mp (circleSymbol_sq_bound ξ)
  by_cases hs : ‖h‖*‖ξ‖≤1
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound h ξ) 2
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    have hs' : ‖h‖ * ‖ξ‖^2 ≤ ‖ξ‖ := by nlinarith [mul_nonneg (sub_nonneg.mpr hs) (norm_nonneg ξ)]
    have hc' : ‖circleSymbol ξ‖^2 * ‖ξ‖ ≤ 400 := by nlinarith [sq_nonneg ‖circleSymbol ξ‖]
    have hb : ‖circleSymbol ξ‖^2 * (‖h‖ * ‖ξ‖^2) ≤ 400 :=
      (mul_le_mul_of_nonneg_left hs' (sq_nonneg _)).trans hc'
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hb' := mul_le_mul_of_nonneg_left hb (by positivity : 0≤64*‖h‖)
    nlinarith
  · have hb2 := pow_le_pow_left₀ (norm_nonneg _) (planePhase_sub_bound_two h ξ) 2
    have hc' : ‖circleSymbol ξ‖^2 ≤ 400*‖h‖ := by
      have hmul := mul_le_mul_of_nonneg_left hc (norm_nonneg h)
      have hi := mul_nonneg (sq_nonneg ‖circleSymbol ξ‖)
        (sub_nonneg.mpr (le_of_lt (lt_of_not_ge hs)))
      nlinarith
    unfold circleDifferenceRatio
    apply (div_le_iff₀ hh0).mpr
    have hmul := mul_le_mul_of_nonneg_left hb2 (sq_nonneg ‖circleSymbol ξ‖)
    nlinarith
lemma circleDifferenceRatio_tendsto (ξ : ℂ) :
    Tendsto (fun h => circleDifferenceRatio h ξ) (𝓝 0) (𝓝 0) := by
  apply squeeze_zero (fun h => circleDifferenceRatio_nonneg h ξ)
    (fun h => circleDifferenceRatio_small h ξ)
  simpa using ((continuous_norm.tendsto (0:ℂ)).const_mul 64).mul_const (‖ξ‖^2)
lemma circleDifferenceRatio_measurable (h : ℂ) : StronglyMeasurable (circleDifferenceRatio h) := by
  unfold circleDifferenceRatio
  have hc : StronglyMeasurable circleSymbol := by
    have h' : Continuous (fun p : ℂ × Angles => planePhase (direction p.2) p.1) := by
      unfold planePhase
      exact (continuous_subtype_val.comp Real.continuous_fourierChar).comp
        ((direction_continuous.comp continuous_snd).inner continuous_fst)
    exact h'.stronglyMeasurable.integral_prod_right'
  exact ((hc.norm.pow 2).mul ((continuous_const.sub (planePhase_continuous h)).stronglyMeasurable.norm.pow 2)).div stronglyMeasurable_const
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory Filter Topology FourierTransform
namespace EuclideanFiveColor
lemma planeL2_norm_sq (g : ComplexPlaneL2) : ‖g‖^2 = ∫ x, ‖g x‖^2 ∂volume := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]
lemma circleDifference_norm_sq (g : ComplexPlaneL2) (h : ℂ) :
    ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖ =
      ∫ ξ, circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2 ∂volume := by
  have hn := (Lp.fourierTransformₗᵢ ℂ ℂ).norm_map (circleOperator (g-planeTranslate h g))
  change ‖𝓕 (circleOperator (g-planeTranslate h g))‖ = _ at hn
  rw [← hn, fourier_circleOperator]
  have hs : 𝓕 (g-planeTranslate h g) = 𝓕 g - phaseMultiplier h (𝓕 g) := by
    change (Lp.fourierTransformₗᵢ ℂ ℂ) (g-planeTranslate h g) = _
    rw [map_sub]
    exact congrArg (fun f => 𝓕 g-f) (fourier_planeTranslate h g)
  rw [hs,planeL2_norm_sq,← integral_div]
  apply integral_congr_ae
  filter_upwards [circleMultiplier_ae (𝓕 g-phaseMultiplier h (𝓕 g)),
    Lp.coeFn_sub (𝓕 g) (phaseMultiplier h (𝓕 g)), phaseMultiplier_ae h (𝓕 g)] with ξ hc hs hp
  rw [hc,hs,Pi.sub_apply,hp]
  have he : 𝓕 g ξ-planePhase h ξ*𝓕 g ξ = (1-planePhase h ξ)*𝓕 g ξ := by ring
  rw [he,norm_mul,norm_mul]
  unfold circleDifferenceRatio
  ring
lemma circle_smoothing_L2 (g : ComplexPlaneL2) :
    Tendsto (fun h : ℂ => ‖circleOperator (g-planeTranslate h g)‖^2 / ‖h‖)
      (𝓝 0) (𝓝 0) := by
  simp_rw [circleDifference_norm_sq]
  have hg : Integrable (fun ξ => ‖𝓕 g ξ‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (𝓕 g))).mp (Lp.memLp (𝓕 g))
  have hd := tendsto_integral_filter_of_dominated_convergence
    (fun ξ : ℂ => 25600*‖𝓕 g ξ‖^2)
    (F := fun h ξ => circleDifferenceRatio h ξ * ‖𝓕 g ξ‖^2)
    (f := fun _ => (0:ℝ)) (l := 𝓝 (0:ℂ))
    (Eventually.of_forall fun h =>
      ((circleDifferenceRatio_measurable h).mul ((Lp.stronglyMeasurable (𝓕 g)).norm.pow 2)).aestronglyMeasurable)
    (Eventually.of_forall fun h => Eventually.of_forall fun ξ => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (circleDifferenceRatio_nonneg h ξ) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right (circleDifferenceRatio_bound h ξ) (sq_nonneg _))
    (hg.const_mul 25600)
    (Eventually.of_forall fun ξ => by simpa using (circleDifferenceRatio_tendsto ξ).mul_const (‖𝓕 g ξ‖^2))
  simpa using hd
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
lemma ae_circle_pullback {p : ℂ → Prop} (hp : ∀ᵐ x ∂(volume : Measure ℂ), p x) :
    ∀ᵐ q ∂(volume : Measure ℂ), ∀ᵐ t ∂angularMeasure, p (q+direction t) := by
  have hq : QuasiMeasurePreserving (fun z : ℂ × Angles => z.1+direction z.2)
      (volume.prod angularMeasure) volume :=
    QuasiMeasurePreserving.prod_of_left
      (measurable_fst.add (direction_continuous.measurable.comp measurable_snd))
      (Eventually.of_forall fun t => (measurePreserving_add_right volume (direction t)).quasiMeasurePreserving)
  exact Measure.ae_ae_of_ae_prod (hq.ae hp)
lemma circleOperator_toLp_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) :
    circleOperator (hf.toLp f) =ᵐ[volume] circleAverage f := by
  filter_upwards [circleOperator_ae (hf.toLp f),ae_circle_pullback (MemLp.coeFn_toLp hf)] with q hq he
  exact hq.trans (integral_congr_ae he)
lemma circleOperator_difference_ae {f : ℂ → ℂ} (hf : MemLp f 2 volume) (h : ℂ) :
    circleOperator (hf.toLp f-planeTranslate h (hf.toLp f)) =ᵐ[volume]
      circleAverage (fun q => f q-f (q+h)) := by
  have hfh : MemLp (fun q => f (q+h)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume h)
  have he : (hf.sub hfh).toLp (fun q => f q-f (q+h)) = hf.toLp f-planeTranslate h (hf.toLp f) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (hf.sub hfh),Lp.coeFn_sub (hf.toLp f) (planeTranslate h (hf.toLp f)),
      MemLp.coeFn_toLp hf,planeTranslate_ae h (hf.toLp f),
      (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (MemLp.coeFn_toLp hf)] with q h1 h2 h3 h4 h5
    change ((hf.sub hfh).toLp (fun q => f q-f (q+h))) q = _ at h1
    simp only [h1,h2,Pi.sub_apply,h3,h4,h5]
  rw [← he]
  exact circleOperator_toLp_ae (hf.sub hfh)
lemma colorMass_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (q : ℂ) : 0 ≤ colorMass c i q :=
  integral_nonneg (sampleFn_nonneg c q 1 i)
lemma colorCutoff_sample {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (x q h : ℂ) (R : ℝ)
    (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) (t : Angles) :
    colorCutoff c i x R (q+direction t+h) = if c (q+direction t+h)=i then 1 else 0 := by
  apply Set.indicator_of_mem
  rw [Metric.mem_closedBall,dist_eq_norm]
  have hn := norm_add_le (q-x) (direction t+h)
  have hn' := norm_add_le (direction t) h
  have hd : ‖direction t‖=1 := Circle.norm_coe _
  have hqr : ‖q-x‖<R := by simpa only [Metric.mem_ball,dist_eq_norm] using hq
  rw [show q+direction t+h-x=(q-x)+(direction t+h) by ring]
  linarith
lemma colorCutoff_circleDifference {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c) (i : Fin k)
    (x q h : ℂ) (R : ℝ) (hq : q ∈ Metric.ball x R) (hh : ‖h‖<1) :
    circleAverage (fun y => colorCutoff c i x R y-colorCutoff c i x R (y+h)) q =
      ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  have he (t : Angles) : colorCutoff c i x R (q+direction t)-colorCutoff c i x R (q+direction t+h) =
      ((sampleFn c q 1 i t-sampleFn c (q+h) 1 i t : ℝ) : ℂ) := by
    have h0 := colorCutoff_sample c i x q 0 R hq (by simp) t
    simp only [add_zero] at h0
    rw [h0,colorCutoff_sample c i x q h R hq hh t]
    simp only [sampleFn,Complex.ofReal_one,one_mul,show q+direction t+h=q+h+direction t by ring,
      Complex.ofReal_sub]
    split_ifs <;> simp
  unfold circleAverage
  simp_rw [he,integral_complex_ofReal]
  rw [integral_sub ((sampleFn_memLp c hc q 1 i).integrable (by norm_num))
    ((sampleFn_memLp c hc (q+h) 1 i).integrable (by norm_num))]
  rfl
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Transitions
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k)
lemma transitionSet_measurable (hc : Measurable c) (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    MeasurableSet (transitionSet c i j x R h) := by
  exact measurableSet_ball.inter (((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)).union
    ((measurableSet_eq_fun hc measurable_const).inter
    (measurableSet_eq_fun (hc.comp (measurable_id.add_const h)) measurable_const)))
lemma transitionSet_finite (i j : Fin k) (x : ℂ) (R : ℝ) (h : ℂ) :
    volume (transitionSet c i j x R h) < ⊤ :=
  (measure_mono (fun _ hq => Metric.ball_subset_closedBall hq.1)).trans_lt
    (isCompact_closedBall x R).measure_lt_top
lemma transition_abundance {i j : Fin k} {x : ℂ} (he : TransitionEdge c i j x)
    {R : ℝ} (hR : 0<R) : ∃ a : ℝ, 0<a ∧
      ∃ᶠ h in 𝓝[≠] (0:ℂ), a*‖h‖ < volume.real (transitionSet c i j x R h) := by
  obtain ⟨a,_,ha,hal⟩ := ENNReal.lt_iff_exists_real_btwn.mp (he.2 R hR)
  have ha0 : 0<a := ENNReal.ofReal_pos.mp ha
  refine ⟨a,ha0,?_⟩
  have hf := frequently_lt_of_lt_limsup (h := hal)
  refine (hf.and_eventually self_mem_nhdsWithin).mono ?_
  intro h hh
  have hne : h≠0 := hh.2
  have hn : ENNReal.ofReal ‖h‖≠0 := (ENNReal.ofReal_pos.mpr (norm_pos_iff.mpr hne)).ne'
  have hm : ENNReal.ofReal a*ENNReal.ofReal ‖h‖ < volume (transitionSet c i j x R h) :=
    (ENNReal.lt_div_iff_mul_lt (Or.inl hn) (Or.inl ENNReal.ofReal_ne_top)).mp hh.1
  rw [← ENNReal.ofReal_mul ha0.le] at hm
  exact (ENNReal.ofReal_lt_iff_lt_toReal (mul_nonneg ha0.le (norm_nonneg h)) (transitionSet_finite c i j x R h).ne).mp hm
lemma colorMass_own_zero (hc : Measurable c) (hw : WeakColoring k c) {q : ℂ}
    (hq : Typical c q) (hs : TypicalSampling c q 1) : colorMass c (c q) q=0 := by
  apply integral_eq_zero_of_ae
  filter_upwards [hs.2] with t ht
  simp only [Complex.ofReal_one,one_mul] at ht
  have hn : c (q+direction t)≠c q := by
    intro he
    have hd : ‖q-(q+direction t)‖=1 := by
      simp only [sub_add_cancel_left,norm_neg]
      exact Circle.norm_coe _
    exact weak_density_proper c hc hw (c q) hd hq (by simpa only [Typical,he] using ht)
  simp only [sampleFn,Complex.ofReal_one,one_mul,ite_eq_right hn,Pi.zero_apply]
lemma exists_energy_small {X : Type*} [MeasurableSpace X] (μ : Measure X)
    {T : Set X} (hT : MeasurableSet T) (hfin : μ T < ⊤) {E : X → ℝ}
    (hE : Integrable E μ) (hn : ∀ᵐ q ∂μ, 0≤E q) {P : X → Prop} (hP : ∀ᵐ q ∂μ, P q)
    {d : ℝ} (hi : (∫ q, E q ∂μ) < d*μ.real T) : ∃ q ∈ T, P q ∧ E q<d := by
  by_contra! h
  have : IsFiniteMeasure (μ.restrict T) := ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hge : ∀ᵐ q ∂μ.restrict T, d≤E q := by
    filter_upwards [ae_restrict_mem hT,ae_restrict_of_ae hP] with q hq hp
    exact h q hq hp
  have hl := integral_mono_ae (integrable_const d) hE.restrict hge
  have hr := integral_mono_measure (μ.restrict_le_self (s := T)) hn hE
  have he : (∫ _q in T, d ∂μ)=d*μ.real T := by simp [mul_comm]
  rw [he] at hl
  exact (not_lt_of_ge (hl.trans hr)) hi
end EuclideanFiveColor
end

noncomputable section
open MeasureTheory MeasureTheory.Measure Filter Topology Set
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma colorError_ae (i : Fin k) (x : ℂ) (R : ℝ) {h : ℂ} (hh : ‖h‖<1) :
    ∀ᵐ q ∂(volume : Measure ℂ), q ∈ Metric.ball x R →
      colorError c hc i x R h q = ((colorMass c i q-colorMass c i (q+h) : ℝ) : ℂ) := by
  filter_upwards [circleOperator_difference_ae (colorCutoff_memLp c hc i x R) h] with q hq hB
  exact hq.trans (colorCutoff_circleDifference c hc i x q h R hB hh)
lemma colorError_smoothing (i : Fin k) (x : ℂ) (R : ℝ) :
    Tendsto (fun h : ℂ => ‖colorError c hc i x R h‖^2 / ‖h‖) (𝓝 0) (𝓝 0) :=
  circle_smoothing_L2 _
lemma transition_mass_energy (hw : WeakColoring k c) (i j : Fin k) (x : ℂ) (R : ℝ)
    {h : ℂ} (hh : ‖h‖<1) : ∀ᵐ q ∂(volume : Measure ℂ), q ∈ transitionSet c i j x R h →
      (colorMass c i q+colorMass c j q)^2 ≤
        ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2 := by
  filter_upwards [colorError_ae c hc i x R hh,colorError_ae c hc j x R hh,
    ae_density_actual c hc,ae_typicalSampling c hc (by norm_num : (0:ℝ)<1),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae (ae_density_actual c hc),
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae
      (ae_typicalSampling c hc (by norm_num : (0:ℝ)<1))] with q hi hj hq hqs hqh hqhs hT
  have he_i : ‖colorError c hc i x R h q‖^2=(colorMass c i q-colorMass c i (q+h))^2 := by
    rw [hi hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have he_j : ‖colorError c hc j x R h q‖^2=(colorMass c j q-colorMass c j (q+h))^2 := by
    rw [hj hT.1,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  rw [he_i,he_j]
  have h0 := colorMass_own_zero c hc hw hq hqs
  have h1 := colorMass_own_zero c hc hw hqh hqhs
  rcases hT.2 with ⟨hqi,hqj⟩ | ⟨hqj,hqi⟩
  · rw [hqi] at h0
    rw [hqj] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c i (q+h))]
  · rw [hqj] at h0
    rw [hqi] at h1
    rw [h0,h1]
    nlinarith [sq_nonneg (colorMass c j (q+h))]
include hc in
lemma transition_small_mass (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) {R ε : ℝ} (hR : 0<R) (hε : 0<ε) :
    ∃ q ∈ Metric.ball x R, TypicalSampling c q 1 ∧ colorMass c i q+colorMass c j q<ε := by
  obtain ⟨a,ha,hfreq⟩ := transition_abundance c he hR
  have hlim : Tendsto (fun h : ℂ =>
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖) (𝓝 0) (𝓝 0) := by
    simp only [add_div]
    simpa only [add_zero] using (colorError_smoothing c hc i x R).add (colorError_smoothing c hc j x R)
  have hsmall : ∀ᶠ h in 𝓝[≠] (0:ℂ),
      (‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2)/‖h‖<ε^2*a :=
    (hlim.eventually (gt_mem_nhds (by positivity))).filter_mono nhdsWithin_le_nhds
  have hnorm : ∀ᶠ h in 𝓝[≠] (0:ℂ), ‖h‖<1 :=
    (continuous_norm.tendsto (0:ℂ)).eventually (by simpa using (gt_mem_nhds (by norm_num : (0:ℝ)<1)))
      |>.filter_mono nhdsWithin_le_nhds
  obtain ⟨h,hab,hsm,hhn,hne⟩ := (hfreq.and_eventually (hsmall.and (hnorm.and self_mem_nhdsWithin))).exists
  have hnpos : 0<‖h‖ := norm_pos_iff.mpr hne
  let E : ℂ → ℝ := fun q => ‖colorError c hc i x R h q‖^2+‖colorError c hc j x R h q‖^2
  have hEi : Integrable (fun q => ‖colorError c hc i x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hEj : Integrable (fun q => ‖colorError c hc j x R h q‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).mp (Lp.memLp _)
  have hInt : (∫ q, E q ∂volume) < ε^2*volume.real (transitionSet c i j x R h) := by
    rw [show (∫ q, E q ∂volume) = ‖colorError c hc i x R h‖^2+‖colorError c hc j x R h‖^2 by
      dsimp only [E]
      rw [integral_add hEi hEj,← planeL2_norm_sq,← planeL2_norm_sq]]
    have hs := (div_lt_iff₀ hnpos).mp hsm
    have hab' := mul_lt_mul_of_pos_left hab (sq_pos_of_pos hε)
    nlinarith
  obtain ⟨q,hq,hqs,henergy⟩ := exists_energy_small volume (transitionSet_measurable c hc i j x R h)
    (transitionSet_finite c i j x R h) (hEi.add hEj)
    (Eventually.of_forall fun q => add_nonneg (sq_nonneg _) (sq_nonneg _))
    ((ae_typicalSampling c hc (by norm_num : (0:ℝ)<1)).and (transition_mass_energy c hc hw i j x R hhn)) hInt
  refine ⟨q,hq.1,hqs.1,?_⟩
  have hm := hqs.2 hq
  change E q<ε^2 at henergy
  change (colorMass c i q+colorMass c j q)^2≤E q at hm
  nlinarith
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
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {k : ℕ} (c : ℂ → Fin k) (hc : Measurable c)
lemma inner_oneL2_integral (f : RealL2 angularMeasure) :
    ⟪f,oneL2 angularMeasure⟫ = ∫ t, f t ∂angularMeasure := by
  rw [real_inner_comm]
  exact (L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top angularMeasure Set.univ) f).trans
    (by simp)
lemma sample_inner_one (i : Fin k) (q : ℂ) :
    ⟪sample c hc q 1 i,oneL2 angularMeasure⟫ = colorMass c i q := by
  rw [inner_oneL2_integral]
  exact integral_congr_ae (sample_ae c hc q 1 i)
lemma transition_avoiding_trace (hw : WeakColoring k c) {i j : Fin k} {x : ℂ}
    (he : TransitionEdge c i j x) :
    ∃ b : TraceVector k, IsTrace c hc x b ∧ traceValue b i=0 ∧ traceValue b j=0 := by
  obtain ⟨q,hq⟩ := Classical.axiomOfChoice (fun n : ℕ => transition_small_mass c hc hw he
    (R := 1/((n:ℝ)+1)) (ε := 1/((n:ℝ)+1)) (by positivity) (by positivity))
  have hqt : Tendsto q atTop (𝓝 x) := by
    rw [tendsto_iff_dist_tendsto_zero]
    apply squeeze_zero (fun n => dist_nonneg)
      (fun n => (hq n).1.le)
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨b,_,φ,hφ,hb⟩ := (isCompact_univ : IsCompact (Set.univ : Set (TraceVector k))).isSeqCompact.subseq_of_frequently_in
    (Eventually.frequently (Eventually.of_forall fun n => Set.mem_univ (sampleCode c hc (q n) 1)))
  have htrace : IsTrace c hc x b := trace_of_realization c hc
    (fun n => (hq (φ n)).2.1) (hqt.comp hφ.tendsto_atTop) tendsto_const_nhds hb
  have hmass (a : Fin k) (ha : a=i ∨ a=j) : ∫ t, traceValue b a t ∂angularMeasure = 0 := by
    have ht := (traceCode_tendsto_iff.mp hb) a (oneL2 angularMeasure)
    simp only [Function.comp_apply,traceValue_sampleCode,sample_inner_one] at ht
    rw [inner_oneL2_integral] at ht
    have ht' : Tendsto (fun n => colorMass c a (q n)) atTop (𝓝 0) := by
      apply squeeze_zero (fun n => colorMass_nonneg c a (q n)) (fun n => ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      rcases ha with rfl | rfl
      · exact (le_add_of_nonneg_right (colorMass_nonneg c j (q n))).trans (hq n).2.2.le
      · exact (le_add_of_nonneg_left (colorMass_nonneg c i (q n))).trans (hq n).2.2.le
    exact tendsto_nhds_unique ht (ht'.comp hφ.tendsto_atTop)
  have hzero (a : Fin k) (ha : a=i ∨ a=j) : traceValue b a=0 := by
    apply Lp.ext
    have hi : Integrable (traceValue b a) angularMeasure := (Lp.memLp _).integrable (by norm_num)
    have hz := (integral_eq_zero_iff_of_nonneg_ae ((trace_bounds c hc htrace).1 a) hi).mp (hmass a ha)
    exact hz.trans (Lp.coeFn_zero ℝ 2 angularMeasure).symm
  exact ⟨b,htrace,hzero i (Or.inl rfl),hzero j (Or.inr rfl)⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PaletteDensity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd _root_.OAI.EuclideanFiveColor.anglesNontrivial _root_.OAI.EuclideanFiveColor.angularMeasure_nullSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
namespace EuclideanFiveColor
lemma angleMk_quasiMeasurePreserving :
    Measure.QuasiMeasurePreserving ((↑) : ℝ → Angles) volume angularMeasure := by
  have hm : Measurable ((↑) : ℝ → Angles) := (AddCircle.measurePreserving_mk (2*Real.pi) 0).measurable
  refine ⟨hm,Measure.AbsolutelyContinuous.mk (fun A hA hz => ?_)⟩
  rw [Measure.map_apply hm hA]
  have hzv : (volume : Measure Angles) A=0 := by
    rw [AddCircle.volume_eq_smul_haarAddCircle,Measure.smul_apply]
    change ENNReal.ofReal (2*Real.pi) * angularMeasure A=0
    rw [hz,mul_zero]
  have hh (n : ℤ) : volume (((↑) : ℝ → Angles) ⁻¹' A ∩
      Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)))=0 := by
    have h := (AddCircle.measurePreserving_mk (2*Real.pi) (n • (2*Real.pi))).quasiMeasurePreserving.preimage_null hzv
    rw [Measure.restrict_apply' measurableSet_Ioc] at h
    simpa only [add_zsmul,one_zsmul] using h
  have hcov := iUnion_Ioc_zsmul (by positivity : 0 < 2*Real.pi)
  have he : ((↑) : ℝ → Angles) ⁻¹' A = ⋃ n : ℤ,
      ((↑) : ℝ → Angles) ⁻¹' A ∩ Ioc (n • (2*Real.pi)) ((n+1) • (2*Real.pi)) := by
    rw [← inter_iUnion,hcov,inter_univ]
  rw [he]
  exact measure_iUnion_null hh
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_FourContinuity
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_avoiding_traces (hw : WeakColoring 5 c) {x : ℂ} (hx : FourCenter c x) :
    ∃ b : Fin 4 → TraceVector 5, (∀e,IsTrace c hc x (b e)) ∧
      ∀e,∀i∈fourEdge e,traceValue (b e) i=0 := by
  have hh (i j : Fin 5) (he : TransitionEdge c i j x) :
      ∃ b : TraceVector 5, IsTrace c hc x b ∧ ∀a∈({i,j} : Finset (Fin 5)),traceValue b a=0 := by
    obtain ⟨b,hb,hi,hj⟩ := transition_avoiding_trace c hc hw he
    refine ⟨b,hb,?_⟩
    intro a ha
    simp only [Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> assumption
  have he (e : Fin 4) : ∃ b : TraceVector 5, IsTrace c hc x b ∧ ∀i∈fourEdge e,traceValue b i=0 := by
    fin_cases e
    · exact hh 0 1 hx.1
    · exact hh 1 2 hx.2.1
    · exact hh 2 3 hx.2.2.1
    · exact hh 3 0 hx.2.2.2
  choose b hb hz using he
  exact ⟨b,hb,hz⟩
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable {Y : Type*} [MeasurableSpace Y] {μ : Measure Y} [IsProbabilityMeasure μ]
lemma indL2_ae (A : Set Y) (hA : MeasurableSet A) :
    indL2 (μ := μ) A hA =ᵐ[μ] A.indicator (fun _ => (1:ℝ)) := indicatorConstLp_coeFn
lemma indL2_nonneg (A : Set Y) (hA : MeasurableSet A) : 0≤ᵐ[μ] indL2 (μ := μ) A hA := by
  filter_upwards [indL2_ae (μ := μ) A hA] with t ht
  rw [ht]
  exact indicator_nonneg (fun _ _ => zero_le_one) _
lemma indL2_le_one (A : Set Y) (hA : MeasurableSet A) : indL2 (μ := μ) A hA≤ᵐ[μ] (fun _ => (1:ℝ)) := by
  filter_upwards [indL2_ae (μ := μ) A hA] with t ht
  rw [ht]
  exact indicator_le_self' (fun _ _ => zero_le_one) _
lemma indL2_norm (A : Set Y) (hA : MeasurableSet A) : ‖indL2 (μ := μ) A hA‖≤1 := by
  have hh : ∀ᵐt∂μ,‖indL2 (μ := μ) A hA t‖≤1 := by
    filter_upwards [indL2_nonneg (μ := μ) A hA,indL2_le_one (μ := μ) A hA] with t ht hu
    rwa [Real.norm_eq_abs,abs_of_nonneg ht]
  simpa [measureUnivNNReal] using Lp.norm_le_of_ae_bound (by norm_num : (0:ℝ)≤1) hh
lemma indL2_weak_L1 {A : ℕ → Set Y} (hA : ∀n,MeasurableSet (A n)) {B : Set Y} (hB : MeasurableSet B)
    (hw : ∀v : RealL2 μ,Tendsto (fun n => ⟪indL2 (A n) (hA n),v⟫) atTop (𝓝 ⟪indL2 B hB,v⟫)) :
    Tendsto (fun n => ∫t,‖(A n).indicator (fun _ => (1:ℝ)) t-B.indicator (fun _ => (1:ℝ)) t‖ ∂μ) atTop (𝓝 0) := by
  have hone (w : RealL2 μ) : ⟪w,oneL2 μ⟫=∫t,w t ∂μ := by
    rw [real_inner_comm]
    simpa only [oneL2,setIntegral_univ] using
      L2.inner_indicatorConstLp_one MeasurableSet.univ (measure_ne_top μ univ) w
  have hBB : ⟪indL2 (μ := μ) B hB,indL2 B hB⟫=⟪indL2 (μ := μ) B hB,oneL2 μ⟫ := by
    rw [hone,L2.inner_def]
    apply integral_congr_ae
    filter_upwards [indL2_ae (μ := μ) B hB] with t ht
    rw [ht]
    by_cases hb : t∈B <;> simp [hb]
  have he (n : ℕ) : (∫t,‖(A n).indicator (fun _ => (1:ℝ)) t-B.indicator (fun _ => (1:ℝ)) t‖ ∂μ) =
      ⟪indL2 (μ := μ) (A n) (hA n),oneL2 μ⟫+⟪indL2 (μ := μ) B hB,oneL2 μ⟫-
      2*⟪indL2 (μ := μ) (A n) (hA n),indL2 (μ := μ) B hB⟫ := by
    rw [hone,hone,L2.inner_def,← integral_const_mul,← integral_add,
      ← integral_sub]
    · apply integral_congr_ae
      filter_upwards [indL2_ae (μ := μ) (A n) (hA n),indL2_ae (μ := μ) B hB] with t ht hu
      rw [ht,hu]
      by_cases ha : t∈A n <;> by_cases hb : t∈B <;> norm_num [ha,hb]
    · exact ((Lp.memLp _).integrable (by norm_num)).add ((Lp.memLp _).integrable (by norm_num))
    · exact (L2.integrable_inner _ _).const_mul 2
    · exact (Lp.memLp _).integrable (by norm_num)
    · exact (Lp.memLp _).integrable (by norm_num)
  simp_rw [he]
  have ht := ((hw (oneL2 μ)).add_const ⟪indL2 (μ := μ) B hB,oneL2 μ⟫).sub
    ((hw (indL2 (μ := μ) B hB)).const_mul 2)
  rw [hBB,show ⟪indL2 (μ := μ) B hB, oneL2 μ⟫+⟪indL2 (μ := μ) B hB,oneL2 μ⟫-
    2*⟪indL2 (μ := μ) B hB,oneL2 μ⟫=0 by ring] at ht
  exact ht
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_state_subseq_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) :
    ∃φ : ℕ → ℕ,StrictMono φ ∧ ∀s,Tendsto (fun n => fourStateDistance c hc (x (φ n)) y s) atTop (𝓝 0) := by
  obtain ⟨f,φ,hφ,_,hf⟩ := exists_finite_weak_subseq (fun n s => fourStateL2 c hc (x n) s) 1
    (fun _ _ => indL2_norm _ _)
  choose b hb hz using fun n => four_avoiding_traces c hc hw (hx (φ n))
  obtain ⟨a,_,ψ,hψ,ha⟩ := (isCompact_univ : IsCompact (univ : Set (Fin 4 → TraceVector 5))).isSeqCompact
    (fun n => mem_univ (b n))
  have hid := four_weak_limit_identify c hc hw (fun n => hx (φ (ψ n))) hy
    (hxt.comp (hφ.tendsto_atTop.comp hψ.tendsto_atTop))
    (fun s v => (hf s v).comp hψ.tendsto_atTop) (fun n => b (ψ n)) a
    (fun n => hb (ψ n)) (fun n => hz (ψ n))
    (fun e => (continuous_apply e).tendsto a |>.comp ha)
  refine ⟨φ∘ψ,hφ.comp hψ,?_⟩
  intro s
  apply indL2_weak_L1 (fun n => measurableSet_eq_fun (fourState_measurable c hc (x (φ (ψ n)))) measurable_const)
    (measurableSet_eq_fun (fourState_measurable c hc y) measurable_const)
  intro v
  have hh := (hf s v).comp hψ.tendsto_atTop
  rw [hid s] at hh
  exact hh
lemma four_state_continuity (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) (s : Fin 3) :
    Tendsto (fun n => fourStateDistance c hc (x n) y s) atTop (𝓝 0) := by
  by_contra hn
  rw [Metric.tendsto_atTop] at hn
  push Not at hn
  obtain ⟨ε,hε,he⟩ := hn
  choose m hm using he
  have hmt : Tendsto m atTop atTop := tendsto_atTop_mono (fun n => (hm n).1) tendsto_id
  obtain ⟨φ,hφ,ht⟩ := four_state_subseq_continuity c hc hw (fun n => hx (m n)) hy (hxt.comp hmt)
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp (ht s) ε hε
  exact (hm (φ N)).2.not_gt (hN N le_rfl)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
open scoped NNReal
namespace EuclideanFiveColor
lemma angleMk_compact_bound {E : Set ℝ} (hE : IsCompact E) :
    ∃ C : ℝ≥0, (volume.restrict E).map ((↑) : ℝ → Angles)≤(C:ENNReal) • angularMeasure := by
  obtain ⟨F,hF⟩ := hE.elim_finite_subcover (fun a : ℝ => Ioo (a-Real.pi) (a+Real.pi))
    (fun _ => isOpen_Ioo) (fun a _ => mem_iUnion.mpr ⟨a,by constructor <;> linarith [Real.pi_pos]⟩)
  let C : ℝ≥0 := ⟨(F.card:ℝ)*(2*Real.pi),by positivity⟩
  refine ⟨C,Measure.le_iff.mpr (fun A hA => ?_)⟩
  rw [Measure.map_apply angleMk_quasiMeasurePreserving.measurable hA,
    Measure.restrict_apply (angleMk_quasiMeasurePreserving.measurable hA),Measure.smul_apply,smul_eq_mul]
  have hsub : ((↑) : ℝ → Angles) ⁻¹' A∩E ⊆
      ⋃a∈F,((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi) := by
    intro t ht
    obtain ⟨a,ha,h₁,h₂⟩ := mem_iUnion₂.mp (hF ht.2)
    exact mem_iUnion₂.mpr ⟨a,ha,ht.1,h₁,by linarith⟩
  calc
    _ ≤ volume (⋃a∈F,((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi)) := measure_mono hsub
    _ ≤ ∑a∈F,volume (((↑) : ℝ → Angles) ⁻¹' A∩Ioc (a-Real.pi) ((a-Real.pi)+2*Real.pi)) := measure_biUnion_finset_le F _
    _ = ∑_a∈F,(volume : Measure Angles) A := by
      apply Finset.sum_congr rfl
      intro a _
      exact (AddCircle.add_projection_respects_measure (2*Real.pi) (a-Real.pi) hA).symm
    _ = (C:ENNReal)*angularMeasure A := by
      rw [AddCircle.volume_eq_smul_haarAddCircle]
      simp only [Measure.smul_apply,smul_eq_mul,Finset.sum_const,nsmul_eq_mul]
      change (F.card:ENNReal)*(ENNReal.ofReal (2*Real.pi)*angularMeasure A)=_
      rw [← mul_assoc]
      congr 1
      rw [show (C:ENNReal)=ENNReal.ofReal ((F.card:ℝ)*(2*Real.pi)) from ENNReal.ofReal_coe_nnreal.symm]
      rw [ENNReal.ofReal_mul (by positivity : 0≤(F.card:ℝ)),ENNReal.ofReal_natCast]
lemma angular_compact_L1 {f : ℕ → Angles → ℝ} {g : Angles → ℝ}
    (hf : ∀n,Integrable (f n) angularMeasure) (hg : Integrable g angularMeasure)
    (ht : Tendsto (fun n => ∫t,‖f n t-g t‖ ∂angularMeasure) atTop (𝓝 0))
    {E : Set ℝ} (hE : IsCompact E) :
    Tendsto (fun n => ∫t in E,‖f n (t : Angles)-g (t : Angles)‖) atTop (𝓝 0) := by
  obtain ⟨C,hC⟩ := angleMk_compact_bound hE
  apply squeeze_zero (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => integral_norm_comp_le angleMk_quasiMeasurePreserving.measurable hC ((hf n).sub hg))
  simpa only [mul_zero,Pi.sub_apply] using ht.const_mul (C:ℝ)
end EuclideanFiveColor
end

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
variable (c : ℂ → Fin 5) (hc : Measurable c)
lemma four_realState_continuity_oai (hw : WeakColoring 5 c)
    {x : ℕ → ℂ} {y : ℂ} (hx : ∀n,FourCenter c (x n)) (hy : FourCenter c y)
    (hxt : Tendsto x atTop (𝓝 y)) (s : Fin 3) {E : Set ℝ} (hE : IsCompact E) :
    Tendsto (fun n => ∫t in E,‖(fourRealState c hc (x n) s).indicator (fun _ => (1:ℝ)) t-
      (fourRealState c hc y s).indicator (fun _ => (1:ℝ)) t‖) atTop (𝓝 0) := by
  exact angular_compact_L1
    (fun n => (integrable_const (1:ℝ)).indicator (measurableSet_eq_fun (fourState_measurable c hc (x n)) measurable_const))
    ((integrable_const (1:ℝ)).indicator (measurableSet_eq_fun (fourState_measurable c hc y) measurable_const))
    (four_state_continuity c hc hw hx hy hxt s) hE
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.four_realState_continuity_oai := @OAI.EuclideanFiveColor.four_realState_continuity_oai
