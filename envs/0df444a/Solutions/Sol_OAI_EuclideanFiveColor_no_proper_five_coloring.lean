-- Prove2me | solution 1 for OAI.EuclideanFiveColor.no_proper_five_coloring
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T13:07:29.06296+00:00
-- url     : https://prove2.me/submissions/e121d4dc-cb41-46fd-bc16-bba99e59bce1

import Mathlib
import Definitions.Def_EuclideanFiveColor
import Definitions.Def_OAIQ5T4002
import Theorems.Thm_OAI_EuclideanFiveColor_fullApprox_exists
import Theorems.Thm_OAI_EuclideanFiveColor_proper_to_borel_weak

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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
lemma direction_exists {u : ℂ} (hu : ‖u‖=1) : ∃ t, direction t=u := by
  let v : Circle := ⟨u,mem_sphere_zero_iff_norm.mpr hu⟩
  obtain ⟨t,ht⟩ := Circle.exp_surjective v
  exact ⟨(t : Angles),by simpa only [direction_real] using congrArg Subtype.val ht⟩
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
open scoped RealInnerProductSpace
namespace EuclideanFiveColor
lemma straddle_connected_unit {K : Set ℂ} (hK : IsPreconnected K) {z : ℂ} (hz : z∈Straddle K) :
    ∃p∈K,dist z p=1 := by
  obtain ⟨p,hp,q,hq,hp1,hq1⟩ := hz
  exact hK.intermediate_value hp hq (continuous_const.dist continuous_id).continuousOn ⟨hp1.le,hq1.le⟩
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskAverages
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma diskLaw_absolutelyContinuous (ε : ℝ) : diskLaw ε ≪ volume :=
  (Measure.restrict_le_self (s := Metric.ball (0:ℂ) ε)).absolutelyContinuous.smul_left _
lemma diskLaw_probability {ε : ℝ} (hε : 0<ε) : IsProbabilityMeasure (diskLaw ε) := by
  constructor
  simp only [diskLaw,Measure.smul_apply,Measure.restrict_apply_univ,smul_eq_mul]
  exact ENNReal.inv_mul_cancel (Metric.measure_ball_pos volume 0 hε).ne'
    ((measure_mono Metric.ball_subset_closedBall).trans_lt (isCompact_closedBall (0:ℂ) ε).measure_lt_top).ne
lemma colorFn_measurable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k) :
    Measurable (colorFn c i) :=
  measurable_one.piecewise (measurableSet_eq_fun hc measurable_const) measurable_zero
lemma colorFn_nonneg {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : 0 ≤ colorFn c i z := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_le_one {k : ℕ} (c : ℂ → Fin k) (i : Fin k) (z : ℂ) : colorFn c i z≤1 := by
  simp only [colorFn]; split_ifs <;> norm_num
lemma colorFn_integrable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k)
    {μ : Measure ℂ} [IsFiniteMeasure μ] (q : ℂ) : Integrable (fun v => colorFn c i (q+v)) μ := by
  apply Integrable.of_bound ((colorFn_measurable hc i).comp (measurable_const.add measurable_id)).aestronglyMeasurable 1
  exact Eventually.of_forall fun v => by
    change ‖colorFn c i (q+v)‖ ≤ 1
    rw [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i (q+v))]
    exact colorFn_le_one c i (q+v)
lemma diskAverage_sum {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) {ε : ℝ} (hε : 0<ε)
    (q : ℂ) : ∑ i,diskAverage c ε i q=1 := by
  have := diskLaw_probability hε
  simp only [diskAverage]
  rw [← integral_finsetSum _ (fun i _ => colorFn_integrable (μ := diskLaw ε) hc i q)]
  simp [colorFn]
lemma colorFn_unit_pair {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {q z : ℂ} (hunit : ‖q-z‖=1) (i : Fin k) :
    ∀ᵐ v ∂(volume : Measure ℂ), colorFn c i (q+v)+colorFn c i (z+v)≤1 := by
  obtain ⟨t,ht⟩ := direction_exists (u := z-q) (by simpa only [norm_sub_rev] using hunit)
  have ha := (measurePreserving_add_left (volume : Measure ℂ) q).quasiMeasurePreserving.ae
    (weak_all_directions c hc hw t)
  filter_upwards [ha] with v hv
  have hne : c (q+v)≠c (z+v) := by
    convert hv using 1
    all_goals try with_reducible_and_instances rfl
    rw [ht]
    congr 1
    ring
  simp only [colorFn]
  split_ifs with h1 h2 h2 <;> try norm_num
  exact False.elim (hne (h1.trans h2.symm))
lemma diskAverage_unit_pair {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (hw : WeakColoring k c)
    {ε : ℝ} (hε : 0<ε) {q z : ℂ} (hunit : ‖q-z‖=1) (i : Fin k) :
    diskAverage c ε i q+diskAverage c ε i z≤1 := by
  have := diskLaw_probability hε
  rw [diskAverage,diskAverage,← integral_add (colorFn_integrable (μ := diskLaw ε) hc i q) (colorFn_integrable (μ := diskLaw ε) hc i z)]
  simpa using integral_mono_ae ((colorFn_integrable (μ := diskLaw ε) hc i q).add (colorFn_integrable (μ := diskLaw ε) hc i z))
    (integrable_const (1:ℝ)) ((diskLaw_absolutelyContinuous ε).ae_le (colorFn_unit_pair hc hw hunit i))
end EuclideanFiveColor
end

noncomputable section
open scoped Classical symmDiff
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma diskAverage_area {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (ε : ℝ)
    (i : Fin k) (q : ℂ) : diskAverage c ε i q=
      volume.real (Metric.ball q ε ∩ {z | c z=i})/volume.real (Metric.ball (0:ℂ) ε) := by
  have he : (fun v : ℂ => q+v) ⁻¹' Metric.ball q ε = Metric.ball 0 ε := by
    ext v
    simp [Metric.mem_ball,dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure ℂ) q).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft q).measurableEmbedding (colorFn c i) (Metric.ball q ε)
  rw [he] at hi
  unfold diskAverage diskLaw
  rw [integral_smul_measure,ENNReal.toReal_inv,hi]
  have hid : colorFn c i=({z | c z=i} : Set ℂ).indicator (fun _ => (1:ℝ)) := by
    funext v
    simp [colorFn,Set.indicator]
  rw [hid]
  rw [setIntegral_indicator (measurableSet_eq_fun hc measurable_const)]
  simp only [integral_const,Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_one,div_eq_mul_inv]
  ring
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_PlanarCovers
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology
namespace PlanarCover
lemma ball_simplyConnected (y : ℂ) {r : ℝ} (hr : 0 < r) :
    IsSimplyConnected (Metric.ball y r) := by
  let := (convex_ball y r).contractibleSpace (Metric.nonempty_ball.mpr hr)
  change SimplyConnectedSpace (Metric.ball y r)
  infer_instance
lemma hit_center {F : ℂ → ℂ} {y : ℂ}
    (hc : ContinuousOn F (Metric.ball y 4))
    (hb : ∀ z ∈ Metric.ball y 4, ‖F z-z‖ ≤ 2) :
    y ∈ F '' Metric.ball y 4 := by
  by_contra hn
  have hzero : 0 ∉ (fun z => F z-y) '' Metric.ball y 4 := by
    rintro ⟨z,hz,he⟩
    apply hn
    exact ⟨z,hz,sub_eq_zero.mp he⟩
  obtain ⟨L,hLc,hL⟩ := Complex.exists_continuousOn_eqOn_exp_comp
    (ball_simplyConnected y (by norm_num : (0:ℝ)<4)) Metric.isOpen_ball
    (hc.sub continuousOn_const) hzero
  let e : ℝ → ℂ := fun t => Complex.exp (t*Complex.I)
  have ec : Continuous e := by fun_prop
  have en (t : ℝ) : ‖e t‖ = 1 := by simp [e,Complex.norm_exp]
  let γ : ℝ → ℂ := fun t => y+3*e t
  have γc : Continuous γ := by fun_prop
  have γmem (t : ℝ) : γ t ∈ Metric.ball y 4 := by
    norm_num [γ,Metric.mem_ball,dist_eq_norm,en]
  let H : ℝ → ℂ := fun t => (F (γ t)-y) / e t
  have Hc : Continuous H := (hc.comp_continuous γc γmem).sub continuous_const |>.div ec (fun t => Complex.exp_ne_zero _)
  have Hnear (t : ℝ) : ‖H t-3‖ ≤ 2 := by
    have he : e t ≠ 0 := Complex.exp_ne_zero _
    have h : H t-3 = (F (γ t)-γ t)/e t := by dsimp [H,γ]; field_simp; ring
    rw [h,norm_div,en,div_one]
    exact hb _ (γmem t)
  have Hpos (t : ℝ) : 0 < (H t).re := by
    have : |(H t-3).re| ≤ 2 := (Complex.abs_re_le_norm (H t-3)).trans (Hnear t)
    have := (abs_le.mp this).1
    norm_num at this
    linarith
  have Hslit (t : ℝ) : H t ∈ Complex.slitPlane := Or.inl (Hpos t)
  have logHc : Continuous (fun t => Complex.log (H t)) :=
    Hc.clog Hslit
  let d : ℝ → ℂ := fun t => L (γ t) - Complex.log (H t) - t*Complex.I
  have dc : Continuous d := ((hLc.comp_continuous γc γmem).sub logHc).sub (by fun_prop)
  have de (t : ℝ) : Complex.exp (d t) = 1 := by
    have hH : H t ≠ 0 := fun hz => by have := Hpos t; simp [hz] at this
    have hLe : Complex.exp (L (γ t)) = F (γ t)-y := hL (γmem t)
    simp only [d,Complex.exp_sub,Complex.exp_log hH,hLe]
    change (F (γ t)-y) / ((F (γ t)-y)/e t) / e t = 1
    have hF : F (γ t)-y ≠ 0 := fun hz => hzero ⟨_,γmem t,hz⟩
    have he : e t ≠ 0 := Complex.exp_ne_zero _
    field_simp
  have hconst : d 0 = d (2*Real.pi) :=
    Complex.isCoveringMap_exp.constOn_of_comp isPreconnected_univ dc.continuousOn
      (fun a _ b _ => Subtype.ext ((de a).trans (de b).symm)) (mem_univ _) (mem_univ _)
  have e0 : e 0 = 1 := by simp [e]
  have e2 : e (2*Real.pi) = 1 := by simp [e,Complex.exp_two_pi_mul_I]
  have γeq : γ (2*Real.pi) = γ 0 := by dsimp [γ]; rw [e0,e2]
  have Heq : H (2*Real.pi) = H 0 := by dsimp [H]; rw [γeq,e0,e2]
  dsimp [d] at hconst
  rw [γeq,Heq] at hconst
  have hi := congrArg Complex.im hconst
  norm_num at hi
  nlinarith [Real.pi_pos]
end PlanarCover
end

noncomputable section
open Set MeasureTheory MeasureTheory.Measure
namespace PlanarCover
lemma affinePair_null (a b : ℂ) : volume (affineSpan ℝ ({a,b} : Set ℂ) : Set ℂ)=0 := by
  apply addHaar_affineSubspace volume
  intro he
  have hd : Submodule.span ℝ ({a-b} : Set ℂ)=⊤ := by
    change Submodule.span ℝ ({a -ᵥ b} : Set ℂ)=⊤
    rw [← vectorSpan_pair ℝ a b,← direction_affineSpan,he]
    exact AffineSubspace.direction_top _ _ _
  have hf := finrank_span_le_card (R := ℝ) ({a-b} : Set ℂ)
  rw [hd,finrank_top,Complex.finrank_real_complex] at hf
  norm_num at hf
lemma hit_center_subtype {Q : Set ℂ} {y : ℂ} (hQ : Metric.ball y 4 ⊆ Q)
    {F : Q → ℂ} (hc : Continuous F) (hb : ∀ z, ‖F z-z.val‖ ≤ 2) :
    y ∈ Set.range F := by
  classical
  let g : ℂ → ℂ := fun z => if hz:z∈Q then F ⟨z,hz⟩ else 0
  have ge (z : ℂ) (hz : z∈Q) : g z=F ⟨z,hz⟩ := dite_eq_left hz
  have hgc : ContinuousOn g (Metric.ball y 4) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have hh := hc.comp (continuous_subtype_val.subtype_mk (fun z : Metric.ball y 4 => hQ z.property))
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    ext z
    exact ge _ (hQ z.property)
  obtain ⟨z,hz,he⟩ := hit_center hgc (fun z hz => by rw [ge _ (hQ hz)]; exact hb _)
  exact ⟨⟨z,hQ hz⟩,by rwa [ge _ (hQ hz)] at he⟩
lemma small_support_pair {ι : Type*} [DecidableEq ι] {s : Finset ι}
    (hs : s.Nonempty) (hc : s.card≤2) : ∃ a b, s ⊆ {a,b} := by
  by_cases h1 : s.card=1
  · obtain ⟨a,rfl⟩ := Finset.card_eq_one.mp h1
    exact ⟨a,a,by simp⟩
  · have h2 : s.card=2 := by have := hs.card_pos; omega
    obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h2
    exact ⟨a,b,Finset.Subset.refl _⟩
lemma barycenter_two {ι : Type*} [Fintype ι] (p : ι → ℂ) (w : ι → ℝ)
    (hn : ∀ i,0≤w i) (hs : ∑ i,w i=1)
    (hcard : (Finset.univ.filter (fun i => w i≠0)).card≤2) :
    ∑ i,w i • p i ∈ ⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ) := by
  classical
  let s := Finset.univ.filter (fun i => w i≠0)
  have hsw : ∑ i ∈ s, w i = ∑ i, w i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    simpa [s] using hi
  have hsv : ∑ i∈s,w i=1 := hsw.trans hs
  have hne : s.Nonempty := by
    by_contra he
    rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty] at hsv
    exact zero_ne_one hsv
  obtain ⟨a,b,hab⟩ := small_support_pair hne hcard
  refine mem_iUnion.mpr ⟨a,mem_iUnion.mpr ⟨b,?_⟩⟩
  have hm := (affineSpan ℝ ({p a,p b} : Set ℂ)).convex.sum_mem
    (z := p) (fun i _ => hn i) hsv (fun i hi => mem_affineSpan ℝ (by
      have hh := hab hi
      simp only [Finset.mem_insert,Finset.mem_singleton] at hh
      rcases hh with rfl|rfl <;> simp))
  have hh : ∑ i ∈ s, w i • p i = ∑ i, w i • p i := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro i _ hi
    have hi0 : w i = 0 := by simpa [s] using hi
    simp [hi0]
  rwa [hh] at hm
lemma finite_partition_impossible {ι : Type*} [Fintype ι] {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (p : ι → ℂ) (w : ι → C(Q,ℝ))
    (hn : ∀ i z,0≤w i z) (hs : ∀ z,∑ i,w i z=1)
    (hm : ∀ z,(Finset.univ.filter (fun i => w i z≠0)).card≤2)
    (hd : ∀ i z, w i z≠0 → ‖p i-z.val‖≤2) : False := by
  classical
  let F : Q → ℂ := fun z => ∑ i,w i z • p i
  have Fc : Continuous F := by fun_prop
  have Fb (z : Q) : ‖F z-z.val‖≤2 := by
    have he : F z-z.val=∑ i,w i z • (p i-z.val) := by
      simp only [smul_sub,Finset.sum_sub_distrib,← Finset.sum_smul,hs,one_smul,F]
    rw [he]
    calc
      ‖∑ i,w i z • (p i-z.val)‖ ≤ ∑ i,‖w i z • (p i-z.val)‖ := norm_sum_le _ _
      _ ≤ ∑ i,w i z*2 := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : w i z=0
        · simp [hi]
        · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hn i z)]
          exact mul_le_mul_of_nonneg_left (hd i z hi) (hn i z)
      _ = 2 := by rw [← Finset.sum_mul,hs]; ring
  have hsub : Metric.ball (0:ℂ) 1 ⊆ Set.range F := by
    intro y hy
    apply hit_center_subtype (F := F) ?_ Fc Fb
    intro z hz
    apply hQ
    rw [Metric.mem_ball,dist_zero_right] at hy ⊢
    have hh := norm_add_le (z-y) y
    rw [sub_add_cancel] at hh
    have hz' : ‖z-y‖<4 := by simpa [Metric.mem_ball,dist_eq_norm] using hz
    exact hh.trans_lt (by linarith)
  have hnull : volume (⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ))=0 :=
    measure_iUnion_null fun a => measure_iUnion_null fun b => affinePair_null _ _
  have hfsub : Set.range F ⊆ ⋃ a, ⋃ b, (affineSpan ℝ ({p a,p b} : Set ℂ) : Set ℂ) := by
    rintro _ ⟨z,rfl⟩
    exact barycenter_two p (fun i => w i z) (fun i => hn i z) (hs z) (hm z)
  have hz := measure_mono_null (hsub.trans hfsub) hnull
  exact (Metric.isOpen_ball.measure_pos volume (Metric.nonempty_ball.mpr (by norm_num : (0:ℝ)<1))).ne' hz
end PlanarCover
end

noncomputable section
open scoped Classical
open Set MeasureTheory
namespace PlanarCover
lemma finite_open_cover_impossible {ι : Type*} [Fintype ι] {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (U : ι → Set Q)
    (ho : ∀ i, IsOpen (U i)) (hcov : ∀ z : Q, ∃ i, z∈U i)
    (hm : ∀ z : Q, (Finset.univ.filter (fun i => z∈U i)).card≤2)
    (hd : ∀ i, ∀ x∈U i, ∀ y∈U i, ‖x.val-y.val‖≤2) : False := by
  classical
  obtain ⟨w,hw⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U ho (by
    intro z _
    exact mem_iUnion.mpr (hcov z))
  have hz0 : (0:ℂ)∈Q := hQ (Metric.mem_ball_self (by norm_num))
  let p : ι → Q := fun i => if h : (U i).Nonempty then h.choose else ⟨0,hz0⟩
  apply finite_partition_impossible hQ (fun i => (p i).val) w (w.nonneg) ?_ ?_ ?_
  · intro z
    simpa only [finsum_eq_sum_of_fintype] using w.sum_eq_one (mem_univ z)
  · intro z
    apply le_trans (Finset.card_le_card ?_) (hm z)
    intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi ⊢
    exact hw i (subset_closure hi)
  · intro i z hz
    have hzu : z∈U i := hw i (subset_closure hz)
    have hp : p i∈U i := by
      dsimp [p]
      rw [dite_eq_left ⟨z,hzu⟩]
      exact Classical.choose_spec _
    exact hd i _ hp z hzu
lemma compact_open_cover_impossible {ι : Type*} {Q : Set ℂ}
    (hQ : Metric.ball (0:ℂ) 5 ⊆ Q) (hQc : IsCompact Q) (U : ι → Set Q)
    (ho : ∀ i, IsOpen (U i)) (hcov : ∀ z : Q, ∃ i, z∈U i)
    (hm : ∀ z : Q, ∀ i j l, z∈U i → z∈U j → z∈U l → i=j ∨ i=l ∨ j=l)
    (hd : ∀ i, ∀ x∈U i, ∀ y∈U i, ‖x.val-y.val‖≤2) : False := by
  classical
  have : CompactSpace Q := isCompact_iff_compactSpace.mp hQc
  obtain ⟨s,hs⟩ := isCompact_univ.elim_finite_subcover U ho (by
    intro z _
    exact mem_iUnion.mpr (hcov z))
  apply finite_open_cover_impossible hQ (fun i : s => U i.val) (fun i => ho i.val) ?_ ?_ ?_
  · intro z
    rcases mem_iUnion.mp (hs (mem_univ z)) with ⟨i,hi⟩
    rcases mem_iUnion.mp hi with ⟨his,hiz⟩
    exact ⟨⟨i,his⟩,hiz⟩
  · intro z
    by_contra! hcard
    obtain ⟨i,hi,j,hj,l,hl,hij,hil,hjl⟩ := Finset.two_lt_card.mp hcard
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hi hj hl
    rcases hm z i.val j.val l.val hi hj hl with h|h|h
    · exact hij (Subtype.ext h)
    · exact hil (Subtype.ext h)
    · exact hjl (Subtype.ext h)
  · intro i
    exact hd i.val
end PlanarCover
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_GraphRealization
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
universe u
namespace EuclideanFiveColor
lemma graphRealization_sum {V : Type u} [Fintype V] {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) : ∑ i,p i=1 := by
  obtain ⟨a,b,_,t,_,rfl⟩ := hp
  simp [graphEdgePoint,graphVertex,Finset.sum_add_distrib]
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Topology MeasureTheory
namespace EuclideanFiveColor
lemma thresholdTotal_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) : 0<thresholdTotal c ε α q := by
  have hs := diskAverage_sum hc hε q
  have hh : 1-5*α ≤ thresholdTotal c ε α q := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 5)))
      (fun i _ => le_max_left (diskAverage c ε i q-α) 0)
    simpa [thresholdTotal,thresholdWeight,Finset.sum_sub_distrib,hs] using hh
  linarith
lemma thresholdMap_pos {c : ℂ → Fin 5} (hc : Measurable c) {ε α : ℝ}
    (hε : 0<ε) (hα : α<1/5) (q : ℂ) (i : Fin 5) :
    0<thresholdMap c ε α q i ↔ α<diskAverage c ε i q := by
  rw [thresholdMap,div_pos_iff_of_pos_right (thresholdTotal_pos hc hε hα q)]
  simp [thresholdWeight]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_ContinuumLimits
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Vanishing exceptional measure is enough: almost every point is outside the
exceptional sets infinitely often. No summability or nesting is required. -/
lemma ae_frequently_notMem_of_measure_tendsto_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {E : ℕ → Set X}
    (hE : Tendsto (fun n => μ (E n)) atTop (𝓝 0)) :
    ∀ᵐ z ∂μ, ∃ᶠ n in atTop, z ∉ E n := by
  let T : ℕ → Set X := fun N => ⋂ n ≥ N, E n
  have hT : ∀ N, μ (T N) = 0 := by
    intro N
    apply le_antisymm _ (by positivity)
    apply ge_of_tendsto hE
    filter_upwards [eventually_ge_atTop N] with n hn
    exact measure_mono (fun z hz => (mem_iInter.mp (mem_iInter.mp hz n)) hn)
  have hn : μ (⋃ N, T N) = 0 := measure_iUnion_null hT
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with z hz
  rw [← not_eventually]
  intro he
  obtain ⟨N,hN⟩ := eventually_atTop.mp he
  exact hz (mem_iUnion.mpr ⟨N,mem_iInter.mpr fun n => mem_iInter.mpr (hN n)⟩)

/-- Pointwise differentiation plus vanishing exceptional sets gives the measure
exclusion used for both the mesh bound and the common continuum exclusions. -/
lemma ae_ne_one_of_eventual_bound {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {p : ℕ → X → ℝ} {f : X → ℝ} {E : ℕ → Set X} {U : Set X}
    {α : ℝ} (hα : 0 < α)
    (hp : ∀ᵐ z ∂μ, Tendsto (fun n => p n z) atTop (𝓝 (f z)))
    (hE : Tendsto (fun n => μ (E n)) atTop (𝓝 0))
    (hb : ∀ z ∈ U, ∀ᶠ n in atTop, z ∉ E n → p n z ≤ 1-α) :
    ∀ᵐ z ∂μ, z ∈ U → f z ≠ 1 := by
  filter_upwards [hp,ae_frequently_notMem_of_measure_tendsto_zero hE] with z hz hgood hzU hf
  have hgt : ∀ᶠ n in atTop, 1-α < p n z :=
    hz.eventually (Ioi_mem_nhds (by rw [hf]; linarith))
  obtain ⟨n,hn,hbnd,hlarge⟩ := (hgood.and_eventually ((hb z hzU).and hgt)).exists
  exact (not_lt_of_ge (hbnd hn)) hlarge
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory MeasureTheory.Measure
namespace EuclideanFiveColor
lemma colorFn_locallyIntegrable {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c) (i : Fin k) :
    LocallyIntegrable (colorFn c i) (volume : Measure ℂ) :=
  (continuous_const.locallyIntegrable (f := fun _ : ℂ => (1:ℝ))).mono
    (colorFn_measurable hc i).aestronglyMeasurable (Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs,abs_of_nonneg (colorFn_nonneg c i z),abs_one] using colorFn_le_one c i z)
lemma diskAverage_eq_average_ball {k : ℕ} (c : ℂ → Fin k) (ε : ℝ) (i : Fin k) (q : ℂ) :
    diskAverage c ε i q = ⨍ z in Metric.ball q ε, colorFn c i z ∂volume := by
  have he : (fun v : ℂ => q+v) ⁻¹' Metric.ball q ε = Metric.ball 0 ε := by
    ext v
    simp [Metric.mem_ball,dist_eq_norm]
  have hi := (measurePreserving_add_left (volume : Measure ℂ) q).setIntegral_preimage_emb
    (MeasurableEquiv.addLeft q).measurableEmbedding (colorFn c i) (Metric.ball q ε)
  rw [he] at hi
  unfold diskAverage diskLaw
  rw [integral_smul_measure,ENNReal.toReal_inv,hi,setAverage_eq]
  simp only [Measure.real,Complex.volume_ball]
lemma complex_ball_ae_closedBall (q : ℂ) (ε : ℝ) :
    Metric.ball q ε =ᵐ[volume] Metric.closedBall q ε :=
  ae_eq_of_subset_of_measure_ge Metric.ball_subset_closedBall
    (by rw [Complex.volume_closedBall,Complex.volume_ball])
    measurableSet_ball.nullMeasurableSet ((isCompact_closedBall q ε).measure_ne_top)
lemma diskAverage_ae_tendsto {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n,0<ε n) (i : Fin k) :
    ∀ᵐ z : ℂ ∂volume, Tendsto (fun n => diskAverage c (ε n) i z) atTop (𝓝 (colorFn c i z)) := by
  have hε' : Tendsto ε atTop (𝓝[>] 0) := tendsto_nhdsWithin_iff.mpr
    ⟨hε,Eventually.of_forall hpos⟩
  filter_upwards [IsUnifLocDoublingMeasure.ae_tendsto_average volume
    (colorFn_locallyIntegrable hc i) 1] with z hz
  have h := hz (fun _ : ℕ => z) ε hε' (Eventually.of_forall fun n => by
    simp only [one_mul,Metric.mem_closedBall,dist_self]; exact (hpos n).le)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext n
  rw [diskAverage_eq_average_ball]
  exact setAverage_congr (complex_ball_ae_closedBall z (ε n))

lemma support_disjoint_open_of_ae {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {U : Set ℂ} (hU : IsOpen U) (i : Fin k)
    (h : ∀ᵐ z ∂(volume : Measure ℂ),z∈U → c z≠i) :
    Disjoint (spatialSupport c i) U := by
  have he : Uᶜ ∈ ae (volume.restrict {z | c z=i}) := by
    change ∀ᵐ z ∂volume.restrict {z | c z=i},z∈Uᶜ
    rw [ae_restrict_iff' (measurableSet_eq_fun hc measurable_const)]
    filter_upwards [h] with z hz hczi hzU
    exact hz hzU hczi
  have hs := Measure.support_subset_of_isClosed hU.isClosed_compl he
  exact Set.disjoint_left.mpr fun z hz hzU => hs hz hzU

lemma diskAverage_support_exclusion {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) (hpos : ∀ n,0<ε n)
    {E : ℕ → Set ℂ} (hE : Tendsto (fun n => volume (E n)) atTop (𝓝 0))
    {α : ℝ} (hα : 0<α) {U : Set ℂ} (hU : IsOpen U) (i : Fin k)
    (hb : ∀ z∈U,∀ᶠ n in atTop,z∉E n → diskAverage c (ε n) i z≤1-α) :
    Disjoint (spatialSupport c i) U := by
  apply support_disjoint_open_of_ae hc hU i
  filter_upwards [ae_ne_one_of_eventual_bound hα (diskAverage_ae_tendsto hc hε hpos i) hE hb]
    with z hz hzU hczi
  exact hz hzU (by simp [colorFn,hczi])
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_DiskExtension
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
universe u
namespace EuclideanFiveColor
lemma mem_diskHoles {S : Finset MarkedDisk} {z : ℂ} : z∈diskHoles S ↔ ∃d∈S,z∈d.ball := by
  simp [diskHoles]
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_HoleApproximation
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology
namespace EuclideanFiveColor
namespace MarkedDisk
lemma sphere_avoids_holes {S : Finset MarkedDisk}
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    {d : MarkedDisk} (hd : d∈S) {z : ℂ} (hz : z∈Metric.sphere d.center d.radius) : z∉diskHoles S := by
  rintro hh
  obtain ⟨e,he,hze⟩ := mem_diskHoles.mp hh
  by_cases hde : d=e
  · subst e
    have hh' : dist z d.center<d.radius := hze
    have hz' : dist z d.center=d.radius := hz
    linarith
  · exact Set.disjoint_left.mp (hdis hd he hde) (Metric.sphere_subset_closedBall hz)
      (Metric.ball_subset_closedBall hze)
end MarkedDisk
end EuclideanFiveColor
end

noncomputable section
open scoped Classical ENNReal
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
lemma unit_from_disk_mem_annulus {d : MarkedDisk} {z q : ℂ}
    (hq : q∈d.closedBall) (hzq : dist z q=1) : z∈diskAnnulus d := by
  have hq' : dist q d.center≤d.radius := hq
  constructor
  · change dist z d.center≤1+d.radius
    exact (dist_triangle z q d.center).trans (by linarith)
  · change ¬ dist z d.center<1-d.radius
    have hh := dist_triangle z d.center q
    rw [dist_comm d.center q,hzq] at hh
    linarith
lemma volume_diskAnnulus {d : MarkedDisk} (h0 : 0≤d.radius) (h1 : d.radius≤1) :
    volume (diskAnnulus d)=ENNReal.ofReal (4*Real.pi*d.radius) := by
  have hsub : Metric.ball d.center (1-d.radius)⊆Metric.closedBall d.center (1+d.radius) :=
    Metric.ball_subset_closedBall.trans (Metric.closedBall_subset_closedBall (by linarith))
  have hvol (r : ℝ) (hr : 0 ≤ r) : ENNReal.ofReal r ^ 2 * (NNReal.pi : ℝ≥0∞)=ENNReal.ofReal (r^2*Real.pi) := by
    rw [ENNReal.ofReal_mul (sq_nonneg r),ENNReal.ofReal_pow hr]
    congr 1
    rw [←NNReal.coe_real_pi,ENNReal.ofReal_coe_nnreal]
  rw [diskAnnulus,measure_sdiff hsub Metric.isOpen_ball.measurableSet.nullMeasurableSet (by finiteness),
    Complex.volume_closedBall,Complex.volume_ball,hvol _ (by linarith),hvol _ (by linarith),
    ←ENNReal.ofReal_sub _ (by positivity : 0≤(1-d.radius)^2*Real.pi)]
  congr 1
  ring

lemma volume_holeAnnuli_le {S : Finset MarkedDisk}
    (hS : ∀d∈S,0≤d.radius ∧ d.radius≤1) :
    volume (holeAnnuli S)≤ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by
  calc
    volume (holeAnnuli S)≤∑d∈S,volume (diskAnnulus d) := measure_biUnion_finset_le S _
    _ = ∑d∈S,ENNReal.ofReal (4*Real.pi*d.radius) := by
      apply Finset.sum_congr rfl
      intro d hd
      exact volume_diskAnnulus (hS d hd).1 (hS d hd).2
    _ = ENNReal.ofReal (∑d∈S,4*Real.pi*d.radius) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun d hd => mul_nonneg (by positivity) (hS d hd).1)]
    _ = ENNReal.ofReal (4*Real.pi*(∑d∈S,d.radius)) := by rw [Finset.mul_sum]
lemma unit_from_hole_mem_annuli {S : Finset MarkedDisk} {z q : ℂ}
    (hq : q∈diskHoles S) (hzq : dist z q=1) : z∈holeAnnuli S := by
  obtain ⟨d,hd,hqd⟩ := mem_diskHoles.mp hq
  exact mem_iUnion.mpr ⟨d,mem_iUnion.mpr ⟨hd,unit_from_disk_mem_annulus (Metric.ball_subset_closedBall hqd) hzq⟩⟩
lemma holeAnnuli_tendsto_zero (S : ℕ → Finset MarkedDisk)
    (hS : ∀n d,d∈S n → 0≤d.radius)
    (hlim : Tendsto (fun n => ∑d∈S n,d.radius) atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (S n))) atTop (𝓝 0) := by
  have hsmall : ∀ᶠ n in atTop,(∑d∈S n,d.radius)≤1 :=
    hlim.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1))
  have hbound : ∀ᶠ n in atTop,volume (holeAnnuli (S n))≤ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius)) := by
    filter_upwards [hsmall] with n hn
    apply volume_holeAnnuli_le
    exact fun d hd => ⟨hS n d hd,(MarkedDisk.radius_le_sum (hS n) hd).trans hn⟩
  have ht : Tendsto (fun n => ENNReal.ofReal (4*Real.pi*(∑d∈S n,d.radius))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hlim.const_mul (4*Real.pi))
  apply ENNReal.tendsto_nhds_zero.mpr
  intro a ha
  filter_upwards [hbound,ENNReal.tendsto_nhds_zero.mp ht a ha] with n hn hn'
  exact hn.trans hn'
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Mesh
attribute [-instance] _root_.OAI.EuclideanFiveColor.BoundedMeasurable.product_measurable_vadd
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- A point of a connected set with a distant partner can be moved to the
boundary of its (unique) small hole. Pairwise disjoint closed disks make the
new point lie outside every open hole. No path regularity is required. -/
lemma connected_escape_holes {S : Finset MarkedDisk} {t : ℝ}
    (hS : ∀d∈S,0≤d.radius)
    (hdis : (S : Set MarkedDisk).Pairwise (fun a b => Disjoint a.closedBall b.closedBall))
    (hsum : (∑d∈S,d.radius)<t) {K : Set ℂ} (hK : IsPreconnected K)
    {a b : ℂ} (ha : a∈K) (hb : b∈K) (hab : 2*t<dist a b) :
    ∃a'∈K,a'∉diskHoles S ∧ dist a a'≤2*t := by
  have ht : 0<t := (Finset.sum_nonneg hS).trans_lt hsum
  by_cases haS : a∈diskHoles S
  · obtain ⟨d,hd,had⟩ := mem_diskHoles.mp haS
    have hrad : d.radius<t := (MarkedDisk.radius_le_sum hS hd).trans_lt hsum
    have had' : dist a d.center<d.radius := had
    have hbd : d.radius<dist b d.center := by
      by_contra! hh
      have htri := dist_triangle a d.center b
      rw [dist_comm d.center b] at htri
      linarith
    obtain ⟨p,hp,hpd⟩ := hK.intermediate_value ha hb
      (continuous_id.dist continuous_const).continuousOn ⟨had'.le,hbd.le⟩
    refine ⟨p,hp,MarkedDisk.sphere_avoids_holes hdis hd hpd,?_⟩
    change dist p d.center=d.radius at hpd
    have htri := dist_triangle a d.center p
    rw [dist_comm d.center p,hpd] at htri
    linarith
  · exact ⟨a,ha,haS,by simpa using (mul_pos (by norm_num : (0:ℝ)<2) ht).le⟩

/-- Positive averages on shrinking disks force every limit center into the
actual measure support of that color. -/
lemma support_of_positive_diskAverage_limit {k : ℕ} {c : ℂ → Fin k} (hc : Measurable c)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0)) {a : ℕ → ℂ} {x : ℂ}
    (ha : Tendsto a atTop (𝓝 x)) (i : Fin k)
    (hp : ∀n,0<diskAverage c (ε n) i (a n)) : x∈spatialSupport c i := by
  apply (Measure.mem_support_iff_forall x).mpr
  intro U hU
  obtain ⟨r,hr,hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hnear : ∀ᶠ n in atTop,dist (a n) x < r/2 := ha.eventually (Metric.ball_mem_nhds x (by positivity))
  have hsmall : ∀ᶠ n in atTop,ε n < r/2 := hε.eventually (gt_mem_nhds (by positivity : (0:ℝ) < r/2))
  obtain ⟨n,han,hεn⟩ := (hnear.and hsmall).exists
  have hsub : Metric.ball (a n) (ε n)⊆U := by
    intro z hz
    apply hrU
    have hh : dist z (a n)<ε n := hz
    have htri := dist_triangle z (a n) x
    change dist z x < r
    linarith
  have hpos := hp n
  rw [diskAverage_area hc] at hpos
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hzero' : volume (U∩{z | c z=i})=0 := by
    simpa only [spatialSupport,Measure.restrict_apply' (measurableSet_eq_fun hc measurable_const)] using hzero
  have hball : volume (Metric.ball (a n) (ε n)∩{z | c z=i})=0 :=
    measure_mono_null (inter_subset_inter_left _ hsub) hzero'
  simp only [Measure.real,hball,ENNReal.toReal_zero,zero_div,lt_self_iff_false] at hpos
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory ContinuousMap
namespace EuclideanFiveColor
namespace FullApprox
lemma ε_tendsto {c : ℂ → Fin 5} {α : ℝ} {t : ℕ → ℝ}
    (a : ∀n,FullApprox c α (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => (a n).ε) atTop (𝓝 0) :=
  squeeze_zero (fun n => (a n).ε_pos.le) (fun n => (a n).ε_lt.le) ht
lemma annuli_tendsto {c : ℂ → Fin 5} {α : ℝ} {t : ℕ → ℝ}
    (a : ∀n,FullApprox c α (t n)) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => volume (holeAnnuli (a n).disks)) atTop (𝓝 0) := by
  apply holeAnnuli_tendsto_zero _ (fun n d hd => ((a n).positive d hd).le)
  exact squeeze_zero (fun n => Finset.sum_nonneg fun d hd => ((a n).positive d hd).le)
    (fun n => (a n).sum_lt.le) ht
lemma positive_average {c : ℂ → Fin 5} (hc : Measurable c) {α t : ℝ} (hα : α<1/5)
    (a : FullApprox c α t) (i : Fin 5) (q : Metric.closedBall (0:ℂ) 5)
    (hq : q.val∉diskHoles a.disks) (hp : 0<(a.map q).val i) : α<diskAverage c a.ε i q.val := by
  rw [a.agrees q hq] at hp
  exact (thresholdMap_pos hc a.ε_pos hα q.val i).mp hp

/-- A continuous graph approximant cannot have positive-coordinate connected
sets of macroscopic diameter at every shrinking scale. This is the manuscript
mesh argument, with connectedness replacing the stronger path assumption. -/
theorem no_large_positive_sequence {c : ℂ → Fin 5} (hc : Measurable c) (hw : WeakColoring 5 c)
    {α : ℝ} (hα : 0<α) (hα' : α<1/5) {t : ℕ → ℝ}
    (F : ∀n,FullApprox c α (t n)) (htlim : Tendsto t atTop (𝓝 0))
    (htsmall : ∀n,t n≤1/16) (i : Fin 5)
    (hbad : ∀n,∃K : Set ℂ, IsPreconnected K ∧ K⊆Metric.closedBall (0:ℂ) 5 ∧
      (∀z : Metric.closedBall (0:ℂ) 5,z.val∈K → 0<((F n).map z).val i) ∧
      ∃x∈K,∃y∈K,2<dist x y) : False := by
  choose K hK hsub hprob x hx y hy hxy using hbad
  have hxy' (n : ℕ) : 2*t n<dist (x n) (y n) := by linarith [htsmall n,hxy n]
  have hyx' (n : ℕ) : 2*t n<dist (y n) (x n) := by rw [dist_comm]; exact hxy' n
  choose a haK haH hax using fun n => connected_escape_holes
    (fun d hd => ((F n).positive d hd).le) (F n).disjoint (F n).sum_lt (hK n) (hx n) (hy n) (hxy' n)
  choose b hbK hbH hby using fun n => connected_escape_holes
    (fun d hd => ((F n).positive d hd).le) (F n).disjoint (F n).sum_lt (hK n) (hy n) (hx n) (hyx' n)
  have hab (n : ℕ) : 3/2≤dist (a n) (b n) := by
    have h1 := dist_triangle (x n) (a n) (y n)
    have h2 := dist_triangle (a n) (b n) (y n)
    rw [dist_comm (b n) (y n)] at h2
    linarith [hxy n,hax n,hby n,htsmall n]
  obtain ⟨p,hp,φ,hφ,hlim⟩ := ((isCompact_closedBall (0:ℂ) 5).prod
    (isCompact_closedBall (0:ℂ) 5)).tendsto_subseq (x := fun n => (a n,b n)) (fun n => ⟨hsub n (haK n),hsub n (hbK n)⟩)
  have halim : Tendsto (fun n => a (φ n)) atTop (𝓝 p.1) := (continuous_fst.tendsto p).comp hlim
  have hblim : Tendsto (fun n => b (φ n)) atTop (𝓝 p.2) := (continuous_snd.tendsto p).comp hlim
  have hpdist : 3/2≤dist p.1 p.2 := ge_of_tendsto (halim.dist hblim) (Eventually.of_forall (fun n => hab (φ n)))
  have hεlim := (ε_tendsto F htlim).comp hφ.tendsto_atTop
  have hE := (annuli_tendsto F htlim).comp hφ.tendsto_atTop
  have hasup : p.1∈spatialSupport c i := support_of_positive_diskAverage_limit hc hεlim halim i
    (fun n => hα.trans (positive_average hc hα' (F (φ n)) i ⟨a (φ n),hsub _ (haK _)⟩
      (haH _) (hprob _ _ (haK _))))
  have hexc : Disjoint (spatialSupport c i) (Metric.ball p.1 (1/8)) := by
    apply diskAverage_support_exclusion hc hεlim (fun n => (F (φ n)).ε_pos) hE hα Metric.isOpen_ball i
    intro z hz
    have hane : ∀ᶠn in atTop,dist (a (φ n)) p.1<1/8 :=
      halim.eventually (Metric.ball_mem_nhds _ (by norm_num))
    have hbne : ∀ᶠn in atTop,dist (b (φ n)) p.2<1/8 :=
      hblim.eventually (Metric.ball_mem_nhds _ (by norm_num))
    filter_upwards [hane,hbne] with n han hbn hzE
    have hza : dist z (a (φ n))<1 := by
      have hh := dist_triangle z p.1 (a (φ n))
      rw [dist_comm p.1 (a (φ n))] at hh
      change dist z p.1<1/8 at hz
      linarith
    have hzb : 1<dist z (b (φ n)) := by
      have h1 := dist_triangle p.1 z p.2
      have h2 := dist_triangle z (b (φ n)) p.2
      rw [dist_comm p.1 z] at h1
      change dist z p.1<1/8 at hz
      linarith
    obtain ⟨q,hq,hunit⟩ := straddle_connected_unit (hK (φ n))
      ⟨a (φ n),haK _,b (φ n),hbK _,hza,hzb⟩
    have hqH : q∉diskHoles (F (φ n)).disks := fun hh => hzE (unit_from_hole_mem_annuli hh hunit)
    have hqprob := positive_average hc hα' (F (φ n)) i ⟨q,hsub _ hq⟩ hqH (hprob _ _ hq)
    have hu : ‖q-z‖=1 := by simpa only [dist_eq_norm,norm_sub_rev] using hunit
    have hh := diskAverage_unit_pair hc hw (F (φ n)).ε_pos hu i
    change diskAverage c (F (φ n)).ε i z≤1-α
    change α<diskAverage c (F (φ n)).ε i q at hqprob
    linarith
  exact Set.disjoint_left.mp hexc hasup (Metric.mem_ball_self (by norm_num))
end FullApprox
end EuclideanFiveColor
end

end OAI
end

section
-- module Solutions.OAIQ5_T4.PlaneColoring_Five
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Set Topology ContinuousMap
namespace EuclideanFiveColor
lemma graphRealization_positive_three {V : Type*} {G : SimpleGraph V} {p : V → ℝ}
    (hp : p∈graphRealization G) {i j k : V} (hi : 0<p i) (hj : 0<p j) (hk : 0<p k) :
    i=j ∨ i=k ∨ j=k := by
  obtain ⟨a,b,_,t,_,rfl⟩ := hp
  have hpos (v : V) (hv : 0<graphEdgePoint a b t v) : v=a ∨ v=b := by
    by_contra! hh
    simp [graphEdgePoint_apply,hh.1,hh.2] at hv
  rcases hpos i hi with rfl|rfl <;> rcases hpos j hj with rfl|rfl <;>
    rcases hpos k hk with rfl|rfl <;> simp

/-- The actual positive-coordinate component cover contradicts the planar cover
obstruction whenever every connected positive region has diameter at most two. -/
theorem graph_map_small_mesh_impossible
    (F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5))))
    (hmesh : ∀(i : Fin 5) (K : Set ℂ),IsPreconnected K → K⊆Metric.closedBall (0:ℂ) 5 →
      (∀z : Metric.closedBall (0:ℂ) 5,z.val∈K → 0<(F z).val i) →
      ∀x∈K,∀y∈K,dist x y≤2) : False := by
  let Q := Metric.closedBall (0:ℂ) 5
  have : LocallyPathConnectedSpace Q := (convex_closedBall (0:ℂ) (5:ℝ)).locallyPathConnectedSpace
  let U : Fin 5 → Set Q := fun i => {z | 0<(F z).val i}
  have hU (i : Fin 5) : IsOpen (U i) :=
    isOpen_lt continuous_const ((continuous_apply i).comp (continuous_subtype_val.comp F.continuous))
  let I := {p : Fin 5 × Set Q // ∃x : Q,p.2=connectedComponentIn (U p.1) x}
  let W : I → Set Q := fun p => p.val.2
  have hW (p : I) : IsOpen (W p) := by
    obtain ⟨x,hx⟩ := p.property
    change IsOpen p.val.2
    rw [hx]
    exact (hU _).connectedComponentIn
  have hpos {p : I} {z : Q} (hz : z∈W p) : 0<(F z).val p.val.1 := by
    obtain ⟨x,hx⟩ := p.property
    change z∈p.val.2 at hz
    rw [hx] at hz
    exact connectedComponentIn_subset (U p.val.1) x hz
  have heq {p q : I} {z : Q} (hpq : p.val.1=q.val.1) (hp : z∈W p) (hq : z∈W q) : p=q := by
    apply Subtype.ext
    apply Prod.ext hpq
    obtain ⟨x,hx⟩ := p.property
    obtain ⟨y,hy⟩ := q.property
    change z∈p.val.2 at hp
    change z∈q.val.2 at hq
    rw [hx,hpq] at hp
    rw [hy] at hq
    rw [hx,hy,hpq,connectedComponentIn_eq hp,connectedComponentIn_eq hq]
  apply PlanarCover.compact_open_cover_impossible Metric.ball_subset_closedBall
    (isCompact_closedBall (0:ℂ) 5) W hW ?_ ?_ ?_
  · intro z
    have he : ∃i,0<(F z).val i := by
      by_contra! hh
      have hsum := Finset.sum_nonpos (s := (Finset.univ : Finset (Fin 5))) (fun i _ => hh i)
      rw [graphRealization_sum (F z).property] at hsum
      norm_num at hsum
    obtain ⟨i,hi⟩ := he
    exact ⟨⟨(i,connectedComponentIn (U i) z),⟨z,rfl⟩⟩,mem_connectedComponentIn hi⟩
  · intro z p q r hp hq hr
    rcases graphRealization_positive_three (F z).property (hpos hp) (hpos hq) (hpos hr) with h|h|h
    · exact Or.inl (heq h hp hq)
    · exact Or.inr (Or.inl (heq h hp hr))
    · exact Or.inr (Or.inr (heq h hq hr))
  · intro p x hx y hy
    obtain ⟨z,hz⟩ := p.property
    let K : Set ℂ := Subtype.val '' W p
    have hK : IsPreconnected K := by
      apply IsPreconnected.image _ _ continuous_subtype_val.continuousOn
      change IsPreconnected p.val.2
      rw [hz]
      exact isPreconnected_connectedComponentIn
    have hsub : K⊆Q := by rintro a ⟨b,_,rfl⟩; exact b.property
    have hprob : ∀z : Q,z.val∈K → 0<(F z).val p.val.1 := by
      rintro z ⟨b,hb,he⟩
      have hh : b=z := Subtype.ext he
      subst b
      exact hpos hb
    have hh := hmesh p.val.1 K hK hsub hprob x.val ⟨x,hx,rfl⟩ y.val ⟨y,hy,rfl⟩
    simpa only [dist_eq_norm] using hh
end EuclideanFiveColor
end

noncomputable section
open scoped Classical
open Set Filter Topology MeasureTheory
namespace EuclideanFiveColor
/-- Every continuous graph-valued map of the disk has a positive-coordinate
connected region of diameter greater than two. -/
lemma graph_map_large_positive
    (F : C(Metric.closedBall (0:ℂ) 5,GraphSpace (⊤ : SimpleGraph (Fin 5)))) :
    ∃i : Fin 5,∃K : Set ℂ,IsPreconnected K ∧ K⊆Metric.closedBall (0:ℂ) 5 ∧
      (∀z : Metric.closedBall (0:ℂ) 5,z.val∈K → 0<(F z).val i) ∧
      ∃x∈K,∃y∈K,2<dist x y := by
  by_contra! h
  exact graph_map_small_mesh_impossible F h

/-- No Borel weak five-coloring exists. The global approximants here are
constructed from the actual coloring, its transition graph, and its common
interface limits, rather than supplied as an extra coloring hypothesis. -/
theorem no_measurable_weak_five_coloring {c : ℂ → Fin 5}
    (hc : Measurable c) (hw : WeakColoring 5 c) : False := by
  let t : ℕ → ℝ := fun n => min (1/16) (1/((n:ℝ)+1))
  have hpos (n : ℕ) : 0<t n := lt_min (by norm_num) (by positivity)
  have hsmall (n : ℕ) : t n≤1/16 := min_le_left _ _
  have ht : Tendsto t atTop (𝓝 0) := squeeze_zero (fun n => (hpos n).le)
    (fun n => min_le_right _ _) tendsto_one_div_add_atTop_nhds_zero_nat
  let F : ∀n,FullApprox c (1/10) (t n) := fun n =>
    Classical.choice (fullApprox_exists hc hw (by norm_num) (by norm_num) (hpos n))
  have hbad : ∃ᶠn in atTop,∃i : Fin 5,∃K : Set ℂ,IsPreconnected K ∧ K⊆Metric.closedBall (0:ℂ) 5 ∧
      (∀z : Metric.closedBall (0:ℂ) 5,z.val∈K → 0<((F n).map z).val i) ∧
      ∃x∈K,∃y∈K,2<dist x y :=
    (Eventually.of_forall (fun n => graph_map_large_positive (F n).map)).frequently
  obtain ⟨i,hi⟩ := Filter.frequently_exists.mp hbad
  obtain ⟨φ,hφ,hφbad⟩ := extraction_of_frequently_atTop hi
  exact FullApprox.no_large_positive_sequence hc hw (by norm_num) (by norm_num)
    (fun n => F (φ n)) (ht.comp hφ.tendsto_atTop) (fun n => hsmall (φ n)) i hφbad

/-- No unrestricted five-coloring separates all unit-distance pairs in the Euclidean plane. -/
theorem no_proper_five_coloring_oai : ¬ ∃ c : ℂ → Fin 5, ProperColoring 5 c := by
  rintro ⟨c,hc⟩
  obtain ⟨d,hd,hw⟩ := proper_to_borel_weak hc
  exact no_measurable_weak_five_coloring hd hw
end EuclideanFiveColor
end

end OAI
end

theorem solution : type_of% @OAI.EuclideanFiveColor.no_proper_five_coloring_oai := @OAI.EuclideanFiveColor.no_proper_five_coloring_oai
