-- Prove2me | solution 1 for OAI.RVM.selectedInitialKernel_integrable_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:44:57.009355+00:00
-- url     : https://prove2.me/submissions/c7e131b0-9915-46d5-a3d7-378236ba15ed

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
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
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

lemma q_sq (v : Vec) : q v ^ 2 = 1 + ‖v‖ ^ 2 := by
  exact Real.sq_sqrt (by positivity)

lemma norm_lt_q (v : Vec) : ‖v‖ < q v := by
  have hp := q_pos v
  have hs := q_sq v
  nlinarith [sq_nonneg ‖v‖, norm_nonneg v]

lemma norm_velocity_lt_one (v : Vec) : ‖velocity v‖ < 1 := by
  rw [velocity, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 (q_pos v))]
  rw [← div_eq_inv_mul]
  exact (div_lt_one (q_pos v)).2 (norm_lt_q v)

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

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

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
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

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_WithinFlow
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open scoped Topology NNReal ContDiff


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Filter
open scoped Topology ContDiff
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

lemma determinant_retarded_graph {D : E →L[ℝ] E} (hD : D.det = 1) (v : E) (ℓ : E →L[ℝ] ℝ) :
    (D.comp ((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ)).det =
      1 - ℓ v := by
  have he : (((ContinuousLinearMap.id ℝ E) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ) : E →L[ℝ] E).toLinearMap =
      LinearMap.transvection ℓ.toLinearMap (-v) := by
    ext x
    simp [LinearMap.transvection,sub_eq_add_neg]
  change LinearMap.det (D.toLinearMap.comp _) = _
  rw [LinearMap.det_comp,he]
  change D.det * _ = _
  rw [hD,one_mul,LinearMap.transvection.det,map_neg]
  rfl

end

open Set MeasureTheory Filter
open scoped Topology ContDiff


lemma hasStrictFDerivAt_norm_nonzero {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    {x : F} (hx : x ≠ 0) :
    HasStrictFDerivAt (fun y : F => ‖y‖) (innerSL ℝ (‖x‖⁻¹ • x)) x := by
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hh := (Real.hasStrictDerivAt_sqrt (pow_ne_zero 2 hn)).comp_hasStrictFDerivAt x
    (hasStrictFDerivAt_norm_sq x)
  have hf : (Real.sqrt ∘ fun y : F => ‖y‖^2) = fun y : F => ‖y‖ := by
    funext y
    exact Real.sqrt_sq (norm_nonneg y)
  rw [hf,Real.sqrt_sq (norm_nonneg x)] at hh
  convert! hh using 1
  all_goals try with_reducible_and_instances rfl
  apply ContinuousLinearMap.ext
  intro y
  simp only [smul_apply,innerSL_apply_apply,inner_smul_left,
    starRingEnd_apply,star_trivial,smul_eq_mul,two_smul,add_apply]
  ring

lemma norm_coneDirection {x y : Vec} (hxy : x ≠ y) : ‖‖x-y‖⁻¹ • (x-y)‖ = 1 := by
  rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg _),inv_mul_cancel₀]
  exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)


open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma PhaseFlowOn.continuousOn_time {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (z : Phase) : ContinuousOn (F.flow z) (Icc 0 T) :=
  fun t ht => (F.ode z t ht).continuousWithinAt

lemma PhaseFlowOn.timelike {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) :
    ∃ c : ℝ≥0, (c : ℝ) < 1 ∧ LipschitzOnWith c (fun t => (F.flow z t).1) (Icc 0 T) := by
  have hc : ContinuousOn (fun t => ‖velocity (F.flow z t).2‖) (Icc 0 T) :=
    ((contDiff_velocity (k := 1)).continuous.comp_continuousOn (F.continuousOn_time z).snd).norm
  obtain ⟨t₀,ht₀,hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hT) hc
  refine ⟨⟨‖velocity (F.flow z t₀).2‖,norm_nonneg _⟩,norm_velocity_lt_one _,?_⟩
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t ht
  exact_mod_cast hmax ht

open Set MeasureTheory Filter
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverRadialDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.arrival_strictMono {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (z : Phase) (y : Vec) :
    StrictMonoOn (fun t => t-‖(F.flow z t).1-y‖) (Icc 0 T) := by
  obtain ⟨c,hc,hLip⟩ := F.timelike hT z
  intro a ha b hb hab
  have hbound := hLip.dist_le_mul a ha b hb
  rw [dist_eq_norm,Real.dist_eq,abs_of_neg (sub_neg.mpr hab)] at hbound
  have hn : ‖(F.flow z b).1-y‖ ≤ ‖(F.flow z a).1-(F.flow z b).1‖ + ‖(F.flow z a).1-y‖ := by
    calc
      _ = ‖((F.flow z b).1-(F.flow z a).1)+((F.flow z a).1-y)‖ := by congr 1; abel
      _ ≤ ‖(F.flow z b).1-(F.flow z a).1‖ + ‖(F.flow z a).1-y‖ := norm_add_le _ _
      _ = _ := by rw [norm_sub_rev]
  have hp := mul_pos (sub_pos.mpr hc) (sub_pos.mpr hab)
  nlinarith

lemma isOpen_receiverRadialDomain (s T : ℝ) : IsOpen (receiverRadialDomain s T) :=
  (isOpen_lt continuous_const continuous_norm).inter
    (isOpen_lt (continuous_const.add continuous_norm) continuous_const)

lemma receiver_time_mem {s T : ℝ} (hs : 0 ≤ s) {w : Vec}
    (hw : w ∈ receiverRadialDomain s T) : s+‖w‖ ∈ Ioo 0 T := by
  constructor <;> linarith [hw.1,hw.2]

lemma PhaseFlowOn.receiver_injective {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) :
    InjOn (receiverRadial F.flow z s) (receiverRadialDomain s T) := by
  intro a ha b hb hab
  have hta := Ioo_subset_Icc_self (receiver_time_mem hs.1 ha)
  have htb := Ioo_subset_Icc_self (receiver_time_mem hs.1 hb)
  let y := receiverRadial F.flow z s a
  have hya : (F.flow z (s+‖a‖)).1-y=a := by dsimp [y,receiverRadial]; abel
  have hyb : (F.flow z (s+‖b‖)).1-y=b := by
    change (F.flow z (s+‖b‖)).1-receiverRadial F.flow z s a=b
    rw [hab]
    unfold receiverRadial
    abel
  have he : s+‖a‖=s+‖b‖ := by
    apply (F.arrival_strictMono (hs.1.trans hs.2) z y).injOn hta htb
    dsimp only
    rw [hya,hyb]
    ring
  rw [← hya,← hyb,he]

lemma PhaseFlowOn.exists_arrival {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {y : Vec}
    (hy : ‖(F.flow z T).1-y‖ < T-s) :
    ∃! t : ℝ, t ∈ Icc s T ∧ t-‖(F.flow z t).1-y‖=s := by
  have hsub : Icc s T ⊆ Icc 0 T := fun _ ht => ⟨hs.1.trans ht.1,ht.2⟩
  have hc : ContinuousOn (fun t => t-‖(F.flow z t).1-y‖) (Icc s T) :=
    continuousOn_id.sub ((((F.continuousOn_time z).mono hsub).fst.sub continuousOn_const).norm)
  have hstart : s-‖(F.flow z s).1-y‖ ≤ s := sub_le_self _ (norm_nonneg _)
  have hend : s ≤ T-‖(F.flow z T).1-y‖ := by linarith
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hs.2 hc ⟨hstart,hend⟩
  refine ⟨t,⟨ht,he⟩,?_⟩
  intro r hr
  apply (F.arrival_strictMono (hs.1.trans hs.2) z y).injOn (hsub hr.1) (hsub ht)
  exact hr.2.trans he.symm

lemma PhaseFlowOn.receiver_image {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) :
    receiverRadial F.flow z s '' receiverRadialDomain s T =
      ball (F.flow z T).1 (T-s) \ {(F.flow z s).1} := by
  ext y
  constructor
  · rintro ⟨w,hw,rfl⟩
    let t := s+‖w‖
    let y := receiverRadial F.flow z s w
    have ht : t ∈ Ioo 0 T := receiver_time_mem hs.1 hw
    have hst : s < t := by dsimp [t]; linarith [hw.1]
    have he : t-‖(F.flow z t).1-y‖=s := by
      have hh : (F.flow z t).1-y=w := by dsimp [y,receiverRadial,t]; abel
      rw [hh]
      dsimp [t]
      ring
    have hm := F.arrival_strictMono (hs.1.trans hs.2) z y
    constructor
    · have hh := hm (Ioo_subset_Icc_self ht) ⟨hs.1.trans hs.2,le_rfl⟩ ht.2
      dsimp only at hh
      rw [he] at hh
      rw [mem_ball,dist_eq_norm,norm_sub_rev]
      linarith
    · intro hh
      change y=(F.flow z s).1 at hh
      have hh' := hm hs (Ioo_subset_Icc_self ht) hst
      dsimp only at hh'
      rw [he,hh,sub_self,norm_zero,sub_zero] at hh'
      exact (lt_irrefl s) hh'
  · rintro ⟨hy,hn⟩
    have hy' : ‖(F.flow z T).1-y‖ < T-s := by
      simpa only [mem_ball,dist_eq_norm,norm_sub_rev] using hy
    obtain ⟨t,⟨ht,he⟩,_⟩ := F.exists_arrival hs z hy'
    have hst : s < t := by
      by_contra h
      have ht' : t=s := le_antisymm (le_of_not_gt h) ht.1
      rw [ht'] at he
      have hh : ‖(F.flow z s).1-y‖=0 := by linarith
      exact hn (sub_eq_zero.mp (norm_eq_zero.mp hh)).symm
    have htT : t < T := by
      by_contra h
      have ht' : t=T := le_antisymm ht.2 (le_of_not_gt h)
      rw [ht'] at he
      linarith
    let w := (F.flow z t).1-y
    have hw : s+‖w‖=t := by dsimp [w]; linarith
    refine ⟨w,⟨?_,?_⟩,?_⟩
    · dsimp [w]; linarith
    · rw [hw]; exact htT
    · unfold receiverRadial
      rw [hw]
      dsimp [w]
      abel

lemma PhaseFlowOn.receiver_differential {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : 0 ≤ s) (z : Phase) {w : Vec} (hw : w ∈ receiverRadialDomain s T) :
    HasFDerivAt (receiverRadial F.flow z s)
      ((ContinuousLinearMap.toSpanSingleton ℝ (velocity (F.flow z (s+‖w‖)).2)).comp
        (innerSL ℝ (‖w‖⁻¹ • w)) - ContinuousLinearMap.id ℝ Vec) w := by
  have ht := receiver_time_mem hs hw
  have hX := ((F.ode z _ (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).fst
  change HasDerivAt (fun t => (F.flow z t).1) (velocity (F.flow z (s+‖w‖)).2) (s+‖w‖) at hX
  have hn := (hasStrictFDerivAt_norm_nonzero (norm_ne_zero_iff.mp (ne_of_gt hw.1))).hasFDerivAt
  convert! (hX.hasFDerivAt.comp w (hn.const_add s)).sub (hasFDerivAt_id w) using 1
  all_goals try with_reducible_and_instances rfl

lemma PhaseFlowOn.receiver_jacobian {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : 0 ≤ s) (z : Phase) {w : Vec} (hw : w ∈ receiverRadialDomain s T) :
    |(fderiv ℝ (receiverRadial F.flow z s) w).det| =
      1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2) := by
  rw [(F.receiver_differential hs z hw).fderiv]
  let v := velocity (F.flow z (s+‖w‖)).2
  let ℓ := innerSL ℝ (‖w‖⁻¹ • w)
  have hd := determinant_retarded_graph
    (D := ContinuousLinearMap.id ℝ Vec) (by exact LinearMap.det_id) v ℓ
  simp only [ContinuousLinearMap.id_comp] at hd
  have he : (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ - ContinuousLinearMap.id ℝ Vec =
      -((ContinuousLinearMap.id ℝ Vec) - (ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ) := by abel
  have hneg (A : Vec →L[ℝ] Vec) : |(-A).det|=|A.det| := by
    change |LinearMap.det (-A.toLinearMap)|=|LinearMap.det A.toLinearMap|
    rw [← neg_one_smul ℝ A.toLinearMap,LinearMap.det_smul,abs_mul,abs_pow]
    norm_num
  change |((ContinuousLinearMap.toSpanSingleton ℝ v).comp ℓ - ContinuousLinearMap.id ℝ Vec).det| = _
  rw [he,hneg,hd]
  change |1 - inner ℝ (‖w‖⁻¹ • w) v| = _
  rw [← dot_eq_inner,abs_of_pos]
  apply cone_denom_pos
  simpa only [sub_zero] using norm_coneDirection (x := w) (y := 0)
    (norm_ne_zero_iff.mp (ne_of_gt hw.1))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_PhaseHits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma lintegral_radial_measure {f : ℝ → ENNReal} (hf : Measurable f) :
    (∫⁻ r : Ioi (0 : ℝ), f r ∂Measure.volumeIoiPow 2) =
      ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r^2) * f r := by
  have hpow : Measurable (fun r : Ioi (0 : ℝ) => ENNReal.ofReal (r.1^2)) :=
    (measurable_subtype_coe.pow_const 2).ennreal_ofReal
  calc
    _ = ∫⁻ r : Ioi (0 : ℝ), ENNReal.ofReal (r.1^2) * f r.1 ∂volume.comap Subtype.val :=
      lintegral_withDensity_eq_lintegral_mul _ hpow (hf.comp measurable_subtype_coe)
    _ = _ := lintegral_subtype_comap (μ := volume) measurableSet_Ioi
      (fun r : ℝ => ENNReal.ofReal (r^2) * f r)

lemma lintegral_polar {f : Vec → ENNReal} (hf : Measurable f) :
    (∫⁻ y : Vec, f y) = ∫⁻ n : Sphere, ∫⁻ r in Ioi (0 : ℝ),
      ENNReal.ofReal (r^2) * f (r • n.1) ∂volume ∂sphereMeasure := by
  calc
    _ = ∫⁻ z : ({0}ᶜ : Set Vec), f z.1 ∂volume.comap Subtype.val := by
      rw [lintegral_subtype_comap (measurableSet_singleton _).compl f,restrict_compl_singleton]
    _ = ∫⁻ p : Sphere × Ioi (0 : ℝ), f (p.2.1 • p.1.1)
        ∂sphereMeasure.prod (Measure.volumeIoiPow 2) := by
      have h := (volume : Measure Vec).measurePreserving_homeomorphUnitSphereProd.lintegral_comp_emb
        (Homeomorph.measurableEmbedding _)
        (fun p => f (((homeomorphUnitSphereProd Vec).symm p).1))
      simpa only [Homeomorph.symm_apply_apply,homeomorphUnitSphereProd_symm_apply_coe,
        finrank_euclideanSpace_fin,Nat.reduceSub] using h
    _ = ∫⁻ n : Sphere, ∫⁻ r : Ioi (0 : ℝ), f (r.1 • n.1) ∂Measure.volumeIoiPow 2
        ∂sphereMeasure := by
      apply lintegral_prod
      exact (hf.comp ((measurable_subtype_coe.comp measurable_snd).smul
        (measurable_subtype_coe.comp measurable_fst))).aemeasurable
    _ = _ := by
      apply lintegral_congr
      intro n
      exact lintegral_radial_measure (hf.comp (measurable_id.smul_const _))

lemma PhaseFlowOn.receiver_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) (g : Vec → ENNReal) :
    ∫⁻ y in ball (F.flow z T).1 (T-s), g y =
      ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
          g (receiverRadial F.flow z s w) := by
  have hd : ∀ w ∈ receiverRadialDomain s T,
      HasFDerivWithinAt (receiverRadial F.flow z s)
        (fderiv ℝ (receiverRadial F.flow z s) w) (receiverRadialDomain s T) w := by
    intro w hw
    exact (F.receiver_differential hs.1 z hw).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  calc
    _ = ∫⁻ y in receiverRadial F.flow z s '' receiverRadialDomain s T, g y := by
      apply setLIntegral_congr
      rw [F.receiver_image hs z]
      exact (sdiff_null_ae_eq_self (measure_singleton (F.flow z s).1)).symm
    _ = ∫⁻ w in receiverRadialDomain s T,
        ENNReal.ofReal |(fderiv ℝ (receiverRadial F.flow z s) w).det| *
          g (receiverRadial F.flow z s w) :=
      lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (isOpen_receiverRadialDomain s T).measurableSet
        hd (F.receiver_injective hs z) g
    _ = _ := by
      apply setLIntegral_congr_fun (isOpen_receiverRadialDomain s T).measurableSet
      intro w hw
      dsimp only
      rw [F.receiver_jacobian hs.1 z hw]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SpaceConeDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.receiver_polar_lintegral {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) {g : Vec → ENNReal} (hg : Measurable g) :
    (∫⁻ y in ball (F.flow z T).1 (T-s), g y) =
      ∫⁻ n : Sphere, ∫⁻ r in Ioo (0 : ℝ) (T-s),
        ENNReal.ofReal (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) *
          g ((F.flow z (s+r)).1-r • n.1) ∂volume ∂sphereMeasure := by
  classical
  let S := receiverRadialDomain s T
  have hS : MeasurableSet S := (isOpen_receiverRadialDomain s T).measurableSet
  let Ψ : Vec → Phase := S.indicator (fun w => F.flow z (s+‖w‖))
  have hcΨ : ContinuousOn (fun w : Vec => F.flow z (s+‖w‖)) S := by
    intro w hw
    have ht : s+‖w‖ ∈ Ioo 0 T := ⟨by linarith [hw.1,hs.1],hw.2⟩
    have hc : ContinuousAt (fun v : Vec => (s+‖v‖,z)) w :=
      (continuousAt_const.add continuousAt_id.norm).prodMk continuousAt_const
    have hh := (F.joint z (s+‖w‖) ht).continuousAt.comp (f := fun v : Vec => (s+‖v‖,z)) hc
    exact hh.continuousWithinAt
  have hmΨ : Measurable Ψ := by
    have h := hcΨ.measurable_piecewise (continuousOn_const (c := (0 : Phase))) hS
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [Ψ,Set.piecewise,hw]
  let R : Vec → Vec := S.indicator (receiverRadial F.flow z s)
  have hcR : ContinuousOn (receiverRadial F.flow z s) S :=
    fun w hw => (F.receiver_differential hs.1 z hw).continuousAt.continuousWithinAt
  have hmR : Measurable R := by
    have h := hcR.measurable_piecewise (continuousOn_const (c := (0 : Vec))) hS
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [R,Set.piecewise,hw]
  have hmK : Measurable (fun w : Vec => ENNReal.ofReal
      (1-dot (‖w‖⁻¹ • w) (velocity (Ψ w).2)) * g (R w)) := by
    simp only [dot_eq_inner]
    exact ((measurable_const.sub
      ((measurable_id.norm.inv.smul measurable_id).inner
        ((contDiff_velocity (k := 1)).continuous.measurable.comp hmΨ.snd))).ennreal_ofReal).mul (hg.comp hmR)
  let H : Vec → ENNReal := S.indicator
    (fun w => ENNReal.ofReal (1-dot (‖w‖⁻¹ • w) (velocity (F.flow z (s+‖w‖)).2)) *
      g (receiverRadial F.flow z s w))
  have hH : Measurable H := by
    convert hmK.indicator hS using 1
    all_goals try with_reducible_and_instances rfl
    funext w
    by_cases hw : w ∈ S <;> simp [H,Ψ,R,Set.indicator,hw]
  rw [F.receiver_lintegral hs z g,← lintegral_indicator hS]
  change (∫⁻ w, H w) = _
  rw [lintegral_polar hH]
  apply lintegral_congr
  intro n
  let k : ℝ → ENNReal := fun r => ENNReal.ofReal
    (r^2*(1-dot n.1 (velocity (F.flow z (s+r)).2))) * g ((F.flow z (s+r)).1-r • n.1)
  have hn : ‖n.1‖=1 := mem_sphere_zero_iff_norm.mp n.2
  have he : ∀ r ∈ Ioi (0 : ℝ), ENNReal.ofReal (r^2) * H (r • n.1) =
      (Iio (T-s)).indicator k r := by
    intro r hr
    have hnorm : ‖r • n.1‖=r := by rw [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hn,mul_one]
    have hd : r • n.1 ∈ S ↔ r < T-s := by
      change 0 < ‖r • n.1‖ ∧ s+‖r • n.1‖ < T ↔ _
      rw [hnorm]
      constructor
      · intro h; linarith [h.2]
      · intro h; exact ⟨hr,by linarith⟩
    by_cases h : r < T-s
    · rw [show H (r • n.1) = _ from Set.indicator_of_mem (hd.mpr h) _,
        Set.indicator_of_mem (show r ∈ Iio (T-s) from h)]
      dsimp only [k,receiverRadial]
      have hnsmul : r⁻¹ • (r • n.1)=n.1 := by
        rw [smul_smul,inv_mul_cancel₀ (ne_of_gt (show 0 < r from hr)),one_smul]
      rw [hnorm,hnsmul,ENNReal.ofReal_mul (sq_nonneg r),mul_assoc]
    · rw [show H (r • n.1) = 0 from Set.indicator_of_notMem (fun hh => h (hd.mp hh)) _,mul_zero,
        Set.indicator_of_notMem (show r ∉ Iio (T-s) from h)]
  calc
    _ = ∫⁻ r in Ioi (0 : ℝ), (Iio (T-s)).indicator k r :=
      setLIntegral_congr_fun measurableSet_Ioi he
    _ = ∫⁻ r in Ioi (0 : ℝ) ∩ Iio (T-s), k r := by
      simpa only [inter_comm] using (setLIntegral_indicator (μ := (volume : Measure ℝ))
        (t := Ioi (0 : ℝ)) measurableSet_Iio k)
    _ = _ := rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeArgument
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open Set MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma sphere_norm (n : Sphere) : ‖n.1‖ = 1 := by
  simpa only [mem_sphere,dist_zero_right] using n.2

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixClamp
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma prefixClamp_mem {T : ℝ} (hT : 0≤T) (t : ℝ) : prefixClamp T t∈Icc 0 T :=
  ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩

lemma prefixClamp_eq {T t : ℝ} (ht : t∈Icc 0 T) : prefixClamp T t=t := by
  simp [prefixClamp,min_eq_right ht.2,max_eq_right ht.1]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DyadicCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
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
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiff_dyadicCut : ContDiff ℝ ∞ dyadicCut :=
  contDiff_const.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))
lemma contDiff_dyadicBump : ContDiff ℝ ∞ dyadicBump :=
  contDiff_dyadicCut.sub (contDiff_dyadicCut.comp (contDiff_const.mul contDiff_id))
lemma contDiff_dyadicFactor (n : ℕ) : ContDiff ℝ ∞ (dyadicFactor n) :=
  contDiff_dyadicBump.comp (contDiff_const.mul contDiff_id)

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicCut_antitone : Antitone dyadicCut := by
  intro x y hxy
  exact sub_le_sub_left (Real.smoothTransition.monotone (sub_le_sub_right hxy 1)) 1
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _

lemma dyadicFactor_eq (n : ℕ) (x : ℝ) :
    dyadicFactor n x=dyadicCut ((2:ℝ)^n*x)-dyadicCut ((2:ℝ)^(n+1)*x) := by
  simp only [dyadicFactor,dyadicBump,pow_succ]
  congr 2
  ring
lemma sum_dyadicFactor (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, dyadicFactor n x=dyadicCut x-dyadicCut ((2:ℝ)^N*x) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.sum_range_succ,ih,dyadicFactor_eq]; ring

lemma dyadicFactor_zero_large {x : ℝ} {n : ℕ} (hn : 2≤(2:ℝ)^n*x) :
    dyadicFactor n x=0 := dyadicBump_zero_right hn

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma dyadicMultiFactor_nonneg {ι : Type*} [Fintype ι] (n : ι→ℕ) (x : ι→ℝ) :
    0≤dyadicMultiFactor n x := Finset.prod_nonneg (fun _i _ => dyadicFactor_nonneg _ _)

lemma sum_dyadicMultiFactor {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x =
      ∏ i, (dyadicCut (x i)-dyadicCut ((2:ℝ)^N*x i)) := by
  classical
  unfold dyadicBox dyadicMultiFactor
  convert Finset.sum_prod_piFinset (Finset.range N) (fun i n => dyadicFactor n (x i)) using 1
  all_goals try with_reducible_and_instances rfl
  simp only [sum_dyadicFactor]

lemma sum_dyadicMultiFactor_eq_one {ι : Type*} [Fintype ι] (N : ℕ) (x : ι→ℝ)
    (hx : ∀ i, x i≤1) (hN : ∀ i, 2≤(2:ℝ)^N*x i) :
    ∑ n∈dyadicBox ι N, dyadicMultiFactor n x=1 := by
  rw [sum_dyadicMultiFactor]
  simp only [dyadicCut_one (hx _),dyadicCut_zero (hN _),sub_zero,Finset.prod_const_one]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_NullConeFlux
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology NNReal
open scoped Topology ContDiff
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory Metric
open scoped Topology Pointwise

namespace RVM

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_PhysicalCutoffCoordinates
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma physicalCutoffCoordinates_pos {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : 0 < r) : ∀ i,0<physicalCutoffCoordinates T r n v w i := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · exact one_div_pos.mpr (q_pos v)
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos v n hn) (by norm_num))
  · exact Real.sqrt_pos.mpr (div_pos (cone_denom_pos w n hn) (by norm_num))
  · exact div_pos hr (lt_of_lt_of_le (by norm_num) (le_max_left _ _))

lemma real_deficit_le_two {n : Vec} (hn : ‖n‖=1) (v : Vec) : 1-dot n (velocity v) ≤ 2 := by
  have h := (abs_dot_le n (velocity v)).trans (by simpa only [hn,one_mul] using (norm_velocity_lt_one v).le)
  linarith [neg_abs_le (dot n (velocity v))]

lemma physicalCutoffCoordinates_le_one {T r : ℝ} {n v w : Vec}
    (hn : ‖n‖=1) (hr : r ≤ max 1 T) : ∀ i,physicalCutoffCoordinates T r n v w i≤1 := by
  intro i
  fin_cases i <;> simp only [physicalCutoffCoordinates]
  · apply (div_le_one (q_pos v)).mpr
    have hs := q_sq v
    nlinarith [q_pos v,sq_nonneg ‖v‖]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn v]
  · apply (Real.sqrt_le_iff).mpr
    constructor
    · norm_num
    · nlinarith [real_deficit_le_two hn w]
  · exact (div_le_one (lt_of_lt_of_le (by norm_num) (le_max_left _ _))).mpr hr

lemma dyadicMultiFactor_curve_locally_finite {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      ∀ᶠ r in 𝓝 t, ∀ n : ι→ℕ, n∉dyadicBox ι N → dyadicMultiFactor n (fun i => g i r)=0 := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/g i t) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*g i t := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  refine ⟨N,fun i => by linarith [hN i],?_⟩
  have he : ∀ᶠ r in 𝓝 t, ∀ i,g i t/2<g i r := by
    apply Filter.eventually_all.mpr
    intro i
    exact (hg i).eventually (Ioi_mem_nhds (by linarith [hx i]))
  filter_upwards [he] with r hr n hn
  have hb : ∃ i,N≤n i := by
    by_contra hb
    push Not at hb
    apply hn
    simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
  obtain ⟨i,hi⟩ := hb
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  apply dyadicFactor_zero_large
  have hpN : 0<(2:ℝ)^N := by positivity
  have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
  have hgr : 0≤g i r := le_of_lt ((by linarith [hx i] : 0<g i t/2).trans (hr i))
  have hh := mul_le_mul_of_nonneg_right hpni hgr
  have hh' := mul_lt_mul_of_pos_left (hr i) hpN
  linarith [hN i]

lemma selectedDyadicCutoff_curve_eventually {ι : Type*} [Fintype ι]
    {g : ι → ℝ → ℝ} {t : ℝ} (hg : ∀ i, ContinuousAt (g i) t) (hx : ∀ i,0<g i t)
    (S : Set (ι→ℕ)) :
    ∃ N : ℕ, (∀ i,2≤(2:ℝ)^N*g i t) ∧
      (fun r => selectedDyadicCutoff S (fun i => g i r)) =ᶠ[𝓝 t]
        (fun r => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n (fun i => g i r)) := by
  classical
  obtain ⟨N,hN,he⟩ := dyadicMultiFactor_curve_locally_finite hg hx
  refine ⟨N,hN,?_⟩
  filter_upwards [he] with r hr
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N) (fun _ n => dyadicMultiFactor n (fun i => g i r)) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hr n hn]
    · exact indicator_of_notMem hs _

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_WaveK
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology ContDiff RealInnerProductSpace
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
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma sphere_area : sphereMeasure.real univ = 4*Real.pi := by
  rw [sphereMeasure,Measure.toSphere_real_apply_univ]
  simp only [Vec,finrank_euclideanSpace,Measure.real,EuclideanSpace.volume_ball_fin_three,
    ENNReal.ofReal_one,one_pow,one_mul,ENNReal.toReal_ofReal (by positivity : 0≤Real.pi*4/3)]
  norm_num
  ring

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



section
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
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
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
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

end RVM

end

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
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ReceiverQ
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma cone_denom_le_two (v n : Vec) (hn : ‖n‖=1) : 1-dot n (velocity v)≤2 := by
  have h := abs_dot_le n (velocity v)
  rw [hn,one_mul] at h
  have h' := (neg_le_abs (dot n (velocity v))).trans h
  linarith [norm_velocity_lt_one v]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClosedBranchDomain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.branch_spec_closed {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s∈Icc s T ∧
      branchTime F.flow zX zY T s-s=
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hsub : Icc s T⊆Icc 0 T := fun _ ht=>⟨hs.1.1.trans ht.1,ht.2⟩
  have hc : ContinuousOn (fun t=>t-‖(F.flow zX t).1-(F.flow zY s).1‖) (Icc s T) :=
    continuousOn_id.sub ((((F.continuousOn_time zX).mono hsub).fst.sub continuousOn_const).norm)
  have hstart : s-‖(F.flow zX s).1-(F.flow zY s).1‖ ≤ s := sub_le_self _ (norm_nonneg _)
  have hend : s ≤ T-‖(F.flow zX T).1-(F.flow zY s).1‖ := by linarith [hs.2]
  obtain ⟨t,ht,he⟩ := intermediate_value_Icc hs.1.2 hc ⟨hstart,hend⟩
  have hex : ∃ t,t∈Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique_closed {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s∈closedBranchDomain F.flow zX zY T)
    (ht : t∈Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hτ,hcone⟩ := F.branch_spec_closed zX zY hs
  apply (F.arrival_strictMono (hs.1.1.trans hs.1.2) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.trans ht.1,ht.2⟩ ⟨hs.1.1.trans hτ.1,hτ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.branch_radius_pos_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    0 < branchTime F.flow zX zY T σ-σ := by
  obtain ⟨ht,he⟩ := F.branch_spec_closed zX zY hσ
  apply sub_pos.mpr
  by_contra h
  have hh : branchTime F.flow zX zY T σ=σ := le_antisymm (le_of_not_gt h) ht.1
  rw [hh,sub_self] at he
  exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))

lemma PhaseFlowOn.branchDirection_norm_closed {E B : Field} {T σ : ℝ}
    (F : PhaseFlowOn E B T) (zX zY : Phase)
    (hσ : σ∈closedBranchDomain F.flow zX zY T)
    (hne : (F.flow zX σ).1≠(F.flow zY σ).1) :
    ‖branchDirection F.flow zX zY T σ‖=1 := by
  have hp := F.branch_radius_pos_closed zX zY hσ hne
  have he := (F.branch_spec_closed zX zY hσ).2
  dsimp only [branchDirection]
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp),← he]
  exact inv_mul_cancel₀ hp.ne'

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_MomentumDirection
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
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


lemma selectedDyadicCutoff_mem_unit {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hp : ∀ i,0<x i) (h1 : ∀ i,x i≤1) (S : Set (ι→ℕ)) :
    selectedDyadicCutoff S x∈Icc (0:ℝ) 1 := by
  classical
  obtain ⟨N,hN,he⟩ := selectedDyadicCutoff_curve_eventually
    (t:=0) (g:=fun i (_r : ℝ)=>x i) (fun _=>continuousAt_const) hp S
  have hh := he.eq_of_nhds
  change selectedDyadicCutoff S x = ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n x at hh
  rw [hh]
  refine ⟨Finset.sum_nonneg (fun n _=>dyadicMultiFactor_nonneg n x),?_⟩
  calc
    _ ≤ ∑ n∈dyadicBox ι N,dyadicMultiFactor n x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (fun n _ _=>dyadicMultiFactor_nonneg n x)
    _ = 1 := sum_dyadicMultiFactor_eq_one N x h1 hN



open MeasureTheory Set

open Filter Set
open scoped Topology

open scoped Topology Pointwise

open Set MeasureTheory Metric ODE
open scoped Topology NNReal

open scoped ContDiff

open Set MeasureTheory Metric

open Set MeasureTheory Metric Filter ODE

open Set MeasureTheory Filter Metric ODE

open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff

open Set MeasureTheory Filter

open scoped Topology ContDiff RealInnerProductSpace NNReal

open Set Filter MeasureTheory Metric

open scoped Topology ContDiff NNReal RealInnerProductSpace

open scoped Topology ContDiff NNReal ENNReal

open Set MeasureTheory
open scoped ENNReal

open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

open scoped Topology ContDiff ENNReal

open scoped Topology ContDiff NNReal

open scoped Topology ContDiff

open Set

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DatumElectricFluxKernel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma datum_velocity_support {f : Phase → ℝ} (hc : HasCompactSupport f) :
    ∃ K : Set Vec, IsCompact K ∧ ∀ y v, v∉K → f (y,v)=0 := by
  refine ⟨Prod.snd '' tsupport f,hc.image continuous_snd,?_⟩
  intro y v hv
  by_contra h
  exact hv ⟨(y,v),subset_tsupport _ h,rfl⟩

lemma datum_integrand_continuousOn {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ContinuousOn (fun p : (Vec × Vec) × Vec => f (p.1.1,p.2) • H (p.1.2,p.2))
      ((univ ×ˢ sphere (0:Vec) 1) ×ˢ univ) := by
  exact (hf.comp (continuous_fst.fst.prodMk continuous_snd)).continuousOn.smul
    (hH.comp (continuous_fst.snd.prodMk continuous_snd).continuousOn
      (fun _ h => ⟨h.1.2,mem_univ _⟩))

lemma uniform_datum_velocity_integral_bound {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {f : Phase → ℝ} {H : Vec × Vec → W} (hf : Continuous f) (hc : HasCompactSupport f)
    (hH : ContinuousOn H (sphere (0:Vec) 1 ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ y n : Vec, ‖n‖=1 → ‖∫ v : Vec, f (y,v) • H (n,v)‖≤C := by
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  let Kx : Set Vec := Prod.fst '' tsupport f
  have hKx : IsCompact Kx := hc.image continuous_fst
  have hF := datum_integrand_continuousOn hf hH
  have hP : IsCompact (Kx ×ˢ sphere (0:Vec) 1) := hKx.prod (isCompact_sphere (0:Vec) 1)
  obtain ⟨C,hC,hbound⟩ := uniform_integral_bound_compact hP hK
    (hF.mono (by intro p hp; exact ⟨⟨mem_univ _,hp.1.2⟩,hp.2⟩))
    (show ∀ p ∈ Kx ×ˢ sphere (0:Vec) 1, ∀ v ∉ K,
      f (p.1,v) • H (p.2,v)=0 from by intro p hp v hv; rw [hz p.1 v hv,zero_smul])
  refine ⟨C,hC,?_⟩
  intro y n hn
  by_cases hy : y∈Kx
  · exact hbound (y,n) ⟨hy,by simpa only [mem_sphere,dist_zero_right] using hn⟩
  · have he (v : Vec) : f (y,v)=0 := by
      by_contra h
      exact hy ⟨(y,v),subset_tsupport _ h,rfl⟩
    simpa only [he,zero_smul,integral_zero,norm_zero] using hC

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_InitialSignedBoundaryDensity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma signedPrimitive_scaled (a u n : Vec) (hD : 1-dot n a≠0) :
    (1-dot n a) • signedPrimitive a u n =
      (1-dot n a) • u-(1-dot a u) • n := by
  rw [signedPrimitive,smul_sub,smul_smul,mul_div_cancel₀ _ hD]

lemma signedPrimitive_scaled_norm (w v n : Vec) (hn : ‖n‖=1) :
    ‖(1-dot n (velocity w)) • signedPrimitive (velocity w) (velocity v) n‖≤4 := by
  rw [signedPrimitive_scaled _ _ _ (cone_denom_pos w n hn).ne']
  have he : |1-dot (velocity w) (velocity v)|≤2 :=
    (abs_sub _ _).trans (by
      have hh := abs_dot_le (velocity w) (velocity v)
      have hu := norm_velocity_lt_one w
      have hv := norm_velocity_lt_one v
      have hprod : ‖velocity w‖*‖velocity v‖≤1 :=
        (mul_le_of_le_one_left (norm_nonneg _) hu.le).trans hv.le
      norm_num only [abs_one]
      linarith)
  calc
    _ ≤ ‖(1-dot n (velocity w)) • velocity v‖+‖(1-dot (velocity w) (velocity v)) • n‖ := norm_sub_le _ _
    _ = (1-dot n (velocity w))*‖velocity v‖+|1-dot (velocity w) (velocity v)| := by
      rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,hn,mul_one,
        abs_of_pos (cone_denom_pos w n hn)]
    _ ≤ 2*1+2 := by
      gcongr
      · exact cone_denom_le_two w n hn
      · exact (norm_velocity_lt_one v).le
    _ = 4 := by norm_num

lemma initialSignedBoundaryDensity_eq (f : Phase→ℝ) (x w : Vec) (t ψ χ : ℝ)
    (P : Vec→L[ℝ]Vec) (n v : Vec) :
    initialSignedBoundaryDensity f x w t ψ χ P n v =
      (t*ψ*χ*f (x-t • n,v)/(1-dot n (velocity v))) •
        P ((1-dot n (velocity w)) • signedPrimitive (velocity w) (velocity v) n) := by
  simp only [initialSignedBoundaryDensity,retardedPrimitive,map_smul,smul_smul]
  congr 1
  by_cases ht : t=0
  · simp [ht]
  · by_cases hd : 1-dot n (velocity v)=0
    · simp [hd]
    · field_simp

lemma initialSignedBoundaryDensity_norm (f : Phase→ℝ) (hf : ∀ z,0≤f z)
    (x w : Vec) {t χ M : ℝ} (ht : 0≤t) (hχ : χ∈Icc (0:ℝ) 1)
    (ψ : ℝ) (P : Vec→L[ℝ]Vec) (hP : ‖P‖≤M) (n v : Vec) (hn : ‖n‖=1) :
    ‖initialSignedBoundaryDensity f x w t ψ χ P n v‖≤
      (4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v))) := by
  have hM : 0≤M := (norm_nonneg P).trans hP
  have hd := cone_denom_pos v n hn
  have hfv := hf (x-t • n,v)
  have hχ0 := hχ.1
  rw [initialSignedBoundaryDensity_eq f x w t ψ χ P n v,
    norm_smul,Real.norm_eq_abs,abs_div,abs_mul,abs_mul,abs_mul,
    abs_of_nonneg ht,abs_of_nonneg hχ.1,abs_of_nonneg (hf _),abs_of_pos hd]
  calc
    _ ≤ (t*|ψ| *χ*f (x-t • n,v)/(1-dot n (velocity v)))*(M*4) := by
      apply mul_le_mul_of_nonneg_left
        ((ContinuousLinearMap.le_opNorm P _).trans
          (mul_le_mul hP (signedPrimitive_scaled_norm w v n hn) (norm_nonneg _) hM))
      positivity
    _ ≤ (t*|ψ| *1*f (x-t • n,v)/(1-dot n (velocity v)))*(M*4) := by
      gcongr
      exact hχ.2
    _ = _ := by ring

lemma datum_reciprocal_cone_bound {f : Phase→ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    :
    ∃ C : ℝ,0≤C ∧ ∀ y n : Vec,‖n‖=1 →
      Integrable (fun v : Vec=>f (y,v)/(1-dot n (velocity v))) ∧
      (∫ v : Vec,f (y,v)/(1-dot n (velocity v)))≤C := by
  have hu : Continuous (fun p : Vec×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hd : Continuous (fun p : Vec×Vec=>1-dot p.1 (velocity p.2)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (continuous_fst.prodMk hu))
  have hi : ContinuousOn (fun p : Vec×Vec=>(1-dot p.1 (velocity p.2))⁻¹)
      (sphere (0:Vec) 1 ×ˢ univ) := hd.continuousOn.inv₀ (by
        intro p hp
        exact (cone_denom_pos p.2 p.1 (mem_sphere_zero_iff_norm.mp hp.1)).ne')
  obtain ⟨C,hC,hbound⟩ := uniform_datum_velocity_integral_bound hf hc hi
  refine ⟨C,hC,?_⟩
  intro y n hn
  have hdv : Continuous (fun v : Vec=>1-dot n (velocity v)) :=
    hd.comp (continuous_const.prodMk continuous_id)
  have hh : Continuous (fun v : Vec=>f (y,v)/(1-dot n (velocity v))) :=
    (hf.comp (continuous_const.prodMk continuous_id)).div hdv (fun v=>(cone_denom_pos v n hn).ne')
  obtain ⟨K,hK,hz⟩ := datum_velocity_support hc
  refine ⟨hh.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK ?_),?_⟩
  · intro v hv
    rw [hz y v hv,zero_div]
  · have hh := hbound y n hn
    simp only [smul_eq_mul,← div_eq_mul_inv,Real.norm_eq_abs] at hh
    exact (le_abs_self _).trans hh

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedRadiusSeparatedClosed
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.initial_branch_pullback {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T) (n : Sphere) (v : Vec) :
    let y := (F.flow zX t).1-t • n.1
    branchTime F.flow zX (y,v) T 0=t ∧
      branchDirection F.flow zX (y,v) T 0=n.1 := by
  let y := (F.flow zX t).1-t • n.1
  have hT : 0≤T := ht.1.le.trans ht.2.le
  have hgeom : (F.flow zX t).1-y=t • n.1 := by dsimp only [y]; abel
  have hnorm : ‖(F.flow zX t).1-y‖=t := by
    rw [hgeom,norm_smul,Real.norm_eq_abs,abs_of_pos ht.1,sphere_norm n,mul_one]
  have hm := (F.arrival_strictMono hT zX y).monotoneOn
    (Ioo_subset_Icc_self ht) ⟨hT,le_rfl⟩ ht.2.le
  have hclosed : 0∈closedBranchDomain F.flow zX (y,v) T := by
    refine ⟨⟨le_rfl,hT⟩,?_⟩
    rw [F.initial,zero_add]
    rw [hnorm] at hm
    linarith
  have htime : branchTime F.flow zX (y,v) T 0=t := by
    symm
    apply F.branch_unique_closed zX (y,v) hclosed (Ioo_subset_Icc_self ht)
    rw [F.initial,sub_zero]
    exact hnorm.symm
  refine ⟨htime,?_⟩
  dsimp only [branchDirection]
  rw [htime,F.initial,sub_zero,hgeom,smul_smul,inv_mul_cancel₀ ht.1.ne',one_smul]

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma continuousOn_retardedPrimitive_space {Q : Type*} [TopologicalSpace Q] {r : Q → ℝ} {a u n : Q → Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S)
    (hu : ContinuousOn u S) (hn : ContinuousOn n S)
    (hr0 : ∀ s ∈ S, r s ≠ 0) (hd : ∀ s ∈ S, 1-dot (n s) (u s) ≠ 0)
    (hD : ∀ s ∈ S, 1-dot (n s) (a s) ≠ 0) :
    ContinuousOn (fun s => retardedPrimitive (r s) (a s) (u s) (n s)) S := by
  have hdu : ContinuousOn (fun s => 1-dot (n s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (hn.inner hu)
  have hDa : ContinuousOn (fun s => 1-dot (n s) (a s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (hn.inner ha)
  have hea : ContinuousOn (fun s => 1-dot (a s) (u s)) S := by
    simp only [dot_eq_inner]
    exact (continuousOn_const : ContinuousOn (fun _ : Q => (1 : ℝ)) S).sub (ha.inner hu)
  exact ((hr.mul hdu).inv₀ (fun s hs => mul_ne_zero (hr0 s hs) (hd s hs))).smul
    (hu.sub ((hea.div hDa hD).smul hn))

lemma PhaseFlowOn.initial_closed_branch_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX zY : Phase)
    (hy : zY∈initialClosedCone F.flow zX T) :
    0∈closedBranchDomain F.flow zX zY T := by
  refine ⟨⟨le_rfl,hT⟩,?_⟩
  simpa only [initialClosedCone,Set.mem_ofPred,F.initial,zero_add] using hy

lemma PhaseFlowOn.initial_branch_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ∃ C : ℝ≥0,LipschitzOnWith C (fun z=>branchTime F.flow zX z T 0)
      (initialClosedCone F.flow zX T) := by
  obtain ⟨c,hc,hX⟩ := F.timelike hT zX
  let C : ℝ≥0 := ⟨1/(1-(c:ℝ)),by positivity⟩
  refine ⟨C,LipschitzOnWith.of_dist_le_mul ?_⟩
  intro z hz w hw
  obtain ⟨ht,het⟩ := F.branch_spec_closed zX z (F.initial_closed_branch_mem hT zX z hz)
  obtain ⟨hu,heu⟩ := F.branch_spec_closed zX w (F.initial_closed_branch_mem hT zX w hw)
  let t := branchTime F.flow zX z T 0
  let u := branchTime F.flow zX w T 0
  have htu := hX.dist_le_mul t ht u hu
  have he : t-u=‖(F.flow zX t).1-z.1‖-‖(F.flow zX u).1-w.1‖ := by
    rw [F.initial,sub_zero] at het heu
    exact congrArg₂ (fun a b : ℝ=>a-b) het heu
  have hdist : dist t u≤(c:ℝ)*dist t u+dist z w := by
    have hn := abs_norm_sub_norm_le ((F.flow zX t).1-z.1) ((F.flow zX u).1-w.1)
    have hh : ‖((F.flow zX t).1-z.1)-((F.flow zX u).1-w.1)‖≤
        dist (F.flow zX t).1 (F.flow zX u).1+dist z.1 w.1 := by
      rw [dist_eq_norm,dist_eq_norm]
      calc
        _ = ‖((F.flow zX t).1-(F.flow zX u).1)-(z.1-w.1)‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [← he,← Real.dist_eq] at hn
    exact (hn.trans hh).trans (add_le_add htu (show dist z.1 w.1≤dist z w from le_max_left _ _))
  change dist t u≤(1/(1-(c:ℝ)))*dist z w
  rw [div_mul_eq_mul_div,one_mul]
  apply (le_div_iff₀ (sub_pos.mpr hc)).mpr
  nlinarith

lemma PhaseFlowOn.initial_primitive_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ContinuousOn (fun z : Phase=>
      retardedPrimitive (branchTime F.flow zX z T 0)
        (velocity (F.flow zX (branchTime F.flow zX z T 0)).2)
        (velocity z.2) (branchDirection F.flow zX z T 0))
      (initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}) := by
  let A := initialClosedCone F.flow zX T ∩ {z : Phase | z.1≠zX.1}
  let τ := fun z=>branchTime F.flow zX z T 0
  have hm : ∀ z∈A,0∈closedBranchDomain F.flow zX z T := fun z hz=>
    F.initial_closed_branch_mem hT zX z hz.1
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>(F.branch_spec_closed zX z (hm z hz)).1
  have hne : ∀ z∈A,(F.flow zX 0).1≠(F.flow z 0).1 := by
    intro z hz
    simpa only [F.initial] using Ne.symm hz.2
  have hpos : ∀ z∈A,τ z≠0 := by
    intro z hz
    have hh := F.branch_radius_pos_closed zX z (hm z hz) (hne z hz)
    simpa only [sub_zero] using hh.ne'
  have ht : ContinuousOn τ A := by
    obtain ⟨C,hC⟩ := F.initial_branch_lipschitz hT zX
    exact hC.continuousOn.mono inter_subset_left
  have hX := (F.continuousOn_time zX).comp ht htm
  have hn : ContinuousOn (fun z=>branchDirection F.flow zX z T 0) A := by
    convert (ht.inv₀ hpos).smul (hX.fst.sub continuous_fst.continuousOn) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp only [branchDirection,sub_zero,F.initial,τ,Function.comp_apply]
    rfl
  have ha := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hX.snd
  have hu : ContinuousOn (fun z : Phase=>velocity z.2) A :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn continuous_snd.continuousOn
  have hn1 : ∀ z∈A,‖branchDirection F.flow zX z T 0‖=1 := fun z hz=>
    F.branchDirection_norm_closed zX z (hm z hz) (hne z hz)
  exact continuousOn_retardedPrimitive_space ht ha hu hn hpos
    (fun z hz=>(cone_denom_pos z.2 _ (hn1 z hz)).ne')
    (fun z hz=>(cone_denom_pos (F.flow zX (τ z)).2 _ (hn1 z hz)).ne')

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CutoffState
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma selectedDyadicCutoff_eventually {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ∃ N : ℕ, selectedDyadicCutoff S =ᶠ[𝓝 x]
      (fun y => ∑ n∈selectedDyadicBox N S,dyadicMultiFactor n y) := by
  classical
  have hp (i : ι) := pow_unbounded_of_one_lt (4/x i) (by norm_num : (1:ℝ)<2)
  choose Ns hNs using hp
  let N := ∑ i,Ns i
  have hN (i : ι) : 4<(2:ℝ)^N*x i := by
    have hNi : Ns i≤N := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    exact ((div_lt_iff₀ (hx i)).mp (hNs i)).trans_le
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hNi) (hx i).le)
  have he : ∀ᶠ y in 𝓝 x, ∀ i,x i/2<y i := by
    apply Filter.eventually_all.mpr
    intro i
    exact (continuous_apply i).continuousAt.eventually (Ioi_mem_nhds (by linarith [hx i]))
  refine ⟨N,?_⟩
  filter_upwards [he] with y hy
  have hz : ∀ n : ι→ℕ,n∉dyadicBox ι N → dyadicMultiFactor n y=0 := by
    intro n hn
    have hb : ∃ i,N≤n i := by
      by_contra hb
      push Not at hb
      apply hn
      simpa only [dyadicBox,Fintype.mem_piFinset,Finset.mem_range] using hb
    obtain ⟨i,hi⟩ := hb
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply dyadicFactor_zero_large
    have hpN : 0<(2:ℝ)^N := by positivity
    have hpni : (2:ℝ)^N≤(2:ℝ)^(n i) := pow_le_pow_right₀ (by norm_num) hi
    have hyr : 0≤y i := le_of_lt ((by linarith [hx i] : 0<x i/2).trans (hy i))
    have hh := mul_le_mul_of_nonneg_right hpni hyr
    have hh' := mul_lt_mul_of_pos_left (hy i) hpN
    linarith [hN i]
  unfold selectedDyadicCutoff
  rw [tsum_eq_sum (s:=dyadicBox ι N) (fun n hn => ?_)]
  · simpa only [selectedDyadicBox,id_eq] using
      (Finset.sum_indicator_eq_sum_filter (dyadicBox ι N)
        (fun _ n => dyadicMultiFactor n y) (fun _ => S) id)
  · by_cases hs : n∈S
    · rw [indicator_of_mem hs,hz n hn]
    · exact indicator_of_notMem hs _

lemma contDiffAt_selectedDyadicCutoff {ι : Type*} [Fintype ι]
    {x : ι→ℝ} (hx : ∀ i,0<x i) (S : Set (ι→ℕ)) :
    ContDiffAt ℝ ∞ (selectedDyadicCutoff S) x := by
  classical
  obtain ⟨N,he⟩ := selectedDyadicCutoff_eventually hx S
  apply (ContDiffAt.sum (s:=selectedDyadicBox N S) (fun n _ => ?_)).congr_of_eventuallyEq he
  exact contDiffAt_prod (fun i _ => (contDiff_dyadicFactor (n i)).contDiffAt.comp x (contDiff_apply ℝ ℝ i).contDiffAt)

lemma contDiffAt_stateCutoff (T : ℝ) (Q : Set (Fin 4→ℕ)) {z : CutoffState}
    (hr : 0<z.1) (hn : ‖z.2.1‖=1) : ContDiffAt ℝ ∞ (stateCutoff T Q) z := by
  have hc : ContDiffAt ℝ ∞ (fun z : CutoffState =>
      physicalCutoffCoordinates T z.1 z.2.1 z.2.2.1 z.2.2.2) z := by
    apply contDiffAt_pi.mpr
    intro i
    have hv : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.1) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst
    have hw : ContDiffAt ℝ ∞ (fun z : CutoffState=>velocity z.2.2.2) z :=
      (contDiff_velocity (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.snd
    have hd := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hv))
    have hD := (contDiffAt_const (c:=(1:ℝ))).sub
      ((contDiff_dot_pair (k:=∞)).contDiffAt.comp z (contDiffAt_id.snd.fst.prodMk hw))
    fin_cases i <;> simp only [physicalCutoffCoordinates]
    · exact contDiffAt_const.div ((contDiff_q (k:=∞)).contDiffAt.comp z contDiffAt_id.snd.snd.fst) (q_pos _).ne'
    · exact (hd.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact (hD.div_const 2).sqrt (div_pos (cone_denom_pos _ _ hn) (by norm_num)).ne'
    · exact contDiffAt_id.fst.div_const _
  exact (contDiffAt_selectedDyadicCutoff (physicalCutoffCoordinates_pos hn hr) Q).comp z hc

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma initialSignedBoundary_velocity_lintegral_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (x w : Vec) (t ψ M : ℝ) (χ : Vec→ℝ)
      (P : Vec→L[ℝ]Vec) (n : Vec), 0≤t → (∀ v,χ v∈Icc (0:ℝ) 1) →
      ‖P‖≤M → ‖n‖=1 →
      (∫⁻ v : Vec, ENNReal.ofReal ‖initialSignedBoundaryDensity f x w t ψ (χ v) P n v‖)
        ≤ ENNReal.ofReal (C*t*|ψ| *M) := by
  obtain ⟨C,hC,hbound⟩ := datum_reciprocal_cone_bound hf hc
  refine ⟨4*C,by positivity,?_⟩
  intro x w t ψ M χ P n ht hχ hP hn
  have hM : 0≤M := (norm_nonneg P).trans hP
  obtain ⟨hgi,hgb⟩ := hbound (x-t • n) n hn
  have hgn (v : Vec) : 0≤f (x-t • n,v)/(1-dot n (velocity v)) :=
    div_nonneg (hpos _) (cone_denom_pos v n hn).le
  calc
    _ ≤ ∫⁻ v : Vec, ENNReal.ofReal
        ((4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v)))) := by
      apply lintegral_mono
      intro v
      exact ENNReal.ofReal_le_ofReal (initialSignedBoundaryDensity_norm f hpos x w ht (hχ v) ψ P hP n v hn)
    _ = ENNReal.ofReal (∫ v : Vec,
        (4*t*|ψ| *M)*(f (x-t • n,v)/(1-dot n (velocity v)))) :=
      (ofReal_integral_eq_lintegral_ofReal (hgi.const_mul _)
        (ae_of_all _ (fun v=>mul_nonneg (by positivity) (hgn v)))).symm
    _ ≤ ENNReal.ofReal ((4*C)*t*|ψ| *M) := by
      apply ENNReal.ofReal_le_ofReal
      rw [integral_const_mul]
      nlinarith [mul_le_mul_of_nonneg_left hgb (show 0≤4*t*|ψ| *M by positivity)]

lemma initialSignedBoundary_lintegral_bound {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (T M : ℝ) (J : Set ℝ) (X V : ℝ→Vec)
      (ψ : ℝ→ℝ) (χ : ℝ→Sphere→Vec→ℝ) (P : ℝ→Vec→L[ℝ]Vec),
      0≤T → 0≤M → MeasurableSet J → J⊆Icc 0 T → IntegrableOn ψ J →
      (∀ t∈J,∀ n v,χ t n v∈Icc (0:ℝ) 1) → (∀ t∈J,‖P t‖≤M) →
      (∫⁻ t in J,∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal ‖initialSignedBoundaryDensity f (X t) (V t) t (ψ t)
          (χ t n v) (P t) n.1 v‖ ∂volume ∂sphereMeasure)
        ≤ ENNReal.ofReal (C*T*M*(∫ t in J,|ψ t|)) := by
  obtain ⟨C,hC,hb⟩ := initialSignedBoundary_velocity_lintegral_bound hf hc hpos
  refine ⟨C*(4*Real.pi),by positivity,?_⟩
  intro T M J X V ψ χ P hT hM hJ hJT hψ hχ hP
  calc
    _ ≤ ∫⁻ t in J, ∫⁻ _n : Sphere, ENNReal.ofReal (C*t*|ψ t| *M) ∂sphereMeasure := by
      apply setLIntegral_mono' hJ
      intro t ht
      apply lintegral_mono
      intro n
      exact hb (X t) (V t) t (ψ t) M (χ t n) (P t) n.1 (hJT ht).1 (hχ t ht n) (hP t ht) (sphere_norm n)
    _ = ∫⁻ t in J, ENNReal.ofReal (C*t*|ψ t| *M*(4*Real.pi)) := by
      apply setLIntegral_congr_fun hJ
      intro t ht
      have ht0 := (hJT ht).1
      dsimp only
      rw [lintegral_const, ← ofReal_measureReal, sphere_area, ← ENNReal.ofReal_mul (by positivity)]
    _ ≤ ∫⁻ t in J, ENNReal.ofReal ((C*(4*Real.pi)*T*M)*|ψ t|) := by
      apply setLIntegral_mono' hJ
      intro t ht
      apply ENNReal.ofReal_le_ofReal
      nlinarith [mul_le_mul_of_nonneg_right (hJT ht).2
        (show 0≤C*|ψ t| *M*(4*Real.pi) by positivity)]
    _ = ENNReal.ofReal ((C*(4*Real.pi))*T*M*(∫ t in J,|ψ t|)) := by
      rw [← ofReal_integral_eq_lintegral_ofReal (hψ.abs.const_mul _)
        (ae_of_all _ (fun t=>by positivity)), integral_const_mul]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_InitialPuncturedCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.initial_label_lintegral {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase)
    {g : Phase→ENNReal} (hg : Measurable g) :
    (∫⁻ z in initialConeLabels T (F.flow zX T).1, g z) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal (t^2*(1-dot n.1 (velocity (F.flow zX t).2))) *
          g ((F.flow zX t).1-t • n.1,v) ∂volume ∂sphereMeasure := by
  classical
  let A := initialConeLabels T (F.flow zX T).1
  have hA : MeasurableSet A :=
    (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
  have hX : Continuous (prefixFlow F.flow T zX) := by
    exact (F.continuousOn_time zX).comp_continuous
      (continuous_const.max (continuous_const.min continuous_id)) (prefixClamp_mem hT)
  let k : Sphere→ℝ→ENNReal := fun n t=>
    ENNReal.ofReal (t^2*(1-dot n.1 (velocity (prefixFlow F.flow T zX t).2))) *
      ∫⁻ v : Vec,g ((prefixFlow F.flow T zX t).1-t • n.1,v)
  have hk : Measurable (Function.uncurry k) := by
    have hn : Measurable (fun p : Sphere×ℝ => (p.1:Vec)) :=
      measurable_subtype_coe.comp measurable_fst
    have hx := hX.measurable.comp (measurable_snd : Measurable (Prod.snd : Sphere×ℝ→ℝ))
    have hv := (contDiff_velocity (k:=1)).continuous.measurable.comp hx.snd
    have hr : Measurable (fun p : Sphere×ℝ =>
        p.2^2*(1-dot (p.1:Vec) (velocity (prefixFlow F.flow T zX p.2).2))) := by
      simp only [dot_eq_inner]
      exact (measurable_snd.pow_const 2).mul
        ((measurable_const (a:=(1:ℝ))).sub (hn.inner hv))
    have hg' : Measurable (fun p : (Sphere×ℝ)×Vec =>
        g ((prefixFlow F.flow T zX p.1.2).1-p.1.2 • (p.1.1:Vec),p.2)) := by
      exact hg.comp (((hx.fst.sub (measurable_snd.smul hn)).comp measurable_fst).prodMk measurable_snd)
    exact hr.ennreal_ofReal.mul hg'.lintegral_prod_right'
  calc
    _ = ∫⁻ y : Vec, ∫⁻ v : Vec, A.indicator g (y,v) := by
      rw [← lintegral_indicator hA]
      exact lintegral_prod _ (hg.indicator hA).aemeasurable
    _ = ∫⁻ y in ball (F.flow zX T).1 T, ∫⁻ v : Vec,g (y,v) := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y∈ball (F.flow zX T).1 T
      · rw [indicator_of_mem hy]
        apply lintegral_congr
        intro v
        apply indicator_of_mem
        simpa only [A,initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hy
      · rw [indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        apply indicator_of_notMem
        intro hz
        apply hy
        simpa only [A,initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hz
    _ = ∫⁻ n : Sphere,∫⁻ t in Ioo (0:ℝ) T,k n t ∂volume ∂sphereMeasure := by
      have hh := F.receiver_polar_lintegral (s:=0) ⟨le_rfl,hT⟩ zX (hg.lintegral_prod_right' (ν:=volume))
      simp only [sub_zero,zero_add] at hh
      rw [hh]
      apply lintegral_congr
      intro n
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      simp only [k,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
    _ = ∫⁻ t in Ioo (0:ℝ) T,∫⁻ n : Sphere,k n t ∂sphereMeasure :=
      lintegral_lintegral_swap hk.aemeasurable
    _ = _ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply lintegral_congr
      intro n
      simp only [k,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
      exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm

lemma isOpen_initialPuncturedCone (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) :
    IsOpen (initialPuncturedCone α zX T) :=
  (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).inter
    (isClosed_eq continuous_fst continuous_const).isOpen_compl

lemma initialPuncturedCone_sub (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ) :
    initialPuncturedCone α zX T ⊆ initialClosedCone α zX T ∩ {z : Phase | z.1≠zX.1} :=
  by
    intro z hz
    refine ⟨?_,hz.2⟩
    change ‖(α zX T).1-z.1‖≤T
    exact le_of_lt hz.1

lemma PhaseFlowOn.initial_spherical_label_mem {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T) (n : Sphere) (v : Vec) :
    ((F.flow zX t).1-t • n.1,v)∈initialPuncturedCone F.flow zX T := by
  have hT : 0≤T := ht.1.le.trans ht.2.le
  have hn : ‖t • n.1‖=t := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos ht.1,sphere_norm n,mul_one]
  have hm : t • n.1 ∈ receiverRadialDomain 0 T := by
    change 0<‖t • n.1‖ ∧ 0+‖t • n.1‖<T
    simpa only [hn,zero_add,mem_Ioo] using ht
  have hi := mem_image_of_mem (receiverRadial F.flow zX 0) hm
  rw [F.receiver_image ⟨le_rfl,hT⟩ zX] at hi
  simp only [receiverRadial,hn,zero_add,sub_zero,F.initial,Set.mem_sdiff,mem_singleton_iff] at hi
  refine ⟨?_,hi.2⟩
  simpa only [initialConeLabels,mem_ofPred_eq,mem_ball,dist_eq_norm,norm_sub_rev] using hi.1

lemma PhaseFlowOn.initial_state_regular {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) :
    ContinuousOn (initialConeState F.flow zX T) (initialPuncturedCone F.flow zX T) ∧
    ∀ z∈initialPuncturedCone F.flow zX T,
      0<(initialConeState F.flow zX T z).1 ∧
      (initialConeState F.flow zX T z).1≤T ∧
      ‖(initialConeState F.flow zX T z).2.1‖=1 := by
  let A := initialPuncturedCone F.flow zX T
  let τ := fun z=>branchTime F.flow zX z T 0
  have hm : ∀ z∈A,0∈closedBranchDomain F.flow zX z T := fun z hz=>
    F.initial_closed_branch_mem hT zX z ((initialPuncturedCone_sub F.flow zX T hz).1)
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>(F.branch_spec_closed zX z (hm z hz)).1
  have hne : ∀ z∈A,(F.flow zX 0).1≠(F.flow z 0).1 := by
    intro z hz
    simpa only [F.initial] using Ne.symm hz.2
  have hpos : ∀ z∈A,0<τ z := by
    intro z hz
    simpa only [sub_zero] using F.branch_radius_pos_closed zX z (hm z hz) (hne z hz)
  have ht : ContinuousOn τ A := by
    obtain ⟨C,hC⟩ := F.initial_branch_lipschitz hT zX
    exact hC.continuousOn.mono (fun z hz=>(initialPuncturedCone_sub F.flow zX T hz).1)
  have hX := (F.continuousOn_time zX).comp ht htm
  have hn : ContinuousOn (fun z=>branchDirection F.flow zX z T 0) A := by
    convert (ht.inv₀ (fun z hz=>(hpos z hz).ne')).smul
      (hX.fst.sub continuous_fst.continuousOn) using 1
    all_goals try with_reducible_and_instances rfl
    funext z
    simp only [branchDirection,sub_zero,F.initial,τ,Function.comp_apply]
    rfl
  refine ⟨ht.prodMk (hn.prodMk (continuous_snd.continuousOn.prodMk hX.snd)),?_⟩
  intro z hz
  exact ⟨hpos z hz,(htm hz).2,F.branchDirection_norm_closed zX z (hm z hz) (hne z hz)⟩

lemma PhaseFlowOn.initial_selected_cutoff {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (Q : Set (Fin 4→ℕ)) :
    ContinuousOn (fun z=>stateCutoff T Q (initialConeState F.flow zX T z))
      (initialPuncturedCone F.flow zX T) ∧
    ∀ z∈initialPuncturedCone F.flow zX T,
      stateCutoff T Q (initialConeState F.flow zX T z)∈Icc (0:ℝ) 1 := by
  obtain ⟨hc,hb⟩ := F.initial_state_regular hT zX
  constructor
  · intro z hz
    exact ((contDiffAt_stateCutoff T Q (hb z hz).1 (hb z hz).2.2).continuousAt).comp_continuousWithinAt (hc z hz)
  · intro z hz
    apply selectedDyadicCutoff_mem_unit
    · exact physicalCutoffCoordinates_pos (hb z hz).2.2 (hb z hz).1
    · exact physicalCutoffCoordinates_le_one (hb z hz).2.2 ((hb z hz).2.1.trans (le_max_right _ _))

lemma PhaseFlowOn.selected_initial_kernel_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) {f : Phase→ℝ}
    (hf : Continuous f) (Q : Set (Fin 4→ℕ)) {ψ : ℝ→ℝ}
    (hψ : ContinuousOn ψ (Icc 0 T)) {W : ℝ→Vec→L[ℝ]Vec}
    (hW : ContinuousOn W (Icc 0 T)) :
    Measurable (selectedInitialKernel F.flow zX T f Q ψ W) := by
  classical
  let A := initialPuncturedCone F.flow zX T
  let τ := fun z=>branchTime F.flow zX z T 0
  have htm : MapsTo τ A (Icc 0 T) := fun z hz=>
    (F.branch_spec_closed zX z (F.initial_closed_branch_mem hT zX z
      ((initialPuncturedCone_sub F.flow zX T hz).1))).1
  have ht : ContinuousOn τ A := (F.initial_state_regular hT zX).1.fst
  have hχ := (F.initial_selected_cutoff hT zX Q).1
  have hp := (F.initial_primitive_continuousOn hT zX).mono (initialPuncturedCone_sub F.flow zX T)
  have hc := ((hf.continuousOn.mul (hψ.comp ht htm)).mul hχ).smul
    ((hW.comp ht htm).clm_apply hp)
  have h := hc.measurable_piecewise (continuousOn_const (c:=(0:Vec)))
    (isOpen_initialPuncturedCone F.flow zX T).measurableSet
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext z
  rfl

lemma PhaseFlowOn.selected_initial_kernel_pullback {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (ht : t∈Ioo 0 T)
    (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ) (W : ℝ→Vec→L[ℝ]Vec)
    (n : Sphere) (v : Vec) :
    (t^2*(1-dot n.1 (velocity (F.flow zX t).2))) •
      selectedInitialKernel F.flow zX T f Q ψ W ((F.flow zX t).1-t • n.1,v) =
    initialSignedBoundaryDensity f (F.flow zX t).1 (F.flow zX t).2 t (ψ t)
      (stateCutoff T Q (t,n.1,v,(F.flow zX t).2)) (W t) n.1 v := by
  rw [selectedInitialKernel,indicator_of_mem (F.initial_spherical_label_mem zX ht n v)]
  obtain ⟨hτ,hn⟩ := F.initial_branch_pullback zX ht n v
  simp only [initialConeState,hτ,hn]
  simp only [initialSignedBoundaryDensity,smul_smul]
  congr 1
  ring

lemma selectedInitialKernel_integrable_bound_oai {f : Phase→ℝ}
    (hf : Continuous f) (hc : HasCompactSupport f) (hpos : ∀ z,0≤f z) :
    ∃ C : ℝ,0≤C ∧ ∀ (E B : Field) (T : ℝ) (F : PhaseFlowOn E B T)
      (zX : Phase) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
      (W : ℝ→Vec→L[ℝ]Vec) (M : ℝ),
      0≤T → 0≤M → ContinuousOn ψ (Icc 0 T) → ContinuousOn W (Icc 0 T) →
      (∀ t∈Icc 0 T,‖W t‖≤M) →
      Integrable (selectedInitialKernel F.flow zX T f Q ψ W) ∧
      ‖∫ z : Phase,selectedInitialKernel F.flow zX T f Q ψ W z‖ ≤
        C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|) := by
  obtain ⟨C,hC,hb⟩ := initialSignedBoundary_lintegral_bound hf hc hpos
  refine ⟨C,hC,?_⟩
  intro E B T F zX Q ψ W M hT hM hψ hW hWM
  let G := selectedInitialKernel F.flow zX T f Q ψ W
  have hG : Measurable G := F.selected_initial_kernel_measurable hT zX hf Q hψ hW
  have hψi : IntegrableOn ψ (Ioo 0 T) :=
    (hψ.integrableOn_compact isCompact_Icc).mono_set Ioo_subset_Icc_self
  let χ := fun t (n : Sphere) v=>stateCutoff T Q (t,n.1,v,(F.flow zX t).2)
  have hχ : ∀ t∈Ioo (0:ℝ) T,∀ n v,χ t n v∈Icc (0:ℝ) 1 := by
    intro t ht n v
    apply selectedDyadicCutoff_mem_unit
    · exact physicalCutoffCoordinates_pos (sphere_norm n) ht.1
    · exact physicalCutoffCoordinates_le_one (sphere_norm n) (ht.2.le.trans (le_max_right _ _))
  have heq : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖) =
      ∫⁻ t in Ioo (0:ℝ) T,∫⁻ n : Sphere,∫⁻ v : Vec,
        ENNReal.ofReal ‖initialSignedBoundaryDensity f (F.flow zX t).1 (F.flow zX t).2 t
          (ψ t) (χ t n v) (W t) n.1 v‖ ∂volume ∂sphereMeasure := by
    calc
      _ = ∫⁻ z in initialConeLabels T (F.flow zX T).1,ENNReal.ofReal ‖G z‖ := by
        have hA : MeasurableSet (initialConeLabels T (F.flow zX T).1) :=
          (isOpen_lt ((continuous_const.sub continuous_fst).norm) continuous_const).measurableSet
        rw [← lintegral_indicator hA]
        apply lintegral_congr
        intro z
        by_cases hz : z∈initialConeLabels T (F.flow zX T).1
        · rw [indicator_of_mem hz]
        · rw [indicator_of_notMem hz]
          have hz' : z∉initialPuncturedCone F.flow zX T := fun hh=>hz hh.1
          simp only [G,selectedInitialKernel,indicator_of_notMem hz',norm_zero,ENNReal.ofReal_zero]
      _ = _ := by
        rw [F.initial_label_lintegral hT zX hG.norm.ennreal_ofReal]
        apply setLIntegral_congr_fun measurableSet_Ioo
        intro t ht
        apply lintegral_congr
        intro n
        apply lintegral_congr
        intro v
        have hr : 0≤t^2*(1-dot n.1 (velocity (F.flow zX t).2)) :=
          mul_nonneg (sq_nonneg _) (cone_denom_pos _ _ (sphere_norm n)).le
        have hp := congrArg (fun x : Vec=>ENNReal.ofReal ‖x‖)
          (F.selected_initial_kernel_pullback zX ht f Q ψ W n v)
        simpa only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hr,ENNReal.ofReal_mul hr] using hp
  have hbound : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖) ≤
      ENNReal.ofReal (C*T*M*(∫ t in Ioo (0:ℝ) T,|ψ t|)) := by
    rw [heq]
    exact hb T M (Ioo 0 T) (fun t=>(F.flow zX t).1) (fun t=>(F.flow zX t).2)
      ψ χ W hT hM measurableSet_Ioo Ioo_subset_Icc_self hψi hχ
      (fun t ht=>hWM t (Ioo_subset_Icc_self ht))
  have hfinite : (∫⁻ z : Phase,ENNReal.ofReal ‖G z‖)<⊤ :=
    hbound.trans_lt ENNReal.ofReal_lt_top
  refine ⟨⟨hG.aestronglyMeasurable,(hasFiniteIntegral_iff_norm G).mpr hfinite⟩,?_⟩
  apply (norm_integral_le_lintegral_norm G).trans
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound).trans
    (le_of_eq (ENNReal.toReal_ofReal (by positivity)))

end RVM

end

open MeasureTheory Set
open Filter Set
open scoped Topology
open scoped Topology Pointwise
open Set MeasureTheory Metric ODE
open scoped Topology NNReal
open scoped ContDiff
open Set MeasureTheory Metric
open Set MeasureTheory Metric Filter ODE
open Set MeasureTheory Filter Metric ODE
open Set MeasureTheory Filter Metric
open scoped Topology NNReal ContDiff
open Set MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open Set
open scoped Topology ContDiff ENNReal
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

end

end OAI
end

theorem solution : type_of% @OAI.RVM.selectedInitialKernel_integrable_bound_oai := @OAI.RVM.selectedInitialKernel_integrable_bound_oai
