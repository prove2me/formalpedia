-- Prove2me | solution 1 for OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:50:06.900189+00:00
-- url     : https://prove2.me/submissions/564fb29a-35c0-415b-894e-f364de2757c2

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V002
import Theorems.Thm_OAI_RVM_PhaseFlowOn_selectedMultiplierCosts_family_bound
import Theorems.Thm_OAI_RVM_SmoothClassicalPrefix_selected_multiplier_decomposition

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

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma hasDerivAt_dot {f g : ℝ → Vec} {f' g' : Vec} {s : ℝ}
    (hf : HasDerivAt f f' s) (hg : HasDerivAt g g' s) :
    HasDerivAt (fun t => dot (f t) (g t))
      (dot (f s) g' + dot f' (g s)) s := by
  simpa only [dot_eq_inner] using hf.inner ℝ hg

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

lemma contDiff_cross {k : ℕ∞ω} : ContDiff ℝ k (fun z : Vec × Vec => cross z.1 z.2) := by
  apply contDiff_euclidean.mpr
  intro i
  fin_cases i
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 1 * z.2 2 - z.1 2 * z.2 1)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 2 * z.2 0 - z.1 0 * z.2 2)
    fun_prop
  · change ContDiff ℝ k (fun z : Vec × Vec => z.1 0 * z.2 1 - z.1 1 * z.2 0)
    fun_prop

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

lemma cone_deficit_positive {x y : Vec} (hxy : x ≠ y) (v : Vec) :
    0 < 1 - dot (‖x-y‖⁻¹ • (x-y)) (velocity v) := by
  have hh := real_inner_le_norm (‖x-y‖⁻¹ • (x-y)) (velocity v)
  rw [norm_coneDirection hxy,one_mul,← dot_eq_inner] at hh
  linarith [norm_velocity_lt_one v]


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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CollisionLabels
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

lemma PhaseFlowOn.branch_spec {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T) :
    branchTime F.flow zX zY T s ∈ Icc s T ∧
      branchTime F.flow zX zY T s-s =
        ‖(F.flow zX (branchTime F.flow zX zY T s)).1-(F.flow zY s).1‖ := by
  have hy : ‖(F.flow zX T).1-(F.flow zY s).1‖ < T-s := by linarith [hs.2]
  obtain ⟨t,⟨ht,he⟩,_⟩ := F.exists_arrival (Ioo_subset_Icc_self hs.1) zX hy
  have hex : ∃ t, t ∈ Icc s T ∧ t-s=‖(F.flow zX t).1-(F.flow zY s).1‖ :=
    ⟨t,ht,by linarith⟩
  simpa only [branchTime,dite_eq_left hex] using hex.choose_spec

lemma PhaseFlowOn.branch_unique {E B : Field} {T s t : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (ht : t ∈ Icc s T) (he : t-s=‖(F.flow zX t).1-(F.flow zY s).1‖) :
    t=branchTime F.flow zX zY T s := by
  obtain ⟨hσ,hcone⟩ := F.branch_spec zX zY hs
  apply (F.arrival_strictMono (hs.1.1.le.trans hs.1.2.le) zX (F.flow zY s).1).injOn
    ⟨hs.1.1.le.trans ht.1,ht.2⟩ ⟨hs.1.1.le.trans hσ.1,hσ.2⟩
  dsimp only
  linarith

lemma PhaseFlowOn.branch_time_mem {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (zX zY : Phase) (hs : s ∈ branchDomain F.flow zX zY T)
    (hne : (F.flow zX s).1 ≠ (F.flow zY s).1) :
    s < branchTime F.flow zX zY T s ∧ branchTime F.flow zX zY T s < T := by
  obtain ⟨ht,he⟩ := F.branch_spec zX zY hs
  constructor
  · by_contra h
    have hts := le_antisymm (le_of_not_gt h) ht.1
    rw [hts,sub_self] at he
    exact hne (sub_eq_zero.mp (norm_eq_zero.mp he.symm))
  · by_contra h
    have htT := le_antisymm ht.2 (le_of_not_gt h)
    rw [htT] at he
    linarith [hs.2]

end RVM
end

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

lemma exists_continuous_scalar_root {W : Type*} [NormedAddCommGroup W]
    [NormedSpace ℝ W] [CompleteSpace W] {H : ℝ × W → ℝ}
    {L : (ℝ × W) →L[ℝ] ℝ} {t : ℝ} {p : W}
    (hH : HasStrictFDerivAt H L (t,p)) (hzero : H (t,p)=0)
    (hk : L (1,0) ≠ 0) :
    ∃ τ : W → ℝ, τ p=t ∧ ContinuousAt τ p ∧ ∀ᶠ q in 𝓝 p, H (τ q,q)=0 := by
  have hL (x : ℝ × W) : L x = x.1 * L (1,0)+L (0,x.2) := by
    have he : x = x.1 • (1,(0 : W))+(0,x.2) := by ext <;> simp
    conv_lhs => rw [he]
    rw [map_add,map_smul,smul_eq_mul]
  let A : (ℝ × W) →L[ℝ] (ℝ × W) := L.prod (ContinuousLinearMap.snd ℝ ℝ W)
  have hi : Function.Injective A := by
    intro x y h
    have hh : L x = L y := congrArg Prod.fst h
    have he : x.2=y.2 := by
      have he := congrArg Prod.snd h
      exact he
    rw [hL x,hL y,he] at hh
    have hf : x.1=y.1 := (mul_right_cancel₀ hk) (add_right_cancel hh)
    exact Prod.ext hf he
  have hs : Function.Surjective A := by
    intro y
    refine ⟨((y.1-L (0,y.2))/L (1,0),y.2),?_⟩
    apply Prod.ext
    · change L ((y.1-L (0,y.2))/L (1,0),y.2)=y.1
      rw [hL]
      dsimp only
      field_simp
      ring
    · rfl
  let e : (ℝ × W) ≃L[ℝ] (ℝ × W) := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hi) (LinearMap.range_eq_top.mpr hs)
  let Φ : ℝ × W → ℝ × W := fun z => (H z,z.2)
  have hΦ : HasStrictFDerivAt Φ (e : (ℝ × W) →L[ℝ] (ℝ × W)) (t,p) :=
    hH.prodMk hasStrictFDerivAt_snd
  let Z := hΦ.localInverse Φ e (t,p)
  have hZ : HasStrictFDerivAt Z (e.symm : (ℝ × W) →L[ℝ] (ℝ × W)) (0,p) := by
    simpa only [Φ,hzero] using hΦ.to_localInverse
  have hZ₀ : Z (0,p)=(t,p) := by
    simpa only [Φ,hzero] using hΦ.localInverse_apply_image
  let τ : W → ℝ := fun q => (Z (0,q)).1
  have hc : ContinuousAt (fun q : W => ((0 : ℝ),q)) p := continuousAt_const.prodMk continuousAt_id
  refine ⟨τ,congrArg Prod.fst hZ₀,hZ.continuousAt.fst.comp hc,?_⟩
  have hev : ∀ᶠ z in 𝓝 (0,p), Φ (Z z)=z := by
    simpa only [Φ,hzero] using hΦ.eventually_right_inverse
  filter_upwards [hc.eventually hev] with q hq
  have he : (Z (0,q)).2=q := congrArg Prod.snd hq
  have hh : H (Z (0,q))=0 := congrArg Prod.fst hq
  have hz : Z (0,q) = (τ q,q) := Prod.ext rfl he
  rwa [hz] at hh

lemma PhaseFlowOn.joint_position_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {p : ℝ × Phase} (hp : p.1 ∈ Ioo 0 T) :
    ContinuousAt (fun q : ℝ × Phase => (F.flow q.2 q.1).1) p :=
  (F.joint p.2 p.1 hp).continuousAt.fst

lemma PhaseFlowOn.isOpen_jointBranchDomain {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) : IsOpen (jointBranchDomain F.flow zX T) := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have hY := F.joint_position_continuousAt hp.1.1
  have hX : ContinuousAt (fun q : ℝ × Phase => (F.flow zX q.1).1) p :=
    (((F.continuousOn_time zX).fst.continuousAt (Icc_mem_nhds hp.1.1.1 hp.1.1.2)).comp
      continuousAt_fst)
  have hd : ContinuousAt (fun q : ℝ × Phase => q.1+‖(F.flow zX T).1-(F.flow q.2 q.1).1‖) p :=
    continuousAt_fst.add ((continuousAt_const.sub hY).norm)
  have ht : ∀ᶠ q : ℝ × Phase in 𝓝 p, q.1 ∈ Ioo 0 T :=
    continuousAt_fst.eventually (isOpen_Ioo.mem_nhds hp.1.1)
  have hb := hd.eventually (isOpen_Iio.mem_nhds hp.1.2)
  have hn := (hX.sub hY).eventually (isOpen_compl_singleton.mem_nhds (sub_ne_zero.mpr hp.2))
  filter_upwards [ht,hb,hn] with q hq hqt hqn
  exact ⟨⟨hq,hqt⟩,sub_ne_zero.mp hqn⟩

lemma PhaseFlowOn.joint_branch_continuousAt {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Phase} (hp : p ∈ jointBranchDomain F.flow zX T) :
    ContinuousAt (fun q : ℝ × Phase => branchTime F.flow zX q.2 T q.1) p := by
  let t := branchTime F.flow zX p.2 T p.1
  have ht := F.branch_time_mem zX p.2 hp.1 hp.2
  have hti : t ∈ Ioo 0 T := ⟨hp.1.1.1.trans ht.1,ht.2⟩
  have hspec := (F.branch_spec zX p.2 hp.1).2
  have hxy : (F.flow zX t).1 ≠ (F.flow p.2 p.1).1 := by
    intro he
    rw [he,sub_self,norm_zero] at hspec
    linarith [ht.1]
  let H : ℝ × (ℝ × Phase) → ℝ := fun q => q.1-q.2.1-‖(F.flow zX q.1).1-(F.flow q.2.2 q.2.1).1‖
  have hmap : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (q.1,zX))
      ((ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)).prod 0) (t,p) :=
    hasStrictFDerivAt_fst.prodMk (hasStrictFDerivAt_const _ _)
  have hparam : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2)
      (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_snd
  have hX : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow zX q.1).1)
      _ (t,p) := ((F.joint zX t hti).comp (t,p) hmap).fst
  have hY : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => (F.flow q.2.2 q.2.1).1)
      _ (t,p) := ((F.joint p.2 p.1 hp.1.1).comp (t,p) hparam).fst
  have hN := (hasStrictFDerivAt_norm_nonzero (sub_ne_zero.mpr hxy)).comp (t,p) (hX.sub hY)
  have htproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.1)
      (ContinuousLinearMap.fst ℝ ℝ (ℝ × Phase)) (t,p) := hasStrictFDerivAt_fst
  have hsproj : HasStrictFDerivAt (fun q : ℝ × (ℝ × Phase) => q.2.1)
      ((ContinuousLinearMap.fst ℝ ℝ Phase).comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × Phase))) (t,p) :=
    hasStrictFDerivAt_fst.comp (t,p) hparam
  have hH := (htproj.sub hsproj).sub hN
  have hroot : ∃ L : (ℝ × (ℝ × Phase)) →L[ℝ] ℝ,
      HasStrictFDerivAt H L (t,p) ∧ L (1,0) =
        1-dot (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
          ((F.flow zX t).1-(F.flow p.2 p.1).1)) (velocity (F.flow zX t).2) := by
    refine ⟨_,hH,?_⟩
    change 1 - (0 : ℝ) - inner ℝ
      (‖(F.flow zX t).1-(F.flow p.2 p.1).1‖⁻¹ •
        ((F.flow zX t).1-(F.flow p.2 p.1).1))
      (((1 : ℝ) • lorentzField E B (t,F.flow zX t) + F.differential zX t 0).1 -
        (((0 : ℝ) • lorentzField E B (p.1,F.flow p.2 p.1) + F.differential p.2 p.1 0).1)) = _
    simp only [map_zero,one_smul,zero_smul,add_zero,Prod.fst_zero,sub_zero,← dot_eq_inner]
    rfl
  obtain ⟨L,hL,hk⟩ := hroot
  have hkne : L (1,0) ≠ 0 := by
    rw [hk]
    exact ne_of_gt (cone_deficit_positive hxy (F.flow zX t).2)
  obtain ⟨τ,hτ,hτc,hev⟩ := exists_continuous_scalar_root hL
    (by dsimp [H]; linarith) hkne
  have hle : ∀ᶠ q in 𝓝 p, q.1 < τ q ∧ τ q < T := by
    have hpos : 0 < τ p-p.1 := by rw [hτ]; exact sub_pos.mpr ht.1
    have h1 : ∀ᶠ q in 𝓝 p, 0 < τ q-q.1 :=
      (hτc.sub continuousAt_fst).eventually (isOpen_Ioi.mem_nhds hpos)
    have hend : τ p < T := by rw [hτ]; exact ht.2
    have h2 := hτc.eventually (isOpen_Iio.mem_nhds hend)
    filter_upwards [h1,h2] with q hq hqT
    exact ⟨sub_pos.mp hq,hqT⟩
  apply hτc.congr_of_eventuallyEq
  filter_upwards [hev,hle,(F.isOpen_jointBranchDomain zX).mem_nhds hp] with q hq hqt hqd
  exact (F.branch_unique zX q.2 hqd.1 ⟨hqt.1.le,hqt.2.le⟩ (by change H (τ q,q)=0 at hq; dsimp [H] at hq; linarith)).symm

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_LabelOccupationDurationMass
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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.position_lipschitz {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) :
    LipschitzOnWith 1 (fun t => (F.flow z t).1) (Icc 0 T) := by
  apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (fun t ht => (F.ode z t ht).fst)
  intro t _
  exact_mod_cast (norm_velocity_lt_one (F.flow z t).2).le

lemma PhaseFlowOn.continuousOn_joint {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T)
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec)))
    (hB : ContinuousOn B (Icc 0 T ×ˢ (univ : Set Vec))) :
    ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  intro p hp
  obtain ⟨M,hM⟩ := (isCompact_Icc.prod (isCompact_closedBall p.2.1 (T+1))).bddAbove_image
    ((hE.norm.add hB.norm).mono (prod_mono Subset.rfl (subset_univ _)))
  let L : ℝ≥0 := ⟨max 1 M, zero_le_one.trans (le_max_left _ _)⟩
  have hpos (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) (t : ℝ) (ht : t ∈ Icc 0 T) :
      (F.flow z t).1 ∈ closedBall p.2.1 (T+1) := by
    have hh := (F.position_lipschitz z).dist_le_mul t ht 0 ⟨le_rfl,hT⟩
    simp only [F.initial,NNReal.coe_one,one_mul,Real.dist_eq,sub_zero,abs_of_nonneg ht.1] at hh
    have hz' : dist z.1 p.2.1 < (1/2:ℝ) := (le_max_left _ _).trans_lt hz
    exact (dist_triangle _ z.1 _).trans (add_le_add hh hz'.le) |>.trans (by linarith [ht.2])
  have hLip (z : Phase) (hz : z ∈ ball p.2 (1/2:ℝ)) :
      LipschitzOnWith L (F.flow z) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (F.ode z)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖lorentzField E B (t,F.flow z t)‖ ≤ max 1 M
    rw [lorentzField,lorentzPhase,Prod.norm_def]
    apply max_le
    · exact (norm_velocity_lt_one _).le.trans (le_max_left _ _)
    · calc
        _ ≤ ‖E (t,(F.flow z t).1)‖+‖B (t,(F.flow z t).1)‖ := by
          exact (norm_add_le _ _).trans (add_le_add le_rfl
            ((norm_cross_le _ _).trans
              (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one _).le)))
        _ ≤ M := hM ⟨(t,(F.flow z t).1),⟨ht,hpos z hz t ht⟩,rfl⟩
        _ ≤ _ := le_max_right _ _
  have hc : ContinuousAt (fun z => F.flow z p.1) p.2 := (F.label p.2 p.1 hp.1).continuousAt
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ,hδ,hlabel⟩ := Metric.continuousAt_iff.mp hc (ε/2) (by positivity)
  refine ⟨min (1/2:ℝ) (min δ (ε/(2*((L:ℝ)+1)))),by positivity,?_⟩
  intro q hq hdist
  have hd₁ : dist q.1 p.1 < ε/(2*((L:ℝ)+1)) :=
    (le_max_left _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  have hd₂ : dist q.2 p.2 < δ :=
    (le_max_right _ _).trans_lt (hdist.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  have hqball : q.2 ∈ ball p.2 (1/2:ℝ) :=
    (le_max_right _ _).trans_lt (hdist.trans_le (min_le_left _ _))
  have hh : (L:ℝ)*dist q.1 p.1 < ε/2 := by
    have hh := (lt_div_iff₀ (show 0<2*((L:ℝ)+1) by positivity)).mp hd₁
    nlinarith [dist_nonneg (x := q.1) (y := p.1)]
  exact (dist_triangle _ (F.flow q.2 p.1) _).trans_lt
    (add_lt_add_of_le_of_lt ((hLip q.2 hqball).dist_le_mul q.1 hq.1 p.1 hp.1)
      (hlabel hd₂) |>.trans_le (by linarith))

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

lemma PhaseFlowOn.continuous_prefixFlow {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) :
    Continuous (fun p : ℝ × Phase => prefixFlow F.flow T p.2 p.1) := by
  apply (F.continuousOn_joint hT hs.E_smooth.continuousOn hs.B_smooth.continuousOn).comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
  intro p
  exact ⟨prefixClamp_mem hT p.1,mem_univ _⟩

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


lemma dot_zero_right_rvm (a : Vec) : dot a 0=0 := by simp [dot]

lemma hasDerivAt_norm_nonzero {Y : ℝ → Vec} {u : Vec} {s : ℝ}
    (hY : HasDerivAt Y u s) (h0 : Y s≠0) :
    HasDerivAt (fun t => ‖Y t‖) (dot (Y s) u / ‖Y s‖) s := by
  have hn := (hY.differentiableAt.norm ℝ h0).hasDerivAt
  have he := (hn.pow 2).unique hY.norm_sq
  simp only [Nat.cast_ofNat,Nat.reduceSub,pow_one,← dot_eq_inner] at he
  have hr : ‖Y s‖≠0 := norm_ne_zero_iff.mpr h0
  have he' : deriv (fun t => ‖Y t‖) s = dot (Y s) u / ‖Y s‖ := by
    apply (eq_div_iff hr).mpr
    linarith
  rwa [he'] at hn

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

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


lemma hasDerivAt_momentumDirection {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) :
    HasDerivAt (momentumDirection ∘ V)
      (‖V t‖⁻¹ • transverseProjection (V t) K) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hh := (hn.inv (norm_ne_zero_iff.mpr hv)).smul hV
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply,transverseProjection,velocityProjection,dot_smul_left,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp
  ring

lemma hasDerivAt_angularMultiplier {V : ℝ → Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t ≠ 0) (w : ℝ) (h : Vec) :
    HasDerivAt (fun r => angularMultiplier w (V r) h)
      ((-w/‖V t‖^2) •
        (dot (momentumDirection (V t)) K • transverseProjection (V t) h +
         dot (momentumDirection (V t)) h • transverseProjection (V t) K +
         dot (transverseProjection (V t) K) h • momentumDirection (V t))) t := by
  have hn := hasDerivAt_norm_nonzero hV hv
  have hξ := hasDerivAt_momentumDirection hV hv
  have hP := (hasDerivAt_const t h).sub
    ((hasDerivAt_dot hξ (hasDerivAt_const t h)).smul hξ)
  have hh := ((hasDerivAt_const t w).div hn (norm_ne_zero_iff.mpr hv)).smul hP
  convert hh using 1 <;> try rfl
  ext i
  simp only [Pi.div_apply,Pi.sub_apply,Pi.smul_apply',momentumDirection,transverseProjection,velocityProjection,dot_smul_left,
      dot_sub_left,dot_zero_right_rvm,Function.comp_apply,zero_add,zero_sub,
      PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.neg_apply,smul_eq_mul,
      zero_mul]
  field_simp
  ring

lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]

lemma contDiffAt_transverseCLM {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k transverseCLM v := by
  have hξ : ContDiffAt ℝ k momentumDirection v :=
    ((contDiffAt_id.norm ℝ hv).inv (norm_ne_zero_iff.mpr hv)).smul contDiffAt_id
  exact contDiffAt_const.sub (((InnerProductSpace.toDual ℝ Vec).contDiff.of_le hk).contDiffAt.comp v hξ |>.smulRight hξ)

lemma contDiffAt_angularMultiplierCLM (w : ℝ) {v : Vec} (hv : v≠0) {k : ℕ∞ω}
    (hk : k≤((⊤ : ℕ∞) : ℕ∞ω)) : ContDiffAt ℝ k (angularMultiplierCLM w) v := by
  exact (contDiffAt_const.div (contDiffAt_id.norm ℝ hv) (norm_ne_zero_iff.mpr hv)).smul
    (contDiffAt_transverseCLM hv hk)

lemma angularDerivativeCLM_apply (w : ℝ) (v K h : Vec) :
    angularDerivativeCLM w v K h = (-w/‖v‖^2) •
      (dot (momentumDirection v) K • transverseProjection v h +
       dot (momentumDirection v) h • transverseProjection v K +
       dot (transverseProjection v K) h • momentumDirection v) := by
  simp only [angularDerivativeCLM,smul_apply,add_apply,
    transverseCLM_apply,ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]

lemma hasDerivAt_angularMultiplierCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (hv : V t≠0) (w : ℝ) :
    HasDerivAt (fun r=>angularMultiplierCLM w (V r)) (angularDerivativeCLM w (V t) K) t := by
  have hd := ((contDiffAt_angularMultiplierCLM w hv (k:=1) (by simp)).differentiableAt one_ne_zero).comp t hV.differentiableAt
  have he : deriv (fun r=>angularMultiplierCLM w (V r)) t=angularDerivativeCLM w (V t) K := by
    apply ContinuousLinearMap.ext
    intro h
    have hh := hd.hasDerivAt.clm_apply (hasDerivAt_const t h)
    simp only [ContinuousLinearMap.map_zero,add_zero,Function.comp_apply,angularMultiplierCLM_apply] at hh
    exact hh.unique (by simpa only [angularDerivativeCLM_apply] using hasDerivAt_angularMultiplier hV hv w h)
  rw [←he]
  exact hd.hasDerivAt



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_AngularBump
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma extendedAngularCLM_contDiff (w : ℝ) (hw : 0<w) :
    ContDiff ℝ ∞ (extendedAngularCLM w hw) := by
  rw [contDiff_iff_contDiffAt]
  intro v
  by_cases hv : v=0
  · subst v
    apply (contDiffAt_const (c:=(0:Vec→L[ℝ]Vec))).congr_of_eventuallyEq
    have he := (angularZeroBump w hw).eventuallyEq_one_of_mem_ball
      (show (0:Vec)∈ball 0 (angularZeroBump w hw).rIn by simpa only [mem_ball,dist_self,angularZeroBump] using div_pos hw (by norm_num : (0:ℝ)<64))
    filter_upwards [he] with v hv
    change (1-angularZeroBump w hw v) • angularMultiplierCLM w v=0
    simp only [hv,Pi.one_apply,sub_self]
    exact zero_smul ℝ (angularMultiplierCLM w v)
  · exact ((contDiffAt_const.sub (angularZeroBump w hw).contDiff.contDiffAt).smul
      (contDiffAt_angularMultiplierCLM w hv le_rfl))

lemma extendedAngularCLM_eq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32≤‖v‖) :
    extendedAngularCLM w hw v=angularMultiplierCLM w v := by
  have hz := (angularZeroBump w hw).zero_of_le_dist (by simpa only [dist_zero_right,angularZeroBump] using hv)
  simp only [extendedAngularCLM,hz,sub_zero,one_smul]

lemma extendedAngularCLM_eventuallyEq (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) :
    extendedAngularCLM w hw =ᶠ[𝓝 v] angularMultiplierCLM w := by
  have he : ∀ᶠ z : Vec in 𝓝 v,w/32<‖z‖ := continuous_norm.continuousAt.eventually (lt_mem_nhds hv)
  filter_upwards [he] with z hz
  exact extendedAngularCLM_eq w hw hz.le

lemma hasDerivAt_extendedAngularCLM {V : ℝ→Vec} {K : Vec} {t : ℝ}
    (hV : HasDerivAt V K t) (w : ℝ) (hw : 0<w) :
    HasDerivAt (fun r=>extendedAngularCLM w hw (V r))
      (fderiv ℝ (extendedAngularCLM w hw) (V t) K) t :=
  ((extendedAngularCLM_contDiff w hw).differentiable (by simp)).differentiableAt.hasFDerivAt.comp_hasDerivAt t hV

lemma extendedAngularCLM_fderiv (w : ℝ) (hw : 0<w) {v : Vec} (hv : w/32<‖v‖) (K : Vec) :
    fderiv ℝ (extendedAngularCLM w hw) v K=angularDerivativeCLM w v K := by
  have hv0 : v≠0 := norm_pos_iff.mp ((div_pos hw (by norm_num : (0:ℝ)<32)).trans hv)
  have hcurve : HasDerivAt (fun r : ℝ=>v+r • K) K 0 := by
    convert (hasDerivAt_const (0:ℝ) v).add ((hasDerivAt_id (0:ℝ)).smul_const K) using 1 <;> first | rfl | simp only [one_smul,zero_add]
  have ht : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 v) := by
    have hc : Tendsto (fun r : ℝ=>v+r • K) (𝓝 0) (𝓝 (v+(0:ℝ) • K)) := hcurve.continuousAt
    simpa only [zero_smul,add_zero] using hc
  have he := (extendedAngularCLM_eventuallyEq w hw hv).comp_tendsto ht
  have ha := (hasDerivAt_angularMultiplierCLM hcurve (by simpa using hv0) w).congr_of_eventuallyEq he
  have hb := hasDerivAt_extendedAngularCLM hcurve w hw
  simpa only [zero_smul,add_zero] using hb.unique ha

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixMomentumForce
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.continuous_prefixMomentumForce {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (z : Phase) :
    Continuous (prefixMomentumForce s F.flow T z) := by
  have hα : Continuous (prefixFlow F.flow T z) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have ht : Continuous (prefixClamp T) := continuous_const.max (continuous_const.min continuous_id)
  have hZ := ht.prodMk hα.fst
  have hE := hs.E_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  have hB := hs.B_smooth.continuousOn.comp_continuous hZ (fun t=>⟨prefixClamp_mem hT t,mem_univ _⟩)
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp (((contDiff_velocity (k:=1)).continuous.comp hα.snd).prodMk hB))

lemma PhaseFlowOn.prefixMomentum_hasDerivAt {E B : Field} {T t : ℝ}
    (F : PhaseFlowOn E B T) (z : Phase) (ht : t∈Ioo 0 T) :
    HasDerivAt (fun r=>(prefixFlow F.flow T z r).2)
      (lorentzField E B (t,F.flow z t)).2 t := by
  have hd : HasDerivAt (fun r=>(F.flow z r).2) (lorentzField E B (t,F.flow z t)).2 t :=
    ((F.ode z t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).snd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds ht.1 ht.2] with r hr
  simp only [prefixFlow,prefixClamp_eq hr]

lemma PhaseFlowOn.prefixAngular_regular {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (hw : 0<w) (z : Phase) :
    Continuous (prefixAngularMultiplier s F.flow T w hw z) ∧
    Continuous (prefixAngularRate s F.flow T w hw z) ∧
    ∀t∈Ioo 0 T,HasDerivAt (prefixAngularMultiplier s F.flow T w hw z)
      (prefixAngularRate s F.flow T w hw z t) t := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T z t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hd := extendedAngularCLM_contDiff w hw
  refine ⟨hd.continuous.comp hV,(hd.continuous_fderiv (by simp)).comp hV |>.clm_apply
    (F.continuous_prefixMomentumForce hs hT z),?_⟩
  intro t ht
  change HasDerivAt (fun r=>extendedAngularCLM w hw (prefixFlow F.flow T z r).2)
    (fderiv ℝ (extendedAngularCLM w hw) (prefixFlow F.flow T z t).2
      (prefixMomentumForce s F.flow T z t)) t
  have he : prefixMomentumForce s F.flow T z t=(lorentzField s.E s.B (t,F.flow z t)).2 := by
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht)]
  rw [he]
  exact hasDerivAt_extendedAngularCLM (F.prefixMomentum_hasDerivAt z ht) w hw

lemma prefixAngular_highband {s : Solution} {α : Phase→ℝ→Phase} {T t w : ℝ}
    (hw : 0<w) (z : Phase) (ht : t∈Icc 0 T) (hv : w/16≤‖(α z t).2‖) :
    prefixAngularMultiplier s α T w hw z t=angularMultiplierCLM w (α z t).2 ∧
    prefixAngularRate s α T w hw z t=angularDerivativeCLM w (α z t).2
      (lorentzField s.E s.B (t,α z t)).2 := by
  have hnorm : w/32<‖(α z t).2‖ := by linarith
  simp only [prefixAngularMultiplier,prefixAngularRate,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  exact ⟨extendedAngularCLM_eq w hw hnorm.le,extendedAngularCLM_fderiv w hw hnorm _⟩

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ActualLabelCutoffCost
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

lemma PhaseFlowOn.labelReceiverTime_measurable {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) : Measurable (labelReceiverTime F.flow zX T) := by
  classical
  apply ContinuousOn.measurable_piecewise _ continuousOn_const (F.isOpen_jointBranchDomain zX).measurableSet
  intro p hp
  exact (F.joint_branch_continuousAt zX hp).continuousWithinAt

lemma PhaseFlowOn.labelReceiverTime_mem {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (hT : 0≤T) (zX : Phase) (p : ℝ×Phase) :
    labelReceiverTime F.flow zX T p∈Icc 0 T := by
  classical
  by_cases hp : p∈labelBranchDomain F.flow zX T
  · rw [labelReceiverTime,indicator_of_mem hp]
    have ht := F.branch_time_mem zX p.2 hp.1 hp.2
    exact ⟨(hp.1.1.1.trans ht.1).le,ht.2.le⟩
  · simp only [labelReceiverTime,indicator_of_notMem hp,mem_Icc,le_refl,hT,and_self]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ClippedRamp
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

lemma clippedRamp_lipschitz (a ℓ : ℝ) : LipschitzWith ‖ℓ⁻¹‖₊ (clippedRamp a ℓ) := by
  have h : LipschitzWith ‖ℓ⁻¹‖₊ (fun t : ℝ=>(t-a)/ℓ) := by
    apply lipschitzWith_iff_dist_le_mul.mpr
    intro x y
    simp only [Real.dist_eq,coe_nnnorm,Real.norm_eq_abs]
    rw [←sub_div,sub_sub_sub_cancel_right,abs_div]
    simp only [div_eq_mul_inv,abs_inv]
    exact le_of_eq (mul_comm _ _)
  exact (h.const_max 0).const_min 1

lemma clippedRamp_of_le {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t≤a) : clippedRamp a ℓ t=0 := by
  rw [clippedRamp,max_eq_left (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hℓ.le)]
  norm_num

lemma clippedRamp_of_ge {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : a+ℓ≤t) : clippedRamp a ℓ t=1 := by
  have h : 1≤(t-a)/ℓ := (le_div_iff₀ hℓ).mpr (by linarith)
  rw [clippedRamp,min_eq_left (le_trans h (le_max_right _ _))]

lemma clippedRamp_of_between {a ℓ t : ℝ} (hℓ : 0<ℓ) (ht : t∈Icc a (a+ℓ)) :
    clippedRamp a ℓ t=(t-a)/ℓ := by
  have h0 : 0≤(t-a)/ℓ := div_nonneg (sub_nonneg.mpr ht.1) hℓ.le
  have h1 : (t-a)/ℓ≤1 := (div_le_iff₀ hℓ).mpr (by linarith [ht.2])
  rw [clippedRamp,max_eq_right h0,min_eq_right h1]

lemma directionWeight_lipschitz (a b ℓ : ℝ) :
    LipschitzWith (‖ℓ⁻¹‖₊+‖ℓ⁻¹‖₊) (directionWeight a b ℓ) :=
  (clippedRamp_lipschitz a ℓ).sub (clippedRamp_lipschitz (b-ℓ) ℓ)

lemma directionWeight_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc a (a+ℓ)) : directionWeight a b ℓ t=(t-a)/ℓ := by
  rw [directionWeight,clippedRamp_of_between hℓ ht,clippedRamp_of_le hℓ (by linarith [ht.2]),sub_zero]

lemma directionWeight_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Icc (b-ℓ) b) : directionWeight a b ℓ t=(b-t)/ℓ := by
  rw [directionWeight,clippedRamp_of_ge hℓ (by linarith [ht.1]),
    clippedRamp_of_between hℓ (by simpa only [sub_add_cancel] using ht)]
  field_simp
  ring

lemma directionWeight_endpoints {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    directionWeight a b ℓ a=0 ∧ directionWeight a b ℓ b=0 := by
  constructor
  · rw [directionWeight_left hℓ hab ⟨le_rfl,by linarith⟩,sub_self,zero_div]
  · rw [directionWeight_right hℓ hab ⟨by linarith,le_rfl⟩,sub_self,zero_div]

lemma directionWeight_bounds {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    0≤directionWeight a b ℓ t ∧ directionWeight a b ℓ t≤1 := by
  have hmon : clippedRamp (b-ℓ) ℓ t ≤ clippedRamp a ℓ t := by
    apply min_le_min le_rfl
    apply max_le_max le_rfl
    exact div_le_div_of_nonneg_right (by linarith) hℓ.le
  have h0 (c : ℝ) : 0 ≤ clippedRamp c ℓ t := le_min (by norm_num) (le_max_left _ _)
  have h1 (c : ℝ) : clippedRamp c ℓ t≤1 := min_le_left _ _
  unfold directionWeight
  constructor
  · exact sub_nonneg.mpr hmon
  · linarith [h0 (b-ℓ),h1 a]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedMomentumForce
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal


lemma selected_multiplier_support_congr (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H G' H' : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ))
    (hG' : EqOn G' H' (tsupport ψ)) :
    selectedMultiplierForce s α zX T Q ψ G=selectedMultiplierForce s α zX T Q ψ H ∧
    selectedMultiplierCosts s α zX T Q ψ G G'=selectedMultiplierCosts s α zX T Q ψ H H' := by
  constructor <;> funext p
  · by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
    · simp only [selectedMultiplierForce,hG ht]
    · have hz := image_eq_zero_of_notMem_tsupport ht
      simp only [selectedMultiplierForce,selectedLabelSignedForce,labelWeight,hz,zero_mul,zero_smul,map_zero]
  · by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
    · simp only [selectedMultiplierCosts,hG ht,hG' ht]
    · have hz := image_eq_zero_of_notMem_tsupport ht
      have hdz : deriv ψ (labelReceiverTime α zX T p)=0 := by
        by_contra hn
        exact ht (support_deriv_subset hn)
      simp only [selectedMultiplierCosts,selectedLabelCosts,labelWeight,hz,hdz,zero_mul,zero_smul,map_zero,add_zero]

lemma selected_initial_support_congr (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (f : Phase→ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ)) :
    selectedInitialKernel α zX T f Q ψ G=selectedInitialKernel α zX T f Q ψ H := by
  funext z
  by_cases hz : z∈initialPuncturedCone α zX T
  · simp only [selectedInitialKernel,indicator_of_mem hz]
    by_cases ht : branchTime α zX z T 0∈tsupport ψ
    · rw [hG ht]
    · simp only [image_eq_zero_of_notMem_tsupport ht,mul_zero,zero_mul,zero_smul]
  · simp only [selectedInitialKernel,indicator_of_notMem hz]

lemma directionWeight_tsupport {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    tsupport (directionWeight a b ℓ)⊆Icc a b := by
  apply closure_minimal _ isClosed_Icc
  intro t ht
  by_contra hn
  have he : directionWeight a b ℓ t=0 := by
    rcases not_and_or.mp hn with ht|ht
    all_goals rw [not_le] at ht
    · rw [directionWeight,clippedRamp_of_le hℓ ht.le,clippedRamp_of_le hℓ (by linarith),sub_self]
    · rw [directionWeight,clippedRamp_of_ge hℓ (by linarith),clippedRamp_of_ge hℓ (by linarith),sub_self]
  exact ht he



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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedReceiverWeightBoundFinite
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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma directionWeight_ne_zero_interior {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : directionWeight a b ℓ t≠0) : t∈Ioo a b := by
  have hc : t∈Icc a b := directionWeight_tsupport hℓ hab (subset_closure ht)
  refine ⟨lt_of_le_of_ne hc.1 ?_,lt_of_le_of_ne hc.2 ?_⟩
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).1
  · intro he
    subst t
    exact ht (directionWeight_endpoints hℓ hab).2

lemma directionWeight_sum_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,directionWeight (a i) (b i) (ℓ i) t≤1 := by
  classical
  by_cases hz : ∀i∈S,directionWeight (a i) (b i) (ℓ i) t=0
  · simp only [Finset.sum_eq_zero hz,zero_le_one]
  · push Not at hz
    obtain ⟨i,hi,hit⟩ := hz
    rw [Finset.sum_eq_single i]
    · exact (directionWeight_bounds (hℓ i hi) (hlen i hi)).2
    · intro j hj hji
      by_contra hn
      exact Set.disjoint_left.mp (hdis hi hj (Ne.symm hji))
        (directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hit)
        (directionWeight_ne_zero_interior (hℓ j hj) (hlen j hj) hn)
    · exact fun hn=>(hn hi).elim

lemma directionWeight_sum_ofReal_le_one {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j)))) (t : ℝ) :
    ∑i∈S,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) t|≤1 := by
  have hn : ∀i∈S,0≤directionWeight (a i) (b i) (ℓ i) t :=
    fun i hi=>(directionWeight_bounds (hℓ i hi) (hlen i hi)).1
  simp_rw [Finset.sum_congr rfl (fun i hi=>congrArg ENNReal.ofReal (abs_of_nonneg (hn i hi)))]
  rw [←ENNReal.ofReal_sum_of_nonneg hn]
  exact (ENNReal.ofReal_le_ofReal (directionWeight_sum_le_one S a b ℓ hℓ hlen hdis t)).trans_eq (by norm_num)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeClosedBinSourceIndices
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

namespace RVM

lemma unselected_multiplier_support_congr (s : Solution) (α : Phase→ℝ→Phase) (zX : Phase)
    (T : ℝ) (Q : Set (Fin 4→ℕ)) (ψ : ℝ→ℝ)
    {G H : ℝ→Vec→L[ℝ]Vec} (hG : EqOn G H (tsupport ψ)) :
    (fun p=>G (labelReceiverTime α zX T p) (unselectedLabelSignedForce s α zX T Q ψ p))=
      fun p=>H (labelReceiverTime α zX T p) (unselectedLabelSignedForce s α zX T Q ψ p) := by
  funext p
  by_cases ht : labelReceiverTime α zX T p∈tsupport ψ
  · rw [hG ht]
  · have hz := image_eq_zero_of_notMem_tsupport ht
    simp only [unselectedLabelSignedForce,hz,zero_smul,smul_zero,map_zero]

lemma SmoothClassicalPrefix.actual_angular_decomposition {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0 ≤ T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ψ : ℝ→ℝ} {L : NNReal} (hψ : LipschitzWith L ψ)
    (hψb : ∀t∈Icc 0 T,|ψ t| ≤ 1) (hψT : ψ T=0)
    (hS : tsupport ψ⊆Icc 0 T) (hband : ∀t∈tsupport ψ,w/16 ≤ ‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    let G' := fun t=>angularDerivativeCLM w (F.flow zX t).2
      (lorentzField s.E s.B (t,F.flow zX t)).2
    (∫t in Ioo (0:ℝ) T,ψ t • G t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2)))=
      (4*Real.pi)⁻¹ • ((∫p,G (labelReceiverTime F.flow zX T p)
        (unselectedLabelSignedForce s F.flow zX T Q ψ p))+
        (∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q ψ G z)+
        ∫p,selectedMultiplierCosts s F.flow zX T Q ψ G G' p) := by
  dsimp only
  have henergy : EnergyPrefix s T := by
    refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
      (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
      (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
      hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
    · intro time ht position momentum
      have hh := (hs.equations time ht.1.le ht.2).1 position momentum
      rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
    · intro time ht position
      have he := (hs.equations time ht.1.le ht.2).2.1 position
      have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
      rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
      exact ⟨he,hb⟩
  obtain ⟨hW,hW',hd⟩ := F.prefixAngular_regular henergy hT hw zX
  have he := hs.selected_multiplier_decomposition hT F zX Q hψ hψb hψT hW hW' hd
  have hG : EqOn (prefixAngularMultiplier s F.flow T w hw zX)
      (fun t=>angularMultiplierCLM w (F.flow zX t).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).1
  have hG' : EqOn (prefixAngularRate s F.flow T w hw zX)
      (fun t=>angularDerivativeCLM w (F.flow zX t).2
        (lorentzField s.E s.B (t,F.flow zX t)).2) (tsupport ψ) :=
    fun t ht=>(prefixAngular_highband hw zX (hS ht) (hband t ht)).2
  obtain ⟨_eF,eC⟩ := selected_multiplier_support_congr s F.flow zX T Q ψ hG hG'
  rw [eC,selected_initial_support_congr F.flow zX T (fun z=>s.f (0,z)) Q ψ hG,
    unselected_multiplier_support_congr s F.flow zX T Q ψ hG] at he
  rw [←he]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro t _ht
  dsimp only
  by_cases ht : t∈tsupport ψ
  · rw [hG ht]
  · rw [image_eq_zero_of_notMem_tsupport ht,zero_smul,zero_smul]

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

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectedDirection
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal

namespace RVM

private lemma SmoothClassicalPrefix.selectedDirectionEnergyPrefix
    {datum : Datum} {solution : Solution} {horizon : ℝ}
    (hs : SmoothClassicalPrefix datum solution horizon) : EnergyPrefix solution horizon := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro time ht position momentum
    have hh := (hs.equations time ht.1.le ht.2).1 position momentum
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro time ht position
    have he := (hs.equations time ht.1.le ht.2).2.1 position
    have hb := (hs.equations time ht.1.le ht.2).2.2.1 position
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

lemma sum_lintegral_le_lintegral_sum {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (f : ι → Ω → ℝ≥0∞) :
    (∑i∈S,∫⁻x,f i x ∂μ) ≤ ∫⁻x,∑i∈S,f i x ∂μ := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add le_rfl ih).trans (le_lintegral_add _ _)

lemma directionWeight_family_label_kernel {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
    (τ : Ω→ℝ) (f : Ω→ℝ≥0∞) :
    (∑i∈S,∫⁻p,ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) (τ p)| * f p ∂μ) ≤
      ∫⁻p,{p : Ω | τ p∈J}.indicator f p ∂μ := by
  classical
  apply (sum_lintegral_le_lintegral_sum μ S _).trans
  apply lintegral_mono
  intro p
  dsimp only
  by_cases hp : τ p∈J
  · rw [indicator_of_mem (show p ∈ {p : Ω | τ p∈J} from hp), ←Finset.sum_mul]
    exact (mul_le_mul' (directionWeight_sum_ofReal_le_one S a b ℓ hℓ hlen hdis (τ p))
      le_rfl).trans_eq (one_mul _)
  · rw [indicator_of_notMem (show p ∉ {p : Ω | τ p∈J} from hp)]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro i hi
    have hz : directionWeight (a i) (b i) (ℓ i) (τ p)=0 :=
      image_eq_zero_of_notMem_tsupport (fun ht=>hp (hcell i hi
        (directionWeight_tsupport (hℓ i hi) (hlen i hi) ht)))
    rw [hz,abs_zero,ENNReal.ofReal_zero,zero_mul]

lemma unselected_multiplier_family_bound (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (Q : Set (Fin 4→ℕ)) (W : ℝ→Vec→L[ℝ]Vec)
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hcell : ∀i∈S,Icc (a i) (b i)⊆J) :
    (∑i∈S,ENNReal.ofReal ‖∫p,W (labelReceiverTime α zX T p)
      (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)‖) ≤
      ∫⁻p,{p : ℝ×Phase | labelReceiverTime α zX T p∈J}.indicator
        (fun p=>ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
          ((1-labelSelectedCutoff α zX T Q p) • actualLabelSignedForce s α zX T p)‖) p := by
  apply (Finset.sum_le_sum (fun i (_hi : i∈S) => by
    simpa only [ofReal_norm] using enorm_integral_le_lintegral_enorm
      (fun p=>W (labelReceiverTime α zX T p)
        (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)))).trans
  have he (i : ι) (p : ℝ×Phase) :
      ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
        (unselectedLabelSignedForce s α zX T Q (directionWeight (a i) (b i) (ℓ i)) p)‖ =
      ENNReal.ofReal |directionWeight (a i) (b i) (ℓ i) (labelReceiverTime α zX T p)| *
        ENNReal.ofReal ‖W (labelReceiverTime α zX T p)
          ((1-labelSelectedCutoff α zX T Q p) • actualLabelSignedForce s α zX T p)‖ := by
    rw [unselectedLabelSignedForce,smul_comm,map_smul,norm_smul,Real.norm_eq_abs,
      ENNReal.ofReal_mul (abs_nonneg _)]
  simp_rw [←ofReal_norm,he]
  exact directionWeight_family_label_kernel volume S a b ℓ hℓ hlen hdis J hcell
    (labelReceiverTime α zX T) _

lemma measurable_angularMultiplierCLM (w : ℝ) : Measurable (angularMultiplierCLM w) := by
  apply measurable_of_continuousOn_compl_singleton (0:Vec)
  intro v hv
  exact (contDiffAt_angularMultiplierCLM w (by simpa using hv) (k:=1) (by simp)).continuousAt.continuousWithinAt

lemma PhaseFlowOn.measurable_labelAngularMultiplier {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (w : ℝ) :
    Measurable (fun p : ℝ×Phase=>angularMultiplierCLM w
      (F.flow zX (labelReceiverTime F.flow zX T p)).2) := by
  have hV : Continuous (fun t=>(prefixFlow F.flow T zX t).2) :=
    ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd
  have hm := (measurable_angularMultiplierCLM w).comp
    (hV.measurable.comp (F.labelReceiverTime_measurable zX))
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  simp only [Function.comp_apply,prefixFlow,prefixClamp_eq (F.labelReceiverTime_mem hT zX p)]

lemma SmoothClassicalPrefix.actual_angular_family_bound_oai {d : Datum} {s : Solution} {T w : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) (hw : 0<w)
    (F : PhaseFlowOn s.E s.B T) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {ι : Type*} (S : Finset ι) (a b ℓ : ι→ℝ)
    (hℓ : ∀i∈S,0<ℓ i) (hlen : ∀i∈S,2*ℓ i≤b i-a i)
    (hdis : (S:Set ι).Pairwise (fun i j=>Disjoint (Ioo (a i) (b i)) (Ioo (a j) (b j))))
    (J : Set ℝ) (hJ : J⊆Icc 0 T) (hcell : ∀i∈S,Icc (a i) (b i)⊆J)
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖) :
    let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
    (∑i∈S,ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,directionWeight (a i) (b i) (ℓ i) t • G t
      (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
        boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖) ≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
       ((∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (fun p=>ENNReal.ofReal ‖G (labelReceiverTime F.flow zX T p)
            ((1-labelSelectedCutoff F.flow zX T Q p) • actualLabelSignedForce s F.flow zX T p)‖) p) +
        (∑i∈S,ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z))
          Q (directionWeight (a i) (b i) (ℓ i)) G z‖) +
        (∑i∈S,selectedAngularWeightCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) +
        (∫⁻p,{p : ℝ×Phase | labelReceiverTime F.flow zX T p∈J}.indicator
          (selectedMultiplierBulkDensity s F.flow zX T Q G) p) +
        ∑i∈S,selectedAngularMovingCost s F.flow zX T w Q (directionWeight (a i) (b i) (ℓ i))) := by
  classical
  dsimp only
  let G := fun t=>angularMultiplierCLM w (F.flow zX t).2
  let G' := fun t=>angularDerivativeCLM w (F.flow zX t).2
    (lorentzField s.E s.B (t,F.flow zX t)).2
  let ψ := fun i=>directionWeight (a i) (b i) (ℓ i)
  have hsupport i (hi : i∈S) : tsupport (ψ i)⊆J :=
    (directionWeight_tsupport (hℓ i hi) (hlen i hi)).trans (hcell i hi)
  have hψT i (hi : i∈S) : ψ i T=0 := by
    by_contra hn
    have hin := directionWeight_ne_zero_interior (hℓ i hi) (hlen i hi) hn
    have hab : a i≤b i := by linarith only [hℓ i hi,hlen i hi]
    exact (not_lt_of_ge (hJ (hcell i hi ⟨hab,le_rfl⟩)).2) hin.2
  have hn (x y : Vec) : ENNReal.ofReal ‖x+y‖ ≤ ENNReal.ofReal ‖x‖+ENNReal.ofReal ‖y‖ := by
    rw [←ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (norm_add_le _ _)
  have hpoint i (hi : i∈S) :
      ENNReal.ofReal ‖∫t in Ioo (0:ℝ) T,ψ i t • G t
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))-
          boundaryLorentzForce (datumBoundarySolution d) t (F.flow zX t).1 (velocity (F.flow zX t).2))‖ ≤
      ENNReal.ofReal (4*Real.pi)⁻¹ *
        (ENNReal.ofReal ‖∫p,G (labelReceiverTime F.flow zX T p)
            (unselectedLabelSignedForce s F.flow zX T Q (ψ i) p)‖ +
         ENNReal.ofReal ‖∫z : Phase,selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q (ψ i) G z‖ +
         ENNReal.ofReal ‖∫p,selectedMultiplierCosts s F.flow zX T Q (ψ i) G G' p‖) := by
    rw [hs.actual_angular_decomposition hT hw F zX Q (directionWeight_lipschitz _ _ _)
      (fun t _=>by rw [abs_of_nonneg (directionWeight_bounds (hℓ i hi) (hlen i hi)).1];
                   exact (directionWeight_bounds (hℓ i hi) (hlen i hi)).2)
      (hψT i hi) ((hsupport i hi).trans hJ) (fun t ht=>hband t (hsupport i hi ht))]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (by positivity : 0<(4*Real.pi)⁻¹),
      ENNReal.ofReal_mul (by positivity : 0≤(4*Real.pi)⁻¹)]
    apply mul_le_mul' le_rfl
    exact (hn _ _).trans (add_le_add (hn _ _) le_rfl)
  have hi := Finset.sum_le_sum hpoint
  rw [←Finset.mul_sum] at hi
  simp only [Finset.sum_add_distrib] at hi
  have hu := unselected_multiplier_family_bound s F.flow zX T Q G S a b ℓ hℓ hlen hdis J hcell
  have hc := F.selectedMultiplierCosts_family_bound hs.selectedDirectionEnergyPrefix zX Q
    (W:=G) (W':=G') (F.measurable_labelAngularMultiplier hs.selectedDirectionEnergyPrefix hT zX w)
    S a b ℓ hℓ hlen hdis J hcell
  apply hi.trans
  apply mul_le_mul' le_rfl
  have hh := add_le_add (add_le_add hu (le_refl (∑i∈S,ENNReal.ofReal ‖∫z : Phase,
    selectedInitialKernel F.flow zX T (fun z=>s.f (0,z)) Q (ψ i) G z‖))) hc
  simpa only [selectedAngularWeightCost,selectedAngularMovingCost,
    selectedMultiplierWeightDensity,selectedMultiplierMovingDensity,add_assoc,G,G',ψ] using hh

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound_oai.{u_1} := @OAI.RVM.SmoothClassicalPrefix.actual_angular_family_bound_oai.{u_1}
