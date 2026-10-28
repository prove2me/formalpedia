-- Prove2me | solution 1 for OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:47:30.307393+00:00
-- url     : https://prove2.me/submissions/5b9aea29-1f78-4ef5-af7b-358be38d7e48

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_crude_budget
import Theorems.Thm_OAI_RVM_PhaseFlowOn_small_closed_bin_refined_stable
import Theorems.Thm_OAI_RVM_PhaseFlowOn_stable_jointBudget_entry

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

lemma sum_basis (v : Vec) : ∑ i : Fin 3, v i • basis i = v := by
  ext j
  simp [basis, Pi.single_apply]

lemma clm_sum_basis (L : Vec →L[ℝ] ℝ) (v : Vec) :
    L v = ∑ i : Fin 3, v i * L (basis i) := by
  conv_lhs => rw [← sum_basis v]
  simp only [map_sum, map_smul, smul_eq_mul]

lemma full_directional_derivative {f : Particle} {t : ℝ} {x v u K : Vec}
    (hf : DifferentiableAt ℝ f (t,x,v)) :
    fderiv ℝ f (t,x,v) (1,u,K) =
      deriv (fun t' => f (t',x,v)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,v)) x i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,x,v')) v i) := by
  let L := fderiv ℝ f (t,x,v)
  have hT := hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_id t).prodMk (hasDerivAt_const t (x,v)))
  have hιX : HasFDerivAt (fun y : Vec => (t,y,v))
      ((0 : Vec →L[ℝ] ℝ).prod ((ContinuousLinearMap.id ℝ Vec).prod 0)) x := by
    exact (hasFDerivAt_const t x).prodMk
      ((hasFDerivAt_id x).prodMk (hasFDerivAt_const v x))
  have hιV : HasFDerivAt (fun y : Vec => (t,x,y))
      ((0 : Vec →L[ℝ] ℝ).prod ((0 : Vec →L[ℝ] Vec).prod (ContinuousLinearMap.id ℝ Vec))) v := by
    exact (hasFDerivAt_const t v).prodMk
      ((hasFDerivAt_const x v).prodMk (hasFDerivAt_id v))
  have hX := hf.hasFDerivAt.comp x hιX
  have hV := hf.hasFDerivAt.comp v hιV
  have ht : deriv (fun t' => f (t',x,v)) t = L (1,0,0) := by
    convert hT.deriv using 1
    all_goals try with_reducible_and_instances rfl
    rfl
  have hx : fderiv ℝ (fun y => f (t,y,v)) x u = L (0,u,0) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F u) hX.fderiv
    convert h using 1 <;> rfl
  have hv : fderiv ℝ (fun v' => f (t,x,v')) v K = L (0,0,K) := by
    have h := congrArg (fun F : Vec →L[ℝ] ℝ => F K) hV.fderiv
    convert h using 1 <;> rfl
  change L (1,u,K) = deriv (fun t' => f (t',x,v)) t +
    (∑ i : Fin 3, u i * fderiv ℝ (fun y => f (t,y,v)) x (basis i)) +
    (∑ i : Fin 3, K i * fderiv ℝ (fun v' => f (t,x,v')) v (basis i))
  rw [← clm_sum_basis, ← clm_sum_basis, ht, hx, hv]
  rw [← map_add, ← map_add]
  congr 1
  ext <;> simp

lemma hasDerivAt_particle_along_curve {f : Particle} {X V : ℝ → Vec}
    {t : ℝ} {u K : Vec} (hf : DifferentiableAt ℝ f (t,X t,V t))
    (hX : HasDerivAt X u t) (hV : HasDerivAt V K t) :
    HasDerivAt (fun s => f (s,X s,V s))
      (deriv (fun s => f (s,X t,V t)) t +
      (∑ i : Fin 3, u i * spatialPartial (fun y => f (t,y,V t)) (X t) i) +
      (∑ i : Fin 3, K i * spatialPartial (fun v' => f (t,X t,v')) (V t) i)) t := by
  have h := hf.hasFDerivAt.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hX.prodMk hV))
  rw [full_directional_derivative hf] at h
  exact h

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_CollisionLabels
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

lemma PhaseFlowOn.measurable_joint_flow_zero {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) :
    Measurable ((Ioo 0 T ×ˢ (univ : Set Phase)).indicator
      (fun p : ℝ × Phase => F.flow p.2 p.1)) := by
  classical
  have hc : ContinuousOn (fun p : ℝ × Phase => F.flow p.2 p.1)
      (Ioo 0 T ×ˢ (univ : Set Phase)) :=
    fun p hp => (F.joint p.2 p.1 hp.1).continuousAt.continuousWithinAt
  have hh := hc.measurable_piecewise
    (continuousOn_const (c := (0 : Phase))) (measurableSet_Ioo.prod MeasurableSet.univ)
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  funext p
  by_cases hp : p ∈ Ioo 0 T ×ˢ (univ : Set Phase) <;>
    simp [Set.indicator,Set.piecewise,hp]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_RetardedPhaseDomain
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
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma PhaseFlowOn.transport {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    f (t,F.flow z t) = f (0,z) := by
  rcases ht.1.eq_or_lt with h | h
  · simp only [← h,F.initial]
  have hsub : Icc 0 t ⊆ Icc 0 T := fun _ hs => ⟨hs.1,hs.2.trans ht.2⟩
  have hc : ContinuousOn (fun s => f (s,F.flow z s)) (Icc 0 t) :=
    hf.continuousOn.comp (continuousOn_id.prodMk ((F.continuousOn_time z).mono hsub))
      (fun _ hs => ⟨hsub hs,mem_univ _⟩)
  have hd : ∀ s ∈ Ioo 0 t, HasDerivAt (fun r => f (r,F.flow z r)) (0 : ℝ) s := by
    intro s hs
    have hsT : s ∈ Ioo 0 T := ⟨hs.1,hs.2.trans_le ht.2⟩
    have hdiff : DifferentiableAt ℝ f (s,F.flow z s) :=
      ((hf (s,F.flow z s) ⟨Ioo_subset_Icc_self hsT,mem_univ _⟩).contDiffAt
        (prod_mem_nhds (Icc_mem_nhds hsT.1 hsT.2) univ_mem)).differentiableAt (by simp)
    have hode := (F.ode z s (Ioo_subset_Icc_self hsT)).hasDerivAt (Icc_mem_nhds hsT.1 hsT.2)
    have hh := hasDerivAt_particle_along_curve (X := fun r => (F.flow z r).1)
      (V := fun r => (F.flow z r).2) hdiff hode.fst hode.snd
    simpa only [lorentzField,lorentzPhase,heq s hsT] using hh
  obtain ⟨r,_,he⟩ := exists_hasDerivAt_eq_slope (fun s => f (s,F.flow z s)) (fun _ => 0) h hc hd
  have hnum : f (t,F.flow z t)-f (0,F.flow z 0)=0 :=
    (div_eq_zero_iff.mp he.symm).resolve_right (sub_ne_zero.mpr (ne_of_gt h))
  simpa only [F.initial] using sub_eq_zero.mp hnum

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
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

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

lemma PhaseFlowOn.lintegral_comp {E B : Field} {T t : ℝ} (F : PhaseFlowOn E B T)
    (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    ∫⁻ z, g (F.flow z t) = ∫⁻ z, g z := by
  have hh := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume
    (s := univ) MeasurableSet.univ
    (fun z _ => (F.label z t ht).hasFDerivWithinAt) (F.bijective t ht).1.injOn g
  simpa only [Set.image_univ,(F.bijective t ht).2.range_eq,setLIntegral_univ,
    F.det_one _ _ ht,abs_one,ENNReal.ofReal_one,one_mul] using hh.symm

lemma label_hit_tonelli {f₀ : Phase → ℝ} (hf₀ : Measurable f₀)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ s : ℝ, ∫⁻ z : Phase, H.indicator
      (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) =
      ∫⁻ z : Phase, ENNReal.ofReal (f₀ z) * volume {s : ℝ | (s,z) ∈ H} := by
  have hm : Measurable (H.indicator (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2))) :=
    ((hf₀.comp measurable_snd).ennreal_ofReal).indicator hH
  rw [lintegral_lintegral_swap (f := fun s z => H.indicator
    (fun p : ℝ × Phase => ENNReal.ofReal (f₀ p.2)) (s,z)) hm.aemeasurable]
  apply lintegral_congr
  intro z
  have hs : MeasurableSet {s : ℝ | (s,z) ∈ H} :=
    hH.preimage (measurable_id.prodMk measurable_const)
  calc
    _ = ∫⁻ s : ℝ, ENNReal.ofReal (f₀ z) * {s : ℝ | (s,z) ∈ H}.indicator 1 s := by
      apply lintegral_congr
      intro s
      by_cases h : (s,z) ∈ H <;> simp [Set.indicator,h]
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,lintegral_indicator_one hs]

lemma PhaseFlowOn.transport_weight_lintegral {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (g : Phase → ENNReal) :
    (∫⁻ z, ENNReal.ofReal (f (t,z)) * g z) =
      ∫⁻ z, ENNReal.ofReal (f (0,z)) * g (F.flow z t) := by
  rw [← F.lintegral_comp ht (fun z => ENNReal.ofReal (f (t,z)) * g z)]
  apply lintegral_congr
  intro z
  rw [F.transport hf heq ht]

lemma PhaseFlowOn.measurable_phaseHits {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    MeasurableSet (phaseHits F.flow T H) := by
  let α₀ := (Ioo 0 T ×ˢ (univ : Set Phase)).indicator (fun p : ℝ × Phase => F.flow p.2 p.1)
  have hm : Measurable (fun p : ℝ × Phase => (p.1,α₀ p)) :=
    measurable_fst.prodMk F.measurable_joint_flow_zero
  have he : phaseHits F.flow T H = (Ioo 0 T ×ˢ (univ : Set Phase)) ∩
      (fun p : ℝ × Phase => (p.1,α₀ p)) ⁻¹' H := by
    ext p
    by_cases hp : p.1 ∈ Ioo 0 T
    · simp only [phaseHits,mem_ofPred_eq,hp,true_and,mem_inter_iff,mem_prod,
        mem_univ,and_true,mem_preimage,α₀,Set.indicator_of_mem (show p ∈ Ioo 0 T ×ˢ (univ : Set Phase) from ⟨hp,mem_univ _⟩)]
    · simp only [phaseHits,mem_ofPred_eq,hp,false_and,mem_inter_iff,mem_prod,
        mem_univ,and_true]
  rw [he]
  exact (measurableSet_Ioo.prod MeasurableSet.univ).inter (hH.preimage hm)

lemma PhaseFlowOn.phase_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    (∫⁻ t in Ioo 0 T, ∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  have hf₀ : Measurable (fun z : Phase => f (0,z)) :=
    (hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable
  have hfixed (t : ℝ) (ht : t ∈ Ioo 0 T) :
      (∫⁻ z : Phase, H.indicator (fun p => ENNReal.ofReal (f p)) (t,z)) =
        ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
          (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
    calc
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (t,z)) * H.indicator 1 (t,z) := by
        apply lintegral_congr
        intro z
        by_cases h : (t,z) ∈ H <;> simp [Set.indicator,h]
      _ = ∫⁻ z : Phase, ENNReal.ofReal (f (0,z)) * H.indicator 1 (t,F.flow z t) :=
        F.transport_weight_lintegral hf heq (Ioo_subset_Icc_self ht) _
      _ = _ := by
        apply lintegral_congr
        intro z
        by_cases h : (t,F.flow z t) ∈ H
        · rw [Set.indicator_of_mem h,Set.indicator_of_mem
              (show (t,z) ∈ phaseHits F.flow T H from ⟨ht,h⟩)]
          simp
        · rw [Set.indicator_of_notMem h,Set.indicator_of_notMem
              (show (t,z) ∉ phaseHits F.flow T H from fun hh => h hh.2)]
          simp
  calc
    _ = ∫⁻ t : ℝ, ∫⁻ z : Phase, (phaseHits F.flow T H).indicator
        (fun p : ℝ × Phase => ENNReal.ofReal (f (0,p.2))) (t,z) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t ∈ Ioo 0 T
      · rw [Set.indicator_of_mem ht]
        exact hfixed t ht
      · rw [Set.indicator_of_notMem ht]
        symm
        calc
          _ = ∫⁻ _z : Phase, (0 : ENNReal) := by
            apply lintegral_congr
            intro z
            exact Set.indicator_of_notMem (fun h => ht h.1) _
          _ = _ := lintegral_zero
    _ = _ := label_hit_tonelli hf₀ (F.measurable_phaseHits hH)
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

lemma PhaseFlowOn.cone_occupation_identity {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (hT : 0 ≤ T) (zX : Phase) {f : Particle}
    (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase))) (heq : VlasovOn f E B T)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H)
    (hsub : H ⊆ spaceConeDomain F.flow zX T) :
    coneOccupation F.flow zX T f H =
      labelOccupation (fun z => f (0,z)) (fun z => {t | (t,z) ∈ phaseHits F.flow T H}) := by
  rw [← F.phase_occupation_identity hT hf heq hH]
  unfold coneOccupation
  symm
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  have hfs : Continuous (fun z : Phase => f (s,z)) :=
    hf.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨Ioo_subset_Icc_self hs,mem_univ _⟩)
  have hm : Measurable (fun z : Phase => H.indicator (fun p => ENNReal.ofReal (f p)) (s,z)) := by
    exact hfs.measurable.ennreal_ofReal.indicator
      (hH.preimage (measurable_const.prodMk measurable_id))
  let g : Vec → ENNReal := fun y => ∫⁻ v : Vec,
    H.indicator (fun p => ENNReal.ofReal (f p)) (s,(y,v))
  have hgm : Measurable g := hm.lintegral_prod_right'
  calc
    _ = ∫⁻ y : Vec, g y := lintegral_prod _ hm.aemeasurable
    _ = ∫⁻ y in ball (F.flow zX T).1 (T-s), g y := by
      rw [← lintegral_indicator measurableSet_ball]
      apply lintegral_congr
      intro y
      by_cases hy : y ∈ ball (F.flow zX T).1 (T-s)
      · exact (Set.indicator_of_mem hy g).symm
      · rw [Set.indicator_of_notMem hy]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro v
        have hp : (s,(y,v)) ∉ H := fun hp => hy (hsub hp).2
        exact Set.indicator_of_notMem hp (fun p => ENNReal.ofReal (f p))
    _ = _ := F.receiver_polar_lintegral (Ioo_subset_Icc_self hs) zX hgm

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_BallCutoff
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

lemma continuous_dot : Continuous (fun p : Vec × Vec => dot p.1 p.2) := by
  simp only [dot_eq_inner]
  exact continuous_fst.inner continuous_snd

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
open scoped Topology ContDiff RealInnerProductSpace NNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

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

lemma isClosed_inClosedConeBin {α : Phase → ℝ → Phase}
    (hα : Continuous (fun p : ℝ × Phase => α p.2 p.1)) (zX : Phase) (B : ClosedConeBin) :
    IsClosed {p : ℝ × ℝ × Phase | InClosedConeBin α zX B p.1 p.2.1 p.2.2} := by
  have hX := hα.comp (continuous_fst.prodMk continuous_const :
    Continuous (fun p : ℝ × ℝ × Phase => (p.1,zX)))
  have hY := hα.comp (continuous_snd.fst.prodMk continuous_snd.snd :
    Continuous (fun p : ℝ × ℝ × Phase => (p.2.1,p.2.2)))
  have hR : Continuous (fun p : ℝ × ℝ × Phase => p.1-p.2.1) := continuous_fst.sub continuous_snd.fst
  have hΔ := hX.fst.sub hY.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hY.snd
  have ha := (contDiff_velocity (k:=1)).continuous.comp hX.snd
  have hd := hR.sub (continuous_dot.comp (hΔ.prodMk hu))
  have hD := hR.sub (continuous_dot.comp (hΔ.prodMk ha))
  have he := continuous_const.sub (continuous_dot.comp (ha.prodMk hu)) (f:=fun _ => (1:ℝ))
  have hq := (contDiff_q (k:=1)).continuous.comp hY.snd
  have hw := (contDiff_q (k:=1)).continuous.comp hX.snd
  exact (isClosed_eq hR hΔ.norm).inter
    ((isClosed_Icc.preimage hR).inter ((isClosed_Icc.preimage hq).inter
      ((isClosed_Icc.preimage hw).inter
        (((isClosed_le (hR.mul continuous_const) hd).inter (isClosed_le hd (hR.mul continuous_const))).inter
          (((isClosed_le (hR.mul continuous_const) hD).inter (isClosed_le hD (hR.mul continuous_const))).inter
            (isClosed_Icc.preimage he))))))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BinHits
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma PhaseFlowOn.compact_closedBinHits_joint {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    IsCompact {p : ℝ × Phase | p.1∈closedBinHits F.flow zX B S a b c d p.2} := by
  let K : Set (ℝ × ℝ × Phase) := (Icc a b ×ˢ (Icc c d ×ˢ S)) ∩
    {p | InClosedConeBin (prefixFlow F.flow T) zX B p.1 p.2.1 p.2.2}
  have hK : IsCompact K := (isCompact_Icc.prod (isCompact_Icc.prod hS)).inter_right
    (isClosed_inClosedConeBin (F.continuous_prefixFlow hs hT) zX B)
  convert hK.image continuous_snd using 1
  all_goals try with_reducible_and_instances rfl
  ext p
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    refine ⟨(t,p),⟨⟨ht,hr,hz⟩,?_⟩,rfl⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t p.1 p.2
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin
  · rintro ⟨⟨t,r,z⟩,⟨⟨ht,hr,hz⟩,hbin⟩,rfl⟩
    refine ⟨hz,hr,t,ht,?_⟩
    change InClosedConeBin (prefixFlow F.flow T) zX B t r z at hbin
    simpa only [InClosedConeBin,prefixFlow,prefixClamp_eq (hJ ht),
      prefixClamp_eq (hC hr)] using hbin



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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma occupation_divide_cell {p len r I O E B : ℝ≥0∞}
    (hp : p ≠ 0) (hpfin : p ≠ ⊤) (hl : len ≠ 0) (hlfin : len ≠ ⊤)
    (h : len*p*O ≤ r*(len*E+I*B)) :
    O ≤ r/p*(E+I/len*B) := by
  have hh := mul_le_mul' (le_refl ((len*p)⁻¹)) h
  have hprod : len*p ≠ 0 := mul_ne_zero hl hp
  have hprodfin : len*p ≠ ⊤ := ENNReal.mul_ne_top hlfin hpfin
  rw [← mul_assoc,ENNReal.inv_mul_cancel hprod hprodfin,one_mul] at hh
  calc
    O ≤ (len*p)⁻¹*(r*(len*E+I*B)) := hh
    _ = r/p*(E+I/len*B) := by
      rw [ENNReal.mul_inv (Or.inl hl) (Or.inl hlfin),mul_add,div_eq_mul_inv,div_eq_mul_inv,mul_add]
      have he : len⁻¹*(p⁻¹*(r*(len*E))) = r*p⁻¹*E := by
        calc
          _ = r*p⁻¹*(len⁻¹*len)*E := by ac_rfl
          _ = _ := by rw [ENNReal.inv_mul_cancel hl hlfin,mul_one]
      rw [mul_assoc _ _ (r*(len*E)),he]
      ring



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
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


lemma measurableSet_spaceConeDomain (α : Phase → ℝ → Phase) (zX : Phase) (T : ℝ) :
    MeasurableSet (spaceConeDomain α zX T) := by
  exact (measurable_fst measurableSet_Ioo).inter
    (measurableSet_lt (measurable_snd.fst.sub measurable_const).norm
      (measurable_const.sub measurable_fst))

lemma PhaseFlowOn.measurable_closedBinEulerian {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T) :
    MeasurableSet (closedBinEulerian F.flow zX T B S a b c d) :=
  ((F.compact_closedBinHits_joint hs hT zX B hS hJ hC).image
    (continuous_fst.prodMk (F.continuous_prefixFlow hs hT))).measurableSet.inter
      (measurableSet_spaceConeDomain _ _ _)

lemma PhaseFlowOn.mem_closedBinEulerian_iff {E B : Field} {T a b c d r : ℝ}
    (F : PhaseFlowOn E B T) (zX z : Phase) (C : ClosedConeBin) (S : Set Phase)
    (hC : Icc c d⊆Icc 0 T) :
    (r,F.flow z r)∈closedBinEulerian F.flow zX T C S a b c d ↔
      r∈closedBinHits F.flow zX C S a b c d z ∧
        (r,F.flow z r)∈spaceConeDomain F.flow zX T := by
  constructor
  · rintro ⟨⟨⟨r',z'⟩,hh,he⟩,hd⟩
    have hr : r'=r := congrArg Prod.fst he
    subst r'
    have heq : F.flow z' r=F.flow z r := by
      have h := congrArg Prod.snd he
      simpa only [prefixFlow,prefixClamp_eq (hC hh.2.1)] using h
    have hz : z'=z := (F.bijective r (hC hh.2.1)).1 heq
    subst z'
    exact ⟨hh,hd⟩
  · rintro ⟨hh,hd⟩
    refine ⟨⟨(r,z),hh,?_⟩,hd⟩
    simp only [prefixFlow,prefixClamp_eq (hC hh.2.1)]

lemma PhaseFlowOn.closedBinEulerian_occupation_le {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T) :
    coneOccupation F.flow zX T s.f (closedBinEulerian F.flow zX T B S a b c d) ≤
      labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) := by
  rw [F.cone_occupation_identity hT zX hs.f_smooth hs.vlasov
    (F.measurable_closedBinEulerian hs hT zX B hS hJ hC) inter_subset_right]
  unfold labelOccupation
  apply lintegral_mono
  intro z
  apply mul_le_mul' le_rfl
  apply measure_mono
  intro r hr
  exact ((F.mem_closedBinEulerian_iff zX z B S hC).mp hr.2).1



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
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal


open Set MeasureTheory
open scoped ENNReal


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_PhysicalGeometryCutoffDensity
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_stable_budget {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax) (hrad : B.rmax ≤ len)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L)
    (hI : 0 < I) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (40*B.rmax)/ENNReal.ofReal (p/256)*
        (ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal I/ENNReal.ofReal len*jointEnergyBudget s F.flow zX T 4
            (max 0 (a-B.rmax-len)) (min T (b+len)) I (np,nf)) := by
  have hp0 : 0 < p := by rw [hp]; positivity
  have ho := F.small_closed_bin_refined_stable hs hT zX B hS np nf hp hφeq
    ha hb hlen hM hA hP hL hm hφ hφ1 hconst hstable hqmin hqmax hmq hmw
    hr hrmax hrad hd hDlo hDhi hw HX HZ hI
  have hbnd := occupation_divide_cell
    (p:=ENNReal.ofReal (p/256)) (len:=ENNReal.ofReal len)
    (ENNReal.ofReal_pos.mpr (by positivity)).ne' ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.mpr hlen).ne' ENNReal.ofReal_ne_top ho
  have he := F.closedBinEulerian_occupation_le (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin))
    hs hT zX B hS (Icc_subset_Icc ha hb)
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  refine he.trans ((show labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) from ?_).trans hbnd)
  unfold labelOccupation
  apply lintegral_mono
  intro z
  apply mul_le_mul' le_rfl
  apply measure_mono
  rintro u ⟨hz,hu,t,ht,hbin⟩
  exact ⟨hz,⟨(le_max_left _ _).trans hu.1,hu.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianCrudeBudget
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma PhaseFlowOn.closedEulerian_baseline_budget_oai {s : Solution}
    {T M A P L a b massScale φ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (np nf : ℕ) (hp : p=64*(2:ℝ)^np) (hφeq : φ=(2:ℝ)⁻¹^nf)
    (ha : 0 ≤ a) (hb : b ≤ T) (hlen : 0 < len) (hlenI : len≤I) (hab : b-a≤I)
    (hM : 0 < M) (hA : 0 ≤ A) (hP : 0 < P) (hL : 0 ≤ L)
    (hm : 0 < massScale) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hconst : 128 ≤ C)
    (hstable : 2*len ≤ (C*(P/massScale)*(M/φ+Real.sqrt (A*L/φ)))⁻¹^2)
    (hqmin : p/128 ≤ B.qmin) (hqmax : B.qmax ≤ p/32)
    (hmq : massScale ≤ B.qmin) (hmw : massScale ≤ B.wmin)
    (hr : 0 < B.rmin) (hrmax : 0 ≤ B.rmax)
    (hd : B.dmax ≤ φ^2/32)
    (hDlo : φ^2/2 ≤ B.Dmin) (hDhi : B.Dmax ≤ 8*φ^2) (hw : 4 ≤ φ*B.wmin)
    (HX : IncrementBootstrap (fun t => (F.flow zX t).2) T M A P L)
    (HZ : ∀ z∈S, IncrementBootstrap (fun t => (F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      ENNReal.ofReal (35512320*B.rmax/p*(1+I/len))*
        ENNReal.ofReal (∫ x : Vec,totalEnergy s (0,x)) := by
  have hp0 : 0<p := by rw [hp]; positivity
  have hI : 0<I := hlen.trans_le hlenI
  have hq0 : 0<B.qmin := (div_pos hp0 (by norm_num)).trans_le hqmin
  by_cases hrad : B.rmax≤len
  · have ho := F.closedEulerian_stable_budget hs hT zX B hS np nf hp hφeq
      ha hb hlen hM hA hP hL hm hφ hφ1 hconst hstable hqmin hqmax hmq hmw
      hr hrmax hrad hd hDlo hDhi hw HX HZ hI
    have he := F.stable_jointBudget_entry hs zX hI hab hrad hlenI (np,nf)
    have hbound := ho.trans (mul_le_mul' le_rfl (add_le_add le_rfl
      (mul_le_mul' le_rfl he)))
    have heq : ENNReal.ofReal (40*B.rmax)/ENNReal.ofReal (p/256)*
        (ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x))+
          ENNReal.ofReal I/ENNReal.ofReal len*ENNReal.ofReal (3468*(∫x : Vec,totalEnergy s (0,x))))=
        ENNReal.ofReal ((40*B.rmax)/(p/256)*(1+(I/len)*3468))*
          ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
      rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤3468)]
      rw [ENNReal.ofReal_mul (by positivity : 0≤(40*B.rmax)/(p/256)),
        ENNReal.ofReal_div_of_pos (by positivity : 0<p/256),
        ENNReal.ofReal_add (by norm_num) (by positivity),ENNReal.ofReal_one,
        ENNReal.ofReal_mul (by positivity : 0≤I/len),ENNReal.ofReal_div_of_pos hlen]
      ring
    rw [heq] at hbound
    apply hbound.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have he : (40*B.rmax)/(p/256)*(1+I/len*3468)=
        10240*B.rmax/p*(1+I/len*3468) := by ring
    rw [he]
    have hh : 1+I/len*3468≤3468*(1+I/len) := by linarith
    exact (mul_le_mul_of_nonneg_left hh (by positivity)).trans_eq (by ring)
  · have ho := F.closedEulerian_crude_budget hs hT zX B hS (Icc_subset_Icc ha hb) hab hr.le hq0
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq0]
    apply ENNReal.ofReal_le_ofReal
    have hlenr : len≤B.rmax := (lt_of_not_ge hrad).le
    have hn : 0≤I+B.rmax := by positivity
    calc
      (I+B.rmax)/B.qmin≤(I+B.rmax)/(p/128) :=
        div_le_div_of_nonneg_left hn (by positivity) hqmin
      _ ≤ (B.rmax*(1+I/len))/(p/128) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have hi : I≤B.rmax*(I/len) := by
          have hh := mul_le_mul_of_nonneg_right hlenr (div_nonneg hI.le hlen.le)
          have he : len*(I/len)=I := by field_simp
          rwa [he] at hh
        nlinarith
      _ ≤ 35512320*B.rmax/p*(1+I/len) := by
        have he : (B.rmax*(1+I/len))/(p/128)=128*B.rmax/p*(1+I/len) := by ring
        rw [he]
        gcongr
        norm_num

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget_oai := @OAI.RVM.PhaseFlowOn.closedEulerian_baseline_budget_oai
