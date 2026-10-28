-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_source_relative_budget
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:44:41.587116+00:00
-- url     : https://prove2.me/submissions/2a77fa1f-69d2-413f-8f2c-1c56a94e248c

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_two_budget_bound
import Theorems.Thm_OAI_RVM_PhaseFlowOn_closedEulerian_crude_budget
import Theorems.Thm_OAI_RVM_PhaseFlowOn_relative_closed_bin_cell_crude

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

namespace RVM

namespace EnergyPrefix
variable {s : Solution} {T : ℝ}

lemma particle_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ particleEnergy s (t,x) := by
  apply integral_nonneg
  intro v
  exact mul_nonneg (q_pos v).le (hs.nonnegative t ht (x,v))

lemma total_energy_nonneg (hs : EnergyPrefix s T) {t : ℝ} (ht : t ∈ Icc 0 T) (x : Vec) :
    0 ≤ totalEnergy s (t,x) := by
  dsimp [totalEnergy]
  have hp := particle_energy_nonneg hs ht x
  positivity

end EnergyPrefix

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceCellLast
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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal
open Set

namespace RVM

lemma sourceCellLast_le {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len) :
    (sourceCellLast T len:ℝ)*len ≤ T := by
  exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg hT hlen.le))

lemma sourceCell_mem_prefix {T len : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ≤ sourceCellLast T len) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  have hil : (i:ℝ)*len ≤ T := (mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hlen.le).trans
    (sourceCellLast_le hT hlen)
  have his : (i:ℝ) ≤ (i+1:ℕ) := by exact_mod_cast Nat.le_succ i
  have hull : (i:ℝ)*len ≤ (i+1:ℕ)*len := mul_le_mul_of_nonneg_right his hlen.le
  refine ⟨by dsimp [sourceCellLo]; positivity,le_min hil hull,min_le_left _ _,?_⟩
  have hh : sourceCellHi T len i ≤ (i:ℝ)*len+len := by
    unfold sourceCellHi
    simpa only [Nat.cast_add,Nat.cast_one,add_mul,one_mul] using (min_le_right T ((i+1:ℕ)*len))
  dsimp [sourceCellLo]
  linarith

lemma sourceCell_cover {T len t : ℝ} (hlen : 0 < len) (ht : t ∈ Icc 0 T) :
    ∃ i ≤ sourceCellLast T len, t ∈ Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  let i := ⌊t/len⌋₊
  have hi : i ≤ sourceCellLast T len := Nat.floor_mono ((div_le_div_iff_of_pos_right hlen).mpr ht.2)
  refine ⟨i,hi,?_,le_min ht.2 ?_⟩
  · exact (le_div_iff₀ hlen).mp (Nat.floor_le (div_nonneg ht.1 hlen.le))
  · have hh := Nat.lt_floor_add_one (t/len)
    apply le_of_lt
    have hf := (div_lt_iff₀ hlen).mp hh
    simpa only [Nat.cast_add,Nat.cast_one] using hf

lemma selectedSourceCells_cover {T len a b r : ℝ} (hlen : 0 < len) :
    Icc (max 0 (a-r)) (min T b) ⊆
      ⋃ i ∈ selectedSourceCells T len a b r, Icc (sourceCellLo len i) (sourceCellHi T len i) := by
  intro t ht
  obtain ⟨i,hi,htC⟩ := sourceCell_cover hlen ⟨(le_max_left _ _).trans ht.1,ht.2.trans (min_le_left _ _)⟩
  refine mem_iUnion₂.mpr ⟨i,?_,htC⟩
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
    htC.1.trans (ht.2.trans (min_le_right _ _)),
    (le_max_right _ _).trans (ht.1.trans htC.2)⟩

lemma selectedSourceCells_subset_prefix {T len a b r : ℝ} (hT : 0 ≤ T) (hlen : 0 < len)
    {i : ℕ} (hi : i ∈ selectedSourceCells T len a b r) :
    0 ≤ sourceCellLo len i ∧ sourceCellLo len i ≤ sourceCellHi T len i ∧
      sourceCellHi T len i ≤ T ∧ sourceCellHi T len i-sourceCellLo len i ≤ len := by
  classical
  exact sourceCell_mem_prefix hT hlen (by
    have hh := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    omega)

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

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


lemma closedBinHits_clip_receiver (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b c d : ℝ) :
    closedBinHits α zX B S a b c d =
      closedBinHits α zX B S (max a c) (min b (d+B.rmax)) c d := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    exact ⟨hz,hr,t,⟨max_le ht.1 (hr.1.trans hrt),le_min ht.2 (by
      have hh := hbin.2.1.2
      linarith [hr.2])⟩,hbin⟩
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,hr,t,⟨(le_max_left a c).trans ht.1,ht.2.trans (min_le_left _ _)⟩,hbin⟩

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

lemma PhaseFlowOn.measurable_closedBinHits_duration {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : Icc c d ⊆ Icc 0 T) :
    Measurable fun z => volume (closedBinHits F.flow zX B S a b c d z) :=
  measurable_measure_prodMk_right (F.compact_closedBinHits_joint hs hT zX B hS hJ hC).measurableSet

lemma PhaseFlowOn.closedBinHits_occupation_le_sum {s : Solution} {T a b c d : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    {ι : Type*} (N : Finset ι) (l u : ι → ℝ)
    (hJ : Icc a b ⊆ Icc 0 T) (hC : ∀ i∈N, Icc (l i) (u i) ⊆ Icc 0 T)
    (hcover : Icc c d ⊆ ⋃ i∈N, Icc (l i) (u i)) :
    labelOccupation (fun z => s.f (0,z)) (closedBinHits F.flow zX B S a b c d) ≤
      ∑ i∈N, labelOccupation (fun z => s.f (0,z))
        (closedBinHits F.flow zX B S a b (l i) (u i)) := by
  have hfm : Measurable (fun z : Phase => ENNReal.ofReal (s.f (0,z))) :=
    (hs.f_smooth.continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨⟨le_rfl,hT⟩,mem_univ _⟩)).measurable.ennreal_ofReal
  have hsub (z : Phase) : closedBinHits F.flow zX B S a b c d z ⊆
      ⋃ i∈N, closedBinHits F.flow zX B S a b (l i) (u i) z := by
    rintro r ⟨hz,hr,t,ht,hbin⟩
    obtain ⟨i,hi,hrC⟩ := mem_iUnion₂.mp (hcover hr)
    exact mem_iUnion₂.mpr ⟨i,hi,hz,hrC,t,ht,hbin⟩
  unfold labelOccupation
  rw [← lintegral_finsetSum (f := fun i z => ENNReal.ofReal (s.f (0,z)) *
    volume (closedBinHits F.flow zX B S a b (l i) (u i) z)) N (fun i hi => hfm.mul
    (F.measurable_closedBinHits_duration hs hT zX B hS hJ (hC i hi)))]
  apply lintegral_mono
  intro z
  calc
    _ ≤ ENNReal.ofReal (s.f (0,z))*∑ i∈N,
        volume (closedBinHits F.flow zX B S a b (l i) (u i) z) :=
      mul_le_mul' le_rfl ((measure_mono (hsub z)).trans (measure_biUnion_finset_le _ _))
    _ = _ := Finset.mul_sum _ _ _



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


lemma closedBinHits_clip_source (α : Phase → ℝ → Phase) (zX : Phase)
    (B : ClosedConeBin) (S : Set Phase) (a b T : ℝ) :
    closedBinHits α zX B S a b 0 T =
      closedBinHits α zX B S a b (max 0 (a-B.rmax)) (min T b) := by
  funext z
  ext r
  constructor
  · rintro ⟨hz,hr,t,ht,hbin⟩
    have hrt : r ≤ t := by
      have hh := hbin.1
      linarith [norm_nonneg ((α zX t).1-(α z r).1)]
    refine ⟨hz,⟨max_le hr.1 ?_,le_min hr.2 (hrt.trans ht.2)⟩,t,ht,hbin⟩
    linarith [hbin.2.1.2,ht.1]
  · rintro ⟨hz,hr,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RelativeClosedBinHitGeometry
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

lemma selectedSourceCells_card {T len a b r : ℝ} (hlen : 0<len)
    (hab : a≤b) (hr : 0 ≤ r) :
    ((selectedSourceCells T len a b r).card:ℝ)≤2+(b-a+r)/len := by
  classical
  let N := selectedSourceCells T len a b r
  by_cases hN : N.Nonempty
  · let lo := N.min' hN
    let hi := N.max' hN
    have hlo : lo∈N := Finset.min'_mem _ _
    have hhi : hi∈N := Finset.max'_mem _ _
    have hlh : lo≤hi := Finset.min'_le _ _ hhi
    have hsub : N⊆Finset.Icc lo hi := by
      intro i hiN
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le _ _ hiN,Finset.le_max' _ _ hiN⟩
    have hc : N.card≤hi+1-lo := by
      simpa only [Nat.card_Icc] using Finset.card_le_card hsub
    have hc' : (N.card:ℝ)≤(hi:ℝ)+1-(lo:ℝ) := by
      have hh : (N.card:ℝ)≤((hi+1-lo:ℕ):ℝ) := Nat.cast_le.mpr hc
      simpa only [Nat.cast_sub (by omega : lo≤hi+1),Nat.cast_add,Nat.cast_one] using hh
    have hu : (hi:ℝ)*len≤b := (Finset.mem_filter.mp hhi).2.1
    have hl : a-r≤((lo:ℝ)+1)*len := by
      have hh := (Finset.mem_filter.mp hlo).2.2
      exact hh.trans (by simpa only [sourceCellHi,Nat.cast_add,Nat.cast_one] using
        (min_le_right T (((lo+1:ℕ):ℝ)*len)))
    apply (mul_le_mul_iff_left₀ hlen).mp
    have he : (2+(b-a+r)/len)*len=2*len+(b-a+r) := by field_simp
    rw [he]
    nlinarith [mul_le_mul_of_nonneg_right hc' hlen.le]
  · have hz : N=∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    change (N.card:ℝ)≤_
    rw [hz,Finset.card_empty,Nat.cast_zero]
    have : 0≤(b-a+r)/len := div_nonneg (by linarith) hlen.le
    linarith

lemma PhaseFlowOn.relative_closed_bin_stable {s : Solution}
    {T M A P L a b massScale φ σ C p len : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hlen : 0<len)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hrad : B.rmax≤len)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    ENNReal.ofReal (p/256)*labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b 0 T)≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ))*
        ENNReal.ofReal ((2+(b-a+B.rmax)/len)*(∫x : Vec,totalEnergy s (0,x))) := by
  classical
  let l := sourceCellLo len
  let u := sourceCellHi T len
  let w := fun i=>min T (u i+B.rmax)
  let N := selectedSourceCells T len a b B.rmax
  let E := ∫x : Vec,totalEnergy s (0,x)
  let D := 40*B.rmax*(1+φ/σ)
  let O := fun i=>labelOccupation (fun z=>s.f (0,z))
    (closedBinHits F.flow zX B S a b (l i) (u i))
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hD : 0≤D := by dsimp [D]; positivity
  have hgrid (i : ℕ) (hi : i∈N) :
      0≤l i ∧ l i≤u i ∧ u i≤T ∧ u i-l i≤len :=
    selectedSourceCells_subset_prefix hT hlen hi
  have hJC (i : ℕ) : Icc (max a (l i)) (min b (u i+B.rmax))⊆Icc (l i) (w i) := by
    intro t ht
    exact ⟨(le_max_right _ _).trans ht.1,
      le_min ((ht.2.trans (min_le_left _ _)).trans hb) (ht.2.trans (min_le_right _ _))⟩
  have hCC (i : ℕ) (hi : i∈N) : Icc (l i) (u i)⊆Icc (l i) (w i) := by
    intro t ht
    exact ⟨ht.1,le_min (ht.2.trans (hgrid i hi).2.2.1) (by linarith [ht.2])⟩
  have hST (i : ℕ) (hi : i∈N) :
      w i-l i≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 := by
    have hg := (hgrid i hi).2.2.2
    have hw' : w i≤u i+B.rmax := min_le_right _ _
    linarith
  have hsum : labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T)≤
      ∑i∈N,O i := by
    rw [closedBinHits_clip_source]
    apply F.closedBinHits_occupation_le_sum hs hT zX B hS N l u (Icc_subset_Icc ha hb)
    · intro i hi
      exact Icc_subset_Icc (hgrid i hi).1 (hgrid i hi).2.2.1
    · exact selectedSourceCells_cover hlen
  have hpay (i : ℕ) (hi : i∈N) : ENNReal.ofReal (p/256)*O i≤ENNReal.ofReal D*ENNReal.ofReal E := by
    dsimp only [O]
    rw [closedBinHits_clip_receiver]
    exact F.relative_closed_bin_cell_crude hs (l i) (left_mem_Icc.mpr (hgrid i hi).2.1)
      zX B (hgrid i hi).1 (min_le_left _ _) (hJC i) (hCC i hi)
      hM hA hP hL hm hφ hσ hσ1 hconst (hST i hi)
      hqmin hqmax hmq hmw hr hDhi helo hehi hq hw HX HZ
  have hcount : (N.card:ℝ≥0∞)≤ENNReal.ofReal (2+(b-a+B.rmax)/len) := by
    rw [←ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (selectedSourceCells_card hlen hab hrmax)
  calc
    _ ≤ ENNReal.ofReal (p/256)*(∑i∈N,O i) := mul_le_mul' le_rfl hsum
    _ = ∑i∈N,ENNReal.ofReal (p/256)*O i := Finset.mul_sum _ _ _
    _ ≤ ∑i∈N,ENNReal.ofReal D*ENNReal.ofReal E := Finset.sum_le_sum hpay
    _ = (N.card:ℝ≥0∞)*(ENNReal.ofReal D*ENNReal.ofReal E) := by simp
    _ ≤ ENNReal.ofReal (2+(b-a+B.rmax)/len)*(ENNReal.ofReal D*ENNReal.ofReal E) :=
      mul_le_mul' hcount le_rfl
    _ = _ := by
      rw [ENNReal.ofReal_mul (by positivity : 0≤2+(b-a+B.rmax)/len)]
      dsimp only [D,E]
      ac_rfl

lemma PhaseFlowOn.relative_closedEulerian_stable {s : Solution}
    {T M A P L a b massScale φ σ C p len : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hp : 0<p) (hlen : 0<len)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax) (hrad : B.rmax≤len)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (40*B.rmax*(1+φ/σ))/ENNReal.ofReal (p/256)*
        ENNReal.ofReal ((2+(b-a+B.rmax)/len)*(∫x : Vec,totalEnergy s (0,x))) := by
  have ho := F.relative_closed_bin_stable hs hT zX B hS ha hb hab hlen hM hA hP hL
    hm hφ hσ hσ1 hconst hstable hqmin hqmax hmq hmw hr hrmax hrad hDhi helo hehi hq hw HX HZ
  have hbnd := mul_le_mul' (le_refl ((ENNReal.ofReal (p/256))⁻¹)) ho
  rw [←mul_assoc,ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr (by positivity : 0<p/256)).ne'
    ENNReal.ofReal_ne_top,one_mul] at hbnd
  have he := F.closedBinEulerian_occupation_le (c:=max 0 (a-B.rmax)) (d:=min T (b-B.rmin))
    hs hT zX B hS (Icc_subset_Icc ha hb)
    (Icc_subset_Icc (le_max_left _ _) (min_le_left _ _))
  refine he.trans ((show labelOccupation (fun z=>s.f (0,z))
      (closedBinHits F.flow zX B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin))) ≤
      labelOccupation (fun z=>s.f (0,z)) (closedBinHits F.flow zX B S a b 0 T) from ?_).trans ?_)
  · unfold labelOccupation
    apply lintegral_mono
    intro z
    apply mul_le_mul' le_rfl
    apply measure_mono
    rintro u ⟨hz,hu,t,ht,hbin⟩
    exact ⟨hz,⟨(le_max_left _ _).trans hu.1,hu.2.trans (min_le_left _ _)⟩,t,ht,hbin⟩
  · exact hbnd.trans_eq (by simp only [div_eq_mul_inv]; ac_rfl)

lemma PhaseFlowOn.relative_closedEulerian_baseline {s : Solution}
    {T M A P L a b massScale φ σ C p len I : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (B : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (ha : 0≤a) (hb : b≤T) (hab : a≤b) (hp : 0<p) (hlen : 0<len)
    (hlenI : len≤I) (hJI : b-a≤I)
    (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L)
    (hm : 0 < massScale) (hφ : 0<φ) (hσ : 0<σ) (hσ1 : σ≤1) (hconst : 128≤C)
    (hstable : 2*len≤(C*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2)
    (hqmin : p/128≤B.qmin) (hqmax : B.qmax≤p/32)
    (hmq : massScale≤B.qmin) (hmw : massScale≤B.wmin)
    (hr : 0<B.rmin) (hrmax : 0≤B.rmax)
    (hDhi : B.Dmax≤8*φ^2) (helo : σ^2/2≤B.emin) (hehi : B.emax≤8*σ^2)
    (hq : 4≤σ*B.qmin) (hw : 4≤σ*B.wmin)
    (HX : IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L)
    (HZ : ∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) :
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))≤
      ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*
        ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)) := by
  have hI : 0<I := hlen.trans_le hlenI
  have hq0 : 0<B.qmin := (div_pos hp (by norm_num)).trans_le hqmin
  by_cases hrad : B.rmax≤len
  · have ho := F.relative_closedEulerian_stable hs hT zX B hS ha hb hab hp hlen
      hM hA hP hL hm hφ hσ hσ1 hconst hstable hqmin hqmax hmq hmw hr hrmax hrad
      hDhi helo hehi hq hw HX HZ
    have hcount : 0≤2+(b-a+B.rmax)/len := by
      have : 0≤b-a+B.rmax := by linarith
      positivity
    have hfactor : 2+(b-a+B.rmax)/len≤3*(1+I/len) := by
      have hh := (div_le_div_iff_of_pos_right hlen).mpr (show b-a+B.rmax≤I+len by linarith)
      have he : (I+len)/len=I/len+1 := by field_simp
      rw [he] at hh
      nlinarith [div_nonneg hI.le hlen.le]
    rw [ENNReal.ofReal_mul hcount,←mul_assoc,←ENNReal.ofReal_div_of_pos (by positivity : 0<p/256),
      ←ENNReal.ofReal_mul (by positivity : 0≤(40*B.rmax*(1+φ/σ))/(p/256))] at ho
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ (40*B.rmax*(1+φ/σ))/(p/256)*(3*(1+I/len)) :=
        mul_le_mul_of_nonneg_left hfactor (by positivity)
      _ = _ := by ring
  · have ho := F.closedEulerian_crude_budget hs hT zX B hS (Icc_subset_Icc ha hb) hJI hr.le hq0
    apply ho.trans
    apply mul_le_mul' _ le_rfl
    rw [←ENNReal.ofReal_div_of_pos hq0]
    apply ENNReal.ofReal_le_ofReal
    have hlenr : len≤B.rmax := (lt_of_not_ge hrad).le
    have hn : 0≤I+B.rmax := by positivity
    have hj : 1≤1+φ/σ := le_add_of_nonneg_right (div_nonneg hφ.le hσ.le)
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
      _ ≤ 30720*B.rmax/p*(1+φ/σ)*(1+I/len) := by
        have he : (B.rmax*(1+I/len))/(p/128)=128*B.rmax/p*1*(1+I/len) := by ring
        rw [he]
        gcongr
        norm_num

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalDirectTransportDensity
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

lemma Admissible.direct_source_relative_budget_oai {d : Datum} (hd₀ : Admissible d) :
    ∃Cg Cb : ℝ,0 ≤ Cg ∧ 0 ≤ Cb ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (B : ClosedConeBin) (S : Set Phase)
        (M A P L a b massScale φ θ σ Cs p len I : ℝ) (k j : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → 0 < p → 0 < len → len ≤ I → b-a ≤ I →
      0 < M → 0 ≤ A → 0 < P → 0 ≤ L → 0 < massScale →
      0 < φ → 0 < θ → 0 < σ → σ ≤ 1 → 128 ≤ Cs →
      2*len ≤ (Cs*(P/massScale)*(M/σ+Real.sqrt (A*L/σ)))⁻¹^2 →
      p/128 ≤ B.qmin → B.qmax ≤ p/32 → massScale ≤ B.qmin → massScale ≤ B.wmin →
      0 < B.rmin → 0 ≤ B.rmax → 0 < B.Dmin →
      θ^2/2 ≤ B.dmin → B.dmax ≤ 8*θ^2 → φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 →
      σ^2/2 ≤ B.emin → B.emax ≤ 8*σ^2 → 4 ≤ σ*B.qmin → 4 ≤ σ*B.wmin →
      (∀D∈Icc B.Dmin B.Dmax,DyadicWindow k j (Real.sqrt (D/2))) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P L →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P L) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let O := (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal E)/
        ENNReal.ofReal (B.rmin^2*B.Dmin)
      let H := volume (Icc a b)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)
      let Dg := ENNReal.ofReal (128*Cg*p^3*(min θ σ)^2)
      let Db := ENNReal.ofReal (128*Cb*p^3*(min θ σ)^2)
      (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V B z ∂physicalBinMeasure V B (Icc a b))≤
        ENNReal.ofReal (80*φ/((p/128)*θ^2))*
          ((ENNReal.ofReal I*goodFieldBudget s X (fun t=>velocity (V t)) k a b I j)^(1/2:ℝ)*
            (min (Dg^2*H) (Dg*O))^(1/2:ℝ))+
        ENNReal.ofReal (80/(p/128))*
          ((ENNReal.ofReal (2*I)*magneticFieldBudget s F.flow zX T k
            (max 0 (a-B.rmax)) (min T (b-B.rmin)) I j)^(1/2:ℝ)*
            (min (Db^2*H) (Db*O))^(1/2:ℝ)) := by
  obtain ⟨Cg,Cb,hCg,hCb,hforce⟩ := hd₀.direct_source_two_budget_bound
  refine ⟨Cg,Cb,hCg,hCb,?_⟩
  intro s T F hs hT h0 zX B S M A P L a b massScale φ θ σ Cs p len I k j
    hS hS0 ha hb hab hp hlen hlenI hJI hM hA hP hL hm hφ hθ hσ hσ1 hCs hstable
    hqmin hqmax hmq hmw hr hrmax hD hdlo hdhi hDlo hDhi helo hehi hq hw hangle HX HZ
  dsimp only
  have hI : 0<I := hlen.trans_le hlenI
  have hpq : B.qmax≤p := hqmax.trans (by linarith)
  have hforceBound := hforce s T F hs hT h0 zX B S a b I (p/128) p θ φ σ k j
    hS hS0 (Icc_subset_Icc ha hb) hI (by positivity) hp hθ hφ hσ.le hr hD
    hqmin hpq hdlo hdhi hDlo hDhi hehi hangle
  have ho := F.relative_closedEulerian_baseline hs hT zX B hS ha hb hab hp hlen hlenI hJI
    hM hA hP hL hm hφ hσ hσ1 hCs hstable hqmin hqmax hmq hmw hr hrmax
    hDhi helo hehi hq hw HX HZ
  have hod : coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T B S a b (max 0 (a-B.rmax)) (min T (b-B.rmin)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) ≤
      (ENNReal.ofReal (30720*B.rmax/p*(1+φ/σ)*(1+I/len))*ENNReal.ofReal (∫x : Vec,totalEnergy s (0,x)))/
        ENNReal.ofReal (B.rmin^2*B.Dmin) := by
    simpa only [div_eq_mul_inv] using mul_le_mul' ho (le_refl ((ENNReal.ofReal (B.rmin^2*B.Dmin))⁻¹))
  apply hforceBound.trans
  gcongr

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

theorem solution : type_of% @OAI.RVM.Admissible.direct_source_relative_budget_oai := @OAI.RVM.Admissible.direct_source_relative_budget_oai
