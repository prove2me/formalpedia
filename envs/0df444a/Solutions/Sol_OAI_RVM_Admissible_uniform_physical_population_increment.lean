-- Prove2me | solution 1 for OAI.RVM.Admissible.uniform_physical_population_increment
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:32:33.956012+00:00
-- url     : https://prove2.me/submissions/1c8e9a79-bd26-411c-b2df-a0fc1941cfcd

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_force_bulk_uniform

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

open Set MeasureTheory Filter
open scoped Topology ContDiff


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

lemma PhaseFlowOn.flow_inversePhase {E B : Field} {T s : ℝ} (F : PhaseFlowOn E B T)
    (hs : s ∈ Icc 0 T) (z : Phase) : F.flow (inversePhase F.flow (s,z)) s = z :=
  Function.invFun_eq ((F.bijective s hs).2 z)

open Set MeasureTheory Filter
open scoped Topology ContDiff


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

lemma PhaseFlowOn.transport_inverse {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    {f : Particle} (hf : ContDiffOn ℝ 1 f (Icc 0 T ×ˢ (univ : Set Phase)))
    (heq : VlasovOn f E B T) {t : ℝ} (ht : t ∈ Icc 0 T) (z : Phase) :
    f (t,z) = f (0,inversePhase F.flow (t,z)) := by
  have hh := F.transport hf heq ht (inversePhase F.flow (t,z))
  simpa only [F.flow_inversePhase ht] using hh

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SignedRemainder
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
open scoped Topology ContDiff

namespace RVM

lemma intervalIntegral_vec_apply {g : ℝ → Vec} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (i : Fin 3) :
    (∫ t in a..b, g t) i = ∫ t in a..b, g t i := by
  exact ((PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) i).intervalIntegral_comp_comm hg).symm

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PrefixParticle
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
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma continuous_prefixField {E : Field} {T : ℝ}
    (hE : ContinuousOn E (Icc 0 T ×ˢ (univ : Set Vec))) (hT : 0 ≤ T) :
    Continuous (prefixField E T) :=
  hE.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

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

end RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_AbsolutelyContinuousIntervalContinuousDerivative
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
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma absolutelyContinuousOnInterval_of_continuous_derivative
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {g g' : ℝ → V} {a b : ℝ} (hab : a<b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    AbsolutelyContinuousOnInterval g a b := by
  obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hg'
  let M : ℝ≥0 := ⟨max C 0,le_max_right _ _⟩
  have hLip : LipschitzOnWith M g (Ioo a b) := by
    apply Convex.lipschitzOnWith_of_nnnorm_deriv_le
      (fun t ht=>(hd t ht).differentiableAt) _ (convex_Ioo a b)
    intro t ht
    rw [(hd t ht).deriv]
    exact_mod_cast (hC t (Ioo_subset_Icc_self ht)).trans (le_max_left C 0)
  have hc : ContinuousOn g (closure (Ioo a b)) := by simpa only [closure_Ioo hab.ne] using hg
  have hLc := LipschitzOnWith.closure hc hLip
  rw [closure_Ioo hab.ne,← uIcc_of_le hab.le] at hLc
  exact hLc.absolutelyContinuousOnInterval

lemma ac_weighted_vector_ibp_closed {ψ : ℝ → ℝ} {g g' : ℝ → Vec} {a b : ℝ}
    (hab : a≤b) (hψ : AbsolutelyContinuousOnInterval ψ a b)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀ t∈Ioo a b,HasDerivAt g (g' t) t) :
    ∫ t in a..b, ψ t • g' t =
      ψ b • g b - ψ a • g a - ∫ t in a..b, deriv ψ t • g t := by
  rcases hab.eq_or_lt with rfl|hab
  · simp
  have hgu : ContinuousOn g (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg
  have hg'u : ContinuousOn g' (uIcc a b) := by simpa only [uIcc_of_le hab.le] using hg'
  have h₁ : IntervalIntegrable (fun t=>ψ t • g' t) volume a b :=
    (hψ.continuousOn.smul hg'u).intervalIntegrable
  have h₂ : IntervalIntegrable (fun t=>deriv ψ t • g t) volume a b :=
    hψ.intervalIntegrable_deriv.smul_continuousOn hgu
  ext i
  rw [intervalIntegral_vec_apply h₁,PiLp.sub_apply,PiLp.sub_apply,
    PiLp.smul_apply,PiLp.smul_apply,intervalIntegral_vec_apply h₂]
  simp only [PiLp.smul_apply,smul_eq_mul]
  have hdi : ∀ t∈Ioo a b,HasDerivAt (fun r=>g r i) (g' t i) t := fun t ht=>
    (PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hgi : AbsolutelyContinuousOnInterval (fun t=>g t i) a b :=
    absolutelyContinuousOnInterval_of_continuous_derivative hab
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg)
      ((PiLp.proj 2 (𝕜:=ℝ) (fun _:Fin 3=>ℝ) i).continuous.comp_continuousOn hg') hdi
  have he : (∫ t in a..b,ψ t*g' t i)=∫ t in a..b,ψ t*deriv (fun r=>g r i) t := by
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    have hti : t∈Ioo a b := by simpa only [uIoo_of_le hab.le] using ht
    exact congrArg (fun x=>ψ t*x) (hdi t hti).deriv.symm
  rw [he]
  exact hψ.integral_mul_deriv_eq_deriv_mul hgi

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

lemma directionWeight_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (_hab : 2*ℓ≤b-a)
    (ht : t∈Icc (a+ℓ) (b-ℓ)) : directionWeight a b ℓ t=1 := by
  rw [directionWeight,clippedRamp_of_ge hℓ ht.1,clippedRamp_of_le hℓ ht.2,sub_zero]

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

lemma directionWeight_deriv_left {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo a (a+ℓ)) : deriv (directionWeight a b ℓ) t=ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(u-a)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_left hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).sub_const a).div_const ℓ).congr_of_eventuallyEq he
  simpa only [one_div] using hd.deriv

lemma directionWeight_deriv_middle {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (a+ℓ) (b-ℓ)) : deriv (directionWeight a b ℓ) t=0 := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun _=>1) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_middle hℓ hab (Ioo_subset_Icc_self hu)
  exact ((hasDerivAt_const t (1:ℝ)).congr_of_eventuallyEq he).deriv

lemma directionWeight_deriv_right {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∈Ioo (b-ℓ) b) : deriv (directionWeight a b ℓ) t= -ℓ⁻¹ := by
  have he : directionWeight a b ℓ =ᶠ[𝓝 t] (fun u=>(b-u)/ℓ) := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with u hu
    exact directionWeight_right hℓ hab (Ioo_subset_Icc_self hu)
  have hd := (((hasDerivAt_id t).const_sub b).div_const ℓ).congr_of_eventuallyEq he
  simpa only [neg_div,one_div] using hd.deriv

lemma directionWeight_signed_average {a b ℓ : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t) :
    (∫t in a..b,directionWeight a b ℓ t • g' t)=
      ℓ⁻¹ • ((∫t in b-ℓ..b,g t)-(∫t in a..a+ℓ,g t)) := by
  have hab' : a≤b := by linarith
  have hL : a≤a+ℓ := by linarith
  have hC : a+ℓ≤b-ℓ := by linarith
  have hR : b-ℓ≤b := by linarith
  have hψ := (directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b) |>.absolutelyContinuousOnInterval
  have hu : ContinuousOn g (uIcc a b) := by simpa only [uIcc_of_le hab'] using hg
  have hi := hψ.intervalIntegrable_deriv.smul_continuousOn hu
  have hiL : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume a (a+ℓ) :=
    hi.mono_set (by rw [uIcc_of_le hL,uIcc_of_le hab']; exact Icc_subset_Icc le_rfl (hC.trans hR))
  have hiR : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume (b-ℓ) b :=
    hi.mono_set (by rw [uIcc_of_le hR,uIcc_of_le hab']; exact Icc_subset_Icc (hL.trans hC) le_rfl)
  have hiC : IntervalIntegrable (fun t=>deriv (directionWeight a b ℓ) t • g t) volume (a+ℓ) (b-ℓ) :=
    hi.mono_set (by rw [uIcc_of_le hC,uIcc_of_le hab']; exact Icc_subset_Icc hL hR)
  have eL : (∫t in a..a+ℓ,deriv (directionWeight a b ℓ) t • g t)=ℓ⁻¹ • ∫t in a..a+ℓ,g t := by
    rw [←intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_left hℓ hab (by simpa only [uIoo_of_le hL] using ht)]
  have eR : (∫t in b-ℓ..b,deriv (directionWeight a b ℓ) t • g t)= -ℓ⁻¹ • ∫t in b-ℓ..b,g t := by
    rw [←intervalIntegral.integral_smul]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_right hℓ hab (by simpa only [uIoo_of_le hR] using ht)]
  have eC : (∫t in a+ℓ..b-ℓ,deriv (directionWeight a b ℓ) t • g t)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a+ℓ) (b:=b-ℓ)]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_middle hℓ hab (by simpa only [uIoo_of_le hC] using ht),zero_smul]
  rw [ac_weighted_vector_ibp_closed hab' hψ hg hg' hd,
    (directionWeight_endpoints hℓ hab).1,(directionWeight_endpoints hℓ hab).2]
  simp only [zero_smul,sub_self]
  rw [←intervalIntegral.integral_add_adjacent_intervals hiL (hiC.trans hiR),
    ←intervalIntegral.integral_add_adjacent_intervals hiC hiR,eL,eC,eR,zero_add,zero_sub]
  rw [neg_smul,smul_sub]
  abel

lemma interval_average_error {a b ε : ℝ} {g : ℝ→Vec} {v : Vec}
    (hab : a<b) (hg : ContinuousOn g (Icc a b))
    (hb : ∀t∈Icc a b,‖g t-v‖≤ε) :
    ‖(b-a)⁻¹ • (∫t in a..b,g t)-v‖≤ε := by
  have hpos : 0<b-a := sub_pos.mpr hab
  have hi : IntervalIntegrable g volume a b := hg.intervalIntegrable_of_Icc hab.le
  have he : (b-a)⁻¹ • (∫t in a..b,g t)-v =
      (b-a)⁻¹ • (∫t in a..b,g t-v) := by
    rw [intervalIntegral.integral_sub hi intervalIntegrable_const,
      intervalIntegral.integral_const,smul_sub,smul_smul,inv_mul_cancel₀ hpos.ne',one_smul]
  rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos)]
  have hb' : ‖∫t in a..b,g t-v‖≤ε*(b-a) := by
    convert intervalIntegral.norm_integral_le_of_norm_le_const (fun t ht=>hb t ?_) using 1
    · rw [abs_of_pos hpos]
    · rw [uIoc_of_le hab.le] at ht
      exact Ioc_subset_Icc_self ht
  calc
    _ ≤ (b-a)⁻¹*(ε*(b-a)) := mul_le_mul_of_nonneg_left hb' (inv_pos.mpr hpos).le
    _ = ε := by field_simp

lemma directionWeight_signed_error {a b ℓ ε : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤ε)
    (hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤ε) :
    ‖(∫t in a..b,directionWeight a b ℓ t • g' t)-(g b-g a)‖≤2*ε := by
  have hL : ‖ℓ⁻¹ • (∫t in a..a+ℓ,g t)-g a‖≤ε := by
    simpa only [add_sub_cancel_left] using interval_average_error (by linarith : a<a+ℓ)
      (hg.mono (Icc_subset_Icc le_rfl (by linarith))) hleft
  have hR : ‖ℓ⁻¹ • (∫t in b-ℓ..b,g t)-g b‖≤ε := by
    simpa only [sub_sub_cancel] using interval_average_error (by linarith : b-ℓ<b)
      (hg.mono (Icc_subset_Icc (by linarith) le_rfl)) hright
  rw [directionWeight_signed_average hℓ hab hg hg' hd,smul_sub]
  have he : ℓ⁻¹ • (∫t in b-ℓ..b,g t)-ℓ⁻¹ • (∫t in a..a+ℓ,g t)-(g b-g a)=
      (ℓ⁻¹ • (∫t in b-ℓ..b,g t)-g b)-(ℓ⁻¹ • (∫t in a..a+ℓ,g t)-g a) := by abel
  rw [he]
  exact (norm_sub_le _ _).trans (by linarith)

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

lemma directionWeight_deriv_outside {a b ℓ t : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (ht : t∉Icc a b) : deriv (directionWeight a b ℓ) t=0 :=
  deriv_of_notMem_tsupport (fun h=>ht (directionWeight_tsupport hℓ hab h))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionOverlap
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
open Set MeasureTheory
open scoped ENNReal
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma SmoothClassicalPrefix.energyPrefix {d : Datum} {s : Solution} {H : ℝ}
    (hs : SmoothClassicalPrefix d s H) : EnergyPrefix s H := by
  refine ⟨(hs.f_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.E_smooth.of_le (by decide)).mono (fun _ hp => hp.1),
    (hs.B_smooth.of_le (by decide)).mono (fun _ hp => hp.1),hs.nonnegative,
    hs.E_L2,hs.B_L2,hs.compact,?_,?_⟩
  · intro t ht x v
    have hh := (hs.equations t ht.1.le ht.2).1 x v
    rwa [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at hh
  · intro t ht x
    have he := (hs.equations t ht.1.le ht.2).2.1 x
    have hb := (hs.equations t ht.1.le ht.2).2.2.1 x
    rw [derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)] at he hb
    exact ⟨he,hb⟩

end RVM

open Set MeasureTheory
open scoped ENNReal

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
open scoped Topology ContDiff
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_BulkTestWeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma directionWeight_test {a b ℓ η I T : ℝ} (hη : 0<η) (hI : 0<I) (hℓ : η*I≤ℓ)
    (hlen : 2*ℓ≤b-a) (hb : b≤T) :
    (∀t,|directionWeight a b ℓ t|≤1) ∧
    (∀t∉Icc a b,directionWeight a b ℓ t=0) ∧
    (∀t∈Icc a b,|deriv (directionWeight a b ℓ) t|≤(2/η)/I) ∧
    (∀t∉Icc a b,deriv (directionWeight a b ℓ) t=0) ∧
    directionWeight a b ℓ T=0 := by
  have hl : 0<ℓ := (mul_pos hη hI).trans_le hℓ
  refine ⟨fun t=>by rw [abs_of_nonneg (directionWeight_bounds hl hlen).1]; exact (directionWeight_bounds hl hlen).2,
    fun t ht=>image_eq_zero_of_notMem_tsupport (fun hh=>ht (directionWeight_tsupport hl hlen hh)),?_,
    fun t ht=>directionWeight_deriv_outside hl hlen ht,?_⟩
  · intro t ht
    have hd := norm_deriv_le_of_lipschitz (x₀:=t) (directionWeight_lipschitz a b ℓ)
    simp only [Real.norm_eq_abs,NNReal.coe_add,coe_nnnorm,abs_of_pos (inv_pos.mpr hl)] at hd
    calc
      _≤ℓ⁻¹+ℓ⁻¹ := hd
      _=2/ℓ := by ring
      _≤2/(η*I) := div_le_div_of_nonneg_left (by norm_num) (mul_pos hη hI) hℓ
      _=(2/η)/I := by ring
  · by_cases ht : T=b
    · rw [ht]; exact (directionWeight_endpoints hl hlen).2
    · exact image_eq_zero_of_notMem_tsupport (fun hh=>ht (le_antisymm (directionWeight_tsupport hl hlen hh).2 hb))

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_Bootstrap
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma incrementBound_nonneg {M A P L w I : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hI : 0≤I) :
    0≤ incrementBound M A P L w I := by unfold incrementBound; positivity

lemma incrementBound_mono {M A P L w I J : ℝ}
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hIJ : I≤J) :
    incrementBound M A P L w I≤ incrementBound M A P L w J := by
  exact add_le_add (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hIJ) (mul_nonneg hM hP))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIJ hA) (by positivity))

lemma IncrementBootstrap.ramp_error {V K : ℝ→Vec} {T M A P L a b : ℝ} (n : ℕ)
    (H : IncrementBootstrap V T M A P L) (ha : 0≤a) (hab : a<b) (hb : b≤T)
    (hM : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L)
    (hband : ∀t∈Icc a b,(2:ℝ)^n/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^n)
    (hV : ContinuousOn V (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt V (K t) t) :
    ‖(∫t in a..b,directionWeight a b ((b-a)/256) t • K t)-(V b-V a)‖≤
      2*incrementBound M A P L (2^n) ((b-a)/256) := by
  have hl : 0<(b-a)/256 := by linarith
  have hn : 0≤(2:ℝ)^n := by positivity
  apply directionWeight_signed_error hl (by linarith) hV hK hd
  · intro t ht
    have htab : t≤b := by linarith [ht.2]
    exact (H n a t ha ht.1 (htab.trans hb) (fun u hu=>hband u ⟨hu.1,hu.2.trans htab⟩)).trans
      (incrementBound_mono hM hA hP hL hn (by linarith [ht.2]))
  · intro t ht
    have hat : a≤t := by linarith [ht.1]
    rw [norm_sub_rev]
    exact (H n t b (ha.trans hat) ht.2 hb (fun u hu=>hband u ⟨hat.trans hu.1,hu.2⟩)).trans
      (incrementBound_mono hM hA hP hL hn (by linarith [ht.1]))

lemma supported_weight_integral_eq {a b T : ℝ} {ψ : ℝ→ℝ} {K : ℝ→Vec}
    (hab : a≤b) (ha : 0≤a) (hb : b≤T) (hout : ∀t∉Icc a b,ψ t=0) :
    (∫t in Ioo (0:ℝ) T,ψ t • K t)=∫t in a..b,ψ t • K t := by
  rw [restrict_Ioo_eq_restrict_Ioc,←integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hab,←integral_Icc_eq_integral_Ioc]
  apply (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Icc (Icc_subset_Icc ha hb) ?_)
  intro t ht
  rw [hout t ht.2,zero_smul]

lemma closure_coefficient_bound {C M A P L w I : ℝ}
    (_ : 0≤C) (_ : 0≤M) (hA : 0≤A) (hP : 0≤P) (hL : 0≤L) (hw : 0≤w) (hI : 0≤I)
    (hCM : 8*C≤M) (hCA : 16*C*M≤A) (hC2A : 256*C^2≤A) :
    C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*L/w)+
      2*incrementBound M A P L w (I/256) ≤ incrementBound M A P L w I/4 := by
  have hs : Real.sqrt (I/256)=Real.sqrt I/16 := by rw [Real.sqrt_div hI]; norm_num
  have hCs : C*Real.sqrt A≤A/16 := by
    have h1 : 16*C≤Real.sqrt A := by nlinarith [Real.sq_sqrt hA,Real.sqrt_nonneg A]
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg A)
    nlinarith [Real.sq_sqrt hA]
  have h1 : C+M/8≤M/4 := by linarith
  have h2 : C*(M+Real.sqrt A)+A/128≤A/4 := by linarith
  have hp := mul_le_mul_of_nonneg_right h1 (mul_nonneg hP (Real.sqrt_nonneg I))
  have hq := mul_le_mul_of_nonneg_right h2 (show 0≤I*(P^2*L/w) by positivity)
  unfold incrementBound
  rw [hs]
  simp only [div_eq_mul_inv] at hp hq ⊢
  nlinarith only [hp,hq]

lemma PhaseFlowOn.physical_cap_of_labels {d : Datum} {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : SmoothClassicalPrefix d s T)
    (hcap : ∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) :
    ∀t∈Icc 0 T,∀z : Phase,s.f (t,z)≠0→1024*q z.2≤P := by
  intro t ht z hz
  have hf0 : d.f₀ (inversePhase F.flow (t,z))≠0 := by
    rw [←hs.initial_f,←F.transport_inverse hs.energyPrefix.f_smooth hs.energyPrefix.vlasov ht]
    exact hz
  have hh := hcap t ht (inversePhase F.flow (t,z)) (subset_tsupport _ hf0)
  simpa only [F.flow_inversePhase ht] using hh

lemma Admissible.signed_increment_strict {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A : ℝ,32≤M ∧ 1≤A ∧ ∀ᶠ P : ℝ in atTop,
      1≤P → 1≤Real.log (2+P) →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
      (∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
    ∀z∈tsupport d.f₀,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤T →
      (∀t∈Icc a b,(2:ℝ)^n/8≤q (F.flow z t).2 ∧ q (F.flow z t).2≤8*(2:ℝ)^n) →
      ‖(F.flow z b).2-(F.flow z a).2‖≤
        incrementBound M A P (Real.log (2+P)) (2^n) (b-a)/2 := by
  obtain ⟨C,hC,hbulk⟩ := hd.force_bulk_uniform T₀ 512 (by norm_num)
  let M := 32+8*C
  let A := 1+16*C*M+256*C^2
  have hM32 : 32≤M := by dsimp [M]; linarith
  have hM : 0≤M := by linarith
  have hA1 : 1≤A := by dsimp [A]; nlinarith [mul_nonneg hC hM, sq_nonneg C]
  have hA : 0≤A := by linarith
  have hCM : 8*C≤M := by dsimp [M]; linarith
  have hCA : 16*C*M≤A := by dsimp [A]; nlinarith [sq_nonneg C]
  have hC2 : 256*C^2≤A := by dsimp [A]; nlinarith [mul_nonneg hC hM, sq_nonneg C]
  refine ⟨M,A,hM32,hA1,?_⟩
  filter_upwards [hbulk M A (by linarith) hA1] with P hB
  intro hP hL s T F hs hT hTT hcap H z hz n a b ha hab hb hband
  let w : ℝ := 2^n
  let I := b-a
  let V := fun t=>(F.flow z t).2
  let K := prefixMomentumForce s F.flow T z
  have hw : 1≤w := one_le_pow₀ (by norm_num)
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hP0 : 0<P := zero_lt_one.trans_le hP
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hI0 : 0≤I := sub_nonneg.mpr hab
  have hnon : 0≤ incrementBound M A P (Real.log (2+P)) w I :=
    incrementBound_nonneg hM hA hP0.le hL0 hw0.le hI0
  have hqa := hband a ⟨le_rfl,hab⟩
  have hqb := hband b ⟨hab,le_rfl⟩
  have hwp : w≤P := by
    have hc := hcap a ⟨ha,hab.trans hb⟩ z hz
    dsimp [w]
    nlinarith [q_pos (F.flow z a).2]
  by_cases hlarge : 32*w≤ incrementBound M A P (Real.log (2+P)) w I
  · have hn := norm_sub_le (F.flow z b).2 (F.flow z a).2
    have hna := norm_lt_q (F.flow z a).2
    have hnb := norm_lt_q (F.flow z b).2
    change _≤ incrementBound M A P (Real.log (2+P)) w I/2
    dsimp [w] at hlarge
    linarith
  by_cases he : a=b
  · subst b
    simp only [sub_self,norm_zero,incrementBound,Real.sqrt_zero,mul_zero,zero_mul,add_zero,zero_div,le_refl]
  have hab' : a<b := lt_of_le_of_ne hab he
  have hI : 0<I := sub_pos.mpr hab'
  have hIP : I≤(w/P)^2 := by
    have hterm : M*P*Real.sqrt I≤ incrementBound M A P (Real.log (2+P)) w I :=
      le_add_of_nonneg_right (by positivity)
    have hlower : 32*(P*Real.sqrt I)≤M*P*Real.sqrt I := by
      nlinarith only [mul_le_mul_of_nonneg_right hM32 (mul_nonneg hP0.le (Real.sqrt_nonneg I))]
    have hr : Real.sqrt I≤w/P := (le_div_iff₀ hP0).mpr (by linarith [lt_of_not_ge hlarge])
    nlinarith [Real.sq_sqrt hI0,Real.sqrt_nonneg I,div_nonneg hw0.le hP0.le]
  have hI1 : I≤1 := by
    have hr := (div_le_one hP0).mpr hwp
    have hr0 := div_nonneg hw0.le hP0.le
    nlinarith
  have hsrc : ∀z',s.f (0,z')≠0→∀r∈Icc 0 T,q (F.flow z' r).2≤P := by
    intro z' hz' r hr
    have hz0 : d.f₀ z'≠0 := by rwa [←hs.initial_f]
    have hh := hcap r hr z' (subset_tsupport _ hz0)
    nlinarith [q_pos (F.flow z' r).2]
  let ψ := directionWeight a b (I/256)
  obtain ⟨hψ1,hout,hψd,hdout,hψT⟩ := directionWeight_test (a:=a) (b:=b) (ℓ:=I/256)
    (η:=1/256) (I:=I) (T:=T) (by norm_num) hI (by dsimp [I]; ring_nf; exact le_rfl)
    (by dsimp [I]; linarith) hb
  have hd' : ∀t∈Icc a b,|deriv ψ t|≤512/I := by simpa only [show 2/(1/256:ℝ)=512 by norm_num] using hψd
  have hmain := hB hP hL s T F hs hT hTT z a b I w hz ha hb hab hI hI1 le_rfl hw hwp hIP
    hsrc (F.physical_cap_of_labels hs hcap) hband H ψ _ (directionWeight_lipschitz a b (I/256)) hψ1 hout hd' hdout hψT
  have heq : (∫t in Ioo (0:ℝ) T,ψ t •
      (s.E (t,(F.flow z t).1)+cross (velocity (F.flow z t).2) (s.B (t,(F.flow z t).1))))=
      ∫t in a..b,ψ t • K t := by
    rw [←supported_weight_integral_eq hab ha hb hout]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    simp only [ψ,K,prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self ht),lorentzField,lorentzPhase]
  rw [heq] at hmain
  have hm : ‖∫t in a..b,ψ t • K t‖≤C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w) :=
    (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain
  have hdV : ∀t∈Ioo a b,HasDerivAt V (K t) t := by
    intro t ht
    have htT : t∈Ioo 0 T := ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
    have hh : HasDerivWithinAt V (K t) (Icc 0 T) t := by
      change HasDerivWithinAt (fun r=>(F.flow z r).2)
        (prefixMomentumForce s F.flow T z t) (Icc 0 T) t
      rw [prefixMomentumForce,prefixFlow,prefixClamp_eq (Ioo_subset_Icc_self htT)]
      exact (F.ode z t (Ioo_subset_Icc_self htT)).snd
    exact hh.hasDerivAt (Icc_mem_nhds htT.1 htT.2)
  have he := (H z hz).ramp_error n ha hab' hb hM hA hP0.le hL0 hband
    ((F.continuousOn_time z).snd.mono (Icc_subset_Icc ha hb))
    (F.continuous_prefixMomentumForce hs.energyPrefix hT z).continuousOn hdV
  have hn := norm_sub_norm_le (V b-V a) (∫t in a..b,ψ t • K t)
  rw [norm_sub_rev (V b-V a) (∫t in a..b,ψ t • K t)] at hn
  have hc := closure_coefficient_bound hC hM hA hP0.le hL0 hw0.le hI0 hCM hCA hC2
  change _≤ incrementBound M A P (Real.log (2+P)) w I/2
  change ‖(∫t in a..b,ψ t • K t)-(V b-V a)‖≤2*incrementBound M A P (Real.log (2+P)) w (I/256) at he
  change ‖V b-V a‖≤_
  linarith

lemma signed_bootstrap_propagation {α : Type*} {V : α→ℝ→Vec} {K : Set α}
    {T M A P L C : ℝ} (hT : 0≤T) (hM : 0<M) (hA : 0≤A) (hP : 0<P) (hL : 0≤L) (hC : 0≤C)
    (hLip : ∀z∈K,∀a∈Icc 0 T,∀b∈Icc 0 T,‖V z b-V z a‖≤C*|b-a|)
    (hstrict : ∀τ∈Icc 0 T,(∀z∈K,IncrementBootstrap (V z) τ M A P L) →
      ∀z∈K,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤τ →
        (∀t∈Icc a b,(2:ℝ)^n/8≤q (V z t) ∧ q (V z t)≤8*(2:ℝ)^n) →
        ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)/2) :
    ∀z∈K,IncrementBootstrap (V z) T M A P L := by
  let H := fun τ=>∀z∈K,IncrementBootstrap (V z) τ M A P L
  let S := {τ : ℝ | τ∈Icc 0 T ∧ H τ}
  have hzero : (0:ℝ)∈S := by
    refine ⟨⟨le_rfl,hT⟩,?_⟩
    intro z hz n a b ha hab hb hband
    have he : a=b := by linarith
    rw [he]
    simp only [sub_self,norm_zero,Real.sqrt_zero,mul_zero,zero_mul,add_zero,le_refl]
  have hbdd : BddAbove S := ⟨T,fun τ hτ=>hτ.1.2⟩
  let τ := sSup S
  have hτ0 : 0≤τ := le_csSup hbdd hzero
  have hτT : τ≤T := csSup_le ⟨0,hzero⟩ (fun r hr=>hr.1.2)
  have hτ : τ∈Icc 0 T := ⟨hτ0,hτT⟩
  have hbound : H τ := by
    intro z hz n a b ha hab hb hband
    change ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)
    rcases hab.eq_or_lt with he|hab
    · rw [he]; simp [incrementBound]
    apply le_of_forall_pos_le_add
    intro ε hε
    let r := max a (b-ε/(C+1))
    have hden : 0<C+1 := by linarith
    have hrb : r<b := max_lt hab (by linarith [div_pos hε hden])
    have har : a ≤ r := le_max_left _ _
    have hr0 : 0 ≤ r := ha.trans har
    obtain ⟨σ,hσ,hrσ⟩ := exists_lt_of_lt_csSup ⟨0,hzero⟩ (hrb.trans_le hb)
    have hpart := hσ.2 z hz n a r ha har hrσ.le (fun t ht=>hband t ⟨ht.1,ht.2.trans hrb.le⟩)
    change ‖V z r-V z a‖≤ incrementBound M A P L (2^n) (r-a) at hpart
    have hm := incrementBound_mono hM.le hA hP.le hL (show 0≤(2:ℝ)^n by positivity)
      (show r-a≤b-a by linarith)
    have hl := hLip z hz r ⟨hr0,hrb.le.trans (hb.trans hτT)⟩ b ⟨ha.trans hab.le,hb.trans hτT⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hrb.le)] at hl
    have hdiff : b-r≤ε/(C+1) := by have := le_max_right a (b-ε/(C+1)); dsimp [r]; linarith
    have hcost : C*(b-r)≤ε := by
      have hh := mul_le_mul_of_nonneg_left hdiff hC
      have he := (div_mul_cancel₀ ε (ne_of_gt hden))
      nlinarith [div_pos hε hden]
    have hn : ‖V z b-V z a‖≤‖V z b-V z r‖+‖V z r-V z a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    linarith
  have hmem : τ∈S := ⟨hτ,hbound⟩
  by_cases he : τ=T
  · rwa [←he]
  have hτlt : τ<T := lt_of_le_of_ne hτT he
  let ℓ := (M*P/(C+1))^2
  have hden : 0<C+1 := by linarith
  have hMP : 0<M*P := mul_pos hM hP
  have hratio : 0<M*P/(C+1) := div_pos hMP hden
  have hℓ : 0<ℓ := sq_pos_of_pos hratio
  have hsℓ : Real.sqrt ℓ=M*P/(C+1) := Real.sqrt_sq hratio.le
  have hshort : ∀z∈K,∀(n : ℕ) (a b : ℝ),0≤a → a≤b → b≤T → b-a≤ℓ →
      ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a) := by
    intro z hz n a b ha hab hb hlen
    have hl := hLip z hz a ⟨ha,hab.trans hb⟩ b ⟨ha.trans hab,hb⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hl
    have hs : Real.sqrt (b-a)≤M*P/(C+1) := by simpa only [hsℓ] using Real.sqrt_le_sqrt hlen
    have hh := (le_div_iff₀ hden).mp hs
    have hprod := mul_le_mul_of_nonneg_right hh (Real.sqrt_nonneg (b-a))
    have hsq := Real.sq_sqrt (sub_nonneg.mpr hab)
    have hrest : 0≤A*(b-a)*(P^2*L/(2:ℝ)^n) := by positivity
    unfold incrementBound
    nlinarith
  let δ := min ((T-τ)/2) (min (ℓ/2) (M*P*Real.sqrt ℓ/(2*(C+1))))
  have hδ : 0<δ := lt_min (by linarith) (lt_min (by positivity) (by positivity))
  have hδT : δ≤(T-τ)/2 := min_le_left _ _
  have hδℓ : δ≤ℓ/2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδcost : δ≤M*P*Real.sqrt ℓ/(2*(C+1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hnewT : τ+δ≤T := by linarith
  have hnew : H (τ+δ) := by
    intro z hz n a b ha hab hb hband
    change ‖V z b-V z a‖≤ incrementBound M A P L (2^n) (b-a)
    by_cases hlen : b-a≤ℓ
    · exact hshort z hz n a b ha hab (hb.trans hnewT) hlen
    have hat : a<τ := by linarith
    by_cases hbt : b≤τ
    · exact hbound z hz n a b ha hab hbt hband
    have htb : τ≤b := (lt_of_not_ge hbt).le
    have hp := hstrict τ hτ hbound z hz n a τ ha hat.le le_rfl
      (fun t ht=>hband t ⟨ht.1,ht.2.trans htb⟩)
    have hm := incrementBound_mono hM.le hA hP.le hL (show 0≤(2:ℝ)^n by positivity)
      (show τ-a≤b-a by linarith)
    have hl := hLip z hz τ hτ b ⟨hτ0.trans htb,hb.trans hnewT⟩
    rw [abs_of_nonneg (sub_nonneg.mpr htb)] at hl
    have hs := Real.sqrt_le_sqrt (le_of_not_ge hlen)
    have hpos := Real.sqrt_nonneg ℓ
    have hc : C*(b-τ)≤M*P*Real.sqrt (b-a)/2 := by
      have hh := (le_div_iff₀ (by positivity : 0<2*(C+1))).mp hδcost
      have h1 := mul_le_mul_of_nonneg_left (show b-τ≤δ by linarith) hC
      have h2 := mul_le_mul_of_nonneg_left hs hMP.le
      nlinarith
    have hrest : 0≤A*(b-a)*(P^2*L/(2:ℝ)^n) := by positivity
    have hn : ‖V z b-V z a‖≤‖V z b-V z τ‖+‖V z τ-V z a‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    dsimp [incrementBound] at hp hm ⊢
    linarith
  have hnewmem : τ+δ∈S := ⟨⟨by linarith,hnewT⟩,hnew⟩
  have hh : τ+δ≤τ := le_csSup hbdd hnewmem
  linarith

lemma SmoothClassicalPrefix.restrict {d : Datum} {s : Solution} {T τ : ℝ}
    (hs : SmoothClassicalPrefix d s T) (hτT : τ≤T) : SmoothClassicalPrefix d s τ where
  f_smooth := hs.f_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  E_smooth := hs.E_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  B_smooth := hs.B_smooth.mono (fun p hp=>⟨hp.1,hp.2.trans hτT⟩)
  nonnegative := fun t ht=>hs.nonnegative t ⟨ht.1,ht.2.trans hτT⟩
  E_L2 := by
    obtain ⟨F₂,hF,hE⟩ := hs.E_L2
    exact ⟨F₂,hF.mono (Icc_subset_Icc le_rfl hτT),fun t ht=>hE t ⟨ht.1,ht.2.trans hτT⟩⟩
  B_L2 := by
    obtain ⟨F₂,hF,hB⟩ := hs.B_L2
    exact ⟨F₂,hF.mono (Icc_subset_Icc le_rfl hτT),fun t ht=>hB t ⟨ht.1,ht.2.trans hτT⟩⟩
  compact := by
    obtain ⟨K,hK,hk⟩ := hs.compact
    exact ⟨K,hK,fun t ht=>hk t ⟨ht.1,ht.2.trans hτT⟩⟩
  equations := fun t ht htτ=>hs.equations t ht (htτ.trans_le hτT)
  initial_f := hs.initial_f
  initial_E := hs.initial_E
  initial_B := hs.initial_B

lemma PhaseFlowOn.supported_momentum_lipschitz {d : Datum} {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hd : Admissible d) (hs : SmoothClassicalPrefix d s T) (hT : 0≤T) :
    ∃C : ℝ,0≤C ∧ ∀z∈tsupport d.f₀,∀a∈Icc 0 T,∀b∈Icc 0 T,
      ‖(F.flow z b).2-(F.flow z a).2‖≤C*|b-a| := by
  have hα := F.continuous_prefixFlow hs.energyPrefix hT
  have hX : Continuous (fun p : ℝ×Phase=>(p.1,(prefixFlow F.flow T p.2 p.1).1)) := continuous_fst.prodMk hα.fst
  have hE := (continuous_prefixField hs.energyPrefix.E_smooth.continuousOn hT).comp hX
  have hB := (continuous_prefixField hs.energyPrefix.B_smooth.continuousOn hT).comp hX
  have hv := (contDiff_velocity (k:=1)).continuous.comp hα.snd
  have hc : Continuous (fun p : ℝ×Phase=>prefixMomentumForce s F.flow T p.2 p.1) :=
    hE.add ((contDiff_cross (k:=1)).continuous.comp (hv.prodMk hB))
  obtain ⟨R,hR⟩ := (isCompact_Icc.prod hd.2.1).bddAbove_image hc.norm.continuousOn
  let C := max 0 R
  have hC : 0≤C := le_max_left _ _
  refine ⟨C,hC,?_⟩
  intro z hz a ha b hb
  have hLip : LipschitzOnWith ⟨C,hC⟩ (fun t=>(F.flow z t).2) (Icc 0 T) := by
    apply (convex_Icc 0 T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (fun t ht=>(F.ode z t ht).snd)
    intro t ht
    apply NNReal.coe_le_coe.mp
    change ‖(lorentzField s.E s.B (t,F.flow z t)).2‖≤C
    have hh := hR ⟨(t,z),⟨ht,hz⟩,rfl⟩
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq ht] at hh
    exact hh.trans (le_max_right _ _)
  have hh := hLip.dist_le_mul b hb a ha
  change ‖(F.flow z b).2-(F.flow z a).2‖≤C*‖b-a‖ at hh
  simpa only [Real.norm_eq_abs] using hh

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.uniform_signed_increment {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A P₀ : ℝ,32≤M ∧ 1≤A ∧ 1≤P₀ ∧
    ∀P : ℝ,P₀≤P →
    ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
      (∀t∈Icc 0 T,∀z∈tsupport d.f₀,1024*q (F.flow z t).2≤P) →
      ∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P)) := by
  obtain ⟨M,A,hM,hA,hstrict⟩ := hd.signed_increment_strict T₀
  obtain ⟨P₁,hP₁⟩ := Filter.eventually_atTop.mp hstrict
  obtain ⟨P₂,hP₂⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_log_atTop.comp (Filter.tendsto_atTop_add_const_left _ 2 tendsto_id)).eventually (eventually_ge_atTop 1))
  let P₀ := max 1 (max P₁ P₂)
  refine ⟨M,A,P₀,hM,hA,le_max_left _ _,?_⟩
  intro P hP s T F hs hT hTT hcap
  have hP1 : 1≤P := (le_max_left 1 _).trans hP
  have hlog : 1≤Real.log (2+P) := hP₂ P (((le_max_right P₁ P₂).trans (le_max_right 1 _)).trans hP)
  have hS := hP₁ P (((le_max_left P₁ P₂).trans (le_max_right 1 _)).trans hP)
  obtain ⟨C,hC,hLip⟩ := F.supported_momentum_lipschitz hd hs hT
  apply signed_bootstrap_propagation hT (by linarith) (by linarith)
    (by linarith) (by linarith) hC hLip
  intro τ hτ H z hz n a b ha hab hb hband
  exact hS hP1 hlog s τ (F.restrict hτ.2) (hs.restrict hτ.2) hτ.1 (hτ.2.trans hTT)
    (fun t ht=>hcap t ⟨ht.1,ht.2.trans hτ.2⟩) H z hz n a b ha hab hb hband

lemma Admissible.population_increment {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃M A P₀ : ℝ,0<M ∧ 0<A ∧ 1≤P₀ ∧
    ∀(s : Solution) (T : ℝ) (flow : Phase→ℝ→Phase),T≤T₀ →
      (∀τ∈Ico 0 T, SmoothClassicalPrefix d s τ ∧
        ∃ F : PhaseFlowOn s.E s.B τ,F.flow=flow) →
      PopulationIncrement (fun z t=>(flow z t).2) (tsupport d.f₀) T M A P₀ := by
  obtain ⟨M,A,P₀,hM,hA,hP₀,hU⟩ := hd.uniform_signed_increment T₀
  refine ⟨M,A,P₀,by linarith,by linarith,hP₀,?_⟩
  intro s T flow hTT hpref τ hτ k hk hcap
  obtain ⟨hs,F,hF⟩ := hpref τ hτ
  have hh := hU (2^k) hk s τ F hs hτ.1 (hτ.2.le.trans hTT)
  rw [hF] at hh
  exact hh hcap

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Main
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Global classical solvability and uniqueness for smooth admissible data. -/

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma Admissible.uniform_physical_population_increment_oai {d : Datum} (hd : Admissible d)
    (H : ℝ) :
    ∃ M A P₀ : ℝ, 0 < M ∧ 0 < A ∧
      ∀ U : ℝ, 0 < U → U ≤ H → ∀ s : Solution,
      BoundedClassicalPrefix d s U → ∀ F : PhaseFlowOn s.E s.B U,
        PopulationIncrement (fun z t => (F.flow z t).2) (tsupport d.f₀) U M A P₀ := by
  obtain ⟨M, A, P₀, hM, hA, hP₀, hinc⟩ := hd.population_increment H
  refine ⟨M, A, P₀, hM, hA, ?_⟩
  intro U hU hUH s hs F
  apply hinc s U F.flow hUH
  intro τ hτ
  exact ⟨hs.classical.restrict hτ.2.le, F.restrict hτ.2.le, rfl⟩

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.uniform_physical_population_increment_oai := @OAI.RVM.Admissible.uniform_physical_population_increment_oai
