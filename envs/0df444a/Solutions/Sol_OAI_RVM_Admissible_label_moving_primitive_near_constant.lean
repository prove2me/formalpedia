-- Prove2me | solution 1 for OAI.RVM.Admissible.label_moving_primitive_near_constant
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:06:38.702995+00:00
-- url     : https://prove2.me/submissions/8d6ad58b-76e4-4e35-9000-c9441a6cf6fd

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_labelConeKernel_triangle_weighted_norm

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

lemma dot_comm (a b : Vec) : dot a b = dot b a := by
  simp only [dot, mul_comm]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_sub_right (a b c : Vec) : dot a (b - c) = dot a b - dot a c := by
  rw [dot_comm, dot_sub_left, dot_comm b a, dot_comm c a]

lemma dot_smul_right (r : ℝ) (a b : Vec) : dot a (r • b) = r * dot a b := by
  rw [dot_comm, dot_smul_left, dot_comm b a]

lemma dot_le_norm (a b : Vec) : dot a b ≤ ‖a‖ * ‖b‖ := by
  rw [dot_eq_inner]
  exact real_inner_le_norm a b

lemma cone_denom_pos (v n : Vec) (hn : ‖n‖ = 1) :
    0 < 1 - dot n (velocity v) := by
  have h := dot_le_norm n (velocity v)
  rw [hn, one_mul] at h
  linarith [norm_velocity_lt_one v]

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

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedSameTimeSeparation
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
open scoped Topology ContDiff NNReal
open Set Filter MeasureTheory Metric
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal RealInnerProductSpace

namespace RVM

lemma exists_axis_basis (a : Vec) : ∃ b : OrthonormalBasis (Fin 3) ℝ Vec,
    ∀ i, i≠0 → dot (b i) a=0 := by
  classical
  by_cases ha : a=0
  · exact ⟨EuclideanSpace.basisFun (Fin 3) ℝ,fun i _ => by simp [ha,dot]⟩
  have hpos : 0<‖a‖ := norm_pos_iff.mpr ha
  let n : Vec := ‖a‖⁻¹ • a
  have hn : ‖n‖=1 := by simp [n,norm_smul,hpos.ne']
  have horth : Orthonormal ℝ (({0} : Set (Fin 3)).domRestrict (fun _ => n)) := by
    rw [orthonormal_subsingleton_iff]
    exact fun _ => hn
  obtain ⟨b,hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (show Module.finrank ℝ Vec=Fintype.card (Fin 3) by simp)
  refine ⟨b,fun i hi => ?_⟩
  have hzero := b.orthonormal.inner_eq_zero hi
  rw [hb 0 (mem_singleton _)] at hzero
  have he : a=‖a‖ • n := by simp [n,smul_smul,hpos.ne']
  rw [dot_eq_inner,he,inner_smul_right,hzero,mul_zero]

lemma volume_axis_box (b : OrthonormalBasis (Fin 3) ℝ Vec) {R S : ℝ}
    (hR : 0≤R) (hS : 0≤S) :
    volume {v : Vec | |dot (b 0) v|≤R ∧ |dot (b 1) v|≤S ∧ |dot (b 2) v|≤S} =
      ENNReal.ofReal (8*R*S^2) := by
  let F : Vec → Fin 3 → ℝ := fun v => WithLp.ofLp (b.repr v)
  have hp : MeasurePreserving F volume volume :=
    (PiLp.volume_preserving_ofLp (Fin 3)).comp b.measurePreserving_repr
  let A : Set (Fin 3 → ℝ) := Icc ![-R,-S,-S] ![R,S,S]
  have he : {v : Vec | |dot (b 0) v|≤R ∧ |dot (b 1) v|≤S ∧ |dot (b 2) v|≤S}=F ⁻¹' A := by
    ext v
    simp only [mem_ofPred_eq,mem_preimage,A,mem_Icc,Pi.le_def,F,OrthonormalBasis.repr_apply_apply,
      ← dot_eq_inner,Fin.forall_fin_succ,Matrix.cons_val_zero,
      Matrix.cons_val_succ,Fin.forall_fin_zero,and_true]
    simp only [abs_le]
    tauto
  rw [he,hp.measure_preimage measurableSet_Icc.nullMeasurableSet,Real.volume_Icc_pi]
  simp only [Matrix.cons_val_zero,Matrix.cons_val_succ,Fin.prod_univ_succ,Fin.prod_univ_zero,
    mul_one,sub_neg_eq_add]
  rw [← ENNReal.ofReal_mul (by positivity),← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

lemma volume_velocity_cap {P δ : ℝ} (hP : 0≤P) (hδ : 0≤δ) (a : Vec) :
    volume {v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ} ≤ ENNReal.ofReal (8*P^3*δ^2) := by
  obtain ⟨b,hb⟩ := exists_axis_basis a
  have hsub : {v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ} ⊆
      {v : Vec | |dot (b 0) v|≤P ∧ |dot (b 1) v|≤P*δ ∧ |dot (b 2) v|≤P*δ} := by
    intro v hv
    have hn : ‖v‖≤P := (norm_lt_q v).le.trans hv.1
    have hall (i : Fin 3) : |dot (b i) v|≤P := by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm _ _).trans (by simpa only [b.orthonormal.norm_eq_one,one_mul] using hn)
    have hsmall (i : Fin 3) (hi : i≠0) : |dot (b i) v|≤P*δ := by
      have hd : |dot (b i) (velocity v-a)|≤δ := by
        rw [dot_eq_inner]
        exact (abs_real_inner_le_norm _ _).trans (by simpa only [b.orthonormal.norm_eq_one,one_mul] using hv.2)
      rw [dot_sub_right,hb i hi,sub_zero,velocity,dot_smul_right,abs_mul,
        abs_of_pos (inv_pos.mpr (q_pos v))] at hd
      have hh := (mul_le_mul_of_nonneg_left hd (q_pos v).le)
      rw [← mul_assoc,mul_inv_cancel₀ (q_pos v).ne',one_mul] at hh
      exact hh.trans (mul_le_mul_of_nonneg_right hv.1 hδ)
    exact ⟨hall 0,hsmall 1 (by decide),hsmall 2 (by decide)⟩
  have hh := (measure_mono hsub).trans_eq (volume_axis_box b hP (mul_nonneg hP hδ))
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma lintegral_velocity_cap_density {P δ C : ℝ} (hP : 0≤P) (hδ : 0≤δ)
    (hC : 0≤C) (a : Vec) {g : Vec → ℝ} (hg : ∀ v, g v≤C)
    {H : Set Vec} (hH : H⊆{v : Vec | q v≤P ∧ ‖velocity v-a‖≤δ}) :
    (∫⁻ v in H, ENNReal.ofReal (g v))≤ENNReal.ofReal (8*C*P^3*δ^2) := by
  calc
    _ ≤ ∫⁻ _v in H, ENNReal.ofReal C := lintegral_mono (fun v => ENNReal.ofReal_le_ofReal (hg v))
    _ = ENNReal.ofReal C * volume H := by rw [lintegral_const,Measure.restrict_apply_univ]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (8*P^3*δ^2) := by
      gcongr
      exact (measure_mono hH).trans (volume_velocity_cap hP hδ a)
    _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring

lemma sphere_cap_area {δ : ℝ} (hδ : 0≤δ) (a : Vec) :
    sphereMeasure {n : Sphere | ‖n.1-a‖≤δ}≤ENNReal.ofReal (24*δ^2) := by
  classical
  let A : Set Sphere := {n | ‖n.1-a‖≤δ}
  have hA : MeasurableSet A := isClosed_le
    ((continuous_subtype_val.sub continuous_const).norm) continuous_const |>.measurableSet
  obtain ⟨b,hb⟩ := exists_axis_basis a
  let B : Set Vec := {v | |dot (b 0) v|≤1 ∧ |dot (b 1) v|≤δ ∧ |dot (b 2) v|≤δ}
  have hsub : Set.image2 (fun (r : ℝ) (n : Vec) => r • n) (Ioo 0 1) (Subtype.val '' A)⊆B := by
    rintro v ⟨r,hr,n,⟨N,hN,rfl⟩,rfl⟩
    have hh (i : Fin 3) : |dot (b i) N.1|≤1 := by
      rw [dot_eq_inner]
      exact (abs_real_inner_le_norm _ _).trans_eq (by rw [b.orthonormal.norm_eq_one,sphere_norm,one_mul])
    have ht (i : Fin 3) (hi : i≠0) : |dot (b i) N.1|≤δ := by
      have hd := abs_real_inner_le_norm (b i) (N.1-a)
      rw [← dot_eq_inner,dot_sub_right,hb i hi,sub_zero,b.orthonormal.norm_eq_one,one_mul] at hd
      exact hd.trans hN
    have hm (i : Fin 3) (D : ℝ) (hD : 0≤D) (hi : |dot (b i) N.1|≤D) :
        |dot (b i) (r • N.1)|≤D := by
      rw [dot_smul_right,abs_mul,abs_of_pos hr.1]
      exact (mul_le_mul_of_nonneg_left hi hr.1.le).trans (by nlinarith [hr.2])
    exact ⟨hm 0 1 zero_le_one (hh 0),hm 1 δ hδ (ht 1 (by decide)),hm 2 δ hδ (ht 2 (by decide))⟩
  rw [show {n : Sphere | ‖n.1-a‖≤δ}=A from rfl,(volume : Measure Vec).toSphere_apply' hA]
  have hdim : Module.finrank ℝ Vec=3 := by simp
  rw [hdim]
  change (3 : ENNReal) * volume (Set.image2 (fun (r : ℝ) (n : Vec) => r • n) (Ioo 0 1) (Subtype.val '' A))≤_
  calc
    _ ≤ 3*volume B := by gcongr
    _ = 3*ENNReal.ofReal (8*1*δ^2) := by rw [volume_axis_box b zero_le_one hδ]
    _ = _ := by rw [show (3:ENNReal)=ENNReal.ofReal 3 by norm_num,← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring

lemma norm_sub_le_of_deficit {u a : Vec} {δ : ℝ} (hu : ‖u‖≤1) (ha : ‖a‖≤1)
    (hδ : 0≤δ) (hd : 1-dot u a≤δ^2/2) : ‖u-a‖≤δ := by
  have he : ‖u-a‖^2=‖u‖^2+‖a‖^2-2*dot u a := by rw [norm_sub_sq_real,dot_eq_inner]; ring
  have hu2 : ‖u‖^2≤1 := by nlinarith [norm_nonneg u]
  have ha2 : ‖a‖^2≤1 := by nlinarith [norm_nonneg a]
  nlinarith [norm_nonneg (u-a)]

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
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma measurableSet_coneBinMomentumSet (B : ClosedConeBin) (n a : Vec) :
    MeasurableSet (coneBinMomentumSet B n a) := by
  exact ((measurableSet_Icc.preimage (contDiff_q (k:=0)).continuous.measurable).inter
    ((measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable).inter
      (measurableSet_Icc.preimage (continuous_const.sub (continuous_dot.comp
      (continuous_const.prodMk (contDiff_velocity (k:=0)).continuous))).measurable)))

lemma coneBin_density_small_bound {B : ClosedConeBin} {n a : Vec} {P θ C : ℝ}
    (hn : ‖n‖ ≤ 1) (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2)
    {g : Vec → ℝ} (hg : ∀ v, g v ≤ C) :
    (∫⁻ v in coneBinMomentumSet B n a, ENNReal.ofReal (g v))  ≤
      ENNReal.ofReal (128*C*P^3*θ^2) := by
  have hsub : coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-n‖ ≤ 4*θ} := by
    intro v hv
    refine ⟨hv.1.2.trans hq,?_⟩
    apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le hn (by positivity)
    rw [dot_comm]
    nlinarith [hv.2.1.2]
  convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*θ) hC n hg hsub using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

lemma measurableSet_physicalBinBase {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinBase V B J) := by
  have htime : MeasurableSet {z : ConeCoordinate | z.2.1 ∈ Icc 0 z.1} :=
    (measurableSet_le measurable_const (measurable_fst.comp measurable_snd)).inter
      (measurableSet_le (measurable_fst.comp measurable_snd) measurable_fst)
  exact (hJ.preimage measurable_fst).inter (htime.inter
    ((measurableSet_Icc.preimage (measurable_fst.sub (measurable_fst.comp measurable_snd))).inter
      ((measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp
        (hV.comp measurable_fst))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp
        ((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).prodMk
          ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))))))

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

lemma velocityProjection_norm (u b : Vec) (hu : ‖u‖ ≤ 1) :
    ‖velocityProjection u b‖ ≤ ‖b‖ := by
  have hsq : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have he : ‖velocityProjection u b‖^2 =
      ‖b‖^2 - 2*(dot u b)^2+(dot u b)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm b u]
    ring
  have hh := mul_le_mul_of_nonneg_left hsq (sq_nonneg (dot u b))
  nlinarith [norm_nonneg (velocityProjection u b), norm_nonneg b]

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

end RVM

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

lemma transverseProjection_norm (w h : Vec) : ‖transverseProjection w h‖≤‖h‖ := by
  apply velocityProjection_norm
  by_cases hw : w=0
  · simp [hw]
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (norm_nonneg w)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]

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


lemma signedPrimitive_decomposition (a u n : Vec) (hD : 1-dot n a ≠ 0) :
    signedPrimitive a u n = (u-n)+
      ((1-dot n a-(1-dot a u))/(1-dot n a)) • n := by
  ext i
  simp only [signedPrimitive,PiLp.sub_apply,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp
  ring

lemma small_deficit_difference {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 ≤ φ) (hsmall : θ ≤ φ)
    (hd0 : 0 ≤ 1-dot n u) (hd : 1-dot n u ≤ 8*θ^2)
    (hun : ‖u-n‖ ≤ 4*θ) (han : ‖a-n‖ ≤ 4*φ) :
    |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ := by
  have he : (1-dot a u)-(1-dot n a)=(1-dot n u)+dot (a-n) (n-u) := by
    simp only [dot_sub_left,dot_sub_right,dot_self,hn,one_pow,dot_comm a n]
    ring
  rw [he]
  calc
    _ ≤ |1-dot n u|+|dot (a-n) (n-u)| := abs_add_le _ _
    _ ≤ 8*θ^2+‖a-n‖*‖n-u‖ := by
      gcongr
      · rwa [abs_of_nonneg hd0]
      · rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
    _ ≤ 8*θ^2+(4*φ)*(4*θ) := by
      gcongr
      rwa [norm_sub_rev]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hsmall hθ]

lemma small_primitive_norm {a u n : Vec} {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1)
    (hD : φ^2/2 ≤ 1-dot n a)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ) :
    ‖signedPrimitive a u n‖ ≤ 52*θ/φ := by
  have hDpos : 0 < 1-dot n a := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n a-(1-dot a u))/(1-dot n a)| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  rw [signedPrimitive_decomposition a u n hDpos.ne']
  calc
    _ ≤ ‖u-n‖+‖((1-dot n a-(1-dot a u))/(1-dot n a)) • n‖ := norm_add_le _ _
    _ ≤ 4*θ+48*θ/φ := by simpa only [norm_smul,Real.norm_eq_abs,hn,mul_one] using add_le_add hun hratio
    _ ≤ _ := by
      apply (le_div_iff₀ hφ).mpr
      have hm := mul_le_mul_of_nonneg_left hφ1 (by positivity : 0 ≤ 4*θ)
      field_simp
      nlinarith


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_UniformParticleDensityConstant
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
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma Admissible.uniform_particle_density_constant {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (t : ℝ), t ∈ Icc 0 T → ∀ (z : Phase), 0 ≤ s.f (t,z) ∧ s.f (t,z) ≤ C := by
  obtain ⟨C,hC⟩ := hd.1.continuous.bounded_above_of_compact_support hd.2.1
  refine ⟨max 0 C,le_max_left _ _,?_⟩
  intro s T F hs h0 t ht z
  refine ⟨hs.nonnegative t ht z,?_⟩
  rw [F.transport_inverse hs.f_smooth hs.vlasov ht,h0]
  exact (le_abs_self _).trans ((hC _).trans (le_max_right _ _))

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

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
lemma dyadicCut_nonneg (x : ℝ) : 0≤dyadicCut x := sub_nonneg.mpr (Real.smoothTransition.le_one _)
lemma dyadicCut_le_one (x : ℝ) : dyadicCut x≤1 := sub_le_self _ (Real.smoothTransition.nonneg _)
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_nonneg (x : ℝ) : 0≤dyadicBump x := by
  by_cases hx : x≤1/2
  · rw [dyadicBump_zero_left hx]
  · exact sub_nonneg.mpr (dyadicCut_antitone (by linarith : x≤2*x))
lemma dyadicBump_le_one (x : ℝ) : dyadicBump x≤1 :=
  (sub_le_self _ (dyadicCut_nonneg _)).trans (dyadicCut_le_one _)
lemma dyadicFactor_nonneg (n : ℕ) (x : ℝ) : 0≤dyadicFactor n x := dyadicBump_nonneg _
lemma dyadicFactor_le_one (n : ℕ) (x : ℝ) : dyadicFactor n x≤1 := dyadicBump_le_one _

lemma dyadicFactor_tsupport {n : ℕ} {x : ℝ} (hx : x ∈ tsupport (dyadicFactor n)) :
    DyadicBand n x := by
  have hcl : IsClosed {x : ℝ | DyadicBand n x} :=
    (isClosed_le continuous_const (continuous_const.mul continuous_id)).inter
      (isClosed_le (continuous_const.mul continuous_id) continuous_const)
  apply (closure_minimal (s:=(Function.support (dyadicFactor n))) ?_ hcl) hx
  intro y hy
  constructor
  · by_contra hn
    exact hy (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hy (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

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

lemma dyadicMultiFactor_positive_bands {ι : Type*} [Fintype ι]
    {n : ι→ℕ} {x : ι→ℝ} (h : 0<dyadicMultiFactor n x) : ∀ i,DyadicBand (n i) (x i) := by
  classical
  intro i
  apply dyadicFactor_tsupport
  apply subset_tsupport
  intro he
  have hz : dyadicMultiFactor n x=0 := Finset.prod_eq_zero (Finset.mem_univ i) he
  linarith

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


lemma momentumDirection_norm {v : Vec} (hv : v ≠ 0) : ‖momentumDirection v‖=1 := by
  simp [momentumDirection,norm_smul,norm_ne_zero_iff.mpr hv]

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

lemma angularMultiplier_derivative_bound (w : ℝ) (v K h : Vec) (hv : v ≠ 0) :
    ‖(-w/‖v‖^2) •
        (dot (momentumDirection v) K • transverseProjection v h +
         dot (momentumDirection v) h • transverseProjection v K +
         dot (transverseProjection v K) h • momentumDirection v)‖ ≤
      3*|w|/‖v‖^2*‖K‖*‖h‖ := by
  have hξ := momentumDirection_norm hv
  have ha : |dot (momentumDirection v) K| ≤ ‖K‖ := by simpa only [hξ,one_mul] using abs_dot_le (momentumDirection v) K
  have hb : |dot (momentumDirection v) h| ≤ ‖h‖ := by simpa only [hξ,one_mul] using abs_dot_le (momentumDirection v) h
  have hc : |dot (transverseProjection v K) h| ≤ ‖K‖*‖h‖ :=
    (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right (transverseProjection_norm _ _) (norm_nonneg _))
  have hsum : ‖dot (momentumDirection v) K • transverseProjection v h +
         dot (momentumDirection v) h • transverseProjection v K +
         dot (transverseProjection v K) h • momentumDirection v‖ ≤ 3*‖K‖*‖h‖ := by
    calc
      _ ≤ ‖dot (momentumDirection v) K • transverseProjection v h‖ +
          ‖dot (momentumDirection v) h • transverseProjection v K‖ +
          ‖dot (transverseProjection v K) h • momentumDirection v‖ := norm_add₃_le
      _ ≤ ‖K‖*‖h‖+‖h‖*‖K‖+‖K‖*‖h‖ := by
        simp only [norm_smul,Real.norm_eq_abs,hξ,mul_one]
        exact add_le_add (add_le_add (mul_le_mul ha (transverseProjection_norm _ _) (norm_nonneg _) (norm_nonneg _))
          (mul_le_mul hb (transverseProjection_norm _ _) (norm_nonneg _) (norm_nonneg _))) hc
      _ = _ := by ring
  rw [norm_smul,Real.norm_eq_abs,abs_div,abs_neg,abs_sq]
  exact (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq (by ring)

lemma dyadicBand_capped_range {n : ℕ} {x : ℝ} (h : DyadicBand n x) :
    cappedRepresentative n/2≤x ∧ x≤2*cappedRepresentative n := by
  have hp : 0<(2:ℝ)^n := by positivity
  have he : cappedRepresentative n = ((2:ℝ)^n)⁻¹ := by simp [cappedRepresentative,inv_pow]
  rw [he]
  constructor
  · rw [inv_eq_one_div,div_div]
    exact (div_le_iff₀ (mul_pos hp (by norm_num))).mpr (by nlinarith [h.1])
  · rw [inv_eq_one_div,mul_one_div]
    exact (le_div_iff₀ hp).mpr (by nlinarith [h.2])

lemma dyadicBand_source_range {n : ℕ} {v : Vec} (h : DyadicBand n (1/q v)) :
    sourceRepresentative n/128≤q v ∧ q v≤ sourceRepresentative n/32 := by
  have hlo := h.1
  have hhi := h.2
  rw [mul_one_div] at hlo hhi
  have ha := (le_div_iff₀ (q_pos v)).mp hlo
  have hb := (div_le_iff₀ (q_pos v)).mp hhi
  dsimp [sourceRepresentative]
  constructor <;> linarith

lemma dyadicBand_angular_range {n : ℕ} {d : ℝ} (hd : 0≤d)
    (h : DyadicBand n (Real.sqrt (d/2))) :
    (cappedRepresentative n)^2/2≤d ∧ d≤8*(cappedRepresentative n)^2 := by
  have hh := dyadicBand_capped_range h
  have hp : 0 < cappedRepresentative n := by dsimp [cappedRepresentative]; positivity
  have hs := Real.sq_sqrt (by positivity : 0≤d/2)
  have hn := Real.sqrt_nonneg (d/2)
  have hlo := mul_self_le_mul_self (by positivity : 0 ≤ cappedRepresentative n/2) hh.1
  have hhi := mul_self_le_mul_self hn hh.2
  constructor <;> nlinarith

lemma dyadicBand_radius_range {n : ℕ} {T r : ℝ}
    (h : DyadicBand n (r/max 1 T)) :
    max 1 T*cappedRepresentative n/2 ≤ r ∧ r≤2*max 1 T*cappedRepresentative n := by
  have hm : 0 < max (1:ℝ) T := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hh := dyadicBand_capped_range h
  have ha := (le_div_iff₀ hm).mp hh.1
  have hb := (div_le_iff₀ hm).mp hh.2
  constructor <;> nlinarith

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

lemma angularDerivativeCLM_norm_le (w : ℝ) (v K : Vec) (hv : v≠0) :
    ‖angularDerivativeCLM w v K‖≤3*|w|/‖v‖^2*‖K‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro h
  rw [angularDerivativeCLM_apply]
  exact angularMultiplier_derivative_bound w v K h hv



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

namespace RVM

lemma physicalBinMeasure_receiver_weight {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {φ : ℝ}
    (hφ : 0≤φ) (hD : B.Dmax≤8*φ^2) {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2) := by
  let A : Set ConeCoordinate := {z | z.1∈J ∧
    z.2.1∈Icc (z.1-B.rmax) (z.1-B.rmin) ∧
    ‖z.2.2.1-velocity (V z.1)‖≤4*φ}
  have hA : MeasurableSet A := by
    exact (hJ.preimage measurable_fst).inter
      (((measurableSet_le (measurable_fst.sub_const _) (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.sub_const _))).inter
      (measurableSet_le (((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).sub
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst))).norm) measurable_const))
  have hsub : physicalBinBase V B J⊆A := by
    intro z hz
    refine ⟨hz.1,⟨by linarith [hz.2.2.1.2],by linarith [hz.2.2.1.1]⟩,?_⟩
    apply norm_sub_le_of_deficit (sphere_norm z.2.2).le (norm_velocity_lt_one _).le (by positivity)
    nlinarith [hz.2.2.2.2.2]
  have hm : (∫⁻z : ConeCoordinate,A.indicator (fun z=>g z.1) z ∂volume.prod (volume.prod sphereMeasure))=
      ∫⁻t in J,g t*(ENNReal.ofReal (B.rmax-B.rmin)*
        sphereMeasure {n : Sphere | ‖n.1-velocity (V t)‖≤4*φ}) := by
    have hmg : Measurable (A.indicator (fun z : ConeCoordinate=>g z.1)) :=
      (hg.comp measurable_fst).indicator hA
    rw [lintegral_prod _ hmg.aemeasurable,←lintegral_indicator hJ]
    apply lintegral_congr
    intro t
    by_cases ht : t∈J
    · rw [indicator_of_mem ht]
      have he : (fun p : ℝ×Sphere=>A.indicator (fun z=>g z.1) (t,p))=
          ((Icc (t-B.rmax) (t-B.rmin))×ˢ{n : Sphere | ‖n.1-velocity (V t)‖≤4*φ}).indicator
            (fun _=>g t) := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻p : ℝ×Sphere,A.indicator (fun z=>g z.1) (t,p) ∂volume.prod sphereMeasure)=_
      rw [he,lintegral_indicator]
      · rw [lintegral_const,Measure.restrict_apply_univ,Measure.prod_prod,Real.volume_Icc]
        congr 2
        ring_nf
      · exact measurableSet_Icc.prod (measurableSet_le
          ((continuous_subtype_val.sub continuous_const).norm.measurable) measurable_const)
    · rw [indicator_of_notMem ht]
      have he : (fun p : ℝ×Sphere=>A.indicator (fun z=>g z.1) (t,p))=0 := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻p : ℝ×Sphere,A.indicator (fun z=>g z.1) (t,p) ∂volume.prod sphereMeasure)=_
      rw [he]
      exact lintegral_zero
  calc
    _ ≤ ∫⁻z : ConeCoordinate,g z.1 ∂(volume.prod (volume.prod sphereMeasure)).restrict A :=
      lintegral_mono_set hsub
    _ = ∫⁻z : ConeCoordinate,A.indicator (fun z=>g z.1) z ∂volume.prod (volume.prod sphereMeasure) :=
      (lintegral_indicator hA _).symm
    _ = _ := hm
    _ ≤ ∫⁻t in J,g t*(ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
      apply lintegral_mono
      intro t
      apply mul_le_mul' le_rfl
      apply mul_le_mul' le_rfl
      convert sphere_cap_area (by positivity : 0≤4*φ) (velocity (V t)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    _ = _ := by
      rw [lintegral_mul_const _ hg]
      ac_rfl

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

lemma continuousOn_normalisedPrimitive {Q : Type*} [TopologicalSpace Q]
    {r : Q→ℝ} {a u n : Q→Vec} {S : Set Q}
    (hr : ContinuousOn r S) (ha : ContinuousOn a S) (hu : ContinuousOn u S)
    (hn : ContinuousOn n S) (hd : ∀p∈S,1-dot (n p) (u p)≠0)
    (hD : ∀p∈S,1-dot (n p) (a p)≠0) :
    ContinuousOn (fun p=>normalisedPrimitive (r p) (a p) (u p) (n p)) S := by
  have hdot {f g : Q→Vec} (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun p=>dot (f p) (g p)) S := by
    simpa only [dot_eq_inner] using hf.inner hg
  exact (hr.div (continuousOn_const.sub (hdot hn hu)) hd).smul
    (hu.sub (((continuousOn_const.sub (hdot ha hu)).div
      (continuousOn_const.sub (hdot hn ha)) hD).smul hn))

end RVM

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

lemma PhaseFlowOn.normalisedRatePrimitive_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) :
    ContinuousOn (normalisedRatePrimitive F.flow zX) (coneKernelDomain T) := by
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2)
      (coneKernelDomain T) := (contDiff_velocity (k:=1)).continuous.comp_continuousOn
        (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd)
  have hu : Continuous (fun p : ConeKernelState=>velocity p.2.2.2) :=
    (contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hD : ∀p∈coneKernelDomain T,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'
  have hr : ContinuousOn (fun p : ConeKernelState=>(1-dot p.2.1 (velocity p.2.2.2))/
      (1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) (coneKernelDomain T) := by
    simp only [dot_eq_inner]
    exact (continuousOn_const.sub (hn.continuousOn.inner hu.continuousOn)).div
      (continuousOn_const.sub (hn.continuousOn.inner ha))
      (fun p hp=>by simpa only [dot_eq_inner] using hD p hp)
  refine hr.smul (continuousOn_normalisedPrimitive
    (continuous_fst.fst.sub continuous_fst.snd).continuousOn ha hu.continuousOn hn.continuousOn ?_ hD)
  intro p hp
  exact (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.2.1)).ne'

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


lemma moving_projector_small_kernel {w f r θ φ : ℝ} {v u n K : Vec}
    (hf : 0≤f) (hr : 0 < r) (hv : v≠0) (hn : ‖n‖=1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1)
    (hD : φ^2/2≤1-dot n (velocity v)) (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularDerivativeCLM w v K (signedPrimitive (velocity v) u n)‖ ≤
      156*f*|w| *θ*‖K‖/(r*‖v‖^2*φ) := by
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (div_nonneg hf hr.le)]
  calc
    _ ≤ (f/r)*(‖angularDerivativeCLM w v K‖*‖signedPrimitive (velocity v) u n‖) := by
      gcongr
      exact ContinuousLinearMap.le_opNorm _ _
    _ ≤ (f/r)*((3*|w|/‖v‖^2*‖K‖)*(52*θ/φ)) := by
      gcongr
      · exact angularDerivativeCLM_norm_le w v K hv
      · exact small_primitive_norm hn hθ hφ hφ1 hD hun he
    _ = _ := by ring



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


lemma moving_projector_highband_kernel {w f r θ φ : ℝ} {v u n K : Vec}
    (hw : 0<w) (hv : w/16≤‖v‖) (hf : 0≤f) (hr : 0 < r) (hn : ‖n‖=1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hD : φ^2/2≤1-dot n (velocity v))
    (hun : ‖u-n‖≤4*θ)
    (he : |(1-dot (velocity v) u)-(1-dot n (velocity v))|≤24*φ*θ) :
    ‖(f/r) • angularDerivativeCLM w v K (signedPrimitive (velocity v) u n)‖≤
      (39936*θ/(w*φ))*‖K‖*(f/r) := by
  have hvp : 0<‖v‖ := (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le hv
  have hrho : w/‖v‖^2≤256/w := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hvp) hw).mpr
    nlinarith [sq_nonneg (‖v‖-w/16)]
  calc
    _ ≤ 156*f*|w| *θ*‖K‖/(r*‖v‖^2*φ) := moving_projector_small_kernel hf hr
      (norm_pos_iff.mp hvp) hn hθ hφ hφ1 hD hun he
    _ = (156*θ/φ*‖K‖*(f/r))*(w/‖v‖^2) := by rw [abs_of_pos hw]; ring
    _ ≤ (156*θ/φ*‖K‖*(f/r))*(256/w) := by gcongr
    _ = _ := by ring


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal



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


lemma physicalMovingProjectorDensity_bound {s : Solution} {X V K : ℝ→Vec}
    {B : ClosedConeBin} {w θ φ : ℝ} {z : ConeCoordinate}
    (hw : 0<w) (hv : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤1-dot z.2.2.1 (velocity (V z.1)))
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalMovingProjectorDensity s X V B w K z≤
      ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have hhan : ‖velocity (V z.1)-z.2.2.1‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le (sphere_norm _).le (by positivity)
    rw [dot_comm]
    nlinarith
  have hpoint : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖(s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))/(z.1-z.2.1)) •
        angularDerivativeCLM w (V z.1) (K z.1) (signedPrimitive (velocity (V z.1)) (velocity v) z.2.2.1)‖≤
      ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    have hdv : 1-dot z.2.2.1 (velocity v)≤8*θ^2 := hvbin.2.1.2.trans hd
    have hun : ‖velocity v-z.2.2.1‖≤4*θ := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le (sphere_norm _).le (by positivity)
      rw [dot_comm]
      nlinarith
    have he := small_deficit_difference (sphere_norm z.2.2) hθ hφ.le hsmall
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).le hdv hun hhan
    rw [←ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))]
    apply ENNReal.ofReal_le_ofReal
    convert moving_projector_highband_kernel hw hv (hf v) hr (sphere_norm z.2.2) hθ hφ hφ1 hDlo hun he using 1 <;> first | rfl | ring
  unfold physicalMovingProjectorDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      exact setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hpoint
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(39936*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))=(39936*θ/(w*φ)*‖K z.1‖)*(z.1-z.2.1) := by
        field_simp [hr.ne']
      rw [he,ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K z.1‖)]
      rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
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
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma representativeClosedBin_radius_pos (T w : ℝ) (k : Fin 4→ℕ) :
    0<(representativeClosedBin T w k).rmin := by
  have h : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  dsimp [representativeClosedBin,cappedRepresentative]
  positivity

lemma velocity_deficit_mem_unit2 (v w : Vec) :
    1-dot (velocity w) (velocity v)∈Icc (0:ℝ) 2 := by
  have hd := abs_real_inner_le_norm (velocity w) (velocity v)
  rw [←dot_eq_inner] at hd
  have hn : ‖velocity w‖*‖velocity v‖≤1 :=
    (mul_le_of_le_one_left (norm_nonneg _) (norm_velocity_lt_one w).le).trans
      (norm_velocity_lt_one v).le
  have ha := (abs_le.mp (hd.trans hn))
  constructor <;> linarith

lemma physicalCutoff_positive_closedBin {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hband : q (V t)∈Icc (w/8) (8*w))
    {k : Fin 4→ℕ} {n : Sphere} {v : Vec}
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))) :
    (t,σ,n)∈physicalBinBase V (representativeClosedBin T w k) J ∧
      v∈coneBinMomentumSet (representativeClosedBin T w k) n.1 (velocity (V t)) := by
  have hh := dyadicMultiFactor_positive_bands hk
  have hq := dyadicBand_source_range (show DyadicBand (k 0) (1/q v) from hh 0)
  have hd := dyadicBand_angular_range (cone_denom_pos v n.1 (sphere_norm n)).le
    (show DyadicBand (k 1) (Real.sqrt ((1-dot n.1 (velocity v))/2)) from hh 1)
  have hD := dyadicBand_angular_range (cone_denom_pos (V t) n.1 (sphere_norm n)).le
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from hh 2)
  have hr := dyadicBand_radius_range
    (show DyadicBand (k 3) ((t-σ)/max 1 T) from hh 3)
  exact ⟨⟨ht,hσ,hr,hband,hD⟩,⟨hq,hd,velocity_deficit_mem_unit2 v (V t)⟩⟩

lemma dyadicMultiFactor_le_one {ι : Type*} [Fintype ι] (k : ι→ℕ) (x : ι→ℝ) :
    dyadicMultiFactor k x≤1 :=
  Finset.prod_le_one (fun i _=>dyadicFactor_nonneg (k i) (x i))
    (fun i _=>dyadicFactor_le_one (k i) (x i))

lemma PhaseFlowOn.coneDyadicFactor_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ) :
    ContinuousOn (coneDyadicFactor F.flow zX T k) (coneKernelDomain T) := by
  have hV : ContinuousOn (fun p : ConeKernelState=>(F.flow zX p.1.1).2) (coneKernelDomain T) :=
    ((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1)).snd
  have hv : Continuous (fun p : ConeKernelState=>p.2.2.2) := continuous_snd.snd.snd
  have hn : Continuous (fun p : ConeKernelState=>p.2.1) := continuous_snd.fst
  have hu := (contDiff_velocity (k:=1)).continuous.comp hv
  have ha := (contDiff_velocity (k:=1)).continuous.comp_continuousOn hV
  have hq := (contDiff_q (k:=1)).continuous.comp hv
  have hc : ∀i,ContinuousOn (fun p : ConeKernelState=>physicalCutoffCoordinates T (p.1.1-p.1.2)
      p.2.1 p.2.2.2 (F.flow zX p.1.1).2 i) (coneKernelDomain T) := by
    intro i
    fin_cases i
    · exact continuousOn_const.div hq.continuousOn (fun p _=>(q_pos p.2.2.2).ne')
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk hu.continuousOn))).div_const 2).sqrt
    · exact ((continuousOn_const.sub (continuous_dot.comp_continuousOn
        (hn.continuousOn.prodMk ha))).div_const 2).sqrt
    · exact (continuous_fst.fst.sub continuous_fst.snd).continuousOn.div_const _
  exact continuousOn_finsetProd Finset.univ (fun i _=>
    (contDiff_dyadicFactor (k i)).continuous.comp_continuousOn (hc i))

lemma PhaseFlowOn.projectedDyadicRateKernel_continuousOn {E B : Field} {T : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (k : Fin 4→ℕ)
    {G : ℝ→Vec→L[ℝ]Vec} (hG : Continuous G) :
    ContinuousOn (projectedDyadicRateKernel F.flow zX T k G) (coneKernelDomain T) :=
  (F.coneDyadicFactor_continuousOn zX k).smul
    ((hG.comp continuous_fst.fst).continuousOn.clm_apply (F.normalisedRatePrimitive_continuousOn zX))

lemma normalisedRatePrimitive_flux_norm (α : Phase→ℝ→Phase) (zX : Phase)
    {t σ c : ℝ} {n : Sphere} {v : Vec} (hσ : σ<t) (G : Vec→L[ℝ]Vec) :
    (1-dot n.1 (velocity (α zX t).2))*
      ‖c • G (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖ =
      (t-σ)*‖c • G (signedPrimitive (velocity (α zX t).2) (velocity v) n.1)‖ := by
  have hd := cone_denom_pos v n.1 (sphere_norm n)
  have hD := cone_denom_pos (α zX t).2 n.1 (sphere_norm n)
  have he : (1-dot n.1 (velocity v))/(1-dot n.1 (velocity (α zX t).2))*
      ((t-σ)/(1-dot n.1 (velocity v)))=(t-σ)/(1-dot n.1 (velocity (α zX t).2)) := by
    field_simp
  dsimp only [normalisedRatePrimitive,normalisedPrimitive]
  rw [smul_smul,he,map_smul,smul_comm c,norm_smul,Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hσ.le) hD.le)]
  field_simp

lemma projectedDyadicRateKernel_flux_norm (α : Phase→ℝ→Phase) (zX : Phase) (T : ℝ)
    (k : Fin 4→ℕ) (G : ℝ→Vec→L[ℝ]Vec) {t σ c : ℝ} {n : Sphere} {y v : Vec} (hσ : σ<t) :
    (1-dot n.1 (velocity (α zX t).2))*
      ‖c • projectedDyadicRateKernel α zX T k G ((t,σ),(n.1,(y,v)))‖ =
      coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v)))*(t-σ)*
        ‖c • G t (signedPrimitive (velocity (α zX t).2) (velocity v) n.1)‖ := by
  have hχ : 0 ≤ coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v))) := dyadicMultiFactor_nonneg _ _
  dsimp only [projectedDyadicRateKernel]
  rw [smul_comm c,norm_smul,Real.norm_eq_abs,abs_of_nonneg hχ]
  have he := normalisedRatePrimitive_flux_norm α zX (c:=c) (n:=n) (v:=v) hσ (G t)
  change _ * (_ * ‖c • G t (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖) = _
  calc
    _ = coneDyadicFactor α zX T k ((t,σ),(n.1,(y,v))) *
        ((1-dot n.1 (velocity (α zX t).2))*
          ‖c • G t (normalisedRatePrimitive α zX ((t,σ),(n.1,((0 : Vec),v))))‖) := by ring
    _ = _ := by rw [he]; ring

lemma physicalPrimitive_radius_norm {c r : ℝ} (hr : 0 < r) (v : Vec) :
    r*‖c • v‖=r^2*‖(c/r) • v‖ := by
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_div,abs_of_pos hr]
  field_simp

lemma physicalBin_triangle_weight_le {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (T : ℝ)
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
      (physicalBinBase V B J).indicator (fun z : ConeCoordinate=>g z.1) (t,σ,n)
        ∂sphereMeasure)≤∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J := by
  let H : ConeCoordinate→ℝ≥0∞ := (physicalBinBase V B J).indicator (fun z=>g z.1)
  have hm : Measurable H := (hg.comp measurable_fst).indicator (measurableSet_physicalBinBase hV B hJ)
  calc
    _ ≤ ∫⁻t : ℝ,∫⁻σ : ℝ,∫⁻n : Sphere,H (t,σ,n) ∂sphereMeasure := by
      calc
        _ ≤ ∫⁻t in Ioo (0:ℝ) T,∫⁻σ : ℝ,∫⁻n : Sphere,H (t,σ,n) ∂sphereMeasure := by
          apply lintegral_mono
          intro t
          exact lintegral_mono' (Measure.restrict_le_self (μ:=volume) (s:=Ioo (0:ℝ) t)) (fun _=>le_rfl)
        _ ≤ _ := lintegral_mono' (Measure.restrict_le_self (μ:=volume) (s:=Ioo (0:ℝ) T)) (fun _=>le_rfl)
    _ = ∫⁻z : ConeCoordinate,H z ∂volume.prod (volume.prod sphereMeasure) := by
      rw [lintegral_prod _ hm.aemeasurable]
      apply lintegral_congr
      intro t
      exact (lintegral_prod _ (hm.comp (measurable_const.prodMk measurable_id)).aemeasurable).symm
    _ = _ := lintegral_indicator (measurableSet_physicalBinBase hV B hJ) _

lemma weighted_labelProjected_congr (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) (k : Fin 4→ℕ) {J : Set ℝ}
    {G H : ℝ→Vec→L[ℝ]Vec} (hGH : EqOn G H J)
    {b : ℝ→ℝ} (hbJ : ∀t∉J,b t=0) (p : ℝ×Phase) :
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k G) p‖=
    ENNReal.ofReal (b (labelReceiverTime α zX T p))*
      ENNReal.ofReal ‖labelConeKernel s α zX T (projectedDyadicRateKernel α zX T k H) p‖ := by
  classical
  by_cases hp : p∈labelBranchDomain α zX T
  · simp only [labelReceiverTime,labelConeKernel,indicator_of_mem hp]
    by_cases ht : branchTime α zX p.2 T p.1∈J
    · simp only [projectedDyadicRateKernel,labelKernelState,hGH ht]
    · simp only [hbJ _ ht,ENNReal.ofReal_zero,zero_mul]
  · simp only [labelConeKernel,indicator_of_notMem hp,norm_zero,ENNReal.ofReal_zero,mul_zero]

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
open Set MeasureTheory
open scoped ENNReal
open Set Filter MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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

lemma physicalDyadicMovingDensity_le {s : Solution} {X V K : ℝ→Vec} {T w t σ : ℝ}
    {k : Fin 4→ℕ} {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) :
    physicalDyadicMovingDensity s X V K T w k (t,σ,n) ≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (physicalMovingProjectorDensity s X V (representativeClosedBin T w k) w K) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  let χ : Vec→ℝ := fun v=>dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
  let H : Vec→ℝ := fun v=>‖s.f (σ,(X t-(t-σ) • n.1,v)) •
    angularDerivativeCLM w (V t) (K t) (signedPrimitive (velocity (V t)) (velocity v) n.1)‖
  have hp : ∀v, ENNReal.ofReal (χ v*(t-σ)*H v) ≤
      (coneBinMomentumSet B n.1 (velocity (V t))).indicator
        (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := by
    intro v
    by_cases hχ : 0<χ v
    · have hv := (physicalCutoff_positive_closedBin ht hσ hband hχ).2
      rw [indicator_of_mem hv]
      apply ENNReal.ofReal_le_ofReal
      have hm := dyadicMultiFactor_le_one k (physicalCutoffCoordinates T (t-σ) n.1 v (V t))
      have hrH : 0≤(t-σ)*H v := mul_nonneg (sub_nonneg.mpr hσt.le) (norm_nonneg _)
      have hm' := mul_le_mul_of_nonneg_right hm hrH
      dsimp [χ] at *
      nlinarith
    · have hz : χ v=0 := le_antisymm (le_of_not_gt hχ) (dyadicMultiFactor_nonneg _ _)
      simp only [hz,zero_mul,ENNReal.ofReal_zero]
      exact bot_le
  by_cases hbase : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hbase]
    calc
      _ ≤ ∫⁻v, (coneBinMomentumSet B n.1 (velocity (V t))).indicator
          (fun v=>ENNReal.ofReal ((t-σ)*H v)) v := lintegral_mono hp
      _ = ∫⁻v in coneBinMomentumSet B n.1 (velocity (V t)), ENNReal.ofReal ((t-σ)*H v) :=
        lintegral_indicator (measurableSet_coneBinMomentumSet _ _ _) _
      _ = _ := by
        simp only [H,physicalPrimitive_radius_norm (sub_pos.mpr hσt)]
        simp_rw [ENNReal.ofReal_mul (sq_nonneg (t-σ))]
        exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  · rw [indicator_of_notMem hbase]
    apply le_of_eq
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro v
    have hχ : χ v=0 := by
      apply le_antisymm _ (dyadicMultiFactor_nonneg _ _)
      exact le_of_not_gt (fun h=>hbase (physicalCutoff_positive_closedBin ht hσ hband h).1)
    change ENNReal.ofReal (χ v*(t-σ)*H v)=0
    simp only [hχ,zero_mul,ENNReal.ofReal_zero]

lemma physicalDyadicMovingDensity_near_pointwise {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V K : ℝ→Vec} {J : Set ℝ} (hJT : J⊆Icc 0 T)
    {w C p θ φ t σ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (_hC : 0≤C) (_hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (ht : t∈J) (hσ : σ∈Icc 0 t) (hσt : σ<t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (hv : w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2)) (n : Sphere) :
    physicalDyadicMovingDensity s X V K T w k (t,σ,n)≤
      (physicalBinBase V (representativeClosedBin T w k) J).indicator
        (fun z=>ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (5111808*C*(p*θ)^3*
          (representativeClosedBin T w k).rmax/(w*φ))) (t,σ,n) := by
  classical
  let B := representativeClosedBin T w k
  have h := physicalDyadicMovingDensity_le ht hσ hσt hband n (s:=s) (X:=X) (K:=K) (k:=k) (T:=T)
  by_cases hz : (t,σ,n)∈physicalBinBase V B J
  · rw [indicator_of_mem hz] at h ⊢
    have hk := physicalMovingProjectorDensity_bound (s:=s) (X:=X) (z:=(t,σ,n)) (K:=K)
      hw hv (sub_pos.mpr hσt) hθ hφ hφ1 hsmall hd (hDlo.trans hz.2.2.2.2.1)
      (hz.2.2.2.2.2.trans hDhi)
      (fun v=>hs.nonnegative σ ⟨hσ.1,hσ.2.trans (hJT ht).2⟩ _)
    have hn : 0≤B.rmax := (representativeClosedBin_radius_pos T w k).le.trans
      (hz.2.2.1.1.trans hz.2.2.1.2)
    have hden := hdensity (t,σ,n) hz
    have hrad : ENNReal.ofReal (t-σ)≤ENNReal.ofReal B.rmax :=
      ENNReal.ofReal_le_ofReal hz.2.2.1.2
    calc
      _ ≤ ENNReal.ofReal (39936*θ/(w*φ)*‖K t‖)*ENNReal.ofReal (t-σ)*
          physicalBinDensity s X V B t σ n := h.trans hk
      _ ≤ ENNReal.ofReal (39936*θ/(w*φ)*‖K t‖)*ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2) :=
        mul_le_mul' (mul_le_mul' le_rfl hrad) hden
      _ = _ := by
        rw [←ENNReal.ofReal_mul (by positivity : 0≤39936*θ/(w*φ)*‖K t‖),
          ←ENNReal.ofReal_mul (mul_nonneg (by positivity) hn),
          ←ENNReal.ofReal_mul (norm_nonneg _)]
        congr 1
        dsimp [B]
        ring
  · exact (h.trans (by rw [indicator_of_notMem hz,indicator_of_notMem hz]))

lemma physicalDyadicMoving_triangle_near {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) {X V K : ℝ→Vec} (hV : Measurable V) (hK : Measurable K)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w)) (hv : ∀t∈J,w/16≤‖V t‖)
    (hdensity : ∀z∈physicalBinBase V (representativeClosedBin T w k) J,
      physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
        ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) (hgJ : ∀t∉J,g t=0) :
    (∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
      g t*physicalDyadicMovingDensity s X V K T w k (t,σ,n) ∂sphereMeasure)≤
    (∫⁻t in J,g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
      (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
        (representativeClosedBin T w k).rmin)) := by
  classical
  let B := representativeClosedBin T w k
  let c := 5111808*C*(p*θ)^3*B.rmax/(w*φ)
  have hc : 0 ≤ c := by
    have hr : 0≤B.rmax := by
      dsimp [B,representativeClosedBin]
      have hh : 0 < cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
      positivity
    dsimp [c]
    positivity
  have hgK : Measurable (fun t=>g t*ENNReal.ofReal ‖K t‖) := hg.mul hK.norm.ennreal_ofReal
  have hm : Measurable (fun t=>(g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal c) := hgK.mul measurable_const
  calc
    _ ≤ ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        (physicalBinBase V B J).indicator (fun z : ConeCoordinate=>(g z.1*ENNReal.ofReal ‖K z.1‖)*ENNReal.ofReal c) (t,σ,n)
          ∂sphereMeasure := by
      apply setLIntegral_mono' measurableSet_Ioo
      intro t _
      apply setLIntegral_mono' measurableSet_Ioo
      intro σ hσ
      apply lintegral_mono
      intro n
      by_cases ht : t∈J
      · have hpw := mul_le_mul' (a:=g t) (b:=g t) le_rfl
          (physicalDyadicMovingDensity_near_pointwise hs hJT hw hC hp hθ hφ hφ1 hsmall
            hDlo hDhi hd ht (Ioo_subset_Icc_self hσ) hσ.2 (hband t ht) (hv t ht) hdensity n (K:=K))
        by_cases hz : (t,σ,n)∈physicalBinBase V B J
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_mem hz,mul_assoc] using hpw
        · dsimp [B] at hz
          simpa only [B,c,indicator_of_notMem hz,mul_zero] using hpw
      · simp only [hgJ t ht,zero_mul]
        exact bot_le
    _ ≤ ∫⁻z : ConeCoordinate,(g z.1*ENNReal.ofReal ‖K z.1‖)*ENNReal.ofReal c ∂physicalBinMeasure V B J :=
      physicalBin_triangle_weight_le hV B hJ T hm
    _ = (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal ‖K z.1‖ ∂physicalBinMeasure V B J)*ENNReal.ofReal c :=
      lintegral_mul_const _ (hgK.comp measurable_fst)
    _ ≤ ((∫⁻t in J,g t*ENNReal.ofReal ‖K t‖)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2))*ENNReal.ofReal c :=
      mul_le_mul' (physicalBinMeasure_receiver_weight hV B hJ hφ.le hDhi hgK) le_rfl
    _ = _ := by
      have hr : B.rmin≤B.rmax := by
        dsimp [B,representativeClosedBin]
        have hh : 0 < cappedRepresentative (k 3) := by dsimp [cappedRepresentative]; positivity
        have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
        nlinarith [mul_pos hT hh]
      rw [mul_assoc,mul_assoc,←ENNReal.ofReal_mul (by positivity : 0≤384*φ^2),
        ←ENNReal.ofReal_mul (sub_nonneg.mpr hr)]
      congr 2
      dsimp [c,B]
      field_simp
      ring

lemma projectedDyadicRateKernel_polar_moving_density (α : Phase→ℝ→Phase) (zX : Phase)
    (s : Solution) (T w : ℝ) (k : Fin 4→ℕ) (K : ℝ→Vec) {G : ℝ→Vec→L[ℝ]Vec} {t σ : ℝ}
    (hσt : σ<t) (hG : G t=angularDerivativeCLM w (α zX t).2 (K t)) (n : Sphere) :
    ENNReal.ofReal (1-dot n.1 (velocity (α zX t).2))*
      (∫⁻v : Vec,ENNReal.ofReal ‖s.f (σ,((α zX t).1-(t-σ) • n.1,v)) •
        projectedDyadicRateKernel α zX T k G ((t,σ),(n.1,((α zX t).1-(t-σ) • n.1,v)))‖)=
      physicalDyadicMovingDensity s (fun t=>(α zX t).1) (fun t=>(α zX t).2) K T w k (t,σ,n) := by
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_congr
  intro v
  rw [←ENNReal.ofReal_mul (cone_denom_pos _ _ (sphere_norm n)).le,
    projectedDyadicRateKernel_flux_norm α zX T k G hσt,hG]
  rfl

lemma PhaseFlowOn.label_moving_primitive_near {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T) (zX : Phase)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    {w C p θ φ : ℝ} {k : Fin 4→ℕ}
    (hw : 0<w) (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0<φ) (hφ1 : φ≤1) (hsmall : θ≤φ)
    (hDlo : φ^2/2≤(representativeClosedBin T w k).Dmin)
    (hDhi : (representativeClosedBin T w k).Dmax≤8*φ^2)
    (hd : (representativeClosedBin T w k).dmax≤8*θ^2)
    (hband : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hv : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (hdensity : ∀z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2)
        (representativeClosedBin T w k) J,
      physicalBinDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z.1 z.2.1 z.2.2≤
          ENNReal.ofReal (128*C*p^3*θ^2))
    {b : ℝ→ℝ} (hb : Measurable b) (hbJ : ∀t∉J,b t=0) :
    (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
      ENNReal.ofReal ‖labelConeKernel s F.flow zX T
        (projectedDyadicRateKernel F.flow zX T k
          (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
    (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
      ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
        (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
          (representativeClosedBin T w k).rmin)) := by
  let X : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).1
  let V : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let G := prefixAngularRate s F.flow T w hw zX
  have hV : Measurable V :=
    (((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd).measurable
  have hK : Measurable K := (F.continuous_prefixMomentumForce hs hT zX).measurable
  have hKe : ∀t∈Icc 0 T,K t=(lorentzField s.E s.B (t,F.flow zX t)).2 := by
    intro t ht
    simp only [K,prefixMomentumForce,prefixFlow,prefixClamp_eq ht]
  have hG : ∀t∈J,G t=angularDerivativeCLM w (F.flow zX t).2 (K t) := by
    intro t ht
    rw [hKe t (hJT ht)]
    exact (prefixAngular_highband (s:=s) hw zX (hJT ht) (hv t ht)).2
  have he : ∀t∈Icc 0 T,X t=(F.flow zX t).1 ∧ V t=(F.flow zX t).2 := by
    intro t ht
    simp only [X,V,prefixFlow,prefixClamp_eq ht,and_self]
  calc
    _ = ∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T (projectedDyadicRateKernel F.flow zX T k G) z‖ := by
      apply lintegral_congr
      intro z
      apply weighted_labelProjected_congr s F.flow zX T k _ hbJ z
      intro t ht
      rw [hG t ht,hKe t (hJT ht)]
    _ = ∫⁻t in Ioo (0:ℝ) T,∫⁻σ in Ioo (0:ℝ) t,∫⁻n : Sphere,
        ENNReal.ofReal (b t)*physicalDyadicMovingDensity s X V K T w k (t,σ,n) ∂sphereMeasure := by
      rw [F.labelConeKernel_triangle_weighted_norm hs hT zX
        (F.projectedDyadicRateKernel_continuousOn zX k (F.prefixAngular_regular hs hT hw zX).2.1) hb]
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro t ht
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      apply lintegral_congr
      intro n
      by_cases htJ : t∈J
      · rw [mul_assoc,projectedDyadicRateKernel_polar_moving_density F.flow zX s T w k K hσ.2 (hG t htJ) n]
        unfold physicalDyadicMovingDensity
        rw [(he t (Ioo_subset_Icc_self ht)).1,(he t (Ioo_subset_Icc_self ht)).2]
      · simp only [hbJ t htJ,ENNReal.ofReal_zero,zero_mul]
    _ ≤ (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (1962934272*C*(p*θ)^3*φ/w*
          (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
            (representativeClosedBin T w k).rmin)) :=
      physicalDyadicMoving_triangle_near hs hV hK hJ hJT hw hC hp hθ hφ hφ1 hsmall
        hDlo hDhi hd (fun t ht=>by rw [(he t (hJT ht)).2]; exact hband t ht)
        (fun t ht=>by rw [(he t (hJT ht)).2]; exact hv t ht) hdensity hb.ennreal_ofReal
        (fun t ht=>by rw [hbJ t ht,ENNReal.ofReal_zero])
    _ = _ := by
      congr 1
      apply setLIntegral_congr_fun hJ
      intro t ht
      dsimp only
      rw [hKe t (hJT ht)]

lemma Admissible.label_moving_primitive_near_constant_oai {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ, 0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w p θ φ : ℝ) (k : Fin 4→ℕ),
      MeasurableSet J → J⊆Icc 0 T → 0<w → 0≤p → 0≤θ → 0<φ → φ≤1 → θ≤φ →
      φ^2/2≤(representativeClosedBin T w k).Dmin →
      (representativeClosedBin T w k).Dmax≤8*φ^2 →
      (representativeClosedBin T w k).dmax≤8*θ^2 →
      (representativeClosedBin T w k).qmax≤p →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      ∀b : ℝ→ℝ,Measurable b → (∀t∉J,b t=0) →
      (∫⁻z : ℝ×Phase,ENNReal.ofReal (b (labelReceiverTime F.flow zX T z))*
        ENNReal.ofReal ‖labelConeKernel s F.flow zX T
          (projectedDyadicRateKernel F.flow zX T k
          (fun t=>angularDerivativeCLM w (F.flow zX t).2 (lorentzField s.E s.B (t,F.flow zX t)).2)) z‖)≤
      (∫⁻t in J,ENNReal.ofReal (b t)*ENNReal.ofReal ‖(lorentzField s.E s.B (t,F.flow zX t)).2‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*
          (representativeClosedBin T w k).rmax*((representativeClosedBin T w k).rmax-
            (representativeClosedBin T w k).rmin)) := by
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨1962934272*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w p θ φ k hJ hJT hw hp hθ hφ hφ1 hsmall hDlo hDhi hd hq hband hv b hbm hbJ
  apply F.label_moving_primitive_near hs hT zX hJ hJT hw hC hp hθ hφ hφ1 hsmall hDlo hDhi hd hband hv _ hbm hbJ
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.label_moving_primitive_near_constant_oai := @OAI.RVM.Admissible.label_moving_primitive_near_constant_oai
