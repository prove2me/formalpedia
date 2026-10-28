-- Prove2me | solution 1 for OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:56:38.539289+00:00
-- url     : https://prove2.me/submissions/7b61b71b-d667-4ba8-9f61-457651e73460

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffLabelCost_triangle
import Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffTriangle_boundary_sum
import Theorems.Thm_OAI_RVM_physicalReceiverCutoff_near

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

lemma dyadicCut_one {x : ℝ} (hx : x≤1) : dyadicCut x=1 := by
  simp only [dyadicCut,Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hx),sub_zero]
lemma dyadicCut_zero {x : ℝ} (hx : 2≤x) : dyadicCut x=0 := by
  rw [dyadicCut,Real.smoothTransition.one_of_one_le (by linarith),sub_self]
lemma dyadicBump_zero_left {x : ℝ} (hx : x≤1/2) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_one (by linarith),dyadicCut_one (by linarith),sub_self]
lemma dyadicBump_zero_right {x : ℝ} (hx : 2≤x) : dyadicBump x=0 := by
  rw [dyadicBump,dyadicCut_zero hx,dyadicCut_zero (by linarith),sub_self]
lemma dyadicBump_support : tsupport dyadicBump ⊆ Icc (1/2) 2 := by
  apply closure_minimal _ isClosed_Icc
  intro x hx
  constructor
  · by_contra hn
    exact hx (dyadicBump_zero_left (le_of_lt (lt_of_not_ge hn)))
  · by_contra hn
    exact hx (dyadicBump_zero_right (le_of_lt (lt_of_not_ge hn)))

lemma hasDerivAt_dyadicFactor (n : ℕ) (x : ℝ) :
    HasDerivAt (dyadicFactor n) ((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) x := by
  have hh := ((contDiff_dyadicBump.differentiable (by simp)) _).hasDerivAt.comp x
    ((hasDerivAt_id x).const_mul ((2:ℝ)^n))
  change HasDerivAt (fun y => dyadicBump ((2:ℝ)^n*y)) _ x
  simpa only [Function.comp_def,id_eq,mul_one,one_mul,mul_comm] using hh

lemma dyadicFactor_log_derivative_bound : ∃ C : ℝ, 0≤C ∧
    ∀ n : ℕ, ∀ x : ℝ, |x*deriv (dyadicFactor n) x|≤C := by
  have hd : Continuous (deriv dyadicBump) := contDiff_dyadicBump.continuous_deriv (by simp)
  have hcon : Continuous (fun x : ℝ => x*deriv dyadicBump x) := continuous_id.mul hd
  obtain ⟨C,hC⟩ := (isCompact_Icc.image hcon).isBounded.exists_norm_le
  refine ⟨max 0 C,le_max_left _ _,fun n x => ?_⟩
  rw [(hasDerivAt_dyadicFactor n x).deriv]
  have he : x*((2:ℝ)^n*deriv dyadicBump ((2:ℝ)^n*x)) =
      ((2:ℝ)^n*x)*deriv dyadicBump ((2:ℝ)^n*x) := by ring
  rw [he]
  by_cases hx : (2:ℝ)^n*x ∈ Icc (1/2:ℝ) 2
  · exact (hC _ ⟨(2:ℝ)^n*x,hx,rfl⟩).trans (le_max_right _ _)
  · rw [deriv_of_notMem_tsupport (fun h => hx (dyadicBump_support h)),mul_zero,abs_zero]
    exact le_max_left _ _

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

lemma PhaseFlowOn.momentumForce_continuousOn_closed {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (z : Phase) :
    ContinuousOn (fun t=>(lorentzField s.E s.B (t,F.flow z t)).2) (Icc 0 T) := by
  have hf := F.continuousOn_time z
  have hp : ContinuousOn (fun t => (t,(F.flow z t).1)) (Icc 0 T) := continuousOn_id.prodMk hf.fst
  have hE : ContinuousOn (fun t => s.E (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.E_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hB : ContinuousOn (fun t => s.B (t,(F.flow z t).1)) (Icc 0 T) :=
    hs.B_smooth.continuousOn.comp hp (fun t ht => ⟨ht,mem_univ _⟩)
  have hu : ContinuousOn (fun t => velocity (F.flow z t).2) (Icc 0 T) :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn hf.snd
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.prodMk hB))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffRateMajorant
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

lemma EnergyPrefix.continuousOn_momentumForce {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) :
    ContinuousOn (fun p : ℝ×Phase=>(lorentzField s.E s.B p).2)
      (Icc 0 T ×ˢ (univ : Set Phase)) := by
  have hp : Continuous (fun p : ℝ×Phase=>(p.1,p.2.1)) := continuous_fst.prodMk continuous_snd.fst
  have hE : ContinuousOn (fun p : ℝ×Phase=>s.E (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.E_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hB : ContinuousOn (fun p : ℝ×Phase=>s.B (p.1,p.2.1)) (Icc 0 T ×ˢ (univ : Set Phase)) :=
    hs.B_smooth.continuousOn.comp hp.continuousOn (fun _ hp=>⟨hp.1,mem_univ _⟩)
  have hu := (contDiff_velocity (k:=1)).continuous.comp (continuous_snd.snd : Continuous (fun p : ℝ×Phase=>p.2.2))
  exact hE.add ((contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hB))

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


lemma selected_radial_factor {x h : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) : x^3*h^2≤Real.sqrt h := by
  have hs : 0≤Real.sqrt h := Real.sqrt_nonneg h
  have hsq := Real.sq_sqrt hh
  calc
    x^3*h^2 = (x*Real.sqrt h)^3*Real.sqrt h := by
      nth_rw 1 [←hsq]
      ring
    _ ≤ 1^3*Real.sqrt h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (mul_nonneg hx hs) hsel 3) hs
    _ = _ := by norm_num

lemma selected_radial_width {x h r R : ℝ} (hx : 0≤x) (hh : 0≤h)
    (hsel : x*Real.sqrt h≤1) (_hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    x^3*R*(R-r)≤4*Real.sqrt h := by
  calc
    _ = x^3*(R*(R-r)) := by ring
    _ ≤ x^3*((2*h)*(2*h)) := mul_le_mul_of_nonneg_left
      (mul_le_mul hhi hw (sub_nonneg.mpr hwidth) (by positivity)) (by positivity)
    _ = 4*(x^3*h^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (selected_radial_factor hx hh hsel) (by norm_num)

lemma selected_moving_coefficient {C p θ φ w h r R : ℝ}
    (hC : 0≤C) (hp : 0≤p) (hθ : 0≤θ) (hφ : 0≤φ) (hw₀ : 0≤w) (hh : 0≤h)
    (hsel : p*θ*Real.sqrt h≤1) (hR : 0≤R) (hwidth : r≤R)
    (hhi : R≤2*h) (hw : R-r≤2*h) :
    C*(p*θ)^3*φ/w*R*(R-r)≤4*C*Real.sqrt h*φ/w := by
  have h := mul_le_mul_of_nonneg_left (selected_radial_width (mul_nonneg hp hθ) hh hsel hR hwidth hhi hw)
    (div_nonneg (mul_nonneg hC hφ) hw₀)
  convert h using 1 <;> first | rfl | ring

lemma radial_half_decay (n : ℕ) : Real.sqrt ((1/2:ℝ)^n)≤(3/4:ℝ)^n := by
  have hs : Real.sqrt (1/2:ℝ)≤3/4 := (Real.sqrt_le_iff).mpr (by norm_num)
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [pow_succ,Real.sqrt_mul (by positivity),pow_succ]
      exact mul_le_mul ih hs (Real.sqrt_nonneg _) (by positivity)

lemma sum_radial_half_decay (N : ℕ) : ∑n∈Finset.range N,Real.sqrt ((1/2:ℝ)^n)≤4 := by
  calc
    _ ≤ ∑n∈Finset.range N,(3/4:ℝ)^n := Finset.sum_le_sum (fun n _=>radial_half_decay n)
    _ ≤ ∑'n : ℕ,(3/4:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 4 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(3/4:ℝ)‖<1)]; norm_num

lemma sum_angular_half_decay (N : ℕ) : ∑n∈Finset.range N,(1/2:ℝ)^n≤2 := by
  calc
    _ ≤ ∑'n : ℕ,(1/2:ℝ)^n := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)).sum_le_tsum
      (Finset.range N) (fun n _=>by positivity)
    _ = 2 := by rw [tsum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖<1)]; norm_num

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_CutoffSourceTangent
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
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.receiver_cutoff_near_constant {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V K : ℝ→Vec) (B : ClosedConeBin) (J : Set ℝ) (w p θ φ : ℝ)
        (Q : Set (Fin 4→ℕ)),
      Measurable V → Measurable K → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0 ≤ p → 0 ≤ θ → 0<φ → B.dmax ≤ B.Dmin → 0<B.rmin →
      φ^2/2 ≤ B.Dmin → B.Dmax ≤ 8*φ^2 → B.dmax ≤ 8*θ^2 → B.qmax ≤ p →
      (∀t∈J,w/16 ≤ ‖V t‖) →
      (∫⁻z : ConeCoordinate,physicalReceiverCutoffDensity s X V B T w Q K z
        ∂physicalBinMeasure V B J) ≤
      (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
  obtain ⟨A,hA,hAb⟩ := dyadicFactor_log_derivative_bound
  obtain ⟨C,hC,hb⟩ := hd₀.uniform_particle_density_constant
  refine ⟨(125440000*49152)*A*C,by positivity,?_⟩
  intro s T F hs h0 X V K B J w p θ φ Q hV hK hJ hJT hw hp hθ hφ hsmall hr hDlo hDhi hd hq hband
  apply physicalReceiverCutoff_near hs hV hK B hJ hJT hA hAb hw hC hp hθ hφ hsmall hr hDlo hDhi hd hband Q
  intro z hz
  exact coneBin_density_small_bound (sphere_norm z.2.2).le hp hθ hC hq hd
    (fun v=>(hb s T F hs h0 z.2.1 ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ _).2)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

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

lemma finset_subset_dyadicBox {ι : Type*} [Fintype ι] (S : Finset (ι→ℕ)) :
    ∃M : ℕ,S⊆dyadicBox ι M := by
  classical
  obtain ⟨M,hM⟩ := (S.biUnion (fun k=>Finset.univ.image k)).exists_nat_subset_range
  refine ⟨M,?_⟩
  intro k hk
  simp only [dyadicBox,Fintype.mem_piFinset]
  intro i
  apply hM
  exact Finset.mem_biUnion.mpr ⟨k,hk,Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

lemma directionWeightMajorant_nonneg (N : ℕ) (k : Fin 4→ℕ) :
    0≤directionWeightMajorant N k := by
  unfold directionWeightMajorant
  positivity

lemma sum_range_indicator_lt (M N : ℕ) :
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)≤N := by
  classical
  rw [Finset.sum_boole,Nat.cast_le]
  have h : (Finset.range M).filter (fun i=>i<N)⊆Finset.range N := by
    intro i hi
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
  simpa only [Finset.card_range] using Finset.card_le_card h

lemma sum_directionWeightMajorant_box (M N : ℕ) :
    ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  classical
  let g : Fin 4→ℕ→ℝ := ![fun i=>if i<N then 1 else 0,
    fun i=>if i<N then 1 else 0,fun i=>(1/2:ℝ)^i,fun i=>Real.sqrt ((1/2:ℝ)^i)]
  have he : ∑k∈dyadicBox (Fin 4) M,directionWeightMajorant N k=
      ∏j,∑i∈Finset.range M,g j i := by
    have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
        (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
    have hh := Finset.sum_prod_piFinset (Finset.range M) g
    rw [heq] at hh
    simpa [dyadicBox,Fin.prod_univ_four,directionWeightMajorant,g] using hh
  rw [he,Fin.prod_univ_four]
  change (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,if i<N then (1:ℝ) else 0)*
    (∑i∈Finset.range M,(1/2:ℝ)^i)*(∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i))≤_
  have hN : 0≤(∑i∈Finset.range M,if i<N then (1:ℝ) else 0) :=
    Finset.sum_nonneg (fun i _=>by positivity)
  have ha : 0≤∑i∈Finset.range M,(1/2:ℝ)^i := Finset.sum_nonneg (fun i _=>by positivity)
  have hs : 0≤∑i∈Finset.range M,Real.sqrt ((1/2:ℝ)^i) := Finset.sum_nonneg (fun i _=>by positivity)
  have h := mul_le_mul
    (mul_le_mul (mul_le_mul (sum_range_indicator_lt M N) (sum_range_indicator_lt M N) hN (by positivity))
      (sum_angular_half_decay M) ha (by positivity))
    (sum_radial_half_decay M) hs (by positivity)
  exact h.trans_eq (by ring)

lemma sum_directionWeightMajorant (S : Finset (Fin 4→ℕ)) (N : ℕ) :
    ∑k∈S,directionWeightMajorant N k≤8*(N:ℝ)^2 := by
  obtain ⟨M,hM⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hM
    (fun k _ _=>directionWeightMajorant_nonneg N k)).trans (sum_directionWeightMajorant_box M N)

lemma tsum_directionWeightMajorant (N : ℕ) :
    (∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k))≤ENNReal.ofReal (8*(N:ℝ)^2) := by
  have hs : Summable (directionWeightMajorant N) :=
    summable_of_sum_le (directionWeightMajorant_nonneg N) (fun S=>sum_directionWeightMajorant S N)
  rw [←ENNReal.ofReal_tsum_of_nonneg (directionWeightMajorant_nonneg N) hs]
  exact ENNReal.ofReal_le_ofReal (hs.tsum_le_of_sum_le (fun S=>sum_directionWeightMajorant S N))

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

namespace RVM

lemma sourceRepresentative_le_four {a b : ℕ} (h : a ≤ b+2) :
    sourceRepresentative a ≤ 4*sourceRepresentative b := by
  have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
  dsimp only [sourceRepresentative]
  calc
    64*(2:ℝ)^a ≤ 64*(2:ℝ)^(b+2) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by rw [pow_add]; ring

lemma cappedRepresentative_le_four {a b : ℕ} (h : b ≤ a+2) :
    cappedRepresentative a ≤ 4*cappedRepresentative b := by
  have hp := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 2⁻¹) (by norm_num : (2:ℝ)⁻¹ ≤ 1) h
  dsimp only [cappedRepresentative]
  rw [pow_add] at hp
  norm_num at hp
  nlinarith

lemma dyadicSelectionBoundary_direction {T κ : ℝ} (hκ : 0 ≤ κ)
    {Q : Set (Fin 4→ℕ)}
    (hQ : ∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
      sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1)
    {k : Fin 4→ℕ} (hk : k∈dyadicSelectionBoundary Q) :
    cappedRepresentative (k 1) ≤ 16*κ*cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 32 := by
  obtain ⟨⟨j,hj,hnear⟩,_⟩ := hk
  have hT : 0 ≤ max (1:ℝ) T := le_trans (by norm_num) (le_max_left _ _)
  have hc (i : Fin 4) : 0 < cappedRepresentative (j i) := by dsimp [cappedRepresentative]; positivity
  have hp : 0 < sourceRepresentative (j 0) := by dsimp [sourceRepresentative]; positivity
  have hφ := cappedRepresentative_le_four (hnear 2).2
  have hθ := cappedRepresentative_le_four (hnear 1).1
  have hr := cappedRepresentative_le_four (hnear 3).1
  have hq := sourceRepresentative_le_four (hnear 0).2
  have hsqrt : Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤
      2*Real.sqrt (max 1 T*cappedRepresentative (j 3)) := by
    calc
      _ ≤ Real.sqrt (max 1 T*(4*cappedRepresentative (j 3))) :=
        Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hr hT)
      _ = _ := by
        rw [show max 1 T*(4*cappedRepresentative (j 3))=4*(max 1 T*cappedRepresentative (j 3)) by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 4)]
        norm_num
  constructor
  · calc
      _ ≤ 4*cappedRepresentative (j 1) := hθ
      _ ≤ 4*(κ*cappedRepresentative (j 2)) := mul_le_mul_of_nonneg_left (hQ j hj).1 (by norm_num)
      _ ≤ 4*(κ*(4*cappedRepresentative (k 2))) := by gcongr
      _ = _ := by ring
  · have hkc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hkp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    calc
      _ ≤ (4*sourceRepresentative (j 0))*(4*cappedRepresentative (j 1))*
          (2*Real.sqrt (max 1 T*cappedRepresentative (j 3))) :=
          mul_le_mul (mul_le_mul hq hθ (hkc 1).le (by positivity)) hsqrt
            (Real.sqrt_nonneg _) (mul_nonneg (by positivity) (mul_nonneg (by norm_num) (hc 1).le))
      _ = 32*(sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))) := by ring
      _ ≤ 32*1 := mul_le_mul_of_nonneg_left (hQ j hj).2 (by norm_num)
      _ = _ := by norm_num

lemma representativeClosedBin_small_of_angle {T w : ℝ} {k : Fin 4→ℕ}
    (h : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/4) :
    (representativeClosedBin T w k).dmax ≤ (representativeClosedBin T w k).Dmin := by
  have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  dsimp only [representativeClosedBin]
  nlinarith [mul_self_le_mul_self (hc 1).le h]

lemma dyadicSelectionBoundary_small {T w κ : ℝ} (hκ : 0 ≤ κ) (hκsmall : κ ≤ 1/64)
    {Q : Set (Fin 4→ℕ)}
    (hQ : ∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
      sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1)
    {k : Fin 4→ℕ} (hk : k∈dyadicSelectionBoundary Q) :
    (representativeClosedBin T w k).dmax ≤ (representativeClosedBin T w k).Dmin := by
  have h := (dyadicSelectionBoundary_direction hκ hQ hk).1
  apply representativeClosedBin_small_of_angle
  have hc : 0 < cappedRepresentative (k 2) := by dsimp [cappedRepresentative]; positivity
  nlinarith [mul_le_mul_of_nonneg_right hκsmall hc.le]

lemma relaxed_representative_moving_bound {T C w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0 ≤ C) (hw : 0 ≤ w) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 32) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin) ≤
      (131072*C*Real.sqrt (max 1 T)/w)*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hsel' : (sourceRepresentative (k 0)/32)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3)) ≤ 1 := by nlinarith
  have hb := selected_moving_coefficient (C:=32768*C) (by positivity)
    (p:=sourceRepresentative (k 0)/32) (by positivity) (hc 1).le (hc 2).le hw
    (mul_nonneg hT.le (hc 3).le) hsel'
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (by exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  calc
    _ = (32768*C)*((sourceRepresentative (k 0)/32)*cappedRepresentative (k 1))^3*
        cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
        ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin) := by ring
    _ ≤ 4*(32768*C)*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)/w := hb
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

lemma Admissible.receiver_cutoff_boundary_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0 ≤ C ∧ ∀(s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(X V K : ℝ→Vec) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      Measurable V → Measurable K → MeasurableSet J → J⊆Icc 0 T →
      0<w → 0 ≤ κ → κ ≤ 1/64 →
      (∀j∈Q,cappedRepresentative (j 1) ≤ κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤ 1) →
      (∀t∈J,w/16 ≤ ‖V t‖) →
      (∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator
        (receiverBoundaryBinCost s X V K T w J Q) k) ≤
      (∫⁻t in J,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hnear⟩ := hd₀.receiver_cutoff_near_constant
  refine ⟨1048576*C,by positivity,?_⟩
  intro s T F hs h0 X V K J w κ N Q hV hK hJ hJT hw hκ hκsm hQ hband
  let W := ∫⁻t in J,ENNReal.ofReal ‖K t‖
  have hb (k : Fin 4→ℕ) (hk : k∈dyadicSelectionBoundary Q) (hk0 : k 0<N) (hk1 : k 1<N) :
      receiverBoundaryBinCost s X V K T w J Q k ≤
        W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (directionWeightMajorant N k)) := by
    have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
    have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
    have hn := hnear s T F hs h0 X V K (representativeClosedBin T w k) J w
      (sourceRepresentative (k 0)) (cappedRepresentative (k 1)) (cappedRepresentative (k 2)) Q
      hV hK hJ hJT hw hp.le (hc 1).le (hc 2)
      (dyadicSelectionBoundary_small hκ hκsm hQ hk) (representativeClosedBin_radius_pos T w k)
      le_rfl le_rfl le_rfl (by change sourceRepresentative (k 0)/32 ≤ sourceRepresentative (k 0); linarith) hband
    refine hn.trans (mul_le_mul' (a:=W) (b:=W) le_rfl ?_)
    rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 131072*C*Real.sqrt (max 1 T)/w)]
    exact ENNReal.ofReal_le_ofReal (relaxed_representative_moving_bound hC hw.le hk0 hk1
      (dyadicSelectionBoundary_direction hκ hQ hk).2)
  calc
    _ ≤ ∑'k : Fin 4→ℕ,W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*
        ENNReal.ofReal (directionWeightMajorant N k)) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
      · simpa only [indicator_of_mem hk] using hb k hk.1 hk.2.1 hk.2.2
      · rw [indicator_of_notMem hk]
        exact bot_le
    _ = W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*
        ∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k)) := by
      rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ W*(ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      mul_le_mul' (a:=W) (b:=W) le_rfl (mul_le_mul' (a:=ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w))
        (b:=ENNReal.ofReal (131072*C*Real.sqrt (max 1 T)/w)) le_rfl (tsum_directionWeightMajorant N))
    _ = _ := by
      rw [←ENNReal.ofReal_mul (by positivity : 0 ≤ 131072*C*Real.sqrt (max 1 T)/w)]
      congr 2
      ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeKernelInterior
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

lemma PhaseFlowOn.coneCutoffRate_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneCutoffRate s F.flow zX) (coneKernelInterior T) := by
  let S := coneKernelInterior T
  have ha : ContinuousOn (fun p : ConeKernelState=>velocity (F.flow zX p.1.1).2) S :=
    (contDiff_velocity (k:=1)).continuous.comp_continuousOn
      (((F.continuousOn_time zX).comp continuous_fst.fst.continuousOn (fun _ hp=>hp.1.1.1)).snd)
  have hu : ContinuousOn (fun p : ConeKernelState=>velocity p.2.2.2) S :=
    ((contDiff_velocity (k:=1)).continuous.comp continuous_snd.snd.snd).continuousOn
  have hn : ContinuousOn (fun p : ConeKernelState=>p.2.1) S := continuous_snd.fst.continuousOn
  have hD : ∀p∈S,1-dot p.2.1 (velocity (F.flow zX p.1.1).2)≠0 := fun p hp=>
    (cone_denom_pos _ _ (by simpa only [mem_sphere,dist_zero_right] using hp.1.2.1)).ne'
  have hρ : ContinuousOn (fun p : ConeKernelState=>
      (1-dot p.2.1 (velocity p.2.2.2))/(1-dot p.2.1 (velocity (F.flow zX p.1.1).2))) S := by
    simp only [dot_eq_inner] at hD ⊢
    exact (continuousOn_const.sub (hn.inner hu)).div (continuousOn_const.sub (hn.inner ha)) hD
  have hN := (hρ.smul (ha.sub hn)).add hn |>.sub hu
  have hr := (continuous_fst.fst.sub continuous_fst.snd).continuousOn.inv₀
    (show ∀p∈S,p.1.1-p.1.2≠0 from fun _ hp=>(sub_pos.mpr hp.2).ne')
  have hKY : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.2,p.2.2)).2) S :=
    hs.continuousOn_momentumForce.comp (continuous_fst.snd.prodMk continuous_snd.snd).continuousOn
      (fun _ hp=>⟨hp.1.1.2,mem_univ _⟩)
  have hKX : ContinuousOn (fun p : ConeKernelState=>(lorentzField s.E s.B (p.1.1,F.flow zX p.1.1)).2) S :=
    (F.momentumForce_continuousOn_closed hs zX).comp continuous_fst.fst.continuousOn
      (fun _ hp=>hp.1.1.1)
  exact (hρ.sub continuousOn_const).prodMk ((hr.smul hN).prodMk (hKY.prodMk (hρ.smul hKX)))

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_IndexTwoPow
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

open Set

namespace RVM

lemma exists_dyadic_count_log {B : ℝ} (hB : 1 ≤ B) :
    ∃N : ℕ, B < (2:ℝ)^N ∧ (N:ℝ) ≤ 2+Real.log B/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h0 : 0 ≤ Real.log B/Real.log 2 := div_nonneg (Real.log_nonneg hB) h2.le
  let n := ⌈Real.log B/Real.log 2⌉₊
  refine ⟨n+1,?_,?_⟩
  · apply (Real.log_lt_log_iff (zero_lt_one.trans_le hB) (by positivity)).mp
    rw [Real.log_pow,Nat.cast_add,Nat.cast_one]
    have hc : Real.log B/Real.log 2 < (n:ℝ)+1 := by
      have hh := Nat.le_ceil (Real.log B/Real.log 2)
      dsimp [n]
      linarith only [hh]
    exact (div_lt_iff₀ h2).mp hc
  · have hh : (n:ℝ) < Real.log B/Real.log 2+1 := Nat.ceil_lt_add_one h0
    push_cast
    linarith only [hh]

lemma exists_far_dyadic_count (T : ℝ) :
    ∃C : ℝ, 0 ≤ C ∧ ∀P : ℝ, 0 < P → 1 ≤ Real.log (2+P) →
      ∃N : ℕ, 2*P < (2:ℝ)^N ∧
        4096*P*Real.sqrt (max 1 T) < (2:ℝ)^N ∧
        (4096*P)^2*max 1 T < (2:ℝ)^N ∧
        (N:ℝ) ≤ C*Real.log (2+P) := by
  let H := max 1 T
  let D := 16777216*H
  let C := 2+Real.log D/Real.log 2+2/Real.log 2
  have hH1 : 1 ≤ H := le_max_left _ _
  have hH : 0 < H := zero_lt_one.trans_le hH1
  have hD1 : 1 ≤ D := by dsimp [D]; linarith only [hH1]
  have hD : 0 < D := zero_lt_one.trans_le hD1
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD : 0 ≤ Real.log D := Real.log_nonneg hD1
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro P hP hL
  let B := D*(2+P)^2
  have hB1 : 1 ≤ B := by
    have hs : 1 ≤ (2+P)^2 := by nlinarith only [hP,sq_nonneg P]
    simpa only [one_mul] using (mul_le_mul hD1 hs (by norm_num) hD.le : (1:ℝ)*1 ≤ D*(2+P)^2)
  obtain ⟨N,hN,hNc⟩ := exists_dyadic_count_log hB1
  refine ⟨N,?_,?_,?_,?_⟩
  · have hh : 2*P < D*(2+P)^2 := by
      have hd : (2:ℝ) ≤ D := by dsimp [D]; linarith only [hH1]
      have hx : 2*(2+P)^2 ≤ D*(2+P)^2 := mul_le_mul_of_nonneg_right hd (sq_nonneg _)
      nlinarith only [hx,hP,sq_nonneg P]
    exact hh.trans hN
  · have hsH : 1 ≤ Real.sqrt H := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hH1
    have hsqH : (Real.sqrt H)^2=H := Real.sq_sqrt hH.le
    have hterm : 4096*P*Real.sqrt H < D*(2+P)^2 := by
      have hx : 0 ≤ P*(Real.sqrt H)*(Real.sqrt H-1) := mul_nonneg (mul_nonneg hP.le (Real.sqrt_nonneg _)) (sub_nonneg.mpr hsH)
      have hy : 0 ≤ H*P^2 := mul_nonneg hH.le (sq_nonneg _)
      dsimp [D]
      nlinarith only [hx,hy,hsqH,hH1,hP,mul_pos hP hH]
    exact hterm.trans hN
  · have hterm : (4096*P)^2*H < D*(2+P)^2 := by
      have hh : P^2 < (2+P)^2 := by nlinarith only [hP]
      have hm := mul_lt_mul_of_pos_left hh (show 0 < 16777216*H by positivity)
      dsimp [D]
      nlinarith only [hm]
    exact hterm.trans hN
  · have hlog : Real.log B=Real.log D+2*Real.log (2+P) := by
      dsimp [B]
      rw [Real.log_mul (ne_of_gt hD) (ne_of_gt (sq_pos_of_pos (by linarith only [hP]))),Real.log_pow]
      norm_num
    rw [hlog] at hNc
    apply hNc.trans
    have hcoeff : 0 ≤ 2+Real.log D/Real.log 2 := by positivity
    have hh := mul_le_mul_of_nonneg_left hL hcoeff
    dsimp [C]
    calc
      _ = (2+Real.log D/Real.log 2)+(2/Real.log 2)*Real.log (2+P) := by ring
      _ ≤ (2+Real.log D/Real.log 2)*Real.log (2+P)+(2/Real.log 2)*Real.log (2+P) := by linarith only [hh]
      _ = _ := by ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PhysicalBinPhaseSet
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

lemma partialCutoffTriangle_of_mem {s : Solution} {α : Phase→ℝ→Phase} {zX : Phase} {T : ℝ}
    {Q : Set (Fin 4→ℕ)} {H : ConeKernelState→CutoffState} {W : ℝ→Vec→L[ℝ]Vec}
    {J : Set ℝ} {p : TrianglePhase} (ht : p.1.1∈J) :
    partialCutoffTriangle s α zX T Q H W J p =
      W p.1.1 (triangleConeKernel s α zX T (normalisedPartialCutoff α zX T Q H) p) :=
  indicator_of_mem (show p∈{p : TrianglePhase | p.1.1∈J} from ht) _

lemma normalised_partial_kernel_eq {r f D l : ℝ} {a u n : Vec}
    (hr : r≠0) (hd : 1-dot n u≠0) (W : Vec→L[ℝ]Vec) :
    W (D • (f • (l • normalisedPrimitive r a u n)))=
      r^2 • ((f*D/(r*(1-dot n u))*l) • W (signedPrimitive a u n)) := by
  simp only [normalisedPrimitive,map_smul,smul_smul]
  congr 1
  field_simp

lemma PhaseFlowOn.coneReceiverCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneReceiverCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk (continuousOn_const.prodMk
    (F.coneCutoffRate_continuousOn hs zX).snd.snd.snd))

lemma PhaseFlowOn.partialCutoffTriangle_receiver_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalReceiverCutoffDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w Q (prefixMomentumForce s F.flow T zX) z := by
  classical
  unfold physicalReceiverCutoffDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have htime := hJT hz.1
    have hprefix : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have hK : prefixMomentumForce s F.flow T zX z.1=
        (lorentzField s.E s.B (z.1,F.flow zX z.1)).2 := by
      simp only [prefixMomentumForce,hprefix,prefixClamp_eq htime]
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (angularMultiplierCLM w (F.flow zX z.1).2)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
          (lorentzField s.E s.B (z.1,F.flow zX z.1)).2))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : partialCutoffTriangle s F.flow zX T Q (coneReceiverCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffReceiverTangent ((1-dot z.2.2.1 (velocity v))/(1-dot z.2.2.1 (velocity (F.flow zX z.1).2)))
              (lorentzField s.E s.B (z.1,F.flow zX z.1)).2)) •
        angularMultiplierCLM w (F.flow zX z.1).2 (signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) := by
      simpa only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_mem hp,
        (prefixAngular_highband hw zX htime (hband _ hz.1)).1,normalisedPartialCutoff,
        coneReceiverCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffReceiverTangent] using he
    rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _),hprefix,hK]
  · simp only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_notMem hp,map_zero,
      norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma Admissible.actual_receiverCutoff_triangle_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0≤κ → κ≤1/64 →
      (∀j∈Q,cappedRepresentative (j 1)≤κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))≤1) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) →
      (∫⁻p,ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q
        (coneReceiverCutoffTangent s F.flow zX) (prefixAngularMultiplier s F.flow T w hw zX) J p‖
        ∂trianglePhaseMeasure)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨C,hC,hbound⟩ := hd₀.receiver_cutoff_boundary_sum
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP
  let X : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).1
  let V : ℝ→Vec := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  have hα : Continuous (prefixFlow F.flow T zX) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hV : Measurable V := hα.snd.measurable
  have hK : Measurable K := (F.continuous_prefixMomentumForce hs hT zX).measurable
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  have hmain := F.partialCutoffTriangle_boundary_sum hs hT zX Q
    (F.coneReceiverCutoffTangent_continuousOn hs zX) hW hJ hJT hq N hP
  apply hmain.trans
  apply le_trans _ (hbound s T F hs h0 X V K J w κ N Q hV hK hJ hJT hw hκ hκsmall hQ (fun t ht=>by
    simpa only [V,prefixFlow,prefixClamp_eq (hJT ht)] using hband t ht))
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
  · simp only [indicator_of_mem hk]
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.partialCutoffTriangle_receiver_density_le hw zX Q hJT hband _ hz
  · simp only [indicator_of_notMem hk]
    exact le_rfl

lemma coneReceiverCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneReceiverCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffReceiverTangent (branchRate α zX p.2 T p.1)
        (lorentzField s.E s.B (branchTime α zX p.2 T p.1,α zX (branchTime α zX p.2 T p.1))).2 := by
  rfl

lemma Admissible.actual_receiverCutoff_label_bound {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w κ : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0≤κ → κ≤1/64 →
      (∀j∈Q,cappedRepresentative (j 1)≤κ*cappedRepresentative (j 2) ∧
        sourceRepresentative (j 0)*cappedRepresentative (j 1)*
          Real.sqrt (max 1 T*cappedRepresentative (j 3))≤1) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T Q
          (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
            (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.actual_receiverCutoff_triangle_bound
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP
  have he := F.partialCutoffLabelCost_triangle hs hT zX Q
    (F.coneReceiverCutoffTangent_continuousOn hs zX)
    (F.prefixAngular_regular hs hT hw zX).1.measurable hJ
  rw [coneReceiverCutoffTangent_pullback] at he
  rw [he]
  exact hbound s T F hs h0 hT zX J w κ N Q hw hJ hJT hκ hκsmall hQ hq hband hP

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

lemma PhaseFlowOn.eulerian_supported_momentum {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    {r : ℝ} (hr : r∈Icc 0 T) (x v : Vec) (hf : s.f (r,(x,v))≠0) : q v≤P := by
  have hf0 : s.f (0,inversePhase F.flow (r,(x,v)))≠0 := by
    rwa [←F.transport_inverse hs.f_smooth hs.vlasov hr]
  have hh := hP (inversePhase F.flow (r,(x,v))) hf0 r hr
  simpa only [F.flow_inversePhase hr] using hh

lemma exists_source_dyadic_count : ∃C : ℝ,0≤C ∧ ∀P : ℝ,
    0<P → 1≤Real.log (2+P) → ∃N : ℕ,1024*P≤(2:ℝ)^N ∧ (N:ℝ)≤C*Real.log (2+P) := by
  obtain ⟨C,hC,hcount⟩ := exists_far_dyadic_count 0
  refine ⟨C,hC,?_⟩
  intro P hP hL
  obtain ⟨N,_hN0,hN1,_hN3,hNc⟩ := hcount P hP hL
  refine ⟨N,?_,hNc⟩
  norm_num at hN1
  linarith only [hN1,hP]

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
open scoped ENNReal Topology ContDiff

namespace RVM

lemma Admissible.direction_receiverCutoff_label_log_bound_oai {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀z,s.f (0,z)=d.f₀ z) → 0≤T →
      ∀(zX : Phase) (J : Set ℝ) (w P : ℝ) (hw : 0<w),
      MeasurableSet J → J⊆Icc 0 T → 0<P → 1≤Real.log (2+P) →
      (∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffReceiverTangent (branchRate F.flow zX p.2 T p.1)
            (lorentzField s.E s.B (branchTime F.flow zX p.2 T p.1,F.flow zX (branchTime F.flow zX p.2 T p.1))).2) p)‖)≤
      (∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.actual_receiverCutoff_label_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  refine ⟨C*Cn^2,by positivity,?_⟩
  intro s T F hs h0 hT zX J w P hw hJ hJT hP hL hq hW hsource
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  have hEuler (σ : ℝ) (hσ : σ∈Icc 0 T) (z : Phase) (hf : s.f (σ,z)≠0) :
      1024*q z.2≤(2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (F.eulerian_supported_momentum hs hsource hσ z.1 z.2 hf)
      (by norm_num : (0:ℝ)≤1024)).trans hN
  apply (hbound s T F hs h0 hT zX J w (1/1024) N (directionSelection T) hw hJ hJT
    (by norm_num) (by norm_num) (fun k hk=>hk) hq hW hEuler).trans
  apply mul_le_mul' le_rfl
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ C*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2/w := by gcongr
    _ = _ := by ring

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound_oai := @OAI.RVM.Admissible.direction_receiverCutoff_label_log_bound_oai
