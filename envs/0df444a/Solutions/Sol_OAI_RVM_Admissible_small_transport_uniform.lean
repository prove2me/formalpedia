-- Prove2me | solution 1 for OAI.RVM.Admissible.small_transport_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:22:47.058255+00:00
-- url     : https://prove2.me/submissions/0e249573-1fb0-45dd-bb4f-d92e4bef769c

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_small_transport_regular_uniform

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
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
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

lemma dot_add_left (a b c : Vec) : dot (a + b) c = dot a c + dot b c := by
  simp [dot, add_mul, Finset.sum_add_distrib]

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

lemma dot_add_right (a b c : Vec) : dot a (b + c) = dot a b + dot a c := by
  rw [dot_comm, dot_add_left, dot_comm b a, dot_comm c a]

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

lemma velocity_self (v : Vec) : dot (velocity v) (velocity v) = 1 - (q v)⁻¹ ^ 2 := by
  rw [velocity, dot_smul_left, dot_smul_right, dot_self]
  have hq := q_sq v
  have hn := ne_of_gt (q_pos v)
  field_simp
  nlinarith

lemma cone_angle_identity (v n : Vec) (hn : ‖n‖ = 1) :
    2 * (1 - dot n (velocity v)) = ‖n - velocity v‖ ^ 2 + (q v)⁻¹ ^ 2 := by
  rw [norm_sub_sq_real, ← dot_eq_inner, hn, ← dot_self (velocity v), velocity_self]
  ring

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

lemma coneBinMomentumSet_subset_cap {B : ClosedConeBin} {n a : Vec} {P θ σ : ℝ}
    (hn : ‖n‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2) (he : B.emax ≤ 8*σ^2) :
    (coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-n‖ ≤ 4*θ}) ∧
    (coneBinMomentumSet B n a⊆{v | q v ≤ P ∧ ‖velocity v-a‖ ≤ 4*σ}) := by
  have hcap (v b : Vec) (hb : ‖b‖ ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
      (hv : 1-dot b (velocity v) ≤ 8*δ^2) : ‖velocity v-b‖ ≤ 4*δ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le hb (by positivity)
    rw [dot_comm]
    nlinarith
  constructor
  · intro v hv
    exact ⟨hv.1.2.trans hq,hcap v n hn θ hθ (hv.2.1.2.trans hd)⟩
  · intro v hv
    exact ⟨hv.1.2.trans hq,hcap v a ha σ hσ (hv.2.2.2.trans he)⟩

lemma coneBin_density_bound {B : ClosedConeBin} {n a : Vec} {P θ σ C : ℝ}
    (hn : ‖n‖ ≤ 1) (ha : ‖a‖ ≤ 1) (hP : 0 ≤ P) (hθ : 0 ≤ θ) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hq : B.qmax ≤ P) (hd : B.dmax ≤ 8*θ^2) (he : B.emax ≤ 8*σ^2)
    {g : Vec → ℝ} (hg : ∀ v, g v ≤ C) :
    (∫⁻ v in coneBinMomentumSet B n a, ENNReal.ofReal (g v))  ≤
      ENNReal.ofReal (128*C*P^3*(min θ σ)^2) := by
  have hh := coneBinMomentumSet_subset_cap hn ha hθ hσ hq hd he
  rcases le_total θ σ with h|h
  · rw [min_eq_left h]
    convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*θ) hC n hg hh.1 using 1
    all_goals try with_reducible_and_instances rfl
    congr 1
    ring
  · rw [min_eq_right h]
    convert lintegral_velocity_cap_density hP (by positivity : 0 ≤ 4*σ) hC a hg hh.2 using 1
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

lemma physicalBinMeasure_volume {V : ℝ → Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {φ : ℝ}
    (hφ : 0 ≤ φ) (hD : B.Dmax ≤ 8*φ^2) :
    physicalBinMeasure V B J univ ≤
      volume J * ENNReal.ofReal (B.rmax-B.rmin) * ENNReal.ofReal (384*φ^2) := by
  let A : Set ConeCoordinate := {z | z.1 ∈ J ∧
    z.2.1 ∈ Icc (z.1-B.rmax) (z.1-B.rmin) ∧
    ‖z.2.2.1-velocity (V z.1)‖ ≤ 4*φ}
  have hA : MeasurableSet A := by
    exact (hJ.preimage measurable_fst).inter
      (((measurableSet_le (measurable_fst.sub_const _) (measurable_fst.comp measurable_snd)).inter
        (measurableSet_le (measurable_fst.comp measurable_snd) (measurable_fst.sub_const _))).inter
      (measurableSet_le (((measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)).sub
        ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst))).norm) measurable_const))
  have hsub : physicalBinBase V B J ⊆ A := by
    intro z hz
    refine ⟨hz.1,⟨by linarith [hz.2.2.1.2],by linarith [hz.2.2.1.1]⟩,?_⟩
    apply norm_sub_le_of_deficit (sphere_norm z.2.2).le (norm_velocity_lt_one _).le (by positivity)
    nlinarith [hz.2.2.2.2.2]
  have hmass : (volume.prod (volume.prod sphereMeasure)) A = ∫⁻ t in J,
      ENNReal.ofReal (B.rmax-B.rmin) * sphereMeasure {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ} := by
    rw [← lintegral_indicator_one hA,lintegral_prod _ (measurable_one.indicator hA).aemeasurable]
    rw [← lintegral_indicator hJ]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ J
    · rw [indicator_of_mem ht]
      have he : (fun p : ℝ × Sphere => A.indicator (fun _ => (1:ℝ≥0∞)) (t,p)) =
          ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}).indicator (fun _ => 1) := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻ p : ℝ × Sphere, A.indicator (fun _ => (1:ℝ≥0∞)) (t,p) ∂(volume.prod sphereMeasure)) = _
      rw [he]
      have hS : MeasurableSet ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ
          {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}) :=
        measurableSet_Icc.prod (measurableSet_le
          ((continuous_subtype_val.sub continuous_const).norm.measurable) measurable_const)
      have hsi := lintegral_indicator_one (μ := volume.prod sphereMeasure) hS
      calc
        _ = (volume.prod sphereMeasure) ((Icc (t-B.rmax) (t-B.rmin)) ×ˢ
            {n : Sphere | ‖n.1-velocity (V t)‖ ≤ 4*φ}) := hsi
        _ = _ := by
          rw [Measure.prod_prod,Real.volume_Icc]
          congr 2
          ring
    · rw [indicator_of_notMem ht]
      have he : (fun p : ℝ × Sphere => A.indicator (fun _ => (1:ℝ≥0∞)) (t,p))=0 := by
        funext p
        simp [A,ht,indicator]
      change (∫⁻ p : ℝ × Sphere, A.indicator (fun _ => (1:ℝ≥0∞)) (t,p) ∂(volume.prod sphereMeasure)) = _
      rw [he]
      change (∫⁻ _ : ℝ × Sphere, (0:ℝ≥0∞) ∂(volume.prod sphereMeasure)) = 0
      exact lintegral_zero
  unfold physicalBinMeasure
  rw [Measure.restrict_apply_univ]
  calc
    _ ≤ (volume.prod (volume.prod sphereMeasure)) A := measure_mono hsub
    _ = _ := hmass
    _ ≤ ∫⁻ _t in J, ENNReal.ofReal (B.rmax-B.rmin) * ENNReal.ofReal (384*φ^2) := by
      apply lintegral_mono
      intro t
      apply mul_le_mul' le_rfl
      convert sphere_cap_area (by positivity : 0 ≤ 4*φ) (velocity (V t)) using 1
      all_goals try with_reducible_and_instances rfl
      congr 1
      ring
    _ = _ := by rw [lintegral_const,Measure.restrict_apply_univ]; ac_rfl

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

lemma velocity_normal_distance_bound (v n : Vec) (hn : ‖n‖=1) :
    ‖velocity v-n‖ ≤ Real.sqrt (2*(1-dot n (velocity v))) := by
  have hi := cone_angle_identity v n hn
  rw [norm_sub_rev] at hi
  have hd := (cone_denom_pos v n hn).le
  have hh := Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hd)
  nlinarith [sq_nonneg ((q v)⁻¹), Real.sqrt_nonneg (2*(1-dot n (velocity v))),
    norm_nonneg (velocity v-n)]

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

lemma receiverQ_add (a n h k : Vec) : receiverQ a n (h+k)=receiverQ a n h+receiverQ a n k := by
  simp only [receiverQ,dot_add_right,smul_add,add_smul]
  module

lemma receiverQ_smul (a n h : Vec) (c : ℝ) : receiverQ a n (c • h)=c • receiverQ a n h := by
  simp only [receiverQ,dot_smul_right,smul_add,smul_smul]
  module

lemma receiverQ_normal (a n : Vec) : receiverQ a n n=n := by
  rw [receiverQ,dot_comm a n,← add_smul]
  simp

lemma cone_denom_le_two (v n : Vec) (hn : ‖n‖=1) : 1-dot n (velocity v)≤2 := by
  have h := abs_dot_le n (velocity v)
  rw [hn,one_mul] at h
  have h' := (neg_le_abs (dot n (velocity v))).trans h
  linarith [norm_velocity_lt_one v]

lemma receiverQ_tangent_bound (w n h : Vec) (hn : ‖n‖=1) (hh : dot n h=0) :
    ‖receiverQ (velocity w) n h‖≤2*Real.sqrt (2*(1-dot n (velocity w)))*‖h‖ := by
  let D := 1-dot n (velocity w)
  have hD : 0≤D := (cone_denom_pos w n hn).le
  have hD2 : D≤2 := cone_denom_le_two w n hn
  have hDs : D≤Real.sqrt (2*D) := by
    nlinarith [Real.sq_sqrt (mul_nonneg (by norm_num : (0:ℝ)≤2) hD),Real.sqrt_nonneg (2*D)]
  have ha : |dot (velocity w) h|≤Real.sqrt (2*D)*‖h‖ := by
    rw [show dot (velocity w) h=dot (velocity w-n) h by rw [dot_sub_left,hh,sub_zero]]
    exact (abs_dot_le _ _).trans (mul_le_mul_of_nonneg_right
      (velocity_normal_distance_bound w n hn) (norm_nonneg h))
  calc
    _ ≤ ‖D • h‖+‖dot (velocity w) h • n‖ := norm_add_le _ _
    _ = D*‖h‖+|dot (velocity w) h| := by rw [norm_smul,norm_smul,Real.norm_eq_abs,
        Real.norm_eq_abs,abs_of_nonneg hD,hn,mul_one]
    _ ≤ 2*Real.sqrt (2*D)*‖h‖ := by nlinarith [mul_le_mul_of_nonneg_right hDs (norm_nonneg h)]

lemma velocity_tangent_norm (v n : Vec) (hn : ‖n‖=1) :
    ‖(n-velocity v)-(1-dot n (velocity v)) • n‖≤Real.sqrt (2*(1-dot n (velocity v))) := by
  have he : (n-velocity v)-(1-dot n (velocity v)) • n =
      -(velocityProjection n (velocity v-n)) := by
    simp only [velocityProjection,dot_sub_right,dot_self,hn,one_pow]
    module
  rw [he,norm_neg]
  exact (velocityProjection_norm _ _ hn.le).trans (velocity_normal_distance_bound v n hn)

lemma receiverQ_transport_bound (w v n : Vec) (hn : ‖n‖=1) :
    ‖receiverQ (velocity w) n (n-velocity v)‖ ≤ (1-dot n (velocity v))+
      2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*(1-dot n (velocity v))) := by
  let d := 1-dot n (velocity v)
  let h := (n-velocity v)-d • n
  have hh : dot n h=0 := by
    dsimp only [h,d]
    simp only [dot_sub_right,dot_smul_right,dot_self,hn,one_pow,mul_one]
    ring
  have he : n-velocity v=d • n+h := by dsimp [h]; module
  rw [he,receiverQ_add,receiverQ_smul,receiverQ_normal]
  calc
    _ ≤ ‖d • n‖+‖receiverQ (velocity w) n h‖ := norm_add_le _ _
    _ ≤ d+2*Real.sqrt (2*(1-dot n (velocity w)))*Real.sqrt (2*d) := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (cone_denom_pos v n hn),hn,mul_one]
      exact add_le_add le_rfl ((receiverQ_tangent_bound w n h hn hh).trans
        (mul_le_mul_of_nonneg_left (velocity_tangent_norm v n hn) (by positivity)))

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


lemma sourceRepresentative_sum_bound {x : ℝ} (hx : 0≤x) (S : Finset ℕ)
    (hS : ∀n∈S,sourceRepresentative n≤x) : ∑n∈S,sourceRepresentative n≤2*x := by
  classical
  have hgeom (N : ℕ) : ∑n∈Finset.range (N+1),sourceRepresentative n≤2*sourceRepresentative N := by
    induction N with
    | zero => norm_num [sourceRepresentative]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      have he : sourceRepresentative (N+1)=2*sourceRepresentative N := by
        dsimp only [sourceRepresentative]
        rw [pow_succ]
        ring
      rw [he]
      linarith
  by_cases hne : S.Nonempty
  · let N := S.max' hne
    have hsub : S⊆Finset.range (N+1) := by
      intro n hn
      apply Finset.mem_range.mpr
      have hh := S.le_max' n hn
      change n≤N at hh
      omega
    have hs : (∑n∈S,sourceRepresentative n)≤∑n∈Finset.range (N+1),sourceRepresentative n :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by dsimp only [sourceRepresentative]; positivity)
    exact hs.trans ((hgeom N).trans (mul_le_mul_of_nonneg_left (hS N (S.max'_mem hne)) (by norm_num)))
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_ElectricBoundaryField
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

lemma forceTransportKernel_bound (r : ℝ) (n w v : Vec) (hn : ‖n‖=1) :
    ‖forceTransportKernel r n (velocity w) v‖ ≤
      (r^2*(q v)^2*(1-dot n (velocity v))^2)⁻¹ *
        ((1-dot n (velocity v))+2*Real.sqrt (2*(1-dot n (velocity w)))*
          Real.sqrt (2*(1-dot n (velocity v)))) := by
  unfold forceTransportKernel
  rw [norm_smul,Real.norm_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (receiverQ_transport_bound w v n hn) (by positivity)

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

lemma Admissible.uniform_physicalBinDensity_constant {d : Datum} (hd : Admissible d) :
    ∃ C : ℝ, 0≤C ∧ ∀ (s : Solution) (T : ℝ) (_F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → (∀ z,s.f (0,z)=d.f₀ z) →
      ∀ (X V : ℝ→Vec) (B : ClosedConeBin) (t r : ℝ) (n : Sphere) (P θ σ : ℝ),
      r∈Icc 0 T → 0≤P → 0≤θ → 0≤σ → B.qmax≤P → B.dmax≤8*θ^2 → B.emax≤8*σ^2 →
      physicalBinDensity s X V B t r n≤ENNReal.ofReal (128*C*P^3*(min θ σ)^2) := by
  obtain ⟨C,hC,hb⟩ := Admissible.uniform_particle_density_constant hd
  refine ⟨C,hC,?_⟩
  intro s T F hs h0 X V B t r n P θ σ hr hP hθ hσ hq hd he
  exact coneBin_density_bound (sphere_norm n).le (norm_velocity_lt_one _).le hP hθ hσ hC
    hq hd he (fun v=>(hb s T F hs h0 r hr _).2)

end RVM

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

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

lemma physicalBin_density_near {s : Solution} {X V : ℝ→Vec}
    (hV : Measurable V) (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {C p θ φ : ℝ} (hφ : 0 ≤ φ) (hD : B.Dmax ≤ 8*φ^2)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ≤ ENNReal.ofReal (128*C*p^3*θ^2)) :
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) ≤
      ENNReal.ofReal (128*C*p^3*θ^2)*
        (volume J*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
  have hb : (∫⁻z : ConeCoordinate,physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) ≤
      ∫⁻_z : ConeCoordinate,ENNReal.ofReal (128*C*p^3*θ^2) ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    exact hdensity z hz
  refine hb.trans ?_
  rw [lintegral_const]
  exact mul_le_mul' le_rfl (physicalBinMeasure_volume hV B hJ hφ hD)

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

lemma direct_transport_bin_bound {r p θ φ : ℝ} (n W v : Vec)
    (hr : 0 < r) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ) (hn : ‖n‖=1)
    (hq : p≤q v) (hdlo : θ^2/2≤1-dot n (velocity v))
    (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDhi : 1-dot n (velocity W)≤8*φ^2) :
    ‖forceTransportKernel r n (velocity W) v‖≤128*(θ+φ)/(r^2*p^2*θ^3) := by
  let d := 1-dot n (velocity v)
  let D := 1-dot n (velocity W)
  have hd : 0<d := cone_denom_pos v n hn
  have hD : 0<D := cone_denom_pos W n hn
  have hsθ : Real.sqrt (2*d)≤4*θ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hsφ : Real.sqrt (2*D)≤4*φ := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have hnum : d+2*Real.sqrt (2*D)*Real.sqrt (2*d)≤8*θ^2+32*φ*θ := by
    have hh := mul_le_mul hsφ hsθ (Real.sqrt_nonneg _) (by positivity : 0≤4*φ)
    dsimp only [d] at *
    nlinarith
  have hb := forceTransportKernel_bound r n W v hn
  change _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) at hb
  calc
    _ ≤ (r^2*(q v)^2*d^2)⁻¹*(d+2*Real.sqrt (2*D)*Real.sqrt (2*d)) := hb
    _ ≤ (r^2*p^2*(θ^2/2)^2)⁻¹*(8*θ^2+32*φ*θ) := by
      apply mul_le_mul _ hnum (by positivity) (by positivity)
      apply inv_anti₀ (by positivity)
      gcongr
    _ = (32*θ+128*φ)/(r^2*p^2*θ^3) := by field_simp; ring
    _ ≤ 128*(θ+φ)/(r^2*p^2*θ^3) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      nlinarith

lemma physicalDirectTransportDensity_bound {s : Solution} {X V : ℝ→Vec}
    {B : ClosedConeBin} {p θ φ : ℝ} {z : ConeCoordinate}
    (hr : 0<z.1-z.2.1) (hp : 0<p) (hθ : 0<θ) (hφ : 0≤φ)
    (hq : p≤B.qmin) (hdlo : θ^2/2≤B.dmin) (hdhi : B.dmax≤8*θ^2)
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalDirectTransportDensity s X V B z≤
      ENNReal.ofReal (128*(θ+φ)/(p^2*θ^3))*physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  unfold physicalDirectTransportDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
      apply mul_le_mul' le_rfl
      apply setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _)
      intro v hv
      rw [←ENNReal.ofReal_mul (by positivity : 0≤128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3))]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hf v)]
      calc
        _ ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (128*(θ+φ)/((z.1-z.2.1)^2*p^2*θ^3)) :=
          mul_le_mul_of_nonneg_left
            (direct_transport_bin_bound _ _ _ hr hp hθ hφ (sphere_norm _)
              (hq.trans hv.1.1) (hdlo.trans hv.2.1.1) (hv.2.1.2.trans hdhi) hDhi) (hf v)
        _ = _ := mul_comm _ _
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,
        ←ENNReal.ofReal_mul (sq_nonneg _)]
      congr 1
      congr 1
      field_simp

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CappedRepresentativePos
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

lemma cappedRepresentative_pos (n : ℕ) : 0 < cappedRepresentative n := by
  dsimp [cappedRepresentative]
  positivity

lemma cappedRepresentative_le_one (n : ℕ) : cappedRepresentative n ≤ 1 := by
  exact pow_le_one₀ (by norm_num) (by norm_num)

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Flow_ClosedEulerianTimeBudget
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

lemma capped_positive_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j/x)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  classical
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.min' hne
    have hj₀ : j₀∈S := S.min'_mem hne
    have hjmin (j : ℕ) (hj : j∈S) : j₀≤j := S.min'_le j hj
    have hp (j : ℕ) (hj : j∈S) : cappedRepresentative j/x≤((2:ℝ)⁻¹)^(j-j₀) := by
      have he : cappedRepresentative j=cappedRepresentative j₀*((2:ℝ)⁻¹)^(j-j₀) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmin j hj)]
      rw [he]
      apply (div_le_iff₀ hx).mpr
      have hh := mul_le_mul_of_nonneg_right (hS j₀ hj₀)
        (pow_nonneg (by norm_num : (0:ℝ)≤2⁻¹) (j-j₀))
      simpa only [mul_comm] using hh
    have hpoint (j : ℕ) (hj : j∈S) : (cappedRepresentative j/x)^α≤(((2:ℝ)⁻¹)^α)^(j-j₀) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg (cappedRepresentative_pos j).le hx.le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j-j₀) S := by
      intro i hi j hj hij
      have hi' := hjmin i hi
      have hj' := hjmin j hj
      change i-j₀=j-j₀ at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j-j₀) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j-j₀),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_QuadIndexEquiv
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

lemma tsum_quad_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'np,∑'nt,∑'nf,∑'nr,f ![np,nt,nf,nr] := by
  have h := quadIndexEquiv.symm.tsum_eq f
  rw [←h]
  simp only [ENNReal.tsum_prod']
  rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RadialSummation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

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


lemma capped_positive_power_sum_unscaled {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,cappedRepresentative j≤x) :
    ∑j∈S,(cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹*x^α := by
  have hh := capped_positive_power_sum hx hα S hS
  have he (j : ℕ) : (cappedRepresentative j/x)^α=(cappedRepresentative j)^α/x^α :=
    Real.div_rpow (cappedRepresentative_pos j).le hx.le α
  simp_rw [he] at hh
  rw [←Finset.sum_div] at hh
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hx α)).mp hh


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SharedOccupation
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

lemma central_near_scalar {C I H h p θ φ : ℝ} :
    (128*C*p^3*θ^2)*(I*(2*H*h-H*h/2)*(384*φ^2))=
      (73728*C*H)*(I*h*p^3*θ^2*φ^2) := by ring

lemma capped_linear_tail_sum {φ : ℝ} (hφ : 0<φ) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))≤
      ENNReal.ofReal (2*φ) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤φ)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤φ then cappedRepresentative n else 0))=
      ∑n∈U,ENNReal.ofReal (cappedRepresentative n) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>(cappedRepresentative_pos n).le)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hφ (by norm_num : (0:ℝ)<1) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num only [Real.rpow_one] at hh
  exact hh

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_CentralOccupation
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

lemma capped_square_tail_sum {x : ℝ} (hx : 0<x) :
    (∑'n : ℕ,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))≤
      ENNReal.ofReal (2*x^2) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun n=>cappedRepresentative n≤x)
  have he : (∑n∈S,ENNReal.ofReal (if cappedRepresentative n≤x then (cappedRepresentative n)^2 else 0))=
      ∑n∈U,ENNReal.ofReal ((cappedRepresentative n)^2) := by simp [U,Finset.sum_filter,apply_ite]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun n _=>sq_nonneg _)]
  apply ENNReal.ofReal_le_ofReal
  have hh := capped_positive_power_sum_unscaled hx (by norm_num : (0:ℝ)<2) U
    (fun n hn=>(Finset.mem_filter.mp hn).2)
  norm_num at hh
  nlinarith [sq_nonneg x]

lemma small_deficit_stabilityLength {P M A p w φ : ℝ}
    (hP : 0<P) (hM : 1≤M) (hp : 0<p) (hw : 0<w) (hφ : 0<φ)
    (hsmall : φ≤512/min p w) : stabilityLength P 16384 M A p w φ≤1/P^2 := by
  have hm : 0 < min p w := lt_min hp hw
  have hprod : min p w*φ≤512 := by
    have hh := (le_div_iff₀ hm).mp hsmall
    nlinarith
  have hPr : P ≤ stabilityRate P 16384 M A p w φ := by
    have he : 16384*(P/min p w)*(M/φ)=(16384*P*M)/(min p w*φ) := by field_simp
    calc
      P≤(16384*P*M)/(min p w*φ) := by
        apply (le_div_iff₀ (mul_pos hm hφ)).mpr
        have hh := mul_le_mul_of_nonneg_left hprod hP.le
        have hM' := mul_le_mul_of_nonneg_left hM (by positivity : 0≤16384*P)
        nlinarith
      _=16384*(P/min p w)*(M/φ) := he.symm
      _≤_ := by
        unfold stabilityRate
        exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (by positivity)
  have hi := one_div_le_one_div_of_le hP hPr
  have hr : 0 < stabilityRate P 16384 M A p w φ := hP.trans_le hPr
  have hh := pow_le_pow_left₀ (by positivity : 0≤1/stabilityRate P 16384 M A p w φ) hi 2
  simpa only [stabilityLength,one_div,inv_pow] using hh

lemma Admissible.representative_central_near {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I →
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*(I*cappedRepresentative (k 3)*(sourceRepresentative (k 0))^3*
          (cappedRepresentative (k 1))^2*(cappedRepresentative (k 2))^2)) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  refine ⟨73728*Cρ*max 1 T₀,by positivity,?_⟩
  intro s T F hs hT hTT zX k a b I w ha hb hI hJI
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hθ : 0<θ := cappedRepresentative_pos _
  have hφ : 0<φ := cappedRepresentative_pos _
  have hh : 0<h := cappedRepresentative_pos _
  have hH : 1≤H := le_max_left _ _
  have hdiff : 0≤2*H*h-H*h/2 := by nlinarith [mul_nonneg (zero_le_one.trans hH) hh.le]
  have hHH : H≤ max 1 T₀ := max_le_max le_rfl hTT
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs.energyPrefix hT).comp (continuous_id.prodMk continuous_const)
  have hdensity (t r : ℝ) (n : Sphere) (hr : r∈Icc 0 T) :
      physicalBinDensity s X V B t r n≤ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
    have he := hden s T F hs.energyPrefix hs.initial_f X V B t r n p θ 1 hr hp.le hθ.le
      (by norm_num : (0:ℝ)≤1) (by change p/32≤p; linarith) le_rfl (by norm_num [B,representativeClosedBin])
    simpa only [min_eq_left (show θ≤1 from cappedRepresentative_le_one (k 1))] using he
  have hn := physicalBin_density_near hα.snd.measurable B (J:=Icc a b) measurableSet_Icc hφ.le
    (by rfl : B.Dmax≤8*φ^2) (fun z hz=>hdensity z.1 z.2.1 z.2.2 ⟨hz.2.1.1,hz.2.1.2.trans (hz.1.2.trans hb)⟩)
  apply hn.trans
  calc
    _≤ENNReal.ofReal (128*Cρ*p^3*θ^2)*
        (ENNReal.ofReal I*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)) := by
      apply mul_le_mul' le_rfl
      apply mul_le_mul' _ le_rfl
      apply mul_le_mul' _ le_rfl
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_le_ofReal hJI
    _=ENNReal.ofReal ((73728*Cρ*H)*(I*h*p^3*θ^2*φ^2)) := by
      change ENNReal.ofReal (128*Cρ*p^3*θ^2)*
        (ENNReal.ofReal I*ENNReal.ofReal (2*H*h-H*h/2)*ENNReal.ofReal (384*φ^2))=_
      rw [←ENNReal.ofReal_mul hI.le,←ENNReal.ofReal_mul (mul_nonneg hI.le hdiff),
        ←ENNReal.ofReal_mul (by positivity : 0≤128*Cρ*p^3*θ^2)]
      exact congrArg ENNReal.ofReal central_near_scalar
    _≤_ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hHH (by positivity)) (by positivity))

lemma central_cost_eq_regular_add_exception {T : ℝ} (s : Solution) (F : PhaseFlowOn s.E s.B T)
    (zX : Phase) (P M A I w : ℝ) (k : Fin 4→ℕ) (a b : ℝ) :
    representativeCentralCost s F zX w k a b=
      representativeRegularCentralCost s F zX P M A I w k a b+
      representativeExceptionCentralCost s F zX P M A I w k a b := by
  classical
  simp only [representativeRegularCentralCost,representativeExceptionCentralCost]
  split_ifs <;> simp

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_ReceiverWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma tsum_quad_pair_index (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,f k)=∑'n : ℕ×ℕ,∑'nt : ℕ,∑'nr : ℕ,f ![n.1,nt,n.2,nr] := by
  rw [tsum_quad_index,ENNReal.tsum_prod']
  apply tsum_congr
  intro np
  exact ENNReal.tsum_comm

lemma representativeSmallSector_subset_centralIndexSector (P : ℝ) :
    representativeSmallSector P⊆centralIndexSector P := by
  intro k hk
  refine ⟨hk.1,hk.2.1.trans (hk.2.2.trans ?_),hk.2.2⟩
  have hφ := (cappedRepresentative_pos (k 2)).le
  linarith



open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_TransportRemainder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section
open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma capped_inverse_power_sum {x α : ℝ} (hx : 0<x) (hα : 0<α)
    (S : Finset ℕ) (hS : ∀j∈S,x ≤ cappedRepresentative j) :
    ∑j∈S,(x/cappedRepresentative j)^α≤(1-((2:ℝ)⁻¹)^α)⁻¹ := by
  have hbase : 0<((2:ℝ)⁻¹)^α := Real.rpow_pos_of_pos (by norm_num) _
  have hbase1 : ((2:ℝ)⁻¹)^α<1 := Real.rpow_lt_one (by norm_num) (by norm_num) hα
  have hnorm : ‖((2:ℝ)⁻¹)^α‖<1 := by rw [Real.norm_eq_abs,abs_of_pos hbase]; exact hbase1
  by_cases hne : S.Nonempty
  · let j₀ := S.max' hne
    have hj₀ : j₀∈S := S.max'_mem hne
    have hjmax (j : ℕ) (hj : j∈S) : j≤j₀ := S.le_max' j hj
    have hp (j : ℕ) (hj : j∈S) : x/cappedRepresentative j≤((2:ℝ)⁻¹)^(j₀-j) := by
      have he : cappedRepresentative j₀=cappedRepresentative j*((2:ℝ)⁻¹)^(j₀-j) := by
        dsimp only [cappedRepresentative]
        rw [←pow_add,Nat.add_sub_of_le (hjmax j hj)]
      apply (div_le_iff₀ (cappedRepresentative_pos j)).mpr
      rw [mul_comm,←he]
      exact hS j₀ hj₀
    have hpoint (j : ℕ) (hj : j∈S) : (x/cappedRepresentative j)^α≤(((2:ℝ)⁻¹)^α)^(j₀-j) := by
      rw [Real.rpow_pow_comm (by norm_num : (0:ℝ)≤2⁻¹)]
      exact Real.rpow_le_rpow (div_nonneg hx.le (cappedRepresentative_pos j).le) (hp j hj) hα.le
    have hinj : Set.InjOn (fun j : ℕ=>j₀-j) S := by
      intro i hi j hj hij
      have hi' := hjmax i hi
      have hj' := hjmax j hj
      change j₀-i=j₀-j at hij
      omega
    calc
      _ ≤ ∑j∈S,(((2:ℝ)⁻¹)^α)^(j₀-j) := Finset.sum_le_sum hpoint
      _ = ∑m∈S.image (fun j=>j₀-j),(((2:ℝ)⁻¹)^α)^m := (Finset.sum_image hinj).symm
      _ ≤ ∑'m : ℕ,(((2:ℝ)⁻¹)^α)^m :=
        (summable_geometric_of_norm_lt_one hnorm).sum_le_tsum _ (fun _ _=>by positivity)
      _ = _ := tsum_geometric_of_norm_lt_one hnorm
  · have he : S=∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [he,Finset.sum_empty]
    exact inv_nonneg.mpr (sub_nonneg.mpr hbase1.le)

lemma capped_inverse_square_floor_sum {p : ℝ} (hp : 0<p) (S : Finset ℕ)
    (hS : ∀nt∈S,1/p ≤ cappedRepresentative nt) :
    (∑nt∈S,1/(p*(cappedRepresentative nt)^2))≤2*p := by
  have hh := capped_inverse_power_sum (one_div_pos.mpr hp) (by norm_num : (0:ℝ)<2) S hS
  norm_num only [Real.rpow_two,inv_pow] at hh
  norm_num at hh
  have he (nt : ℕ) : 1/(p*(cappedRepresentative nt)^2)=p*((1/p)/cappedRepresentative nt)^2 := by
    have ht := (cappedRepresentative_pos nt).ne'
    field_simp
  simp_rw [he]
  rw [←Finset.mul_sum]
  have hh' := mul_le_mul_of_nonneg_left hh hp.le
  simp only [one_div] at *
  nlinarith

lemma capped_inverse_square_floor_tsum {p : ℝ} (hp : 0<p) :
    (∑'nt : ℕ,ENNReal.ofReal (if 1/p ≤ cappedRepresentative nt then
      1/(p*(cappedRepresentative nt)^2) else 0))≤ENNReal.ofReal (2*p) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun nt=>1/p ≤ cappedRepresentative nt)
  have he : (∑nt∈S,ENNReal.ofReal (if 1/p ≤ cappedRepresentative nt then
      1/(p*(cappedRepresentative nt)^2) else 0))=
      ∑nt∈U,ENNReal.ofReal (1/(p*(cappedRepresentative nt)^2)) := by
    simp only [U,Finset.sum_filter,apply_ite,ENNReal.ofReal_zero]
  rw [he,←ENNReal.ofReal_sum_of_nonneg (fun nt _=>by positivity)]
  exact ENNReal.ofReal_le_ofReal (capped_inverse_square_floor_sum hp U
    (fun nt hnt=>(Finset.mem_filter.mp hnt).2))

lemma small_transport_coefficient {p θ φ : ℝ} (hp : 0<p) (hθ : 0<θ) (_hφ : 0<φ)
    (hsmall : θ≤φ/16) :
    128*(θ+φ)/((p/128)^2*θ^3)≤4194304*φ/(p^2*θ^3) := by
  have hd : 0<p^2*θ^3 := by positivity
  have he : 128*(θ+φ)/((p/128)^2*θ^3)=2097152*(θ+φ)/(p^2*θ^3) := by ring
  rw [he]
  apply (div_le_div_iff_of_pos_right hd).mpr
  nlinarith

lemma small_transport_near_scalar {I h p θ φ : ℝ} (hI : 0≤I) (hh : 0≤h)
    (hp : 0<p) (ht : 0<θ) (hf : 0<φ) (ht1 : θ≤1) (hf1 : φ≤1) :
    (4194304*φ/(p^2*θ^3))*(I*h*p^3*θ^2*φ^2)≤
      (4194304*I*h*p^2*φ^2)*(1/(p*θ^2)) := by
  have hx : φ*θ≤1 := by nlinarith [mul_le_mul_of_nonneg_left ht1 hf.le]
  calc
    _=(4194304*I*h*p^2*φ^2)*(1/(p*θ^2))*(φ*θ) := by field_simp
    _≤(4194304*I*h*p^2*φ^2)*(1/(p*θ^2))*1 :=
      mul_le_mul_of_nonneg_left hx (by positivity)
    _=_ := mul_one _

lemma small_transport_exception_model_sum {P I p : ℝ} (hP : 0<P) (hI : 0≤I) (hp : 0<p) :
    (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
      if 1/p ≤ cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0)≤
      ENNReal.ofReal (33554432*I*p^3/P^2) := by
  have hc : 0≤4194304*I*p^2 := by positivity
  have hr (nf nt : ℕ) : (∑'nr : ℕ,if cappedRepresentative nr≤1/P^2 then
      ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
        (1/(p*(cappedRepresentative nt)^2))) else 0)≤
        ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)))*
          ENNReal.ofReal (2/P^2) := by
    have hc' : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)) := by positivity
    have he (nr : ℕ) : (if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0)=
          ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2)))*
            ENNReal.ofReal (if cappedRepresentative nr≤1/P^2 then cappedRepresentative nr else 0) := by
      split_ifs with h
      · rw [←ENNReal.ofReal_mul hc']
        congr 1
        ring
      · simp
    simp_rw [he,ENNReal.tsum_mul_left]
    exact mul_le_mul' le_rfl ((capped_linear_tail_sum (by positivity : 0<(1:ℝ)/P^2)).trans_eq (by congr 1; ring))
  have ht (nf : ℕ) : (∑'nt : ℕ,∑'nr : ℕ,
      if 1/p ≤ cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0)≤
      ENNReal.ofReal (16777216*I*p^3/P^2*(cappedRepresentative nf)^2) := by
    have hc' : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2) := by positivity
    calc
      _≤ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2))*
          (∑'nt : ℕ,ENNReal.ofReal (if 1/p ≤ cappedRepresentative nt then 1/(p*(cappedRepresentative nt)^2) else 0)) := by
        rw [←ENNReal.tsum_mul_left]
        apply ENNReal.tsum_le_tsum
        intro nt
        split_ifs with hnt
        · apply (hr nf nt).trans_eq
          rw [←ENNReal.ofReal_mul (by positivity : 0≤4194304*I*p^2*(cappedRepresentative nf)^2*(1/(p*(cappedRepresentative nt)^2))),←ENNReal.ofReal_mul hc']
          congr 1
          ring
        · simp
      _≤ENNReal.ofReal (4194304*I*p^2*(cappedRepresentative nf)^2*(2/P^2))*ENNReal.ofReal (2*p) :=
        mul_le_mul' le_rfl (capped_inverse_square_floor_tsum hp)
      _=_ := by rw [←ENNReal.ofReal_mul hc']; congr 1; ring
  have hsq : (∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2))≤2 := by
    have hh := capped_square_tail_sum (by norm_num : (0:ℝ)<1)
    simpa only [ite_eq_left (cappedRepresentative_le_one _),one_pow,ENNReal.ofReal_ofNat,mul_one] using hh
  calc
    _≤∑'nf : ℕ,ENNReal.ofReal (16777216*I*p^3/P^2*(cappedRepresentative nf)^2) := ENNReal.tsum_le_tsum ht
    _=ENNReal.ofReal (16777216*I*p^3/P^2)*(∑'nf : ℕ,ENNReal.ofReal ((cappedRepresentative nf)^2)) := by
      simp_rw [ENNReal.ofReal_mul (by positivity : 0≤16777216*I*p^3/P^2),ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal (16777216*I*p^3/P^2)*2 := mul_le_mul' le_rfl hsq
    _=_ := by rw [←ENNReal.ofReal_ofNat 2,←ENNReal.ofReal_mul (by positivity : 0≤16777216*I*p^3/P^2)]; congr 1; ring

lemma smallTransportCoefficient_nonneg (k : Fin 4→ℕ) : 0 ≤ smallTransportCoefficient k := by
  have hp : 0 < sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  unfold smallTransportCoefficient
  positivity

lemma physicalDirectTransportDensity_representative_small {s : Solution} {X V : ℝ→Vec}
    {T w a b : ℝ} (hs : EnergyPrefix s T) (ha : 0≤a) (hb : b≤T)
    (k : Fin 4→ℕ) (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16)
    (z : ConeCoordinate) (hz : z∈physicalBinBase V (representativeClosedBin T w k) (Icc a b)) :
    physicalDirectTransportDensity s X V (representativeClosedBin T w k) z≤
      ENNReal.ofReal (smallTransportCoefficient k)*
        physicalBinDensity s X V (representativeClosedBin T w k) z.1 z.2.1 z.2.2 := by
  have hp : 0 < sourceRepresentative (k 0) := by unfold sourceRepresentative; positivity
  have ht := cappedRepresentative_pos (k 1)
  have hf := cappedRepresentative_pos (k 2)
  have hrad : 0<z.1-z.2.1 := (representativeClosedBin_radius_pos T w k).trans_le hz.2.2.1.1
  have hh := physicalDirectTransportDensity_bound (s:=s) (X:=X) (V:=V) hrad
    (show 0 < sourceRepresentative (k 0)/128 by positivity) ht hf.le
    (B:=representativeClosedBin T w k) le_rfl le_rfl le_rfl hz.2.2.2.2.2
    (fun v=>hs.nonnegative _ ⟨hz.2.1.1,hz.2.1.2.trans ((Icc_subset_Icc ha hb) hz.1).2⟩ _)
  exact hh.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (small_transport_coefficient hp ht hf hsmall)) le_rfl)

lemma PhaseFlowOn.directTransport_representative_small {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (k : Fin 4→ℕ) {a b : ℝ} (ha : 0≤a) (hb : b≤T)
    (hsmall : cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16) :
    (∫⁻z : ConeCoordinate,physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
      (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
        ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b))≤
      ENNReal.ofReal (smallTransportCoefficient k)*representativeCentralCost s F zX w k a b := by
  have hV := ((F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))).snd.measurable
  unfold representativeCentralCost
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) measurableSet_Icc)] with z hz
  exact physicalDirectTransportDensity_representative_small hs ha hb k hsmall z hz

lemma Admissible.small_transport_exception_triple_sum {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (np : ℕ) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      (∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative np ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
          ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
            representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
        ENNReal.ofReal (C*I*(sourceRepresentative np)^3/P^2) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.representative_central_near T₀
  refine ⟨33554432*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
  let p := sourceRepresentative np
  have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
  have hpoint (nf nt nr : ℕ) :
      (if 1/p ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
        ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
          representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0)≤
      ENNReal.ofReal Cn*(if 1/p ≤ cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
        ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
          (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) := by
    by_cases ht : 1/p ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16
    · rw [ite_eq_left ht,ite_eq_left ht.1]
      by_cases hr : regularCentralIndex P M A I w ![np,nt,nf,nr]
      · simp only [representativeExceptionCentralCost,ite_eq_left hr,mul_zero]
        exact bot_le
      · have hreg : ¬(512/min p w < cappedRepresentative nf ∨
            min I (stabilityLength P 16384 M A p w (cappedRepresentative nf)) < cappedRepresentative nr) := by
          simpa [regularCentralIndex,p] using hr
        have hf : cappedRepresentative nf≤512/min p w := le_of_not_gt (not_or.mp hreg).1
        have hnr : cappedRepresentative nr≤1/P^2 :=
          ((le_of_not_gt (not_or.mp hreg).2).trans (min_le_right _ _)).trans
            (small_deficit_stabilityLength hP hM hp hw (cappedRepresentative_pos _) hf)
        rw [ite_eq_left hnr,representativeExceptionCentralCost,ite_eq_right hr]
        have hc := smallTransportCoefficient_nonneg ![np,nt,nf,nr]
        apply (mul_le_mul' le_rfl (hnear s T F hs hT hTT zX ![np,nt,nf,nr] a b I w ha hb hI hJI)).trans
        rw [←ENNReal.ofReal_mul hc,←ENNReal.ofReal_mul hCn]
        apply ENNReal.ofReal_le_ofReal
        have hn := mul_le_mul_of_nonneg_left (small_transport_near_scalar hI.le
          (cappedRepresentative_pos nr).le hp (cappedRepresentative_pos nt) (cappedRepresentative_pos nf)
          (cappedRepresentative_le_one _) (cappedRepresentative_le_one _)) hCn
        simpa only [smallTransportCoefficient,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Matrix.cons_val,Fin.reduceFinMk,
          p,mul_left_comm,mul_assoc] using hn
    · rw [ite_eq_right ht]
      exact bot_le
  calc
    _≤∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        ENNReal.ofReal Cn*(if 1/p ≤ cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
            (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) :=
      ENNReal.tsum_le_tsum (fun nf=>ENNReal.tsum_le_tsum (fun nt=>ENNReal.tsum_le_tsum (hpoint nf nt)))
    _=ENNReal.ofReal Cn*(∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
        if 1/p ≤ cappedRepresentative nt then if cappedRepresentative nr≤1/P^2 then
          ENNReal.ofReal ((4194304*I*cappedRepresentative nr*p^2*(cappedRepresentative nf)^2)*
            (1/(p*(cappedRepresentative nt)^2))) else 0 else 0) := by
      simp only [ENNReal.tsum_mul_left]
    _≤ENNReal.ofReal Cn*ENNReal.ofReal (33554432*I*p^3/P^2) :=
      mul_le_mul' le_rfl (small_transport_exception_model_sum hP hI.le hp)
    _=_ := by rw [←ENNReal.ofReal_mul hCn]; congr 1; dsimp only [p]; ring


end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma sourceRepresentative_cube_sum {P : ℝ} (hP : 0≤P) (S : Finset ℕ)
    (hS : ∀np∈S,sourceRepresentative np≤P) :
    (∑np∈S,(sourceRepresentative np)^3)≤2*P^3 := by
  have hp (np : ℕ) : 0 ≤ sourceRepresentative np := by unfold sourceRepresentative; positivity
  calc
    _≤∑np∈S,P^2*sourceRepresentative np := by
      apply Finset.sum_le_sum
      intro np hn
      have hh := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hp np) (hS np hn) 2) (hp np)
      nlinarith only [hh]
    _=P^2*(∑np∈S,sourceRepresentative np) := (Finset.mul_sum ..).symm
    _≤P^2*(2*P) := mul_le_mul_of_nonneg_left (sourceRepresentative_sum_bound hP S hS) (sq_nonneg P)
    _=2*P^3 := by ring

lemma Admissible.small_transport_exception_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      0≤a → b≤T → 0<I → b-a≤I → 0<w →
      let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
      (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
        if 1/sourceRepresentative n.1 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
          ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
            representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ENNReal.ofReal (C*I*P) := by
  obtain ⟨Cn,hCn,hnear⟩ := hd.small_transport_exception_triple_sum T₀
  refine ⟨2*Cn,by positivity,?_⟩
  intro M A P hM hP s T F hs hT hTT zX a b I w ha hb hI hJI hw
  dsimp only
  let Q := {n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
    1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}
  let g := fun np=>∑'nf : ℕ,∑'nt : ℕ,∑'nr : ℕ,
    if 1/sourceRepresentative np ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative nf/16 then
      ENNReal.ofReal (smallTransportCoefficient ![np,nt,nf,nr])*
        representativeExceptionCentralCost s F zX P M A I w ![np,nt,nf,nr] a b else 0
  have hc : 0≤Cn*I/P^2 := by positivity
  have hdom : (∑'n : ℕ×ℕ,Q.indicator (fun n=>∑'nt : ℕ,∑'nr : ℕ,
      if 1/sourceRepresentative n.1 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 then
        ENNReal.ofReal (smallTransportCoefficient ![n.1,nt,n.2,nr])*
          representativeExceptionCentralCost s F zX P M A I w ![n.1,nt,n.2,nr] a b else 0) n)≤
        ∑'np : ℕ,if sourceRepresentative np≤P then g np else 0 := by
    rw [ENNReal.tsum_prod']
    apply ENNReal.tsum_le_tsum
    intro np
    split_ifs with hn
    · apply ENNReal.tsum_le_tsum
      intro nf
      exact (indicator_le_self _ _) (np,nf)
    · have hz (nf : ℕ) : (np,nf)∉Q := fun hh=>hn hh.1
      simp only [indicator_of_notMem (hz _),tsum_zero,le_refl]
  apply hdom.trans
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun np=>sourceRepresentative np≤P)
  have hU (np) (hn : np∈U) : sourceRepresentative np≤P := (Finset.mem_filter.mp hn).2
  have he : (∑np∈S,if sourceRepresentative np≤P then g np else 0)=∑np∈U,g np := by
    simp [U,Finset.sum_filter]
  rw [he]
  calc
    _≤∑np∈U,ENNReal.ofReal (Cn*I*(sourceRepresentative np)^3/P^2) := by
      apply Finset.sum_le_sum
      intro np hn
      exact hnear M A P hM hP s T F hs hT hTT zX np a b I w ha hb hI hJI hw
    _=ENNReal.ofReal ((Cn*I/P^2)*(∑np∈U,(sourceRepresentative np)^3)) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun np _=>by unfold sourceRepresentative; positivity)]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro np hn
      ring
    _≤ENNReal.ofReal ((Cn*I/P^2)*(2*P^3)) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (sourceRepresentative_cube_sum hP.le U hU) hc)
    _=_ := by congr 1; field_simp



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma tsum_representativeSmallSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(representativeSmallSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if 1/sourceRepresentative n.1 ≤ cappedRepresentative nt ∧
          cappedRepresentative nt ≤ cappedRepresentative n.2/16 then f ![n.1,nt,n.2,nr] else 0) n := by
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2
  · rw [indicator_of_mem (show n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} from hn)]
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈representativeSmallSector P) ↔
        1/sourceRepresentative n.1 ≤ cappedRepresentative nt ∧ cappedRepresentative nt ≤ cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧ _ ∧ _) ↔ _
      simp only [hn.1,true_and,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val]
    simp only [indicator_apply,hi]
  · rw [indicator_of_notMem (show n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} from hn)]
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    intro hk
    have hc := representativeSmallSector_subset_centralIndexSector P hk
    exact hn ⟨hc.1,hc.2.1⟩

lemma Admissible.small_transport_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃C : ℝ,0≤C ∧ ∀M A P : ℝ,1≤M → 0≤A → 1≤P → 1≤Real.log (2+P) →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → I≤1 → b-a≤I → 0<w → w≤P →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      (∑'k : Fin 4→ℕ,(representativeSmallSector P).indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectTransportDensity s X V (representativeClosedBin T w k) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w)) := by
  obtain ⟨Cr,hCr,hregular⟩ := hd.small_transport_regular_uniform T₀
  obtain ⟨Ce,hCe,hexception⟩ := hd.small_transport_exception_uniform T₀
  refine ⟨Cr+Ce,add_nonneg hCr hCe,?_⟩
  intro M A P hM hA hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hI1 hJI hw hwP HZ
  dsimp only
  let B := P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w
  have hB : 0≤B := by dsimp [B]; positivity
  let R := representativeSmallSector P
  let c := fun k=>ENNReal.ofReal (smallTransportCoefficient k)
  let g := fun k=>c k*representativeRegularCentralCost s F zX P M A I w k a b
  let e := fun k=>c k*representativeExceptionCentralCost s F zX P M A I w k a b
  have hdom : (∑'k : Fin 4→ℕ,R.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalDirectTransportDensity s (fun t=>(prefixFlow F.flow T zX t).1)
          (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) (Icc a b)) k)≤
      (∑'k,R.indicator g k)+(∑'k,R.indicator e k) := by
    rw [←ENNReal.tsum_add]
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈R
    · simp only [indicator_of_mem hk]
      apply (F.directTransport_representative_small hs.energyPrefix hT zX k ha hb hk.2.2).trans_eq
      rw [central_cost_eq_regular_add_exception (P:=P) (M:=M) (A:=A) (I:=I),mul_add]
    · simp only [indicator_of_notMem hk,add_zero,le_refl]
  have hr : (∑'k,R.indicator g k)≤ENNReal.ofReal (Cr*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    exact hregular M A P (zero_lt_one.trans_le hM) hA hP hL s T F hs hT hTT zX a b I w
      hzX ha hb hI hJI hw hwP HZ
  have he : (∑'k,R.indicator e k)≤ENNReal.ofReal (Ce*B) := by
    rw [show R=representativeSmallSector P from rfl,tsum_representativeSmallSector]
    apply (hexception M A P hM (zero_lt_one.trans_le hP) s T F hs hT hTT zX a b I w ha hb hI hJI hw).trans
    apply ENNReal.ofReal_le_ofReal
    have hi : I≤Real.sqrt I := by nlinarith [Real.sq_sqrt hI.le,Real.sqrt_nonneg I]
    have hip : I*P≤P*Real.sqrt I := by
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hi (zero_le_one.trans hP)
    have hh : I*P≤B := hip.trans (le_add_of_nonneg_right (by positivity))
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hCe
  apply (hdom.trans (add_le_add hr he)).trans_eq
  rw [←ENNReal.ofReal_add (mul_nonneg hCr hB) (mul_nonneg hCe hB)]
  congr 1
  ring

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.small_transport_uniform_oai := @OAI.RVM.Admissible.small_transport_uniform_oai
