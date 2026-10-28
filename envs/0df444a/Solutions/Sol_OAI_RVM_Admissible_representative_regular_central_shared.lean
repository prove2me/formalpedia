-- Prove2me | solution 1 for OAI.RVM.Admissible.representative_regular_central_shared
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:14:53.319977+00:00
-- url     : https://prove2.me/submissions/e9778687-d11d-47f2-804e-dabb1c8018c4

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_representative_large_shared_occupation
import Theorems.Thm_OAI_RVM_Admissible_representative_shared_occupation

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ArrivalDomain
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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PhaseFlowOn.arrivalLabel_mem {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalLabel F.flow p ∈ jointBranchDomain F.flow zX T := by
  have h := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow _ p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow _ p.1).1
  change (p.1 ∈ Ioo 0 T ∧ p.1+‖(F.flow zX T).1-(F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖<T) ∧
    (F.flow zX p.1).1 ≠ (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1
  rw [h]
  exact ⟨⟨hp.1,hp.2.1⟩,hp.2.2⟩

lemma PhaseFlowOn.arrival_time_spec {E B : Field} {T : ℝ} (F : PhaseFlowOn E B T)
    (zX : Phase) {p : ℝ × Vec} (hp : p ∈ arrivalDomain F.flow zX T) :
    arrivalTime F.flow zX T p ∈ Ioo p.1 T ∧
      arrivalTime F.flow zX T p-p.1=‖(F.flow zX (arrivalTime F.flow zX T p)).1-p.2‖ := by
  have h := F.arrivalLabel_mem zX hp
  have ht := F.branch_time_mem zX (arrivalLabel F.flow p).2 h.1 h.2
  have he := (F.branch_spec zX (arrivalLabel F.flow p).2 h.1).2
  have hh := F.flow_inversePhase (Ioo_subset_Icc_self hp.1) (p.2,0)
  change _-p.1=‖_- (F.flow (inversePhase F.flow (p.1,(p.2,0))) p.1).1‖ at he
  rw [hh] at he
  exact ⟨ht,he⟩

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

lemma inClosedConeBin_iff {α : Phase → ℝ → Phase} {zX z : Phase} {B : ClosedConeBin}
    {t r : ℝ} (hR : 0<t-r) :
    InClosedConeBin α zX B t r z ↔
      t-r=‖(α zX t).1-(α z r).1‖ ∧ t-r∈Icc B.rmin B.rmax ∧
      q (α z r).2∈Icc B.qmin B.qmax ∧ q (α zX t).2∈Icc B.wmin B.wmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α z r).2)∈Icc B.dmin B.dmax ∧
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) (velocity (α zX t).2)∈Icc B.Dmin B.Dmax ∧
      1-dot (velocity (α zX t).2) (velocity (α z r).2)∈Icc B.emin B.emax := by
  have he (v : Vec) :
      1-dot ((t-r)⁻¹ • ((α zX t).1-(α z r).1)) v=
        ((t-r)-dot ((α zX t).1-(α z r).1) v)/(t-r) := by
    rw [dot_smul_left]
    field_simp
  simp only [InClosedConeBin,he,mem_Icc]
  rw [le_div_iff₀ hR,div_le_iff₀ hR,le_div_iff₀ hR,div_le_iff₀ hR]
  simp only [mul_comm]

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

lemma PhaseFlowOn.physical_hit_arrival {E B : Field} {T r t : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (y : Vec)
    (hr : r∈Ioo 0 T) (ht : t∈Icc 0 T) (hrt : r<t)
    (he : t-r=‖(F.flow zX t).1-y‖) (htT : t<T) :
    (r,y)∈arrivalDomain F.flow zX T ∧ arrivalTime F.flow zX T (r,y)=t := by
  have hT : 0≤T := hr.1.le.trans hr.2.le
  have hmono := F.arrival_strictMono hT zX y
  have htip : (F.flow zX r).1≠y := by
    intro h
    have hm := hmono (Ioo_subset_Icc_self hr) ht hrt
    dsimp only at hm
    rw [h,sub_self,norm_zero] at hm
    linarith
  have hlast : r+‖(F.flow zX T).1-y‖<T := by
    have hm := hmono ht ⟨hT,le_rfl⟩ htT
    dsimp only at hm
    linarith
  have hp : (r,y)∈arrivalDomain F.flow zX T := ⟨hr,hlast,htip⟩
  refine ⟨hp,?_⟩
  obtain ⟨hτ,hτe⟩ := F.arrival_time_spec zX hp
  apply hmono.injOn ⟨hr.1.le.trans hτ.1.le,hτ.2.le⟩ ht
  dsimp only
  linarith

lemma EnergyPrefix.continuous_prefixParticle {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) : Continuous (prefixParticle s T) :=
  hs.f_smooth.continuousOn.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

lemma measurable_coneBinDensity {g : Particle} (hg : Measurable g)
    {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin) :
    Measurable (fun z : ConeCoordinate => ∫⁻ v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal (g (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v)))) := by
  let H : Set (ConeCoordinate × Vec) :=
    {p | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))}
  have hn : Measurable (fun p : ConeCoordinate × Vec => p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate × Vec => velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate × Vec => velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp (measurable_fst.comp measurable_fst))
  have hH : MeasurableSet H := by
    exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
      ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
        (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))
  have hf : Measurable (fun p : ConeCoordinate × Vec =>
      ENNReal.ofReal (g (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) := by
    exact (hg.comp ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul hn)).prodMk
        measurable_snd))).ennreal_ofReal
  have hm : Measurable (fun z : ConeCoordinate =>
      ∫⁻ v : Vec, H.indicator (fun p => ENNReal.ofReal (g (p.1.2.1,
        (X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2)))) (z,v)) :=
    (hf.indicator hH).lintegral_prod_right'
  convert hm using 1
  all_goals try with_reducible_and_instances rfl
  ext z
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
  apply lintegral_congr
  intro v
  rfl

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


lemma lintegral_add_left_Ioo (s T : ℝ) (f : ℝ → ℝ≥0∞) :
    (∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r)) = ∫⁻ t in Ioo s T, f t := by
  rw [← lintegral_indicator measurableSet_Ioo,← lintegral_indicator measurableSet_Ioo]
  calc
    _ = ∫⁻ r : ℝ, (Ioo s T).indicator f (s+r) := by
      apply lintegral_congr
      intro r
      have he : r∈Ioo 0 (T-s) ↔ s+r∈Ioo s T := by
        simp only [mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith [h.1,h.2]
      by_cases hr : r∈Ioo 0 (T-s)
      · rw [indicator_of_mem hr,indicator_of_mem (he.mp hr)]
      · rw [indicator_of_notMem hr,indicator_of_notMem (mt he.mpr hr)]
    _ = _ := lintegral_add_left_eq_self _ _

lemma lintegral_retarded_triangle (T : ℝ) {f : ℝ × ℝ → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s)) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, f (t,s) := by
  let H : Set (ℝ × ℝ) := {p | 0<p.1 ∧ p.1<p.2 ∧ p.2<T}
  let g : ℝ × ℝ → ℝ≥0∞ := H.indicator (fun p => f (p.2,p.1))
  have hH : MeasurableSet H :=
    (measurableSet_lt measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const))
  have hg : Measurable g := (hf.comp (measurable_snd.prodMk measurable_fst)).indicator hH
  calc
    _ = ∫⁻ s : ℝ, ∫⁻ t : ℝ, g (s,t) := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro s
      by_cases hs : s∈Ioo 0 T
      · rw [indicator_of_mem hs,lintegral_add_left_Ioo s T (fun t => f (t,s)),← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro t
        have he : (s,t)∈H ↔ t∈Ioo s T := by simp only [H,mem_ofPred_eq,mem_Ioo,hs.1,true_and]
        by_cases ht : t∈Ioo s T
        · simp only [g,indicator_of_mem ht,indicator_of_mem (he.mpr ht)]
        · simp only [g,indicator_of_notMem ht,indicator_of_notMem (mt he.mp ht)]
      · rw [indicator_of_notMem hs]
        symm
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro t
        exact indicator_of_notMem (fun hh => hs ⟨hh.1,hh.2.1.trans hh.2.2⟩) _
    _ = ∫⁻ t : ℝ, ∫⁻ s : ℝ, g (s,t) := lintegral_lintegral_swap hg.aemeasurable
    _ = _ := by
      rw [← lintegral_indicator measurableSet_Ioo]
      apply lintegral_congr
      intro t
      by_cases ht : t∈Ioo 0 T
      · rw [indicator_of_mem ht,← lintegral_indicator measurableSet_Ioo]
        apply lintegral_congr
        intro s
        have he : (s,t)∈H ↔ s∈Ioo 0 t := by simp only [H,mem_ofPred_eq,mem_Ioo,ht.2,and_true]
        by_cases hs : s∈Ioo 0 t
        · simp only [g,indicator_of_mem hs,indicator_of_mem (he.mpr hs)]
        · simp only [g,indicator_of_notMem hs,indicator_of_notMem (mt he.mp hs)]
      · rw [indicator_of_notMem ht]
        apply lintegral_eq_zero_of_ae_eq_zero
        apply ae_of_all
        intro s
        exact indicator_of_notMem (fun hh => ht ⟨hh.1.trans hh.2.1,hh.2.2⟩) _

lemma lintegral_retarded_triangle_parameter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (T : ℝ) {f : ℝ × ℝ × Ω → ℝ≥0∞} (hf : Measurable f) :
    (∫⁻ s in Ioo (0:ℝ) T, ∫⁻ n : Ω, ∫⁻ r in Ioo (0:ℝ) (T-s), f (s+r,s,n) ∂volume ∂μ) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ s in Ioo (0:ℝ) t, ∫⁻ n : Ω, f (t,s,n) ∂μ := by
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => f (p.1.1,p.1.2,p.2)) :=
    hf.comp ((measurable_fst.comp measurable_fst).prodMk
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
  calc
    _ = ∫⁻ s in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) (T-s), ∫⁻ n : Ω, f (s+r,s,n) ∂μ := by
      apply setLIntegral_congr_fun measurableSet_Ioo
      intro s _
      have hg : Measurable (fun p : Ω × ℝ => f (s+p.2,s,p.1)) :=
        hf.comp ((measurable_const.add measurable_snd).prodMk
          (measurable_const.prodMk measurable_fst))
      exact lintegral_lintegral_swap hg.aemeasurable
    _ = _ := lintegral_retarded_triangle T hm.lintegral_prod_right'

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_ConeEulerianIntegrand
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
open scoped Topology ContDiff
open Set
open scoped Topology ContDiff RealInnerProductSpace
open Set MeasureTheory
open scoped ENNReal
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma physicalBin_integral_eq_triangle {V : ℝ → Vec} (hV : Measurable V)
    (C : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) {T : ℝ} (hJT : J⊆Icc 0 T)
    {g : ConeCoordinate → ℝ≥0∞} (hg : Measurable g) :
    (∫⁻ z,g z ∂physicalBinMeasure V C J) =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) t, ∫⁻ n : Sphere,
        (physicalBinBase V C J).indicator g (t,r,n) ∂sphereMeasure := by
  have hbase := measurableSet_physicalBinBase hV C hJ
  unfold physicalBinMeasure
  rw [← lintegral_indicator hbase,lintegral_prod _ (hg.indicator hbase).aemeasurable]
  simp_rw [restrict_Ioo_eq_restrict_Icc]
  rw [← lintegral_indicator measurableSet_Icc]
  apply lintegral_congr
  intro t
  have hm : Measurable (fun p : ℝ × Sphere => (physicalBinBase V C J).indicator g (t,p)) :=
    (hg.indicator hbase).comp (measurable_const.prodMk measurable_id)
  by_cases ht : t∈Icc 0 T
  · rw [indicator_of_mem ht,lintegral_prod _ hm.aemeasurable,← lintegral_indicator measurableSet_Icc]
    apply lintegral_congr
    intro r
    by_cases hr : r∈Icc 0 t
    · rw [indicator_of_mem hr]
    · rw [indicator_of_notMem hr]
      apply lintegral_eq_zero_of_ae_eq_zero
      apply ae_of_all
      intro n
      exact indicator_of_notMem (fun hz => hr hz.2.1) _
  · rw [indicator_of_notMem ht]
    apply lintegral_eq_zero_of_ae_eq_zero
    apply ae_of_all
    intro p
    exact indicator_of_notMem (fun hz => ht (hJT hz.1)) _

lemma measurable_coneEulerianIntegrand {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0≤T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    Measurable (coneEulerianIntegrand s T X V H) := by
  have hn : Measurable (fun z : ConeCoordinate => z.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp measurable_snd)
  have hW : Measurable (fun z : ConeCoordinate =>
      ENNReal.ofReal ((z.1-z.2.1)^2*(1-dot z.2.2.1 (velocity (V z.1))))) :=
    (((measurable_fst.sub (measurable_fst.comp measurable_snd)).pow_const 2).mul
      (measurable_const.sub (continuous_dot.measurable.comp
        (hn.prodMk ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst)))))).ennreal_ofReal
  have hk : Measurable (fun p : ConeCoordinate × Vec =>
      H.indicator (fun p => ENNReal.ofReal (prefixParticle s T p))
        (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))) := by
    apply ((hs.continuous_prefixParticle hT).measurable.ennreal_ofReal.indicator hH).comp
    exact (measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
      (((hX.comp (measurable_fst.comp measurable_fst)).sub
        (((measurable_fst.comp measurable_fst).sub
          (measurable_fst.comp (measurable_snd.comp measurable_fst))).smul (hn.comp measurable_fst))).prodMk measurable_snd)
  exact hW.mul hk.lintegral_prod_right'

lemma PhaseFlowOn.cone_occupation_eq_receiver_coordinates {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) {H : Set (ℝ × Phase)} (hH : MeasurableSet H) :
    coneOccupation F.flow zX T s.f H =
      ∫⁻ t in Ioo (0:ℝ) T, ∫⁻ r in Ioo (0:ℝ) t, ∫⁻ n : Sphere,
        coneEulerianIntegrand s T (fun t => (prefixFlow F.flow T zX t).1)
          (fun t => (prefixFlow F.flow T zX t).2) H (t,r,n) ∂sphereMeasure := by
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hg := measurable_coneEulerianIntegrand hs hT hα.fst.measurable hα.snd.measurable hH
  rw [← lintegral_retarded_triangle_parameter sphereMeasure T hg]
  unfold coneOccupation
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro r hr
  apply lintegral_congr
  intro n
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro R hR
  have ht : r+R∈Icc 0 T := ⟨by linarith [hr.1,hR.1],by linarith [hR.2]⟩
  simp only [coneEulerianIntegrand,prefixFlow,prefixClamp_eq ht,add_sub_cancel_left]
  congr 1
  apply lintegral_congr
  intro v
  by_cases hp : (r,((F.flow zX (r+R)).1-R • n.1,v))∈H
  · rw [indicator_of_mem hp,indicator_of_mem hp,prefixParticle,prefixClamp_eq (Ioo_subset_Icc_self hr)]
  · rw [indicator_of_notMem hp,indicator_of_notMem hp]

lemma PhaseFlowOn.physical_bin_point_mem {E B : Field} {T a b c d t r : ℝ}
    (F : PhaseFlowOn E B T) (zX : Phase) (C : ClosedConeBin) (S : Set Phase)
    (n : Sphere) (v : Vec) (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : r∈Ioo 0 T) (hrC : r∈Icc c d) (hrt : r<t) (htT : t<T)
    (hb : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b))
    (hv : v∈coneBinMomentumSet C n.1 (velocity (F.flow zX t).2))
    (hz : inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v))∈S) :
    (r,((F.flow zX t).1-(t-r) • n.1,v))∈closedBinEulerian F.flow zX T C S a b c d := by
  let z := inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v))
  have hflow : F.flow z r=((F.flow zX t).1-(t-r) • n.1,v) :=
    F.flow_inversePhase (Ioo_subset_Icc_self hr) _
  have hR : 0<t-r := sub_pos.mpr hrt
  have hΔ : (F.flow zX t).1-(F.flow z r).1=(t-r) • n.1 := by
    rw [hflow]
    dsimp only
    abel
  have hnorm : t-r=‖(F.flow zX t).1-(F.flow z r).1‖ := by
    rw [hΔ,norm_smul,Real.norm_eq_abs,abs_of_pos hR,sphere_norm,mul_one]
  have hn : (t-r)⁻¹ • ((F.flow zX t).1-(F.flow z r).1)=n.1 := by
    rw [hΔ,smul_smul,inv_mul_cancel₀ hR.ne',one_smul]
  have hbin : InClosedConeBin F.flow zX C t r z := by
    apply (inClosedConeBin_iff hR).mpr
    rw [hn,hflow]
    refine ⟨?_,hb.2.2.1,hv.1,hb.2.2.2.1,hv.2.1,hb.2.2.2.2,hv.2.2⟩
    simpa only [hflow] using hnorm
  have hh : r∈closedBinHits F.flow zX C S a b c d z := ⟨hz,hrC,t,hb.1,hbin⟩
  have ha := F.physical_hit_arrival zX ((F.flow z r).1) hr (hJ hb.1) hrt hnorm htT
  have hd : (r,F.flow z r)∈spaceConeDomain F.flow zX T := by
    refine ⟨hr,?_⟩
    rw [mem_ball,dist_eq_norm']
    linarith [ha.1.2.1]
  have he := (F.mem_closedBinEulerian_iff zX z C S hC).mpr ⟨hh,hd⟩
  simpa only [hflow] using he

lemma PhaseFlowOn.physicalBinDensity_le_Eulerian {s : Solution} {T a b c d t r : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase}
    (hS : tsupport (fun z => s.f (0,z))⊆S) (n : Sphere)
    (hJ : Icc a b⊆Icc 0 T) (hC : Icc c d⊆Icc 0 T)
    (hr : r∈Ioo 0 T) (hrC : r∈Icc c d) (hrt : r<t) (htT : t<T)
    (hb : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b)) :
    physicalBinDensity s (fun t => (F.flow zX t).1) (fun t => (F.flow zX t).2) C t r n ≤
      ∫⁻ v : Vec, (closedBinEulerian F.flow zX T C S a b c d).indicator
        (fun p => ENNReal.ofReal (s.f p)) (r,((F.flow zX t).1-(t-r) • n.1,v)) := by
  unfold physicalBinDensity
  rw [← lintegral_indicator (measurableSet_coneBinMomentumSet C _ _)]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hv : v∈coneBinMomentumSet C n.1 (velocity (F.flow zX t).2)
  · rw [indicator_of_mem hv]
    by_cases hf : s.f (r,((F.flow zX t).1-(t-r) • n.1,v))=0
    · rw [hf,ENNReal.ofReal_zero]
      exact bot_le
    · have hf0 : s.f (0,inversePhase F.flow (r,((F.flow zX t).1-(t-r) • n.1,v)))≠0 := by
        rwa [← F.transport_inverse hs.f_smooth hs.vlasov (Ioo_subset_Icc_self hr)]
      have hz := hS (subset_tsupport _ hf0)
      rw [indicator_of_mem (F.physical_bin_point_mem zX C S n v hJ hC hr hrC hrt htT hb hv hz)]
  · rw [indicator_of_notMem hv]
    exact bot_le

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Continuation_PhysicalBinBasePrefix
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
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

namespace RVM

lemma physicalBinBase_prefix {α : Phase → ℝ → Phase} {T : ℝ} (zX : Phase)
    (C : ClosedConeBin) {J : Set ℝ} (hJ : J⊆Icc 0 T) :
    physicalBinBase (fun t => (prefixFlow α T zX t).2) C J =
      physicalBinBase (fun t => (α zX t).2) C J := by
  ext z
  by_cases hz : z.1∈J
  · simp only [physicalBinBase,mem_ofPred_eq,prefixFlow,prefixClamp_eq (hJ hz)]
  · simp only [physicalBinBase,mem_ofPred_eq,hz,false_and]

lemma PhaseFlowOn.physicalBin_weighted_occupation {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z => s.f (0,z))⊆S)
    (hJ : Icc a b⊆Icc 0 T) (hR : 0≤C.rmin) (hD : 0≤C.Dmin) :
    ENNReal.ofReal (C.rmin^2*C.Dmin) *
      (∫⁻ z : ConeCoordinate,physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C z.1 z.2.1 z.2.2
        ∂physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b)) ≤
      coneOccupation F.flow zX T s.f
        (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) := by
  let c := max 0 (a-C.rmax)
  let d := min T (b-C.rmin)
  let H := closedBinEulerian F.flow zX T C S a b c d
  let X : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).1
  let V : ℝ → Vec := fun t => (prefixFlow F.flow T zX t).2
  let g : ConeCoordinate → ℝ≥0∞ := fun z =>
    physicalBinDensity {s with f := prefixParticle s T} X V C z.1 z.2.1 z.2.2
  have hC : Icc c d⊆Icc 0 T := fun _ hr =>
    ⟨(le_max_left _ _).trans hr.1,hr.2.trans (min_le_left _ _)⟩
  have hH : MeasurableSet H := F.measurable_closedBinEulerian hs hT zX C hS hJ hC
  have hα : Continuous (fun t => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hX : Measurable X := hα.fst.measurable
  have hV : Measurable V := hα.snd.measurable
  have hg : Measurable g := measurable_coneBinDensity
    (hs.continuous_prefixParticle hT).measurable hX hV C
  have hμ : physicalBinMeasure (fun t => (F.flow zX t).2) C (Icc a b) =
      physicalBinMeasure V C (Icc a b) := by
    unfold physicalBinMeasure V
    rw [physicalBinBase_prefix zX C hJ]
  have hgactual (t r : ℝ) (n : Sphere) (ht : t∈Icc 0 T) (hr : r∈Icc 0 T) :
      g (t,r,n)=physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C t r n := by
    simp only [g,physicalBinDensity,X,V,prefixFlow,prefixClamp_eq ht,
      prefixParticle,prefixClamp_eq hr]
  rw [hμ]
  have he : (∫⁻ z : ConeCoordinate,physicalBinDensity s (fun t => (F.flow zX t).1)
        (fun t => (F.flow zX t).2) C z.1 z.2.1 z.2.2 ∂physicalBinMeasure V C (Icc a b)) =
      ∫⁻ z,g z ∂physicalBinMeasure V C (Icc a b) := by
    apply lintegral_congr_ae
    apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV C measurableSet_Icc)
    intro z hz
    exact (hgactual z.1 z.2.1 z.2.2 (hJ hz.1)
      ⟨hz.2.1.1,hz.2.1.2.trans (hJ hz.1).2⟩).symm
  rw [he,physicalBin_integral_eq_triangle hV C measurableSet_Icc hJ hg,
    F.cone_occupation_eq_receiver_coordinates hs hT zX hH]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro t ht
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  apply ae_restrict_of_forall_mem measurableSet_Ioo
  intro r hr
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro n
  dsimp only
  have ht' := Ioo_subset_Icc_self ht
  have hr' : r∈Ioo 0 T := ⟨hr.1,hr.2.trans ht.2⟩
  by_cases hz : (t,r,n)∈physicalBinBase V C (Icc a b)
  · rw [indicator_of_mem hz,hgactual t r n ht' (Ioo_subset_Icc_self hr')]
    have hz' : (t,r,n)∈physicalBinBase (fun t => (F.flow zX t).2) C (Icc a b) := by
      rwa [show V=(fun t => (prefixFlow F.flow T zX t).2) from rfl,
        physicalBinBase_prefix zX C hJ] at hz
    have hrC : r∈Icc c d := by
      constructor
      · exact max_le hr.1.le (by linarith [hz'.1.1,hz'.2.2.1.2])
      · exact le_min hr'.2.le (by linarith [hz'.1.2,hz'.2.2.1.1])
    have hden := F.physicalBinDensity_le_Eulerian hs zX C hS0 n hJ hC hr' hrC hr.2 ht.2 hz'
    have hw : C.rmin^2*C.Dmin ≤ (t-r)^2*(1-dot n.1 (velocity (F.flow zX t).2)) := by
      exact mul_le_mul (sq_le_sq₀ hR (sub_pos.mpr hr.2).le |>.mpr hz'.2.2.1.1)
        hz'.2.2.2.2.1 hD (sq_nonneg _)
    change _ ≤ coneEulerianIntegrand s T X V H (t,r,n)
    have hprefix : coneEulerianIntegrand s T X V H (t,r,n) =
        ENNReal.ofReal ((t-r)^2*(1-dot n.1 (velocity (F.flow zX t).2))) *
          ∫⁻ v : Vec,H.indicator (fun p => ENNReal.ofReal (s.f p))
            (r,((F.flow zX t).1-(t-r) • n.1,v)) := by
      simp only [coneEulerianIntegrand,X,V,prefixFlow,prefixClamp_eq ht']
      congr 1
      apply lintegral_congr
      intro v
      by_cases hp : (r,((F.flow zX t).1-(t-r) • n.1,v))∈H
      · simp only [indicator_of_mem hp,prefixParticle,prefixClamp_eq (Ioo_subset_Icc_self hr')]
      · simp only [indicator_of_notMem hp]
    rw [hprefix]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal hw) hden
  · rw [indicator_of_notMem hz,mul_zero]
    exact bot_le

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

lemma PhaseFlowOn.physicalBin_density_far {s : Solution} {T a b : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0 ≤ T)
    (zX : Phase) (C : ClosedConeBin) {S : Set Phase} (hS : IsCompact S)
    (hS0 : tsupport (fun z=>s.f (0,z))⊆S) (hJ : Icc a b⊆Icc 0 T)
    (hr : 0<C.rmin) (hD : 0<C.Dmin) :
    (∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      C z.1 z.2.1 z.2.2 ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b)) ≤
    coneOccupation F.flow zX T s.f
      (closedBinEulerian F.flow zX T C S a b (max 0 (a-C.rmax)) (min T (b-C.rmin))) /
      ENNReal.ofReal (C.rmin^2*C.Dmin) := by
  have hmass := F.physicalBin_weighted_occupation hs hT zX C hS hS0 hJ hr.le hD.le
  have hμ : physicalBinMeasure (fun t=>(F.flow zX t).2) C (Icc a b)=
      physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b) := by
    unfold physicalBinMeasure
    rw [physicalBinBase_prefix zX C hJ]
  rw [hμ] at hmass
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have he : (∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(F.flow zX t).1) (fun t=>(F.flow zX t).2) C z.1 z.2.1 z.2.2
      ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b))=
      ∫⁻z : ConeCoordinate,physicalBinDensity s
      (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
      C z.1 z.2.1 z.2.2 ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) C (Icc a b) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hα.snd.measurable C measurableSet_Icc)] with z hz
    simp only [physicalBinDensity,prefixFlow,prefixClamp_eq (hJ hz.1)]
  rw [he] at hmass
  apply (ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.mpr (by positivity)).ne')
    (Or.inl ENNReal.ofReal_ne_top)).mpr
  simpa only [mul_comm] using hmass

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

lemma central_far_scalar {C H h p φ R : ℝ} (hC : 0≤C) (hH : 1≤H)
    (hh : 0<h) (hp : 0<p) (hφ : 0<φ) :
    (C*h/p*R^2)/((H*h/2)^2*(φ^2/2))≤(8*C)*(R^2/(p*h*φ^2)) := by
  have hH0 : 0<H := zero_lt_one.trans_le hH
  calc
    _=((8*C)*(R^2/(p*h*φ^2)))/H^2 := by field_simp; ring
    _≤_ := div_le_self (by positivity) (by nlinarith)

lemma Admissible.representative_central_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      512/min (sourceRepresentative (k 0)) w < cappedRepresentative (k 2) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  obtain ⟨Co,hCo,hocc⟩ := hd.representative_shared_occupation T₀
  let C := max (73728*Cρ*max 1 T₀) (8*Co)
  have hC : 0≤C := (by positivity : 0≤73728*Cρ*max 1 T₀).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hactual HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
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
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hf := F.physicalBin_density_far hs.energyPrefix hT zX B hd.2.1 hS0 hJ
    (representativeClosedBin_radius_pos T w k) (by change 0<φ^2/2; positivity)
  have ho := hocc M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hactual HZ
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hn.trans
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
        ((mul_le_mul_of_nonneg_left hHH (by positivity)).trans (le_max_left _ _)) (by positivity))
  · apply hf.trans ((ENNReal.div_le_div_right ho _).trans ?_)
    change ENNReal.ofReal (Co*h/p*R^2)/ENNReal.ofReal ((H*h/2)^2*(φ^2/2))≤_
    rw [←ENNReal.ofReal_div_of_pos (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact (central_far_scalar hCo hH hh hp hφ).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

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

lemma Admissible.representative_central_large_shared {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      min I (stabilityLength P 16384 M A (sourceRepresentative (k 0)) w
        (cappedRepresentative (k 2))) < cappedRepresentative (k 3) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeCentralCost s F zX w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  obtain ⟨Cρ,hCρ,hden⟩ := hd.uniform_physicalBinDensity_constant
  obtain ⟨Co,hCo,hocc⟩ := hd.representative_large_shared_occupation T₀
  let C := max (73728*Cρ*max 1 T₀) (8*Co)
  have hC : 0≤C := (by positivity : 0≤73728*Cρ*max 1 T₀).trans (le_max_left _ _)
  refine ⟨C,hC,?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hsmall hlarge HZ
  dsimp only
  let p := sourceRepresentative (k 0)
  let θ := cappedRepresentative (k 1)
  let φ := cappedRepresentative (k 2)
  let h := cappedRepresentative (k 3)
  let H := max 1 T
  let B := representativeClosedBin T w k
  let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
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
  have hS0 : tsupport (fun z=>s.f (0,z))⊆tsupport d.f₀ := by
    have he : (fun z=>s.f (0,z))=d.f₀ := funext hs.initial_f
    rw [he]
  have hf := F.physicalBin_density_far hs.energyPrefix hT zX B hd.2.1 hS0 hJ
    (representativeClosedBin_radius_pos T w k) (by change 0<φ^2/2; positivity)
  have ho := hocc M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha hb hI hJI hw hlarge
  rw [mul_min_of_nonneg _ _ hC,ENNReal.ofReal_min]
  apply le_min
  · apply hn.trans
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
        ((mul_le_mul_of_nonneg_left hHH (by positivity)).trans (le_max_left _ _)) (by positivity))
  · apply hf.trans ((ENNReal.div_le_div_right ho _).trans ?_)
    change ENNReal.ofReal (Co*h/p*R^2)/ENNReal.ofReal ((H*h/2)^2*(φ^2/2))≤_
    rw [←ENNReal.ofReal_div_of_pos (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    exact (central_far_scalar hCo hH hh hp hφ).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

lemma Admissible.representative_regular_central_shared_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A P : ℝ,0<M → 0≤A → 0<P →
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (k : Fin 4→ℕ) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 0<w →
      cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let p := sourceRepresentative (k 0)
      let θ := cappedRepresentative (k 1)
      let φ := cappedRepresentative (k 2)
      let h := cappedRepresentative (k 3)
      let R := representativeSharedRadius s F zX P M A w a b I (k 0,k 2)
      representativeRegularCentralCost s F zX P M A I w k a b≤
        ENNReal.ofReal (C*min (I*h*p^3*θ^2*φ^2) (R^2/(p*h*φ^2))) := by
  classical
  obtain ⟨Ca,hCa,ha⟩ := hd.representative_central_shared T₀
  obtain ⟨Cr,hCr,hr⟩ := hd.representative_central_large_shared T₀
  refine ⟨max Ca Cr,hCa.trans (le_max_left _ _),?_⟩
  intro M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall HZ
  dsimp only
  unfold representativeRegularCentralCost
  split_ifs with h
  · rcases h with h|h
    · apply (ha M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall h HZ).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      exact le_min (by dsimp [sourceRepresentative,cappedRepresentative]; positivity) (by dsimp [sourceRepresentative,cappedRepresentative]; positivity)
    · apply (hr M A P hM hA hP s T F hs hT hTT zX k a b I w hzX ha0 hb hI hJI hw hsmall h HZ).trans
      apply ENNReal.ofReal_le_ofReal
      apply mul_le_mul_of_nonneg_right (le_max_right _ _)
      exact le_min (by dsimp [sourceRepresentative,cappedRepresentative]; positivity) (by dsimp [sourceRepresentative,cappedRepresentative]; positivity)
  · exact bot_le

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.representative_regular_central_shared_oai := @OAI.RVM.Admissible.representative_regular_central_shared_oai
