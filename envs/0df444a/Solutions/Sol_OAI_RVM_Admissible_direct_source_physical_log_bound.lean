-- Prove2me | solution 1 for OAI.RVM.Admissible.direct_source_physical_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:43:19.547769+00:00
-- url     : https://prove2.me/submissions/8b4f0930-f231-428f-89cd-2b2ebcd68344

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direct_source_remaining_all_radii
import Theorems.Thm_OAI_RVM_Admissible_direct_source_small_all_radii

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

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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

lemma hasDerivAt_particle_energy {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => q (V t)) (dot (velocity (V s)) K) s := by
  have hp : 1+‖V s‖^2 ≠ 0 := ne_of_gt (by positivity)
  have h := ((hV.norm_sq).const_add 1).sqrt hp
  convert h using 1 <;> try rfl
  rw [velocity, dot_smul_left, dot_eq_inner]
  dsimp [q]
  have hq : Real.sqrt (1+‖V s‖^2) ≠ 0 := ne_of_gt (q_pos (V s))
  field_simp

lemma hasDerivAt_particle_velocity {V : ℝ → Vec} {K : Vec} {s : ℝ}
    (hV : HasDerivAt V K s) :
    HasDerivAt (fun t => velocity (V t))
      ((q (V s))⁻¹ • (K-dot (velocity (V s)) K • velocity (V s))) s := by
  have hq := hasDerivAt_particle_energy hV
  have h := (hq.inv (ne_of_gt (q_pos (V s)))).smul hV
  convert h using 1 <;> try rfl
  ext i
  simp only [Pi.inv_apply, velocity, PiLp.sub_apply, PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  ring

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

lemma fderiv_velocity_apply (v h : Vec) :
    fderiv ℝ velocity v h = (q v)⁻¹ • (h-dot (velocity v) h • velocity v) := by
  have hc : HasDerivAt (fun r : ℝ => v+r • h) h 0 := by
    have hh := (hasDerivAt_const (0 : ℝ) v).add
      ((hasDerivAt_id (0 : ℝ)).smul_const h)
    change HasDerivAt (fun r : ℝ => v+r • h) (0+(1 : ℝ) • h) 0 at hh
    simpa only [zero_add, one_smul] using hh
  have hv : HasFDerivAt velocity (fderiv ℝ velocity v) (v+(0 : ℝ) • h) := by
    simpa only [zero_smul, add_zero] using
      (contDiff_velocity.differentiable (by simp : (1 : ℕ∞ω) ≠ 0) v).hasFDerivAt
  have h₁ := hv.comp_hasDerivAt 0 hc
  have h₂ := hasDerivAt_particle_velocity hc
  have he := h₁.unique h₂
  simpa using he

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

lemma abs_dot_le (a b : Vec) : |dot a b| ≤ ‖a‖*‖b‖ := by
  rw [dot_eq_inner]
  exact abs_real_inner_le_norm a b

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

lemma EnergyPrefix.continuous_prefixParticle {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0 ≤ T) : Continuous (prefixParticle s T) :=
  hs.f_smooth.continuousOn.comp_continuous
    ((continuous_const.max (continuous_const.min continuous_fst)).prodMk continuous_snd)
    (fun p => ⟨prefixClamp_mem hT p.1,mem_univ _⟩)

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_RealJointEnergyBudget
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
open Set
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal ENNReal
open scoped Topology ContDiff
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff ENNReal

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma relative_angle_identity (v w : Vec) :
    2*(1-dot (velocity w) (velocity v)) =
      ‖velocity v-velocity w‖^2+(q v)⁻¹^2+(q w)⁻¹^2 :=  by
  rw [norm_sub_sq_real,← dot_eq_inner,← dot_self (velocity v),
    ← dot_self (velocity w),velocity_self,velocity_self,dot_comm (velocity v)]
  ring

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

lemma dyadicFactor_eventually_zero {x : ℝ} (hx : 0<x) :
    ∃ N : ℕ, ∀ n, N≤n → ∀ y, x/2<y → dyadicFactor n y=0 := by
  obtain ⟨N,hN⟩ := pow_unbounded_of_one_lt (4/x) (by norm_num : (1:ℝ)<2)
  refine ⟨N,fun n hn y hy => dyadicFactor_zero_large ?_⟩
  have hpow := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hn
  have hN' : 4<(2:ℝ)^N*x := (div_lt_iff₀ hx).mp hN
  have hp : 0<(2:ℝ)^n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right hpow hx.le]

lemma tsum_dyadicFactor {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    ∑' n : ℕ, dyadicFactor n x=1 := by
  obtain ⟨N,hN⟩ := dyadicFactor_eventually_zero hx
  have hz (n : ℕ) (hn : n ∉ Finset.range N) : dyadicFactor n x=0 :=
    hN n (Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)) x (by linarith)
  rw [tsum_eq_sum (s:=Finset.range N) hz,sum_dyadicFactor,dyadicCut_one hx1]
  have hN' := hN N le_rfl (x/2+ x/4) (by linarith)
  obtain ⟨M,hM⟩ := pow_unbounded_of_one_lt (2/x) (by norm_num : (1:ℝ)<2)
  have hm : 2≤(2:ℝ)^(max N M)*x :=
    ((div_lt_iff₀ hx).mp hM).le.trans
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (le_max_right N M)) hx.le)
  have he := sum_dyadicFactor (max N M) x
  have hs : ∑ n ∈ Finset.range (max N M), dyadicFactor n x =
      ∑ n ∈ Finset.range N, dyadicFactor n x := by
    symm
    apply Finset.sum_subset (Finset.range_mono (le_max_left N M))
    intro n _ hn
    exact hz n hn
  rw [hs,sum_dyadicFactor,dyadicCut_one hx1,dyadicCut_zero hm,sub_zero] at he
  exact he

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

lemma measurableSet_trianglePhaseDomain (T : ℝ) : MeasurableSet (trianglePhaseDomain T) :=
  ((measurable_fst.fst measurableSet_Ioo).inter
    ((measurableSet_lt measurable_const measurable_fst.snd.fst).inter
      (measurableSet_lt measurable_fst.snd.fst measurable_fst.fst)))

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

lemma source_angle_coordinate_lower (v n : Vec) (hn : ‖n‖=1) :
    1/2≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by
  have hq := q_pos v
  have hv := norm_velocity_lt_one v
  have hdot := dot_le_norm n (velocity v)
  rw [hn,one_mul] at hdot
  have hs := velocity_self v
  rw [dot_self] at hs
  have hinv : (q v)^2*((q v)⁻¹)^2=1 := by field_simp
  have hd : ((q v)⁻¹)^2≤2*(1-dot n (velocity v)) := by
    nlinarith [sq_nonneg (1-‖velocity v‖)]
  have hdq := mul_le_mul_of_nonneg_left hd (sq_nonneg (q v))
  rw [hinv] at hdq
  have hroot := Real.sq_sqrt (div_nonneg (cone_denom_pos v n hn).le (by norm_num : (0:ℝ)≤2))
  have hp : 0≤q v*Real.sqrt ((1-dot n (velocity v))/2) := by positivity
  have hsq : 1≤4*(q v*Real.sqrt ((1-dot n (velocity v))/2))^2 := by
    nlinarith [sq_nonneg (q v)]
  nlinarith

lemma source_energy_index_lt {n N : ℕ} {v : Vec}
    (h : DyadicBand n (1/q v)) (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hr := (dyadicBand_source_range h).1
  dsimp [sourceRepresentative] at hr
  nlinarith [q_pos v]

lemma source_angle_index_lt {n N : ℕ} {v nu : Vec} (hnu : ‖nu‖=1)
    (h : DyadicBand n (Real.sqrt ((1-dot nu (velocity v))/2)))
    (hP : 1024*q v≤(2:ℝ)^N) : n<N := by
  by_contra hc
  have hn : N≤n := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^n := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right (hP.trans hpow)
    (Real.sqrt_nonneg ((1-dot nu (velocity v))/2))
  have hl := source_angle_coordinate_lower v nu hnu
  nlinarith [h.2]

lemma physicalCutoff_positive_source_indices {T r : ℝ} {v w n : Vec} {k : Fin 4→ℕ} {N : ℕ}
    (hn : ‖n‖=1) (hP : 1024*q v≤(2:ℝ)^N)
    (hk : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v w)) :
    k 0<N ∧ k 1<N := by
  have hb := dyadicMultiFactor_positive_bands hk
  exact ⟨source_energy_index_lt (hb 0) hP,source_angle_index_lt hn (hb 1) hP⟩

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
open scoped Topology ContDiff
open scoped Topology ContDiff ENNReal
open scoped Topology ContDiff NNReal
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_RelativeAngleCoordinate
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

lemma relative_deficit_pos (v w : Vec) : 0<1-dot (velocity w) (velocity v) := by
  have hd := dot_le_norm (velocity w) (velocity v)
  have hm := mul_le_mul_of_nonneg_right (norm_velocity_lt_one w).le (norm_nonneg (velocity v))
  rw [one_mul] at hm
  linarith [norm_velocity_lt_one v]

lemma relativeAngleCoordinate_pos (v w : Vec) : 0 < relativeAngleCoordinate v w := by
  exact Real.sqrt_pos.mpr (div_pos (relative_deficit_pos v w) (by norm_num))

lemma relativeAngleCoordinate_le_one (v w : Vec) : relativeAngleCoordinate v w≤1 := by
  apply (Real.sqrt_le_iff).mpr
  constructor
  · norm_num
  · linarith [(velocity_deficit_mem_unit2 v w).2]

lemma relativeAngleCoordinate_lower (v w : Vec) : 1/2≤q v*relativeAngleCoordinate v w := by
  have hq := q_pos v
  have hv := norm_velocity_lt_one v
  have hdot : dot (velocity w) (velocity v)≤‖velocity v‖ := by
    calc
      _ ≤ ‖velocity w‖*‖velocity v‖ := dot_le_norm _ _
      _ ≤ 1*‖velocity v‖ := mul_le_mul_of_nonneg_right (norm_velocity_lt_one w).le (norm_nonneg _)
      _ = _ := one_mul _
  have hs := velocity_self v
  rw [dot_self] at hs
  have hinv : (q v)^2*((q v)⁻¹)^2=1 := by field_simp
  have hd : ((q v)⁻¹)^2≤2*(1-dot (velocity w) (velocity v)) := by
    nlinarith [sq_nonneg (1-‖velocity v‖)]
  have hdq := mul_le_mul_of_nonneg_left hd (sq_nonneg (q v))
  rw [hinv] at hdq
  have hroot := Real.sq_sqrt (div_nonneg (relative_deficit_pos v w).le (by norm_num : (0:ℝ)≤2))
  have hp : 0≤q v*relativeAngleCoordinate v w := mul_nonneg hq.le (relativeAngleCoordinate_pos _ _).le
  have hsq : 1≤4*(q v*relativeAngleCoordinate v w)^2 := by
    dsimp [relativeAngleCoordinate]
    nlinarith [sq_nonneg (q v)]
  nlinarith

lemma relative_angle_index_lt {j N : ℕ} {v w : Vec}
    (h : DyadicBand j (relativeAngleCoordinate v w)) (hP : 1024*q v≤(2:ℝ)^N) : j<N := by
  by_contra hc
  have hn : N≤j := Nat.le_of_not_gt hc
  have hpow : (2:ℝ)^N≤(2:ℝ)^j := pow_le_pow_right₀ (by norm_num) hn
  have hm := mul_le_mul_of_nonneg_right (hP.trans hpow) (relativeAngleCoordinate_pos v w).le
  have hl := relativeAngleCoordinate_lower v w
  nlinarith [h.2]

lemma relativePhysicalFactor_positive_closedBin {T w t σ : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} (ht : t∈J) (hσ : σ∈Icc 0 t) (hband : q (V t)∈Icc (w/8) (8*w))
    {k : Fin 4→ℕ} {j : ℕ} {n : Sphere} {v : Vec}
    (hk : 0 < relativePhysicalFactor T (t-σ) n.1 v (V t) k j) :
    (t,σ,n)∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J ∧
      v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n.1 (velocity (V t)) := by
  have h1 : 0<dyadicMultiFactor k (physicalCutoffCoordinates T (t-σ) n.1 v (V t)) :=
    pos_of_mul_pos_left hk (dyadicFactor_nonneg _ _)
  have h2 : 0<dyadicFactor j (relativeAngleCoordinate v (V t)) :=
    pos_of_mul_pos_right hk (dyadicMultiFactor_nonneg _ _)
  have hmem := physicalCutoff_positive_closedBin ht hσ hband h1
  have hrelative := dyadicBand_angular_range (relative_deficit_pos v (V t)).le
    (dyadicFactor_tsupport (subset_tsupport _ (ne_of_gt h2)))
  exact ⟨hmem.1,hmem.2.1,hmem.2.2.1,hrelative⟩

lemma relativePhysicalFactor_positive_indices {T r : ℝ} {v w n : Vec}
    {k : Fin 4→ℕ} {j N : ℕ} (hn : ‖n‖=1) (hP : 1024*q v≤(2:ℝ)^N)
    (hk : 0 < relativePhysicalFactor T r n v w k j) : k 0<N ∧ k 1<N ∧ j<N := by
  have h1 : 0<dyadicMultiFactor k (physicalCutoffCoordinates T r n v w) :=
    pos_of_mul_pos_left hk (dyadicFactor_nonneg _ _)
  have h2 : 0<dyadicFactor j (relativeAngleCoordinate v w) :=
    pos_of_mul_pos_right hk (dyadicMultiFactor_nonneg _ _)
  have hbase := physicalCutoff_positive_source_indices hn hP h1
  exact ⟨hbase.1,hbase.2,relative_angle_index_lt
    (dyadicFactor_tsupport (subset_tsupport _ (ne_of_gt h2))) hP⟩

lemma exists_relative_dyadic_positive (v w : Vec) :
    ∃j : ℕ,0<dyadicFactor j (relativeAngleCoordinate v w) := by
  by_contra hn
  push Not at hn
  have hz (j : ℕ) : dyadicFactor j (relativeAngleCoordinate v w)=0 :=
    le_antisymm (hn j) (dyadicFactor_nonneg _ _)
  have hh := tsum_dyadicFactor (relativeAngleCoordinate_pos v w) (relativeAngleCoordinate_le_one v w)
  simp_rw [hz] at hh
  norm_num at hh

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

lemma measurable_forceSourceFamily {α : Type*} [MeasurableSpace α]
    {r : α→ℝ} {n a v b : α→Vec} (hr : Measurable r) (hn : Measurable n)
    (ha : Measurable a) (hv : Measurable v) (hb : Measurable b) :
    Measurable (fun x=>forceSourceKernel (r x) (n x) (a x) (v x) (b x)) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hd : Measurable (fun x=>1-dot (n x) (velocity (v x))) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hu))
  have hD : Measurable (fun x=>1-dot (n x) (a x)) :=
    measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk ha))
  have hN : Measurable (fun x=>sourceNumerator (n x) (velocity (v x)) (b x)) :=
    ((continuous_dot.measurable.comp (hn.prodMk hb)).smul (hn.sub hu)).sub (hd.smul hb)
  unfold forceSourceKernel receiverQ
  exact ((hr.mul (hd.pow_const 2)).inv.smul
    ((hD.smul hN).add ((continuous_dot.measurable.comp (ha.prodMk hN)).smul hn)))

lemma measurable_lorentz_acceleration {α : Type*} [MeasurableSpace α]
    {v E B : α→Vec} (hv : Measurable v) (hE : Measurable E) (hB : Measurable B) :
    Measurable (fun x=>fderiv ℝ velocity (v x) (E x+cross (velocity (v x)) (B x))) := by
  have hu := (contDiff_velocity (k:=0)).continuous.measurable.comp hv
  have hq := (contDiff_q (k:=0)).continuous.measurable.comp hv
  have hK := hE.add ((contDiff_cross (k:=0)).continuous.measurable.comp (hu.prodMk hB))
  simp_rw [fderiv_velocity_apply]
  exact hq.inv.smul (hK.sub ((continuous_dot.measurable.comp (hu.prodMk hK)).smul hu))

end RVM

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

lemma cone_relative_deficit_triangle (v w n : Vec) (hn : ‖n‖=1) :
    1-dot (velocity w) (velocity v)≤2*((1-dot n (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity v)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity w))) ∧
    1-dot n (velocity w)≤2*((1-dot (velocity w) (velocity v))+(1-dot n (velocity v))) := by
  have hi := relative_angle_identity v w
  have hv := cone_angle_identity v n hn
  have hw := cone_angle_identity w n hn
  have hab : ‖velocity v-velocity w‖≤‖n-velocity v‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(n-velocity v)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(n-velocity v)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hna : ‖n-velocity v‖≤‖velocity v-velocity w‖+‖n-velocity w‖ := by
    calc
      _ = ‖-(velocity v-velocity w)+(n-velocity w)‖ := by congr 1; abel
      _ ≤ ‖-(velocity v-velocity w)‖+‖n-velocity w‖ := norm_add_le _ _
      _ = _ := by rw [norm_neg]
  have hnb : ‖n-velocity w‖≤‖velocity v-velocity w‖+‖n-velocity v‖ := by
    calc
      _ = ‖(velocity v-velocity w)+(n-velocity v)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hsq {a b c : ℝ} (ha : 0≤a) (h : a≤b+c) : a^2≤2*(b^2+c^2) := by
    have hbc : 0≤b+c := ha.trans h
    have hh := mul_self_le_mul_self ha h
    nlinarith [sq_nonneg (b-c)]
  have hab2 := hsq (norm_nonneg _) hab
  have hna2 := hsq (norm_nonneg _) hna
  have hnb2 := hsq (norm_nonneg _) hnb
  refine ⟨?_,?_,?_⟩ <;>
    nlinarith [sq_nonneg ((q v)⁻¹),sq_nonneg ((q w)⁻¹)]

lemma cone_relative_bin_triangle {v w n : Vec} {θ φ σ : ℝ} (hn : ‖n‖=1)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) :
    σ^2≤32*(θ^2+φ^2) ∧ θ^2≤32*(σ^2+φ^2) ∧ φ^2≤32*(σ^2+θ^2) := by
  obtain ⟨he,hd,hD⟩ := cone_relative_deficit_triangle v w n hn
  constructor
  · linarith
  constructor <;> linarith

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

lemma measurableSet_coneMomentumFiber {V : ℝ→Vec} (hV : Measurable V) (B : ClosedConeBin) :
    MeasurableSet {p : ConeCoordinate×Vec | p.2∈coneBinMomentumSet B p.1.2.2.1 (velocity (V p.1.1))} := by
  have hn : Measurable (fun p : ConeCoordinate×Vec=>p.1.2.2.1) :=
    measurable_subtype_coe.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hv : Measurable (fun p : ConeCoordinate×Vec=>velocity p.2) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp measurable_snd
  have ha : Measurable (fun p : ConeCoordinate×Vec=>velocity (V p.1.1)) :=
    (contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp measurable_fst.fst)
  exact (measurableSet_Icc.preimage ((contDiff_q (k:=0)).continuous.measurable.comp measurable_snd)).inter
    ((measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (hn.prodMk hv)))).inter
      (measurableSet_Icc.preimage (measurable_const.sub (continuous_dot.measurable.comp (ha.prodMk hv)))))

lemma measurableSet_physicalBinPhaseSet {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (physicalBinPhaseSet V B J) :=
  ((measurableSet_physicalBinBase hV B hJ).preimage measurable_fst).inter
    (measurableSet_coneMomentumFiber hV B)

lemma physicalBinPhase_integral {V : ℝ→Vec} (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻p in physicalBinPhaseSet V B J,g p ∂trianglePhaseMeasure)=
      ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        g (z,v) ∂volume ∂physicalBinMeasure V B J := by
  classical
  rw [←lintegral_indicator (measurableSet_physicalBinPhaseSet hV B hJ)]
  rw [trianglePhaseMeasure,lintegral_prod _ (hg.indicator (measurableSet_physicalBinPhaseSet hV B hJ)).aemeasurable]
  rw [physicalBinMeasure,←lintegral_indicator (measurableSet_physicalBinBase hV B hJ)]
  apply lintegral_congr
  intro z
  by_cases hz : z∈physicalBinBase V B J
  · rw [indicator_of_mem hz,←lintegral_indicator (measurableSet_coneBinMomentumSet B _ _)]
    apply lintegral_congr
    intro v
    by_cases hv : v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1))
    · rw [indicator_of_mem (show (z,v)∈physicalBinPhaseSet V B J from ⟨hz,hv⟩),indicator_of_mem hv]
    · rw [indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hv h.2),indicator_of_notMem hv]
  · rw [indicator_of_notMem hz]
    apply lintegral_eq_zero_of_ae_eq_zero
    exact ae_of_all _ (fun v=>indicator_of_notMem (show (z,v)∉physicalBinPhaseSet V B J from fun h=>hz h.1) _)

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_GeneralDirectRadial
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

lemma relativeRepresentative_source_angle {T w : ℝ} {k : Fin 4→ℕ} {j : ℕ}
    {v n a : Vec} (hn : ‖n‖=1)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) n a) :
    1 ≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) := by
  have he := source_angle_coordinate_lower v n hn
  have hθ := cappedRepresentative_pos (k 1)
  have hq := q_pos v
  have hhi : 1-dot n (velocity v)≤8*(cappedRepresentative (k 1))^2 := hv.2.1.2
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    linarith only [hhi]
  have hqθ : 1/2≤2*q v*cappedRepresentative (k 1) :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  have hp : q v ≤ sourceRepresentative (k 0)/32 := hv.1.2
  nlinarith only [mul_le_mul_of_nonneg_right hp hθ.le,hqθ]

lemma cone_relative_bin_small {v w n : Vec} {θ φ σ : ℝ}
    (hn : ‖n‖=1) (hθ : 0≤θ) (hφ : 0≤φ) (hσ : 0≤σ) (hsep : 16*θ≤φ)
    (hdlo : θ^2/2≤1-dot n (velocity v)) (hdhi : 1-dot n (velocity v)≤8*θ^2)
    (hDlo : φ^2/2≤1-dot n (velocity w)) (hDhi : 1-dot n (velocity w)≤8*φ^2)
    (helo : σ^2/2≤1-dot (velocity w) (velocity v))
    (hehi : 1-dot (velocity w) (velocity v)≤8*σ^2) : φ/8≤σ ∧ σ≤8*φ := by
  obtain ⟨he,_,hD⟩ := cone_relative_bin_triangle hn hdlo hdhi hDlo hDhi helo hehi
  have hsq := mul_self_le_mul_self (show 0≤16*θ by positivity) hsep
  constructor <;> nlinarith

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma relativeRepresentative_nonempty_geometry {T w : ℝ} {V : ℝ→Vec}
    {J : Set ℝ} {k : Fin 4→ℕ} {j : ℕ} {z : ConeCoordinate} {v : Vec}
    (hz : z∈physicalBinBase V (relativeRepresentativeClosedBin T w k j) J)
    (hv : v∈coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))) :
    1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) ∧
      (16*cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) →
        cappedRepresentative (k 2)≤8*cappedRepresentative j) := by
  refine ⟨relativeRepresentative_source_angle (sphere_norm z.2.2) hv,?_⟩
  intro hsep
  have h := cone_relative_bin_small (sphere_norm z.2.2)
    (cappedRepresentative_pos (k 1)).le (cappedRepresentative_pos (k 2)).le
    (cappedRepresentative_pos j).le hsep hv.2.1.1 hv.2.1.2
    hz.2.2.2.2.1 hz.2.2.2.2.2 hv.2.2.1 hv.2.2.2
  linarith only [h.1]

lemma physicalDirectSource_integral_geometry_zero (s : Solution) {T w : ℝ}
    {X V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    {k : Fin 4→ℕ} {j : ℕ}
    (hbad : ¬(1≤ sourceRepresentative (k 0)*cappedRepresentative (k 1) ∧
      (16*cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) →
        cappedRepresentative (k 2)≤8*cappedRepresentative j))) :
    (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (relativeRepresentativeClosedBin T w k j) z
      ∂physicalBinMeasure V (relativeRepresentativeClosedBin T w k j) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  have hempty : coneBinMomentumSet (relativeRepresentativeClosedBin T w k j) z.2.2.1 (velocity (V z.1))=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    exact hbad (relativeRepresentative_nonempty_geometry hz hv)
  simp only [physicalDirectSourceDensity,hempty,Measure.restrict_empty,lintegral_zero_measure,mul_zero,Pi.zero_apply]

lemma Admissible.direct_source_all_radii {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (np nθ nφ j : ℕ) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a ≤ b → b-a ≤ (w/P)^2 →
      0 < M → 0 ≤ A → 1≤P → 1 ≤ Real.log (2+P) → 1≤w → w≤P →
      sourceRepresentative np≤128*P →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let B := fun nr=>relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'nr : ℕ,∫⁻z : ConeCoordinate,physicalDirectSourceDensity s X V (B nr) z
        ∂physicalBinMeasure V (B nr) (Icc a b)) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  obtain ⟨Cr,hCr,hr⟩ := hd₀.direct_source_remaining_all_radii
  obtain ⟨Cs,hCs,hs'⟩ := hd₀.direct_source_small_all_radii
  refine ⟨Cr+Cs,add_nonneg hCr hCs,?_⟩
  intro s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
    hM hA hP hL hw hwP hpP HX HZ
  dsimp only
  have hE : 0≤∫x : Vec,totalEnergy s (0,x) := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  by_cases hremaining : cappedRepresentative nφ≤16*cappedRepresentative nθ
  · have hn := hr s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
      hM hA hP hL hw0 hwP hpP hremaining HX HZ
    apply hn.trans
    apply ENNReal.ofReal_le_ofReal
    have hroot : 1≤Real.sqrt w := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hw
    calc
      _ = Cr*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*1*Real.log (2+P) := by ring
      _ ≤ _ := by gcongr; exact le_add_of_nonneg_right hCs
  · have hsep : 16*cappedRepresentative nθ ≤ cappedRepresentative nφ := le_of_lt (lt_of_not_ge hremaining)
    by_cases hgeometry : 1≤ sourceRepresentative np*cappedRepresentative nθ ∧ cappedRepresentative nφ≤8*cappedRepresentative j
    · have hθφ : cappedRepresentative nθ ≤ cappedRepresentative nφ := by
        linarith [cappedRepresentative_pos nθ]
      have hn := hs' s T F hs hT h0 zX S np nθ nφ j a b w M A P hS hS0 ha hb hab hJI
        hM hA hP hL hw hwP hpP hθφ hgeometry.2 hgeometry.1 HX HZ
      apply hn.trans
      apply ENNReal.ofReal_le_ofReal
      gcongr
      exact le_add_of_nonneg_left hCr
    · have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
        ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
      have hz (nr : ℕ) : (∫⁻z : ConeCoordinate,physicalDirectSourceDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
          (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2)
            (relativeRepresentativeClosedBin T w ![np,nθ,nφ,nr] j) (Icc a b))=0 := by
        apply physicalDirectSource_integral_geometry_zero s hV measurableSet_Icc
        intro h
        exact hgeometry ⟨h.1,h.2 hsep⟩
      simp_rw [hz,tsum_zero]
      exact bot_le

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_DirectForce
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

lemma exists_dyadicFactor_positive {x : ℝ} (hx : 0<x) (hx1 : x≤1) :
    ∃n : ℕ,0<dyadicFactor n x := by
  by_contra hn
  push Not at hn
  have hz (n : ℕ) : dyadicFactor n x=0 := le_antisymm (hn n) (dyadicFactor_nonneg _ _)
  have hh := tsum_dyadicFactor hx hx1
  simp_rw [hz] at hh
  simp at hh

lemma exists_dyadicMultiFactor_positive {ι : Type*} [Fintype ι] {x : ι→ℝ}
    (hx : ∀i,0<x i) (hx1 : ∀i,x i≤1) : ∃k : ι→ℕ,0<dyadicMultiFactor k x := by
  choose k hk using fun i=>exists_dyadicFactor_positive (hx i) (hx1 i)
  exact ⟨k,Finset.prod_pos (fun i _=>hk i)⟩

lemma physical_direct_finite_cover {T w P t σ : ℝ} {V : ℝ→Vec} {J : Set ℝ}
    {N : ℕ} (hP : 0≤P) (hwP : w≤P) (hN : 8192*P≤(2:ℝ)^N)
    (ht : t∈J) (htT : t≤T) (hσ : σ∈Ico 0 t)
    (hband : q (V t)∈Icc (w/8) (8*w)) (n : Sphere) (v : Vec) (hq : q v≤P) :
    ∃i : DirectOuterIndex N, ∃nr : ℕ,
      sourceRepresentative (i 0).val≤128*P ∧
      (t,σ,n)∈physicalBinBase V (directOuterBin T w i nr) J ∧
      v∈coneBinMomentumSet (directOuterBin T w i nr) n.1 (velocity (V t)) := by
  have hr : 0<t-σ := sub_pos.mpr hσ.2
  have hrT : t-σ≤ max 1 T := by linarith [le_max_right (1:ℝ) T,hσ.1]
  obtain ⟨k,hk⟩ := exists_dyadicMultiFactor_positive
    (physicalCutoffCoordinates_pos (v:=v) (w:=V t) (sphere_norm n) hr)
    (physicalCutoffCoordinates_le_one (v:=v) (w:=V t) (sphere_norm n) hrT)
  obtain ⟨j,hj⟩ := exists_relative_dyadic_positive v (V t)
  have hrel : 0 < relativePhysicalFactor T (t-σ) n.1 v (V t) k j := mul_pos hk hj
  have hvN : 1024*q v≤(2:ℝ)^N := by linarith only [hq,hP,hN]
  have hidx := relativePhysicalFactor_positive_indices (sphere_norm n) hvN hrel
  have hW : 1024*q (V t)≤(2:ℝ)^N := by linarith only [hband.2,hwP,hN]
  have hnf : k 2<N := source_angle_index_lt (sphere_norm n)
    (show DyadicBand (k 2) (Real.sqrt ((1-dot n.1 (velocity (V t)))/2)) from
      dyadicMultiFactor_positive_bands hk 2) hW
  let i : DirectOuterIndex N := ![⟨k 0,hidx.1⟩,⟨k 1,hidx.2.1⟩,⟨k 2,hnf⟩,⟨j,hidx.2.2⟩]
  have he : ![(i 0).val,(i 1).val,(i 2).val,k 3]=k := by
    funext l
    fin_cases l <;> rfl
  have hmem := relativePhysicalFactor_positive_closedBin ht ⟨hσ.1,hσ.2.le⟩ hband hrel
  refine ⟨i,k 3,?_,?_,?_⟩
  · have hlo : sourceRepresentative (k 0)/128≤q v := hmem.2.1.1
    change sourceRepresentative (k 0)≤128*P
    linarith only [hlo,hq]
  · simpa only [directOuterBin,he,show (i 3).val=j from rfl] using hmem.1
  · simpa only [directOuterBin,he,show (i 3).val=j from rfl] using hmem.2

lemma physicalBinFamily_cover_lintegral {ι : Type*} [Countable ι]
    {V : ℝ→Vec} (hV : Measurable V) {J : Set ℝ} (hJ : MeasurableSet J)
    (B : ι→ClosedConeBin) (R : Set ι) {g : TrianglePhase→ℝ≥0∞} (hg : Measurable g)
    (hcover : ∀p,g p≠0→∃i∈R,p∈physicalBinPhaseSet V (B i) J) :
    (∫⁻p,g p ∂trianglePhaseMeasure)≤
      ∑'i : ι,R.indicator (fun i=>
        ∫⁻z : ConeCoordinate,∫⁻v in coneBinMomentumSet (B i) z.2.2.1 (velocity (V z.1)),
          g (z,v) ∂volume ∂physicalBinMeasure V (B i) J) i := by
  classical
  let f : ι→TrianglePhase→ℝ≥0∞ := fun i=>
    if i∈R then (physicalBinPhaseSet V (B i) J).indicator g else 0
  have hm (i : ι) : Measurable (f i) := by
    dsimp only [f]
    split_ifs
    · exact hg.indicator (measurableSet_physicalBinPhaseSet hV _ hJ)
    · exact measurable_const
  calc
    _ ≤ ∫⁻p,∑'i : ι,f i p ∂trianglePhaseMeasure := by
      apply lintegral_mono
      intro p
      by_cases hp : g p=0
      · rw [hp]; exact bot_le
      · obtain ⟨i,hi,hpi⟩ := hcover p hp
        calc
          _ = f i p := by simp only [f,ite_eq_left hi,indicator_of_mem hpi]
          _ ≤ _ := ENNReal.le_tsum (f := fun index => f index p) i
    _ = ∑'i : ι,∫⁻p,f i p ∂trianglePhaseMeasure := lintegral_tsum (fun i=>(hm i).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro i
      by_cases hi : i∈R
      · simp only [f,ite_eq_left hi,indicator_of_mem hi]
        rw [lintegral_indicator (measurableSet_physicalBinPhaseSet hV _ hJ),physicalBinPhase_integral hV _ hJ hg]
      · simp only [f,ite_eq_right hi,Pi.zero_apply,lintegral_zero,indicator_of_notMem hi]

lemma directOuter_family_sum_bound {N : ℕ} {P : ℝ}
    (f : DirectOuterIndex N→ℕ→ℝ≥0∞) (C : ℝ≥0∞)
    (hf : ∀i,sourceRepresentative (i 0).val≤128*P→(∑'nr,f i nr)≤C) :
    (∑'i : DirectOuterIndex N×ℕ,
      {i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P}.indicator
        (fun i=>f i.1 i.2) i) ≤ (N:ℝ≥0∞)^4*C := by
  classical
  rw [ENNReal.tsum_prod']
  calc
    _ ≤ ∑'i : DirectOuterIndex N,C := by
      apply ENNReal.tsum_le_tsum
      intro i
      change (∑'nr,if sourceRepresentative (i 0).val≤128*P then f i nr else 0)≤C
      by_cases hi : sourceRepresentative (i 0).val≤128*P
      · simpa only [ite_eq_left hi] using hf i hi
      · simp only [ite_eq_right hi,tsum_zero]
        exact bot_le
    _ = _ := by simp [tsum_fintype,nsmul_eq_mul]

lemma measurableSet_directTriangleDomain (T : ℝ) {J : Set ℝ} (hJ : MeasurableSet J) :
    MeasurableSet (directTriangleDomain T J) :=
  (measurableSet_trianglePhaseDomain T).inter (hJ.preimage measurable_fst.fst)

lemma measurable_directTriangleDensity {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X : ℝ→Vec} (hX : Measurable X)
    {J : Set ℝ} (hJ : MeasurableSet J) {K : TrianglePhase→Vec} (hK : Measurable K) :
    Measurable (directTriangleDensity s X T J K) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk (((hX.comp ht).sub ((ht.sub hσ).smul hn)).prodMk measurable_snd)
  have hf := (hs.continuous_prefixParticle hT).measurable.comp hy
  exact (((ht.sub hσ).pow_const 2).ennreal_ofReal.mul
    (hf.smul hK).norm.ennreal_ofReal).indicator (measurableSet_directTriangleDomain T hJ)

lemma measurable_directSourceTriangleKernel {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V : ℝ→Vec} (hX : Measurable X) (hV : Measurable V) :
    Measurable (directSourceTriangleKernel s X V T) := by
  have ht : Measurable (fun p : TrianglePhase=>p.1.1) := measurable_fst.fst
  have hσ : Measurable (fun p : TrianglePhase=>p.1.2.1) := measurable_fst.snd.fst
  have hn : Measurable (fun p : TrianglePhase=>p.1.2.2.1) :=
    measurable_subtype_coe.comp measurable_fst.snd.snd
  have hy := hσ.prodMk ((hX.comp ht).sub ((ht.sub hσ).smul hn))
  exact measurable_forceSourceFamily (ht.sub hσ) hn
    ((contDiff_velocity (k:=0)).continuous.measurable.comp (hV.comp ht)) measurable_snd
    (measurable_lorentz_acceleration measurable_snd
      ((continuous_prefixField hs.E_smooth.continuousOn hT).measurable.comp hy)
      ((continuous_prefixField hs.B_smooth.continuousOn hT).measurable.comp hy))

lemma directTriangleDensity_nonzero {s : Solution} {X : ℝ→Vec} {T : ℝ} {J : Set ℝ}
    {K : TrianglePhase→Vec} {p : TrianglePhase} (hp : directTriangleDensity s X T J K p≠0) :
    p∈directTriangleDomain T J ∧
      s.f (p.1.2.1,(X p.1.1-(p.1.1-p.1.2.1) • p.1.2.2.1,p.2))≠0 := by
  have hmem : p∈directTriangleDomain T J := by
    by_contra hc
    exact hp (indicator_of_notMem hc _)
  refine ⟨hmem,?_⟩
  intro hz
  apply hp
  have hσ : p.1.2.1∈Icc 0 T := ⟨hmem.1.2.1.le,hmem.1.2.2.le.trans hmem.1.1.2.le⟩
  simp only [directTriangleDensity,indicator_of_mem hmem,prefixParticle,prefixClamp_eq hσ,
    hz,zero_smul,norm_zero,ENNReal.ofReal_zero,mul_zero]

lemma directSourceTriangle_bin_bound {s : Solution} {X V : ℝ→Vec} {T : ℝ}
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase V B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      directTriangleDensity s X T J (directSourceTriangleKernel s X V T) (z,v))≤
      physicalDirectSourceDensity s X V B z := by
  unfold physicalDirectSourceDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  by_cases hp : (z,v)∈directTriangleDomain T J
  · have hσ : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    simp only [directTriangleDensity,indicator_of_mem hp,directSourceTriangleKernel,
      prefixParticle,prefixField,prefixClamp_eq hσ]
    exact le_rfl
  · simp only [directTriangleDensity,indicator_of_notMem hp]
    exact bot_le

lemma PhaseFlowOn.directTriangleDensity_finite_cover {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hbound : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (X V : ℝ→Vec) {J : Set ℝ} (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (p : TrianglePhase)
    (hp : directTriangleDensity s X T J K p≠0) :
    ∃i : DirectOuterIndex N×ℕ,
      i∈{i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P} ∧
      p∈physicalBinPhaseSet V (directOuterBin T w i.1 i.2) J := by
  have hh := directTriangleDensity_nonzero hp
  have hσ : p.1.2.1∈Icc 0 T := ⟨hh.1.1.2.1.le,hh.1.1.2.2.le.trans hh.1.1.1.2.le⟩
  have hq := F.eulerian_supported_momentum hs hbound hσ _ p.2 hh.2
  obtain ⟨i,nr,hcap,hbase,hv⟩ := physical_direct_finite_cover hP hwP hN hh.1.2
    hh.1.1.1.2.le ⟨hh.1.1.2.1.le,hh.1.1.2.2⟩ (hband _ hh.1.2) p.1.2.2 p.2 hq
  exact ⟨(i,nr),hcap,hbase,hv⟩

lemma PhaseFlowOn.directTriangle_family_estimate {s : Solution} {T P w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (hP : 0≤P) (hwP : w≤P) (N : ℕ) (hN : 8192*P≤(2:ℝ)^N)
    (hbound : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (X V : ℝ→Vec) (hX : Measurable X) (hV : Measurable V)
    (J : Set ℝ) (hJ : MeasurableSet J) (hband : ∀t∈J,q (V t)∈Icc (w/8) (8*w))
    (K : TrianglePhase→Vec) (hK : Measurable K) (f : ClosedConeBin → ConeCoordinate → ℝ≥0∞)
    (C : ℝ≥0∞)
    (hbin : ∀B z,z∈physicalBinBase V B J→
      (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
        directTriangleDensity s X T J K (z,v))≤f B z)
    (hfamily : ∀i : DirectOuterIndex N,sourceRepresentative (i 0).val≤128*P→
      (∑'nr,∫⁻z,f (directOuterBin T w i nr) z ∂physicalBinMeasure V (directOuterBin T w i nr) J)≤C) :
    (∫⁻p,directTriangleDensity s X T J K p ∂trianglePhaseMeasure)≤(N:ℝ≥0∞)^4*C := by
  let R := {i : DirectOuterIndex N×ℕ | sourceRepresentative (i.1 0).val≤128*P}
  have hc := physicalBinFamily_cover_lintegral hV hJ
    (fun i : DirectOuterIndex N×ℕ=>directOuterBin T w i.1 i.2) R
    (measurable_directTriangleDensity hs hT hX hJ hK)
    (F.directTriangleDensity_finite_cover hs hP hwP N hN hbound X V hband K)
  apply hc.trans
  apply (ENNReal.tsum_le_tsum (fun i=>?_)).trans
  · exact directOuter_family_sum_bound
      (fun i nr=>∫⁻z,f (directOuterBin T w i nr) z ∂physicalBinMeasure V (directOuterBin T w i nr) J) C hfamily
  · apply indicator_le_indicator
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
    exact hbin _ z hz

lemma Admissible.direct_source_physical_bound {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (N : ℕ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a≤b → b-a ≤ (w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      8192*P≤(2:ℝ)^N →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directSourceTriangleKernel s X V T) p
        ∂trianglePhaseMeasure) ≤
      (N:ℝ≥0∞)^4*ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_source_all_radii
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hab hJI hM hA hP hL hw hwP hN hPbound hW HX HZ
  dsimp only
  have hα : Continuous (fun t : ℝ => prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hJT : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hband : ∀t∈Icc a b,q (prefixFlow F.flow T zX t).2∈Icc (w/8) (8*w) := by
    intro t ht
    simpa only [prefixFlow,prefixClamp_eq (hJT ht)] using hW t ht
  apply F.directTriangle_family_estimate hs hT (zero_le_one.trans hP) hwP N hN hPbound
    (fun t => (prefixFlow F.flow T zX t).1) (fun t => (prefixFlow F.flow T zX t).2)
    hα.fst.measurable hα.snd.measurable (Icc a b) measurableSet_Icc hband
    (directSourceTriangleKernel s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2) T)
    (measurable_directSourceTriangleKernel hs hT hα.fst.measurable hα.snd.measurable)
    (physicalDirectSourceDensity s (fun t => (prefixFlow F.flow T zX t).1)
      (fun t => (prefixFlow F.flow T zX t).2))
    (ENNReal.ofReal (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)))
    (fun B z hz=>directSourceTriangle_bin_bound (s:=s)
      (X:=fun t=>(prefixFlow F.flow T zX t).1) (V:=fun t=>(prefixFlow F.flow T zX t).2)
      (T:=T) hJT B hz)
  intro i hi
  exact hbound s T F hs hT h0 zX S (i 0).val (i 1).val (i 2).val (i 3).val a b w M A P
    hS hS0 ha hb hab hJI hM hA hP hL hw hwP hi HX HZ

lemma exists_direct_dyadic_count : ∃C : ℝ,0≤C ∧ ∀P : ℝ,
    1≤P → 1≤Real.log (2+P) → ∃N : ℕ,8192*P≤(2:ℝ)^N ∧ (N:ℝ)≤C*Real.log (2+P) := by
  obtain ⟨C,hC,hcount⟩ := exists_far_dyadic_count 0
  refine ⟨C,hC,?_⟩
  intro P hP hL
  obtain ⟨N,_,_,hN,hNc⟩ := hcount P (zero_lt_one.trans_le hP) hL
  refine ⟨N,?_,hNc⟩
  norm_num at hN
  have hh : P≤P^2 := by nlinarith only [hP,sq_nonneg (P-1)]
  nlinarith only [hN,hP,hh]

lemma ennreal_count_four_bound {N : ℕ} {C L : ℝ} (hC : 0≤C) (hL : 0≤L)
    (hN : (N:ℝ)≤C*L) (B : ℝ) :
    (N:ℝ≥0∞)^4*ENNReal.ofReal B ≤ ENNReal.ofReal (C^4*L^4*B) := by
  have hNc : (N:ℝ≥0∞)≤ENNReal.ofReal (C*L) := by
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal hN
  calc
    _ ≤ (ENNReal.ofReal (C*L))^4*ENNReal.ofReal B := mul_le_mul' (pow_le_pow_left' hNc 4) le_rfl
    _ = _ := by
      rw [←ENNReal.ofReal_pow (mul_nonneg hC hL),←ENNReal.ofReal_mul (pow_nonneg (mul_nonneg hC hL) 4)]
      congr 1
      ring

lemma Admissible.direct_source_physical_log_bound_oai {d : Datum} (hd₀ : Admissible d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0 ≤ T → (∀ z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0 ≤ a → b ≤ T → a≤b → b-a ≤ (w/P)^2 →
      0<M → 0≤A → 1≤P → 1≤Real.log (2+P) → 1≤w → w≤P →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p,directTriangleDensity s X T (Icc a b) (directSourceTriangleKernel s X V T) p
        ∂trianglePhaseMeasure) ≤
      ENNReal.ofReal (C*(1+E)*(1+M+Real.sqrt A)*w*Real.sqrt w*(Real.log (2+P))^5) := by
  obtain ⟨C,hC,hbound⟩ := hd₀.direct_source_physical_bound
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  refine ⟨C*Cn^4,by positivity,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPbound hW HX HZ
  dsimp only
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  apply (hbound s T F hs hT h0 zX S a b w M A P N hS hS0 ha hb hab hJI hM hA hP hL hw hwP
    hN hPbound hW HX HZ).trans
  convert ennreal_count_four_bound hCn (zero_le_one.trans hL) hNc
    (C*(1+∫x : Vec,totalEnergy s (0,x))*(1+M+Real.sqrt A)*w*Real.sqrt w*Real.log (2+P)) using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  ring

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direct_source_physical_log_bound_oai := @OAI.RVM.Admissible.direct_source_physical_log_bound_oai
