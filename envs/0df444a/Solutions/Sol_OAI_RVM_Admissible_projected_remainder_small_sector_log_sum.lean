-- Prove2me | solution 1 for OAI.RVM.Admissible.projected_remainder_small_sector_log_sum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:09:21.118011+00:00
-- url     : https://prove2.me/submissions/8aed18f1-7442-40d9-9b21-70c07236167e

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_central_density_small_sector_log_sum

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

lemma velocityProjection_add (u b c : Vec) :
    velocityProjection u (b+c) = velocityProjection u b + velocityProjection u c := by
  simp only [velocityProjection,dot_add_right,add_smul]
  module

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

lemma velocityProjection_dot_symm (u b n : Vec) :
    dot n (velocityProjection u b) = dot (velocityProjection u n) b := by
  simp only [velocityProjection,dot_sub_right,dot_sub_left,dot_smul_left,dot_smul_right]
  rw [dot_comm n u]
  ring

lemma norm_velocityProjection_normal (u n : Vec) (hu : ‖u‖ ≤ 1) (hn : ‖n‖=1) :
    ‖velocityProjection u n‖ ≤ Real.sqrt (2*(1-dot n u)) := by
  have hs : ‖u‖^2 ≤ 1 := by nlinarith [norm_nonneg u]
  have hdot := dot_le_norm n u
  rw [hn,one_mul] at hdot
  have hd : 0 ≤ 2*(1-dot n u) := by linarith
  have he : ‖velocityProjection u n‖^2 =
      1-2*(dot n u)^2+(dot n u)^2*‖u‖^2 := by
    rw [velocityProjection,norm_sub_sq_real,norm_smul,Real.norm_eq_abs,
      mul_pow,sq_abs,inner_smul_right,← dot_eq_inner,dot_comm u n,hn]
    ring
  have hh := mul_le_mul_of_nonneg_left hs (sq_nonneg (dot n u))
  have hsq := Real.sq_sqrt hd
  nlinarith [Real.sqrt_nonneg (2*(1-dot n u)),sq_nonneg (1-dot n u)]

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

lemma physicalBinDensity_aemeasurable {s : Solution} {T : ℝ} (hs : EnergyPrefix s T)
    (hT : 0 ≤ T) {X V : ℝ → Vec} (hX : Measurable X) (hV : Measurable V)
    (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) :
    AEMeasurable (fun z : ConeCoordinate => physicalBinDensity s X V B z.1 z.2.1 z.2.2)
      (physicalBinMeasure V B J) := by
  have hm := (measurable_coneBinDensity (hs.continuous_prefixParticle hT).measurable hX hV B).aemeasurable
    (μ := physicalBinMeasure V B J)
  apply hm.congr
  apply ae_restrict_of_forall_mem (measurableSet_physicalBinBase hV B hJ)
  intro z hz
  unfold physicalBinDensity
  apply lintegral_congr
  intro v
  rw [prefixParticle,prefixClamp_eq (show z.2.1∈Icc 0 T from ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩)]

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

lemma velocityProjection_smul (u h : Vec) (c : ℝ) :
    velocityProjection u (c • h)=c • velocityProjection u h := by
  simp only [velocityProjection,dot_smul_right,smul_sub,smul_smul]

lemma transverseProjection_velocity (w : Vec) : transverseProjection w (velocity w)=0 := by
  by_cases hw : w=0
  · simp [hw,transverseProjection,velocityProjection,velocity,dot]
  · have hn := norm_ne_zero_iff.mpr hw
    ext i
    simp only [transverseProjection,velocityProjection,velocity,dot_smul_left,dot_smul_right,
      dot_self,PiLp.sub_apply,PiLp.smul_apply,PiLp.zero_apply,smul_eq_mul]
    field_simp
    ring

lemma transverseProjection_normal_bound (w n : Vec) (hn : ‖n‖=1) :
    ‖transverseProjection w n‖≤Real.sqrt (2*(1-dot n (velocity w))) := by
  have he : transverseProjection w n=transverseProjection w (n-velocity w) := by
    have h := velocityProjection_add (‖w‖⁻¹ • w) (n-velocity w) (velocity w)
    rw [sub_add_cancel] at h
    change transverseProjection w n=transverseProjection w (n-velocity w)+transverseProjection w (velocity w) at h
    rwa [transverseProjection_velocity,add_zero] at h
  rw [he]
  exact (transverseProjection_norm _ _).trans (by simpa only [norm_sub_rev] using velocity_normal_distance_bound w n hn)

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

lemma transverseProjection_add (w h k : Vec) :
    transverseProjection w (h+k)=transverseProjection w h+transverseProjection w k :=
  velocityProjection_add _ _ _

lemma transverseProjection_smul (w h : Vec) (c : ℝ) :
    transverseProjection w (c • h)=c • transverseProjection w h := velocityProjection_smul _ _ _

lemma small_primitive_acceleration_pairing {a u n b : Vec} {θ φ K : ℝ}
    (hθ : 0 ≤ θ) (hφ : 0 < φ) (hK : 0 ≤ K)
    (hD : φ^2/2 ≤ 1-dot n a) (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ)
    (hb : ‖b‖ ≤ K) (hbn : |dot b n| ≤ 20*φ*K) :
    |dot b (signedPrimitive a u n)| ≤ 964*θ*K := by
  have hDpos : 0 < 1-dot n a := lt_of_lt_of_le (by positivity) hD
  have hratio : |(1-dot n a-(1-dot a u))/(1-dot n a)| ≤ 48*θ/φ := by
    rw [abs_div,abs_of_pos hDpos,abs_sub_comm]
    apply (div_le_iff₀ hDpos).mpr
    have hm := mul_le_mul_of_nonneg_left hD (by positivity : 0 ≤ 48*θ/φ)
    have hh : 48*θ/φ*(φ^2/2)=24*φ*θ := by field_simp; ring
    rw [hh] at hm
    exact he.trans hm
  rw [signedPrimitive_decomposition _ _ _ hDpos.ne',dot_add_right,dot_smul_right]
  calc
    _ ≤ |dot b (u-n)|+|(1-dot n a-(1-dot a u))/(1-dot n a)*dot b n| := abs_add_le _ _
    _ ≤ ‖b‖*‖u-n‖+|(1-dot n a-(1-dot a u))/(1-dot n a)| *|dot b n| := by
      rw [abs_mul]
      apply add_le_add _ le_rfl
      rw [dot_eq_inner]
      exact abs_real_inner_le_norm _ _
    _ ≤ K*(4*θ)+(48*θ/φ)*(20*φ*K) := by gcongr
    _ = _ := by field_simp; ring

lemma receiver_acceleration_bounds (w K n : Vec) {φ : ℝ}
    (hn : ‖n‖=1) (hφ : 0 ≤ φ) (hD : 1-dot n (velocity w) ≤ 8*φ^2) :
    ‖fderiv ℝ velocity w K‖ ≤ ‖K‖/q w ∧
    |dot (fderiv ℝ velocity w K) n| ≤ 4*φ*(‖K‖/q w) := by
  have hp : ‖velocityProjection (velocity w) n‖ ≤ 4*φ := by
    apply (norm_velocityProjection_normal _ _ (norm_velocity_lt_one w).le hn).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have he : fderiv ℝ velocity w K=(q w)⁻¹ • velocityProjection (velocity w) K := by
    rw [fderiv_velocity_apply]
    rfl
  constructor
  · rw [he,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (q_pos w))]
    have hh := mul_le_mul_of_nonneg_left
      (velocityProjection_norm (velocity w) K (norm_velocity_lt_one w).le)
      (inv_pos.mpr (q_pos w)).le
    simpa only [div_eq_mul_inv,mul_comm] using hh
  · rw [he,dot_smul_left,abs_mul,abs_of_pos (inv_pos.mpr (q_pos w)),
      dot_comm (velocityProjection _ _) n,velocityProjection_dot_symm]
    calc
      _ ≤ (q w)⁻¹*(‖velocityProjection (velocity w) n‖*‖K‖) := by
        apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (q_pos w)).le
        rw [dot_eq_inner]
        exact abs_real_inner_le_norm _ _
      _ ≤ (q w)⁻¹*((4*φ)*‖K‖) := by
        gcongr
        exact (inv_pos.mpr (q_pos w)).le
      _ = _ := by ring

lemma receiver_small_primitive_pairing (w K u n : Vec) {θ φ : ℝ}
    (hn : ‖n‖=1) (hθ : 0 ≤ θ) (hφ : 0 < φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity w))
    (hDu : 1-dot n (velocity w) ≤ 8*φ^2)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot (velocity w) u)-(1-dot n (velocity w))| ≤ 24*φ*θ) :
    |dot (fderiv ℝ velocity w K) (signedPrimitive (velocity w) u n)| ≤
      964*θ*(‖K‖/q w) := by
  have hb := receiver_acceleration_bounds w K n hn hφ.le hDu
  have hK : 0 ≤ ‖K‖/q w := div_nonneg (norm_nonneg _) (q_pos w).le
  apply small_primitive_acceleration_pairing hθ hφ hK hD hun he hb.1
  exact hb.2.trans (mul_le_mul_of_nonneg_right (by nlinarith) hK)

lemma receiver_bulk_transverse_bound {w n : Vec} {φ : ℝ}
    (hn : ‖n‖=1) (hφ : 0 ≤ φ) (hD : 1-dot n (velocity w) ≤ 8*φ^2) :
    ‖transverseProjection w (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) •
      n-velocity w)‖ ≤ 8*φ := by
  have hDp : 0 < 1-dot n (velocity w) := cone_denom_pos w n hn
  have hnon : 0 ≤ 1-dot (velocity w) (velocity w) := by
    rw [dot_self]
    nlinarith [norm_velocity_lt_one w,norm_nonneg (velocity w)]
  have hfrac : |(1-dot (velocity w) (velocity w))/(1-dot n (velocity w))| ≤ 2 := by
    rw [abs_of_nonneg (div_nonneg hnon hDp.le)]
    apply (div_le_iff₀ hDp).mpr
    have hh := sq_nonneg ‖n-velocity w‖
    rw [norm_sub_sq_real,← dot_eq_inner,hn,one_pow] at hh
    rw [dot_self]
    linarith
  have hpn : ‖transverseProjection w n‖ ≤ 4*φ := by
    apply (transverseProjection_normal_bound w n hn).trans
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,by nlinarith⟩
  have he : transverseProjection w
      (((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • n-velocity w)=
      ((1-dot (velocity w) (velocity w))/(1-dot n (velocity w))) • transverseProjection w n := by
    rw [sub_eq_add_neg,transverseProjection_add,show -velocity w=(-1:ℝ) • velocity w by simp,
      transverseProjection_smul,transverseProjection_smul,transverseProjection_velocity,smul_zero,add_zero]
  rw [he,norm_smul,Real.norm_eq_abs]
  exact (mul_le_mul hfrac hpn (norm_nonneg _) (by norm_num)).trans_eq (by ring)

lemma small_energy_ratio {a u n : Vec} {θ φ : ℝ}
    (_hθ : 0 ≤ θ) (hφ : 0 < φ) (hsmall : θ ≤ φ)
    (hD : φ^2/2 ≤ 1-dot n a)
    (he : |(1-dot a u)-(1-dot n a)| ≤ 24*φ*θ) :
    |(1-dot a u)/(1-dot n a)| ≤ 49 := by
  have hDp : 0<1-dot n a := lt_of_lt_of_le (by positivity) hD
  rw [abs_div,abs_of_pos hDp]
  apply (div_le_iff₀ hDp).mpr
  have hab : |1-dot a u| ≤ |(1-dot a u)-(1-dot n a)|+|1-dot n a| :=
    calc
      _ = |((1-dot a u)-(1-dot n a))+(1-dot n a)| := by congr 1; ring
      _ ≤ _ := abs_add_le _ _
  rw [abs_of_pos hDp] at hab
  have hm := mul_le_mul_of_nonneg_left hsmall (by positivity : 0≤24*φ)
  nlinarith

lemma signedRemainder_physical_decomposition {r f : ℝ} {a u n b : Vec}
    (hr : r≠0) (hD : 1-dot n a≠0) :
    (f*(1-dot n a)) • signedRemainder r a u n b =
      (f/r^2*((1-dot a u)/(1-dot n a))) •
        (((1-dot a a)/(1-dot n a)) • n-a) +
      (f/r*(dot b (signedPrimitive a u n)/(1-dot n a))) • n := by
  ext i
  simp only [signedRemainder,PiLp.smul_apply,PiLp.add_apply,PiLp.sub_apply,smul_eq_mul]
  field_simp


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


lemma transverseCLM_apply (v h : Vec) : transverseCLM v h=transverseProjection v h := by
  simp only [transverseCLM,sub_apply,ContinuousLinearMap.id_apply,
    ContinuousLinearMap.smulRight_apply,InnerProductSpace.toDual_apply_apply,← dot_eq_inner]
  rfl

lemma angularMultiplierCLM_apply (w : ℝ) (v h : Vec) :
    angularMultiplierCLM w v h=angularMultiplier w v h := by
  simp only [angularMultiplierCLM,smul_apply,transverseCLM_apply,angularMultiplier]



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

lemma physicalBin_radial_density_near {s : Solution} {X V : ℝ→Vec}
    (hV : Measurable V) (B : ClosedConeBin) {J : Set ℝ} (hJ : MeasurableSet J)
    {C p θ φ : ℝ} (_hC : 0≤C) (_hp : 0≤p) (_hθ : 0≤θ) (hφ : 0≤φ)
    (hr : 0≤B.rmax) (hD : B.Dmax≤8*φ^2)
    (hdensity : ∀z∈physicalBinBase V B J,
      physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*C*p^3*θ^2))
    {g : ℝ→ℝ≥0∞} (hg : Measurable g) :
    (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      (∫⁻t in J,g t)*ENNReal.ofReal (49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)) := by
  have hm := physicalBinMeasure_receiver_weight hV B hJ hφ hD hg
  have hbound : (∫⁻z : ConeCoordinate,g z.1*ENNReal.ofReal (z.1-z.2.1)*
      physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)≤
      (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)*
        (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := by
    calc
      _ ≤ ∫⁻z : ConeCoordinate,g z.1*(ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2))
          ∂physicalBinMeasure V B J := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
        have hr' : ENNReal.ofReal (z.1-z.2.1)≤ENNReal.ofReal B.rmax := ENNReal.ofReal_le_ofReal hz.2.2.1.2
        have hd := hdensity z hz
        simpa only [mul_assoc] using mul_le_mul' (mul_le_mul' le_rfl hr') hd
      _ = _ := lintegral_mul_const _ (hg.comp measurable_fst)
  by_cases hwidth : B.rmin≤B.rmax
  · calc
      _ ≤ (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)*
          (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := hbound
      _ ≤ (∫⁻t in J,g t)*ENNReal.ofReal (B.rmax-B.rmin)*ENNReal.ofReal (384*φ^2)*
          (ENNReal.ofReal B.rmax*ENNReal.ofReal (128*C*p^3*θ^2)) := mul_le_mul' hm le_rfl
      _ = _ := by
        have he : 49152*C*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin)=
            (B.rmax-B.rmin)*(384*φ^2)*(B.rmax*(128*C*p^3*θ^2)) := by ring
        rw [he,ENNReal.ofReal_mul (by positivity : 0≤(B.rmax-B.rmin)*(384*φ^2)),
          ENNReal.ofReal_mul (sub_nonneg.mpr hwidth),ENNReal.ofReal_mul hr]
        ac_rfl
  · have hw : ENNReal.ofReal (B.rmax-B.rmin)=0 := ENNReal.ofReal_eq_zero.mpr (by linarith)
    have hzero : (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)=0 := by
      apply le_antisymm
      · change (∫⁻z : ConeCoordinate,g z.1 ∂physicalBinMeasure V B J)≤(0:ℝ≥0∞)
        simpa only [hw,mul_zero,zero_mul] using hm
      · exact bot_le
    calc
      _ ≤ (0:ℝ≥0∞) := by simpa only [hzero,zero_mul] using hbound
      _ ≤ _ := bot_le

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

namespace RVM

lemma selected_representative_moving_bound {T C w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    (hC : 0≤C) (hw : 0≤w) (h0 : k 0<N) (h1 : k 1<N)
    (hsel : sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) :
    C*(sourceRepresentative (k 0)*cappedRepresentative (k 1))^3*
      cappedRepresentative (k 2)/w*(representativeClosedBin T w k).rmax*
      ((representativeClosedBin T w k).rmax-(representativeClosedBin T w k).rmin)≤
      (4*C*Real.sqrt (max 1 T)/w)*directionWeightMajorant N k := by
  have hT : 0 < max (1:ℝ) T := zero_lt_one.trans_le (le_max_left _ _)
  have hp : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
  have hc (i : Fin 4) : 0 < cappedRepresentative (k i) := by dsimp [cappedRepresentative]; positivity
  have hb := selected_moving_coefficient hC hp.le (hc 1).le (hc 2).le hw
    (mul_nonneg hT.le (hc 3).le) hsel
    (R:=(representativeClosedBin T w k).rmax) (r:=(representativeClosedBin T w k).rmin)
    (by exact mul_nonneg (mul_nonneg (by norm_num) hT.le) (hc 3).le)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
    (by dsimp [representativeClosedBin]; ring_nf; exact le_rfl)
    (by dsimp [representativeClosedBin]; nlinarith [mul_pos hT (hc 3)])
  calc
    _ ≤ 4*C*Real.sqrt (max 1 T*cappedRepresentative (k 3))*cappedRepresentative (k 2)/w := hb
    _ = _ := by
      rw [Real.sqrt_mul hT.le]
      simp only [directionWeightMajorant,ite_eq_left h0,ite_eq_left h1,one_mul,cappedRepresentative]
      norm_num
      ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderDensity
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

lemma angularMultiplierCLM_highband_transverse {w : ℝ} {W x : Vec}
    (hw : 0<w) (hW : w/16 ≤ ‖W‖) :
    ‖angularMultiplierCLM w W x‖ ≤ 16*‖transverseProjection W x‖ := by
  have hρ : 0<‖W‖ := lt_of_lt_of_le (by positivity) hW
  rw [angularMultiplierCLM_apply,angularMultiplier,norm_smul,Real.norm_eq_abs,
    abs_of_pos (div_pos hw hρ)]
  exact mul_le_mul_of_nonneg_right ((div_le_iff₀ hρ).mpr (by linarith)) (norm_nonneg _)

lemma signedRemainder_projected_norm {r f θ φ w : ℝ} (W K u n : Vec)
    (hr : 0 < r) (hf : 0 ≤ f) (hn : ‖n‖=1) (hw : 0<w) (hW : w/16 ≤ ‖W‖)
    (hθ : 0 ≤ θ) (hφ : 0<φ) (hsmall : θ ≤ φ)
    (hD : φ^2/2 ≤ 1-dot n (velocity W)) (hDu : 1-dot n (velocity W) ≤ 8*φ^2)
    (hun : ‖u-n‖ ≤ 4*θ)
    (he : |(1-dot (velocity W) u)-(1-dot n (velocity W))| ≤ 24*φ*θ) :
    ‖angularMultiplierCLM w W ((f*(1-dot n (velocity W))) •
      signedRemainder r (velocity W) u n (fderiv ℝ velocity W K))‖ ≤
      (6272*φ/r^2+1974272*θ/(w*φ)*‖K‖/r)*f := by
  have hDp : 0<1-dot n (velocity W) := cone_denom_pos W n hn
  have hratio := small_energy_ratio hθ hφ hsmall hD he
  have hpair := receiver_small_primitive_pairing W K u n hn hθ hφ hD hDu hun he
  have hK : 0 ≤ ‖K‖/q W := div_nonneg (norm_nonneg _) (q_pos W).le
  have hpairD : |dot (fderiv ℝ velocity W K) (signedPrimitive (velocity W) u n)/
      (1-dot n (velocity W))| ≤ 1928*θ*(‖K‖/q W)/φ^2 := by
    rw [abs_div,abs_of_pos hDp]
    apply (div_le_iff₀ hDp).mpr
    have hm := mul_le_mul_of_nonneg_left hD
      (by positivity : 0 ≤ 1928*θ*(‖K‖/q W)/φ^2)
    have heq : 1928*θ*(‖K‖/q W)/φ^2*(φ^2/2)=964*θ*(‖K‖/q W) := by field_simp; ring
    rw [heq] at hm
    exact hpair.trans hm
  let c : Vec := ((1-dot (velocity W) (velocity W))/(1-dot n (velocity W))) • n-velocity W
  have hcentral : ‖angularMultiplierCLM w W c‖ ≤ 128*φ := by
    exact (angularMultiplierCLM_highband_transverse hw hW).trans
      ((mul_le_mul_of_nonneg_left (receiver_bulk_transverse_bound hn hφ.le hDu) (by norm_num)).trans_eq (by ring))
  have hnormal : ‖angularMultiplierCLM w W n‖ ≤ 64*φ := by
    have hp : ‖transverseProjection W n‖ ≤ 4*φ := by
      apply (transverseProjection_normal_bound W n hn).trans
      exact (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩
    exact (angularMultiplierCLM_highband_transverse hw hW).trans
      ((mul_le_mul_of_nonneg_left hp (by norm_num)).trans_eq (by ring))
  have hq : w/16 ≤ q W := hW.trans (norm_lt_q _).le
  have hqK : ‖K‖/q W ≤ ‖K‖/(w/16) := div_le_div_of_nonneg_left (norm_nonneg _) (by positivity) hq
  rw [signedRemainder_physical_decomposition hr.ne' hDp.ne',map_add,map_smul,map_smul]
  calc
    _ ≤ ‖(f/r^2*((1-dot (velocity W) u)/(1-dot n (velocity W)))) •
          (angularMultiplierCLM w W c)‖+
        ‖(f/r*(dot (fderiv ℝ velocity W K) (signedPrimitive (velocity W) u n)/(1-dot n (velocity W)))) •
          (angularMultiplierCLM w W n)‖ := norm_add_le _ _
    _ ≤ (f/r^2*49)*(128*φ)+(f/r*(1928*θ*(‖K‖/q W)/φ^2))*(64*φ) := by
      simp only [norm_smul,Real.norm_eq_abs,abs_mul,abs_of_nonneg (div_nonneg hf (sq_nonneg r)),abs_of_nonneg (div_nonneg hf hr.le)]
      exact add_le_add (mul_le_mul (mul_le_mul_of_nonneg_left hratio (by positivity)) hcentral (norm_nonneg _) (by positivity))
        (mul_le_mul (mul_le_mul_of_nonneg_left hpairD (by positivity)) hnormal (norm_nonneg _) (by positivity))
    _ ≤ (f/r^2*49)*(128*φ)+(f/r*(1928*θ*(‖K‖/(w/16))/φ^2))*(64*φ) := by gcongr
    _ = _ := by field_simp; ring

lemma physicalProjectedRemainderDensity_bound {s : Solution} {X V K : ℝ→Vec}
    {B : ClosedConeBin} {w θ φ : ℝ} {z : ConeCoordinate}
    (hw : 0<w) (hv : w/16≤‖V z.1‖) (hr : 0<z.1-z.2.1)
    (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤1-dot z.2.2.1 (velocity (V z.1)))
    (hDhi : 1-dot z.2.2.1 (velocity (V z.1))≤8*φ^2)
    (hf : ∀v,0 ≤ s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :
    physicalProjectedRemainderDensity s X V B w K z≤
      ENNReal.ofReal (6272*φ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2+
      ENNReal.ofReal (1974272*θ/(w*φ)*‖K z.1‖)*ENNReal.ofReal (z.1-z.2.1)*
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 := by
  have han : ‖velocity (V z.1)-z.2.2.1‖≤4*φ := by
    apply norm_sub_le_of_deficit (norm_velocity_lt_one _).le (sphere_norm _).le (by positivity)
    rw [dot_comm]
    nlinarith
  have hpoint : ∀v∈coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖≤
      ENNReal.ofReal (6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
        ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) := by
    intro v hvbin
    have hdv : 1-dot z.2.2.1 (velocity v)≤8*θ^2 := hvbin.2.1.2.trans hd
    have hun : ‖velocity v-z.2.2.1‖≤4*θ := by
      apply norm_sub_le_of_deficit (norm_velocity_lt_one v).le (sphere_norm _).le (by positivity)
      rw [dot_comm]
      nlinarith
    have he := small_deficit_difference (sphere_norm z.2.2) hθ hφ.le hsmall
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).le hdv hun han
    rw [←ENNReal.ofReal_mul (by positivity :
      0≤6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))]
    exact ENNReal.ofReal_le_ofReal (signedRemainder_projected_norm (V z.1) (K z.1)
      (velocity v) z.2.2.1 hr (hf v) (sphere_norm z.2.2) hw hv hθ hφ hsmall hDlo hDhi hun he)
  unfold physicalProjectedRemainderDensity
  calc
    _ ≤ ENNReal.ofReal ((z.1-z.2.1)^2)*
        ∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (V z.1)),
          ENNReal.ofReal (6272*φ/(z.1-z.2.1)^2+1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))*
            ENNReal.ofReal (s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))) :=
      mul_le_mul' le_rfl (setLIntegral_mono' (measurableSet_coneBinMomentumSet _ _ _) hpoint)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,←mul_assoc,←ENNReal.ofReal_mul (sq_nonneg _)]
      have he : (z.1-z.2.1)^2*(6272*φ/(z.1-z.2.1)^2+
          1974272*θ/(w*φ)*‖K z.1‖/(z.1-z.2.1))=
          6272*φ+(1974272*θ/(w*φ)*‖K z.1‖)*(z.1-z.2.1) := by field_simp [hr.ne']
      rw [he,ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ)*‖K z.1‖),add_mul]
      rfl

lemma physicalProjectedRemainder_integral_bound {s : Solution} {T : ℝ}
    (hs : EnergyPrefix s T) (hT : 0≤T) {X V K : ℝ→Vec}
    (hX : Measurable X) (hV : Measurable V) (B : ClosedConeBin)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) {w θ φ : ℝ}
    (hw : 0<w) (hθ : 0≤θ) (hφ : 0<φ) (hsmall : θ≤φ)
    (hr : 0<B.rmin) (hd : B.dmax≤8*θ^2) (hDlo : φ^2/2≤B.Dmin) (hDhi : B.Dmax≤8*φ^2)
    (hband : ∀t∈J,w/16≤‖V t‖) :
    (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V B w K z ∂physicalBinMeasure V B J)≤
      ENNReal.ofReal (6272*φ)*(∫⁻z : ConeCoordinate,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J)+
      ENNReal.ofReal (1974272*θ/(w*φ))*(∫⁻z : ConeCoordinate,
        ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J) := by
  have hN := physicalBinDensity_aemeasurable hs hT hX hV B hJ hJT
  have hb : (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V B w K z ∂physicalBinMeasure V B J)≤
      ∫⁻z : ConeCoordinate,ENNReal.ofReal (6272*φ)*physicalBinDensity s X V B z.1 z.2.1 z.2.2+
        ENNReal.ofReal (1974272*θ/(w*φ))*(ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2) ∂physicalBinMeasure V B J := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV B hJ)] with z hz
    have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
    have hb := physicalProjectedRemainderDensity_bound (X:=X) (K:=K) hw (hband z.1 hz.1)
      (hr.trans_le hz.2.2.1.1) hθ hφ hsmall hd (hDlo.trans hz.2.2.2.2.1)
      (hz.2.2.2.2.2.trans hDhi) (fun v=>hs.nonnegative _ hzT _)
    rw [ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ))] at hb
    convert hb using 1
    all_goals try with_reducible_and_instances rfl
    ac_rfl
  refine hb.trans_eq ?_
  rw [lintegral_add_left' (hN.const_mul _),lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

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

namespace RVM

lemma cappedRepresentative_mul_pow (n : ℕ) : cappedRepresentative n*(2:ℝ)^n=1 := by
  simp [cappedRepresentative,inv_pow]

end RVM

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

lemma representativeClosedBin_source_indices {T w : ℝ} {k : Fin 4→ℕ} {N : ℕ}
    {v n a : Vec} (hn : ‖n‖=1)
    (hv : v∈coneBinMomentumSet (representativeClosedBin T w k) n a)
    (hP : 1024*q v≤(2:ℝ)^N) : k 0<N ∧ k 1<N := by
  have hq := q_pos v
  have hθ := cappedRepresentative_pos (k 1)
  have heq := cappedRepresentative_mul_pow (k 1)
  have he := source_angle_coordinate_lower v n hn
  have hlo : sourceRepresentative (k 0)/128≤q v := hv.1.1
  have hhi : 1-dot n (velocity v)≤8*(cappedRepresentative (k 1))^2 := hv.2.1.2
  have hroot : Real.sqrt ((1-dot n (velocity v))/2)≤2*cappedRepresentative (k 1) := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity,?_⟩
    nlinarith only [hhi]
  have hqθ : 1/2≤2*q v*cappedRepresentative (k 1) :=
    he.trans (by nlinarith only [mul_le_mul_of_nonneg_left hroot hq.le])
  constructor
  · by_contra hc
    have hp : (2:ℝ)^N≤(2:ℝ)^(k 0) := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hc)
    dsimp [sourceRepresentative] at hlo
    nlinarith only [hP,hp,hlo,hq]
  · by_contra hc
    have hp : (2:ℝ)^N≤(2:ℝ)^(k 1) := pow_le_pow_right₀ (by norm_num) (Nat.le_of_not_gt hc)
    have hh := mul_le_mul_of_nonneg_right (hP.trans hp) hθ.le
    nlinarith only [hh,heq,hqθ]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_GeometryCutoffStableLogSum
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

lemma Admissible.projected_remainder_selected_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (J : Set ℝ) (w : ℝ) (N : ℕ) (Q : Set (Fin 4→ℕ)),
      (∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1) →
      MeasurableSet J → J⊆Icc 0 T → 0<w →
      (∀t∈J,w/16≤‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let W := ∫⁻t in J,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w
          (prefixMomentumForce s F.flow T zX) z
          ∂physicalBinMeasure V (representativeClosedBin T w k) J) k)≤
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>
        ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
        (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
          z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J)) k)+
      W*ENNReal.ofReal (C*Real.sqrt (max 1 T)*(N:ℝ)^2/w) := by
  classical
  obtain ⟨Cρ,hCρ,hdensity⟩ := hd₀.uniform_physicalBinDensity_constant
  let C := 1974272*49152*Cρ
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨32*C,by positivity,?_⟩
  intro s T F hs hT h0 zX J w N Q hQ hJ hJT hw hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in J,ENNReal.ofReal ‖K t‖
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) J)
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J
  let coeff := ENNReal.ofReal (4*C*Real.sqrt (max 1 T)/w)
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have hK : Measurable (fun t=>ENNReal.ofReal ‖K t‖) :=
    (F.continuous_prefixMomentumForce hs hT zX).norm.measurable.ennreal_ofReal
  have hband' : ∀t∈J,w/16≤‖V t‖ := by
    intro t ht
    simpa only [V,prefixFlow,prefixClamp_eq (hJT ht)] using hband t ht
  have hbnd (k : Fin 4→ℕ) (hk : k∈Q) :
      rfun k ≤ cfun k+W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
    let p := sourceRepresentative (k 0)
    let θ := cappedRepresentative (k 1)
    let φ := cappedRepresentative (k 2)
    let B := representativeClosedBin T w k
    have hp : 0<p := by dsimp [p,sourceRepresentative]; positivity
    have hθ : 0<θ := cappedRepresentative_pos _
    have hφ : 0<φ := cappedRepresentative_pos _
    have hsmall : θ≤φ := (hQ k hk).2.2.1
    have hr : 0<B.rmin := representativeClosedBin_radius_pos T w k
    have hR : 0≤B.rmax := by dsimp [B,representativeClosedBin,cappedRepresentative]; positivity
    have hden : ∀z∈physicalBinBase V B J,
        physicalBinDensity s X V B z.1 z.2.1 z.2.2≤ENNReal.ofReal (128*Cρ*p^3*θ^2) := by
      intro z hz
      have hzT : z.2.1∈Icc 0 T := ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩
      have hh := hdensity s T F hs h0 X V B z.1 z.2.1 z.2.2 p θ 1 hzT hp.le hθ.le (by norm_num)
        (by change p/32≤p; linarith only [hp]) le_rfl (by norm_num [B,representativeClosedBin])
      simpa only [min_eq_left (show θ≤1 from cappedRepresentative_le_one _)] using hh
    have hb := physicalProjectedRemainder_integral_bound hs hT hα.fst.measurable hα.snd.measurable B
      hJ hJT hw hθ.le hφ hsmall hr le_rfl le_rfl le_rfl hband' (K:=K)
    have hac := physicalBin_radial_density_near hα.snd.measurable B hJ
      hCρ hp.le hθ.le hφ.le hR le_rfl hden hK
    have hc : 6272*φ≤78400000*φ^2/θ := by
      apply (le_div_iff₀ hθ).mpr
      have hh := mul_le_mul_of_nonneg_left hsmall hφ.le
      nlinarith only [hh,sq_nonneg φ]
    have hacc : ENNReal.ofReal (1974272*θ/(w*φ))*
        ((∫⁻z : ConeCoordinate,ENNReal.ofReal ‖K z.1‖*ENNReal.ofReal (z.1-z.2.1)*
          physicalBinDensity s X V B z.1 z.2.1 z.2.2 ∂physicalBinMeasure V B J))≤
        W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
      calc
        _ ≤ ENNReal.ofReal (1974272*θ/(w*φ))*
            (W*ENNReal.ofReal (49152*Cρ*p^3*θ^2*φ^2*B.rmax*(B.rmax-B.rmin))) :=
          mul_le_mul' le_rfl hac
        _ = W*ENNReal.ofReal (C*(p*θ)^3*φ/w*B.rmax*(B.rmax-B.rmin)) := by
          rw [mul_left_comm,←ENNReal.ofReal_mul (by positivity : 0≤1974272*θ/(w*φ))]
          congr 2
          dsimp [C]
          field_simp [hφ.ne',hw.ne']
        _ ≤ W*(coeff*ENNReal.ofReal (directionWeightMajorant N k)) := by
          apply mul_le_mul' le_rfl
          dsimp [coeff]
          rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
          exact ENNReal.ofReal_le_ofReal (selected_representative_moving_bound hC hw.le
            (hQ k hk).1 (hQ k hk).2.1 (hQ k hk).2.2.2)
    exact hb.trans (add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal hc) le_rfl) hacc)
  change (∑'k,Q.indicator rfun k)≤(∑'k,Q.indicator cfun k)+_
  calc
    _ ≤ ∑'k : Fin 4→ℕ,(Q.indicator cfun k+W*(coeff*ENNReal.ofReal (directionWeightMajorant N k))) := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · simpa only [indicator_of_mem hk] using hbnd k hk
      · simp only [indicator_of_notMem hk,zero_add]
        exact bot_le
    _ = (∑'k,Q.indicator cfun k)+W*(coeff*(∑'k : Fin 4→ℕ,ENNReal.ofReal (directionWeightMajorant N k))) := by
      rw [ENNReal.tsum_add,ENNReal.tsum_mul_left,ENNReal.tsum_mul_left]
    _ ≤ (∑'k,Q.indicator cfun k)+W*(coeff*ENNReal.ofReal (8*(N:ℝ)^2)) :=
      add_le_add le_rfl (mul_le_mul' le_rfl (mul_le_mul' le_rfl (tsum_directionWeightMajorant N)))
    _ = _ := by
      dsimp [coeff]
      rw [←ENNReal.ofReal_mul (by positivity : 0≤4*C*Real.sqrt (max 1 T)/w)]
      congr 3
      ring

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_PhysicalProjectedRemainderSourceTruncate
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

lemma PhaseFlowOn.physicalProjectedRemainder_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V K : ℝ→Vec)
    {z : ConeCoordinate} {w : ℝ} (hr : z.2.1∈Icc 0 T) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z=0 := by
  unfold physicalProjectedRemainderDensity
  suffices h : (∫⁻v in coneBinMomentumSet (representativeClosedBin T w k) z.2.2.1 (velocity (V z.1)),
      ENNReal.ofReal ‖angularMultiplierCLM w (V z.1)
        ((s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))*
            (1-dot z.2.2.1 (velocity (V z.1)))) •
          signedRemainder (z.1-z.2.1) (velocity (V z.1)) (velocity v) z.2.2.1
            (fderiv ℝ velocity (V z.1) (K z.1)))‖)=0 by rw [h,mul_zero]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_coneBinMomentumSet _ _ _)] with v hv
  have hf : s.f (z.2.1,(X z.1-(z.1-z.2.1) • z.2.2.1,v))=0 := by
    by_contra hc
    have hq := F.eulerian_supported_momentum hs hP hr _ v hc
    have hidx := representativeClosedBin_source_indices (sphere_norm z.2.2) hv
      ((mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ)≤1024)).trans hN)
    have hp : sourceRepresentative (k 0)≤128*P := by
      have hh : sourceRepresentative (k 0)/128≤q v := hv.1.1
      linarith only [hh,hq]
    exact hk ⟨hidx.1,hidx.2,hp⟩
  simp only [hf,zero_mul,zero_smul,map_zero,norm_zero,ENNReal.ofReal_zero,Pi.zero_apply]

lemma PhaseFlowOn.physicalProjectedRemainder_integral_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V K : ℝ→Vec) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (w : ℝ) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact F.physicalProjectedRemainder_source_truncate hs hP N hN X V K
    ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ k hk

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCutoffs
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

lemma Admissible.projected_remainder_small_sector_log_sum_oai {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 →
      0<M → 0≤A → 0<P → 1≤Real.log (2+P) → 0<w → w≤P → P≤w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let K := prefixMomentumForce s F.flow T zX
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3)+
      (∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖)*
        ENNReal.ofReal (C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w) := by
  classical
  obtain ⟨Cs,hCs,hcentral⟩ := hd₀.central_density_small_sector_log_sum
  obtain ⟨Cr,hCr,hremainder⟩ := hd₀.projected_remainder_selected_sum
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let C := Cs+Cr*Cn^2
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab hM hA hP hL hw hwP hPw hsource hband HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let K := prefixMomentumForce s F.flow T zX
  let W := ∫⁻t in Icc a b,ENNReal.ofReal ‖K t‖
  let E := ∫x : Vec,totalEnergy s (0,x)
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1}
  let stable : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedRemainderDensity s X V (representativeClosedBin T w k) w K z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  let cfun := fun k : Fin 4→ℕ=>
    ENNReal.ofReal (78400000*(cappedRepresentative (k 2))^2/cappedRepresentative (k 1))*
    (∫⁻z : ConeCoordinate,physicalBinDensity s X V (representativeClosedBin T w k)
      z.1 z.2.1 z.2.2 ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b))
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  let Q := source∩sector
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator rfun=Q.indicator rfun := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,indicator_of_mem (show k∈Q from ⟨hsrc,hk⟩)]
      · rw [indicator_of_mem hk,indicator_of_notMem (show k∉Q from fun h=>hsrc h.1)]
        exact F.physicalProjectedRemainder_integral_source_truncate hs hsource N hN X V K
          hα.snd.measurable measurableSet_Icc hJ w k hsrc
    · rw [indicator_of_notMem hk,indicator_of_notMem (show k∉Q from fun h=>hk h.2)]
  have hQ : ∀k∈Q,k 0<N ∧ k 1<N ∧ cappedRepresentative (k 1) ≤ cappedRepresentative (k 2) ∧
      sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))≤1 := by
    intro k hk
    refine ⟨hk.1.1,hk.1.2.1,?_,hk.2.2⟩
    have hh := hk.2.1
    have hφ := cappedRepresentative_pos (k 2)
    linarith only [hh,hφ]
  have hcsub : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤∑'k : Fin 4→ℕ,stable.indicator cfun k := by
    apply ENNReal.tsum_le_tsum
    intro k
    by_cases hk : k∈Q
    · rw [indicator_of_mem hk,indicator_of_mem (show k∈stable from hk.2.1)]
    · rw [indicator_of_notMem hk]
      exact bot_le
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hL0 : 0≤Real.log (2+P) := zero_le_one.trans hL
  have hc : (∑'k : Fin 4→ℕ,Q.indicator cfun k)≤
      ENNReal.ofReal (C*max 1 T*(1+E)*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^3) := by
    apply (hcsub.trans (hcentral s T F hs hT h0 zX S a b w M A P hS hS0 ha hb hab
      hM hA hP hL hw hwP hPw hsource HX HZ)).trans
    apply ENNReal.ofReal_le_ofReal
    have hCsC : Cs≤C := by dsimp [C]; linarith only [mul_nonneg hCr (sq_nonneg Cn)]
    gcongr
  have hN2 : Cr*Real.sqrt (max 1 T)*(N:ℝ)^2/w≤C*Real.sqrt (max 1 T)*(Real.log (2+P))^2/w := by
    apply div_le_div_of_nonneg_right _ hw.le
    calc
      _ ≤ Cr*Real.sqrt (max 1 T)*(Cn*Real.log (2+P))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hNc _) (by positivity)
      _ = (Cr*Cn^2)*Real.sqrt (max 1 T)*(Real.log (2+P))^2 := by ring
      _ ≤ _ := by
        have hh : Cr*Cn^2≤C := by dsimp [C]; linarith only [hCs]
        gcongr
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k)≤_
  rw [heq]
  exact (hremainder s T F hs hT h0 zX (Icc a b) w N Q hQ measurableSet_Icc hJ hw hband).trans
    (add_le_add hc (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hN2)))

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.projected_remainder_small_sector_log_sum_oai := @OAI.RVM.Admissible.projected_remainder_small_sector_log_sum_oai
