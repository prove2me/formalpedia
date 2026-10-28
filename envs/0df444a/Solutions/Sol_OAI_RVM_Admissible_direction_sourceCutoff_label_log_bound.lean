-- Prove2me | solution 1 for OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:58:29.196454+00:00
-- url     : https://prove2.me/submissions/9c57aeee-681a-4949-84db-3cd4eafc613e

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_projected_source_near_real_bin
import Theorems.Thm_OAI_RVM_Admissible_projected_source_stable_far_log_sum
import Theorems.Thm_OAI_RVM_Admissible_projected_source_structural_edge_log_sum
import Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffLabelCost_triangle
import Theorems.Thm_OAI_RVM_PhaseFlowOn_partialCutoffTriangle_boundary_sum

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

lemma dot_sub_left (a b c : Vec) : dot (a - b) c = dot a c - dot b c := by
  simp [dot, sub_mul, Finset.sum_sub_distrib]

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RepresentativeCosts
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

lemma ennreal_capped_half_sum :
    (∑'n : ℕ,ENNReal.ofReal ((2:ℝ)⁻¹^n)) = 2 := by
  have hsum : Summable (fun n : ℕ=>(2:ℝ)⁻¹^n) := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  rw [←ENNReal.ofReal_tsum_of_nonneg (fun n=>by positivity) hsum]
  rw [tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤2⁻¹) (by norm_num : (2:ℝ)⁻¹<1)]
  norm_num

lemma ennreal_tsum_indicator_lt (N : ℕ) (c : ℝ≥0∞) :
    (∑'n : ℕ,if n<N then c else 0)=(N:ℝ≥0∞)*c := by
  classical
  calc
    _ = ∑n∈Finset.range N,if n<N then c else 0 := by
      apply tsum_eq_sum
      intro n hn
      exact ite_eq_right (fun h=>hn (Finset.mem_range.mpr h))
    _ = _ := by
      rw [Finset.sum_ite_of_true (fun n hn=>Finset.mem_range.mp hn)]
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]

lemma tsum_quad_of_radial_bound (f : (Fin 4→ℕ)→ℝ≥0∞) (N : ℕ) (c : ℝ≥0∞)
    (h : ∀np nt nf, (∑'nr,f ![np,nt,nf,nr]) ≤
      (if np<N ∧ nt<N then c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0)) :
    (∑'k,f k) ≤ c*(2*(N:ℝ≥0∞)^2) := by
  classical
  rw [tsum_quad_index]
  calc
    _ ≤ ∑'np,∑'nt,∑'nf,if np<N ∧ nt<N then c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0 := by
      apply ENNReal.tsum_le_tsum
      intro np
      apply ENNReal.tsum_le_tsum
      intro nt
      exact ENNReal.tsum_le_tsum (h np nt)
    _ = ∑'np,∑'nt,if np<N ∧ nt<N then c*2 else 0 := by
      apply tsum_congr
      intro np
      apply tsum_congr
      intro nt
      by_cases hb : np<N ∧ nt<N
      · simp only [ite_eq_left hb,ENNReal.tsum_mul_left,ennreal_capped_half_sum]
      · simp only [ite_eq_right hb,tsum_zero]
    _ = ∑'np,if np<N then ∑'nt,if nt<N then c*2 else 0 else 0 := by
      apply tsum_congr
      intro np
      by_cases hp : np<N <;> simp [hp]
    _ = c*(2*(N:ℝ≥0∞)^2) := by
      rw [ennreal_tsum_indicator_lt]
      simp only [ennreal_tsum_indicator_lt]
      ring

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

lemma PhaseFlowOn.coneSourceCutoffTangent_continuousOn {s : Solution} {T : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (zX : Phase) :
    ContinuousOn (coneSourceCutoffTangent s F.flow zX) (coneKernelInterior T) :=
  continuousOn_const.prodMk (continuousOn_const.prodMk
    ((F.coneCutoffRate_continuousOn hs zX).snd.snd.fst.prodMk continuousOn_const))

lemma coneSourceCutoffTangent_pullback (s : Solution) (α : Phase→ℝ→Phase)
    (zX : Phase) (T : ℝ) :
    coneSourceCutoffTangent s α zX ∘ labelKernelState α zX T =
      fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,α p.2 p.1)).2 := rfl

lemma PhaseFlowOn.partialCutoffTriangle_source_density_le {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hw : 0<w) (zX : Phase) (Q : Set (Fin 4→ℕ))
    {J : Set ℝ} (hJT : J⊆Icc 0 T) (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (B : ClosedConeBin) {z : ConeCoordinate}
    (hz : z∈physicalBinBase (fun t=>(prefixFlow F.flow T zX t).2) B J) :
    (∫⁻v in coneBinMomentumSet B z.2.2.1 (velocity (prefixFlow F.flow T zX z.1).2),
      ENNReal.ofReal ‖partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)‖)≤
      physicalProjectedSourceDensity s (fun t=>(prefixFlow F.flow T zX t).1)
        (fun t=>(prefixFlow F.flow T zX t).2) B T w Q z := by
  classical
  unfold physicalProjectedSourceDensity
  rw [←lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono
  intro v
  dsimp only
  by_cases hp : (z,v)∈trianglePhaseDomain T
  · have htime := hJT hz.1
    have hprefix : prefixFlow F.flow T zX z.1=F.flow zX z.1 := by
      simp only [prefixFlow,prefixClamp_eq htime]
    have he := normalised_partial_kernel_eq (sub_pos.mpr hp.2.2).ne'
      (cone_denom_pos v z.2.2.1 (sphere_norm z.2.2)).ne'
      (angularMultiplierCLM w (F.flow zX z.1).2)
      (f:=s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v)))
      (D:=1-dot z.2.2.1 (velocity (F.flow zX z.1).2))
      (l:=fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
        (cutoffSourceTangent
          (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)+
            cross (velocity v) (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)))))
      (a:=velocity (F.flow zX z.1).2)
    have htriangle : partialCutoffTriangle s F.flow zX T Q (coneSourceCutoffTangent s F.flow zX)
        (prefixAngularMultiplier s F.flow T w hw zX) J (z,v)=
      (z.1-z.2.1)^2 • ((s.f (z.2.1,((F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1,v))*
        (1-dot z.2.2.1 (velocity (F.flow zX z.1).2))/((z.1-z.2.1)*(1-dot z.2.2.1 (velocity v)))*
          fderiv ℝ (stateCutoff T Q) (z.1-z.2.1,z.2.2.1,v,(F.flow zX z.1).2)
            (cutoffSourceTangent
              (s.E (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1)+
                cross (velocity v) (s.B (z.2.1,(F.flow zX z.1).1-(z.1-z.2.1) • z.2.2.1))))) •
        angularMultiplierCLM w (F.flow zX z.1).2 (signedPrimitive (velocity (F.flow zX z.1).2) (velocity v) z.2.2.1)) := by
      simpa only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_mem hp,
        (prefixAngular_highband hw zX htime (hband _ hz.1)).1,normalisedPartialCutoff,
        coneSourceCutoffTangent,coneCutoffRate,coneCutoffState,triangleKernelState,cutoffSourceTangent,lorentzField,lorentzPhase] using he
    rw [htriangle,norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),ENNReal.ofReal_mul (sq_nonneg _),hprefix]
    apply mul_le_mul' le_rfl
    exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_left (norm_nonneg _))
  · simp only [partialCutoffTriangle_of_mem (p:=(z,v)) hz.1,triangleConeKernel,indicator_of_notMem hp,map_zero,
      norm_zero,ENNReal.ofReal_zero]
    exact bot_le

lemma PhaseFlowOn.actual_sourceCutoff_label_boundary_sum {s : Solution} {T w : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T) (hT : 0≤T)
    (zX : Phase) (Q : Set (Fin 4→ℕ)) (hw : 0<w)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T)
    (hq : ∀t∈J,q (F.flow zX t).2∈Icc (w/8) (8*w))
    (hband : ∀t∈J,w/16≤‖(F.flow zX t).2‖)
    (N : ℕ) (hP : ∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤(2:ℝ)^N) :
    (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖J.indicator (prefixAngularMultiplier s F.flow T w hw zX)
      (labelReceiverTime F.flow zX T p)
      (partialCutoffLabelCost s F.flow zX T Q (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
      ∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}).indicator (fun k=>
        ∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s
          (fun t=>(prefixFlow F.flow T zX t).1) (fun t=>(prefixFlow F.flow T zX t).2)
          (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure (fun t=>(prefixFlow F.flow T zX t).2) (representativeClosedBin T w k) J) k := by
  classical
  have hW := (F.prefixAngular_regular hs hT hw zX).1.measurable
  have hH := F.coneSourceCutoffTangent_continuousOn hs zX
  have he := F.partialCutoffLabelCost_triangle hs hT zX Q hH hW hJ
  rw [coneSourceCutoffTangent_pullback] at he
  rw [he]
  apply (F.partialCutoffTriangle_boundary_sum hs hT zX Q hH hW hJ hJT hq N hP).trans
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈dyadicSelectionBoundary Q∩{k | k 0<N ∧ k 1<N}
  · simp only [indicator_of_mem hk]
    apply lintegral_mono_ae
    have hV : Measurable (fun t=>(prefixFlow F.flow T zX t).2) :=
      ((F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)).snd.measurable
    filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV (representativeClosedBin T w k) hJ)] with z hz
    exact F.partialCutoffTriangle_source_density_le hw zX Q hJT hband _ hz
  · simp only [indicator_of_notMem hk]
    exact le_rfl

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

end RVM

end

open Set Filter Metric MeasureTheory Classical
open scoped ENNReal Topology ContDiff

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

lemma capped_radius_sqrt_sum {H : ℝ} (hH : 1≤H) :
    (∑'n : ℕ,ENNReal.ofReal (Real.sqrt (H*cappedRepresentative n)))≤ENNReal.ofReal (4*H) := by
  have hH0 : 0≤H := zero_le_one.trans hH
  have hs : Real.sqrt H≤H := (Real.sqrt_le_iff.mpr ⟨hH0,by nlinarith only [hH]⟩)
  have hhalf : Real.sqrt ((2:ℝ)⁻¹)≤3/4 := (Real.sqrt_le_iff.mpr ⟨by norm_num,by norm_num⟩)
  have hpow (n : ℕ) : Real.sqrt (cappedRepresentative n)≤(3/4:ℝ)^n := by
    induction n with
    | zero => norm_num [cappedRepresentative]
    | succ n ih =>
      rw [cappedRepresentative,pow_succ,Real.sqrt_mul (by positivity)]
      rw [pow_succ]
      exact mul_le_mul ih hhalf (Real.sqrt_nonneg _) (by positivity)
  have hpoint (n : ℕ) : ENNReal.ofReal (Real.sqrt (H*cappedRepresentative n))≤
      ENNReal.ofReal H*ENNReal.ofReal ((3/4:ℝ)^n) := by
    rw [←ENNReal.ofReal_mul hH0,Real.sqrt_mul hH0]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul hs (hpow n) (Real.sqrt_nonneg _) hH0)
  have hge : (∑'n : ℕ,ENNReal.ofReal ((3/4:ℝ)^n))=4 := by
    have hsum : Summable (fun n : ℕ=>(3/4:ℝ)^n) :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    rw [←ENNReal.ofReal_tsum_of_nonneg (fun n=>by positivity) hsum,
      tsum_geometric_of_lt_one (by norm_num : (0:ℝ)≤3/4) (by norm_num : (3/4:ℝ)<1)]
    norm_num
  calc
    _ ≤ ∑'n : ℕ,ENNReal.ofReal H*ENNReal.ofReal ((3/4:ℝ)^n) := ENNReal.tsum_le_tsum hpoint
    _ = _ := by
      rw [ENNReal.tsum_mul_left,hge,←ENNReal.ofReal_ofNat (n:=4),←ENNReal.ofReal_mul hH0]
      congr 1
      ring

lemma source_low_receiver_scalar {Cg Cb E H p θ φ r w P : ℝ}
    (hCg : 0≤Cg) (hCb : 0≤Cb) (hE : 0≤E) (hH : 1≤H) (hp : 0≤p)
    (hθ : 0≤θ) (hφ : 0<φ) (hr : 0 ≤ r) (hw : 0<w) (hP : 0<P)
    (hple : p≤128*P) (hθφ : θ≤φ) (hφw : φ*w≤32) (hrH : r≤H)
    (hwP : w≤P) (hPw : P≤w^2) :
    Cg*Real.sqrt E*(w/P)^2*p^2*φ^3*Real.sqrt r+
      Cb*Real.sqrt E*Real.sqrt ((w/P)^2)*Real.sqrt ((w/P)^2+2*r)*p^2*θ^2*φ^2*Real.sqrt r≤
    (128^2*32^2*Cg+2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := by
  have hH0 : 0≤H := zero_le_one.trans hH
  have hwp : 0≤w/P := div_nonneg hw.le hP.le
  have hI : (w/P)^2≤1 := by
    have hh : w/P≤1 := (div_le_one hP).mpr hwP
    nlinarith only [hh,hwp]
  have hsE : Real.sqrt E≤1+E := Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hE]⟩
  have hsH : Real.sqrt ((w/P)^2+2*r)≤2*H :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hI,hrH,hH]⟩
  have hφle : φ≤32/w := (le_div_iff₀ hw).mpr hφw
  have hφ3 : φ^3≤(32/w)^2*φ := by
    calc
      _ = φ^2*φ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hφ.le hφle _) hφ.le
  have htφ4 : θ^2*φ^2≤(32/w)^3*φ := by
    calc
      _ ≤ φ^2*φ^2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hθ hθφ _) (sq_nonneg φ)
      _ = φ^3*φ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hφ.le hφle _) hφ.le
  have hrat : P/w^2≤1 := (div_le_one (sq_pos_of_pos hw)).mpr hPw
  have hg : Cg*Real.sqrt E*(w/P)^2*p^2*φ^3*Real.sqrt r≤
      (128^2*32^2*Cg)*(1+E)*H*φ*Real.sqrt r := by
    calc
      _ ≤ Cg*(1+E)*(w/P)^2*(128*P)^2*((32/w)^2*φ)*Real.sqrt r := by gcongr
      _ = (128^2*32^2*Cg)*(1+E)*1*φ*Real.sqrt r := by field_simp
      _ ≤ _ := by gcongr
  have hb : Cb*Real.sqrt E*Real.sqrt ((w/P)^2)*Real.sqrt ((w/P)^2+2*r)*p^2*θ^2*φ^2*Real.sqrt r≤
      (2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := by
    rw [Real.sqrt_sq hwp]
    calc
      _ = Cb*Real.sqrt E*(w/P)*Real.sqrt ((w/P)^2+2*r)*p^2*(θ^2*φ^2)*Real.sqrt r := by ring
      _ ≤ Cb*(1+E)*(w/P)*(2*H)*(128*P)^2*((32/w)^3*φ)*Real.sqrt r := by gcongr
      _ = ((2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r)*(P/w^2) := by field_simp
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hrat
  calc
    _ ≤ (128^2*32^2*Cg)*(1+E)*H*φ*Real.sqrt r+
        (2*128^2*32^3*Cb)*(1+E)*H*φ*Real.sqrt r := add_le_add hg hb
    _ = _ := by ring

lemma PhaseFlowOn.physicalProjectedSource_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec) (Q : Set (Fin 4→ℕ))
    {z : ConeCoordinate} {w : ℝ} (hr : z.2.1∈Icc 0 T) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z=0 := by
  unfold physicalProjectedSourceDensity
  apply mul_eq_zero_of_right
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
  simp only [hf,zero_mul,zero_div,zero_smul,norm_zero,add_zero,ENNReal.ofReal_zero,Pi.zero_apply]

lemma PhaseFlowOn.physicalProjectedSource_integral_source_truncate {s : Solution} {T P : ℝ}
    (F : PhaseFlowOn s.E s.B T) (hs : EnergyPrefix s T)
    (hP : ∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P)
    (N : ℕ) (hN : 1024*P≤(2:ℝ)^N) (X V : ℝ→Vec) (Q : Set (Fin 4→ℕ)) (hV : Measurable V)
    {J : Set ℝ} (hJ : MeasurableSet J) (hJT : J⊆Icc 0 T) (w : ℝ) (k : Fin 4→ℕ)
    (hk : ¬(k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P)) :
    (∫⁻z : ConeCoordinate,physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) J)=0 := by
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (measurableSet_physicalBinBase hV _ hJ)] with z hz
  exact F.physicalProjectedSource_source_truncate hs hP N hN X V Q
    ⟨hz.2.1.1,hz.2.1.2.trans (hJT hz.1).2⟩ k hk

lemma Admissible.projected_source_low_receiver_log_sum {d : Datum} (hd₀ : Admissible d) :
    ∃C : ℝ,0≤C ∧ ∀(s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤T → (∀z,s.f (0,z)=d.f₀ z) →
      ∀(zX : Phase) (S : Set Phase) (Q : Set (Fin 4→ℕ)) (a b w P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤a → b≤T → b-a≤(w/P)^2 → 0<w → w≤P → P≤w^2 → 0<P →
      1≤Real.log (2+P) →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let sector : Set (Fin 4→ℕ) := {k |
        cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
        cappedRepresentative (k 2)*w≤32}
      (∑'k : Fin 4→ℕ,sector.indicator (fun k=>∫⁻z : ConeCoordinate,
        physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
          ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (C*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Cg,Cb,hCg,hCb,hnear⟩ := hd₀.projected_source_near_real_bin
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  let B := 128^2*32^2*Cg+2*128^2*32^3*Cb
  have hB : 0≤B := by dsimp [B]; positivity
  refine ⟨8*B*Cn^2,by positivity,?_⟩
  intro s T F hs hT h0 zX S Q a b w P hS hS0 ha hb hab hw hwP hPw hP hL hsource hband
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let E := ∫x : Vec,totalEnergy s (0,x)
  let I := (w/P)^2
  let H := max 1 T
  let sector : Set (Fin 4→ℕ) := {k |
    cappedRepresentative (k 1) ≤ cappedRepresentative (k 2)/16 ∧
    cappedRepresentative (k 2)*w≤32}
  let rfun := fun k : Fin 4→ℕ=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  have hE : 0≤E := integral_nonneg (hs.total_energy_nonneg ⟨le_rfl,hT⟩)
  have hH : 1≤H := le_max_left _ _
  have hH0 : 0≤H := zero_le_one.trans hH
  obtain ⟨N,hN,hNc⟩ := hcount P hP hL
  let source : Set (Fin 4→ℕ) := {k | k 0<N ∧ k 1<N ∧ sourceRepresentative (k 0)≤128*P}
  let f := (source∩sector).indicator rfun
  let c := 4*B*(1+E)*H^2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα : Continuous (fun t=>prefixFlow F.flow T zX t) :=
    (F.continuous_prefixFlow hs hT).comp (continuous_id.prodMk continuous_const)
  have heq : sector.indicator rfun=f := by
    funext k
    by_cases hk : k∈sector
    · by_cases hsrc : k∈source
      · rw [indicator_of_mem hk,show f k=rfun k from indicator_of_mem (show k∈source∩sector from ⟨hsrc,hk⟩) rfun]
      · rw [indicator_of_mem hk,show f k=0 from indicator_of_notMem (fun h=>hsrc h.1) rfun]
        exact F.physicalProjectedSource_integral_source_truncate hs hsource N hN X V Q
          hα.snd.measurable measurableSet_Icc hJ w k hsrc
    · rw [indicator_of_notMem hk,show f k=0 from indicator_of_notMem (fun h=>hk h.2) rfun]
  have hrad (np nt nf : ℕ) : (∑'nr,f ![np,nt,nf,nr])≤
      (if np<N ∧ nt<N then ENNReal.ofReal c*ENNReal.ofReal ((2:ℝ)⁻¹^nf) else 0) := by
    by_cases hidx : np<N ∧ nt<N
    · rw [ite_eq_left hidx]
      let φ := cappedRepresentative nf
      have hφ : 0<φ := cappedRepresentative_pos _
      let coeff := B*(1+E)*H*φ
      have hcoeff : 0 ≤ coeff := by dsimp [coeff]; positivity
      have hpoint (nr : ℕ) : f ![np,nt,nf,nr]≤
          ENNReal.ofReal coeff*ENNReal.ofReal (Real.sqrt (H*cappedRepresentative nr)) := by
        let k : Fin 4→ℕ := ![np,nt,nf,nr]
        by_cases hk : k∈source∩sector
        · change (source∩sector).indicator rfun k≤_
          rw [indicator_of_mem hk]
          have hh := hnear s T F hs hT h0 zX S Q k a b I w hS hS0 ha hb
            (by dsimp [I]; positivity) hab hw hk.2.1 hband
          apply hh.trans
          rw [←ENNReal.ofReal_mul hcoeff]
          apply ENNReal.ofReal_le_ofReal
          have hp : 0 ≤ sourceRepresentative np := by dsimp [sourceRepresentative]; positivity
          have hθ : 0 ≤ cappedRepresentative nt := (cappedRepresentative_pos _).le
          have hθφ : cappedRepresentative nt≤φ := by
            have ht : cappedRepresentative nt≤φ/16 := hk.2.1
            linarith only [ht,hφ]
          have hrH : H*cappedRepresentative nr≤H := mul_le_of_le_one_right hH0 (cappedRepresentative_le_one nr)
          exact source_low_receiver_scalar hCg hCb hE hH hp hθ hφ
            (mul_nonneg hH0 (cappedRepresentative_pos _).le) hw hP hk.1.2.2 hθφ hk.2.2 hrH hwP hPw
        · change (source∩sector).indicator rfun k≤_
          rw [indicator_of_notMem hk]
          exact bot_le
      have hh := ENNReal.tsum_le_tsum hpoint
      rw [ENNReal.tsum_mul_left] at hh
      apply (hh.trans (mul_le_mul' le_rfl (capped_radius_sqrt_sum hH))).trans_eq
      rw [←ENNReal.ofReal_mul hcoeff,←ENNReal.ofReal_mul hc]
      congr 1
      dsimp [coeff,c,φ,cappedRepresentative]
      ring
    · have hz (nr : ℕ) : f ![np,nt,nf,nr]=0 := by
        apply indicator_of_notMem
        intro hk
        exact hidx ⟨hk.1.1,hk.1.2.1⟩
      simp only [hz,tsum_zero,ite_eq_right hidx,le_refl]
  change (∑'k : Fin 4→ℕ,sector.indicator rfun k)≤_
  rw [heq]
  apply (tsum_quad_of_radial_bound f N (ENNReal.ofReal c) hrad).trans
  have heN : (2:ℝ≥0∞)*(N:ℝ≥0∞)^2=ENNReal.ofReal (2*(N:ℝ)^2) := by
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2),
      ENNReal.ofReal_pow (Nat.cast_nonneg N),ENNReal.ofReal_natCast,ENNReal.ofReal_ofNat]
  rw [heN,←ENNReal.ofReal_mul hc]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ c*(2*(Cn*Real.log (2+P))^2) := by gcongr
    _ = _ := by dsimp [c,H,E]; ring

end RVM

end

section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma dyadic_neighbor_product_le {T : ℝ} {j k : Fin 4→ℕ}
    (h : ∀i,j i≤ k i+2 ∧ k i≤ j i+2) :
    sourceRepresentative (j 0)*cappedRepresentative (j 1)*
      Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤
    32*(sourceRepresentative (k 0)*cappedRepresentative (k 1)*
      Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
  have hH : 0≤ max (1:ℝ) T := le_trans (by norm_num) (le_max_left _ _)
  have hp := sourceRepresentative_le_four (h 0).1
  have hθ := cappedRepresentative_le_four (h 1).2
  have hr := cappedRepresentative_le_four (h 3).2
  have hsqrt : Real.sqrt (max 1 T*cappedRepresentative (j 3)) ≤
      2*Real.sqrt (max 1 T*cappedRepresentative (k 3)) := by
    calc
      _ ≤ Real.sqrt (max 1 T*(4*cappedRepresentative (k 3))) := by gcongr
      _ = _ := by
        rw [show max 1 T*(4*cappedRepresentative (k 3))=4*(max 1 T*cappedRepresentative (k 3)) by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ)≤4)]
        norm_num
  calc
    _ ≤ (4*sourceRepresentative (k 0))*(4*cappedRepresentative (k 1))*
        (2*Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
      have hpk : 0 < sourceRepresentative (k 0) := by dsimp [sourceRepresentative]; positivity
      have hθk := cappedRepresentative_pos (k 1)
      exact mul_le_mul (mul_le_mul hp hθ (cappedRepresentative_pos _).le (by positivity))
        hsqrt (Real.sqrt_nonneg _) (by positivity)
    _ = _ := by ring

lemma directionSelection_boundary_split {T : ℝ} {k : Fin 4→ℕ}
    (hk : k∈dyadicSelectionBoundary (directionSelection T)) :
    cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/64 ∧
    (cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∨
      1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
        Real.sqrt (max 1 T*cappedRepresentative (k 3))) := by
  have hu := dyadicSelectionBoundary_direction (T:=T) (κ:=1/1024) (by norm_num)
    (Q:=directionSelection T) (fun j hj=>hj) hk
  refine ⟨by linarith only [hu.1],?_⟩
  by_cases hs : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
  · exact Or.inl hs
  · right
    obtain ⟨j,hjn,hnear⟩ := hk.2
    have hjθ := cappedRepresentative_le_four (hnear 1).2
    have hkφ := cappedRepresentative_le_four (hnear 2).1
    have hjselect : cappedRepresentative (j 1)≤(1/1024)*cappedRepresentative (j 2) := by
      linarith only [hjθ,hkφ,lt_of_not_ge hs]
    have hjprod : 1< sourceRepresentative (j 0)*cappedRepresentative (j 1)*
        Real.sqrt (max 1 T*cappedRepresentative (j 3)) := by
      by_contra hh
      exact hjn ⟨hjselect,le_of_not_gt hh⟩
    have hp := dyadic_neighbor_product_le (T:=T) hnear
    linarith only [hjprod,hp]

lemma direction_source_cover_sum {T w P : ℝ} (f : (Fin 4→ℕ)→ℝ≥0∞)
    (S : Set (Fin 4→ℕ))
    (hS : ∀k∈S,cappedRepresentative (k 1)≤ cappedRepresentative (k 2)/16 ∧
      (cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1) ∨
        1/32≤ sourceRepresentative (k 0)*cappedRepresentative (k 1)*
          Real.sqrt (max 1 T*cappedRepresentative (k 3))))
    (hf : ∀k,¬sourceRepresentative (k 0)≤128*P→f k=0) :
    (∑'k,S.indicator f k)≤
      (∑'k,directionSourceEdge.indicator f k)+
      (∑'k,(directionSourceFar T w P).indicator f k)+
      (∑'k,(directionSourceLow w).indicator f k) := by
  classical
  rw [←ENNReal.tsum_add,←ENNReal.tsum_add]
  apply ENNReal.tsum_le_tsum
  intro k
  by_cases hk : k∈S
  · rw [Set.indicator_of_mem hk]
    by_cases hp : sourceRepresentative (k 0)≤128*P
    · obtain ⟨hθ,hcase⟩ := hS k hk
      by_cases he : cappedRepresentative (k 2)≤16384*cappedRepresentative (k 1)
      · have hm : k∈directionSourceEdge := ⟨he,hθ⟩
        rw [Set.indicator_of_mem hm]
        exact (le_add_of_nonneg_right (bot_le)).trans (le_add_of_nonneg_right (bot_le))
      · by_cases hl : cappedRepresentative (k 2)*w≤32
        · have hm : k∈directionSourceLow w := ⟨hθ,hl⟩
          rw [Set.indicator_of_mem hm]
          exact le_add_of_nonneg_left (bot_le)
        · have hm : k∈directionSourceFar T w P := ⟨hp,hθ,(lt_of_not_ge hl).le,hcase.resolve_left he⟩
          rw [Set.indicator_of_mem hm]
          exact (le_add_of_nonneg_left (bot_le)).trans (le_add_of_nonneg_right (bot_le))
    · rw [hf k hp]
      exact bot_le
  · rw [Set.indicator_of_notMem hk]
    exact bot_le

lemma Admissible.direction_boundary_source_log_sum {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let X := fun t=>(prefixFlow F.flow T zX t).1
      let V := fun t=>(prefixFlow F.flow T zX t).2
      let E := ∫x : Vec,totalEnergy s (0,x)
      let Q := directionSelection T
      (∑'k : Fin 4→ℕ,(dyadicSelectionBoundary Q).indicator (fun k=>∫⁻z : ConeCoordinate,
          physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
            ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)) k)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Ce,hCe,hedge⟩ := hd₀.projected_source_structural_edge_log_sum
  obtain ⟨Cf,hCf,hfar⟩ := hd₀.projected_source_stable_far_log_sum T₀
  obtain ⟨Cl,hCl,hlow⟩ := hd₀.projected_source_low_receiver_log_sum
  refine ⟨Ce,Cf,Cl,hCe,hCf,hCl,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw hwP hPw hsource hW HX HZ
  dsimp only
  let X := fun t=>(prefixFlow F.flow T zX t).1
  let V := fun t=>(prefixFlow F.flow T zX t).2
  let Q := directionSelection T
  let f := fun k=>∫⁻z : ConeCoordinate,
    physicalProjectedSourceDensity s X V (representativeClosedBin T w k) T w Q z
      ∂physicalBinMeasure V (representativeClosedBin T w k) (Icc a b)
  have hj : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hα := (F.continuous_prefixFlow hs hT).comp
    (continuous_id.prodMk continuous_const : Continuous (fun t : ℝ=>(t,zX)))
  obtain ⟨Cn,hCn,hcount⟩ := exists_direct_dyadic_count
  obtain ⟨N,hN,_⟩ := hcount P hP hL
  have h1024 : 1024*P≤(2:ℝ)^N := by linarith only [hN,hP]
  have hzero (k : Fin 4→ℕ) (hk : ¬sourceRepresentative (k 0)≤128*P) : f k=0 := by
    apply F.physicalProjectedSource_integral_source_truncate hs hsource N h1024 X V Q
      hα.snd.measurable measurableSet_Icc hj w k
    intro hc
    exact hk hc.2.2
  have hroute (k : Fin 4→ℕ) (hk : k∈dyadicSelectionBoundary Q) :=
    directionSelection_boundary_split hk
  have hh := direction_source_cover_sum (T:=T) (w:=w) (P:=P) f (dyadicSelectionBoundary Q)
    (fun k hk=>⟨by have hφ := cappedRepresentative_pos (k 2); linarith only [(hroute k hk).1,hφ],
      (hroute k hk).2⟩) hzero
  apply hh.trans
  exact add_le_add (add_le_add
    (hedge s T F hs hT h0 zX S Q a b w M A P hS hS0 ha hb hab hJI hM hA hP hL
      (zero_lt_one.trans_le hw) hwP hsource hW HX HZ)
    (hfar s T F hs hT hTT h0 zX S Q a b w M A P hS hS0 ha hb hJI hM hA
      (zero_lt_one.trans_le hP) hL hw hwP hW HX HZ))
    (hlow s T F hs hT h0 zX S Q a b w P hS hS0 ha hb hJI
      (zero_lt_one.trans_le hw) hwP hPw (zero_lt_one.trans_le hP) hL hsource hW)

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

namespace RVM

lemma tsum_set_indicator_mono {ι : Type*} {A B : Set ι} (hAB : A⊆B)
    (f : ι→ℝ≥0∞) : (∑'i,A.indicator f i)≤∑'i,B.indicator f i := by
  classical
  apply ENNReal.tsum_le_tsum
  intro i
  by_cases hi : i∈A
  · rw [Set.indicator_of_mem hi,Set.indicator_of_mem (hAB hi)]
  · rw [Set.indicator_of_notMem hi]
    exact bot_le

lemma Admissible.direction_sourceCutoff_label_log_bound_oai {d : Datum} (hd₀ : Admissible d)
    (T₀ : ℝ) :
    ∃Ce Cf Cl : ℝ,0≤ Ce ∧ 0≤ Cf ∧ 0≤ Cl ∧
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      EnergyPrefix s T → 0≤ T → T≤ T₀ → (∀z,s.f (0,z)=d.f₀ z) →
    ∀ (zX : Phase) (S : Set Phase) (a b w M A P : ℝ) (hw : 0<w),
      IsCompact S → tsupport (fun z=>s.f (0,z))⊆S →
      0≤ a → b≤ T → a≤ b → b-a≤(w/P)^2 →
      0< M → 0≤ A → 1≤ P → 1≤ Real.log (2+P) → 1≤ w → w≤ P → P≤ w^2 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤ P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
      (∀t∈Icc a b,w/16≤‖(F.flow zX t).2‖) →
      IncrementBootstrap (fun t=>(F.flow zX t).2) T M A P (Real.log (2+P)) →
      (∀z∈S,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      let E := ∫x : Vec,totalEnergy s (0,x)
      (∫⁻p : ℝ×Phase,ENNReal.ofReal ‖(Icc a b).indicator (prefixAngularMultiplier s F.flow T w hw zX)
        (labelReceiverTime F.flow zX T p)
        (partialCutoffLabelCost s F.flow zX T (directionSelection T)
          (fun p=>cutoffSourceTangent (lorentzField s.E s.B (p.1,F.flow p.2 p.1)).2) p)‖)≤
      ENNReal.ofReal (Ce*(1+E)*(1+M+Real.sqrt A)*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cf*E*(1+16384*(M+Real.sqrt A))*w*(Real.log (2+P))^5)+
      ENNReal.ofReal (Cl*(1+E)*(max 1 T)^2*(Real.log (2+P))^2) := by
  classical
  obtain ⟨Ce,Cf,Cl,hCe,hCf,hCl,hbound⟩ := hd₀.direction_boundary_source_log_sum T₀
  refine ⟨Ce,Cf,Cl,hCe,hCf,hCl,?_⟩
  intro s T F hs hT hTT h0 zX S a b w M A P hw hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hq hW HX HZ
  dsimp only
  obtain ⟨Cn,hCn,hcount⟩ := exists_source_dyadic_count
  obtain ⟨N,hN,_⟩ := hcount P (zero_lt_one.trans_le hP) hL
  have hEuler (σ : ℝ) (hσ : σ∈Icc 0 T) (z : Phase) (hf : s.f (σ,z)≠0) :
      1024*q z.2≤(2:ℝ)^N :=
    (mul_le_mul_of_nonneg_left (F.eulerian_supported_momentum hs hsource hσ z.1 z.2 hf)
      (by norm_num : (0:ℝ)≤1024)).trans hN
  apply (F.actual_sourceCutoff_label_boundary_sum hs hT zX (directionSelection T) hw
    measurableSet_Icc (Icc_subset_Icc ha hb) hq hW N hEuler).trans
  apply (tsum_set_indicator_mono inter_subset_left _).trans
  exact hbound s T F hs hT hTT h0 zX S a b w M A P hS hS0 ha hb hab hJI hM hA hP hL hw1 hwP hPw hsource hW HX HZ

end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound_oai := @OAI.RVM.Admissible.direction_sourceCutoff_label_log_bound_oai
