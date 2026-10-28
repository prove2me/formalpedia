-- Prove2me | solution 1 for OAI.RVM.family_local_spatially_smooth_bounded_classical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T12:28:07.415253+00:00
-- url     : https://prove2.me/submissions/8660ed1d-65e5-4efc-af09-c76c3fd6b688

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_family_picard_field_limit
import Theorems.Thm_OAI_RVM_local_c1_limit_of_picard
import Theorems.Thm_OAI_RVM_mixed_electric_physical_representation
import Theorems.Thm_OAI_RVM_mixed_magnetic_physical_representation
import Theorems.Thm_OAI_RVM_transported_comparison
import Theorems.Thm_OAI_RVM_uniform_picard_sequence_jets

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

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Geometry_ParticleBySpacetime
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

lemma compactSupport_of_zero_off {W : Type*} [Zero W]
    {K : Set Vec} {g : Vec → W} (hK : IsCompact K)
    (hz : ∀ v ∉ K, g v = 0) : HasCompactSupport g := by
  apply hK.of_isClosed_subset (isClosed_tsupport _)
  apply closure_minimal _ hK.isClosed
  intro v hv
  by_contra hn
  exact hv (hz v hn)

lemma contDiffOn_integral_uniform_support
    {H W : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {n : ℕ∞} {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hU : IsOpen U) (hK : IsCompact K)
    (hF : ContDiffOn ℝ n F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContDiffOn ℝ n (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := contDiffOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) contDiffOn_const (g := fun x v => F (x,v))
    hU hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_EnergyBump
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set
open scoped ContDiff

namespace RVM
open scoped Topology

lemma continuousOn_integral_uniform_support
    {H W : Type*} [TopologicalSpace H]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {U : Set H} {K : Set Vec} {F : H × Vec → W}
    (hK : IsCompact K) (hF : ContinuousOn F (U ×ˢ univ))
    (hzero : ∀ x ∈ U, ∀ v ∉ K, F (x,v) = 0) :
    ContinuousOn (fun x => ∫ v : Vec, F (x,v)) U := by
  have h := continuousOn_convolution_right_with_param_comp
    (μ := (volume : Measure Vec)) (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] W →L[ℝ] W)
    (v := fun _ : H => (0 : Vec)) continuousOn_const (g := fun x v => F (x,v))
    hK (fun x v hx hv => hzero x hx v hv) (locallyIntegrable_const (1 : ℝ)) hF
  have hn (x : H) : convolution (fun _ : Vec => (1 : ℝ)) (fun v => F (x,v))
      (ContinuousLinearMap.lsmul ℝ ℝ) volume 0 = ∫ v : Vec, F (x,v) := by
    simp only [convolution_def, zero_sub, ContinuousLinearMap.lsmul_apply, one_smul]
    exact integral_neg_eq_self (fun v : Vec => F (x,v)) volume
  simpa only [hn] using h

end RVM

end

open MeasureTheory Set
open scoped ContDiff
open Filter Set
open scoped Topology
open Set MeasureTheory Filter
open scoped Topology ContDiff

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Maxwell_DifferenceFieldEnergy
attribute [-instance] _root_.OAI.RVM.phaseVolume_isAddHaarMeasure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma norm_sub_sq_le_twice (x y : Vec) :
    ‖x-y‖^2  ≤  2*‖x‖^2+2*‖y‖^2 := by
  have h := norm_sub_le x y
  nlinarith [norm_nonneg (x-y),norm_nonneg x,norm_nonneg y,sq_nonneg (‖x‖-‖y‖)]

lemma pair_sq_difference_tendsto {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0))
    {s : ℝ} (hs : 0 ≤ s) :
    Tendsto (fun t => ∫ x : Vec, ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2)
      (𝓝[Ici 0] s) (𝓝 0) := by
  let e : ℝ → Vec → ℝ := fun t x => ‖E (t,x)‖^2+‖B (t,x)‖^2
  let D : ℝ → Vec → ℝ := fun t x => ‖E (t,x)-E (s,x)‖^2+‖B (t,x)-B (s,x)‖^2
  let g : ℝ → Vec → ℝ := fun t x => min (4*e s x) (2*e t x+2*e s x-D t x)
  have heI (t : ℝ) (ht : 0 ≤ t) : Integrable (e t) :=
    ((memLp_two_iff_integrable_sq_norm (hLp t ht).1.aestronglyMeasurable).mp (hLp t ht).1).add
      ((memLp_two_iff_integrable_sq_norm (hLp t ht).2.aestronglyMeasurable).mp (hLp t ht).2)
  have hDI (t : ℝ) (ht : 0 ≤ t) : Integrable (D t) := by
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt).add
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt)
  have hD0 (t : ℝ) (x : Vec) : 0 ≤ D t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have he0 (t : ℝ) (x : Vec) : 0 ≤ e t x := add_nonneg (sq_nonneg _) (sq_nonneg _)
  have hDle (t : ℝ) (x : Vec) : D t x ≤ 2*e t x+2*e s x := by
    have h1 := norm_sub_sq_le_twice (E (t,x)) (E (s,x))
    have h2 := norm_sub_sq_le_twice (B (t,x)) (B (s,x))
    dsimp only [D,e]
    linarith
  have hg0 (t : ℝ) (x : Vec) : 0 ≤ g t x :=
    le_min (mul_nonneg (by norm_num) (he0 s x)) (sub_nonneg.mpr (hDle t x))
  have hgI (t : ℝ) (ht : 0 ≤ t) : Integrable (g t) :=
    ((heI s hs).const_mul 4).inf (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
  have hgc (x : Vec) : Continuous (fun t => g t x) := by
    apply continuous_const.min
    exact ((((hE.comp (continuous_id.prodMk continuous_const)).norm.pow 2).add
      ((hB.comp (continuous_id.prodMk continuous_const)).norm.pow 2)).const_mul 2 |>.add continuous_const |>.sub
      ((((hE.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2).add
        (((hB.comp (continuous_id.prodMk continuous_const)).sub continuous_const).norm.pow 2)))
  have hgs (x : Vec) : g s x=4*e s x := by
    dsimp only [g,D]
    simp only [sub_self,norm_zero,zero_pow (by norm_num : 2≠0),add_zero,sub_zero]
    rw [show 2*e s x+2*e s x=4*e s x by ring,min_self]
  have hglim : Tendsto (fun t => ∫ x : Vec, g t x) (𝓝[Ici 0] s) (𝓝 (4*∫ x : Vec, e s x)) := by
    rw [← integral_const_mul]
    apply tendsto_integral_filter_of_dominated_convergence (fun x => 4*e s x)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact (hgI t ht).aestronglyMeasurable
    · exact Eventually.of_forall (fun t => ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (hg0 t x)]
        exact min_le_left _ _))
    · exact (heI s hs).const_mul 4
    · exact ae_of_all _ (fun x => by
        simpa only [hgs] using
          ((hgc x).continuousAt (x:=s)).continuousWithinAt (s:=Ici 0) |>.tendsto)
  have hlim : Tendsto (fun t => 2*(∫ x : Vec, e t x)+2*(∫ x : Vec, e s x)-∫ x : Vec, g t x)
      (𝓝[Ici 0] s) (𝓝 0) := by
    have hh := (((henergy s hs).tendsto.const_mul 2).add_const (2*∫ x : Vec, e s x)).sub hglim
    convert hh using 1
    all_goals try with_reducible_and_instances rfl
    dsimp only [e]
    congr 1
    ring
  apply squeeze_zero' (Eventually.of_forall (fun t => integral_nonneg (hD0 t))) ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with t ht
  have hm : (∫ x : Vec, g t x) ≤ ∫ x : Vec, 2*e t x+2*e s x-D t x :=
    integral_mono (hgI t ht) (((heI t ht).const_mul 2).add ((heI s hs).const_mul 2) |>.sub (hDI t ht))
      (fun x => min_le_right _ _)
  have hsum : Integrable (fun x => 2*e t x+2*e s x) :=
    ((heI t ht).const_mul 2).add ((heI s hs).const_mul 2)
  rw [integral_sub hsum (hDI t ht),
    integral_add ((heI t ht).const_mul 2) ((heI s hs).const_mul 2),integral_const_mul,integral_const_mul] at hm
  linarith

lemma L2_norm_sub_sq_eq_integral {u v : Lp Vec 2 (volume : Measure Vec)}
    {f g : Vec → Vec} (hu : (u : Vec → Vec) =ᵐ[volume] f)
    (hv : (v : Vec → Vec) =ᵐ[volume] g) :
    ‖u-v‖^2=∫ x : Vec, ‖f x-g x‖^2 := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub u v,hu,hv] with x hsub hf hg
  rw [hsub]
  simp only [Pi.sub_apply,hf,hg,real_inner_self_eq_norm_sq]

lemma timeContinuousL2_of_continuous_energy {E B : Field}
    (hE : Continuous E) (hB : Continuous B)
    (hLp : ∀ t, 0 ≤ t → MemLp (fun x => E (t,x)) 2 volume ∧
      MemLp (fun x => B (t,x)) 2 volume)
    (henergy : ContinuousOn (fun t => ∫ x : Vec, ‖E (t,x)‖^2+‖B (t,x)‖^2) (Ici 0)) :
    TimeContinuousL2 E ∧ TimeContinuousL2 B := by
  classical
  let E₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).1.toLp (fun x => E (t,x)) else 0
  let B₂ : ℝ → Lp Vec 2 (volume : Measure Vec) := fun t =>
    if ht : 0 ≤ t then (hLp t ht).2.toLp (fun x => B (t,x)) else 0
  have hEe (t : ℝ) (ht : 0 ≤ t) : (E₂ t : Vec → Vec) =ᵐ[volume] (fun x => E (t,x)) := by
    dsimp only [E₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hBe (t : ℝ) (ht : 0 ≤ t) : (B₂ t : Vec → Vec) =ᵐ[volume] (fun x => B (t,x)) := by
    dsimp only [B₂]; rw [dite_eq_left ht]; exact MemLp.coeFn_toLp _
  have hlim (s : ℝ) (hs : 0 ≤ s) :
      Tendsto (fun t => ‖E₂ t-E₂ s‖^2+‖B₂ t-B₂ s‖^2) (𝓝[Ici 0] s) (𝓝 0) := by
    apply (pair_sq_difference_tendsto hE hB hLp henergy hs).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [L2_norm_sub_sq_eq_integral (hEe t ht) (hEe s hs),
      L2_norm_sub_sq_eq_integral (hBe t ht) (hBe s hs)]
    have hEt := (hLp t ht).1.sub (hLp s hs).1
    have hBt := (hLp t ht).2.sub (hLp s hs).2
    exact (integral_add
      ((memLp_two_iff_integrable_sq_norm hEt.aestronglyMeasurable).mp hEt)
      ((memLp_two_iff_integrable_sq_norm hBt.aestronglyMeasurable).mp hBt))
  have hEc : ContinuousOn E₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖E₂ t-E₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_right (sq_nonneg ‖B₂ t-B₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  have hBc : ContinuousOn B₂ (Ici 0) := by
    intro s hs
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    have hsq := squeeze_zero' (Eventually.of_forall (fun t : ℝ => sq_nonneg ‖B₂ t-B₂ s‖))
      (Eventually.of_forall (fun t : ℝ => le_add_of_nonneg_left (sq_nonneg ‖E₂ t-E₂ s‖))) (hlim s hs)
    simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
      (Real.continuous_sqrt.continuousAt.tendsto.comp hsq)
  exact ⟨⟨E₂,hEc,hEe⟩,⟨B₂,hBc,hBe⟩⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_VlasovConstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff RealInnerProductSpace

namespace RVM

lemma timeContinuousL2_compact {F : Field} (hF : Continuous F)
    (hK : ∀ T, 0 ≤ T → ∃ K : Set Vec, IsCompact K ∧
      ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=0) : TimeContinuousL2 F := by
  have hLp (t : ℝ) (ht : 0 ≤ t) : MemLp (fun x => F (t,x)) 2 volume := by
    obtain ⟨K,hK,hz⟩ := hK t ht
    exact (hF.comp (continuous_const.prodMk continuous_id)).memLp_of_hasCompactSupport
      (compactSupport_of_zero_off hK (hz t ⟨ht,le_rfl⟩))
  have he : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Ici 0) := by
    intro s hs
    change 0 ≤ s at hs
    obtain ⟨K,hK,hz⟩ := hK (s+1) (by linarith : 0 ≤ s+1)
    have hc : ContinuousOn (fun t => ∫ x : Vec, ‖F (t,x)‖^2) (Icc 0 (s+1)) :=
      continuousOn_integral_uniform_support hK (hF.norm.pow 2).continuousOn
        (fun t ht x hx => by change ‖F (t,x)‖^2=0; rw [hz t ht x hx]; simp)
    apply (hc s ⟨hs,by linarith⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (lt_add_one s))] with t ht ht'
    exact ⟨ht,ht'.le⟩
  have hh := timeContinuousL2_of_continuous_energy (B:=0) hF continuous_const
    (fun t ht => ⟨hLp t ht,MemLp.zero⟩) (by simpa using he)
  exact hh.1

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


lemma integrableOn_norm_rpow_neg {α R : ℝ} (hα : α<3) :
    IntegrableOn (fun z : Vec => ‖z‖ ^ (-α)) (ball (0:Vec) R) := by
  apply integrableOn_ball_of_norm_le_rpow (by simp) (C:=1) (α:=α) (by simpa using hα)
  · exact ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]; simp)
  · exact (continuous_norm.measurable.pow measurable_const).aestronglyMeasurable

lemma coneDirection_norm {x y : Vec} (h : x≠y) : ‖coneDirection x y‖=1 := by
  have hr : 0<‖x-y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
  simp [coneDirection,coneRadius,norm_smul,hr.ne']



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


lemma contDiff_dot_pair {k : ℕ∞ω} :
    ContDiff ℝ k (fun z : Vec × Vec => dot z.1 z.2) := by
  unfold dot
  fun_prop

lemma contDiffAt_coneRadius {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneRadius x) y :=
  (contDiffAt_const.sub contDiffAt_id).norm ℝ (sub_ne_zero.mpr hxy)

lemma contDiffAt_coneDirection {k : ℕ∞ω} {x y : Vec} (hxy : x≠y) :
    ContDiffAt ℝ k (coneDirection x) y :=
  ((contDiffAt_coneRadius hxy).inv (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy))).smul
    (contDiffAt_const.sub contDiffAt_id)

lemma contDiffAt_retardedDensity {k : ℕ∞ω} {f : Particle} {x y v : Vec} {t : ℝ}
    (hf : ContDiffAt ℝ k f (t-coneRadius x y,y,v)) (hxy : x≠y) :
    ContDiffAt ℝ k (retardedDensity f t x) (y,v) := by
  have hr : ContDiffAt ℝ k (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=k) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hm : ContDiffAt ℝ k (fun z : Phase => (t-coneRadius x z.1,z)) (y,v) :=
    ((contDiffAt_const (c:=t)).sub hr).prodMk contDiffAt_id
  exact hf.comp (f:=fun z : Phase => (t-coneRadius x z.1,z)) (y,v) hm

lemma particle_contDiffAt_positive {k : ℕ∞ω} {f : Particle}
    (hf : ContDiffOn ℝ k f particleHalfSpace) {t : ℝ} (ht : 0<t) (x v : Vec) :
    ContDiffAt ℝ k f (t,x,v) := by
  have hn : particleHalfSpace ∈ 𝓝 (t,x,v) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Phase → ℝ))).mem_nhds ht)
      (fun z hz => show 0≤z.1 from hz.le)
  exact (hf _ ht.le).contDiffAt hn

lemma isOpen_retardedSpaceDomain (t : ℝ) (x : Vec) : IsOpen (retardedSpaceDomain t x) := by
  have h₁ : IsOpen {y : Vec | y≠x} := isOpen_ne
  have h₂ : IsOpen {y : Vec | 0<t-coneRadius x y} :=
    isOpen_lt continuous_const (continuous_const.sub ((continuous_const.sub continuous_id).norm))
  convert h₁.inter h₂ using 1
  all_goals try with_reducible_and_instances rfl
  ext y
  simp only [retardedSpaceDomain,mem_ofPred_eq,mem_inter_iff,ne_comm]

lemma retarded_local_data {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ∃ K : Set Vec, IsCompact K ∧
      ContDiffOn ℝ 1 (retardedDensity s.f t x) (retardedSpaceDomain t x ×ˢ univ) ∧
      ∀ y ∈ retardedSpaceDomain t x, ∀ v ∉ K, retardedDensity s.f t x (y,v)=0 := by
  obtain ⟨K,hK,hz⟩ := hc t ht
  refine ⟨Prod.snd '' K,hK.image continuous_snd,?_,?_⟩
  · intro z hz
    exact (contDiffAt_retardedDensity
      (particle_contDiffAt_positive hf hz.1.2 z.1 z.2) hz.1.1).contDiffWithinAt
  · intro y hy v hv
    by_contra hne
    have htime : t-coneRadius x y ∈ Icc 0 t :=
      ⟨hy.2.le,sub_le_self _ (norm_nonneg _)⟩
    exact hv ⟨(y,v),hz _ htime (subset_tsupport _ hne),rfl⟩

end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_SourceWaveSpatialIbp
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

lemma uniform_integral_bound_compact {H W : Type*}
    [TopologicalSpace H] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {P : Set H} {K : Set Vec} {F : H × Vec → W}
    (hP : IsCompact P) (hK : IsCompact K)
    (hF : ContinuousOn F (P ×ˢ univ)) (hz : ∀ p ∈ P, ∀ v ∉ K, F (p,v)=0) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ∈ P, ‖∫ v : Vec, F (p,v)‖≤C := by
  obtain ⟨C,hC⟩ := ((hP.prod hK).image_of_continuousOn (hF.mono (by intro z hz; exact ⟨hz.1,mem_univ _⟩))).isBounded.exists_norm_le
  refine ⟨max C 0*volume.real K,mul_nonneg (le_max_right _ _) (measureReal_nonneg),?_⟩
  intro p hp
  have hc : Continuous (fun v : Vec => F (p,v)) :=
    hF.comp_continuous (continuous_const.prodMk continuous_id) (fun v => ⟨hp,mem_univ _⟩)
  have hi : Integrable (fun v : Vec => F (p,v)) :=
    hc.integrable_of_hasCompactSupport (compactSupport_of_zero_off hK (hz p hp))
  have hfi : (∫ v : Vec, F (p,v))=∫ v in K, F (p,v) := by
    symm
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (hz p hp)
  rw [hfi]
  apply le_trans (norm_integral_le_integral_norm _)
  calc
    (∫ v in K, ‖F (p,v)‖) ≤ ∫ v in K, max C 0 := by
      apply integral_mono_ae hi.norm.integrableOn
        (integrableOn_const (hK.measure_lt_top.ne))
      filter_upwards [ae_restrict_mem hK.measurableSet] with v hv
      exact le_trans (hC _ ⟨(p,v),⟨hp,hv⟩,rfl⟩) (le_max_left _ _)
    _ = max C 0*volume.real K := by simp [mul_comm]

lemma coneRadius_add (x z : Vec) : coneRadius x (x+z)=‖z‖ := by
  unfold coneRadius
  rw [show x-(x+z) = -z by abel,norm_neg]

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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma normalisedElectricKernel_eq {r : ℝ} (hr : r≠0) (n u b : Vec) :
    normalisedElectricKernel r n u b=r^2 • physicalElectricKernel r n u b := by
  ext i
  simp only [normalisedElectricKernel,physicalElectricKernel,PiLp.add_apply,PiLp.smul_apply,
    PiLp.sub_apply,smul_eq_mul]
  field_simp

lemma continuousOn_normalisedElectricKernel {H : Type*} [TopologicalSpace H]
    {r : H → ℝ} {n u b : H → Vec} {S : Set H}
    (hr : ContinuousOn r S) (hn : ContinuousOn n S) (hu : ContinuousOn u S)
    (hb : ContinuousOn b S) (hd : ∀ z ∈ S, 1-dot (n z) (u z)≠0) :
    ContinuousOn (fun z => normalisedElectricKernel (r z) (n z) (u z) (b z)) S := by
  have hdot (f g : H → Vec) (hf : ContinuousOn f S) (hg : ContinuousOn g S) :
      ContinuousOn (fun z => dot (f z) (g z)) S :=
    (contDiff_dot_pair (k:=1)).continuous.comp_continuousOn (hf.prodMk hg)
  have hD : ContinuousOn (fun z => 1-dot (n z) (u z)) S :=
    continuousOn_const.sub (hdot n u hn hu)
  have hp : ∀ z ∈ S, (1-dot (n z) (u z))^3≠0 := fun z hz => pow_ne_zero 3 (hd z hz)
  exact (((continuousOn_const.sub (hdot u u hu hu)).div (hD.pow 3) hp).smul (hn.sub hu)).add
    ((hr.div (hD.pow 3) hp).smul (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma field_contDiffAt_positive {k : ℕ∞ω} {F : Field}
    (hF : ContDiffOn ℝ k F fieldHalfSpace) {t : ℝ} (ht : 0<t) (x : Vec) :
    ContDiffAt ℝ k F (t,x) := by
  have hn : fieldHalfSpace ∈ 𝓝 (t,x) :=
    mem_of_superset ((isOpen_lt continuous_const
      (continuous_fst : Continuous (Prod.fst : ℝ × Vec → ℝ))).mem_nhds ht)
      (fun p hp => show 0≤p.1 from hp.le)
  exact (hF _ ht.le).contDiffAt hn

lemma contDiffAt_physicalElectricKernel {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {k : ℕ∞ω} {r : H → ℝ} {n u b : H → Vec} {z : H}
    (hr : ContDiffAt ℝ k r z) (hn : ContDiffAt ℝ k n z) (hu : ContDiffAt ℝ k u z)
    (hb : ContDiffAt ℝ k b z) (hr0 : r z≠0) (hd0 : 1-dot (n z) (u z)≠0) :
    ContDiffAt ℝ k (fun p => physicalElectricKernel (r p) (n p) (u p) (b p)) z := by
  have hdot (f g : H → Vec) (hf : ContDiffAt ℝ k f z) (hg : ContDiffAt ℝ k g z) :
      ContDiffAt ℝ k (fun p => dot (f p) (g p)) z :=
    contDiff_dot_pair.contDiffAt.comp z (hf.prodMk hg)
  have hD : ContDiffAt ℝ k (fun p => 1-dot (n p) (u p)) z :=
    contDiffAt_const.sub (hdot n u hn hu)
  exact (((contDiffAt_const.sub (hdot u u hu hu)).div ((hr.pow 2).mul (hD.pow 3))
      (mul_ne_zero (pow_ne_zero 2 hr0) (pow_ne_zero 3 hd0))).smul (hn.sub hu)).add
    (((hr.mul (hD.pow 3)).inv (mul_ne_zero hr0 (pow_ne_zero 3 hd0))).smul
      (((hdot n b hn hb).smul (hn.sub hu)).sub (hD.smul hb)))

lemma contDiffAt_retardedElectricIntegrand {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    {t : ℝ} {x y v : Vec} (hxy : x≠y) (ht : 0<t-coneRadius x y) :
    ContDiffAt ℝ 1 (fun z : Phase =>
      (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
        physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
          (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+
            cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))))) (y,v) := by
  have hr : ContDiffAt ℝ 1 (fun z : Phase => coneRadius x z.1) (y,v) :=
    (contDiffAt_coneRadius (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hn : ContDiffAt ℝ 1 (fun z : Phase => coneDirection x z.1) (y,v) :=
    (contDiffAt_coneDirection (k:=1) hxy).comp (f:=Prod.fst) (y,v) contDiffAt_fst
  have hu : ContDiffAt ℝ 1 (fun z : Phase => velocity z.2) (y,v) :=
    contDiff_velocity.contDiffAt.comp (y,v) contDiffAt_snd
  have harg : ContDiffAt ℝ 1 (fun z : Phase => (t-coneRadius x z.1,z.1)) (y,v) :=
    (contDiffAt_const.sub hr).prodMk contDiffAt_fst
  have he := (field_contDiffAt_positive hE ht y).comp (y,v) harg
  have hm := (field_contDiffAt_positive hB ht y).comp (y,v) harg
  have hcross : ContDiffAt ℝ 1 (fun z : Phase =>
      cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1))) (y,v) :=
    contDiff_cross.contDiffAt.comp (y,v) (hu.prodMk hm)
  have hdf : ContDiff ℝ 1 (fderiv ℝ velocity) :=
    (contDiff_velocity (k:=2)).fderiv_right (by norm_num)
  have hb : ContDiffAt ℝ 1 (fun z : Phase => fderiv ℝ velocity z.2
      (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))) (y,v) :=
    (hdf.contDiffAt.comp (y,v) contDiffAt_snd).clm_apply (he.add hcross)
  have hd0 : 1-dot (coneDirection x y) (velocity v)≠0 :=
    (cone_denom_pos v _ (coneDirection_norm hxy)).ne'
  have hk := contDiffAt_physicalElectricKernel hr hn hu hb
    (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)) hd0
  exact ((contDiffAt_retardedDensity (particle_contDiffAt_positive hf ht y v) hxy).mul
    (contDiffAt_const.sub (contDiff_dot_pair.contDiffAt.comp (y,v) (hn.prodMk hu)))).smul hk

lemma contDiffOn_retardedElectricDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedElectricDensity s t x) (retardedSpaceDomain t x) := by
  obtain ⟨K,hK,_,hz⟩ := retarded_local_data hf hc ht x
  unfold retardedElectricDensity
  apply contDiffOn_integral_uniform_support (n:=1)
    (F:=fun z : Phase => (s.f (t-coneRadius x z.1,z.1,z.2)*(1-dot (coneDirection x z.1) (velocity z.2))) •
      physicalElectricKernel (coneRadius x z.1) (coneDirection x z.1) (velocity z.2)
        (fderiv ℝ velocity z.2 (s.E (t-coneRadius x z.1,z.1)+cross (velocity z.2) (s.B (t-coneRadius x z.1,z.1)))))
    (isOpen_retardedSpaceDomain t x) hK
  · intro z hz
    exact (contDiffAt_retardedElectricIntegrand hf hE hB hz.1.1 hz.1.2).contDiffWithinAt
  · intro y hy v hv
    change (retardedDensity s.f t x (y,v)*_) • _=0
    rw [hz y hy v hv,zero_mul,zero_smul]

lemma integrableOn_ball_of_punctured_bound {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : Vec → W} {R C α : ℝ} (hα : α<3)
    (hF : ContinuousOn F (ball (0:Vec) R \ {0}))
    (hb : ∀ z : Vec, 0<‖z‖ → ‖z‖<R → ‖F z‖≤C*‖z‖^(-α)) :
    IntegrableOn F (ball (0:Vec) R) := by
  have hae : (ball (0:Vec) R \ ({0} : Set Vec) : Set Vec) =ᵐ[volume] (ball (0:Vec) R : Set Vec) := by
    filter_upwards [volume.ae_ne (0:Vec)] with z hz
    apply propext
    exact ⟨fun h => h.1, fun h => ⟨h, hz⟩⟩
  have hmeas : AEStronglyMeasurable F (volume.restrict (ball (0:Vec) R)) := by
    rw [← Measure.restrict_congr_set hae]
    exact hF.aestronglyMeasurable (measurableSet_ball.diff (measurableSet_singleton _))
  apply ((integrableOn_norm_rpow_neg hα).const_mul C).mono' hmeas
  filter_upwards [ae_restrict_mem measurableSet_ball,
    ae_restrict_of_ae (volume.ae_ne (0:Vec))] with z hz hz0
  exact hb z (norm_pos_iff.mpr hz0) (by simpa only [mem_ball_zero_iff] using hz)

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Retarded_MagneticMomentDensity
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma contDiffOn_retardedMagneticDensity {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t : ℝ} (ht : 0≤t) (x : Vec) :
    ContDiffOn ℝ 1 (retardedMagneticDensity s t x) (retardedSpaceDomain t x) := by
  intro y hy
  have hn : ContDiffAt ℝ 1 (coneDirection x) y := contDiffAt_coneDirection hy.1
  exact (contDiff_cross.contDiffAt.comp y (hn.prodMk
    ((contDiffOn_retardedElectricDensity hf hE hB hc ht x).contDiffAt
      ((isOpen_retardedSpaceDomain t x).mem_nhds hy)))).contDiffWithinAt

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_RetardedWeightedIntegralBound
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma retarded_weighted_integral_bound_le {W : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {s : Solution} (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec)
    {A : (Vec × Vec) × Vec → W}
    (hA : ContinuousOn A ((closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ)) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, ‖z‖≤R → ∀ n : Vec, ‖n‖=1 →
      ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) • A ((z,n),v)‖≤C := by
  have ht : 0≤t := le_trans hR hRt
  obtain ⟨K,hK,hz⟩ := hc t ht
  let P : Set (Vec × Vec) := closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1
  have hP : IsCompact P := (isCompact_closedBall (0:Vec) R).prod (isCompact_sphere (0:Vec) 1)
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1,p.2)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk
      ((continuous_const.add continuous_fst.fst).prodMk continuous_snd)
  have htime (z : Vec) (hz' : z ∈ closedBall (0:Vec) R) : t-‖z‖ ∈ Icc 0 t := by
    have hn : ‖z‖≤R := by simpa only [mem_closedBall_zero_iff] using hz'
    exact ⟨by linarith,sub_le_self _ (norm_nonneg _)⟩
  have hcf : ContinuousOn (fun p : (Vec × Vec) × Vec => s.f (t-‖p.1.1‖,x+p.1.1,p.2)) (P ×ˢ univ) :=
    hf.continuousOn.comp harg.continuousOn (fun p hp => (htime p.1.1 hp.1.1).1)
  have hzero : ∀ p ∈ P, ∀ v ∉ Prod.snd '' K, s.f (t-‖p.1‖,x+p.1,v) • A (p,v)=0 := by
    intro p hp v hv
    have hsf : s.f (t-‖p.1‖,x+p.1,v)=0 := by
      by_contra hne
      exact hv ⟨(x+p.1,v),hz _ (htime p.1 hp.1) (subset_tsupport _ hne),rfl⟩
    rw [hsf,zero_smul]
  obtain ⟨C,hC,hb⟩ := uniform_integral_bound_compact hP (hK.image continuous_snd) (hcf.smul hA) hzero
  refine ⟨C,hC,?_⟩
  intro z hz n hn
  exact hb (z,n) ⟨by simpa only [mem_closedBall_zero_iff] using hz,
    by simpa only [mem_sphere,dist_zero_right] using hn⟩

lemma retarded_electric_kernel_norm_bound_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContinuousOn s.E fieldHalfSpace) (hB : ContinuousOn s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    ∃ C : ℝ, 0≤C ∧ ∀ z : Vec, 0<‖z‖ → ‖z‖≤R →
      ‖∫ v : Vec, (s.f (t-coneRadius x (x+z),x+z,v)*
        (1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel (coneRadius x (x+z)) (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-coneRadius x (x+z),x+z)+
            cross (velocity v) (s.B (t-coneRadius x (x+z),x+z))))‖≤C/‖z‖^2 := by
  let S : Set ((Vec × Vec) × Vec) := (closedBall (0:Vec) R ×ˢ sphere (0:Vec) 1) ×ˢ univ
  let u : (Vec × Vec) × Vec → Vec := fun p => velocity p.2
  let n : (Vec × Vec) × Vec → Vec := fun p => p.1.2
  let b : (Vec × Vec) × Vec → Vec := fun p => fderiv ℝ velocity p.2
    (s.E (t-‖p.1.1‖,x+p.1.1)+cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1)))
  have hu : Continuous u := (contDiff_velocity (k:=1)).continuous.comp continuous_snd
  have hn : Continuous n := continuous_fst.snd
  have harg : Continuous (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) :=
    (continuous_const.sub (continuous_fst.fst.norm)).prodMk (continuous_const.add continuous_fst.fst)
  have hmap : MapsTo (fun p : (Vec × Vec) × Vec => (t-‖p.1.1‖,x+p.1.1)) S fieldHalfSpace := by
    intro p hp
    have hnz : ‖p.1.1‖≤R := by simpa only [mem_closedBall_zero_iff] using hp.1.1
    change 0≤t-‖p.1.1‖
    linarith
  have he := hE.comp harg.continuousOn hmap
  have hm := hB.comp harg.continuousOn hmap
  have hcross : ContinuousOn (fun p : (Vec × Vec) × Vec =>
      cross (velocity p.2) (s.B (t-‖p.1.1‖,x+p.1.1))) S :=
    (contDiff_cross (k:=1)).continuous.comp_continuousOn (hu.continuousOn.prodMk hm)
  have hb : ContinuousOn b S :=
    (((contDiff_velocity (k:=1)).continuous_fderiv (by simp)).comp continuous_snd).continuousOn.clm_apply (he.add hcross)
  have hD : Continuous (fun p : (Vec × Vec) × Vec => 1-dot (n p) (u p)) :=
    continuous_const.sub ((contDiff_dot_pair (k:=1)).continuous.comp (hn.prodMk hu))
  have hD0 (p : (Vec × Vec) × Vec) (hp : p ∈ S) : 1-dot (n p) (u p)≠0 := by
    apply (cone_denom_pos _ _ ?_).ne'
    simpa only [n,mem_sphere,dist_zero_right] using hp.1.2
  have hN := continuousOn_normalisedElectricKernel (S:=S)
    continuous_fst.fst.norm.continuousOn hn.continuousOn hu.continuousOn hb hD0
  obtain ⟨C,hC,hbound⟩ := retarded_weighted_integral_bound_le hf hc hR hRt x (hD.continuousOn.smul hN)
  refine ⟨C,hC,?_⟩
  intro z hz0 hzR
  have hxy : x≠x+z := by
    intro h
    apply (norm_pos_iff.mp hz0)
    exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
  have hh := hbound z hzR (coneDirection x (x+z)) (coneDirection_norm hxy)
  have heq : (∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))) =
      ‖z‖^2 • ∫ v : Vec, (s.f (t-‖z‖,x+z,v)*(1-dot (coneDirection x (x+z)) (velocity v))) •
        physicalElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))) := by
    rw [← integral_smul]
    apply integral_congr_ae
    filter_upwards [] with v
    rw [normalisedElectricKernel_eq hz0.ne']
    simp only [smul_smul]
    congr 1
    ring
  change ‖∫ v : Vec, s.f (t-‖z‖,x+z,v) •
      ((1-dot (coneDirection x (x+z)) (velocity v)) •
        normalisedElectricKernel ‖z‖ (coneDirection x (x+z)) (velocity v)
          (fderiv ℝ velocity v (s.E (t-‖z‖,x+z)+cross (velocity v) (s.B (t-‖z‖,x+z)))))‖≤C at hh
  rw [heq,norm_smul,Real.norm_of_nonneg (sq_nonneg _)] at hh
  simp only [coneRadius_add]
  apply (le_div_iff₀ (sq_pos_of_pos hz0)).mpr
  simpa only [mul_comm] using hh

lemma integrableOn_retardedElectricDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedElectricDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hcont := (contDiffOn_retardedElectricDensity hf hE hB hc ht x).continuousOn
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont' := hcont.comp (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (C:=C) (α:=2) (by norm_num) hcont'
  intro z hz hzR
  have hh := hbound z hz hzR.le
  change ‖retardedElectricDensity s t x (x+z)‖≤C*‖z‖^(-(2:ℝ))
  rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]
  exact hh

lemma integrableOn_retardedMagneticDensity_le {s : Solution}
    (hf : ContDiffOn ℝ 1 s.f particleHalfSpace)
    (hE : ContDiffOn ℝ 1 s.E fieldHalfSpace) (hB : ContDiffOn ℝ 1 s.B fieldHalfSpace)
    (hc : CompactOnFiniteHorizons s) {t R : ℝ} (hR : 0≤R) (hRt : R≤t) (x : Vec) :
    IntegrableOn (fun z => retardedMagneticDensity s t x (x+z)) (ball (0:Vec) R) := by
  have ht : 0≤t := le_trans hR hRt
  have hm : MapsTo (fun z : Vec => x+z) (ball (0:Vec) R \ {0}) (retardedSpaceDomain t x) := by
    intro z hz
    have hn : ‖z‖<R := by simpa only [mem_ball_zero_iff] using hz.1
    have hzero : z≠0 := by simpa only [mem_singleton_iff] using hz.2
    refine ⟨?_,?_⟩
    · intro h
      apply hzero
      exact add_left_cancel (show x+z=x+0 by simpa using h.symm)
    · rw [coneRadius_add]
      linarith
  have hcont := (contDiffOn_retardedMagneticDensity hf hE hB hc ht x).continuousOn.comp
    (continuous_const.add continuous_id).continuousOn hm
  obtain ⟨C,_,hbound⟩ := retarded_electric_kernel_norm_bound_le hf hE.continuousOn hB.continuousOn hc hR hRt x
  apply integrableOn_ball_of_punctured_bound (α:=2) (C:=C) (by norm_num) hcont
  intro z hz hzR
  have hxy : x≠x+z := (hm ⟨by simpa only [mem_ball_zero_iff] using hzR,by simpa only [mem_singleton_iff] using norm_pos_iff.mp hz⟩).1
  calc
    ‖retardedMagneticDensity s t x (x+z)‖ ≤ ‖coneDirection x (x+z)‖*‖retardedElectricDensity s t x (x+z)‖ := norm_cross_le _ _
    _ = ‖retardedElectricDensity s t x (x+z)‖ := by rw [coneDirection_norm hxy,one_mul]
    _ ≤ C/‖z‖^2 := hbound z hz hzR.le
    _ = C*‖z‖^(-(2:ℝ)) := by rw [Real.rpow_neg (norm_nonneg z),Real.rpow_two]; rfl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_ContinuousIntegralSphere
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
open scoped Topology ContDiff RealInnerProductSpace
open scoped Topology ContDiff NNReal RealInnerProductSpace
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff ENNReal
open Set
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma coneBoundary_radius {T a : ℝ} (hT : 0<T) (ha : a ∈ Icc 0 (T/2)) {n : Vec}
    (hn : n ∈ sphere (0:Vec) 1) (x : Vec) : coneRadius x (x+(T-a) • n)=T-a := by
  rw [coneRadius_add,norm_smul,Real.norm_of_nonneg (by linarith [ha.2]),
    show ‖n‖=1 by simpa only [mem_sphere,dist_zero_right] using hn,mul_one]

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

lemma electricConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    electricConeBoundary s t x i 0=electricConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedElectricFlux s t x i (x+t • n.1)=
      retardedElectricFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedElectricFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold electricConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [rho,current,hf]

lemma magneticConeBoundary_initial_congr {s s' : Solution}
    (hf : ∀ z, s.f (0,z)=s'.f (0,z)) (hE : ∀ x, s.E (0,x)=s'.E (0,x))
    (hB : ∀ x, s.B (0,x)=s'.B (0,x)) {t : ℝ} (ht : 0<t) (x : Vec) (i : Fin 3) :
    magneticConeBoundary s t x i 0=magneticConeBoundary s' t x i 0 := by
  have hflux (n : Sphere) : retardedMagneticFlux s t x i (x+t • n.1)=
      retardedMagneticFlux s' t x i (x+t • n.1) := by
    have hr : coneRadius x (x+t • n.1)=t := by
      simpa only [sub_zero] using coneBoundary_radius ht
        (show (0:ℝ)∈Icc 0 (t/2) from ⟨le_rfl,by linarith⟩) n.2 x
    unfold retardedMagneticFlux retardedDensity
    dsimp only
    rw [hr,sub_self]
    simp_rw [hf]
  unfold magneticConeBoundary
  simp only [sub_zero]
  simp_rw [hE,hB,hflux]
  simp only [current,hf]

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBoundary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma smooth_compact_lipschitz {U W : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] {f : U → W}
    (hf : ContDiff ℝ 1 f) (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y, ‖f y-f x‖≤C*‖y-x‖ := by
  obtain ⟨D,hD⟩ := (hf.continuous_fderiv (by norm_num)).bounded_above_of_compact_support (hc.fderiv ℝ)
  refine ⟨max D 0,le_max_right _ _,?_⟩
  intro x y
  exact (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => hf.differentiable (by norm_num) z)
    (fun z _ => (hD z).trans (le_max_left _ _)) (mem_univ x) (mem_univ y)

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma mixed_physical_vector {s : Solution} {E B : Field}
    (hf : ContDiff ℝ ∞ s.f) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hE' : ContDiff ℝ ∞ s.E) (hB' : ContDiff ℝ ∞ s.B)
    (hc : CompactOnFiniteHorizons s) (hV : TransportFor s E B)
    (hρ : ContDiff ℝ ∞ (fun p : ℝ × Vec => rho (fun q => s.f (p.1,q)) p.2))
    (hj : ContDiff ℝ ∞ (fun p : ℝ × Vec => current (fun q => s.f (p.1,q)) p.2))
    (hM : MaxwellFor s) {t : ℝ} (ht : 0<t) (x : Vec) :
    s.E (t,x)=electricBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedElectricDensity {s with E:=E,B:=B} t x (x+z) ∧
    s.B (t,x)=magneticBoundaryField s t x+
      (4*Real.pi)⁻¹ • ∫ z in ball (0:Vec) t, retardedMagneticDensity {s with E:=E,B:=B} t x (x+z) := by
  have hf1 : ContDiffOn ℝ 1 s.f particleHalfSpace := (hf.of_le (by simp)).contDiffOn
  have hE1 : ContDiffOn ℝ 1 E fieldHalfSpace := (hE.of_le (by simp)).contDiffOn
  have hB1 : ContDiffOn ℝ 1 B fieldHalfSpace := (hB.of_le (by simp)).contDiffOn
  constructor
  · ext i
    have hD := integrableOn_retardedElectricDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_electric_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hρ hj hM ht x i).trans
      (by simpa only [electricBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => electricConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)
  · ext i
    have hD := integrableOn_retardedMagneticDensity_le (s:={s with E:=E,B:=B}) hf1 hE1 hB1 hc ht.le le_rfl x
    have he := (PiLp.proj 2 (𝕜:=ℝ) (fun _ : Fin 3 => ℝ) i).integral_comp_comm hD
    exact (mixed_magnetic_physical_representation (s:={s with E:=E,B:=B})
      hf1 hE1 hB1 hc hV hE' hB' hj hM ht x i).trans
      (by simpa only [magneticBoundaryField,PiLp.add_apply,PiLp.smul_apply,PiLp.toLp_apply,
        smul_eq_mul,PiLp.proj_apply] using congrArg (fun r : ℝ => magneticConeBoundary s t x i 0+(4*Real.pi)⁻¹*r) he)

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma PicardRegular.boundary_eq {d : Datum} {s : Solution} (hs : PicardRegular d s)
    {t : ℝ} (ht : 0<t) (x : Vec) :
    electricBoundaryField s t x=electricBoundaryField (datumBoundarySolution d) t x ∧
    magneticBoundaryField s t x=magneticBoundaryField (datumBoundarySolution d) t x := by
  constructor
  · ext i
    exact electricConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i
  · ext i
    exact magneticConeBoundary_initial_congr (s':=datumBoundarySolution d)
      hs.initial_f hs.initial_E hs.initial_B ht x i

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_PicardContraction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma exists_uniform_limit_geometric {X W : Type*} [NormedAddCommGroup W] [CompleteSpace W]
    {F : ℕ → X → W} {S : Set X} {C : ℝ}
    (h : ∀ n, ∀ x∈S, ‖F (n+1) x-F n x‖≤C*(1/2:ℝ)^n) :
    ∃ f : X → W, TendstoUniformlyOn F f atTop S := by
  let g : ℕ → X → W := fun n x => F (n+1) x-F n x
  have hu : Summable (fun n => C*(1/2:ℝ)^n) :=
    (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1/2:ℝ)<1)).mul_left C
  have hh := tendstoUniformlyOn_tsum_nat hu (f:=g) h
  refine ⟨fun x => F 0 x+∑' n, g n x,?_⟩
  rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
  intro ε hε
  filter_upwards [hh ε hε] with n hn x hx
  have he : (∑ i∈Finset.range n, g i x)=F n x-F 0 x := Finset.sum_range_sub (fun n => F n x) n
  specialize hn x hx
  rw [he,dist_eq_norm] at hn
  rw [dist_eq_norm]
  convert hn using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  abel

lemma geometric_picard_particle_differences {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T L N : ℝ} (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B)
    (hg : ∀ n, ∀ t∈Icc 0 T, ∀ x,
      ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
      ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) :
    ∃ C : ℝ, 0≤C ∧ ∀ n, ∀ t∈Icc 0 T, ∀ z : Phase,
      |(S (n+1+1)).f (t,z)-(S (n+1)).f (t,z)|≤C*(1/2:ℝ)^n := by
  obtain ⟨A,hA,hAf⟩ := smooth_compact_lipschitz (hd.1.of_le (by simp)) hd.2.1
  let K := 1+2*N+L
  have hK : 0≤K := by dsimp [K]; positivity
  refine ⟨4*A*Real.exp (K*T)*L*T,by positivity,?_⟩
  intro n t ht z
  have hh := transported_comparison (hr (n+1)).1.smooth_f (hr n).1.smooth_f
    (hsm (n+1)).1 (hsm (n+1)).2 (hsm n).1 (hsm n).2 (hr (n+1)).2 (hr n).2
    (hr (n+1)).1.initial_f (hr n).1.initial_f hA hL hN (D:=2*L*(1/2:ℝ)^n) (by positivity)
    (fun z w => by simpa only [Real.norm_eq_abs] using hAf w z)
    (fun r hr x => ((hc (n+1)).1 r hr x).2)
    (fun r hr x y => ((hc (n+1)).2 r hr x y).1)
    (fun r hr x y => ((hc (n+1)).2 r hr x y).2)
    (fun r hr x => (hg n r hr x).1) (fun r hr x => (hg n r hr x).2) ht z z
  simp only [sub_self,norm_zero,zero_add] at hh
  have he := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
  apply hh.trans
  calc
    _ ≤ A*(2*(2*L*(1/2:ℝ)^n)*T)*Real.exp (K*T) :=
      mul_le_mul (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left ht.2 (by positivity)) hA) he (Real.exp_pos _).le (by positivity)
    _ = (4*A*Real.exp (K*T)*L*T)*(1/2:ℝ)^n := by ring

lemma picard_particle_limit {d : Datum} (hd : Admissible d)
    {S : ℕ → Solution} {T A R P L N M : ℝ} (hT : 0≤T) (hL : 0≤L) (hN : 0≤N)
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hc : ∀ n, FieldControl T L N (S n).E (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)) ∧ TransportFor (S (n+1)) (S n).E (S n).B ∧
      LocalParticleBound T A R P (S (n+1)).f ∧ PhaseParticleLip T M (S (n+1)).f)
    (hg : ∀ n, ∀ t∈Icc 0 T, ∀ x,
      ‖(S (n+1)).E (t,x)-(S n).E (t,x)‖≤2*L*(1/2:ℝ)^n ∧
      ‖(S (n+1)).B (t,x)-(S n).B (t,x)‖≤2*L*(1/2:ℝ)^n) :
    ∃ f : Particle, TendstoUniformlyOn (fun n => (S (n+1)).f) f atTop {p | p.1∈Icc 0 T} ∧
      ContinuousOn f {p | p.1∈Icc 0 T} ∧ (∀ t∈Icc 0 T, ∀ z, 0≤f (t,z)) ∧
      (∀ z, f (0,z)=d.f₀ z) ∧ LocalParticleBound T A R P f ∧ PhaseParticleLip T M f := by
  obtain ⟨C,hC,hg'⟩ := geometric_picard_particle_differences hd hT hL hN hsm hc
    (fun n => ⟨(hr n).1,(hr n).2.1⟩) hg
  obtain ⟨f,hf⟩ := exists_uniform_limit_geometric (F:=fun n => (S (n+1)).f) (C:=C)
    (fun n (p : ℝ × Phase) (hp : p.1∈Icc 0 T) => by simpa only [Real.norm_eq_abs] using hg' n p.1 hp p.2)
  refine ⟨f,hf,hf.continuousOn (Frequently.of_forall fun n => (hr n).1.smooth_f.continuous.continuousOn),?_,?_,?_,?_⟩
  · intro t ht z
    exact ge_of_tendsto (hf.tendsto_at (x:=(t,z)) ht) (Eventually.of_forall fun n => (hr n).1.nonneg _)
  · intro z
    have hh := hf.tendsto_at (x:=(0,z)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT⟩)
    simp only [(hr _).1.initial_f] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  · intro t ht x v
    have hb : |f (t,x,v)|≤A := le_of_tendsto (hf.tendsto_at (x:=(t,x,v)) ht).abs
      (Eventually.of_forall fun n => ((hr n).2.2.1 t ht x v).1)
    refine ⟨hb,?_⟩
    intro hn
    by_contra hnot
    have hz (n : ℕ) : (S (n+1)).f (t,x,v)=0 := by
      by_contra hnn
      exact hnot (((hr n).2.2.1 t ht x v).2 hnn)
    have hh := hf.tendsto_at (x:=(t,x,v)) ht
    simp only [hz] at hh
    exact hn (tendsto_nhds_unique hh tendsto_const_nhds)
  · intro t ht z z'
    exact le_of_tendsto ((hf.tendsto_at (x:=(t,z)) ht).sub (hf.tendsto_at (x:=(t,z')) ht)).abs
      (Eventually.of_forall fun n => (hr n).2.2.2 t ht z z')

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma picard_field_exterior {d : Datum} {s : Solution} {E B : Field}
    (hs : PicardRegular d s) (hE : ContDiff ℝ ∞ E) (hB : ContDiff ℝ ∞ B)
    (hV : TransportFor s E B) {T A R P t : ℝ} (hb : LocalParticleBound T A R P s.f)
    (ht : t∈Ioc 0 T) (x : Vec) (hx : R+T<‖x‖) :
    s.E (t,x)=electricBoundaryField (datumBoundarySolution d) t x ∧
      s.B (t,x)=magneticBoundaryField (datumBoundarySolution d) t x := by
  have he := mixed_physical_vector hs.smooth_f hE hB hs.smooth_E hs.smooth_B hs.compact hV
    hs.smooth_rho hs.smooth_current hs.maxwell ht.1 x
  have hz (z : Vec) (hz : z∈ball (0:Vec) t) :
      retardedElectricDensity {s with E:=E,B:=B} t x (x+z)=0 := by
    have hnorm : ‖z‖<t := by simpa only [mem_ball,dist_zero_right] using hz
    have hr : coneRadius x (x+z)=‖z‖ := by simp [coneRadius]
    have htime : t-coneRadius x (x+z)∈Icc 0 T := by rw [hr]; exact ⟨by linarith,by linarith [norm_nonneg z,ht.2]⟩
    have hloc : R<‖x+z‖ := by
      have htri := norm_sub_le (x+z) z
      have hid : x+z-z=x := by abel
      rw [hid] at htri
      linarith [ht.2]
    have hfzero (v : Vec) : s.f (t-coneRadius x (x+z),x+z,v)=0 := by
      by_contra hn
      exact (not_le_of_gt hloc) (((hb _ htime (x+z) v).2 hn).1)
    simp only [retardedElectricDensity,hfzero,zero_mul,zero_smul,integral_zero]
  have hzB (z : Vec) (hz' : z∈ball (0:Vec) t) :
      retardedMagneticDensity {s with E:=E,B:=B} t x (x+z)=0 := by
    rw [retardedMagneticDensity,hz z hz']
    ext i; fin_cases i <;> simp [cross]
  have hiE : (∫ z in ball (0:Vec) t,retardedElectricDensity {s with E:=E,B:=B} t x (x+z))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact hz
  have hiB : (∫ z in ball (0:Vec) t,retardedMagneticDensity {s with E:=E,B:=B} t x (x+z))=0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    exact hzB
  simp only [hiE,hiB,smul_zero,add_zero] at he
  exact ⟨he.1.trans (hs.boundary_eq ht.1 x).1,he.2.trans (hs.boundary_eq ht.1 x).2⟩

lemma picard_uniform_limit_exterior {d : Datum} {S : ℕ → Solution} {E B : Field} {T A R P : ℝ}
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hV : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop {p | p.1∈Icc 0 T})
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop {p | p.1∈Icc 0 T}) :
    ∀ t∈Icc 0 T, ∀ x, R+T<‖x‖ → E (t,x)=(S 1).E (t,x) ∧ B (t,x)=(S 1).B (t,x) := by
  intro t ht x hx
  have hE := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at (x:=(t,x)) ht
  have hB := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at (x:=(t,x)) ht
  have heq (n : ℕ) : (S (n+1)).E (t,x)=(S 1).E (t,x) ∧ (S (n+1)).B (t,x)=(S 1).B (t,x) := by
    rcases eq_or_lt_of_le ht.1 with ht0|ht0
    · subst t
      exact ⟨(hr n).initial_E x |>.trans ((hr 0).initial_E x).symm,
        (hr n).initial_B x |>.trans ((hr 0).initial_B x).symm⟩
    · have hn := picard_field_exterior (hr n) (hsm n).1 (hsm n).2 (hV n) (hb n) ⟨ht0,ht.2⟩ x hx
      have hz := picard_field_exterior (hr 0) (hsm 0).1 (hsm 0).2 (hV 0) (hb 0) ⟨ht0,ht.2⟩ x hx
      exact ⟨hn.1.trans hz.1.symm,hn.2.trans hz.2.symm⟩
  have he (n : ℕ) := (heq n).1
  have hb' (n : ℕ) := (heq n).2
  simp only [he] at hE
  simp only [hb'] at hB
  exact ⟨tendsto_nhds_unique hE tendsto_const_nhds,tendsto_nhds_unique hB tendsto_const_nhds⟩

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

lemma taylor_remainder_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) (x y : U) :
    ‖f y-f x-fderiv ℝ f x (y-x)‖≤H*‖y-x‖^2 := by
  have h := (convex_closedBall x ‖y-x‖).norm_image_sub_le_of_norm_fderiv_le'
    (f:=f) (φ:=fderiv ℝ f x) (C:=H*‖y-x‖) (fun z _ => hf z)
    (fun z hz => (hD x z).trans (mul_le_mul_of_nonneg_left
      (by simpa only [mem_closedBall,dist_eq_norm] using hz) hH))
    (show x∈closedBall x ‖y-x‖ by simp)
    (show y∈closedBall x ‖y-x‖ by simp only [mem_closedBall,dist_eq_norm,le_refl])
  exact h.trans_eq (by ring)

lemma curvature_of_fderiv_lipschitz {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : Differentiable ℝ f) {H : ℝ} (hH : 0≤H)
    (hD : ∀ x y, ‖fderiv ℝ f y-fderiv ℝ f x‖≤H*‖y-x‖) : CurvatureBound f (2*H) := by
  intro x v
  have hp := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x+v)
  have hm := taylor_remainder_of_fderiv_lipschitz hf hH hD x (x-v)
  simp only [add_sub_cancel_left,sub_sub_cancel_left,norm_neg,map_neg] at hp hm
  have he : f (x+v)+f (x-v)-(2:ℝ) • f x =
      (f (x+v)-f x-fderiv ℝ f x v)+(f (x-v)-f x+fderiv ℝ f x v) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add hp (by simpa only [sub_neg_eq_add] using hm))).trans_eq (by ring)

lemma CurvatureBound.add {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x+g x) (H+K) := by
  intro x v
  have he : f (x+v)+g (x+v)+(f (x-v)+g (x-v))-(2:ℝ) • (f x+g x)=
      (f (x+v)+f (x-v)-(2:ℝ) • f x)+(g (x+v)+g (x-v)-(2:ℝ) • g x) := by module
  rw [he]
  exact ((norm_add_le _ _).trans (add_le_add (hf x v) (hg x v))).trans_eq (by ring)

lemma CurvatureBound.neg {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hf : CurvatureBound f H) : CurvatureBound (fun x => -f x) H := by
  intro x v
  simpa only [← neg_add,smul_neg,neg_sub_neg,norm_sub_rev] using hf x v

lemma CurvatureBound.sub {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H K : ℝ} (hf : CurvatureBound f H) (hg : CurvatureBound g K) :
    CurvatureBound (fun x => f x-g x) (H+K) := by
  simpa only [sub_eq_add_neg] using hf.add hg.neg

lemma curvature_of_second_derivative_bound {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} (hf : ContDiff ℝ ∞ f) {H : ℝ} (hH : 0≤H)
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 f x‖≤H) : CurvatureBound f (2*H) := by
  apply curvature_of_fderiv_lipschitz (hf.differentiable (by simp)) hH
  intro x y
  apply (convex_univ : Convex ℝ (univ : Set U)).norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (hf.fderiv_right (by decide : (1:ℕ∞ω)+1≤∞)).differentiable (by norm_num) z) _ (mem_univ _) (mem_univ _)
  intro z _
  simpa only [← norm_iteratedFDeriv_one,norm_iteratedFDeriv_fderiv] using hb z

end


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_CurvatureInterpolation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma CurvatureBound.taylor {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (x v : U) :
    ‖f (x+v)-f x-fderiv ℝ f x v‖≤H*‖v‖^2 := by
  let q : ℕ → W := fun n => (2:ℝ)^n • (f (x+(1/2:ℝ)^n • v)-f x)
  have hD : HasDerivAt (fun t : ℝ => f (x+t • v)) (fderiv ℝ f x v) 0 := by
    have hd := (hf (x+(0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ)
      ((hasDerivAt_const (0:ℝ) x).add ((hasDerivAt_id (0:ℝ)).smul_const v))
    simpa only [zero_smul,add_zero,one_smul,zero_add,Function.comp_def,Pi.add_apply,id_eq] using hd
  have hp : Tendsto (fun n : ℕ => (1/2:ℝ)^n) atTop (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num),
      Eventually.of_forall (fun n => by simp only [mem_Ioi]; positivity)⟩
  have hq : Tendsto q atTop (𝓝 (fderiv ℝ f x v)) := by
    simpa [Function.comp_def,q,← inv_pow] using hD.tendsto_slope_zero_right.comp hp
  have hb (n : ℕ) : dist (q n) (q (n+1))≤(H*‖v‖^2/2)*(1/2:ℝ)^n := by
    let r : ℝ := (1/2:ℝ)^n
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hn : 0≤(2:ℝ)^n := by positivity
    have hinv : (2:ℝ)^n*r=1 := by dsimp [r]; rw [← mul_pow]; norm_num
    have hcent := hc (x+(r/2) • v) ((r/2) • v)
    rw [show (x+(r/2) • v)+(r/2) • v=x+r • v by module,
      show (x+(r/2) • v)-(r/2) • v=x by module,norm_smul,Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ r/2)] at hcent
    have he : q n-q (n+1)=(2:ℝ)^n • (f (x+r • v)+f x-(2:ℝ) • f (x+(r/2) • v)) := by
      dsimp only [q]
      rw [pow_succ,pow_succ]
      change (2:ℝ)^n • (f (x+r • v)-f x)-((2:ℝ)^n*2) • (f (x+(r*(1/2)) • v)-f x)=_
      rw [show r*(1/2)=r/2 by ring]
      module
    rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_nonneg hn]
    apply (mul_le_mul_of_nonneg_left hcent hn).trans
    have heq : (2:ℝ)^n*(H*(r/2*‖v‖)^2)=(H*‖v‖^2/4)*r := by
      calc
        _ = (H*‖v‖^2/4)*((2:ℝ)^n*r)*r := by ring
        _ = _ := by rw [hinv]; ring
    rw [heq]
    change (H*‖v‖^2/4)*r≤(H*‖v‖^2/2)*r
    gcongr
    nlinarith [mul_nonneg hH (sq_nonneg ‖v‖)]
  have hh := dist_le_of_le_geometric_of_tendsto₀ (r:=(1/2:ℝ)) (C:=H*‖v‖^2/2) (by norm_num) hb hq
  simpa only [q,pow_zero,one_smul,dist_eq_norm,show (H*‖v‖^2/2)/(1-(1/2:ℝ))=H*‖v‖^2 by ring] using hh

lemma fderiv_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f : U → W} {H ε δ : ℝ} (hc : CurvatureBound f H) (hH : 0≤H)
    (hf : Differentiable ℝ f) (hb : ∀ x, ‖f x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x‖≤2*ε/δ+H*δ := by
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro v hv
  have hv' : ‖v‖≤1 := hv.le
  have ht := hc.taylor hH hf x (δ • v)
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos hδ,map_smul] at ht
  have hb' : ‖f (x+δ • v)-f x‖≤2*ε := (norm_sub_le _ _).trans (by linarith [hb (x+δ • v),hb x])
  have hD : δ*‖fderiv ℝ f x v‖≤2*ε+H*δ^2 := by
    have hh := norm_sub_le (f (x+δ • v)-f x) (f (x+δ • v)-f x-δ • fderiv ℝ f x v)
    rw [sub_sub_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos hδ] at hh
    have hv2 : ‖v‖^2≤1 := by nlinarith [norm_nonneg v]
    nlinarith [mul_le_mul_of_nonneg_left hv2 (show 0≤H*δ^2 by positivity)]
  have hD' : ‖fderiv ℝ f x v‖≤2*ε/δ+H*δ := by
    have hD' : ‖fderiv ℝ f x v‖≤(2*ε+H*δ^2)/δ :=
      (le_div_iff₀ hδ).mpr (by nlinarith [hD])
    convert hD' using 1
    all_goals try with_reducible_and_instances rfl
    field_simp
  simpa only [div_one] using hD'

lemma fderiv_difference_bound_of_curvature {U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {f g : U → W} {H ε δ : ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hfc : CurvatureBound f H) (hgc : CurvatureBound g H) (hH : 0≤H)
    (hfg : ∀ x, ‖f x-g x‖≤ε) (hε : 0≤ε) (hδ : 0<δ) (x : U) :
    ‖fderiv ℝ f x-fderiv ℝ g x‖≤2*ε/δ+2*H*δ := by
  have hb := fderiv_bound_of_curvature (hfc.sub hgc) (add_nonneg hH hH) (hf.sub hg) hfg hε hδ x
  change ‖fderiv ℝ (f-g) x‖≤_ at hb
  rwa [fderiv_sub (hf x) (hg x),← two_mul H] at hb

lemma uniform_spatial_derivative_limit {X U W : Type*}
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → X × U → W} {f : X × U → W} {S : Set X} {H : ℝ} (hH : 0≤H)
    (hF : ∀ n, ∀ t∈S, Differentiable ℝ (fun x => F n (t,x)))
    (hc : ∀ n, ∀ t∈S, CurvatureBound (fun x => F n (t,x)) H)
    (hlim : TendstoUniformlyOn F f atTop {p | p.1∈S}) :
    ∃ D : X × U → (U →L[ℝ] W),
      TendstoUniformlyOn (fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2) D atTop {p | p.1∈S} ∧
      ∀ t∈S, ∀ x, HasFDerivAt (fun x => f (t,x)) (D (t,x)) x := by
  let DF : ℕ → X × U → (U →L[ℝ] W) := fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2
  have huc : UniformCauchySeqOn DF atTop {p | p.1∈S} := by
    rw [Metric.uniformCauchySeqOn_iff]
    intro ε hε
    let δ := ε/(8*(H+1))
    let η := ε*δ/8
    have hδ : 0<δ := by dsimp [δ]; positivity
    have hη : 0<η := by dsimp [η]; positivity
    obtain ⟨K,hK⟩ := Metric.uniformCauchySeqOn_iff.mp hlim.uniformCauchySeqOn η hη
    refine ⟨K,?_⟩
    intro m hm n hn p hp
    have hh := fderiv_difference_bound_of_curvature (hF m p.1 hp) (hF n p.1 hp)
      (hc m p.1 hp) (hc n p.1 hp) hH
      (fun x => (show ‖F m (p.1,x)-F n (p.1,x)‖<η by simpa only [dist_eq_norm] using hK m hm n hn (p.1,x) hp).le)
      hη.le hδ p.2
    rw [dist_eq_norm]
    apply hh.trans_lt
    have hd : δ*(8*(H+1))=ε := by dsimp [δ]; exact div_mul_cancel₀ _ (by positivity)
    have he : 2*η/δ=ε/4 := by dsimp [η]; field_simp; ring
    rw [he]
    nlinarith [mul_nonneg hH hδ.le]
  have hpoint (p : X × U) : ∃ a : U →L[ℝ] W, p.1∈S → Tendsto (fun n => DF n p) atTop (𝓝 a) := by
    by_cases hp : p.1∈S
    · obtain ⟨a,ha⟩ := cauchySeq_tendsto_of_complete (huc.cauchySeq hp)
      exact ⟨a,fun _ => ha⟩
    · exact ⟨0,fun h => (hp h).elim⟩
  choose D hD using hpoint
  have hdlim := huc.tendstoUniformlyOn_of_tendsto (fun p hp => hD p hp)
  refine ⟨D,hdlim,?_⟩
  intro t ht x
  have hds : TendstoUniformly (fun n x => DF n (t,x)) (fun x => D (t,x)) atTop := by
    simpa only [Function.comp_def,preimage_ofPred_eq,ht,ofPred_true,tendstoUniformlyOn_univ] using hdlim.comp (fun x : U => (t,x))
  exact hasFDerivAt_of_tendstoUniformly hds (fun n x => (hF n t ht x).hasFDerivAt)
    (fun x => hlim.tendsto_at (x:=(t,x)) ht) x

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM
universe u v

lemma contDiff_fderiv_slice {A U W : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [NormedAddCommGroup W] [NormedSpace ℝ W]
    {F : A × U → W} (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p : A × U => fderiv ℝ (fun x => F (p.1,x)) p.2) := by
  have he (p : A × U) : fderiv ℝ (fun x => F (p.1,x)) p.2 =
      (fderiv ℝ F p).comp (ContinuousLinearMap.inr ℝ A U) := by
    have hin : HasFDerivAt (fun x : U => (p.1,x)) (ContinuousLinearMap.inr ℝ A U) p.2 := by
      convert (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2) using 1 <;> rfl
    exact ((hF.differentiable (by simp) p).hasFDerivAt.comp p.2 hin).fderiv
  simp_rw [he]
  exact (hF.fderiv_right (m:=∞) (by simp)).clm_comp contDiff_const

lemma smooth_spatial_limit_nat {A U : Type u} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup U] [NormedSpace ℝ U] (k : ℕ) :
    ∀ {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
      {F : ℕ → A × U → W} {f : A × U → W} {S : Set A},
      (∀ n, ContDiff ℝ ∞ (F n)) →
      (∀ j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈S → ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => F n (t,y)) x‖≤C) →
      TendstoUniformlyOn F f atTop {p | p.1∈S} →
      (∀ t∈S, ContDiff ℝ k (fun x => f (t,x))) ∧
      ContinuousOn (fun p : A × U => iteratedFDeriv ℝ k (fun x => f (p.1,x)) p.2) {p | p.1∈S} ∧
      TendstoUniformlyOn (fun n (p : A × U) => iteratedFDeriv ℝ k (fun x => F n (p.1,x)) p.2)
        (fun p : A × U => iteratedFDeriv ℝ k (fun x => f (p.1,x)) p.2) atTop {p | p.1∈S} := by
  induction k with
  | zero =>
    intro W _ _ _ F f S hF hb hl
    have hc : ContinuousOn f {p | p.1∈S} := hl.continuousOn
      (Frequently.of_forall fun n => (hF n).continuous.continuousOn)
    refine ⟨fun t ht => contDiff_zero.mpr (hc.comp_continuous
      (continuous_const.prodMk continuous_id) (fun x => ht)),?_,?_⟩
    · simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryFin0 ℝ U W).symm.continuous.comp_continuousOn hc
    · simpa only [iteratedFDeriv_zero_eq_comp,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryFin0 ℝ U W).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hl
  | succ k ih =>
    intro W _ _ _ F f S hF hb hl
    obtain ⟨C,hC,hCb⟩ := hb 2
    obtain ⟨D,hD,hd⟩ := uniform_spatial_derivative_limit (by positivity : 0≤2*C)
      (fun n t ht => ((hF n).comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp))
      (fun n t ht => curvature_of_second_derivative_bound
        ((hF n).comp (contDiff_const.prodMk contDiff_id)) hC (hCb n t ht)) hl
    let DF : ℕ → A × U → (U →L[ℝ] W) := fun n p => fderiv ℝ (fun x => F n (p.1,x)) p.2
    let df : A × U → (U →L[ℝ] W) := fun p => fderiv ℝ (fun x => f (p.1,x)) p.2
    have hdl : TendstoUniformlyOn DF df atTop {p | p.1∈S} :=
      hD.congr_right (fun p hp => (hd p.1 hp p.2).fderiv.symm)
    have hdb : ∀ j : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈S → ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => DF n (t,y)) x‖≤C := by
      intro j
      obtain ⟨C,hC,hCb⟩ := hb (j+1)
      exact ⟨C,hC,fun n t ht x => by simpa only [DF,norm_iteratedFDeriv_fderiv] using hCb n t ht x⟩
    obtain ⟨hsc,hjc,hjl⟩ := ih (fun n => contDiff_fderiv_slice (hF n)) hdb hdl
    refine ⟨?_,?_,?_⟩
    · intro t ht
      rw [show (↑(k+1) : ℕ∞ω)=↑k+1 by simp,contDiff_succ_iff_fderiv]
      exact ⟨fun x => (hd t ht x).differentiableAt,by simp,hsc t ht⟩
    · simpa only [df,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryRightEquiv' ℝ k U W).symm.continuous.comp_continuousOn hjc
    · simpa only [DF,df,iteratedFDeriv_succ_eq_comp_right,Function.comp_def,Prod.mk.eta] using
        (continuousMultilinearCurryRightEquiv' ℝ k U W).symm.isometry.uniformContinuous.comp_tendstoUniformlyOn hjl

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SlabL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma slabTimeContinuousL2_compact {F : Field} {T : ℝ} (hT : 0≤T)
    (hF : ContinuousOn F (fieldSlab T)) {K : Set Vec} (hK : IsCompact K)
    (hz : ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=0) : SlabTimeContinuousL2 T F := by
  let c : ℝ → ℝ := fun t => max 0 (min T t)
  have hc : Continuous c := continuous_const.max (continuous_const.min continuous_id)
  have hcm (t : ℝ) : c t∈Icc 0 T := ⟨le_max_left _ _,max_le hT (min_le_left _ _)⟩
  have hce (t : ℝ) (ht : t∈Icc 0 T) : c t=t := by
    dsimp [c]; rw [min_eq_right ht.2,max_eq_right ht.1]
  let G : Field := fun p => F (c p.1,p.2)
  have hG : Continuous G := by
    apply continuousOn_univ.mp
    exact hF.comp (((hc.comp continuous_fst).prodMk continuous_snd).continuousOn) (fun p hp => hcm p.1)
  have hL := timeContinuousL2_compact hG (fun U hU => ⟨K,hK,fun t ht x hx => hz _ (hcm t) x hx⟩)
  obtain ⟨G₂,hGc,hGe⟩ := hL
  refine ⟨G₂,hGc.mono (fun t ht => ht.1),fun t ht => ?_⟩
  simpa only [G,hce t ht] using hGe t ht.1

lemma slabTimeContinuousL2_of_exterior {F G : Field} {T : ℝ} (hT : 0≤T)
    (hF : ContinuousOn F (fieldSlab T)) (hG : Continuous G) (hGL : TimeContinuousL2 G)
    {K : Set Vec} (hK : IsCompact K) (hz : ∀ t∈Icc 0 T, ∀ x∉K, F (t,x)=G (t,x)) :
    SlabTimeContinuousL2 T F := by
  have hL := slabTimeContinuousL2_compact hT (hF.sub hG.continuousOn) hK
    (fun t ht x hx => sub_eq_zero.mpr (hz t ht x hx))
  obtain ⟨D₂,hDc,hDe⟩ := hL
  obtain ⟨G₂,hGc,hGe⟩ := hGL
  refine ⟨fun t => G₂ t+D₂ t,(hGc.mono (fun t ht => ht.1)).add hDc,?_⟩
  intro t ht
  filter_upwards [Lp.coeFn_add (G₂ t) (D₂ t),hGe t ht.1,hDe t ht] with x ha hg hd
  rw [ha]
  change (G₂ t : Vec → Vec) x+(D₂ t : Vec → Vec) x=F (t,x)
  rw [hg,hd]
  exact add_sub_cancel _ _

lemma picard_limit_slab_l2 {d : Datum} {S : ℕ → Solution} {E B : Field} {T A R P : ℝ}
    (hT : 0≤T) (hEc : ContinuousOn E (fieldSlab T)) (hBc : ContinuousOn B (fieldSlab T))
    (hsm : ∀ n, ContDiff ℝ ∞ (S n).E ∧ ContDiff ℝ ∞ (S n).B)
    (hr : ∀ n, PicardRegular d (S (n+1)))
    (hV : ∀ n, TransportFor (S (n+1)) (S n).E (S n).B)
    (hb : ∀ n, LocalParticleBound T A R P (S (n+1)).f)
    (hEl : TendstoUniformlyOn (fun n => (S n).E) E atTop (fieldSlab T))
    (hBl : TendstoUniformlyOn (fun n => (S n).B) B atTop (fieldSlab T)) :
    SlabTimeContinuousL2 T E ∧ SlabTimeContinuousL2 T B := by
  have he := picard_uniform_limit_exterior hsm hr hV hb hEl hBl
  have hn (x : Vec) (hx : x∉closedBall (0:Vec) (R+T)) : R+T<‖x‖ := by
    simpa only [mem_closedBall,dist_zero_right,not_le] using hx
  exact ⟨slabTimeContinuousL2_of_exterior hT hEc (hr 0).smooth_E.continuous (hr 0).l2E
    (isCompact_closedBall (0:Vec) (R+T)) (fun t ht x hx => (he t ht x (hn x hx)).1),
    slabTimeContinuousL2_of_exterior hT hBc (hr 0).smooth_B.continuous (hr 0).l2B
    (isCompact_closedBall (0:Vec) (R+T)) (fun t ht x hx => (he t ht x (hn x hx)).2)⟩

end RVM
end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_SlabEquations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma derivWithin_Ici_eq_Icc_of_lt {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    (f : ℝ → W) {t T : ℝ} (ht : t<T) :
    derivWithin f (Ici 0) t=derivWithin f (Icc 0 T) t := by
  apply derivWithin_congr_set
  filter_upwards [Iio_mem_nhds ht] with r hr
  change (0 ≤ r) = (0 ≤ r ∧ r≤T)
  exact propext ⟨fun h => ⟨h,hr.le⟩,fun h => h.1⟩

lemma SlabEquations.equationsBefore {s : Solution} {T : ℝ} (h : SlabEquations s T) :
    EquationsBefore s T := by
  intro t ht htT
  simpa only [derivWithin_Ici_eq_Icc_of_lt _ htT] using h t ⟨ht,htT.le⟩

lemma LocalParticleBound.compact {T A R P : ℝ} {f : Particle} (h : LocalParticleBound T A R P f) :
    ∃ K : Set Phase, IsCompact K ∧ ∀ t∈Icc 0 T, tsupport (fun z => f (t,z)) ⊆ K := by
  refine ⟨closedBall (0:Vec) R ×ˢ closedBall (0:Vec) P,
    (isCompact_closedBall _ _).prod (isCompact_closedBall _ _),?_⟩
  intro t ht
  apply closure_minimal
  · intro z hz
    exact ⟨by simpa only [mem_closedBall,dist_zero_right] using ((h t ht z.1 z.2).2 hz).1,
      by simpa only [mem_closedBall,dist_zero_right] using ((h t ht z.1 z.2).2 hz).2⟩
  · exact isClosed_closedBall.prod isClosed_closedBall

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Regularity_SpatialJets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

section

lemma spatiallySmoothSlab_of_uniform_jets {U W : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {T : ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈Icc (0:ℝ) T → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => F n (t,y)) x‖≤C)
    (hl : TendstoUniformlyOn F f atTop {p | p.1∈Icc (0:ℝ) T}) :
    SpatiallySmoothSlab T f := by
  refine ⟨?_,?_⟩
  · intro t ht
    rw [contDiff_infty]
    exact fun n => (smooth_spatial_limit_nat n hF hb hl).1 t ht
  · exact fun n => (smooth_spatial_limit_nat n hF hb hl).2.1

universe u

end

universe u

end


open Set Filter Metric MeasureTheory
open scoped Topology

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

universe u

end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_LocalPDE_StrongLocalExistence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

namespace RVM

lemma boundedSpatiallySmoothSlab_of_uniform_jets {U W : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]
    {F : ℕ → ℝ × U → W} {f : ℝ × U → W} {T : ℝ}
    (hF : ∀ n, ContDiff ℝ ∞ (F n))
    (hb : ∀ k : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ n t, t∈Icc (0:ℝ) T → ∀ x,
      ‖iteratedFDeriv ℝ k (fun y => F n (t,y)) x‖≤C)
    (hl : TendstoUniformlyOn F f atTop {p | p.1∈Icc (0:ℝ) T}) :
    BoundedSpatiallySmoothSlab T f := by
  refine ⟨spatiallySmoothSlab_of_uniform_jets hF hb hl,?_⟩
  intro k
  obtain ⟨C,hC,hCb⟩ := hb k
  refine ⟨C,hC,?_⟩
  intro t ht x
  have hj := (smooth_spatial_limit_nat k hF hb hl).2.2.tendsto_at (x:=(t,x)) ht
  exact le_of_tendsto hj.norm (Eventually.of_forall fun n => hCb n t ht x)

theorem family_local_spatially_smooth_bounded_classical_oai {ι : Type*} {d : ι → Datum} (hd : ∀ i, Admissible (d i))
    {A R₀ P₀ D D₀ A₁ : ℝ} (hA : 0≤A) (hR₀ : 0≤R₀) (hP₀ : 0≤P₀)
    (hD : 0≤D) (hD₀ : 0≤D₀) (hA₁ : 0≤A₁)
    (hcaps : ∀ i, DatumRestartControl (d i) A R₀ P₀ D D₀ A₁) :
    ∃ T : ℝ, 0<T ∧ ∀ i, ∃ s : Solution, C1ClassicalPrefix (d i) s T ∧ SlabEquations s T ∧
      BoundedSpatiallySmoothSlab T s.f ∧ BoundedSpatiallySmoothSlab T s.E ∧ BoundedSpatiallySmoothSlab T s.B := by
  obtain ⟨T,A,R,P,L,N,M,hT,hT1,hA,hR,hP,hL,hN,hM,hfamily⟩ :=
    family_picard_field_limit hd hA hR₀ hP₀ hD hD₀ hA₁ hcaps
  refine ⟨T,hT,?_⟩
  intro i
  obtain ⟨S,E,B,hS0,hsm,hc,hr,hg,hEl,hBl,hEc,hBc,hcLim⟩ := hfamily i
  have hjets := uniform_picard_sequence_jets (hd i) hT hT1 hN.le hM hS0 hsm hc hr
  obtain ⟨Q,hQ,hQEB,hQf⟩ := hjets 1
  have hQ0 : 0≤Q := zero_le_one.trans hQ
  have hcurv : ∀ n, SpatialFieldCurvature T (2*Q) (S n).E (S n).B := by
    intro n t ht
    exact ⟨curvature_of_second_derivative_bound ((hsm n).1.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).1),
      curvature_of_second_derivative_bound ((hsm n).2.comp (contDiff_const.prodMk contDiff_id)) hQ0
        (fun x => (hQEB n t ht x 2 le_rfl).2)⟩
  have hcurvf : ∀ n, PhaseParticleCurvature T (2*Q) (S (n+1)).f := by
    intro n t ht
    exact curvature_of_second_derivative_bound ((hr n).1.smooth_f.comp (contDiff_const.prodMk contDiff_id)) hQ0
      (hQf n t ht 2 le_rfl)
  obtain ⟨f,hfl,hfc,hfn,hfi,hfb,hfLip⟩ := picard_particle_limit (hd i) hT.le hL.le hN.le hsm hc hr hg
  obtain ⟨hfC,hEC,hBC,heq⟩ := local_c1_limit_of_picard (s:=⟨f,E,B⟩) hT (by positivity) (by positivity) hM hL.le
    (fun n => (hr n).1) (fun n => (hr n).2.1) hcurv hcurvf (fun n => (hr n).2.2.1)
    (fun n => (hr n).2.2.2) hcLim.1 hfb hfc hfl hEl hBl
  have hEi (x : Vec) : E (0,x)=(d i).E₀ x := by
    have hh := (hEl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_E] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hBi (x : Vec) : B (0,x)=(d i).B₀ x := by
    have hh := (hBl.seq_tendstoUniformlyOn (fun n => n+1) (tendsto_add_atTop_nat 1)).tendsto_at
      (x:=(0,x)) (show (0:ℝ)∈Icc 0 T from ⟨le_rfl,hT.le⟩)
    simp only [(hr _).1.initial_B] at hh
    exact tendsto_nhds_unique hh tendsto_const_nhds
  have hL2 := picard_limit_slab_l2 hT.le hEC.continuousOn hBC.continuousOn hsm
    (fun n => (hr n).1) (fun n => (hr n).2.1) (fun n => (hr n).2.2.1) hEl hBl
  refine ⟨⟨f,E,B⟩,⟨hfC,hEC,hBC,hfn,hL2.1,hL2.2,hfb.compact,heq.equationsBefore,hfi,hEi,hBi⟩,
    heq,?_,?_,?_⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hr n).1.smooth_f) _ hfl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht z => hQf n t ht k (by omega) z⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).1) _ hEl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).1⟩
  · apply boundedSpatiallySmoothSlab_of_uniform_jets (fun n => (hsm n).2) _ hBl
    intro k
    obtain ⟨Q,hQ,hQE,hQf⟩ := hjets k
    exact ⟨Q,zero_le_one.trans hQ,fun n t ht x => (hQE n t ht x k (by omega)).2⟩

end RVM
end

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.RVM.family_local_spatially_smooth_bounded_classical_oai.{u_1} := @OAI.RVM.family_local_spatially_smooth_bounded_classical_oai.{u_1}
