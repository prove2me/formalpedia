-- Prove2me | solution 1 for OAI.RVM.Admissible.exists_bounded_direction_partition
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:01:41.192594+00:00
-- url     : https://prove2.me/submissions/e4bc8674-bdc5-49f1-b5b8-e7f2dd255009

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_direction_count_bound

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

lemma dot_smul_left (r : ℝ) (a b : Vec) : dot (r • a) b = r * dot a b := by
  simp [dot, mul_assoc, Finset.mul_sum]

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

open Set MeasureTheory Filter
open scoped Topology ContDiff


end RVM

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

open Set Filter Metric MeasureTheory
open scoped Topology ContDiff NNReal

namespace RVM

lemma exists_direction_step {g : ℝ→Vec} {a b δ : ℝ} (hab : a≤b)
    (hg : ContinuousOn g (Icc a b)) (hδ : 0<δ) :
    ∃c∈Icc a b, (∀t∈Icc a c,‖g t-g a‖≤δ) ∧
      (c=b ∨ ‖g c-g a‖=δ) ∧ (a<b→a < c) := by
  classical
  let f := fun t=>‖g t-g a‖
  have hf : ContinuousOn f (Icc a b) := (hg.sub continuousOn_const).norm
  have hfa : f a=0 := by simp [f]
  by_cases hex : ∃t∈Icc a b,f t=δ
  · let S : Set ℝ := Icc a b ∩ f ⁻¹' {δ}
    have hS : IsCompact S := isCompact_Icc.of_isClosed_subset
      (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton) inter_subset_left
    obtain ⟨c,hc,hmin⟩ := hS.exists_isMinOn (by simpa only [S,Set.Nonempty,mem_inter_iff,
      mem_preimage,mem_singleton_iff] using hex) continuousOn_id
    have hfc : f c=δ := hc.2
    refine ⟨c,hc.1,?_,Or.inr hfc,?_⟩
    · intro t ht
      by_contra h
      have hft : δ<f t := lt_of_not_ge h
      obtain ⟨u,hu,he⟩ := intermediate_value_Icc ht.1
        (hf.mono (Icc_subset_Icc_right (ht.2.trans hc.1.2))) ⟨by simpa only [hfa] using hδ.le,hft.le⟩
      have huS : u∈S := ⟨⟨hu.1,hu.2.trans (ht.2.trans hc.1.2)⟩,he⟩
      have hct : c≤t := (hmin huS).trans hu.2
      have htc : t=c := le_antisymm ht.2 hct
      rw [htc,hfc] at hft
      exact (lt_irrefl δ hft)
    · intro _
      apply lt_of_le_of_ne hc.1.1
      intro he
      rw [←he,hfa] at hfc
      linarith
  · refine ⟨b,right_mem_Icc.mpr hab,?_,Or.inl rfl,fun h=>h⟩
    intro t ht
    by_contra h
    have hft : δ<f t := lt_of_not_ge h
    obtain ⟨u,hu,he⟩ := intermediate_value_Icc ht.1
      (hf.mono (Icc_subset_Icc_right ht.2)) ⟨by simpa only [hfa] using hδ.le,hft.le⟩
    exact hex ⟨u,⟨hu.1,hu.2.trans ht.2⟩,he⟩

lemma exists_finite_direction_stops {g : ℝ→Vec} {a b δ ℓ : ℝ}
    (hab : a≤b) (hg : ContinuousOn g (Icc a b)) (hδ : 0<δ) (hℓ : 0<ℓ)
    (hmod : ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ℓ→‖g t-g s‖<δ) :
    ∃n : ℕ,∃t : ℕ→ℝ,t 0=a ∧ t n=b ∧
      (∀i≤n,t i∈Icc a b) ∧
      (∀i<n,t i<t (i+1) ∧
        (∀x∈Icc (t i) (t (i+1)),‖g x-g (t i)‖≤δ) ∧
        (i+1<n→‖g (t (i+1))-g (t i)‖=δ ∧ ℓ≤t (i+1)-t i)) := by
  classical
  let S := Icc a b
  have hs : ∀x : S,∃c∈Icc x.1 b,(∀u∈Icc x.1 c,‖g u-g x.1‖≤δ) ∧
      (c=b ∨ ‖g c-g x.1‖=δ) ∧ (x.1<b→x.1 < c) := fun x=>
    exists_direction_step x.2.2 (hg.mono (Icc_subset_Icc_left x.2.1)) hδ
  let next : S→S := fun x=>⟨(hs x).choose,⟨x.2.1.trans (hs x).choose_spec.1.1,
    (hs x).choose_spec.1.2⟩⟩
  let seq : ℕ→S := fun n=>(next^[n]) ⟨a,left_mem_Icc.mpr hab⟩
  let t : ℕ→ℝ := fun n=>(seq n).1
  have ht0 : t 0=a := rfl
  have hnext (i : ℕ) : seq (i+1)=next (seq i) := by
    exact Function.iterate_succ_apply' next i _
  have htmem (i : ℕ) : t i∈Icc a b := (seq i).2
  have hstep (i : ℕ) : t i≤t (i+1) ∧
      (∀u∈Icc (t i) (t (i+1)),‖g u-g (t i)‖≤δ) ∧
      (t (i+1)=b ∨ ‖g (t (i+1))-g (t i)‖=δ) ∧
      (t i<b→t i<t (i+1)) := by
    have hh := (hs (seq i)).choose_spec
    dsimp only [t]
    rw [hnext]
    exact ⟨hh.1.1,hh.2⟩
  have hm : Monotone t := monotone_nat_of_le_succ (fun i=>(hstep i).1)
  have hsep (i : ℕ) (hi : t (i+1)≠b) : ℓ≤t (i+1)-t i := by
    have he : ‖g (t (i+1))-g (t i)‖=δ := (hstep i).2.2.1.resolve_left hi
    by_contra hh
    have hl : |t (i+1)-t i|<ℓ := by
      rw [abs_of_nonneg (sub_nonneg.mpr (hstep i).1)]
      exact lt_of_not_ge hh
    have hb := hmod (t i) (htmem i) (t (i+1)) (htmem (i+1)) hl
    rw [he] at hb
    exact lt_irrefl δ hb
  have hex : ∃n,t n=b := by
    by_contra hn
    have hne : ∀n,t n≠b := by simpa only [not_exists] using hn
    have hlower : ∀n : ℕ,a+(n:ℝ)*ℓ≤t n := by
      intro n
      induction n with
      | zero => simp only [Nat.cast_zero,zero_mul,add_zero,ht0,le_refl]
      | succ n ih =>
        have hh := hsep n (hne (n+1))
        rw [Nat.cast_add,Nat.cast_one]
        nlinarith
    obtain ⟨N,hN⟩ := exists_nat_gt ((b-a)/ℓ)
    have hh := (div_lt_iff₀ hℓ).mp hN
    have hNlo := hlower N
    have hNhi := (htmem N).2
    nlinarith
  let n := Nat.find hex
  have hnb : t n=b := Nat.find_spec hex
  have hnot : ∀i<n,t i≠b := fun i hi=>Nat.find_min hex hi
  refine ⟨n,t,ht0,hnb,fun i _=>htmem i,?_⟩
  intro i hi
  have hib : t i<b := lt_of_le_of_ne (htmem i).2 (hnot i hi)
  refine ⟨(hstep i).2.2.2 hib,(hstep i).2.1,?_⟩
  intro his
  exact ⟨(hstep i).2.2.1.resolve_left (hnot (i+1) his),hsep i (hnot (i+1) his)⟩

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

lemma continuousOn_momentumDirection {S : Set ℝ} {V : ℝ→Vec}
    (hV : ContinuousOn V S) (hne : ∀ t∈S,V t≠0) :
    ContinuousOn (fun t=>momentumDirection (V t)) S :=
  (hV.norm.inv₀ (fun t ht=>norm_ne_zero_iff.mpr (hne t ht))).smul hV



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

lemma momentumDirection_increment {v w : Vec} (hv : v≠0) (hw : w≠0) :
    ‖momentumDirection v-momentumDirection w‖≤2*‖v-w‖/‖v‖ := by
  have hvn : 0<‖v‖ := norm_pos_iff.mpr hv
  have hwn : ‖w‖≠0 := norm_ne_zero_iff.mpr hw
  have he : ‖v‖ • (momentumDirection v-momentumDirection w)=
      (v-w)+(‖w‖-‖v‖) • momentumDirection w := by
    simp only [momentumDirection,smul_sub,smul_smul,sub_mul,mul_inv_cancel₀ hvn.ne',
      mul_inv_cancel₀ hwn,one_smul]
    module
  have hh := norm_add_le (v-w) ((‖w‖-‖v‖) • momentumDirection w)
  rw [←he,norm_smul,Real.norm_eq_abs,abs_of_pos hvn,norm_smul,Real.norm_eq_abs,
    momentumDirection_norm hw,mul_one] at hh
  have hn : |‖w‖-‖v‖|≤‖v-w‖ := by
    simpa only [norm_sub_rev] using abs_norm_sub_norm_le w v
  exact (le_div_iff₀ hvn).mpr (by nlinarith)

lemma norm_momentum_of_high_band {v : Vec} {w : ℝ} (hw : 16≤w) (hq : w/8≤q v) :
    w/16≤‖v‖ := by
  have hqn := q_pos v
  have hn := norm_nonneg v
  have hqs := q_sq v
  nlinarith [sq_nonneg (q v-w/8),sq_nonneg (‖v‖-w/16)]

lemma IncrementBootstrap.direction_increment {V : ℝ→Vec} {T M A P L a b : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    {s t : ℝ} (hs : s∈Icc a b) (ht : t∈Icc a b) :
    ‖momentumDirection (V t)-momentumDirection (V s)‖≤
      (32/(2:ℝ)^k)*(M*P*Real.sqrt |t-s|+A*|t-s| *(P^2*L/(2:ℝ)^k)) := by
  have hw : 0<(2:ℝ)^k := by positivity
  have hn (r : ℝ) (hr : r∈Icc a b) : (2:ℝ)^k/16≤‖V r‖ :=
    norm_momentum_of_high_band hk (hband r hr).1
  have hn0 (r : ℝ) (hr : r∈Icc a b) : V r≠0 := by
    apply norm_pos_iff.mp
    exact (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le (hn r hr)
  have hnorm : ‖V t-V s‖≤M*P*Real.sqrt |t-s|+A*|t-s| *(P^2*L/(2:ℝ)^k) := by
    rcases le_total s t with hst|hts
    · rw [abs_of_nonneg (sub_nonneg.mpr hst)]
      exact H k s t (hJ hs).1 hst (hJ ht).2 (fun r hr=>hband r ⟨hs.1.trans hr.1,hr.2.trans ht.2⟩)
    · rw [norm_sub_rev,abs_of_nonpos (sub_nonpos.mpr hts),neg_sub]
      exact H k t s (hJ ht).1 hts (hJ hs).2 (fun r hr=>hband r ⟨ht.1.trans hr.1,hr.2.trans hs.2⟩)
  calc
    _ ≤ 2*‖V t-V s‖/‖V t‖ := momentumDirection_increment (hn0 t ht) (hn0 s hs)
    _ ≤ 2*‖V t-V s‖/((2:ℝ)^k/16) := div_le_div_of_nonneg_left (by positivity)
      (div_pos hw (by norm_num)) (hn t ht)
    _ = (32/(2:ℝ)^k)*‖V t-V s‖ := by field_simp; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hnorm (by positivity)

lemma sqrt_linear_small {B C δ u : ℝ} (hB : 0<B) (hC : 0<C) (hδ : 0<δ)
    (_hu : 0≤u) (hsmall : u < min ((δ/(4*B))^2) (δ/(4*C))) :
    B*Real.sqrt u+C*u<δ := by
  have hs : Real.sqrt u<δ/(4*B) := (Real.sqrt_lt' (by positivity)).mpr (lt_of_lt_of_le hsmall (min_le_left _ _))
  have hc : u<δ/(4*C) := lt_of_lt_of_le hsmall (min_le_right _ _)
  have hs' := (lt_div_iff₀ (show 0<4*B by positivity)).mp hs
  have hc' := (lt_div_iff₀ (show 0<4*C by positivity)).mp hc
  linarith

lemma IncrementBootstrap.finite_direction_stops {V : ℝ→Vec} {T M A P L a b δ : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hab : a≤b) (hV : ContinuousOn V (Icc a b)) (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ) :
    let B := (32/(2:ℝ)^k)*M*P
    let C := (32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k)
    let ℓ := min ((δ/(4*B))^2) (δ/(4*C))
    ∃n : ℕ,∃t : ℕ→ℝ,t 0=a ∧ t n=b ∧
      (∀i≤n,t i∈Icc a b) ∧
      (∀i<n,t i<t (i+1) ∧
        (∀x∈Icc (t i) (t (i+1)),‖momentumDirection (V x)-momentumDirection (V (t i))‖≤δ) ∧
        (i+1<n→‖momentumDirection (V (t (i+1)))-momentumDirection (V (t i))‖=δ ∧ ℓ≤t (i+1)-t i)) := by
  dsimp only
  have hB : 0<(32/(2:ℝ)^k)*M*P := by positivity
  have hC : 0<(32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k) := by positivity
  apply exists_finite_direction_stops hab
    (continuousOn_momentumDirection hV (fun t ht=>by
      apply norm_pos_iff.mp
      exact (div_pos (pow_pos (by norm_num : (0:ℝ)<2) k) (by norm_num : (0:ℝ)<16)).trans_le
        (norm_momentum_of_high_band hk (hband t ht).1))) hδ (by positivity)
  intro s hs t ht hst
  apply (H.direction_increment k hk hJ hband hs ht).trans_lt
  convert sqrt_linear_small hB hC hδ (abs_nonneg (t-s)) hst using 1
  all_goals try with_reducible_and_instances rfl
  first | rfl | ring

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

lemma directionWeight_signed_exit {a b ℓ δ : ℝ} {g g' : ℝ→Vec}
    (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤δ/4)
    (hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤δ/4)
    (hexit : δ≤‖g b-g a‖) :
    δ/2≤‖∫t in a..b,directionWeight a b ℓ t • g' t‖ := by
  have he := directionWeight_signed_error hℓ hab hg hg' hd hleft hright
  have hn := norm_sub_norm_le (g b-g a) (∫t in a..b,directionWeight a b ℓ t • g' t)
  rw [norm_sub_rev (g b-g a) (∫t in a..b,directionWeight a b ℓ t • g' t)] at hn
  linarith

lemma directionWeight_total_variation {a b ℓ : ℝ} (hℓ : 0<ℓ) (hab : 2*ℓ≤b-a) :
    (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 := by
  have hab' : a≤b := by linarith
  have hL : a≤a+ℓ := by linarith
  have hC : a+ℓ≤b-ℓ := by linarith
  have hR : b-ℓ≤b := by linarith
  have hψ := (directionWeight_lipschitz a b ℓ).lipschitzOnWith (s:=uIcc a b) |>.absolutelyContinuousOnInterval
  have hi : IntervalIntegrable (fun t=>|deriv (directionWeight a b ℓ) t|) volume a b :=
    hψ.intervalIntegrable_deriv.norm
  have hiL := hi.mono_set (show uIcc a (a+ℓ)⊆uIcc a b by
    rw [uIcc_of_le hL,uIcc_of_le hab']; exact Icc_subset_Icc le_rfl (hC.trans hR))
  have hiC := hi.mono_set (show uIcc (a+ℓ) (b-ℓ)⊆uIcc a b by
    rw [uIcc_of_le hC,uIcc_of_le hab']; exact Icc_subset_Icc hL hR)
  have hiR := hi.mono_set (show uIcc (b-ℓ) b⊆uIcc a b by
    rw [uIcc_of_le hR,uIcc_of_le hab']; exact Icc_subset_Icc (hL.trans hC) le_rfl)
  have eL : (∫t in a..a+ℓ,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in a..a+ℓ,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_left hℓ hab (by simpa only [uIoo_of_le hL] using ht),
          abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eR : (∫t in b-ℓ..b,|deriv (directionWeight a b ℓ) t|)=1 := by
    calc
      _ = ∫t in b-ℓ..b,ℓ⁻¹ := by
        apply intervalIntegral.integral_congr_uIoo
        intro t ht
        dsimp only
        rw [directionWeight_deriv_right hℓ hab (by simpa only [uIoo_of_le hR] using ht),
          abs_neg,abs_of_pos (inv_pos.mpr hℓ)]
      _ = 1 := by rw [intervalIntegral.integral_const]; simp [hℓ.ne']
  have eC : (∫t in a+ℓ..b-ℓ,|deriv (directionWeight a b ℓ) t|)=0 := by
    rw [←intervalIntegral.integral_zero (a:=a+ℓ) (b:=b-ℓ)]
    apply intervalIntegral.integral_congr_uIoo
    intro t ht
    dsimp only
    rw [directionWeight_deriv_middle hℓ hab (by simpa only [uIoo_of_le hC] using ht),abs_zero]
  rw [←intervalIntegral.integral_add_adjacent_intervals hiL (hiC.trans hiR),
    ←intervalIntegral.integral_add_adjacent_intervals hiC hiR,eL,eC,eR]
  norm_num

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

lemma continuousOn_angular_force {S : Set ℝ} {V K : ℝ→Vec}
    (hV : ContinuousOn V S) (hK : ContinuousOn K S) (hv : ∀t∈S,V t≠0) (w : ℝ) :
    ContinuousOn (fun t=>angularMultiplier w (V t) (K t)) S := by
  have hG : ContinuousOn (fun t=>angularMultiplierCLM w (V t)) S := by
    intro t ht
    exact (contDiffAt_angularMultiplierCLM w (hv t ht) (k:=1) (by simp)).continuousAt.comp_continuousWithinAt (hV t ht)
  simpa only [angularMultiplierCLM_apply] using hG.clm_apply hK

lemma exists_weighted_exit_of_modulus {g g' : ℝ→Vec} {a b δ ε : ℝ}
    (hab : a≤b) (hδ : 0<δ) (hε : 0<ε)
    (hg : ContinuousOn g (Icc a b)) (hg' : ContinuousOn g' (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt g (g' t) t)
    (hsmall : ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ε→‖g t-g s‖<δ/4)
    (hex : δ≤‖g b-g a‖) :
    ∃ℓ : ℝ,0<ℓ ∧ 2*ℓ≤b-a ∧
      (δ/2≤‖∫t in a..b,directionWeight a b ℓ t • g' t‖) ∧
      (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 ∧
      tsupport (directionWeight a b ℓ)⊆Icc a b := by
  have hlen : ε≤b-a := by
    by_contra hn
    have hh := hsmall a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab)
      (show |b-a|<ε by rw [abs_of_nonneg (sub_nonneg.mpr hab)]; exact lt_of_not_ge hn)
    linarith
  let ℓ := ε/2
  have hℓ : 0<ℓ := by dsimp [ℓ]; positivity
  have hsep : 2*ℓ≤b-a := by dsimp [ℓ]; linarith
  have hleft : ∀t∈Icc a (a+ℓ),‖g t-g a‖≤δ/4 := by
    intro t ht
    exact (hsmall a (left_mem_Icc.mpr hab) t
      ⟨ht.1,by dsimp [ℓ] at ht; linarith [ht.2]⟩
      (by rw [abs_of_nonneg (sub_nonneg.mpr ht.1)]; dsimp [ℓ] at ht; linarith [ht.2])).le
  have hright : ∀t∈Icc (b-ℓ) b,‖g t-g b‖≤δ/4 := by
    intro t ht
    exact (hsmall b (right_mem_Icc.mpr hab) t
      ⟨by dsimp [ℓ] at ht; linarith [ht.1],ht.2⟩
      (by rw [abs_of_nonpos (sub_nonpos.mpr ht.2)]; dsimp [ℓ] at ht; linarith [ht.1])).le
  exact ⟨ℓ,hℓ,hsep,directionWeight_signed_exit hℓ hsep hg hg' hd hleft hright hex,
    directionWeight_total_variation hℓ hsep,directionWeight_tsupport hℓ hsep⟩

lemma IncrementBootstrap.direction_modulus {V : ℝ→Vec} {T M A P L a b δ : ℝ}
    (H : IncrementBootstrap V T M A P L) (k : ℕ) (hk : 16≤(2:ℝ)^k)
    (hJ : Icc a b⊆Icc 0 T)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ) :
    ∃ε : ℝ,0<ε ∧ ∀s∈Icc a b,∀t∈Icc a b,|t-s|<ε→
      ‖momentumDirection (V t)-momentumDirection (V s)‖<δ := by
  have hB : 0<(32/(2:ℝ)^k)*M*P := by positivity
  have hC : 0<(32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k) := by positivity
  refine ⟨min ((δ/(4*((32/(2:ℝ)^k)*M*P)))^2)
    (δ/(4*((32/(2:ℝ)^k)*A*(P^2*L/(2:ℝ)^k)))),by positivity,?_⟩
  intro s hs t ht hst
  apply (H.direction_increment k hk hJ hband hs ht).trans_lt
  convert sqrt_linear_small hB hC hδ (abs_nonneg (t-s)) hst using 1 <;> first | rfl | ring

lemma IncrementBootstrap.exists_weighted_angular_exit {V K : ℝ→Vec}
    {T M A P L a b δ : ℝ} (H : IncrementBootstrap V T M A P L)
    (k : ℕ) (hk : 16≤(2:ℝ)^k) (hJ : Icc a b⊆Icc 0 T) (hab : a≤b)
    (hV : ContinuousOn V (Icc a b)) (hK : ContinuousOn K (Icc a b))
    (hd : ∀t∈Ioo a b,HasDerivAt V (K t) t)
    (hband : ∀t∈Icc a b,(2:ℝ)^k/8≤q (V t) ∧ q (V t)≤8*(2:ℝ)^k)
    (hM : 0<M) (hA : 0<A) (hP : 0<P) (hL : 0<L) (hδ : 0<δ)
    (hexit : δ≤‖momentumDirection (V b)-momentumDirection (V a)‖) :
    ∃ℓ : ℝ,0<ℓ ∧ 2*ℓ≤b-a ∧
      ((2:ℝ)^k*δ/2≤‖∫t in a..b,directionWeight a b ℓ t • angularMultiplier ((2:ℝ)^k) (V t) (K t)‖) ∧
      (∫t in a..b,|deriv (directionWeight a b ℓ) t|)=2 ∧
      tsupport (directionWeight a b ℓ)⊆Icc a b := by
  have hw : 0<(2:ℝ)^k := by positivity
  have hv (t : ℝ) (ht : t∈Icc a b) : V t≠0 := by
    apply norm_pos_iff.mp
    exact (div_pos hw (by norm_num : (0:ℝ)<16)).trans_le
      (norm_momentum_of_high_band hk (hband t ht).1)
  obtain ⟨ε,hε,hsmall⟩ := H.direction_modulus k hk hJ hband hM hA hP hL
    (show 0<δ/4 by positivity)
  apply exists_weighted_exit_of_modulus (g:=fun t=>((2:ℝ)^k) • momentumDirection (V t)) hab
    (mul_pos hw hδ) hε ((continuousOn_momentumDirection hV hv).const_smul ((2:ℝ)^k))
    (continuousOn_angular_force hV hK hv _)
  · intro t ht
    convert (hasDerivAt_momentumDirection (hd t ht) (hv t (Ioo_subset_Icc_self ht))).const_smul ((2:ℝ)^k) using 1 <;>
      first | rfl | simp only [angularMultiplier,smul_smul,div_eq_mul_inv]
  · intro s hs t ht hst
    rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hw]
    convert mul_lt_mul_of_pos_left (hsmall s hs t ht hst) hw using 1 <;> first | rfl | ring
  · rw [←smul_sub,norm_smul,Real.norm_eq_abs,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left hexit hw.le



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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_DirectionCounts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



section
open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff NNReal


lemma IncrementBootstrap.weighted_direction_partition {V K : ℝ → Vec}
    {T M A P L a b δ : ℝ} (H : IncrementBootstrap V T M A P L)
    (k : ℕ) (hk : 16 ≤ (2:ℝ)^k) (hab : a ≤ b)
    (hJ : Icc a b ⊆ Icc 0 T) (hV : ContinuousOn V (Icc a b))
    (hK : ContinuousOn K (Icc a b))
    (hd : ∀ t ∈ Ioo a b, HasDerivAt V (K t) t)
    (hband : ∀ t ∈ Icc a b, (2:ℝ)^k/8 ≤ q (V t) ∧ q (V t) ≤ 8*(2:ℝ)^k)
    (hM : 0 < M) (hA : 0 < A) (hP : 0 < P) (hL : 0 < L) (hδ : 0 < δ) :
    Nonempty (WeightedDirectionPartition V K a b ((2:ℝ)^k) δ) := by
  classical
  obtain ⟨n,t,ht0,htn,htmem,hstep⟩ :=
    H.finite_direction_stops k hk hab hV hJ hband hM hA hP hL hδ
  have hcell (i : ℕ) (hi : i < n) : Icc (t i) (t (i+1)) ⊆ Icc a b :=
    Icc_subset_Icc (htmem i (by omega)).1 (htmem (i+1) (by omega)).2
  have hwit (i : ℕ) (hi : i < n-1) :
      ∃ ℓ : ℝ, 0 < ℓ ∧ 2*ℓ ≤ t (i+1)-t i ∧
        ((2:ℝ)^k*δ/2 ≤ ‖∫ u in t i..t (i+1),
          directionWeight (t i) (t (i+1)) ℓ u • angularMultiplier ((2:ℝ)^k) (V u) (K u)‖) ∧
        (∫ u in t i..t (i+1), |deriv (directionWeight (t i) (t (i+1)) ℓ) u|)=2 ∧
        tsupport (directionWeight (t i) (t (i+1)) ℓ) ⊆ Icc (t i) (t (i+1)) := by
    have hin : i < n := by omega
    apply H.exists_weighted_angular_exit k hk ((hcell i hin).trans hJ) (hstep i hin).1.le
      (hV.mono (hcell i hin)) (hK.mono (hcell i hin))
    · intro u hu
      exact hd u ⟨(htmem i (by omega)).1.trans_lt hu.1,
        hu.2.trans_le (htmem (i+1) (by omega)).2⟩
    · exact fun u hu => hband u (hcell i hin hu)
    · exact hM
    · exact hA
    · exact hP
    · exact hL
    · exact hδ
    · exact ((hstep i hin).2.2 (by omega)).1.ge
  let ℓ : ℕ → ℝ := fun i => if hi : i < n-1 then (hwit i hi).choose else 1
  have hℓ (i : ℕ) (hi : i < n-1) : ℓ i = (hwit i hi).choose := dite_eq_left hi
  refine ⟨{
    count := n, time := t, ramp := ℓ, initial := ht0, terminal := htn,
    time_mem := htmem,
    strict := strictMonoOn_Iic_of_lt_succ (fun i hi => (hstep i hi).1),
    direction_control := fun i hi => (hstep i hi).2.1,
    exit := fun i hi => ((hstep i (by omega)).2.2 (by omega)).1,
    ramp_pos := ?_, ramp_separation := ?_, signed_exit := ?_, variation := ?_ }⟩
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.2.1
  · intro i hi
    rw [hℓ i hi]
    exact (hwit i hi).choose_spec.2.2.2.1

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma eventually_direction_absorption (C : ℝ) :
    ∀ᶠ P : ℝ in atTop, 1≤P ∧ 1≤Real.log (2+P) ∧
      ∀ w δ : ℝ, P^(3/5:ℝ)≤w → w^(-3/5:ℝ)≤δ →
        1≤w ∧ 16≤w ∧ P≤w^2 ∧ Real.log (2+P)≤Real.sqrt w ∧
          4*C*(Real.log (2+P))^2≤w*δ := by
  have ht (k : ℕ) (ε : ℝ) (hε : 0<ε) (D : ℝ) :
      ∀ᶠ P : ℝ in atTop, D*(Real.log (2+P))^k≤P^ε := by
    have ho := (isLittleO_log_rpow_rpow_atTop (k:ℝ) hε).const_mul_left (D*2^k)
    filter_upwards [ho.bound (by norm_num : (0:ℝ)<1),eventually_ge_atTop (2:ℝ)] with P hp hP
    have hp0 : 0<P := by linarith
    have hlog : 0≤Real.log P := Real.log_nonneg (by linarith)
    have hlog2nonneg : 0≤Real.log (2+P) := Real.log_nonneg (by linarith)
    have hlog2 : Real.log (2+P)≤2*Real.log P := by
      calc
        _≤Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
        _=_ := by rw [Real.log_pow]; norm_num
    have hbo : |D*2^k| * (Real.log P)^k≤P^ε := by
      simpa only [Real.norm_eq_abs,Real.rpow_natCast,abs_mul,abs_of_nonneg (pow_nonneg hlog _),
        one_mul,abs_of_pos (Real.rpow_pos_of_pos hp0 _)] using hp
    calc
      D*(Real.log (2+P))^k≤|D| * (Real.log (2+P))^k := mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _≤|D| * (2*Real.log P)^k := by gcongr
      _=|D*2^k| * (Real.log P)^k := by rw [mul_pow,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2^k)]; ring
      _≤_ := hbo
  filter_upwards [ht 1 (3/10) (by norm_num) 1,ht 2 (6/25) (by norm_num) (4*C),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<3/5)).eventually_ge_atTop 16,
    (Real.tendsto_log_atTop.comp (tendsto_const_nhds.add_atTop tendsto_id)).eventually_ge_atTop 1,
    eventually_ge_atTop (1:ℝ)] with P hroot hcharge h16 hL hP
  refine ⟨hP,hL,?_⟩
  intro w δ hw hδ
  have hp0 := zero_lt_one.trans_le hP
  have hw16 := h16.trans hw
  have hw1 : 1≤w := by linarith
  have hw0 := zero_lt_one.trans_le hw1
  have hsq : P≤w^2 := by
    calc
      P = P^(1:ℝ) := (Real.rpow_one P).symm
      _≤P^(6/5:ℝ) := Real.rpow_le_rpow_of_exponent_le hP (by norm_num)
      _=(P^(3/5:ℝ))^2 := by rw [←Real.rpow_natCast,←Real.rpow_mul hp0.le]; norm_num
      _≤w^2 := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hw _
  have hs : Real.log (2+P)≤Real.sqrt w := by
    simp only [pow_one,one_mul] at hroot
    apply hroot.trans
    rw [Real.sqrt_eq_rpow]
    calc
      P^(3/10:ℝ) = (P^(3/5:ℝ))^(1/2:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
      _≤w^(1/2:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
  refine ⟨hw1,hw16,hsq,hs,?_⟩
  calc
    4*C*(Real.log (2+P))^2≤P^(6/25:ℝ) := hcharge
    _=(P^(3/5:ℝ))^(2/5:ℝ) := by rw [←Real.rpow_mul hp0.le]; norm_num
    _≤w^(2/5:ℝ) := Real.rpow_le_rpow (Real.rpow_nonneg hp0.le _) hw (by norm_num)
    _=w^(1+(-3/5:ℝ)) := by norm_num
    _=w*w^(-3/5:ℝ) := by rw [Real.rpow_add hw0,Real.rpow_one]
    _≤w*δ := mul_le_mul_of_nonneg_left hδ hw0.le



open Set Filter Metric MeasureTheory
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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_PartitionOccupation
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

lemma Admissible.exists_bounded_direction_partition_oai {d : Datum} (hd : Admissible d)
    (T₀ M A : ℝ) (hM : 0<M) (hA : 0<A) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b δ : ℝ) (k : ℕ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → a≤b → b-a≤((2:ℝ)^k/P)^2 →
      P^(3/5:ℝ)≤(2:ℝ)^k → (2:ℝ)^k≤P → ((2:ℝ)^k)^(-3/5:ℝ)≤δ → δ≤1 →
      (∀z,s.f (0,z)≠0→∀r∈Icc 0 T,q (F.flow z r).2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc ((2:ℝ)^k/8) (8*(2:ℝ)^k)) →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      ∃ D : WeightedDirectionPartition (fun t=>(F.flow zX t).2)
        (fun t=>s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) a b ((2:ℝ)^k) δ,
        (D.count:ℝ)≤C*(Real.log (2+P))^6/δ := by
  obtain ⟨C,hC,hcount⟩ := hd.direction_count_bound T₀ M A hM hA.le
  refine ⟨C,hC,?_⟩
  filter_upwards [hcount,eventually_direction_absorption 0] with P hcount hP
  intro s T F hs hT hTT zX a b δ k hz ha hb hab hlen hw hwP hδ hδ1 hsource hq HZ
  have hm := hP.2.2 ((2:ℝ)^k) δ hw hδ
  have hJ : Icc a b⊆Icc 0 T := Icc_subset_Icc ha hb
  have hV := (F.continuousOn_time zX).snd.mono hJ
  have hK : ContinuousOn (fun t=>s.E (t,(F.flow zX t).1)+
      cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) (Icc a b) := by
    apply ((F.continuous_prefixMomentumForce hs.energyPrefix hT zX).continuousOn).congr
    intro t ht
    simp only [prefixMomentumForce,prefixFlow,prefixClamp_eq (hJ ht),lorentzField,lorentzPhase]
  have hder (t : ℝ) (ht : t∈Ioo a b) :
      HasDerivAt (fun t=>(F.flow zX t).2)
        (s.E (t,(F.flow zX t).1)+cross (velocity (F.flow zX t).2) (s.B (t,(F.flow zX t).1))) t := by
    have hti : t∈Ioo (0:ℝ) T := ⟨ha.trans_lt ht.1,ht.2.trans_le hb⟩
    exact ((F.ode zX t (Ioo_subset_Icc_self hti)).hasDerivAt (Icc_mem_nhds hti.1 hti.2)).snd
  obtain ⟨D⟩ := (HZ zX hz).weighted_direction_partition k hm.2.1 hab hJ hV hK hder hq
    hM hA (zero_lt_one.trans_le hP.1) (zero_lt_one.trans_le hP.2.1)
    ((Real.rpow_pos_of_pos (by positivity) (-3/5)).trans_le hδ)
  refine ⟨D,?_⟩
  exact hcount s T F hs hT hTT zX (tsupport d.f₀) a b ((2:ℝ)^k) δ hz hd.2.1 subset_rfl ha hb hab hlen hw hwP hδ hδ1
    hsource hq (fun t ht=>norm_momentum_of_high_band hm.2.1 (hq t ht).1) (HZ zX hz) HZ D

end RVM

end

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.exists_bounded_direction_partition_oai := @OAI.RVM.Admissible.exists_bounded_direction_partition_oai
