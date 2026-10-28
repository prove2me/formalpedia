-- Prove2me | solution 1 for OAI.RVM.Admissible.bulk_remainder_uniform
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:30:42.427463+00:00
-- url     : https://prove2.me/submissions/ca8d1323-350b-49d1-bd1c-e614bbeea8a0

import Mathlib
import Definitions.Def_VlasovMaxwell
import Definitions.Def_OAIQ073V000
import Theorems.Thm_OAI_RVM_Admissible_central_uniform
import Theorems.Thm_OAI_RVM_Admissible_representative_receiver_envelope
import Theorems.Thm_OAI_RVM_PhaseFlowOn_bulkRemainder_selected_sum

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

lemma unsafe_selected_actual_margins
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b) :
    0 < z ∧ Δ < z/1000 ∧ 2*c < H ∧
      (496/1000 : ℝ)*z + 3*(α+c) < H ∧
      (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z ∧
      (500/751 : ℝ) < z ∧
      y < (377/1000 : ℝ)*z - (175/100 : ℝ)*α - (75/100 : ℝ)*c ∧
      (623/1000 : ℝ) < z-y ∧ (623/1000 : ℝ) < 1-α-y := by
  have hb : b < H - α + Δ := by
    by_cases hh : H ≤ 2*c
    · have h := hfar₁ hh
      linarith
    · have h := hfar₂ (lt_of_not_ge hh)
      linarith
  have hdsmall : 99995*Δ < 4*z := by linarith
  have hzpos : 0 < z := by
    by_contra hh
    have hz0 : z = 0 := le_antisymm (le_of_not_gt hh) hz
    subst z
    have hdneg : Δ < 0 := by linarith
    linarith
  have hd : Δ < z/1000 := by linarith
  have hh : 2*c < H := by
    by_contra hh
    have hf := hfar₁ (le_of_not_gt hh)
    linarith
  have hf := hfar₂ hh
  have hlow : (496/1000 : ℝ)*z + 3*(α+c) < H := by linarith
  have hm : (35/10 : ℝ)*α + (15/10 : ℝ)*c + 2*y < (753/1000 : ℝ)*z := by
    linarith
  refine ⟨hzpos, hd, hh, hlow, hm, ?_, ?_, ?_, ?_⟩ <;> linarith

lemma unsafe_selected_improved_window
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z + c = 1) (hΔ : Δ = (α + b + y + H) / 100000)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hfar₁ : H ≤ 2*c → b < H/2 - α + Δ)
    (hfar₂ : 2*c < H → b < H - c - α + Δ)
    (hu₁ : 2*H/3 + z/6 - Δ/3 < b)
    (hu₂ : b < H + 2*y - z/2 + Δ)
    (hactual : b < H/2 - min α c + y + (2/1000 : ℝ)*z) :
    (9/10 : ℝ) < z ∧ (895/1000 : ℝ) < 1-α ∧
      (16/100 : ℝ)*max z (1-α) < y ∧ y < (49/100 : ℝ)*min z (1-α) := by
  obtain ⟨hzpos, hd, _, hlow, hm, _, hym, _, _⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have hm0 : 0 ≤ min α c := le_min hα hc
  have hHup : H < (81/100 : ℝ)*z := by linarith
  have hac : α+c < (105/1000 : ℝ)*z := by linarith
  have hz9 : (9/10 : ℝ) < z := by linarith
  have hp : (895/1000 : ℝ) < 1-α := by linarith
  have hy19 : (19/100 : ℝ)*z < y := by linarith
  refine ⟨hz9, hp, ?_, ?_⟩
  · rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 16/100), max_lt_iff]
    constructor <;> linarith
  · rw [mul_min_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 49/100), lt_min_iff]
    constructor <;> linarith

lemma unsafe_selected_improved_contradiction
    {α z c b y H Δ : ℝ}
    (hα : 0 ≤ α) (hz : 0 < z) (hc : 0 ≤ c)
    (hsmall : Δ < z/1000)
    (hlow : (496/1000 : ℝ)*z + 3*(α+c) < H)
    (hnear : 2*α + H/2 + 2*y < z + Δ)
    (hu : 2*H/3 + z/6 - Δ/3 < b)
    (himproved : b < H/2 - min α c + (29/50 : ℝ)*y + Δ) : False := by
  have hm : 0 ≤ min α c := le_min hα hc
  linarith

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionWeight
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

namespace RVM

lemma max_growth_bound {P c H E : ℝ} (hP : 1 < P)
    (hHc : 2*c ≤ H) (hE : 2*c ≤ E) :
    max 1 (max (P^(-2*c)*P^E) (P^(-H)*P^E)) ≤ P^(-2*c+E) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  refine max_le ?_ (max_le ?_ ?_)
  · exact Real.one_le_rpow hP.le (by linarith)
  · rw [← Real.rpow_add hP0]
  · rw [← Real.rpow_add hP0]
    exact (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma selected_coefficient_power_table
    {P C₀ α z c b y H Δ k Λ : ℝ} (hP : 1 < P)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hnear : 2*α+H/2+2*y < z+Δ)
    (hk : 0 ≤ k) (hfar : P^(α+b-H-Δ) < k)
    (henergy : k^2 ≤ P^(-min (2*c) H))
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hΛ : (66/100 : ℝ) < z → Λ^2 ≤ P^(2*max α c+2*y+2*z/1000))
    (hactual : C₀ < P^(min z (1-α)-y) →
      k^2 ≤ P^(-H)*max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)))
    (himproved : (7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y →
      y ≤ (49/100 : ℝ)*min z (1-α) →
      k^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) :
    min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) ≤ P^(-z/2-Δ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hkfar : P^((α+b-H-Δ)*2) < k^2 := by
    rw [Real.rpow_mul hP0.le, Real.rpow_two]
    exact (sq_lt_sq₀ (Real.rpow_nonneg hP0.le _) hk).mpr hfar
  have hfarE := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le henergy)
  have hfar₁ : H ≤ 2*c → b < H/2-α+Δ := by
    intro hh
    rw [min_eq_right hh] at hfarE
    linarith
  have hfar₂ : 2*c < H → b < H-c-α+Δ := by
    intro hh
    rw [min_eq_left hh.le] at hfarE
    linarith
  by_contra hbad
  have hb' := lt_of_not_ge hbad
  have hl := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_left _ _))
  have hr := (Real.rpow_lt_rpow_left_iff hP).mp
    (hb'.trans_le (min_le_right _ _))
  have hu₁ : 2*H/3+z/6-Δ/3 < b := by linarith
  have hu₂ : b < H+2*y-z/2+Δ := by linarith
  obtain ⟨hzp,hd,hHc,hlow,_,hzlarge,_,hm₁,hm₂⟩ :=
    unsafe_selected_actual_margins hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁
  have ham : (623/1000 : ℝ) < min z (1-α)-y := by
    rw [← min_sub_sub_right]; exact lt_min hm₁ hm₂
  have hC : C₀ < P^(min z (1-α)-y) :=
    hC₀.trans_lt ((Real.rpow_lt_rpow_left_iff hP).mpr (by linarith))
  have hΛ' := hΛ (by linarith)
  have hmax : max 1 (max (P^(-2*c)*Λ^2) (P^(-H)*Λ^2)) ≤
      P^(-2*c+(2*max α c+2*y+2*z/1000)) := by
    calc
      _ ≤ max 1 (max (P^(-2*c)*P^(2*max α c+2*y+2*z/1000))
          (P^(-H)*P^(2*max α c+2*y+2*z/1000))) := by gcongr
      _ ≤ _ := max_growth_bound hP hHc.le (by have := le_max_right α c; linarith)
  have hka := (hactual hC).trans
    (mul_le_mul_of_nonneg_left hmax (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hka
  have hfa := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hka)
  have hmaxmin : max α c + min α c = α+c := max_add_min α c
  have hactual' : b < H/2-min α c+y+(2/1000 : ℝ)*z := by linarith
  obtain ⟨hz',hpa',hyl,hyu⟩ := unsafe_selected_improved_window
    hα hz hc hy hH hzc hΔ hnear hfar₁ hfar₂ hu₁ hu₂ hactual'
  have hki := (himproved (by linarith) (by linarith) hyl.le hyu.le).trans
    (mul_le_mul_of_nonneg_left
      (max_growth_bound hP hHc.le (by have := le_max_right α c; linarith))
      (Real.rpow_nonneg hP0.le _))
  rw [← Real.rpow_add hP0] at hki
  have hfi := (Real.rpow_lt_rpow_left_iff hP).mp (hkfar.trans_le hki)
  have himproved' : b < H/2-min α c+(29/50 : ℝ)*y+Δ := by linarith
  exact unsafe_selected_improved_contradiction hα hzp hc hd hlow hnear hu₁ himproved'

lemma eventually_selection_constants (C₀ C₁ M A : ℝ)
    (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A) :
    ∀ᶠ P : ℝ in atTop, 1 < P ∧ C₀ ≤ P^(3/10 : ℝ) ∧
      C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ) := by
  have he : (0 : ℝ) < 66/100000 := by norm_num
  have hconst : (fun _ : ℝ => C₁*M) =o[atTop]
      (fun P : ℝ => P^(66/100000 : ℝ)) :=
    (Asymptotics.isLittleO_const_id_atTop _).comp_tendsto (tendsto_rpow_atTop he)
  have hsqrt := (isLittleO_log_rpow_rpow_atTop (1/2 : ℝ) he).const_mul_left
    (C₁*Real.sqrt (2*A))
  have hsum := hconst.add hsqrt
  filter_upwards [hsum.bound (by norm_num : (0 : ℝ) < 1),
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3/10)).eventually_ge_atTop C₀,
    eventually_ge_atTop (2 : ℝ)] with P hsum hC₀ hP
  have hP0 : 0 < P := by linarith
  refine ⟨by linarith,hC₀,?_⟩
  have hlog : Real.log (2+P) ≤ 2*Real.log P := by
    calc
      _ ≤ Real.log (P^2) := Real.log_le_log (by positivity) (by nlinarith)
      _ = _ := by rw [Real.log_pow]; norm_num
  have hs : Real.sqrt (A*Real.log (2+P)) ≤
      Real.sqrt (2*A)*Real.sqrt (Real.log P) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*A)]
    apply Real.sqrt_le_sqrt
    nlinarith
  have hb : C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ) ≤ P^(66/100000 : ℝ) := by
    have := (le_abs_self (C₁*M+(C₁*Real.sqrt (2*A))*Real.log P^(1/2 : ℝ))).trans hsum
    simpa only [Real.norm_eq_abs, one_mul, abs_of_pos (Real.rpow_pos_of_pos hP0 _)] using this
  rw [← Real.sqrt_eq_rpow] at hb
  nlinarith

lemma div_stabilityLength (P C₁ M A p w φ t : ℝ) :
    t/stabilityLength P C₁ M A p w φ =
      t*(stabilityRate P C₁ M A p w φ)^2 := by
  simp [stabilityLength, div_eq_mul_inv, inv_pow]

lemma sqrt_div_le_small_denominator {a x : ℝ} (ha : 0 ≤ a)
    (hx : 0 < x) (hx₁ : x ≤ 1) : Real.sqrt (a/x) ≤ Real.sqrt a/x := by
  rw [Real.sqrt_div ha]
  exact div_le_div_of_nonneg_left (Real.sqrt_nonneg a) hx
    (Real.le_sqrt_self_iff.mpr hx₁)

lemma rpow_min_exponent {P a b : ℝ} (hP : 1 < P) :
    min (P^a) (P^b) = P^(min a b) := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, min_eq_left ((Real.rpow_le_rpow_left_iff hP).mpr h)]
  · rw [min_eq_right h, min_eq_right ((Real.rpow_le_rpow_left_iff hP).mpr h)]

lemma sqrt_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) :
    Real.sqrt (P^a) = P^(a/2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hP]
  congr 1
  ring

lemma stabilityRate_power_bound {P C₁ M A p w φ α z c y : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hφ₁ : φ ≤ 1) (hzc : z+c=1) (hz : (66/100 : ℝ) < z)
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ)) :
    stabilityRate P C₁ M A p w φ ≤ P^(max α c+y+z/1000) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hm0 : 0 < min p w := hm ▸ Real.rpow_pos_of_pos hP0 _
  have hAL : 0 ≤ A*Real.log (2+P) := mul_nonneg hA (Real.log_nonneg (by linarith))
  have hs := sqrt_div_le_small_denominator hAL hφ0 hφ₁
  have hfactor : P/min p w/φ = P^(max α c+y) := by
    rw [hm,hφ]
    nth_rw 1 [← Real.rpow_one P]
    rw [← Real.rpow_sub hP0,← Real.rpow_sub hP0]
    congr 1
    ring
  calc
    _ ≤ C₁*(P/min p w)*(M/φ+Real.sqrt (A*Real.log (2+P))/φ) := by
      unfold stabilityRate
      gcongr
    _ = (C₁*(M+Real.sqrt (A*Real.log (2+P)))) * P^(max α c+y) := by
      rw [← hfactor]
      ring
    _ ≤ P^(66/100000 : ℝ) * P^(max α c+y) := by gcongr
    _ = P^((66/100000 : ℝ)+(max α c+y)) := (Real.rpow_add hP0 _ _).symm
    _ ≤ _ := (Real.rpow_le_rpow_left_iff hP).mpr (by linarith)

lemma nat_pow_rpow_base {P : ℝ} (hP : 0 ≤ P) (a : ℝ) (n : ℕ) :
    (P^a)^n = P^(a*n) := (Real.rpow_mul_natCast hP a n).symm

lemma selectionWeight_power {P p θ φ h α b y H : ℝ} (hP : 0 < P)
    (hp : p=P^(1-α)) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    selectionWeight P θ φ h = P^(-(α+b+y+H)/100000) := by
  have hp0 : p ≠ 0 := hp ▸ (Real.rpow_pos_of_pos hP _).ne'
  have hPθ : P*θ = P^(α+b) := by
    calc
      _ = (P*(p*θ))/p := by field_simp
      _ = (P*P^b)/P^(1-α) := by rw [hpθ,hp]
      _ = P^(1+b)/P^(1-α) := by rw [Real.rpow_add hP,Real.rpow_one]
      _ = P^((1+b)-(1-α)) := (Real.rpow_sub hP _ _).symm
      _ = _ := by congr 1; ring
  unfold selectionWeight
  rw [hPθ,hφ,hh,← Real.rpow_mul hP.le,← Real.rpow_mul hP.le,
    ← Real.rpow_mul hP.le,← Real.rpow_add hP,← Real.rpow_add hP]
  congr 1
  ring

lemma receiverCoefficient_power {P w p θ φ h z b y H : ℝ} (hP : 0 < P)
    (hw : w=P^z) (hpθ : p*θ=P^b) (hφ : φ=P^(-y)) (hh : h=P^(-H)) :
    receiverCoefficient w p θ φ h =
      min (P^(-z-2*H+3*b)) (P^(-z-b+H+2*y)) := by
  unfold receiverCoefficient
  rw [hw,hpθ,hφ,hh,mul_min_of_nonneg _ _ (inv_nonneg.mpr (Real.rpow_nonneg hP.le _)),
    ← Real.rpow_neg hP.le, nat_pow_rpow_base hP.le, nat_pow_rpow_base hP.le,
    nat_pow_rpow_base hP.le]
  norm_num only [Nat.cast_ofNat]
  simp only [← Real.rpow_add hP,← Real.rpow_neg hP.le]
  congr 2 <;> ring

lemma selected_near_far_powers
    {P p w θ φ h I μ α z c b y H Δ : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hΔ : Δ=(α+b+y+H)/100000)
    (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    2*α+H/2+2*y < z+Δ ∧ P^(α+b-H-Δ) < Real.sqrt (p*μ) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hθ0 : 0 < θ := (mul_pos_iff.mp (hpθ ▸ Real.rpow_pos_of_pos hP0 _)).resolve_right
    (by rintro ⟨hh,_⟩; linarith) |>.2
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hWI : selectionWeight P θ φ h = P^(-Δ) := by
    rw [selectionWeight_power hP0 hp hpθ hφ hh,hΔ,neg_div]
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hsI : 0 < Real.sqrt I := Real.sqrt_pos.mpr hI0
  have hsI' : Real.sqrt I ≤ P^(-c) := by
    calc
      _ ≤ Real.sqrt (P^(-2*c)) := Real.sqrt_le_sqrt hI'
      _ = _ := by rw [sqrt_rpow_base hP0.le]; congr 1; ring
  have hθeq : θ=P^(α+b-1) := by
    calc
      θ = (p*θ)/p := by field_simp
      _ = P^b/P^(1-α) := by rw [hpθ,hp]
      _ = P^(b-(1-α)) := (Real.rpow_sub hP0 _ _).symm
      _ = _ := by congr 1; ring
  have hn := hselected.trans_le (min_le_left _ _)
  have hf := hselected.trans_le (min_le_right _ _)
  have hn' : P*selectionWeight P θ φ h < Real.sqrt I*Real.sqrt h*p^2*φ^2 := by
    apply (mul_lt_mul_iff_right₀ hsI).mp
    calc
      _ = P*Real.sqrt I*selectionWeight P θ φ h := by ring
      _ < _ := hn
      _ = (Real.sqrt I)^2*Real.sqrt h*p^2*φ^2 := by rw [Real.sq_sqrt hI0.le]
      _ = _ := by ring
  have hnb : P^(1-Δ) < P^(-c-H/2+2*(1-α)-2*y) := by
    calc
      _ = P*selectionWeight P θ φ h := by
        rw [hWI,Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
      _ < _ := hn'
      _ ≤ P^(-c)*Real.sqrt h*p^2*φ^2 := by gcongr
      _ = _ := by
        rw [hh,hp,hφ,sqrt_rpow_base hP0.le,nat_pow_rpow_base hP0.le,nat_pow_rpow_base hP0.le]
        norm_num only [Nat.cast_ofNat]
        simp only [← Real.rpow_add hP0]
        congr 1
        ring
  have hne := (Real.rpow_lt_rpow_left_iff hP).mp hnb
  have hf' : P*selectionWeight P θ φ h*(θ*h) < Real.sqrt (p*μ) := by
    have ht := (lt_div_iff₀ (mul_pos hθ0 hh0)).mp hf
    apply (mul_lt_mul_iff_right₀ hsI).mp
    convert ht using 1 <;> first | rfl | ring
  have hfb : P*selectionWeight P θ φ h*(θ*h) = P^(α+b-H-Δ) := by
    rw [hWI,hθeq,hh]
    have ee : P*P^(-Δ)=P^(1-Δ) := by
      rw [Real.rpow_sub hP0,Real.rpow_one,Real.rpow_neg hP0.le,div_eq_mul_inv]
    rw [ee,← Real.rpow_add hP0,← Real.rpow_add hP0]
    congr 1
    ring
  exact ⟨by linarith, hfb ▸ hf'⟩

lemma improvedWindow_of_powers {P p w φ α z y : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y))
    (hp' : (7/10 : ℝ) ≤ 1-α) (hw' : (7/10 : ℝ) ≤ z)
    (hyl : (16/100 : ℝ)*max z (1-α) ≤ y)
    (hyu : y ≤ (49/100 : ℝ)*min z (1-α)) : ImprovedWindow P p w φ := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hzlo := le_max_left z (1-α)
  have hplo := le_max_right z (1-α)
  have hzup := min_le_left z (1-α)
  have hpup := min_le_right z (1-α)
  unfold ImprovedWindow
  rw [hp,hw,hφ]
  refine ⟨(Real.rpow_le_rpow_left_iff hP).mpr hp',
    (Real.rpow_le_rpow_left_iff hP).mpr hw',?_,?_,?_,?_⟩ <;>
    rw [← Real.rpow_mul hP0.le] <;>
    apply (Real.rpow_le_rpow_left_iff hP).mpr <;> linarith

lemma pureOccupationBounds_power_table
    {P C₀ C₁ M A p w φ h I μ α z c y H : ℝ} (hP : 1 < P)
    (hp : p=P^(1-α)) (hw : w=P^z) (hφ : φ=P^(-y)) (hh : h=P^(-H))
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI : I ≤ (w/P)^2)
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ) :
    (Real.sqrt (p*μ))^2 ≤ P^(-min (2*c) H) ∧
    (C₀ < P^(min z (1-α)-y) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H)*max 1
        (max (P^(-2*c)*(stabilityRate P C₁ M A p w φ)^2)
          (P^(-H)*(stabilityRate P C₁ M A p w φ)^2))) ∧
    ((7/10 : ℝ) ≤ z → (7/10 : ℝ) ≤ 1-α →
      (16/100 : ℝ)*max z (1-α) ≤ y → y ≤ (49/100 : ℝ)*min z (1-α) →
      (Real.sqrt (p*μ))^2 ≤ P^(-H+(29/25 : ℝ)*y)*
        max 1 (max (P^(-2*c)*P^(2*max α c)) (P^(-H)*P^(2*max α c)))) := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
  have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
  have hm0 : 0 < min p w := lt_min hp0 hw0
  have hh0 : 0 < h := hh ▸ Real.rpow_pos_of_pos hP0 _
  have hI' : I ≤ P^(-2*c) := by
    calc
      I ≤ (w/P)^2 := hI
      _ = (P^(z-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hw]
      _ = P^(-2*c) := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; linarith
  have hm : min p w = P^(1-max α c) := by
    rw [hp,hw,rpow_min_exponent hP]
    congr 1
    rcases le_total α c with hh | hh
    · rw [max_eq_right hh,min_eq_right (by linarith)]; linarith
    · rw [max_eq_left hh,min_eq_left (by linarith)]
  have hIm : (min p w/P)^2 = P^(-2*max α c) := by
    calc
      _ = (P^((1-max α c)-1))^2 := by rw [Real.rpow_sub hP0,Real.rpow_one,hm]
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hmp : min p w*φ = P^(min z (1-α)-y) := by
    rw [hp,hw,hφ,rpow_min_exponent hP,← Real.rpow_add hP0,min_comm]
    congr 1
  rw [Real.sq_sqrt (mul_nonneg hp0.le hμ)]
  rcases hbounds with ⟨he,ha,hi⟩
  refine ⟨?_,?_,?_⟩
  · calc
      p*μ ≤ p*(max I h/p) := mul_le_mul_of_nonneg_left he hp0.le
      _ = max I h := by field_simp
      _ ≤ P^(-min (2*c) H) := by
        apply max_le
        · exact hI'.trans ((Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_left (2*c) H; linarith))
        · rw [hh]; exact (Real.rpow_le_rpow_left_iff hP).mpr (by have := min_le_right (2*c) H; linarith)
  · intro hC
    have hC' : C₀/min p w < φ := (div_lt_iff₀ hm0).mpr (by rw [mul_comm,hmp]; exact hC)
    calc
      p*μ ≤ p*((h/p)*max 1 (max (I/stabilityLength P C₁ M A p w φ)
        (h/stabilityLength P C₁ M A p w φ))) := mul_le_mul_of_nonneg_left (ha hC') hp0.le
      _ = h*max 1 (max (I*(stabilityRate P C₁ M A p w φ)^2)
          (h*(stabilityRate P C₁ M A p w φ)^2)) := by
        rw [div_stabilityLength,div_stabilityLength]
        field_simp
      _ ≤ _ := by rw [hh]; gcongr
  · intro hz' hp' hyl hyu
    have hi' := hi (improvedWindow_of_powers hP hp hw hφ hp' hz' hyl hyu)
    calc
      p*μ ≤ p*((h/p)*φ^(-29/25 : ℝ)*max 1 (max (I/(min p w/P)^2) (h/(min p w/P)^2))) :=
        mul_le_mul_of_nonneg_left hi' hp0.le
      _ = (h*φ^(-29/25 : ℝ))*max 1 (max (I*P^(2*max α c)) (h*P^(2*max α c))) := by
        rw [hIm,show -2*max α c = -(2*max α c) by ring,Real.rpow_neg hP0.le]
        simp only [div_inv_eq_mul]
        field_simp
      _ ≤ (h*φ^(-29/25 : ℝ))*max 1 (max (P^(-2*c)*P^(2*max α c)) (h*P^(2*max α c))) := by
        gcongr
        exact mul_nonneg hh0.le (Real.rpow_nonneg (hφ ▸ Real.rpow_nonneg hP0.le _) _)
      _ = _ := by
        rw [hh,hφ,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
        congr 2
        ring

lemma selected_receiverCoefficient_of_powers
    {P C₀ C₁ M A p w θ φ h I μ α z c b y H : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp : p=P^(1-α)) (hw : w=P^z) (hpθ : p*θ=P^b)
    (hφ : φ=P^(-y)) (hh : h=P^(-H)) (hφ₁ : φ ≤ 1)
    (hα : 0 ≤ α) (hz : 0 ≤ z) (hc : 0 ≤ c) (hy : 0 ≤ y) (hH : 0 ≤ H)
    (hzc : z+c=1) (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  let Δ := (α+b+y+H)/100000
  obtain ⟨hn,hf⟩ := selected_near_far_powers hP hp hw hpθ hφ hh hzc (show Δ=_ from rfl)
    hI0 hI hselected
  obtain ⟨he,ha,hi⟩ := pureOccupationBounds_power_table hP hp hw hφ hh hzc hμ hI hbounds
  have hr0 : 0 ≤ stabilityRate P C₁ M A p w φ := by
    have hp0 : 0 < p := hp ▸ Real.rpow_pos_of_pos hP0 _
    have hw0 : 0 < w := hw ▸ Real.rpow_pos_of_pos hP0 _
    have hm0 : 0 < min p w := lt_min hp0 hw0
    have hφ0 : 0 < φ := hφ ▸ Real.rpow_pos_of_pos hP0 _
    unfold stabilityRate
    positivity
  have hr : (66/100 : ℝ) < z → (stabilityRate P C₁ M A p w φ)^2 ≤
      P^(2*max α c+2*y+2*z/1000) := by
    intro hz'
    have hrate := stabilityRate_power_bound hP hC₁ hA hp hw hφ hφ₁ hzc hz' hconst
    calc
      _ ≤ (P^(max α c+y+z/1000))^2 := (sq_le_sq₀ hr0 (Real.rpow_nonneg hP0.le _)).mpr hrate
      _ = _ := by rw [nat_pow_rpow_base hP0.le]; congr 1; norm_num; ring
  have hb := selected_coefficient_power_table hP hα hz hc hy hH hzc (show Δ=_ from rfl)
    hn (Real.sqrt_nonneg _) hf he hC₀ hr ha hi
  rw [receiverCoefficient_power hP0 hw hpθ hφ hh,
    selectionWeight_power hP0 hp hpθ hφ hh,hw,← Real.rpow_mul hP0.le,← Real.rpow_add hP0]
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [Δ]
  congr 1
  ring

lemma selected_receiverCoefficient
    {P C₀ C₁ M A p w θ φ h I μ : ℝ}
    (hP : 1 < P) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hp0 : 0 < p) (hpP : p ≤ P) (hw1 : 1 ≤ w) (hwP : w ≤ P)
    (hθ : 0 < θ) (hφ : 0 < φ) (hφ1 : φ ≤ 1) (hh : 0 < h) (hh1 : h ≤ 1)
    (hμ : 0 ≤ μ) (hI0 : 0 < I) (hI : I ≤ (w/P)^2)
    (hC₀ : C₀ ≤ P^(3/10 : ℝ))
    (hconst : C₁*(M+Real.sqrt (A*Real.log (2+P))) ≤ P^(66/100000 : ℝ))
    (hbounds : PureOccupationBounds P C₀ C₁ M A p w φ h I μ)
    (hselected : P*Real.sqrt I*selectionWeight P θ φ h <
      min (I*Real.sqrt h*p^2*φ^2) (Real.sqrt I*Real.sqrt (p*μ)/(θ*h))) :
    receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  have hP0 : 0 < P := zero_lt_one.trans hP
  have hp' : p=P^(1-(1-Real.logb P p)) := by
    rw [sub_sub_cancel,Real.rpow_logb hP0 hP.ne' hp0]
  have hw' : w=P^(Real.logb P w) := (Real.rpow_logb hP0 hP.ne' (zero_lt_one.trans_le hw1)).symm
  have hpθ' : p*θ=P^(Real.logb P (p*θ)) := (Real.rpow_logb hP0 hP.ne' (mul_pos hp0 hθ)).symm
  have hφ' : φ=P^(-(-Real.logb P φ)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hφ]
  have hh' : h=P^(-(-Real.logb P h)) := by rw [neg_neg,Real.rpow_logb hP0 hP.ne' hh]
  have hα : 0 ≤ 1-Real.logb P p := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hp0).mpr (by simpa using hpP))
  have hc : 0 ≤ 1-Real.logb P w := sub_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP (zero_lt_one.trans_le hw1)).mpr (by simpa using hwP))
  have hy : 0 ≤ -Real.logb P φ := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hφ).mpr (by simpa using hφ1))
  have hH : 0 ≤ -Real.logb P h := neg_nonneg.mpr
    ((Real.logb_le_iff_le_rpow hP hh).mpr (by simpa using hh1))
  exact selected_receiverCoefficient_of_powers hP hC₁ hM hA hp' hw' hpθ' hφ' hh' hφ1
    hα (Real.logb_nonneg hP hw1) hc hy hH (by ring) hμ hI0 hI hC₀ hconst hbounds hselected

lemma pureOccupationEnvelope_bounds (P C₀ C₁ M A p w φ h I : ℝ) :
    PureOccupationBounds P C₀ C₁ M A p w φ h I
      (pureOccupationEnvelope P C₀ C₁ M A p w φ h I) := by
  classical
  unfold PureOccupationBounds pureOccupationEnvelope
  dsimp only
  refine ⟨?_,?_,?_⟩
  · exact (min_le_left _ _).trans (by split_ifs <;> simp only [min_le_left,le_refl])
  · intro ha
    rw [ite_eq_left ha]
    exact (min_le_left _ _).trans (min_le_right _ _)
  · intro hb
    rw [ite_eq_left hb]
    exact (min_le_right _ _).trans (min_le_right _ _)

lemma pureOccupationEnvelope_nonneg
    {P C₀ C₁ M A p w φ h I : ℝ} (hp : 0 ≤ p) (hφ : 0 ≤ φ)
    (hh : 0 ≤ h) (hI : 0 ≤ I) :
    0 ≤ pureOccupationEnvelope P C₀ C₁ M A p w φ h I := by
  classical
  unfold pureOccupationEnvelope
  dsimp only
  split_ifs <;> positivity

theorem receiverCoefficient_on_selected_bins
    (C₀ C₁ M A : ℝ) (hC₁ : 0 ≤ C₁) (hM : 0 ≤ M) (hA : 0 ≤ A) :
    ∀ᶠ P in atTop, ∀ p w θ φ h I : ℝ,
      0 < p → p ≤ P → 1 ≤ w → w ≤ P → 0 < θ →
      0 < φ → φ ≤ 1 → 0 < h → h ≤ 1 → 0 < I → I ≤ (w/P)^2 →
      P*Real.sqrt I*selectionWeight P θ φ h <
        min (I*Real.sqrt h*p^2*φ^2)
          (Real.sqrt I*Real.sqrt (p*pureOccupationEnvelope P C₀ C₁ M A p w φ h I)/(θ*h)) →
      receiverCoefficient w p θ φ h ≤ w^(-1/2 : ℝ)*selectionWeight P θ φ h := by
  filter_upwards [eventually_selection_constants C₀ C₁ M A hC₁ hA] with P hP
  intro p w θ φ h I hp hpP hw hwP hθ hφ hφ1 hh hh1 hI0 hI hselected
  exact selected_receiverCoefficient hP.1 hC₁ hM hA hp hpP hw hwP hθ hφ hφ1 hh hh1
    (pureOccupationEnvelope_nonneg hp.le hφ.le hh.le hI0.le) hI0 hI hP.2.1 hP.2.2
    (pureOccupationEnvelope_bounds ..) hselected

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
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SelectionCounts
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

lemma selectionDecay_pos : 0 < selectionDecay := Real.rpow_pos_of_pos (by norm_num) _
lemma selectionDecay_lt_one : selectionDecay<1 := by
  exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

lemma selectionDecay_pow (n : ℕ) :
    selectionDecay^n=((2:ℝ)^n)^(-1/100000:ℝ) := by
  rw [selectionDecay,←Real.rpow_natCast_mul (by norm_num),←Real.rpow_mul_natCast (by norm_num)]
  congr 1
  ring

lemma cappedRepresentative_selection_pow (n : ℕ) :
    (cappedRepresentative n)^(1/100000:ℝ)=selectionDecay^n := by
  rw [selectionDecay_pow]
  dsimp [cappedRepresentative]
  rw [inv_pow,Real.inv_rpow (by positivity),←Real.rpow_neg (by positivity)]
  congr 1
  norm_num

lemma sourceRepresentative_two_pow (n : ℕ) : sourceRepresentative n=(2:ℝ)^(n+6) := by
  simp only [sourceRepresentative,pow_add]
  ring

lemma selection_angle_index {np nt : ℕ}
    (h : 1/sourceRepresentative np ≤ cappedRepresentative nt) : nt≤np+6 := by
  rw [sourceRepresentative_two_pow] at h
  have he : (2:ℝ)^nt≤2^(np+6) := by
    have hp : 0<(2:ℝ)^nt := by positivity
    have hq : 0<(2:ℝ)^(np+6) := by positivity
    dsimp [cappedRepresentative] at h
    rw [inv_pow,one_div] at h
    exact (inv_le_inv₀ hq hp).mp h
  exact (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp he

lemma selectionWeight_gap_bound {P : ℝ} {N : ℕ} {k : Fin 4→ℕ}
    (hP : sourceRepresentative N≤P) (h0 : k 0≤N) (h1 : k 1≤k 0+6) :
    selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤
      selectionDecay^(N-k 0)*selectionDecay^(k 0+6-k 1)*selectionDecay^(k 2)*selectionDecay^(k 3) := by
  have hθ := cappedRepresentative_pos (k 1)
  have hN := sourceRepresentative_two_pow N
  have hle : k 1≤N+6 := by omega
  have hid : sourceRepresentative N*cappedRepresentative (k 1)=(2:ℝ)^(N+6-k 1) := by
    rw [hN]
    dsimp [cappedRepresentative]
    rw [inv_pow, pow_sub₀ (2:ℝ) (by norm_num) hle]
  have hdec : (P*cappedRepresentative (k 1))^(-1/100000:ℝ)≤ selectionDecay^(N+6-k 1) := by
    rw [selectionDecay_pow,←hid]
    exact Real.rpow_le_rpow_of_nonpos (by rw [hN]; positivity)
      (mul_le_mul_of_nonneg_right hP hθ.le) (by norm_num)
  have he : N+6-k 1=(N-k 0)+(k 0+6-k 1) := by omega
  unfold selectionWeight
  rw [cappedRepresentative_selection_pow,cappedRepresentative_selection_pow]
  rw [he,pow_add] at hdec
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hdec
    (pow_nonneg selectionDecay_pos.le _)) (pow_nonneg selectionDecay_pos.le _)

lemma sum_selectionDecay (N : ℕ) :
    ∑n∈Finset.range N,selectionDecay^n≤(1-selectionDecay)⁻¹ := by
  have hr : |selectionDecay|<1 := by rw [abs_of_pos selectionDecay_pos]; exact selectionDecay_lt_one
  exact ((summable_geometric_of_abs_lt_one hr).sum_le_tsum (Finset.range N)
    (fun _ _=>pow_nonneg selectionDecay_pos.le _)).trans_eq (tsum_geometric_of_abs_lt_one hr)

lemma sum_selectionDecay_box (N : ℕ) :
    ∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  classical
  have heq : (instDecidableEqFin 4 : DecidableEq (Fin 4))=
      (fun a b=>Classical.propDecidable (a=b)) := Subsingleton.elim _ _
  have hh := Finset.sum_prod_piFinset (Finset.range N) (fun (_i : Fin 4) (n : ℕ)=>selectionDecay^n)
  rw [heq] at hh
  have hsum : (∑k∈dyadicBox (Fin 4) N,∏i,selectionDecay^(k i))=
      (∑n∈Finset.range N,selectionDecay^n)^4 := by
    simpa [dyadicBox,Fin.prod_univ_four,pow_succ] using hh
  rw [hsum]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))
    (sum_selectionDecay N) 4

lemma sum_selectionDecay_finset (S : Finset (Fin 4→ℕ)) :
    ∑k∈S,∏i,selectionDecay^(k i)≤((1-selectionDecay)⁻¹)^4 := by
  obtain ⟨N,hN⟩ := finset_subset_dyadicBox S
  exact (Finset.sum_le_sum_of_subset_of_nonneg hN (fun _ _ _=>Finset.prod_nonneg (fun _ _=>pow_nonneg selectionDecay_pos.le _))).trans
    (sum_selectionDecay_box N)

lemma sum_selectionWeight (S : Finset (Fin 4→ℕ)) {P : ℝ}
    (hP : ∀k∈S,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈S,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1)) :
    ∑k∈S,selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
      (cappedRepresentative (k 3))≤((1-selectionDecay)⁻¹)^4 := by
  classical
  by_cases hS : S.Nonempty
  · let N := S.sup (fun k=>k 0)
    have hN (k) (hk : k∈S) : k 0≤N := Finset.le_sup (f:=fun k : Fin 4→ℕ=>k 0) hk
    have hNP : sourceRepresentative N≤P := by
      obtain ⟨k,hk,he⟩ := Finset.exists_mem_eq_sup S hS (fun k=>k 0)
      change sourceRepresentative (S.sup (fun k : Fin 4→ℕ=>k 0))≤P
      rw [he]
      exact hP k hk
    let g : (Fin 4→ℕ)→(Fin 4→ℕ) := fun k=>![N-k 0,k 0+6-k 1,k 2,k 3]
    have hg : Set.InjOn g ↑S := by
      intro k hk l hl hkl
      have hk1 := selection_angle_index (hθ k hk)
      have hl1 := selection_angle_index (hθ l hl)
      have h00 := congrFun hkl 0
      have h11 := congrFun hkl 1
      have h22 := congrFun hkl 2
      have h33 := congrFun hkl 3
      change N-k 0=N-l 0 at h00
      change k 0+6-k 1=l 0+6-l 1 at h11
      change k 2=l 2 at h22
      change k 3=l 3 at h33
      have hk0 := hN k hk
      have hl0 := hN l hl
      have h0e : k 0=l 0 := by omega
      have h1e : k 1=l 1 := by omega
      apply funext
      intro i
      fin_cases i
      · exact h0e
      · exact h1e
      · exact h22
      · exact h33
    calc
      _≤∑k∈S,∏i,selectionDecay^(g k i) := Finset.sum_le_sum (fun k hk=>by
        simpa [g,Fin.prod_univ_four] using selectionWeight_gap_bound hNP (hN k hk) (selection_angle_index (hθ k hk)))
      _=∑k∈S.image g,∏i,selectionDecay^(k i) := (Finset.sum_image (f:=fun k : Fin 4→ℕ=>∏i,selectionDecay^(k i)) (fun k hk l hl he=>hg hk hl he)).symm
      _≤_ := sum_selectionDecay_finset _
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS,Finset.sum_empty]
    positivity

lemma selectionWeight_nonneg {P θ φ h : ℝ} (hP : 0≤P) (hθ : 0≤θ) (hφ : 0≤φ) (hh : 0≤h) :
    0 ≤ selectionWeight P θ φ h := by unfold selectionWeight; positivity

lemma selection_weighted_tsum {P c : ℝ} (hP0 : 0≤P) (hc : 0 ≤ c)
    (Q : Set (Fin 4→ℕ)) (hP : ∀k∈Q,sourceRepresentative (k 0)≤P)
    (hθ : ∀k∈Q,1/sourceRepresentative (k 0) ≤ cappedRepresentative (k 1))
    (f : (Fin 4→ℕ)→ℝ≥0∞)
    (hf : ∀k∈Q,f k≤ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) :
    (∑'k,Q.indicator f k)≤ENNReal.ofReal (c*((1-selectionDecay)⁻¹)^4) := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  apply iSup_le
  intro S
  let U := S.filter (fun k=>k∈Q)
  have hU (k) (hk : k∈U) : k∈Q := (Finset.mem_filter.mp hk).2
  have hsum : (∑k∈S,Q.indicator f k)=∑k∈U,f k := by simp [U,Finset.sum_filter,indicator_apply]
  rw [hsum]
  calc
    _ ≤ ∑k∈U,ENNReal.ofReal (c*selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3))) := Finset.sum_le_sum (fun k hk=>hf k (hU k hk))
    _ = ENNReal.ofReal (c*(∑k∈U,selectionWeight P (cappedRepresentative (k 1))
        (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) := by
      rw [←ENNReal.ofReal_sum_of_nonneg (fun k _=>mul_nonneg hc
        (selectionWeight_nonneg hP0 (cappedRepresentative_pos _).le
          (cappedRepresentative_pos _).le (cappedRepresentative_pos _).le)),Finset.mul_sum]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
      (sum_selectionWeight U (fun k hk=>hP k (hU k hk)) (fun k hk=>hθ k (hU k hk))) hc)

end RVM

end

open Set Filter Metric MeasureTheory
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

lemma tsum_centralIndexSector (P : ℝ) (f : (Fin 4→ℕ)→ℝ≥0∞) :
    (∑'k,(centralIndexSector P).indicator f k)=
      ∑'n : ℕ×ℕ,({n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2}).indicator
        (fun n=>∑'nt : ℕ,∑'nr : ℕ,if cappedRepresentative nt ≤ cappedRepresentative n.2/16
          then f ![n.1,nt,n.2,nr] else 0) n := by
  classical
  rw [tsum_quad_pair_index]
  apply tsum_congr
  intro n
  by_cases hn : sourceRepresentative n.1≤P ∧ 1/sourceRepresentative n.1 ≤ cappedRepresentative n.2
  · have hn' : n∈{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_mem hn']
    apply tsum_congr
    intro nt
    apply tsum_congr
    intro nr
    have hi : (![n.1,nt,n.2,nr]∈centralIndexSector P) ↔
        cappedRepresentative nt ≤ cappedRepresentative n.2/16 := by
      change (sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
        cappedRepresentative nt ≤ cappedRepresentative n.2/16) ↔_
      simp only [hn.1,hn.2,true_and]
    simp only [indicator_apply,hi]
  · have hn' : n∉{n : ℕ×ℕ | sourceRepresentative n.1≤P ∧
        1/sourceRepresentative n.1 ≤ cappedRepresentative n.2} := hn
    rw [indicator_of_notMem hn']
    apply ENNReal.tsum_eq_zero.mpr
    intro nt
    apply ENNReal.tsum_eq_zero.mpr
    intro nr
    apply indicator_of_notMem
    change ¬(sourceRepresentative n.1≤P ∧
      1/sourceRepresentative n.1 ≤ cappedRepresentative n.2 ∧
      cappedRepresentative nt ≤ cappedRepresentative n.2/16)
    exact fun h=>hn ⟨h.1,h.2.1⟩

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


lemma Admissible.selected_receiver_uniform {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,0<M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ) (g : ℝ→ℝ≥0∞),
      0≤a → b≤T → 1≤w → w≤P → 0<I → I≤(w/P)^2 →
      Measurable g → (∀t,g t≠⊤) →
      let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
      (∑'k : Fin 4→ℕ,Q.indicator (fun k=>representativeReceiverCost s F zX w k a b g) k)≤
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,g t) := by
  obtain ⟨C,hC,hbound⟩ := hd.representative_receiver_envelope T₀
  refine ⟨C*((1-selectionDecay)⁻¹)^4,by positivity,?_⟩
  intro M A hM hA
  filter_upwards [receiverCoefficient_on_selected_bins 512 16384 M A (by norm_num) hM.le hA.le,
    eventually_ge_atTop (1:ℝ)] with P hsafe hP
  intro s T F hs hT hTT zX a b I w g ha hb hw hwP hI hIP hg hgf
  dsimp only
  let Q := {k | k∈representativeSmallSector P ∧ representativeSelected P M A w I k}
  let L := ∫⁻t in Icc a b,g t
  have hw0 : 0<w := zero_lt_one.trans_le hw
  have hpt (k : Fin 4→ℕ) (hk : k∈Q) :
      representativeReceiverCost s F zX w k a b g≤
        ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
          (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))*L := by
    have he := hbound s T F hs hT hTT zX k a b w g ha hb hw0 hg hgf
    have hu := hsafe (sourceRepresentative (k 0)) w (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)) I
      (by unfold sourceRepresentative; positivity) hk.1.1 hw hwP (cappedRepresentative_pos _)
      (cappedRepresentative_pos _) (cappedRepresentative_le_one _) (cappedRepresentative_pos _)
      (cappedRepresentative_le_one _) hI hIP hk.2
    apply he.trans
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hu hC
  have hwgt := selection_weighted_tsum (zero_le_one.trans hP) (by positivity : 0≤C*w^(-1/2:ℝ))
    Q (fun _ hk=>hk.1.1) (fun _ hk=>hk.1.2.1)
    (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*selectionWeight P (cappedRepresentative (k 1))
      (cappedRepresentative (k 2)) (cappedRepresentative (k 3)))) (fun _ _=>le_rfl)
  classical
  calc
    _ ≤ ∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))*L) k := by
      apply ENNReal.tsum_le_tsum
      intro k
      by_cases hk : k∈Q
      · change Q.indicator _ k≤_
        simpa only [indicator_of_mem hk] using hpt k hk
      · change Q.indicator _ k≤_
        simp only [indicator_of_notMem hk,le_refl]
    _ = (∑'k : Fin 4→ℕ,Q.indicator (fun k=>ENNReal.ofReal ((C*w^(-1/2:ℝ))*
        selectionWeight P (cappedRepresentative (k 1)) (cappedRepresentative (k 2))
        (cappedRepresentative (k 3)))) k)*L := by
      simp_rw [indicator_mul_left]
      exact ENNReal.tsum_mul_right
    _ ≤ ENNReal.ofReal ((C*w^(-1/2:ℝ))*((1-selectionDecay)⁻¹)^4)*L := mul_le_mul' hwgt le_rfl
    _ = _ := by congr 2; ring



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

section
-- module Solutions.OAIQ073_VM.VlasovMaxwell_Population_SpatialEstimates
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace RVM

open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff


open Set Filter Metric MeasureTheory
open scoped ENNReal Topology ContDiff



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


lemma Admissible.bulk_remainder_uniform_oai {d : Datum} (hd : Admissible d) (T₀ : ℝ) :
    ∃ C : ℝ,0≤C ∧ ∀ M A : ℝ,1≤M → 0<A → ∀ᶠ P : ℝ in atTop,
    ∀ (s : Solution) (T : ℝ) (F : PhaseFlowOn s.E s.B T),
      SmoothClassicalPrefix d s T → 0≤T → T≤T₀ →
    ∀ (zX : Phase) (a b I w : ℝ),
      zX∈tsupport d.f₀ → 0≤a → b≤T → 0<I → b-a≤I → 1≤w → w≤P → I≤(w/P)^2 →
      (∀z∈tsupport d.f₀,IncrementBootstrap (fun t=>(F.flow z t).2) T M A P (Real.log (2+P))) →
      (∀σ∈Icc 0 T,∀z : Phase,s.f (σ,z)≠0→1024*q z.2≤P) →
      (∀t∈Icc a b,q (F.flow zX t).2∈Icc (w/8) (8*w)) →
    ∀ W : ℝ→Vec→L[ℝ]Vec,Measurable W → (∀t∈Icc a b,‖W t‖≤1) →
      (∫⁻p,ENNReal.ofReal ‖selectedConeTriangle s F.flow zX T (bulkSelection P M A w I)
        (remainderConeKernel s F.flow zX) W (Icc a b) p‖ ∂trianglePhaseMeasure)≤
        ENNReal.ofReal (C*(P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w))+
        ENNReal.ofReal (C*w^(-1/2:ℝ))*(∫⁻t in Icc a b,ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) := by
  obtain ⟨Cc,hCc,hcentral⟩ := hd.central_uniform T₀
  obtain ⟨Cr,hCr,hreceiver⟩ := hd.selected_receiver_uniform T₀
  let C := 147*Cc+15424*Cr
  have hC : 0≤C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M A hM hA
  filter_upwards [hreceiver M A (zero_lt_one.trans_le hM) hA,
    eventually_ge_atTop (1:ℝ),eventually_ge_atTop (Real.exp 1)] with P hr hP he
  have hL : 1≤Real.log (2+P) := by
    calc
      1=Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _≤Real.log (2+P) := Real.log_le_log (Real.exp_pos 1) (by linarith)
  intro s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP hIP HZ hphysical hband W hW hW1
  have hc := hcentral M A P hM hA.le hP hL s T F hs hT hTT zX a b I w hzX ha hb hI hJI hw hwP HZ
  dsimp only at hc
  rw [←tsum_centralIndexSector P (fun k=>representativeCentralCost s F zX w k a b)] at hc
  have hg := (F.continuous_prefixMomentumForce hs.energyPrefix hT zX).norm.measurable.ennreal_ofReal
  have hr' := hr s T F hs hT hTT zX a b I w
    (fun t=>ENNReal.ofReal ‖prefixMomentumForce s F.flow T zX t‖) ha hb hw hwP hI hIP hg
    (fun _=>ENNReal.ofReal_ne_top)
  apply (F.bulkRemainder_selected_sum hs.energyPrefix hT zX (zero_lt_one.trans_le hw)
    ha hb hband hphysical hW hW1).trans
  apply (add_le_add (mul_le_mul' le_rfl hc) (mul_le_mul' le_rfl hr')).trans
  rw [←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤147)]
  apply add_le_add
  · apply ENNReal.ofReal_le_ofReal
    have hB : 0≤P*Real.sqrt I+(M+Real.sqrt A)*I*P^2*Real.log (2+P)/w := by positivity
    dsimp [C]
    nlinarith [mul_nonneg (by positivity : 0≤15424*Cr) hB]
  · rw [←mul_assoc,←ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤15424)]
    apply mul_le_mul' _ le_rfl
    apply ENNReal.ofReal_le_ofReal
    have hn := Real.rpow_nonneg (zero_le_one.trans hw) (-1/2:ℝ)
    dsimp [C]
    nlinarith [mul_nonneg (by positivity : 0≤147*Cc) hn]



open Set Filter Metric MeasureTheory _root_.Classical
open scoped ENNReal Topology ContDiff


end RVM

end

end OAI
end

theorem solution : type_of% @OAI.RVM.Admissible.bulk_remainder_uniform_oai := @OAI.RVM.Admissible.bulk_remainder_uniform_oai
