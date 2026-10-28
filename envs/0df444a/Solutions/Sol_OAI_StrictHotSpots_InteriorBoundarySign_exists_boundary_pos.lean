-- Prove2me | solution 1 for OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T05:24:05.178382+00:00
-- url     : https://prove2.me/submissions/3eaa2c5b-87dd-46ba-8be1-cd472041557d

import Mathlib
import Definitions.Def_HotSpots
import Definitions.Def_OAIQ3Ho002
import Definitions.Def_OAIQ3Ho003
import Theorems.Thm_OAI_StrictHotSpots_H10_subcritical

section
-- module Solutions.OAIQ3_Hot.HotSpots_Variational
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section L2InnerToLpCombinedLayer
open MeasureTheory Filter
open scoped ENNReal InnerProductSpace
namespace StrictHotSpots.L2Inner
lemma toLp_pair {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f g : α → E} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ x, inner ℝ (f x) (g x) ∂μ := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp,hg.coeFn_toLp] with x hx hy
  rw [hx,hy]
end StrictHotSpots.L2Inner
end L2InnerToLpCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Trace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section DouglasLipschitzBase
noncomputable section

section BoundarySignLimitsCombinedLayer
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace StrictHotSpots.Nodal
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {u : α → ℝ}
lemma cutoff_square_integral (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ x, (cutoff n (u x))^2 ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then (u x)^2 else 0 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (u x)^2)
  · intro n
    exact ((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable).pow 2
  · exact hu.integrable_sq
  · intro n
    exact Eventually.of_forall fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      simpa only [Real.norm_eq_abs,sq_abs] using
        pow_le_pow_left₀ (norm_nonneg _) (cutoff_norm_le n (u x)) 2
  · exact Eventually.of_forall fun x => by
      simpa only [ite_pow,zero_pow (by decide : 2 ≠ 0)] using (cutoff_tendsto (u x)).pow 2
lemma cutoff_product_integral (hu : MemLp u 2 μ) :
    Tendsto (fun n => ∫ x, u x * cutoff n (u x) ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then (u x)^2 else 0 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => (u x)^2)
  · intro n
    exact hu.aestronglyMeasurable.mul
      ((cutoff_contDiff n).continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  · exact hu.integrable_sq
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul]
      calc
        ‖u x‖ * ‖cutoff n (u x)‖ ≤ ‖u x‖ * ‖u x‖ :=
          mul_le_mul_of_nonneg_left (cutoff_norm_le n _) (norm_nonneg _)
        _ = (u x)^2 := by rw [← pow_two,Real.norm_eq_abs,sq_abs]
  · exact Eventually.of_forall fun x => by
      simpa only [mul_ite,mul_zero,← pow_two] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => u x) atTop (𝓝 (u x))).mul (cutoff_tendsto (u x))
lemma cutoff_deriv_integral (hu : AEStronglyMeasurable u μ) {g : α → ℝ}
    (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    Tendsto (fun n => ∫ x, deriv (cutoff n) (u x) * g x ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then g x else 0 ∂μ)) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply tendsto_integral_of_dominated_convergence (fun x => C * g x)
  · intro n
    exact (((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable hu).mul
      hg.aestronglyMeasurable
  · exact hg.const_mul C
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul,Real.norm_of_nonneg (hgn x)]
      exact mul_le_mul_of_nonneg_right (hbd n _) (hgn x)
  · exact Eventually.of_forall fun x => by
      simpa only [ite_mul,one_mul,zero_mul] using (cutoff_deriv_tendsto (u x)).mul tendsto_const_nhds
lemma cutoff_deriv_square_integral (hu : AEStronglyMeasurable u μ) {g : α → ℝ}
    (hg : Integrable g μ) (hgn : ∀ x, 0 ≤ g x) :
    Tendsto (fun n => ∫ x, (deriv (cutoff n) (u x))^2 * g x ∂μ) atTop
      (𝓝 (∫ x, if 0 < u x then g x else 0 ∂μ)) := by
  obtain ⟨C,hC,hbd⟩ := cutoff_deriv_bound
  apply tendsto_integral_of_dominated_convergence (fun x => C^2 * g x)
  · intro n
    exact ((((cutoff_contDiff n).continuous_deriv (by simp)).comp_aestronglyMeasurable hu).pow 2).mul
      hg.aestronglyMeasurable
  · exact hg.const_mul (C^2)
  · intro n
    exact Eventually.of_forall fun x => by
      rw [norm_mul,Real.norm_of_nonneg (hgn x),norm_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hbd n _) 2) (hgn x)
  · exact Eventually.of_forall fun x => by
      simpa only [ite_pow,one_pow,zero_pow (by decide : 2 ≠ 0),ite_mul,one_mul,zero_mul] using
        ((cutoff_deriv_tendsto (u x)).pow 2).mul tendsto_const_nhds
end StrictHotSpots.Nodal
end BoundarySignLimitsCombinedLayer


end

end DouglasLipschitzBase

end OAI
end

section
-- module Solutions.OAIQ3_Hot.HotSpots_Multiplicity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section ActualInteriorBoundarySign

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace ENNReal
namespace StrictHotSpots.InteriorBoundarySign
open StrictHotSpots.BoundarySign
variable {Ω : Set Plane} {u : Plane → ℝ}
lemma gap_test (ho : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0)
    {lam : ℝ} (hg : ∀ v : H10 ho, lam * ‖H10.value ho v‖^2 ≤ ‖H10.grad ho v‖^2)
    (n : ℕ) :
    lam * (∫ x in Ω, (Nodal.cutoff n (u x))^2) ≤
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
  let f := test_interior ho hu.1 hc hbound hb n
  have hh := hg (smoothTestToH10 ho f)
  change lam * ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).1.toLp f.val‖^2 ≤
    ‖(HasH1Gradient.test ho f.property.1 f.property.2.1).2.1.toLp (gradient f.val)‖^2 at hh
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    L2Inner.toLp_pair,L2Inner.toLp_pair] at hh
  have hval : (∫ x in Ω, inner ℝ (f.val x) (f.val x)) = ∫ x in Ω, (Nodal.cutoff n (u x))^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test_interior,cut,indicator_of_mem hx,RCLike.inner_apply,conj_trivial,pow_two]
  have hgrad : (∫ x in Ω, inner ℝ (gradient f.val x) (gradient f.val x)) =
      ∫ x in Ω, (deriv (Nodal.cutoff n) (u x))^2 * ‖gradient u x‖^2 := by
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    dsimp only
    rw [real_inner_self_eq_norm_sq]
    change ‖gradient (cut Ω u n) x‖^2 = _
    rw [cut_gradient_interior ho hu.1 n hx,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
  rwa [hval,hgrad] at hh

lemma equation_test (ho : IsOpen Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hbound : Bornology.IsBounded Ω) (hb : ∀ x ∈ frontier Ω, u x ≤ 0) (n : ℕ) :
    (∫ x in Ω, deriv (Nodal.cutoff n) (u x) * ‖gradient u x‖^2) =
      firstPositiveNeumannValue Ω * (∫ x in Ω, u x * Nodal.cutoff n (u x)) := by
  let f := test_interior ho hu.1 hc hbound hb n
  have hh := hu.2.2.2 f.val (gradient f.val) (HasH1Gradient.test ho f.property.1 f.property.2.1)
  convert hh using 1
  · apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    change _ = inner ℝ (gradient u x) (gradient (cut Ω u n) x)
    rw [cut_gradient_interior ho hu.1 n hx,inner_smul_right,real_inner_self_eq_norm_sq]
  · congr 1
    apply setIntegral_congr_fun ho.measurableSet
    intro x hx
    simp only [f,test_interior,cut,indicator_of_mem hx]
lemma positivePart_square (t : ℝ) : (if 0 < t then t^2 else 0) = (max t 0)^2 := by
  by_cases h : 0 < t
  · rw [ite_eq_left h,max_eq_left h.le]
  · rw [ite_eq_right h,max_eq_right (le_of_not_gt h),zero_pow (by decide : 2 ≠ 0)]
lemma positivePart_memLp (hu : MemLp u 2 (volume.restrict Ω)) :
    MemLp (fun x => max (u x) 0) 2 (volume.restrict Ω) := by
  apply hu.mono (((continuous_id.max continuous_const : Continuous (fun t : ℝ => max t 0))).comp_aestronglyMeasurable hu.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖max (u x) 0‖ ≤ ‖u x‖
    by_cases h : 0 ≤ u x
    · rw [max_eq_left h]
    · rw [max_eq_right (le_of_not_ge h),norm_zero]
      exact norm_nonneg _




lemma nonpos_of_boundary_nonpos (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hbound : Bornology.IsBounded Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) : ∀ x ∈ Ω, u x ≤ 0 := by
  obtain ⟨lam,_hl,hgap,hDir⟩ := H10.subcritical ho hne hbound
  let M := ∫ x in Ω, if 0 < u x then (u x)^2 else 0
  let E := ∫ x in Ω, if 0 < u x then ‖gradient u x‖^2 else 0
  have hIg : Integrable (fun x => ‖gradient u x‖^2) (volume.restrict Ω) :=
    hu.2.1.2.1.integrable_norm_pow (by norm_num)
  have hM := Nodal.cutoff_square_integral hu.2.1.1
  have hE := Nodal.cutoff_deriv_square_integral hu.2.1.1.aestronglyMeasurable hIg (fun x => sq_nonneg _)
  have hi : lam * M ≤ E := le_of_tendsto_of_tendsto
    (hM.const_mul lam) hE (Eventually.of_forall (gap_test ho hu hc hbound hb hDir))
  have hD := Nodal.cutoff_deriv_integral hu.2.1.1.aestronglyMeasurable hIg (fun x => sq_nonneg _)
  have hP := Nodal.cutoff_product_integral hu.2.1.1
  have he : E = firstPositiveNeumannValue Ω * M := by
    apply tendsto_nhds_unique hD
    apply (hP.const_mul (firstPositiveNeumannValue Ω)).congr
    intro n
    exact (equation_test ho hu hc hbound hb n).symm
  have hMn : 0 ≤ M := integral_nonneg fun x => by split_ifs <;> positivity
  have hMz : M = 0 := by nlinarith
  have hMz' : (∫ x in Ω, (max (u x) 0)^2) = 0 := by
    simpa only [M,positivePart_square] using hMz
  have hz := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (positivePart_memLp hu.2.1.1).integrable_sq).mp hMz'
  have hae : (fun x => max (u x) 0) =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hz] with x hx
    exact eq_zero_of_pow_eq_zero hx
  have hall := Measure.eqOn_open_of_ae_eq hae ho
    ((continuous_id.max continuous_const : Continuous (fun t : ℝ => max t 0)).comp_continuousOn
      hu.1.continuousOn) continuousOn_const
  intro x hx
  exact (le_max_left (u x) 0).trans (le_of_eq (hall hx))

lemma zero_of_boundary_nonpos (ho : IsOpen Ω) (hne : Ω.Nonempty)
    (hbound : Bornology.IsBounded Ω) (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω))
    (hb : ∀ x ∈ frontier Ω, u x ≤ 0) : ∀ x ∈ Ω, u x = 0 := by
  let : IsFiniteMeasure (volume.restrict Ω) := isFiniteMeasure_restrict.mpr hbound.measure_lt_top.ne
  have hnp := nonpos_of_boundary_nonpos ho hne hbound hu hc hb
  have hn : 0 ≤ᵐ[volume.restrict Ω] -u := by
    filter_upwards [ae_restrict_mem ho.measurableSet] with x hx
    simpa only [Pi.neg_apply,Pi.zero_apply,neg_nonneg] using hnp x hx
  have hm : (∫ x in Ω, (-u) x) = 0 := by
    simp only [Pi.neg_apply,integral_neg,hu.2.2.1,neg_zero]
  have hz := (integral_eq_zero_iff_of_nonneg_ae hn (hu.2.1.1.neg.integrable (by norm_num))).mp hm
  have hae : u =ᵐ[volume.restrict Ω] 0 := by
    filter_upwards [hz] with x hx
    simpa only [Pi.neg_apply,Pi.zero_apply,neg_eq_zero] using hx
  exact fun x hx => Measure.eqOn_open_of_ae_eq hae ho
    hu.1.continuousOn continuousOn_const hx

lemma exists_boundary_pos_oai (ho : IsOpen Ω) (hbound : Bornology.IsBounded Ω)
    (hu : InInteriorNeumannEigenspace Ω u) (hc : ContinuousOn u (closure Ω)) (hne : ∃ x ∈ Ω, u x ≠ 0) :
    ∃ x ∈ frontier Ω, 0 < u x := by
  by_contra hn
  push Not at hn
  obtain ⟨x,hx,hux⟩ := hne
  exact hux (zero_of_boundary_nonpos ho ⟨x,hx⟩ hbound hu hc hn x hx)

end StrictHotSpots.InteriorBoundarySign
end
end ActualInteriorBoundarySign


end OAI
end

theorem solution : type_of% @OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos_oai := @OAI.StrictHotSpots.InteriorBoundarySign.exists_boundary_pos_oai
