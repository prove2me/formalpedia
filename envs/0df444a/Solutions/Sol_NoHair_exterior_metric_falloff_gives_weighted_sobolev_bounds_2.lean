-- Prove2me | solution 2 for NoHair.exterior_metric_falloff_gives_weighted_sobolev_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-23T12:56:50.083308+00:00
-- url     : https://prove2.me/submissions/a829078a-d431-4709-ab70-1651870fd9ca

import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Definitions.Def_NoHair_staticReflectionAndCap
import Definitions.Def_NoHair_staticInvertedEndMetric

open NoHair Set Filter Metric
open scoped Topology ContDiff
open MeasureTheory

noncomputable section

private abbrev X := ADMPoint

private lemma bound_at {r D C : ℝ} {k:ℕ} (hr:1<r) (non:0≤D) (cp:0<C)
    (h:D≤C/r^(k+1)) : (1+r^2)^k/(1+r^2)*D^2 ≤ (2^(k+1)*C^2)/((1+r^2)^2) := by
  have rp := zero_lt_one.trans hr
  have wpos : 0<1+r^2 := by positivity
  have ww : 1+r^2 ≤ 2*r^2 := by nlinarith only [hr, sq_nonneg (r-1)]
  apply (le_div_iff₀ (sq_pos_of_pos wpos)).mpr
  calc (1+r^2)^k/(1+r^2)*D^2*(1+r^2)^2 = (1+r^2)^(k+1)*D^2 := by
          rw [pow_succ (1+r^2) k]; field_simp <;> ring
       _ ≤ (2*r^2)^(k+1)*(C/r^(k+1))^2 := by gcongr
       _ = 2^(k+1)*C^2 := by
          have e : (r^2)^(k+1)=(r^(k+1))^2 := by rw [←pow_mul,←pow_mul,Nat.mul_comm 2 (k+1)]
          rw [mul_pow,e,div_pow]
          field_simp

theorem solution (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (B : ℝ) (s : ℕ)
    (smooth : ∀ x : ADMPoint, B < ‖x‖ → ∀ i j, ContDiffAt ℝ ∞ (fun z => h z i j) x)
    (falloff : ∀ k : ℕ, ∃ L C : ℝ, 0 < L ∧ 0 < C ∧ ∀ x : ADMPoint, L < ‖x‖ → ∀ i j,
       ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖ ≤ C/‖x‖^(k+1)) :
    ∃ R : ℝ, max B 1 ≤ R ∧ ∀ k : ℕ, k ≤ s → ∀ i j : Fin 3, IntegrableOn
      (fun x : ADMPoint => ((1+‖x‖^2)^k/(1+‖x‖^2))*
        ‖iteratedFDeriv ℝ k (fun z => h z i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j) x‖^2)
      {x : ADMPoint | R < ‖x‖} := by
  classical
  choose L C lp cp bounds using falloff
  let T := max B 1 + ∑ m:Fin (s+1), |L m.val|
  have big : max B 1 ≤ T := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have allk (k:ℕ) (hk : k ≤ s) : L k ≤ T := by
    let m : Fin (s+1) := ⟨k,Nat.lt_succ_of_le hk⟩
    have d := Finset.single_le_sum (fun j _ => abs_nonneg (L (j:Fin (s+1)).val)) (Finset.mem_univ m)
    dsimp only [T]; linarith only [show |L k| ≤ ∑ i:Fin (s+1), |L i.val| from d,le_abs_self (L k),le_max_right B 1]
  refine ⟨T,big,?_⟩
  intro k hk i j
  let U := {x:X | T<‖x‖}
  have op : IsOpen U := isOpen_lt continuous_const continuous_norm
  let v := fun x:X => h x i j-(1:Matrix (Fin 3) (Fin 3) ℝ) i j
  let g := fun x:X => ((1+‖x‖^2)^k/(1+‖x‖^2))*‖iteratedFDeriv ℝ k v x‖^2
  have cg : ContinuousOn g U := by
    intro x hx
    have af := smooth x (((le_max_left B 1).trans big).trans_lt hx) i j
    have sv : ContDiffAt ℝ ∞ v x := af.sub contDiffAt_const
    have dc := sv.continuousAt_iteratedFDeriv (show (k:ℕ∞ω)≤∞ from WithTop.coe_le_coe.mpr (le_top : (k:ℕ∞)≤⊤))
    have nc : ContinuousAt (fun z:X => 1+‖z‖^2) x := by fun_prop
    exact (((nc.pow k).div nc (by positivity)).mul (dc.norm.pow 2)).continuousWithinAt
  have model : Integrable (fun x:X => ((1+‖x‖^2)^2)⁻¹) := by
    have v₀ := integrable_rpow_neg_one_add_norm_sq (μ:=volume) (by norm_num : (Module.finrank ℝ X : ℝ)<4)
    apply v₀.congr (Filter.Eventually.of_forall fun x => ?_)
    change (1+‖x‖^2)^(-(4:ℝ)/2) = ((1+‖x‖^2)^2)⁻¹
    rw [show -(4:ℝ)/2 = -(2:ℝ) by norm_num,Real.rpow_neg (by positivity : 0 ≤ 1+‖x‖^2)]
    norm_cast
  apply ((model.const_mul (2^(k+1)*(C k)^2)).integrableOn).mono' (cg.aestronglyMeasurable op.measurableSet)
  filter_upwards [ae_restrict_mem (μ:=volume) op.measurableSet] with x hx
  have hr := ((le_max_right B 1).trans big).trans_lt (show T<‖x‖ from hx)
  have est := bounds k x ((allk k hk).trans_lt hx) i j
  change ‖((1+‖x‖^2)^k/(1+‖x‖^2))*‖iteratedFDeriv ℝ k v x‖^2‖ ≤ _
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤((1+‖x‖^2)^k/(1+‖x‖^2))*‖iteratedFDeriv ℝ k v x‖^2),←div_eq_mul_inv]
  exact bound_at hr (norm_nonneg _) (cp k) est
