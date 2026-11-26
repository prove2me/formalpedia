-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_coupled_drift_density
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:49:14.019821+00:00
-- url     : https://prove2.me/submissions/7332f5b5-87f4-4cee-97dc-22573aa50a95

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_coupling_transfers_weighted_path_lipschitz_bounds
import Theorems.Thm_ManyServerQED_Scheduling_weighted_lipschitz_path_has_measurable_drift_density
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 2600000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s) :
    let m := k+k+k+2
    let A (z : Fin m → ℝ) (i : Fin k) := z (Fin.castAdd 2 (Fin.natAdd (k+k) i))
    let R (z : Fin m → ℝ) := 1+∑ i : Fin k, |z (Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i)))|
    ∃ a > (0:ℝ), ∃ b : d.Ω' → ℝ → Fin k → ℝ,
      Measurable (fun z : d.Ω' × ℝ => b z.1 z.2) ∧
      (∀ ω t, ‖b ω t‖ ≤ a*R (d.limit ω (t.toNNReal:ℝ))) ∧
      (∀ᵐ ω ∂d.Q, ∀ T : ℝ≥0, (∫ s in (0:ℝ)..(T:ℝ), b ω s) =
        d.driftIntegral T ω-d.driftIntegral 0 ω) ∧
      ∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
        (∀ u ∈ Icc s t, a*R (d.row n ω u) ≤ C) →
        ‖A (d.row n ω t)-A (d.row n ω s)‖ ≤ C*(t-s) := by
  intro m A R
  classical
  let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
  let ix (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i))
  let ia (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.natAdd (k+k) i)
  have hA : Continuous A := continuous_pi (fun i => continuous_apply (ia i))
  have hR : Continuous R := continuous_const.add
    (continuous_finsetSum _ (fun i _ => (continuous_apply (ix i)).abs))
  have hRn (z : Fin m → ℝ) : 0 ≤ R z := by
    have hS : 0 ≤ ∑ i, |z (ix i)| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    dsimp [R,ix] at *
    linarith
  obtain ⟨_,_,_,_,⟨a,ha,hLinear⟩,_⟩ :=
    queue_hjb_integrands_on_bounded_state_sets M.diffData Lt γ ϱ mL hA2 f hH
  have hRR (x y : Fin m → ℝ) : |a*R x-a*R y| ≤ a*∑ i, |x i-y i| := by
    rw [← mul_sub,abs_mul,abs_of_nonneg ha.le]
    apply mul_le_mul_of_nonneg_left _ ha.le
    dsimp [R]
    rw [add_sub_add_left_eq_sub,← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
      (fun i _ => abs_abs_sub_abs_le_abs_sub (x (ix i)) (y (ix i)))).trans ?_)
    have hInject : Function.Injective ix :=
      (Fin.castAdd_injective (k+k+k) 2).comp
        ((Fin.castAdd_injective (k+k) k).comp (Fin.castAdd_injective k k))
    calc
      ∑ i, |x (ix i)-y (ix i)| = ∑ j ∈ Finset.univ.image ix, |x j-y j| :=
        (Finset.sum_image (s := Finset.univ) (f := fun j => |x j-y j|) hInject.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => abs_nonneg _)
  have hInt := (queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hH X Ψ X0 hC hWork).1
  have hCad := queue_hjb_observation_rows_are_cadlag M Lt γ ϱ mL hA2 u0 hu0 f hH X Ψ X0 hC hWork
  have hOrig : ∀ᶠ n in atTop, ∀ ω,
      (∀ t, 0 ≤ t → ContinuousWithinAt (Z n ω) (Ici t) t) ∧
      ∀ s t C, 0 ≤ s → s ≤ t → (∀ u ∈ Icc s t, a*R (Z n ω u) ≤ C) →
        ‖A (Z n ω t)-A (Z n ω s)‖ ≤ C*(t-s) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    intro ω
    refine ⟨fun t ht => continuousWithinAt_pi.2 (fun i => (hCad n hn ω i).1 t ht),?_⟩
    intro s t C hs hst hB
    have hC0 : 0 ≤ C := (mul_nonneg ha.le (hRn _)).trans (hB s ⟨le_rfl,hst⟩)
    have ht := hs.trans hst
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC0 (sub_nonneg.2 hst))).2
    intro i
    let v (t : ℝ) := drift M.diffData (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t) i
    have hIt := (hInt n hn ω).2.2.2.2.2.2.1
    have hU := (hInt n hn ω).2.2.2.2.2.2.2
    have hsI : IntervalIntegrable v volume 0 s := (hIt s hs).1 i
    have htI : IntervalIntegrable v volume 0 t := (hIt t ht).1 i
    have hEq (r : ℝ) : A (Z n ω r) i = ∫ u in (0:ℝ)..r,v u := by
      simp only [A,Z,queueHJBObservation,Fin.append_left,Fin.append_right,v]
    rw [Pi.sub_apply,hEq,hEq,← intervalIntegral.integral_add_adjacent_intervals hsI
      (hsI.symm.trans htI),add_sub_cancel_left]
    have hNorm := intervalIntegral.norm_integral_le_of_norm_le_const (C := C)
      (a := s) (b := t) (f := v) (fun r hr => by
        have hr' : r ∈ Ioc s t := uIoc_of_le hst ▸ hr
        have h0 := hs.trans hr'.1.le
        rw [Real.norm_eq_abs]
        refine (hLinear _ _ (hU r h0) i).trans ?_
        simpa only [R,Z,queueHJBObservation,Fin.append_left,l1norm] using hB r ⟨hr'.1.le,hr'.2⟩)
    simpa only [abs_of_nonneg (sub_nonneg.2 hst)] using hNorm
  obtain ⟨hRows,hLim⟩ := coupling_transfers_weighted_path_lipschitz_bounds d hs A hA
    (fun z => a*R z) (hR.const_mul _) (fun z => mul_nonneg ha.le (hRn z)) a ha.le hRR hOrig
  let S : Set d.Ω' := {ω | ∀ s t C, 0 ≤ s → s ≤ t →
    (∀ u ∈ Icc s t, a*R (d.limit ω u) ≤ C) →
      ‖A (d.limit ω t)-A (d.limit ω s)‖ ≤ C*(t-s)}
  obtain ⟨N,hN,hNm,hNz⟩ := exists_measurable_superset_of_null (μ := d.Q)
    (show d.Q Sᶜ = 0 from ae_iff.1 hLim)
  have hAe : ∀ᵐ ω ∂d.Q, ω ∉ N := by
    apply ae_iff.2
    have he : {ω : d.Ω' | ¬ω ∉ N} = N := by
      ext w
      exact not_not
    rw [he,hNz]
  let val (ω : d.Ω') (t : ℝ) := d.limit ω (t.toNNReal:ℝ)
  have hv (ω : d.Ω') : Continuous (val ω) :=
    (d.limit_cont ω).comp_continuous
      ((continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t:ℝ))).comp continuous_real_toNNReal)
      (fun t => t.toNNReal.2)
  have hm : Measurable (Function.uncurry val) := by
    have hh := measurable_uncurry_of_continuous_of_measurable (u := fun t ω => val ω t)
      hv (fun t => d.limit_meas t.toNNReal)
    exact hh.comp measurable_swap
  let v (ω : d.Ω') (t : ℝ) := if ω ∈ N then 0 else A (val ω t)
  let r (ω : d.Ω') (t : ℝ) := a*R (val ω t)
  have hVm : Measurable (fun z : d.Ω' × ℝ => v z.1 z.2) :=
    Measurable.ite (hNm.preimage measurable_fst) measurable_const (hA.measurable.comp hm)
  have hRm : Measurable (fun z : d.Ω' × ℝ => r z.1 z.2) := (hR.measurable.comp hm).const_mul _
  have hRc (ω : d.Ω') : Continuous (r ω) := (hR.comp (hv ω)).const_mul _
  have hNonneg (ω : d.Ω') (t : ℝ) : 0 ≤ r ω t := mul_nonneg ha.le (hRn _)
  have hBound (ω : d.Ω') (s t C : ℝ) (hs : 0 ≤ s) (ht : 0 ≤ t)
      (hC : ∀ u ∈ uIcc s t, r ω u ≤ C) :
      ‖v ω t-v ω s‖ ≤ C*|t-s| := by
    have hC0 : 0 ≤ C := (hNonneg _ _).trans (hC s left_mem_uIcc)
    by_cases h : ω ∈ N
    · simp only [v,if_pos h,sub_self,norm_zero]
      positivity
    · have hh : ω ∈ S := notMem_compl_iff.1 (fun h' => h (hN h'))
      simp only [v,if_neg h,val,Real.coe_toNNReal _ hs,Real.coe_toNNReal _ ht]
      rcases le_total s t with hst | hst
      · rw [abs_of_nonneg (sub_nonneg.2 hst)]
        exact hh s t C hs hst (fun u hu => by
          simpa only [r,val,Real.coe_toNNReal _ (hs.trans hu.1)] using hC u ((uIcc_of_le hst).symm ▸ hu))
      · rw [← norm_sub_rev,abs_of_nonpos (sub_nonpos.2 hst),neg_sub]
        exact hh t s C ht hst (fun u hu => by
          simpa only [r,val,Real.coe_toNNReal _ (ht.trans hu.1)] using
            hC u (uIcc_comm t s ▸ ((uIcc_of_le hst).symm ▸ hu)))
  obtain ⟨b,hBm,hB,hEq⟩ :=
    weighted_lipschitz_path_has_measurable_drift_density v r hVm hRm hRc hNonneg hBound
  refine ⟨a,ha,b,hBm,hB,?_,hRows⟩
  filter_upwards [hAe] with ω hω
  intro T
  change (∫ s in (0:ℝ)..(T:ℝ), b ω s) = A (d.limit ω T)-A (d.limit ω 0)
  simpa only [v,if_neg hω,val,Real.toNNReal_coe,Real.toNNReal_zero,NNReal.coe_zero] using hEq ω T T.2
