-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_gap_identity_on_coupled_limit
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:51:53.945608+00:00
-- url     : https://prove2.me/submissions/82672aae-9b07-45b7-8d6e-b8eb3fffa5be

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_observation_rows_are_cadlag
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_integrands_on_bounded_state_sets
import Theorems.Thm_ManyServerQED_Scheduling_right_endpoint_stieltjes_sums_for_cadlag_weight
import Theorems.Thm_ManyServerQED_Scheduling_stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
open Filter Topology Set MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem cadlag_compact_bounds (f : ℝ → ℝ) (hf : IsCadlag f) (T : ℝ) :
    ∃ C ≥ (0:ℝ), ∀ t ∈ Set.Icc (0:ℝ) T, |f t| ≤ C := by
  have hl (s : ℝ) (hs : s ∈ Icc (0:ℝ) T) :
      ∃ r > (0:ℝ), ∃ C ≥ (0:ℝ), ∀ t ∈ Metric.ball s r ∩ Icc (0:ℝ) T, |f t| ≤ C := by
    obtain ⟨r,hr,hright⟩ := Metric.continuousWithinAt_iff.1 (hf.1 s hs.1) 1 zero_lt_one
    rcases hs.1.eq_or_lt with h | h
    · refine ⟨r,hr,|f s|+1,by positivity,?_⟩
      intro t ht
      have hts : s ≤ t := h ▸ ht.2.1
      have hft := hright hts ht.1
      rw [Real.dist_eq] at hft
      have w := abs_add_le (f t-f s) (f s)
      rw [sub_add_cancel] at w
      linarith
    · obtain ⟨u,hu⟩ := hf.2 s h
      have hleft := (Metric.tendsto_nhdsWithin_nhds.1 hu) 1 zero_lt_one
      obtain ⟨q,hq,hq'⟩ := hleft
      refine ⟨min r q,lt_min hr hq,max |f s| |u|+1,by positivity,?_⟩
      intro t ht
      have ht' : dist t s < min r q := ht.1
      rcases le_or_gt s t with hst | hst
      · have hft := hright hst (lt_min_iff.1 ht').1
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-f s) (f s)
        rw [sub_add_cancel] at w
        linarith [le_max_left |f s| |u|]
      · have hft := hq' hst (lt_min_iff.1 ht').2
        rw [Real.dist_eq] at hft
        have w := abs_add_le (f t-u) u
        rw [sub_add_cancel] at w
        linarith [le_max_right |f s| |u|]
  choose r hr C hC h using fun s : Icc (0:ℝ) T => hl s s.2
  obtain ⟨S,hS⟩ := (isCompact_Icc : IsCompact (Icc (0:ℝ) T)).elim_finite_subcover
    (fun s : Icc (0:ℝ) T => Metric.ball (s:ℝ) (r s))
    (fun _ => Metric.isOpen_ball) (by
      intro s hs
      exact mem_iUnion.2 ⟨⟨s,hs⟩,Metric.mem_ball_self (hr ⟨s,hs⟩)⟩)
  refine ⟨∑ s ∈ S,C s,Finset.sum_nonneg (fun s _ => hC s),?_⟩
  intro t ht
  obtain ⟨s,hs,hst⟩ := mem_iUnion₂.1 (hS ht)
  exact (h s t ⟨hst,ht⟩).trans (Finset.single_le_sum (fun s _ => hC s) hs)

private theorem right_continuousOn_aestronglyMeasurable (T : ℝ) (hT : 0 ≤ T)
    (v : ℝ → ℝ) (hv : ∀ t ∈ Icc (0:ℝ) T, ContinuousWithinAt v (Ici t) t) :
    AEStronglyMeasurable v (volume.restrict (Icc (0:ℝ) T)) := by
  let f (t : ℝ≥0) (_ : Unit) := v (min (t:ℝ) T)
  have hf (t : ℝ≥0) : Measurable (f t) := measurable_const
  have hr (ω : Unit) (t : ℝ≥0) : ContinuousWithinAt (fun s : ℝ≥0 => f s ω) (Ici t) t := by
    by_cases h : (t:ℝ) ≤ T
    · have he : min (t:ℝ) T = t := min_eq_left h
      let g (s : ℝ≥0) := min (s:ℝ) T
      have hg : Continuous g := continuous_subtype_val.min continuous_const
      have hm : MapsTo g (Ici t) (Ici (min (t:ℝ) T)) :=
        fun s hs => min_le_min_right T (by exact_mod_cast (show t ≤ s from hs))
      have hv' : ContinuousWithinAt v (Ici (g t)) (g t) := by
        dsimp [g]
        rw [he]
        exact hv t ⟨t.2,h⟩
      exact hv'.comp hg.continuousWithinAt hm
    · have hc : ContinuousWithinAt (fun _ : ℝ≥0 => v T) (Ici t) t := continuousWithinAt_const
      apply hc.congr
      · intro s hs
        have hs' : T ≤ (s:ℝ) :=
          (le_of_not_ge h).trans (by exact_mod_cast (show t ≤ s from hs))
        simp only [f,min_eq_right hs']
      · simp only [f,min_eq_right (le_of_not_ge h)]
  have hm := AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation f hf hr
  let inc (t : ℝ) : ℝ≥0 × Unit := (t.toNNReal,())
  have hinc : Measurable inc := measurable_id.real_toNNReal.prodMk measurable_const
  have hu : Measurable (fun t : ℝ => v (min (t.toNNReal:ℝ) T)) := hm.comp hinc
  refine hu.aestronglyMeasurable.congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  change v (min (t.toNNReal:ℝ) T) = v t
  rw [Real.coe_toNNReal _ ht.1,min_eq_left ht.2]

private noncomputable def rightGrid (T : ℝ) (w A : ℝ → ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m+1), w (T*(j+1:ℕ)/(m+1:ℕ)) *
    (A (T*(j+1:ℕ)/(m+1:ℕ))-A (T*j/(m+1:ℕ)))

private theorem bounded_aestronglyMeasurable_intervalIntegrable (T : ℝ) (hT : 0 ≤ T)
    (v : ℝ → ℝ) (C : ℝ)
    (hm : AEStronglyMeasurable v (volume.restrict (Icc (0:ℝ) T)))
    (hB : ∀ t ∈ Icc (0:ℝ) T, |v t| ≤ C) : IntervalIntegrable v volume 0 T := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT enorm_ne_top]
  letI : IsFiniteMeasure (volume.restrict (Icc (0:ℝ) T)) :=
    isFiniteMeasure_restrict.2 (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
  refine ⟨hm,HasFiniteIntegral.of_bounded (C := C) ?_⟩
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simpa only [Real.norm_eq_abs] using hB t ht

private theorem continuous_function_compact_state_bound {m : ℕ}
    (F : ℝ → (Fin m → ℝ) → ℝ) (hF : Continuous (Function.uncurry F)) (T B : ℝ) :
    ∃ C ≥ (0:ℝ), ∀ t ∈ Icc (0:ℝ) T, ∀ z, ‖z‖ ≤ B → |F t z| ≤ C := by
  let S := Set.prod (Icc (0:ℝ) T) (Metric.closedBall (0:Fin m → ℝ) B)
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨A,hA⟩ := (hS.image hF.abs).bddAbove
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro t ht z hz
  exact (hA ⟨(t,z),⟨ht,by simpa only [Metric.mem_closedBall,dist_zero_right]⟩,rfl⟩).trans (le_max_left _ _)

private theorem continuous_joint_function_preserves_local_uniform_limit {m : ℕ}
    (F : ℝ → (Fin m → ℝ) → ℝ) (hF : Continuous (Function.uncurry F))
    (T : ℝ) (Y : ℕ → ℝ → Fin m → ℝ) (Z : ℝ → Fin m → ℝ) (B : ℝ)
    (hB : ∀ t ∈ Icc (0:ℝ) T, ‖Z t‖ ≤ B)
    (hU : Tendsto (fun n => supDist (Y n) Z T) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T,
      |F t (Y n t)-F t (Z t)| < ε := by
  intro ε hε
  let S := Set.prod (Icc (0:ℝ) T) (Metric.closedBall (0:Fin m → ℝ) (B+1))
  have hS : IsCompact S := isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨δ,hδ,hδ'⟩ := Metric.uniformContinuousOn_iff.1
    (hS.uniformContinuousOn_of_continuous hF.continuousOn) ε hε
  have hδ0 : 0 < min δ 1 := lt_min hδ zero_lt_one
  filter_upwards [(tendsto_order.1 hU).2 _ (ENNReal.ofReal_pos.2 hδ0)] with n hn
  intro t ht
  have hNN : ‖Y n t-Z t‖ < min δ 1 := by
    have hSum : ∑ i, |Y n t i-Z t i| < min δ 1 :=
      (ENNReal.ofReal_lt_ofReal_iff hδ0).1 ((le_iSup₂_of_le t ht le_rfl).trans_lt hn)
    refine lt_of_le_of_lt ?_ hSum
    apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).2
    intro i
    rw [Pi.sub_apply,Real.norm_eq_abs]
    exact Finset.single_le_sum (f := fun i => |Y n t i-Z t i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
  have hY : ‖Y n t‖ ≤ B+1 := by
    have hA := norm_add_le (Y n t-Z t) (Z t)
    rw [sub_add_cancel] at hA
    linarith [hB t ht,hNN.trans_le (min_le_right δ 1)]
  have hZ : ‖Z t‖ ≤ B+1 := by linarith [hB t ht]
  have hD : dist (t,Y n t) (t,Z t) < δ := by
    rw [Prod.dist_eq,dist_self,max_eq_right dist_nonneg,dist_eq_norm]
    exact hNN.trans_le (min_le_left _ _)
  have h1 : (t,Y n t) ∈ S := ⟨ht,by simpa only [Metric.mem_closedBall,dist_zero_right] using hY⟩
  have h2 : (t,Z t) ∈ S := ⟨ht,by simpa only [Metric.mem_closedBall,dist_zero_right] using hZ⟩
  simpa only [Real.dist_eq,Function.uncurry] using hδ' _ h1 _ h2 hD

set_option maxHeartbeats 4400000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (γ ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (f : (Fin k → ℝ) → ℝ) (hH : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ) (X0 : ℕ → Fin k → ℕ)
    (hC : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ) s)
    (a : ℝ) (ha : 0 < a) (b : d.Ω' → ℝ → Fin k → ℝ)
    (hBm : Measurable (fun z : d.Ω' × ℝ => b z.1 z.2))
    (hB : ∀ ω t, ‖b ω t‖ ≤ a*(1+l1norm (d.state t.toNNReal ω)))
    (hPrim : ∀ᵐ ω ∂d.Q, ∀ T : ℝ≥0,
      (∫ s in (0:ℝ)..(T:ℝ), b ω s) = d.driftIntegral T ω-d.driftIntegral 0 ω)
    (hRows : ∀ᵐ ω ∂d.Q, ∀ᶠ n in atTop, ∀ s t C, 0 ≤ s → s ≤ t →
      (∀ u ∈ Icc s t, a*(1+∑ i : Fin k,
        |d.row n ω u (Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i)))|) ≤ C) →
      ‖(fun i : Fin k => d.row n ω t (Fin.castAdd 2 (Fin.natAdd (k+k) i))) -
        (fun i : Fin k => d.row n ω s (Fin.castAdd 2 (Fin.natAdd (k+k) i)))‖ ≤ C*(t-s)) :
    ∀ᵐ ω ∂d.Q, ∀ t : ℝ≥0, d.gap t ω = d.runningCost t ω +
        ∫ r in (0:ℝ)..(t:ℝ), Real.exp (-γ*r) *
          ((∑ i, b ω r i * grad f (d.state r.toNNReal ω) i) -
            hamiltonian M.diffData (costOfTilde Lt) (d.state r.toNNReal ω)
              (grad f (d.state r.toNNReal ω))) := by
  classical
  let m := k+k+k+2
  let E := Fin m → ℝ
  let L := costOfTilde Lt
  let D := M.diffData
  let Z := queueHJBObservation M L γ u0 f X Ψ
  let ix (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i))
  let ia (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.natAdd (k+k) i)
  let ic : Fin m := Fin.natAdd (k+k+k) (0:Fin 2)
  let ig : Fin m := Fin.natAdd (k+k+k) (1:Fin 2)
  let state (z : E) (i : Fin k) := z (ix i)
  let p (z : E) (i : Fin k) := z (ia i)
  let w (i : Fin k) (t : ℝ) (z : E) := Real.exp (-γ*t)*grad f (state z) i
  let H (t : ℝ) (z : E) := Real.exp (-γ*t)*hamiltonian D L (state z) (grad f (state z))
  have hcS : Continuous state := continuous_pi (fun i => continuous_apply (ix i))
  have hcGrad : Continuous (grad f) := by
    apply continuous_pi
    intro i
    exact (hH.1.continuous_fderiv two_ne_zero).clm_apply continuous_const
  have hcHam : Continuous (fun z => hamiltonian D L z (grad f z)) := by
    have he (z : Fin k → ℝ) :
        hamiltonian D L z (grad f z) = γ*f z -
          (1/2)*∑ i, D.r i^2 * iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1) := by
      linarith only [hH.2 z]
    simp_rw [he]
    have hD2 : Continuous (fderiv ℝ (fderiv ℝ f)) :=
      (hH.1.fderiv_right (m := 1) (by norm_num)).continuous_fderiv one_ne_zero
    have hT (i : Fin k) : Continuous (fun z => iteratedFDeriv ℝ 2 f z (fun _ => Pi.single i 1)) := by
      simp_rw [iteratedFDeriv_two_apply]
      exact (hD2.clm_apply continuous_const).clm_apply continuous_const
    exact (hH.1.continuous.const_mul _).sub
      ((continuous_finsetSum _ fun i _ => (hT i).const_mul (D.r i ^ 2)).const_mul _)
  have hExp : Continuous (fun t : ℝ => Real.exp (-γ*t)) := by fun_prop
  have hw (i : Fin k) : Continuous (Function.uncurry (w i)) :=
    (hExp.comp continuous_fst).mul ((continuous_apply i).comp (hcGrad.comp (hcS.comp continuous_snd)))
  have hHc : Continuous (Function.uncurry H) :=
    (hExp.comp continuous_fst).mul (hcHam.comp (hcS.comp continuous_snd))
  have hCad := queue_hjb_observation_rows_are_cadlag M Lt γ ϱ mL hA2 u0 hu0 f hH X Ψ X0 hC hWork
  have hInt := (queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hH X Ψ X0 hC hWork).1
  obtain ⟨_,_,_,_,⟨a₀,ha₀,hA₀⟩,_⟩ :=
    queue_hjb_integrands_on_bounded_state_sets D Lt γ ϱ mL hA2 f hH
  have meas_int (T : ℝ) (hT : 0 ≤ T) (P : ℝ → E)
      (hP : ∀ t, 0 ≤ t → ContinuousWithinAt P (Ici t) t)
      (F : ℝ → E → ℝ) (hF : Continuous (Function.uncurry F)) :
      AEStronglyMeasurable (fun t => F t (P t)) (volume.restrict (Icc 0 T)) :=
    right_continuousOn_aestronglyMeasurable T hT _ (fun t ht =>
      hF.continuousAt.comp_continuousWithinAt (continuousWithinAt_id.prodMk (hP t ht.1)))
  have rightW (T : ℝ) (P : ℝ → E)
      (hP : ∀ t, 0 ≤ t → ContinuousWithinAt P (Ici t) t)
      (F : ℝ → E → ℝ) (hF : Continuous (Function.uncurry F)) :
      ∀ t ∈ Icc (0:ℝ) T, ContinuousWithinAt (fun t => F t (P t)) (Ici t) t :=
    fun t ht => hF.continuousAt.comp_continuousWithinAt (continuousWithinAt_id.prodMk (hP t ht.1))
  have path_bound (P : ℝ → E) (hP : ∀ i, IsCadlag (fun t => P t i)) (T : ℝ) :
      ∃ B ≥ (0:ℝ), ∀ t ∈ Icc (0:ℝ) T, ‖P t‖ ≤ B := by
    choose B hBn hB using fun i => cadlag_compact_bounds (fun t => P t i) (hP i) T
    have hB0 : 0 ≤ ∑ i, B i := Finset.sum_nonneg (fun i _ => hBn i)
    refine ⟨∑ i, B i,hB0,fun t ht => (pi_norm_le_iff_of_nonneg hB0).2 (fun i => ?_)⟩
    rw [Real.norm_eq_abs]
    exact (hB i t ht).trans (Finset.single_le_sum (fun j _ => hBn j) (Finset.mem_univ i))
  let q (T : ℝ≥0) (m j : ℕ) := (T:ℝ)*j/(m+1:ℕ)
  have hq (T : ℝ≥0) (m j : ℕ) : 0 ≤ q T m j := by dsimp [q]; positivity
  let Grid (T : ℝ≥0) (v : ℝ≥0 → E) (m : ℕ) :=
    (∑ i, rightGrid T (fun t => w i t (v t.toNNReal)) (fun t => p (v t.toNNReal) i) m) -
      rightGrid T (fun t => H t (v t.toNNReal)) id m
  have hGrid (T : ℝ≥0) (m : ℕ) : Measurable (fun v => Grid T v m) := by
    apply Measurable.sub
    · apply Finset.measurable_sum
      intro i _
      unfold rightGrid
      apply Finset.measurable_sum
      intro j _
      let l := q T m j
      let r := q T m (j+1)
      have h1 : Measurable (fun v : ℝ≥0 → E => w i r (v r.toNNReal)) :=
        (hw i).measurable.comp (measurable_const.prodMk (measurable_pi_apply _))
      have h2 (t : ℝ) : Measurable (fun v : ℝ≥0 → E => p (v t.toNNReal) i) :=
        (measurable_pi_apply _).comp (measurable_pi_apply _)
      exact h1.mul ((h2 r).sub (h2 l))
    · unfold rightGrid
      apply Finset.measurable_sum
      intro j _
      exact ((hHc.measurable.comp (measurable_const.prodMk (measurable_pi_apply _)))).mul_const _
  have hGridEval (T : ℝ≥0) (m : ℕ) (P : ℝ → E) :
      Grid T (fun t : ℝ≥0 => P t) m =
        (∑ i, rightGrid T (fun t => w i t (P t)) (fun t => p (P t) i) m) -
        rightGrid T (fun t => H t (P t)) id m := by
    have he (j : ℕ) : ((q T m j).toNNReal:ℝ) = q T m j :=
      Real.coe_toNNReal _ (hq T m j)
    simp only [Grid,rightGrid,show ∀ j : ℕ, (((T:ℝ)*j/(m+1:ℕ)).toNNReal:ℝ) = (T:ℝ)*j/(m+1:ℕ) from he]
  let Mark (T : ℝ≥0) (v : ℝ≥0 → E) := v T ig-v T ic
  have hMark (T : ℝ≥0) : Measurable (Mark T) := by
    have hAt : Measurable (fun v : ℝ≥0 → E => v T) := measurable_pi_apply T
    exact ((measurable_pi_apply ig).comp hAt).sub ((measurable_pi_apply ic).comp hAt)
  have hBound_b (B : ℝ) (z : E) (hz : ‖z‖ ≤ B) : l1norm (state z) ≤ (k:ℝ)*B := by
    unfold l1norm
    calc
      ∑ i, |state z i| ≤ ∑ _ : Fin k, B := Finset.sum_le_sum (fun i _ => ?_)
      _ = (k:ℝ)*B := by simp
    · have h := norm_le_pi_norm z (ix i)
      rw [Real.norm_eq_abs] at h
      exact h.trans hz
  have hPre (T : ℝ≥0) (n : ℕ) (hn : 1 ≤ n) (ω : Ω) :
      Tendsto (fun m => Grid T (fun t : ℝ≥0 => Z n ω t) m) atTop
        (𝓝 (Mark T (fun t : ℝ≥0 => Z n ω t))) := by
    let P := Z n ω
    let β (t : ℝ) (i : Fin k) := drift D (M.Xhat n (X n) ω t)
      (uProc n u0 (X n) (Ψ n) ω t) i
    have hP (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt P (Ici t) t :=
      continuousWithinAt_pi.2 (fun i => (hCad n hn ω i).1 t ht)
    obtain ⟨B,hB0,hPbound⟩ := path_bound P (hCad n hn ω) T
    let C := a₀*(1+(k:ℝ)*B)
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hβ (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (i : Fin k) : |β t i| ≤ C := by
      have hu := (hInt n hn ω).2.2.2.2.2.2.2 t ht.1
      refine (hA₀ _ _ hu i).trans (mul_le_mul_of_nonneg_left ?_ ha₀.le)
      have hB := hBound_b B (P t) (hPbound t ht)
      simpa only [P,state,Z,ix,queueHJBObservation,Fin.append_left] using add_le_add_right hB 1
    have hβI (i : Fin k) : IntervalIntegrable (fun t => β t i) volume 0 T :=
      ((hInt n hn ω).2.2.2.2.2.2.1 T T.2).1 i
    have hwp (i : Fin k) :
        ∃ J ≥ (0:ℝ), ∀ t ∈ Icc (0:ℝ) T, |w i t (P t)| ≤ J := by
      obtain ⟨J,hJ,hJp⟩ := continuous_function_compact_state_bound (w i) (hw i) T B
      exact ⟨J,hJ,fun t ht => hJp t ht _ (hPbound t ht)⟩
    choose J hJ hJp using hwp
    obtain ⟨K,hK,hKp⟩ := continuous_function_compact_state_bound H hHc T B
    have hHInt : IntervalIntegrable (fun t => H t (P t)) volume 0 T :=
      bounded_aestronglyMeasurable_intervalIntegrable T T.2 _ K (meas_int T T.2 P hP H hHc)
        (fun t ht => hKp t ht _ (hPbound t ht))
    have hwi (i : Fin k) : IntervalIntegrable (fun t => w i t (P t)*β t i) volume 0 T := by
      apply bounded_aestronglyMeasurable_intervalIntegrable T T.2 _ (J i*C)
        ((meas_int T T.2 P hP (w i) (hw i)).mul ((intervalIntegrable_iff_integrableOn_Icc_of_le
          T.2 enorm_ne_top).1 (hβI i)).1)
      intro t ht
      change |w i t (P t)*β t i| ≤ _
      rw [abs_mul]
      exact mul_le_mul (hJp i t ht) (hβ t ht i) (abs_nonneg _) (hJ i)
    have hP' (t : ℝ) (i : Fin k) : p (P t) i = ∫ u in (0:ℝ)..t, β u i := by
      simp only [p,P,Z,ia,queueHJBObservation,Fin.append_left,Fin.append_right,D,β]
    have hS (i : Fin k) : Tendsto (rightGrid T (fun t => w i t (P t)) (fun t => p (P t) i))
        atTop (𝓝 (∫ t in (0:ℝ)..(T:ℝ),w i t (P t)*β t i)) := by
      simp only [rightGrid,hP']
      exact right_endpoint_stieltjes_sums_for_cadlag_weight T C (J i) T.2 hC0 (hJ i)
        (fun t => w i t (P t)) (fun t => β t i) (rightW T P hP _ (hw i)) (hJp i)
        (hβI i) (fun t ht => hβ t ht i)
    have h₁ (T : ℝ) : (∫ t in (0:ℝ)..T, (1:ℝ)) = T := by simp
    have hJ₀ : Tendsto (rightGrid T (fun t => H t (P t)) id) atTop
        (𝓝 (∫ t in (0:ℝ)..(T:ℝ),H t (P t))) := by
      have h' := right_endpoint_stieltjes_sums_for_cadlag_weight T 1 K T.2 zero_le_one hK
        (fun t => H t (P t)) (fun _ => 1) (rightW T P hP H hHc)
        (fun t ht => hKp t ht _ (hPbound t ht)) intervalIntegrable_const
        (fun _ _ => abs_one.le)
      unfold rightGrid
      simpa only [h₁,mul_one,id_eq] using h'
    have hEq : Mark T (fun t : ℝ≥0 => P t) =
        (∑ i, ∫ t in (0:ℝ)..(T:ℝ),w i t (P t)*β t i) -
          ∫ t in (0:ℝ)..(T:ℝ),H t (P t) := by
      let c (t : ℝ) := Real.exp (-γ*t)*L (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t)
      have hCI : IntervalIntegrable c volume 0 T := ((hInt n hn ω).2.2.2.2.2.2.1 T T.2).2.1
      have hWI : IntervalIntegrable (fun t => ∑ i, w i t (P t)*β t i) volume 0 T := by
        have he : (∑ i : Fin k, fun t => w i t (P t)*β t i) =
            (fun t => ∑ i, w i t (P t)*β t i) := Finset.sum_fn _ _
        rw [← he]
        exact IntervalIntegrable.sum Finset.univ (fun i _ => hwi i)
      have heq : P T ig = ∫ t in (0:ℝ)..(T:ℝ),
          (c t + (∑ i, w i t (P t)*β t i)) - H t (P t) := by
        simp only [ig,P,Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,
          Matrix.cons_val_succ,Matrix.cons_val_zero',Matrix.cons_val_succ']
        apply intervalIntegral.integral_congr
        intro t ht
        simp only [c,w,P,state,ix,Z,queueHJBObservation,Fin.append_left,H,β,D]
        rw [mul_sub,mul_add,Finset.mul_sum]
        have h : ∑ i, Real.exp (-γ*t)*(drift D (M.Xhat n (X n) ω t)
            (uProc n u0 (X n) (Ψ n) ω t) i * grad f (M.Xhat n (X n) ω t) i) =
            ∑ i, Real.exp (-γ*t)*grad f (M.Xhat n (X n) ω t) i*
              drift D (M.Xhat n (X n) ω t) (uProc n u0 (X n) (Ψ n) ω t) i := by
          apply Finset.sum_congr rfl
          intro i _
          ring
        rw [h]
        ring
      have heq₁ : P T ic = ∫ t in (0:ℝ)..(T:ℝ),c t := by
        simp only [ic,P,Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,c,L]
      change P T ig-P T ic = _
      rw [heq,heq₁,intervalIntegral.integral_sub (hCI.add hWI) hHInt,
        intervalIntegral.integral_add hCI hWI,intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => hwi i)]
      ring
    simp_rw [hGridEval]
    rw [hEq]
    exact (tendsto_finsetSum Finset.univ (fun i _ => hS i)).sub hJ₀
  let Q (ω : d.Ω') (t : ℝ) := d.limit ω (t.toNNReal:ℝ)
  have hQc (ω : d.Ω') : Continuous (Q ω) :=
    (d.limit_cont ω).comp_continuous
      ((continuous_subtype_val : Continuous (fun v : ℝ≥0 => (v:ℝ))).comp continuous_real_toNNReal)
      (fun t => t.toNNReal.2)
  have hBme (ω : d.Ω') : Measurable (b ω) := hBm.comp (measurable_const.prodMk measurable_id)
  have hBI (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) : IntervalIntegrable (b ω) volume 0 T := by
    obtain ⟨A,hA⟩ := (isCompact_Icc.image_of_continuousOn ((hQc ω).norm.continuousOn :
      ContinuousOn (fun t => ‖Q ω t‖) (Icc (0:ℝ) T))).bddAbove
    have hBs (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) : ‖b ω t‖ ≤ a*(1+(k:ℝ)*A) :=
      (hB ω t).trans (mul_le_mul_of_nonneg_left
        (add_le_add_right (hBound_b A (Q ω t) (hA ⟨t,ht,rfl⟩)) 1) ha.le)
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT enorm_ne_top]
    apply Measure.integrableOn_of_bounded (Real.volume_Icc .. ▸ ENNReal.ofReal_ne_top)
      (hBme ω).aestronglyMeasurable
    exact (ae_restrict_mem measurableSet_Icc).mono hBs
  have hBIcoord (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) (i : Fin k) :
      IntervalIntegrable (fun t => b ω t i) volume 0 T :=
    let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
    ⟨proj.integrable_comp (hBI ω T hT).1,proj.integrable_comp (hBI ω T hT).2⟩
  have hWc (ω : d.Ω') (i : Fin k) : Continuous (fun t => w i t (Q ω t)) :=
    (hw i).comp (continuous_id.prodMk (hQc ω))
  have hHlim (ω : d.Ω') : Continuous (fun t => H t (Q ω t)) :=
    hHc.comp (continuous_id.prodMk (hQc ω))
  let value (ω : d.Ω') (t : ℝ) := ∑ i, w i t (Q ω t)*b ω t i
  let gapInt (ω : d.Ω') (T : ℝ) := ∫ t in (0:ℝ)..T,value ω t-H t (Q ω t)
  have hVia (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) (i : Fin k) :
      IntervalIntegrable (fun t => w i t (Q ω t)*b ω t i) volume 0 T :=
    (hBIcoord ω T hT i).continuousOn_mul (hWc ω i).continuousOn
  have hVA (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) :
      IntervalIntegrable (value ω) volume 0 T := by
    have he : (∑ i : Fin k, fun t => w i t (Q ω t)*b ω t i) = value ω := Finset.sum_fn _ _
    rw [← he]
    exact IntervalIntegrable.sum Finset.univ (fun i _ => hVia ω T hT i)
  have hVia' (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) :
      IntervalIntegrable (fun t => value ω t-H t (Q ω t)) volume 0 T :=
    (hVA ω T hT).sub ((hHlim ω).intervalIntegrable 0 T)
  have hIntEq (ω : d.Ω') (T : ℝ) (hT : 0 ≤ T) :
      gapInt ω T = (∑ i, ∫ t in (0:ℝ)..T,w i t (Q ω t)*b ω t i) -
        ∫ t in (0:ℝ)..T,H t (Q ω t) := by
    dsimp only [gapInt]
    rw [intervalIntegral.integral_sub (hVA ω T hT) ((hHlim ω).intervalIntegrable 0 T)]
    unfold value
    rw [intervalIntegral.integral_finsetSum (s := Finset.univ) (fun i _ => hVia ω T hT i)]
  have hFixed (T : ℝ≥0) : ∀ᵐ ω ∂d.Q, d.gap T ω-d.runningCost T ω = gapInt ω T := by
    let A : Set (ℝ≥0 → E) := {p | Tendsto (Grid T p) atTop (𝓝 (Mark T p))}
    have hA : MeasurableSet A := measurableSet_tendsto_fun (hGrid T) (hMark T)
    have hDef : ∀ᶠ j in atTop, ∀ ω, (fun t : ℝ≥0 => Z (s (d.r j)) ω t) ∈ A :=
      (hs.comp d.r_cofinal).eventually ((eventually_ge_atTop 1).mono (fun n hn ω => hPre T n hn ω))
    obtain ⟨N,hN⟩ := eventually_atTop.1 (d.row_law.and hDef)
    have hRow (n : ℕ) : ∀ᵐ ω ∂d.Q, N ≤ n → (fun t : ℝ≥0 => d.row n ω t) ∈ A := by
      by_cases hn : N ≤ n
      · have hh := (hN n hn).1.measure_mem_eq hA.compl
        have he : {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ Aᶜ} = ∅ := by
          apply eq_empty_iff_forall_notMem.2
          intro ω hw
          exact hw ((hN n hn).2 ω)
        change d.Q {ω | (fun t : ℝ≥0 => d.row n ω t) ∈ Aᶜ} =
          M.P {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ Aᶜ} at hh
        rw [he,measure_empty] at hh
        exact (ae_iff.2 hh).mono (fun ω h _ => h)
      · exact Eventually.of_forall (fun _ h => (hn h).elim)
    filter_upwards [ae_all_iff.2 hRow,hRows,hPrim,d.convergence] with ω hRow hR hPr hU
    obtain ⟨B,hB0,hBB⟩ := path_bound (d.limit ω) (fun i => by
      refine ⟨fun t ht => ((continuous_apply i).comp_continuousOn (d.limit_cont ω) t ht).mono
        (fun s hs => ht.trans hs),?_⟩
      intro t ht
      have hc := ((continuous_apply i).comp_continuousOn (d.limit_cont ω) t ht.le).continuousAt
        (Ici_mem_nhds ht)
      exact ⟨_,hc.tendsto.mono_left nhdsWithin_le_nhds⟩) T
    have hQR (t : ℝ) (ht : 0 ≤ t) : Q ω t = d.limit ω t := by
      dsimp [Q]
      rw [max_eq_left ht]
    have hNorm (ε : ℝ) (hε : 0 < ε) :
        ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T, ‖d.row n ω t-d.limit ω t‖ < ε := by
      filter_upwards [(tendsto_order.1 (hU T T.2)).2 _ (ENNReal.ofReal_pos.2 hε)] with n hn
      intro t ht
      have hSum : ∑ i, |d.row n ω t i-d.limit ω t i| < ε :=
        (ENNReal.ofReal_lt_ofReal_iff hε).1 ((le_iSup₂_of_le t ht le_rfl).trans_lt hn)
      refine lt_of_le_of_lt ?_ hSum
      apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))).2
      intro i
      rw [Pi.sub_apply,Real.norm_eq_abs]
      exact Finset.single_le_sum (f := fun j => |d.row n ω t j-d.limit ω t j|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ i)
    have hBound : ∀ᶠ n in atTop, ∀ t ∈ Icc (0:ℝ) T, ‖d.row n ω t‖ ≤ B+1 := by
      filter_upwards [hNorm 1 zero_lt_one] with n hn
      intro t ht
      have hh := norm_add_le (d.row n ω t-d.limit ω t) (d.limit ω t)
      rw [sub_add_cancel] at hh
      linarith [hn t ht,hBB t ht]
    obtain ⟨N',hN'⟩ := eventually_atTop.1 (hR.and (hBound.and (eventually_ge_atTop N)))
    let U (j : ℕ) (t : ℝ) := d.row (j+N') ω t
    have hN'' (j : ℕ) := hN' (j+N') (by omega)
    have hRc (j : ℕ) (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (U j) (Ici t) t :=
      continuousWithinAt_pi.2 (fun i => (d.row_cadlag (j+N') ω i).1 t ht)
    have hUc : Tendsto (fun j => supDist (U j) (d.limit ω) T) atTop (𝓝 0) :=
      (hU T T.2).comp (tendsto_add_atTop_nat N')
    let C := a*(1+(k:ℝ)*(B+1))
    have hC0 : 0 ≤ C := by dsimp [C]; positivity
    have hBd : ∀ j t, t ∈ Icc (0:ℝ) T → a*(1+l1norm (state (U j t))) ≤ C := by
      intro j t ht
      exact mul_le_mul_of_nonneg_left
        (add_le_add_right (hBound_b _ _ ((hN'' j).2.1 t ht)) 1) ha.le
    have hBlim (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (i : Fin k) : |b ω t i| ≤ C := by
      have h' := norm_le_pi_norm (b ω t) i
      rw [Real.norm_eq_abs] at h'
      refine h'.trans ((hB ω t).trans ?_)
      apply mul_le_mul_of_nonneg_left _ ha.le
      have h : ‖Q ω t‖ ≤ B+1 := by rw [hQR t ht.1]; linarith [hBB t ht]
      exact add_le_add_right (hBound_b _ _ h) 1
    have hUcEval (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (i : Fin k) :
        Tendsto (fun j => p (U j t) i) atTop (𝓝 (p (Q ω t) i)) := by
      apply Metric.tendsto_nhds.2
      intro ε hε
      filter_upwards [(tendsto_add_atTop_nat N').eventually (hNorm ε hε)] with j hj
      rw [Real.dist_eq,hQR t ht.1]
      exact lt_of_le_of_lt (by simpa only [p,Real.norm_eq_abs,Pi.sub_apply] using
          (norm_le_pi_norm (U j t-d.limit ω t) (ia i))) (hj t ht)
    have hDens (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (i : Fin k) :
        (∫ s in (0:ℝ)..t,b ω s i) = p (Q ω t) i-p (Q ω 0) i := by
      let t' : ℝ≥0 := ⟨t,ht.1⟩
      let proj := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin k => ℝ) i
      have he := proj.intervalIntegral_comp_comm (hBI ω t ht.1)
      change (∫ s in (0:ℝ)..t,b ω s i) = (∫ s in (0:ℝ)..t,b ω s) i at he
      have hh := hPr t'
      change (∫ s in (0:ℝ)..t,b ω s) = d.driftIntegral t' ω-d.driftIntegral 0 ω at hh
      rw [he,hh,hQR t ht.1,hQR 0 le_rfl]
      rfl
    have hWi (i : Fin k) : ∃ z : ℕ → ℝ,
        (∀ j, Tendsto (rightGrid T (fun t => w i t (U j t)) (fun t => p (U j t) i))
          atTop (𝓝 (z j))) ∧
        Tendsto z atTop (𝓝 (∫ t in (0:ℝ)..(T:ℝ),w i t (Q ω t)*b ω t i)) := by
      obtain ⟨J,hJ0,hJ⟩ := continuous_function_compact_state_bound (w i) (hw i) T (B+1)
      refine stieltjes_integrals_stable_under_uniform_weight_and_primitive_limits T C J T.2 hC0 hJ0
        (fun j t => w i t (U j t)) (fun j t => p (U j t) i)
        (fun t => w i t (Q ω t)) (fun t => p (Q ω t) i) (fun t => b ω t i)
        (fun j => rightW T (U j) (hRc j) _ (hw i))
        (fun j t ht => hJ t ht _ ((hN'' j).2.1 t ht)) ?_ (hWc ω i).continuousOn
        ?_ (fun t ht => hUcEval t ht i) (fun t ht => hDens t ht i)
        (hBIcoord ω T T.2 i) (fun t ht => hBlim t ht i)
      · intro ε hε
        filter_upwards [continuous_joint_function_preserves_local_uniform_limit (w i) (hw i) T U
          (d.limit ω) B hBB hUc ε hε] with j hj
        intro t ht
        exact hQR t ht.1 ▸ hj t ht
      · intro j s t hs ht
        rcases le_total s t with h | h
        · have h' := (hN'' j).1 s t C hs.1 h (fun u hu =>
            hBd j u ⟨hs.1.trans hu.1,hu.2.trans ht.2⟩)
          rw [abs_of_nonneg (sub_nonneg.2 h)]
          exact (by simpa only [p,Real.norm_eq_abs,Pi.sub_apply] using
            norm_le_pi_norm ((fun i => p (U j t) i)-(fun i => p (U j s) i)) i :
            |p (U j t) i-p (U j s) i| ≤ ‖(fun i => p (U j t) i)-(fun i => p (U j s) i)‖).trans h'
        · have h' := (hN'' j).1 t s C ht.1 h (fun u hu =>
            hBd j u ⟨ht.1.trans hu.1,hu.2.trans hs.2⟩)
          rw [abs_sub_comm (p (U j t) i),abs_of_nonpos (sub_nonpos.2 h),neg_sub]
          exact (by simpa only [p,Real.norm_eq_abs,Pi.sub_apply] using
            norm_le_pi_norm ((fun i => p (U j s) i)-(fun i => p (U j t) i)) i :
            |p (U j s) i-p (U j t) i| ≤ ‖(fun i => p (U j s) i)-(fun i => p (U j t) i)‖).trans h'
    choose z hz hzLim using hWi
    obtain ⟨K,hK0,hK⟩ := continuous_function_compact_state_bound H hHc T (B+1)
    have hHRow (j : ℕ) : IntervalIntegrable (fun t => H t (U j t)) volume 0 T :=
      bounded_aestronglyMeasurable_intervalIntegrable T T.2 _ K
        (meas_int T T.2 (U j) (hRc j) H hHc) (fun t ht => hK t ht _ ((hN'' j).2.1 t ht))
    have hHG (j : ℕ) : Tendsto (rightGrid T (fun t => H t (U j t)) id) atTop
        (𝓝 (∫ t in (0:ℝ)..(T:ℝ),H t (U j t))) := by
      have h' := right_endpoint_stieltjes_sums_for_cadlag_weight T 1 K T.2 zero_le_one hK0
        (fun t => H t (U j t)) (fun _ => 1) (rightW T (U j) (hRc j) H hHc)
        (fun t ht => hK t ht _ ((hN'' j).2.1 t ht)) intervalIntegrable_const (fun _ _ => abs_one.le)
      unfold rightGrid
      simpa [intervalIntegral.integral_const] using h'
    have hHL : Tendsto (fun j => ∫ t in (0:ℝ)..(T:ℝ),H t (U j t)) atTop
        (𝓝 (∫ t in (0:ℝ)..(T:ℝ),H t (Q ω t))) := by
      apply Metric.tendsto_nhds.2
      intro ε hε
      let δ := ε/((T:ℝ)+1)
      have hδ : 0 < δ := by dsimp [δ]; positivity
      filter_upwards [continuous_joint_function_preserves_local_uniform_limit H hHc T U
        (d.limit ω) B hBB hUc δ hδ] with j hj
      rw [Real.dist_eq,← intervalIntegral.integral_sub (hHRow j) ((hHlim ω).intervalIntegrable 0 _ )]
      have hh := intervalIntegral.norm_integral_le_of_norm_le_const (C := δ)
        (a := (0:ℝ)) (b := (T:ℝ)) (f := fun t => H t (U j t)-H t (Q ω t)) (fun t ht => by
          have ht' : t ∈ Ioc (0:ℝ) T := uIoc_of_le T.2 ▸ ht
          rw [Real.norm_eq_abs,hQR t ht'.1.le]
          exact (hj t ⟨ht'.1.le,ht'.2⟩).le)
      have hTa : |(T:ℝ)| = (T:ℝ) := abs_of_nonneg T.2
      have hhh : |∫ t in (0:ℝ)..(T:ℝ),H t (U j t)-H t (Q ω t)| ≤ δ*(T:ℝ) := by
        simpa only [Real.norm_eq_abs,sub_zero,hTa] using hh
      refine hhh.trans_lt ?_
      dsimp [δ]
      have hT' : 0 < (T:ℝ)+1 := by positivity
      rw [div_mul_eq_mul_div,div_lt_iff₀ hT']
      nlinarith
    have hId (j : ℕ) : U j T ig-U j T ic =
        (∑ i, z i j) - ∫ t in (0:ℝ)..(T:ℝ),H t (U j t) := by
      have hGrid' := hRow (j+N') ((hN'' j).2.2)
      have h := (tendsto_finsetSum Finset.univ (fun i _ => hz i j)).sub (hHG j)
      have eq (m : ℕ) := hGridEval T m (U j)
      exact tendsto_nhds_unique hGrid' (h.congr' (Eventually.of_forall fun m => (eq m).symm))
    have hA' : Tendsto (fun j => U j T ig-U j T ic) atTop (𝓝 (d.gap T ω-d.runningCost T ω)) := by
      have hEv (i : Fin m) : Tendsto (fun j => U j T i) atTop (𝓝 (d.limit ω T i)) := by
        apply Metric.tendsto_nhds.2
        intro ε hε
        filter_upwards [(tendsto_add_atTop_nat N').eventually (hNorm ε hε)] with j hj
        rw [Real.dist_eq]
        exact lt_of_le_of_lt (by simpa only [Real.norm_eq_abs,Pi.sub_apply] using
            (norm_le_pi_norm (U j T-d.limit ω T) i)) (hj T ⟨T.2,le_rfl⟩)
      exact (hEv ig).sub (hEv ic)
    rw [hIntEq ω T T.2]
    exact tendsto_nhds_unique hA' (((tendsto_finsetSum Finset.univ (fun i _ => hzLim i)).sub hHL).congr'
      (Eventually.of_forall fun j => (hId j).symm))
  have hRat := ae_all_iff.2 (fun q : ℚ => hFixed ((q:ℝ).toNNReal))
  filter_upwards [hRat] with ω hω
  have hCont : ContinuousOn (gapInt ω) (Ici (0:ℝ)) := by
    intro t ht
    have hpos : 0 ≤ t+1 := by linarith [show 0 ≤ t from ht]
    have h : ContinuousOn (gapInt ω) (Icc (0:ℝ) (t+1)) := by
      simpa only [uIcc_of_le hpos] using intervalIntegral.continuousOn_primitive_interval'
        (hVia' ω (t+1) hpos) (left_mem_uIcc (a := (0:ℝ)) (b := t+1))
    have hN : Icc (0:ℝ) (t+1) ∈ 𝓝[Ici 0] t := by
      rw [← Ici_inter_Iic,inter_mem_iff]
      exact ⟨self_mem_nhdsWithin,nhdsWithin_le_nhds (Iic_mem_nhds (show t < t+1 by linarith))⟩
    exact (h t ⟨ht,by linarith⟩).mono_of_mem_nhdsWithin hN
  have hF : IsClosed {r : ℝ | Q ω r ig-Q ω r ic=gapInt ω (r.toNNReal:ℝ)} := by
    have hg := hCont.comp_continuous
      ((continuous_subtype_val : Continuous (fun t : ℝ≥0 => (t:ℝ))).comp continuous_real_toNNReal)
      (fun t => t.toNNReal.2)
    exact isClosed_eq (((continuous_apply ig).comp (hQc ω)).sub ((continuous_apply ic).comp (hQc ω))) hg
  have hS : range (fun q : ℚ => (q:ℝ)) ⊆ {r : ℝ | Q ω r ig-Q ω r ic=gapInt ω (r.toNNReal:ℝ)} := by
    rintro _ ⟨q,rfl⟩
    exact hω q
  have hAll := closure_minimal hS hF
  rw [(Rat.denseRange_cast : DenseRange (fun q : ℚ => (q:ℝ))).closure_range] at hAll
  intro t
  have he : d.gap t ω-d.runningCost t ω = gapInt ω t := by
    change d.limit ω t ig-d.limit ω t ic = _
    simpa only [Q,Real.toNNReal_coe,mem_setOf_eq] using hAll (mem_univ (t:ℝ))
  rw [sub_eq_iff_eq_add] at he
  rw [he,add_comm]
  apply congrArg (d.runningCost t ω + ·)
  apply intervalIntegral.integral_congr
  intro r hr
  simp only [value,w,H,state,ix,Q,QueueHJBPathSubseq.state]
  rw [mul_sub,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  change Real.exp (-γ*r)*grad f (d.state r.toNNReal ω) i*b ω r i =
    Real.exp (-γ*r)*(b ω r i*grad f (d.state r.toNNReal ω) i)
  ring
