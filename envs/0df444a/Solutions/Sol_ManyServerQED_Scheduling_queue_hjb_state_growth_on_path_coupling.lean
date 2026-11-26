-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_hjb_state_growth_on_path_coupling
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:44:49.43926+00:00
-- url     : https://prove2.me/submissions/7bf1e728-276c-46b2-9f01-8702bcbf7a36

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_scaled_queue_state_supremum_bounded_by_forcing
import Theorems.Thm_ManyServerQED_Scheduling_measurable_compact_supremum_of_evaluation_path
import Theorems.Thm_ManyServerQED_Scheduling_coupled_lipschitz_observable_compact_suprema_converge
open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy
private noncomputable def inputRate {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) : ℝ :=
  (M.lamN n i - M.rho i * M.muN n i * n) / Real.sqrt n

private theorem inputRate_tendsto {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) :
    Tendsto (fun n => inputRate M n i) atTop (𝓝 (M.ell i)) := by
  have hlim := (M.lamHat_lim i).sub (tendsto_const_nhds.mul (M.muHat_lim i) :
    Tendsto (fun n : ℕ => M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) atTop
      (𝓝 (M.rho i * M.muHat i)))
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hn'
  have hmul : Real.sqrt (n : ℝ) * Real.sqrt n = n := Real.mul_self_sqrt hn'.le
  have hρ : M.rho i * M.mu i = M.lam i := div_mul_cancel₀ _ (M.mu_pos i).ne'
  unfold inputRate
  symm
  apply (div_eq_iff hs.ne').2
  symm
  calc
    (Real.sqrt (n : ℝ) * (M.lamN n i / n - M.lam i) -
        M.rho i * (Real.sqrt n * (M.muN n i - M.mu i))) * Real.sqrt n =
      (Real.sqrt n * Real.sqrt n) *
        (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) := by ring
    _ = _ := by
      rw [hmul]
      calc
        (n : ℝ) * (M.lamN n i / n - M.lam i - M.rho i * (M.muN n i - M.mu i)) =
            M.lamN n i - (n : ℝ) * M.lam i -
              (n : ℝ) * M.rho i * M.muN n i + (n : ℝ) * (M.rho i * M.mu i) := by
          rw [mul_sub, mul_sub, mul_div_cancel₀ _ hn'.ne']
          ring
        _ = _ := by rw [hρ]; ring


set_option maxHeartbeats 2300000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (L : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (u0 : Fin k → ℝ) (f : (Fin k → ℝ) → ℝ) (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hC : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (X n) (Ψ n))
    (hWork : ∀ n, 1 ≤ n → IsWorkConserving n (X n) (Ψ n))
    (s : ℕ → ℕ) (hs : Tendsto s atTop atTop)
    (d : QueueHJBPathSubseq M.P (queueHJBObservation M L γ u0 f X Ψ) s)
    (hCadLaw : ∀ᶠ n in atTop, ∀ ω i, IsCadlag (fun t => queueHJBObservation M L γ u0 f X Ψ n ω t i)) :
    ∃ a : ℝ, 0 < a ∧ ∀ T : ℝ≥0, ∀ᵐ ω ∂d.Q, ∀ t ≤ T,
      ENNReal.ofReal (l1norm (d.state t ω)) ≤
        ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2) *
          (ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ))) +
            ∑ i, ENNReal.ofReal (M.diffData.r i) *
              (⨆ u : Iic T, ENNReal.ofReal |d.noise u.1 ω i|)) := by
  classical
  let Z := queueHJBObservation M L γ u0 f X Ψ
  let m := k+k+k+2
  let r := M.diffData.r
  let ix (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.castAdd k (Fin.castAdd k i))
  let iw (i : Fin k) : Fin m := Fin.castAdd 2 (Fin.castAdd k (Fin.natAdd k i))
  let v (z : Fin m → ℝ) := ∑ i, |z (ix i)|
  let w (i : Fin k) (z : Fin m → ℝ) := |z (iw i)|
  have hW (i : Fin k) : Continuous (w i) := (continuous_apply _).abs
  have hV : Continuous v := continuous_finsetSum _ (fun i _ => (continuous_apply _).abs)
  have hWn (i : Fin k) (z : Fin m → ℝ) : 0 ≤ w i z := abs_nonneg _
  have hVn (z : Fin m → ℝ) : 0 ≤ v z := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hWl (i : Fin k) (x y : Fin m → ℝ) : |w i x-w i y| ≤ ∑ j, |x j-y j| :=
    (abs_abs_sub_abs_le_abs_sub _ _).trans
      (Finset.single_le_sum (f := fun j => |x j-y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ _))
  have hVl (x y : Fin m → ℝ) : |v x-v y| ≤ ∑ j, |x j-y j| := by
    dsimp only [v]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum
      (fun i _ => abs_abs_sub_abs_le_abs_sub (x (ix i)) (y (ix i)))).trans ?_)
    have hInject : Function.Injective ix :=
      (Fin.castAdd_injective (k+k+k) 2).comp
        ((Fin.castAdd_injective (k+k) k).comp (Fin.castAdd_injective k k))
    calc
      ∑ i, |x (ix i)-y (ix i)| = ∑ j ∈ Finset.univ.image ix, |x j-y j| :=
        (Finset.sum_image (s := Finset.univ) (f := fun j => |x j-y j|) hInject.injOn).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => abs_nonneg _)
  let a : ℝ := 1 + ∑ i, (|x i|+|M.ell i|+M.mu i+M.theta i+4)
  have hComp (i : Fin k) : |x i|+|M.ell i|+M.mu i+M.theta i+4 ≤ a := by
    dsimp only [a]
    have h := Finset.single_le_sum
      (f := fun i => |x i|+|M.ell i|+M.mu i+M.theta i+4)
      (fun j _ => by positivity [M.mu_pos j,M.theta_nonneg j]) (Finset.mem_univ i)
    linarith
  have ha : 0 < a := by
    have hh : 0 ≤ ∑ i, (|x i|+|M.ell i|+M.mu i+M.theta i+4) :=
      Finset.sum_nonneg (fun i _ => by positivity [M.mu_pos i,M.theta_nonneg i])
    dsimp [a]
    linarith
  have hRates : ∀ᶠ n in atTop, ∀ i,
      |M.Xhat0 n (X0 n) i| ≤ a ∧ |inputRate M n i| ≤ a ∧
      M.muN n i ≤ a ∧ M.thetaN n i ≤ a := by
    apply eventually_all.2
    intro i
    have hX := (continuous_apply i).continuousAt.tendsto.comp hX0
    filter_upwards [Metric.tendsto_nhds.1 hX 1 zero_lt_one,
      Metric.tendsto_nhds.1 (inputRate_tendsto M i) 1 zero_lt_one,
      Metric.tendsto_nhds.1 (M.mu_lim i) 1 zero_lt_one,
      Metric.tendsto_nhds.1 (M.theta_lim i) 1 zero_lt_one] with n hx hEll hμ hθ
    simp only [Real.dist_eq,Function.comp_apply] at hx hEll hμ hθ
    have h := hComp i
    have hμ0 := (M.mu_pos i).le
    have hθ0 := M.theta_nonneg i
    exact ⟨by linarith [abs_sub_abs_le_abs_sub (M.Xhat0 n (X0 n) i) (x i),abs_nonneg (M.ell i)],
      by linarith [abs_sub_abs_le_abs_sub (inputRate M n i) (M.ell i),abs_nonneg (x i)],
      by linarith [(abs_lt.1 hμ).2,abs_nonneg (x i),abs_nonneg (M.ell i)],
      by linarith [(abs_lt.1 hθ).2,abs_nonneg (x i),abs_nonneg (M.ell i)]⟩
  refine ⟨a,ha,?_⟩
  intro T
  let A := ENNReal.ofReal ((k:ℝ)*(1+a*(T:ℝ))^2)
  let B := ENNReal.ofReal ((k:ℝ)*a*(1+(T:ℝ)))
  obtain ⟨V,hVm,hVE⟩ := measurable_compact_supremum_of_evaluation_path v hV T
  have hwExist (i : Fin k) := measurable_compact_supremum_of_evaluation_path (w i) (hW i) T
  choose W hWm hWE using hwExist
  let RHS (p : ℝ≥0 → Fin m → ℝ) := A*(B+∑ i, ENNReal.ofReal (r i)*W i p)
  have hRHS : Measurable RHS :=
    (measurable_const.add (Finset.measurable_sum _ (fun i _ => (hWm i).const_mul _))).const_mul _
  let E : Set (ℝ≥0 → Fin m → ℝ) := {p | V p ≤ RHS p}
  have hE : MeasurableSet E := measurableSet_le hVm hRHS
  have hp : ∀ᶠ n in atTop, ∀ ω,
      (∀ i, IsCadlag (fun t => Z n ω t i)) →
      (fun t : ℝ≥0 => Z n ω t) ∈ E := by
    filter_upwards [eventually_ge_atTop 1,hRates] with n hn hrates
    intro ω hCad
    have hRight (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (Z n ω) (Ici t) t :=
      continuousWithinAt_pi.2 (fun i => (hCad i).1 t ht)
    let p (t : ℝ≥0) := Z n ω t
    let b (t : ℝ) (i : Fin k) :=
      M.Xhat0 n (X0 n) i + r i*Z n ω t (iw i) + inputRate M n i*t
    have he (t : ℝ) (i : Fin k) : r i*Z n ω t (iw i) =
        M.Ahat n ω t i-M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i-
        M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i := by
      simp only [r,iw,Z,queueHJBObservation,Fin.append_left,Fin.append_right]
      field_simp [(M.diffData.r_pos i).ne']
      ring
    have hZ (t : ℝ) : v (Z n ω t) = l1norm (M.Xhat n (X n) ω t) := by
      simp only [v,Z,ix,queueHJBObservation,Fin.append_left,l1norm]
    have hstate : V p = supDist (M.Xhat n (X n) ω) (fun _ => 0) T := by
      rw [hVE _ hRight]
      simp only [hZ,supDist,Pi.zero_apply,sub_zero,l1norm]
    have hPoint (t : ℝ) (ht : t ∈ Icc (0:ℝ) T) (i : Fin k) :
        ENNReal.ofReal |b t i| ≤ ENNReal.ofReal (a*(1+(T:ℝ)))+ENNReal.ofReal (r i)*W i p := by
      have hh := (abs_add_le (M.Xhat0 n (X0 n) i+r i*Z n ω t (iw i))
        (inputRate M n i*t)).trans (add_le_add_left (abs_add_le _ _) _)
      rw [abs_mul (r i),abs_of_nonneg (M.diffData.r_pos i).le,abs_mul (inputRate M n i),abs_of_nonneg ht.1] at hh
      have hb0 : |b t i| ≤ a*(1+(T:ℝ))+r i*|Z n ω t (iw i)| := by
        dsimp only [b]
        have ht' := mul_le_mul ((hrates i).2.1) ht.2 ht.1 ha.le
        linarith [(hrates i).1]
      have hS : ENNReal.ofReal |Z n ω t (iw i)| ≤ W i p := by
        rw [hWE i _ hRight]
        exact le_iSup₂_of_le t ht le_rfl
      refine (ENNReal.ofReal_le_ofReal hb0).trans ?_
      rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (M.diffData.r_pos i).le (abs_nonneg _)),
        ENNReal.ofReal_mul (M.diffData.r_pos i).le]
      exact add_le_add le_rfl (mul_le_mul_right hS _)
    have hB : supDist b (fun _ => 0) T ≤ B+∑ i, ENNReal.ofReal (r i)*W i p := by
      apply iSup₂_le
      intro t ht
      simp only [Pi.zero_apply,sub_zero,ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg (b t i))]
      refine (Finset.sum_le_sum (fun i _ => hPoint t ht i)).trans_eq ?_
      rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,← ENNReal.ofReal_natCast k,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 2
      ring
    have hG := scaled_queue_state_supremum_bounded_by_forcing M n (Nat.zero_lt_of_lt hn) (X0 n)
      (X n) (Ψ n) (hC n hn) (hWork n hn) a ha
      (fun i => (hrates i).2.2.1) (fun i => (hrates i).2.2.2) T T.2 ω
    simp only at hG
    change V p ≤ RHS p
    rw [hstate]
    refine hG.trans ?_
    apply mul_le_mul_right
    have heq : (fun t i => M.Xhat0 n (X0 n) i+M.Ahat n ω t i-
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i-
      M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i+inputRate M n i*t) = b := by
      funext t i
      simp only [b,he]
      ring
    exact heq.symm ▸ hB
  have hOrig : ∀ᶠ j in atTop, ∀ ω, (fun t : ℝ≥0 => Z (s (d.r j)) ω t) ∈ E :=
    (hs.comp d.r_cofinal).eventually ((hp.and hCadLaw).mono fun _ h ω => h.1 ω (h.2 ω))
  obtain ⟨N,hN⟩ := eventually_atTop.1 (d.row_law.and hOrig)
  have hRow (n : ℕ) : ∀ᵐ ω ∂d.Q, N ≤ n → (fun t : ℝ≥0 => d.row n ω t) ∈ E := by
    by_cases hn : N ≤ n
    · have hLaw := (hN n hn).1
      apply ae_iff.2
      have hO : {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ Eᶜ} = ∅ := by
        ext ω
        simp only [mem_setOf_eq,mem_compl_iff,notMem_empty,iff_false,not_not]
        exact (hN n hn).2 ω
      have hQ := hLaw.measure_mem_eq hE.compl
      change d.Q {ω | (fun t : ℝ≥0 => d.row n ω t) ∈ Eᶜ} =
        M.P {ω | (fun t : ℝ≥0 => Z (s (d.r n)) ω t) ∈ Eᶜ} at hQ
      rw [hO,measure_empty] at hQ
      simpa only [hn,true_implies,mem_compl_iff] using hQ
    · exact Eventually.of_forall (fun _ h => (hn h).elim)
  have hbV := (coupled_lipschitz_observable_compact_suprema_converge d T v hV hVn hVl).2
  have hbW (i : Fin k) := (coupled_lipschitz_observable_compact_suprema_converge
    d T (w i) (hW i) (hWn i) (hWl i)).2
  filter_upwards [ae_all_iff.2 hRow,hbV,ae_all_iff.2 hbW] with ω hRows hVL hWL
  let P (n : ℕ) (t : ℝ≥0) := d.row n ω t
  let I (t : ℝ≥0) := d.limit ω t
  have hr (n : ℕ) (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (d.row n ω) (Ici t) t :=
    continuousWithinAt_pi.2 (fun i => (d.row_cadlag n ω i).1 t ht)
  have hl (t : ℝ) (ht : 0 ≤ t) : ContinuousWithinAt (d.limit ω) (Ici t) t :=
    (d.limit_cont ω t ht).mono (fun u hu => ht.trans hu)
  have hVL' : Tendsto (fun n => V (P n)) atTop (𝓝 (V I)) := by
    simp only [P,I,hVE _ hl,show ∀ n, V (P n)=_ from fun n => hVE _ (hr n),iSup_subtype] at *
    exact hVL
  have hWL' (i : Fin k) : Tendsto (fun n => W i (P n)) atTop (𝓝 (W i I)) := by
    convert hWL i using 2
    · rw [hWE i _ (hr _),iSup_subtype]
    · rw [hWE i _ hl,iSup_subtype]
  have hM (x : ℝ≥0∞) (h : x ≠ ⊤) (f : ℕ → ℝ≥0∞) (v : ℝ≥0∞)
      (hf : Tendsto f atTop (𝓝 v)) : Tendsto (fun n => x*f n) atTop (𝓝 (x*v)) :=
    (ENNReal.continuous_const_mul h).continuousAt.tendsto.comp hf
  have hD : Tendsto (fun n => RHS (P n)) atTop (𝓝 (RHS I)) := by
    refine hM A ENNReal.ofReal_ne_top _ _ (tendsto_const_nhds.add ?_)
    exact tendsto_finsetSum _ (fun i _ => hM _ ENNReal.ofReal_ne_top _ _ (hWL' i))
  have hInequality : V I ≤ RHS I := le_of_tendsto_of_tendsto hVL' hD
    ((eventually_ge_atTop N).mono (fun n hn => hRows n hn))
  intro t ht
  have htV : ENNReal.ofReal (l1norm (d.state t ω)) ≤ V I := by
    rw [hVE _ hl]
    exact le_iSup₂_of_le (t:ℝ) (show (t:ℝ) ∈ Icc (0:ℝ) T from ⟨t.2,by exact_mod_cast ht⟩) le_rfl
  refine htV.trans (hInequality.trans ?_)
  unfold RHS
  apply mul_le_mul_right
  apply add_le_add_right
  apply Finset.sum_le_sum
  intro i _
  apply mul_le_mul_right
  rw [hWE i _ hl]
  apply iSup₂_le
  intro u hu
  let u' : ℝ≥0 := ⟨u,hu.1⟩
  have hu' : u' ∈ Iic T := mem_Iic.2 (by exact_mod_cast hu.2)
  exact le_iSup (fun u : Iic T => ENNReal.ofReal |d.noise u.1 ω i|) ⟨u',hu'⟩
