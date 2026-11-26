-- Prove2me | solution 1 for ManyServerQED.Scheduling.queue_positive_variance_arrivals_uniform_walk_approximation
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T02:23:45.398704+00:00
-- url     : https://prove2.me/submissions/d79486b5-077d-4d17-b7a9-955826abeec5

import Mathlib
import Theorems.Thm_DurrettProbability_donsker
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_DurrettProbability_Donsker

open Set Filter Topology MeasureTheory ProbabilityTheory DurrettProbability
open scoped ENNReal NNReal
private abbrev I := Icc (0:ℝ) 1

private def modBad (d ε : ℝ) : Set PathSpace :=
  {f | ∃ s t : I, dist s t ≤ d ∧ ε ≤ ‖(fun _ : Fin 1 => f s) - (fun _ : Fin 1 => f t)‖}

private theorem isClosed_modBad (d ε : ℝ) : IsClosed (modBad d ε) := by
  let R : Set (I × I) := {p | dist p.1 p.2 ≤ d}
  have hr : IsClosed R := isClosed_le (continuous_fst.dist continuous_snd) continuous_const
  let Q : Set (PathSpace × (I × I)) :=
    {p | p.2 ∈ R ∧ ε ≤ ‖(fun _ : Fin 1 => p.1 p.2.1) - (fun _ : Fin 1 => p.1 p.2.2)‖}
  have h₁ : Continuous (fun p : PathSpace × (I × I) => (fun _ : Fin 1 => p.1 p.2.1)) := by
    apply continuous_pi
    intro i
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))
  have h₂ : Continuous (fun p : PathSpace × (I × I) => (fun _ : Fin 1 => p.1 p.2.2)) := by
    apply continuous_pi
    intro i
    exact continuous_eval.comp (continuous_fst.prodMk (continuous_snd.comp continuous_snd))
  have hQ : IsClosed Q :=
    (hr.preimage continuous_snd).inter (isClosed_le continuous_const (h₁.sub h₂).norm)
  have him := isClosedMap_fst_of_compactSpace Q hQ
  convert him using 1
  ext f
  change (∃ s t : I, dist s t ≤ d ∧ _) ↔ ∃ p ∈ Q, p.1 = f
  constructor
  · rintro ⟨s,t,h₁,h₂⟩
    exact ⟨(f,s,t),⟨h₁,h₂⟩,rfl⟩
  · rintro ⟨⟨p,s,t⟩,⟨h₁,h₂⟩,rfl⟩
    exact ⟨s,t,h₁,h₂⟩

private theorem continuous_path_tightness {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → PathSpace) (Y : Ω' → PathSpace)
    (h : TendstoInDistribution X atTop Y (fun _ => P) P')
    (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    ∃ A > 0, ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | A ≤ ‖X n ω‖ ∨ ∃ s t : Set.Icc (0:ℝ) 1,
        dist s t ≤ δ ∧ ε ≤ |X n ω s-X n ω t|} ≤ ENNReal.ofReal η := by
  let μn : ℕ → ProbabilityMeasure PathSpace := fun n =>
    ⟨P.map (X n),Measure.isProbabilityMeasure_map (h.forall_aemeasurable n)⟩
  let μ : ProbabilityMeasure PathSpace :=
    ⟨P'.map Y,Measure.isProbabilityMeasure_map h.aemeasurable_limit⟩
  have hμ : Tendsto μn atTop (𝓝 μ) := h.tendsto
  have hPos : 0 < η/2 := by linarith
  have small_closed_family (B : ℕ → Set PathSpace) (hB : ∀ m, IsClosed (B m))
      (hA : Antitone B) (h0 : (⋂ m, B m) = ∅) :
      ∃ m, ∀ᶠ n in atTop, (μn n : Measure PathSpace) (B m) ≤ ENNReal.ofReal (η/2) := by
    have hL := tendsto_measure_iInter_atTop (μ := (μ : Measure PathSpace))
      (fun m => (hB m).measurableSet.nullMeasurableSet) hA ⟨0,measure_ne_top _ _⟩
    rw [h0,measure_empty] at hL
    obtain ⟨m,hm⟩ := ((tendsto_order.1 hL).2 (ENNReal.ofReal (η/2)) (ENNReal.ofReal_pos.2 hPos)).exists
    have hLS := ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hμ (hB m)
    exact ⟨m,(eventually_lt_of_limsup_lt (hLS.trans_lt hm)).mono (fun _ h => h.le)⟩
  let B (m : ℕ) : Set PathSpace := {f | (m:ℝ)+1 ≤ ‖f‖}
  have hB (m : ℕ) : IsClosed (B m) := isClosed_le continuous_const continuous_norm
  have hBA : Antitone B := by
    intro m n hmn f hf
    have hc : (m:ℝ) ≤ n := by exact_mod_cast hmn
    exact le_trans (add_le_add_left hc 1) hf
  have hB0 : (⋂ m, B m) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro f hf
    obtain ⟨m,hm⟩ := exists_nat_gt ‖f‖
    have hh : (m:ℝ)+1 ≤ ‖f‖ := (Set.mem_iInter.1 hf) m
    linarith
  obtain ⟨m,hm⟩ := small_closed_family B hB hBA hB0
  let d (l : ℕ) : ℝ := 1/((l:ℝ)+1)
  have hd : Tendsto d atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hdpos (l : ℕ) : 0 < d l := by dsimp [d]; positivity
  have hdant : Antitone d := by
    intro i j hij
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hij)
  let C (l : ℕ) := modBad (d l) ε
  have hC (l : ℕ) : IsClosed (C l) := isClosed_modBad _ _
  have hCA : Antitone C := by
    rintro i j h f ⟨s,t,hst,hεt⟩
    exact ⟨s,t,hst.trans (hdant h),hεt⟩
  have hC0 : (⋂ l, C l) = ∅ := by
    apply eq_empty_iff_forall_notMem.2
    intro f hf
    have hCont : Continuous (fun t : I => fun _ : Fin 1 => f t) :=
      continuous_pi (fun _ => f.continuous)
    obtain ⟨δ,hδ,hmod⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous hCont) ε hε
    obtain ⟨l,hl⟩ := ((tendsto_order.1 hd).2 δ hδ).exists
    obtain ⟨s,t,hst,hεt⟩ := mem_iInter.1 hf l
    exact (not_lt_of_ge hεt) (by simpa only [dist_eq_norm] using hmod (hst.trans_lt hl))
  obtain ⟨l,hl⟩ := small_closed_family C hC hCA hC0
  refine ⟨(m:ℝ)+1,by positivity,d l,hdpos l,?_⟩
  filter_upwards [hm,hl] with n hmn hln
  have hIncl : {ω | (m:ℝ)+1 ≤ ‖X n ω‖ ∨ ∃ s t : I,
      dist s t ≤ d l ∧ ε ≤ |X n ω s-X n ω t|} ⊆ X n ⁻¹' (B m ∪ C l) := by
    rintro ω (h1 | ⟨s,t,hst,h2⟩)
    · exact Or.inl h1
    · apply Or.inr
      refine ⟨s,t,hst,?_⟩
      have hh : |X n ω s-X n ω t| ≤ ‖(fun _ : Fin 1 => X n ω s) - (fun _ : Fin 1 => X n ω t)‖ := by
        simpa [Real.norm_eq_abs] using norm_le_pi_norm ((fun _ : Fin 1 => X n ω s) -
          (fun _ : Fin 1 => X n ω t)) (0:Fin 1)
      exact h2.trans hh
  refine (measure_mono hIncl).trans ?_
  rw [← Measure.map_apply_of_aemeasurable (h.forall_aemeasurable n) ((hB m).measurableSet.union (hC l).measurableSet)]
  change (μn n : Measure PathSpace) (B m ∪ C l) ≤ _
  refine (measure_union_le _ _).trans ((add_le_add hmn hln).trans_eq ?_)
  rw [← ENNReal.ofReal_add hPos.le hPos.le]
  congr 1
  ring

open MeasureTheory ProbabilityTheory Filter Topology Finset
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private theorem renewal_bracket {e : ℕ → ℝ} (he : StrictMono e) {s : ℝ} {m : ℕ}
    (h0 : e 0 ≤ s) (hm : s < e m) :
    ∃ j < m, e j ≤ s ∧ s < e (j + 1) ∧ renewalCount e s = j := by
  have hExists : ∃ i, s < e i := ⟨m, hm⟩
  let b := Nat.find hExists
  have hb : s < e b := Nat.find_spec hExists
  have hb_le : b ≤ m := Nat.find_min' hExists hm
  have hb_pos : 0 < b := by
    by_contra! hb0
    rw [Nat.eq_zero_of_le_zero hb0] at hb
    exact (not_lt_of_ge h0) hb
  let j := b - 1
  have hsucc : j + 1 = b := by dsimp [j]; omega
  have hj_lt : j < b := by omega
  have hj : e j ≤ s := le_of_not_gt (Nat.find_min hExists hj_lt)
  have hj_succ : s < e (j + 1) := by rwa [hsucc]
  refine ⟨j, hj_lt.trans_le hb_le, hj, hj_succ, le_antisymm ?_ ?_⟩
  · unfold renewalCount
    refine iSup_le fun r => iSup_le fun hr => ?_
    have h : r ≤ j := by
      by_contra! hjr
      exact (not_lt_of_ge hr) (hj_succ.trans_le (he.monotone hjr))
    exact_mod_cast h
  · unfold renewalCount
    exact le_iSup_of_le j (le_iSup_of_le hj le_rfl)

set_option maxHeartbeats 850000 in
private theorem local_renewal_sandwich (n : ℕ) (hn : 1 ≤ n) (e : ℕ → ℝ) (he : StrictMono e) (he0 : e 0 = 0)
    (u : ℝ → ℝ) (H : ℝ) (hgrid : ∀ j : ℕ, (j:ℝ)/n ≤ H → u ((j:ℝ)/n) = (e j-j)/Real.sqrt n)
    (a T D δ ε : ℝ) (ha : 0 ≤ a) (hT : 0 ≤ T) (hH : a*T+3 ≤ H)
    (hD : ∀ s ∈ Set.Icc (0:ℝ) H, |u s| ≤ D)
    (hDsmall : D/Real.sqrt n < min 1 (δ/4))
    (hNsmall : 1/(n:ℝ) < δ/4) (hRsmall : 1/Real.sqrt n < ε/4) (hε : 0 < ε)
    (hMod : ∀ s ∈ Set.Icc (0:ℝ) H, ∀ t ∈ Set.Icc (0:ℝ) H,
      |s-t| < δ → |u s-u t| < ε/2) :
    ∀ t ∈ Set.Icc (0:ℝ) T,
      |(((renewalCount e ((n:ℝ)*a*t)).toNat:ℝ) - (n:ℝ)*a*t)/Real.sqrt n + u (a*t)| < ε := by
  intro t ht
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hsqrt : 0 < Real.sqrt (n:ℝ) := Real.sqrt_pos.2 hn0
  have hdiv1 : 1/(n:ℝ) ≤ 1 := by rwa [div_le_one hn0]
  have haT : a*t ≤ H-3 :=
    (mul_le_mul_of_nonneg_left ht.2 ha).trans (by linarith)
  have hvt : a*t ∈ Set.Icc 0 H := ⟨mul_nonneg ha ht.1,by linarith⟩
  let m : ℕ := ⌈(n:ℝ)*(H-1)⌉₊
  have hhm : H-1 ≤ (m:ℝ)/n := by
    apply (le_div_iff₀ hn0).2
    simpa [m,mul_comm] using (Nat.le_ceil ((n:ℝ)*(H-1)))
  have hmH : (m:ℝ)/n ≤ H := by
    have hH1 : 0 ≤ H-1 := by nlinarith [mul_nonneg ha hT]
    have hce := (Nat.ceil_lt_add_one (mul_nonneg hn0.le hH1)).le
    have he : (m:ℝ)/n ≤ (H-1)+1/(n:ℝ) := by
      apply (div_le_iff₀ hn0).2
      rw [add_mul, div_mul_cancel₀ _ hn0.ne']
      exact (by simpa only [m, mul_comm (H-1)] using hce)
    linarith
  have hDiv (j : ℕ) (hj : j ≤ m) : (j:ℝ)/n ∈ Set.Icc 0 H :=
    ⟨by positivity, (div_le_div_of_nonneg_right (by exact_mod_cast hj) hn0.le).trans hmH⟩
  have hDiff (j : ℕ) (hj : j ≤ m) : |(e j)/(n:ℝ) - (j:ℝ)/n| ≤ D / Real.sqrt n := by
    have huB := hD _ (hDiv j hj)
    have hcalc : e j/(n:ℝ) - (j:ℝ)/n = (e j - j) / Real.sqrt n / Real.sqrt n := by
      rw [← sub_div, div_div, ← pow_two, Real.sq_sqrt hn0.le]
    rw [hcalc, ← hgrid j (hDiv j hj).2, abs_div, abs_of_pos hsqrt]
    exact div_le_div_of_nonneg_right huB hsqrt.le
  have hStop : (n:ℝ) * a * t < e m := by
    calc
      _ = (a*t) * n := by ring
      _ < (e m / (n:ℝ)) * n := by
        apply mul_lt_mul_of_pos_right _ hn0
        have hdiff := (abs_le.mp (hDiff m le_rfl)).1
        linarith [(lt_min_iff.mp hDsmall).1]
      _ = _ := div_mul_cancel₀ _ hn0.ne'
  obtain ⟨j, hj, hjL, hjR, hCount⟩ := renewal_bracket (he)
    (by rw [he0]; exact mul_nonneg (mul_nonneg hn0.le (ha)) ht.1) hStop
  have hjm : j+1 ≤ m := Nat.succ_le_of_lt hj
  have hrot : (n:ℝ) * a * t = a * t * (n:ℝ) := by ring
  have hL : (e j)/(n:ℝ) ≤ a*t := by
    rw [div_le_iff₀ hn0]
    exact hrot ▸ hjL
  have hR : a*t < (e (j+1))/(n:ℝ) := by
    rw [lt_div_iff₀ hn0]
    exact hrot ▸ hjR
  have hNext : ((j+1:ℕ):ℝ)/(n:ℝ) = (j:ℝ)/n + 1/n := by
    simp [add_div]
  have hNear0 : |(j:ℝ)/n - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hNear1 : |((j+1:ℕ):ℝ)/(n:ℝ) - a*t| < δ/2 := by
    have hdiff1 := abs_le.mp (hDiff j hj.le)
    have hdiff2 := abs_le.mp (hDiff (j+1) hjm)
    rw [hNext] at hdiff2 ⊢
    exact abs_lt.mpr ⟨by linarith [(lt_min_iff.mp hDsmall).2], by linarith [(lt_min_iff.mp hDsmall).2]⟩
  have hLocal (k : ℕ) (hk : k ≤ m) (hh : |(k:ℝ)/n - a*t| < δ/2) :
      |u ((k:ℝ)/n) - u (a*t)| < ε/2 := by
    have hδ : 0 < δ := by linarith [show 0 ≤ 1/(n:ℝ) by positivity]
    exact hMod _ (hDiv k hk) _ hvt (hh.trans (by linarith))
  have hu0 := (abs_lt.mp (hLocal j hj.le hNear0)).1
  have hu1 := (abs_lt.mp (hLocal (j+1) hjm hNear1)).2
  have hupper : ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n ≤ -u ((j:ℝ)/n) := by
    rw [hgrid j (hDiv j hj.le).2, ← neg_div]
    exact div_le_div_of_nonneg_right (by linarith) hsqrt.le
  have hlower : -u (((j+1:ℕ):ℝ)/n) - 1/Real.sqrt n <
      ((j:ℝ) - (n:ℝ)*a*t) / Real.sqrt n := by
    rw [hgrid (j+1) (hDiv (j+1) hjm).2, ← neg_div, ← sub_div]
    apply div_lt_div_of_pos_right _ hsqrt
    push_cast
    linarith
  rw [hCount, ENat.toNat_natCast]
  exact abs_lt.mpr ⟨by linarith, by linarith⟩


private theorem renewal_approximation_prob {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (Y : ℕ → Ω → PathSpace) (Z : Ω' → PathSpace)
    (h : TendstoInDistribution Y atTop Z (fun _ => P) P')
    (q J : ℝ) (hq : 0 < q) (hJ : 0 < J)
    (e : ℕ → Ω → ℕ → ℝ) (he : ∀ n ω, StrictMono (e n ω)) (he0 : ∀ n ω, e n ω 0 = 0)
    (aN : ℕ → ℝ) (haN : ∀ n, 0 ≤ aN n) (T : ℝ) (hT : 0 ≤ T)
    (hH : ∀ᶠ n in atTop, aN n*T+3 ≤ J)
    (hg : ∀ (n : ℕ), 1 ≤ n → ∀ ω (j : ℕ), (j:ℝ)/n ≤ J →
      q*Y n ω (projIcc 0 1 zero_le_one (((j:ℝ)/n)/J)) =
        (e n ω j-j)/Real.sqrt n) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n => P {ω | ∃ t ∈ Icc (0:ℝ) T,
        ε ≤ |(((renewalCount (e n ω) ((n:ℝ)*aN n*t)).toNat:ℝ) - (n:ℝ)*aN n*t)/Real.sqrt n +
          q*Y n ω (projIcc 0 1 zero_le_one (aN n*t/J))|}) atTop (𝓝 0) := by
  intro ε hε
  apply (ENNReal.tendsto_nhds_zero.2)
  intro η hη
  obtain ⟨η',_,hη',hη'E⟩ := ENNReal.lt_iff_exists_real_btwn.1 hη
  have hη0 : 0 < η' := ENNReal.ofReal_pos.1 hη'
  obtain ⟨A,hA,δ,hδ,htight⟩ := continuous_path_tightness Y Z h (ε/(2*q)) η'
    (by positivity) hη0
  have hsq : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hD0 : Tendsto (fun n : ℕ => (q*A)/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  have hN0 : Tendsto (fun n : ℕ => 1/(n:ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have hR0 : Tendsto (fun n : ℕ => 1/Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hsq
  filter_upwards [htight,hH,eventually_ge_atTop (1:ℕ),
    (tendsto_order.1 hD0).2 _ (show 0 < min 1 ((J*δ)/4) by positivity),
    (tendsto_order.1 hN0).2 _ (show 0 < J*δ/4 by positivity),
    (tendsto_order.1 hR0).2 _ (show 0 < ε/4 by positivity)]
    with n hn hnn hn0 hDsm hNsm hRsm
  refine (measure_mono ?_).trans (hn.trans hη'E.le)
  intro ω hω
  by_contra! hbad
  have hSup : ‖Y n ω‖ < A := lt_of_not_ge (fun h => hbad (Or.inl h))
  have hMod (s t : I) (hst : dist s t ≤ δ) : |Y n ω s-Y n ω t| < ε/(2*q) :=
    lt_of_not_ge (fun hh => hbad (Or.inr ⟨s,t,hst,hh⟩))
  let c (s : ℝ) : I := projIcc 0 1 zero_le_one (s/J)
  let u (s : ℝ) := q*Y n ω (c s)
  have hc (s : ℝ) (hs : s ∈ Icc 0 J) : (c s : ℝ) = s/J := by
    have h0 : 0 ≤ s/J := div_nonneg hs.1 hJ.le
    have h1 : s/J ≤ 1 := (div_le_one hJ).2 hs.2
    simp [c,Set.projIcc,max_eq_right h0,min_eq_right h1]
  have hUb (s : ℝ) (_ : s ∈ Icc (0:ℝ) J) : |u s| ≤ q*A := by
    dsimp only [u]
    rw [abs_mul,abs_of_pos hq]
    apply mul_le_mul_of_nonneg_left _ hq.le
    have hN := ContinuousMap.norm_coe_le_norm (Y n ω) (c s)
    rw [Real.norm_eq_abs] at hN
    exact hN.trans hSup.le
  have hUm (s : ℝ) (hs : s ∈ Icc (0:ℝ) J) (t : ℝ) (ht : t ∈ Icc (0:ℝ) J)
      (hh : |s-t| < J*δ) : |u s-u t| < ε/2 := by
    have hd : dist (c s) (c t) ≤ δ := by
      rw [Subtype.dist_eq,Real.dist_eq,hc s hs,hc t ht,← sub_div,abs_div,abs_of_pos hJ]
      exact (div_le_iff₀ hJ).2 (by simpa [mul_comm] using hh.le)
    have h := hMod (c s) (c t) hd
    dsimp only [u]
    rw [← mul_sub,abs_mul,abs_of_pos hq]
    have he : q*(ε/(2*q)) = ε/2 := by field_simp
    exact (mul_lt_mul_of_pos_left h hq).trans_eq he
  obtain ⟨t,ht,hh⟩ := hω
  have hClose := local_renewal_sandwich n hn0 (e n ω) (he n ω) (he0 n ω) u J
    (hg n hn0 ω) (aN n) T (q*A) (J*δ) ε (haN n) hT hnn hUb hDsm hNsm hRsm hε hUm t ht
  exact (not_lt_of_ge hh) hClose

private theorem interp_grid {Ω : Type*} {X : ℕ → Ω → ℝ} {m j : ℕ}
    (hj : j ≤ m) (ω : Ω) :
    walkInterp X m ω j = ∑ i ∈ Finset.range j, X i ω := by
  unfold walkInterp
  rw [← Finset.sum_range_add_sum_Ico _ hj]
  have ha : (∑ i ∈ Finset.range j, X i ω*max 0 (min 1 ((j:ℝ)-i))) =
      ∑ i ∈ Finset.range j, X i ω := by
    apply Finset.sum_congr rfl
    intro i hi
    have hh : (1:ℝ) ≤ (j:ℝ)-i := by
      have hi' : (i:ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.1 hi)
      linarith
    rw [min_eq_left hh,max_eq_right zero_le_one,mul_one]
  have hb : (∑ i ∈ Finset.Ico j m, X i ω*max 0 (min 1 ((j:ℝ)-i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hh : (j:ℝ)-(i:ℝ) ≤ 0 :=
      sub_nonpos.mpr (by exact_mod_cast (Finset.mem_Ico.1 hi).1)
    rw [max_eq_left ((min_le_right _ _).trans hh),mul_zero]
  rw [ha,hb,add_zero]

set_option maxHeartbeats 650000 in
private theorem renewal_grid_algebra {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    (s : ℝ) (hs : 0 < s) (J n : ℕ) (hJ : 0 < J) (hn : 0 < n) :
    ∀ ω (j : ℕ), (j:ℝ)/n ≤ J →
      (s*Real.sqrt (J:ℝ)) *
        walkPath (fun a ω => (M.U i (a+1) ω-1)/s) (J*n) ω
          (projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ))) =
        ((∑ a ∈ Finset.range j,M.U i (a+1) ω)-j)/Real.sqrt n := by
  intro ω j hj
  have hjR : 0 ≤ ((j:ℝ)/n)/(J:ℝ) := by positivity
  have hN : (0:ℝ) < n := by exact_mod_cast hn
  have hJR : (0:ℝ) < J := by exact_mod_cast hJ
  have hJ1 : ((j:ℝ)/n)/(J:ℝ) ≤ 1 := (div_le_one hJR).2 hj
  have hProj : ((projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ)) :
        Icc (0:ℝ) 1) : ℝ) = ((j:ℝ)/n)/(J:ℝ) := by
    simp [Set.projIcc,max_eq_right hjR,min_eq_right hJ1]
  have hIdx : j ≤ J*n := by
    exact_mod_cast ((div_le_iff₀ hN).1 hj)
  have hMul : ((J*n:ℕ):ℝ)*(((j:ℝ)/n)/(J:ℝ)) = j := by
    push_cast
    field_simp
  let X (a : ℕ) (ω : Ω) := (M.U i (a+1) ω-1)/s
  change s*Real.sqrt (J:ℝ) * (walkInterp X (J*n) ω
    (((J*n:ℕ):ℝ) * ((projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ)) : Icc (0:ℝ) 1):ℝ)) /
    Real.sqrt ((J*n:ℕ):ℝ)) = _
  rw [hProj,hMul,interp_grid hIdx,Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg J)]
  simp only [X,← Finset.sum_div,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_one]
  field_simp [(Real.sqrt_pos.2 hN).ne',(Real.sqrt_pos.2 hJR).ne',hs.ne']
  <;> ring

private theorem renewal_epoch_walk_donsker_and_zero_variance {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k)
    {P' : Measure Ω'} [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω)) :
    letI : IsProbabilityMeasure M.P := M.isProb
    (0 < M.cU2 i →
      TendstoInDistribution (fun n : ℕ =>
        walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) n)
        atTop (brownianPath B) (fun _ => M.P) P') ∧
    (M.cU2 i = 0 → ∀ᵐ ω ∂M.P, ∀ j : ℕ, M.U i (j+1) ω = 1) := by
  letI : IsProbabilityMeasure M.P := M.isProb
  let g : ℕ → (Fin k × ℕ) ⊕ (Fin k ⊕ Fin k) := fun j => Sum.inl (i,j)
  have hg : Function.Injective g := fun _ _ h => congrArg Prod.snd (Sum.inl.inj h)
  have hiU : iIndepFun (fun j => M.U i (j+1)) M.P := (M.indep 0).precomp hg
  have hId (j : ℕ) : IdentDistrib (M.U i (j+1)) (M.U i 1) M.P M.P :=
    M.U_ident i (j+1) (by omega)
  have hMeas (j : ℕ) : Measurable (M.U i (j+1)) := M.U_meas _ _
  constructor
  · intro hσ
    let s := Real.sqrt (M.cU2 i)
    let Y (j : ℕ) (ω : Ω) := (M.U i (j+1) ω-1)/s
    have hs : 0 < s := Real.sqrt_pos.2 hσ
    have hY (j : ℕ) : Measurable (Y j) := ((hMeas j).sub_const 1).div_const s
    have hid (j : ℕ) : IdentDistrib (Y j) (Y 0) M.P M.P :=
      (hId j).comp ((measurable_id.sub_const 1).div_const s)
    have hind : iIndepFun Y M.P :=
      hiU.comp (fun _ (x:ℝ) => (x-1)/s) (fun _ => (measurable_id.sub_const 1).div_const s)
    have hmem := (M.U_memLp i).sub (memLp_const (1:ℝ) : MemLp (fun _ : Ω => (1:ℝ)) 2 M.P)
    have hy2 : MemLp (Y 0) 2 M.P := by
      have h := hmem.const_mul (1/s)
      convert h using 1
      funext ω
      simp [Y,div_eq_mul_inv,mul_comm]
    have hy0 : ∫ ω, Y 0 ω ∂M.P = 0 := by
      change (∫ ω, (M.U i 1 ω-1)/s ∂M.P) = 0
      rw [integral_div,integral_sub ((M.U_memLp i).integrable one_le_two) (integrable_const 1),
        M.U_mean]
      simp
    have hvar : ∫ ω, Y 0 ω^2 ∂M.P = 1 := by
      change (∫ ω, ((M.U i 1 ω-1)/s)^2 ∂M.P) = 1
      simp_rw [div_pow]
      rw [integral_div,Real.sq_sqrt hσ.le,div_eq_one_iff_eq hσ.ne']
      rw [SystemSequence.cU2, variance_eq_integral (M.U_meas i 1).aemeasurable, M.U_mean]
    exact DurrettProbability.donsker hY hind hid hy2.integrable_sq hy0 hvar hB hBc
  · intro hzero
    have he : evariance (M.U i 1) M.P = 0 := by
      have hne := (M.U_memLp i).evariance_ne_top
      exact ((ENNReal.toReal_eq_zero_iff _).1 hzero).resolve_right hne
    have hAE : M.U i 1 =ᵐ[M.P] fun _ => 1 := by
      simpa only [M.U_mean] using (evariance_eq_zero_iff (M.U_meas i 1).aemeasurable).1 he
    refine ae_all_iff.2 (fun j => ?_)
    have hl : M.P.map (M.U i 1) = Measure.dirac (1:ℝ) := by
      rw [Measure.map_congr hAE, Measure.map_const, measure_univ, one_smul]
    exact (show HasLaw (M.U i (j+1)) (Measure.dirac (1:ℝ)) M.P from
      ⟨(hMeas j).aemeasurable,(hId j).map_eq.trans hl⟩).ae_eq_of_dirac

private theorem epoch_sum_eq {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (i : Fin k) (ω : Ω) (m : ℕ) :
    ∑ j ∈ range m, M.U i (j+1) ω = partialSum (fun j => M.U i j ω) m := by
  unfold partialSum
  rw [show Finset.Icc 1 m = Finset.Ico 1 (m+1) from by ext; simp,
    Finset.sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, add_comm]

private theorem renewal_on_rate_clock {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (i : Fin k) (ω : Ω) (s : ℝ) :
    M.A n i ω s =
      ((renewalCount (fun j => ∑ l ∈ range j, M.U i (l+1) ω) (M.lamN n i * s)).toNat : ℝ) := by
  have heq (j : ℕ) : M.arrivalEpoch n i ω j = (∑ l ∈ range j, M.U i (l+1) ω) / M.lamN n i := by
    rw [epoch_sum_eq]
    simp [SystemSequence.arrivalEpoch, partialSum, Finset.sum_div]
  unfold SystemSequence.A renewalCount
  simp only [heq, div_le_iff₀ (M.lamN_pos n i), mul_comm s]


open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy DurrettProbability
open Filter Topology MeasureTheory ProbabilityTheory Set Finset
open scoped NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem solution {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {k : ℕ} (M : SystemSequence Ω k) (i : Fin k) (hVar : 0 < M.cU2 i)
    (P' : Measure Ω') [IsProbabilityMeasure P'] {B : ℝ≥0 → Ω' → ℝ}
    (hB : IsBrownianReal B P') (hBc : ∀ ω, Continuous (fun t => B t ω))
    (T : ℝ) (hT : 0 ≤ T) (J : ℕ) (hJ : (M.lam i + 1)*T+3 ≤ J) :
    ∀ ε : ℝ, 0 < ε →
      Tendsto (fun n : ℕ => M.P {ω | ∃ t ∈ Icc (0:ℝ) T, ε ≤
        |M.Ahat n ω t i + (Real.sqrt (M.cU2 i)*Real.sqrt (J:ℝ)) *
          walkPath (fun j ω => (M.U i (j+1) ω-1)/Real.sqrt (M.cU2 i)) (J*n) ω
          (projIcc 0 1 zero_le_one ((M.lamN n i/n)*t/(J:ℝ)))|}) atTop (𝓝 0) := by
  let : IsProbabilityMeasure M.P := M.isProb
  let aN (n : ℕ) := M.lamN n i / n
  let s := Real.sqrt (M.cU2 i)
  have hs : 0 < s := Real.sqrt_pos.2 hVar
  have hJlo : 0 < (M.lam i+1)*T+3 :=
    add_pos_of_nonneg_of_pos (mul_nonneg (by linarith [M.lam_pos i]) hT) (by norm_num)
  have hJr : (0:ℝ) < J := hJlo.trans_le hJ
  have hJn : 0 < J := by exact_mod_cast hJr
  have hcoef : 0 < s*Real.sqrt (J:ℝ) := mul_pos hs (Real.sqrt_pos.2 hJr)
  let Y (n : ℕ) := walkPath (fun j ω => (M.U i (j+1) ω-1)/s) (J*n)
  have hDon := (renewal_epoch_walk_donsker_and_zero_variance M i hB hBc).1 hVar
  have hR : Tendsto (fun n : ℕ => J*n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) tendsto_id
    change n ≤ J*n
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right n (show 1 ≤ J from hJn)
  have hWeak : TendstoInDistribution Y atTop (brownianPath B) (fun _ => M.P) P' :=
    ⟨fun n => hDon.forall_aemeasurable (J*n),hDon.aemeasurable_limit,hDon.tendsto.comp hR⟩
  let e (_ : ℕ) (ω : Ω) (j : ℕ) := ∑ a ∈ Finset.range j,M.U i (a+1) ω
  have he (n : ℕ) (ω : Ω) : StrictMono (e n ω) := by
    apply strictMono_nat_of_lt_succ
    intro j
    dsimp only [e]
    rw [Finset.sum_range_succ]
    exact lt_add_of_pos_right _ (M.U_pos i (j+1) ω (by omega))
  have he0 (n : ℕ) (ω : Ω) : e n ω 0 = 0 := by simp [e]
  have haN (n : ℕ) : 0 ≤ aN n := div_nonneg (M.lamN_pos n i).le (Nat.cast_nonneg _)
  have hH : ∀ᶠ n in atTop, aN n*T+3 ≤ (J:ℝ) := by
    filter_upwards [(tendsto_order.1 (M.lam_lim i)).2 _ (by linarith : M.lam i < M.lam i+1)]
      with n hn
    exact (add_le_add_left (mul_le_mul_of_nonneg_right hn.le hT) _).trans hJ
  have hg (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (j : ℕ) (hj : (j:ℝ)/n ≤ (J:ℝ)) :
      (s*Real.sqrt (J:ℝ))*Y n ω (projIcc 0 1 zero_le_one (((j:ℝ)/n)/(J:ℝ))) =
      (e n ω j-j)/Real.sqrt n :=
    renewal_grid_algebra M i s hs J n hJn hn ω j hj
  have hA (n : ℕ) (hn : 1 ≤ n) (ω : Ω) (t : ℝ) :
      M.Ahat n ω t i =
      (((renewalCount (e n ω) ((n:ℝ)*aN n*t)).toNat:ℝ) - (n:ℝ)*aN n*t)/Real.sqrt n := by
    have hR : (0:ℝ) < n := by exact_mod_cast hn
    have hScale : ((n:ℝ)*aN n*t) = M.lamN n i*t := by dsimp [aN]; field_simp
    unfold SystemSequence.Ahat
    rw [hScale,renewal_on_rate_clock M n i ω t]
  have hProb := renewal_approximation_prob Y (brownianPath B) hWeak (s*Real.sqrt (J:ℝ)) J
    hcoef hJr e he he0 aN haN T hT hH hg
  intro ε hε
  refine (hProb ε hε).congr' ?_
  filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
  apply congrArg M.P
  ext ω
  simp only [Set.mem_setOf_eq, hA n hn ω]
  rfl
