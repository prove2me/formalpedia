-- Prove2me | solution 1 for ManyServerQED.Scheduling.weighted_arctangent_time_compression_transfers_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T03:06:37.822125+00:00
-- url     : https://prove2.me/submissions/004662c8-f9a0-4085-a01a-2ffe7f230ac0

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_Reiman84_QueueLength_Paths

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open BellWilliams2001.ThresholdPolicy Reiman84.QueueLength

private noncomputable def compressedTime (s : ℝ) : ℝ := s/(1-s)
private noncomputable def timeLeft (s : ℝ) : ℝ := max 0 (1-s)
private noncomputable def unitEmbed (t : ℝ) : ℝ := max t 0/(1+max t 0)
private noncomputable def unweight (t : ℝ) : ℝ := 1+max t 0

private noncomputable def arctanVector {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun i => Real.arctan (x i)

private noncomputable def compactify {k : ℕ} (x : ℝ → Fin k → ℝ) (s : ℝ) :
    Fin k → ℝ := timeLeft s • arctanVector (x (compressedTime s))

private theorem continuous_arctanVector {k : ℕ} : Continuous (arctanVector (k := k)) :=
  continuous_pi (fun i => Real.continuous_arctan.comp (continuous_apply i))

private theorem norm_arctanVector {k : ℕ} (x : Fin k → ℝ) :
    ‖arctanVector x‖ ≤ Real.pi/2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ Real.pi/2)).2
  intro i
  rw [Real.norm_eq_abs]
  exact (abs_lt.2 (Real.arctan_mem_Ioo (x i))).le

private theorem arctanVector_lip {k : ℕ} (x y : Fin k → ℝ) :
    ‖arctanVector x-arctanVector y‖ ≤ ‖x-y‖ := by
  have h : LipschitzWith 1 Real.arctan := by
    apply lipschitzWith_of_nnnorm_deriv_le Real.differentiable_arctan
    intro x
    change ((‖deriv Real.arctan x‖₊ : ℝ) ≤ 1)
    rw [coe_nnnorm,Real.deriv_arctan,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    exact (div_le_one (show (0:ℝ) < 1+x^2 by positivity)).2
      (le_add_of_nonneg_right (sq_nonneg x))
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg (x-y))).2
  intro i
  have hh := h.dist_le_mul (x i) (y i)
  simpa only [arctanVector,Real.norm_eq_abs,Real.dist_eq,NNReal.coe_one,one_mul,Pi.sub_apply] using
    hh.trans (by simpa only [Real.dist_eq,Real.norm_eq_abs,NNReal.coe_one,one_mul,Pi.sub_apply] using
      norm_le_pi_norm (x-y) i)

private theorem continuousAt_compressedTime {s : ℝ} (hs : s < 1) :
    ContinuousAt compressedTime s :=
  continuous_id.continuousAt.div (continuous_const.sub continuous_id).continuousAt (by linarith)

private theorem continuous_timeLeft : Continuous timeLeft :=
  continuous_const.max (continuous_const.sub continuous_id)

private theorem timeLeft_eq {s : ℝ} (hs : s ≤ 1) : timeLeft s = 1-s :=
  max_eq_right (sub_nonneg.2 hs)

private theorem compressedTime_nonneg {s : ℝ} (hs : s ∈ Icc (0:ℝ) 1) :
    0 ≤ compressedTime s := div_nonneg hs.1 (sub_nonneg.2 hs.2)

private theorem compressedTime_mono : StrictMonoOn compressedTime (Ico (0:ℝ) 1) := by
  intro s hs t ht hst
  apply (div_lt_div_iff₀ (sub_pos.2 hs.2) (sub_pos.2 ht.2)).2
  nlinarith only [hst]

private theorem continuous_unitEmbed : Continuous unitEmbed := by
  have hM : Continuous (fun t : ℝ => max t 0) := continuous_id.max continuous_const
  exact hM.div (continuous_const.add hM) (fun t => by positivity)

private theorem unitEmbed_bounds {t : ℝ} (ht : 0 ≤ t) : unitEmbed t ∈ Ico (0:ℝ) 1 := by
  dsimp [unitEmbed]
  rw [max_eq_left ht]
  exact ⟨div_nonneg ht (by positivity),(div_lt_one (by positivity)).2 (by linarith)⟩

private theorem unitEmbed_mono : StrictMonoOn unitEmbed (Ici 0) := by
  intro s hs t ht hst
  unfold unitEmbed
  rw [max_eq_left hs,max_eq_left ht]
  apply (div_lt_div_iff₀ (by linarith [show 0 ≤ s from hs] : 0 < 1+s) (by linarith [show 0 ≤ t from ht] : 0 < 1+t)).2
  nlinarith only [hst]

private theorem compactify_inverse {k : ℕ} (f : ℝ → Fin k → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    unweight t • compactify f (unitEmbed t) = arctanVector (f t) := by
  have h := unitEmbed_bounds ht
  have hl : 1-unitEmbed t = (1+t)⁻¹ := by
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
    ring
  have hC : compressedTime (unitEmbed t) = t := by
    unfold compressedTime
    rw [hl]
    unfold unitEmbed
    rw [max_eq_left ht]
    field_simp
  simp only [compactify, hC,timeLeft_eq h.2.le,hl,smul_smul,unweight,max_eq_left ht]
  rw [mul_inv_cancel₀ (by positivity : 1+t ≠ 0),one_smul]

private theorem norm_compactify {k : ℕ} (f : ℝ → Fin k → ℝ) {s : ℝ}
    (hs : s ≤ 1) : ‖compactify f s‖ ≤ (1-s)*(Real.pi/2) := by
  rw [compactify,norm_smul,timeLeft_eq hs,Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.2 hs)]
  exact mul_le_mul_of_nonneg_left (norm_arctanVector _) (sub_nonneg.2 hs)

private theorem compactify_one {k : ℕ} (f : ℝ → Fin k → ℝ) : compactify f 1 = 0 := by
  simp [compactify,timeLeft]

private theorem compactified_diff_le {k : ℕ} (x : ℝ → Fin k → ℝ) {s t : ℝ}
    (hs : s ∈ Icc (0:ℝ) 1) (ht : t ∈ Icc (0:ℝ) 1) :
    ‖compactify x s-compactify x t‖ ≤ ‖x (compressedTime s)-x (compressedTime t)‖
      + |s-t| *(Real.pi/2) := by
  let u := arctanVector (x (compressedTime s))
  let v := arctanVector (x (compressedTime t))
  rw [compactify, compactify,timeLeft_eq hs.2,timeLeft_eq ht.2]
  change ‖(1-s) • u-(1-t) • v‖ ≤ _
  have he : (1-s) • u-(1-t) • v = (1-s) • (u-v)+(t-s) • v := by
    module
  rw [he]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_sub_comm t s,
    abs_of_nonneg (sub_nonneg.2 hs.2)]
  apply add_le_add
  · exact (mul_le_of_le_one_left (norm_nonneg _) (by linarith [hs.1])).trans
      (arctanVector_lip _ _)
  · exact mul_le_mul_of_nonneg_left (norm_arctanVector _) (abs_nonneg _)

theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {k : ℕ}
    (X : ℕ → Ω → ℝ → Fin k → ℝ)
    (h : ∀ (T : ℕ) (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖X n ω s-X n ω t‖} ≤ ENNReal.ofReal η) :
    let z (n : ℕ) (ω : Ω) (s : ℝ) := max 0 (1-s) • (fun i => Real.arctan (X n ω (s/(1-s)) i))
    ∀ (ε η : ℝ), 0 < ε → 0 < η → ∃ δ > 0, ∀ᶠ n in atTop,
      P {ω | ∃ s ∈ Icc (0:ℝ) 1, ∃ t ∈ Icc (0:ℝ) 1, |s-t| ≤ δ ∧
        ε ≤ ‖z n ω s-z n ω t‖} ≤ ENNReal.ofReal η := by
  intro z ε η hε hη
  let C := Real.pi/2
  have hC : 0 < C := by dsimp [C]; positivity
  let a := min (1/4) (ε/(16*(C+1)))
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha' : a ≤ 1/4 := min_le_left _ _
  have hsmall : 4*a*C < ε := by
    have h0 := (le_div_iff₀ (show 0 < 16*(C+1) by positivity)).1 (min_le_right (1/4:ℝ) (ε/(16*(C+1))))
    nlinarith [mul_pos ha hC,hε]
  obtain ⟨T,hT⟩ := exists_nat_gt (1/a)
  obtain ⟨d,hd,hN⟩ := h T (ε/2) η (by positivity) hη
  let δ := min a (d*a*a)
  have hδ : 0 < δ := lt_min ha (by positivity)
  refine ⟨δ,hδ,?_⟩
  filter_upwards [hN] with n hn
  refine (measure_mono ?_).trans hn
  rintro ω ⟨s,hs,t,ht,hst,hBad⟩
  have hx : z n ω = compactify (X n ω) := rfl
  rw [hx] at hBad
  have hδa : |s-t| ≤ a := hst.trans (min_le_left _ _)
  have hδd : |s-t| ≤ d*a*a := hst.trans (min_le_right _ _)
  have hClose : 1-a ≤ s ∨ 1-a ≤ t → False := by
    intro hST
    have hab := abs_le.1 hδa
    have hsA : 1-2*a ≤ s := by rcases hST with h | h <;> linarith
    have htA : 1-2*a ≤ t := by rcases hST with h | h <;> linarith
    have hDiff := (norm_sub_le (compactify (X n ω) s) _).trans
      (add_le_add (norm_compactify (X n ω) hs.2) (norm_compactify (X n ω) ht.2))
    change ‖compactify (X n ω) s-compactify (X n ω) t‖ ≤ (1-s)*C+(1-t)*C at hDiff
    have hsN : (1-s)*C ≤ 2*a*C :=
      mul_le_mul_of_nonneg_right (by linarith) hC.le
    have htN : (1-t)*C ≤ 2*a*C :=
      mul_le_mul_of_nonneg_right (by linarith) hC.le
    linarith only [hBad,hDiff,hsN,htN,hsmall]
  have hsD : a ≤ 1-s := by linarith [lt_of_not_ge (fun h => hClose (Or.inl h))]
  have htD : a ≤ 1-t := by linarith [lt_of_not_ge (fun h => hClose (Or.inr h))]
  have hsP : 0 < 1-s := ha.trans_le hsD
  have htP : 0 < 1-t := ha.trans_le htD
  have hTime (r : ℝ) (hr : r ∈ Icc (0:ℝ) 1) (hrA : a ≤ 1-r) :
      compressedTime r ∈ Icc (0:ℝ) (T:ℝ) := by
    refine ⟨compressedTime_nonneg hr,(le_trans ?_ hT.le)⟩
    unfold compressedTime
    exact (div_le_div_of_nonneg_right hr.2 ((ha.trans_le hrA).le)).trans
      (div_le_div_of_nonneg_left zero_le_one ha hrA)
  have hDen : a*a ≤ (1-s)*(1-t) := mul_le_mul hsD htD ha.le hsP.le
  have hAlgo : compressedTime s-compressedTime t = (s-t)/((1-s)*(1-t)) := by
    unfold compressedTime
    field_simp [hsP.ne',htP.ne']
    ring
  refine ⟨compressedTime s,hTime s hs hsD,compressedTime t,hTime t ht htD,?_,?_⟩
  · rw [hAlgo,abs_div,abs_of_pos (mul_pos hsP htP)]
    exact (div_le_iff₀ (mul_pos hsP htP)).2
      (hδd.trans (by rw [mul_assoc]; exact mul_le_mul_of_nonneg_left hDen hd.le))
  · have hEst := compactified_diff_le (X n ω) hs ht
    have hErr : |s-t| *C ≤ a*C := mul_le_mul_of_nonneg_right hδa hC.le
    change ‖compactify (X n ω) s-compactify (X n ω) t‖ ≤
      ‖X n ω (compressedTime s)-X n ω (compressedTime t)‖+|s-t| *C at hEst
    linarith only [hEst,hErr,hBad,hsmall,mul_pos ha hC,hε]
