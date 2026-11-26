-- Prove2me | solution 1 for ManyServerQED.Scheduling.joint_queue_hjb_observation_asymptotic_interval_modulus
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T04:43:34.375409+00:00
-- url     : https://prove2.me/submissions/edd45013-cba8-4be7-98fd-deabf9d66fca

import Definitions.Def_ManyServerQED_Scheduling_QueueHJBCompactPath
import Theorems.Thm_ManyServerQED_Scheduling_queue_hjb_row_integral_paths
import Theorems.Thm_ManyServerQED_Scheduling_queue_effective_noise_asymptotic_interval_modulus
import Theorems.Thm_ManyServerQED_Scheduling_queue_diffusion_drift_remainder_uoc
import Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment
import Theorems.Thm_ManyServerQED_Scheduling_finite_coordinate_modulus_controls_vector_modulus
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

set_option maxHeartbeats 2100000 in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU)
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (X Ψ : ℕ → Ω → ℝ → Fin k → ℝ)
    (hpol : ∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧
      M.IsAdmissible n (X n) (Ψ n) ∧ IsWorkConserving n (X n) (Ψ n))
    (f : (Fin k → ℝ) → ℝ) (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (T : ℕ) (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
    let Z := queueHJBObservation M (costOfTilde Lt) γ u0 f X Ψ
    ∃ δ > 0, ∀ᶠ n in atTop,
      M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
        ε ≤ ‖Z n ω s-Z n ω t‖} ≤ ENNReal.ofReal η := by
  intro Z
  let ctl (n : ℕ) (h : 1 ≤ n) := (hpol n h).1.controlled
  let work (n : ℕ) (h : 1 ≤ n) := (hpol n h).2.2
  let Y := fun (n : ℕ) => M.Xhat n (X n)
  let D := M.diffData
  let W (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    (M.Ahat n ω t i-M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i-
      M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i)/D.r i
  let A (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    Z n ω t (Fin.castAdd 2 (Fin.natAdd (k+k) i))
  let E (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :=
    Y n ω t i-M.Xhat0 n (X0 n) i-D.r i*W n ω t i-A n ω t i
  have hQ : ∀ n, 1 ≤ n → ∀ ω t i, 0 ≤ t →
      X n ω t i-Ψ n ω t i ≤ max ((∑ j, X n ω t j)-n) 0 := by
    intro n hn ω t i ht
    rw [work n hn ω t ht]
    exact Finset.single_le_sum (fun j _ => (ctl n hn).phi_nonneg ω t j ht) (Finset.mem_univ i)
  have hC := controlled_compact_containment M X0 x hX0 X Ψ ctl hQ T (Nat.cast_nonneg _)
  have hA := (queue_hjb_row_integral_paths M Lt γ ϱ mL hA2 u0 hu0 f hHJB X Ψ X0
    (fun n hn => (hpol n hn).1) work).2
  have hR := queue_diffusion_drift_remainder_uoc M X0 x hX0 X Ψ ctl work u0
  have hR' : UocInProb M.P E (fun _ => 0) := by
    have he (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
        D.r i * W n ω t i = M.Ahat n ω t i -
          M.Rhat n ω (queueTime (X n) (Ψ n) ω i t/(n:ℝ)) i -
          M.Shat n ω (busyTime (Ψ n) ω i t/(n:ℝ)) i := by
      dsimp [W,D]
      field_simp [(M.diffData.r_pos i).ne']
      ring
    have ha (n : ℕ) (ω : Ω) (t : ℝ) (i : Fin k) :
        A n ω t i = ∫ s in (0:ℝ)..t, drift D (Y n ω s)
          (uProc n u0 (X n) (Ψ n) ω s) i := by
      simp only [A,Z,queueHJBObservation,Fin.append_left,Fin.append_right]
      rfl
    simpa only [E,he,ha,Y,D] using hR
  have hW (i : Fin k) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
      ∃ δ > 0, ∀ᶠ n in atTop,
        M.P {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ δ ∧
          a ≤ |W n ω s i-W n ω t i|} ≤ ENNReal.ofReal b :=
    queue_effective_noise_asymptotic_interval_modulus M mL mU hA3 X0 x hX0 X Ψ ctl work i T a b ha hb
  refine finite_coordinate_modulus_controls_vector_modulus M.P Z T ?_ ε η hε hη
  intro l a b ha hb
  let EMod (v : ℕ → Ω → ℝ → ℝ) (d' : ℝ) (n : ℕ) : Set Ω :=
    {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ), |s-t| ≤ d' ∧
      a ≤ |v n ω s-v n ω t|}
  have hInt (v : ℕ → Ω → ℝ → ℝ)
      (hv : ∀ C : ℝ, ∃ L > 0, ∀ n, 1 ≤ n → ∀ ω,
        (∀ t ∈ Icc (0:ℝ) (T:ℝ), ‖Y n ω t‖ ≤ C) →
        ∀ s ∈ Icc (0:ℝ) (T:ℝ), ∀ t ∈ Icc (0:ℝ) (T:ℝ),
          |v n ω s-v n ω t| ≤ L*|s-t|) :
      ∃ δ > 0, ∀ᶠ n in atTop, M.P (EMod v δ n) ≤ ENNReal.ofReal b := by
    obtain ⟨C,hC0,hC'⟩ := hC (ENNReal.ofReal b) (ENNReal.ofReal_pos.2 hb)
    obtain ⟨L,hL,hV⟩ := hv C
    let δ := a/(2*L)
    have hδ : 0 < δ := by dsimp [δ]; positivity
    refine ⟨δ,hδ,?_⟩
    filter_upwards [eventually_ge_atTop 1,hC'] with n hn hnC
    refine (measure_mono ?_).trans hnC.le
    rintro ω ⟨s,hs,t,ht,hst,he⟩
    by_contra h
    have hh := hV n hn ω (fun t ht => le_of_not_gt (fun h' => h ⟨t,ht,h'⟩)) s hs t ht
    have hδL : L*δ = a/2 := by dsimp [δ]; field_simp [hL.ne']
    have hD := mul_le_mul_of_nonneg_left hst hL.le
    linarith
  have hY (i : Fin k) : ∃ δ > 0, ∀ᶠ n in atTop,
      M.P (EMod (fun n ω t => Y n ω t i) δ n) ≤ ENNReal.ofReal b := by
    let c := b/3
    have hc : 0 < c := by dsimp [c]; positivity
    let r := D.r i
    have hr : 0 < r := D.r_pos i
    obtain ⟨C,_,hC'⟩ := hC (ENNReal.ofReal c) (ENNReal.ofReal_pos.2 hc)
    obtain ⟨L,hL,hA'⟩ := hA T C
    obtain ⟨δW,hδW,hW'⟩ := hW i (a/(4*r)) c (by positivity) hc
    let δ := min δW (a/(4*L))
    refine ⟨δ,lt_min hδW (by positivity),?_⟩
    have hE' := (tendsto_order.1 (hR' T (Nat.cast_nonneg _) (a/4) (by positivity))).2
      (ENNReal.ofReal c) (ENNReal.ofReal_pos.2 hc)
    filter_upwards [eventually_ge_atTop 1,hC',hW',hE'] with n hn hnC hnW hnE
    let B₀ : Set Ω := {ω | ∃ t ∈ Icc (0:ℝ) (T:ℝ), C < ‖Y n ω t‖}
    let B₁ : Set Ω := {ω | ∃ s ∈ Icc (0:ℝ) (T:ℝ), ∃ t ∈ Icc (0:ℝ) (T:ℝ),
      |s-t| ≤ δW ∧ a/(4*r) ≤ |W n ω s i-W n ω t i|}
    let B₂ : Set Ω := {ω | ENNReal.ofReal (a/4) ≤ supDist (E n ω) (fun _ => 0) T}
    have hsum : M.P ((B₀ ∪ B₁) ∪ B₂) ≤ ENNReal.ofReal b := by
      refine (measure_union_le _ _).trans ((add_le_add (measure_union_le _ _) le_rfl).trans ?_)
      refine (add_le_add (add_le_add hnC.le hnW) hnE.le).trans_eq ?_
      rw [← ENNReal.ofReal_add hc.le hc.le,← ENNReal.ofReal_add (add_nonneg hc.le hc.le) hc.le]
      congr 1
      dsimp [c]
      ring
    refine (measure_mono ?_).trans hsum
    rintro ω ⟨s,hs,t,ht,hst,he⟩
    by_contra hh
    have hB (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T:ℝ)) : ‖Y n ω t‖ ≤ C :=
      le_of_not_gt fun h => hh (Or.inl (Or.inl ⟨t,ht,h⟩))
    have hB₁ : |W n ω s i-W n ω t i| < a/(4*r) :=
      lt_of_not_ge fun h => hh (Or.inl (Or.inr ⟨s,hs,t,ht,hst.trans (min_le_left _ _),h⟩))
    have hB₂ (t : ℝ) (ht : t ∈ Icc (0:ℝ) (T:ℝ)) : |E n ω t i| < a/4 := by
      by_contra! h
      apply hh
      right
      refine (ENNReal.ofReal_le_ofReal (h.trans ?_)).trans
        (le_iSup_of_le t (le_iSup_of_le ht le_rfl))
      simpa only [Pi.zero_apply,sub_zero] using
        (Finset.single_le_sum (f := fun i => |E n ω t i|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
    have hA'' : |A n ω s i-A n ω t i| ≤ L*|s-t| := by
      simpa only [A,Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
        (hA' n hn ω hB s hs t ht).1 i
    have hA₀ : |A n ω s i-A n ω t i| ≤ a/4 := by
      have h := mul_le_mul_of_nonneg_left (hst.trans (min_le_right δW (a/(4*L)))) hL.le
      have he : L*(a/(4*L)) = a/4 := by field_simp [hL.ne']
      exact hA''.trans (h.trans_eq he)
    have hW₀ : |r*(W n ω s i-W n ω t i)| < a/4 := by
      rw [abs_mul,abs_of_nonneg hr.le]
      have h := mul_lt_mul_of_pos_left hB₁ hr
      have he : r*(a/(4*r)) = a/4 := by field_simp [hr.ne']
      exact h.trans_eq he
    have heq : Y n ω s i-Y n ω t i = (r*(W n ω s i-W n ω t i)+
        (A n ω s i-A n ω t i))+(E n ω s i-E n ω t i) := by
      dsimp [E,r]
      ring
    rw [heq] at he
    have hle := abs_add_le (r*(W n ω s i-W n ω t i)+
      (A n ω s i-A n ω t i)) (E n ω s i-E n ω t i)
    have h₁ := abs_add_le (r*(W n ω s i-W n ω t i)) (A n ω s i-A n ω t i)
    have h₂ := abs_sub (E n ω s i) (E n ω t i)
    linarith [hB₂ s hs,hB₂ t ht]
  cases l using Fin.addCases with
  | right j =>
    fin_cases j
    · apply hInt
      intro C
      obtain ⟨L,hL,h⟩ := hA T C
      exact ⟨L,hL,fun n hn ω hC s hs t ht => by
        simpa only [Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
          (h n hn ω hC s hs t ht).2.1⟩
    · apply hInt
      intro C
      obtain ⟨L,hL,h⟩ := hA T C
      exact ⟨L,hL,fun n hn ω hC s hs t ht => by
        simpa only [Z,queueHJBObservation,Fin.append_right,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_zero',Matrix.cons_val_succ'] using
          (h n hn ω hC s hs t ht).2.2⟩
  | left j =>
    cases j using Fin.addCases with
    | right i =>
      apply hInt
      intro C
      obtain ⟨L,hL,h⟩ := hA T C
      exact ⟨L,hL,fun n hn ω hC s hs t ht => by
        simpa only [Z,queueHJBObservation,Fin.append_left,Fin.append_right] using
          (h n hn ω hC s hs t ht).1 i⟩
    | left j =>
      cases j using Fin.addCases with
      | left i => simpa only [Z,queueHJBObservation,Fin.append_left,Y] using hY i
      | right i => simpa only [Z,queueHJBObservation,Fin.append_left,Fin.append_right,W,D] using hW i a b ha hb
