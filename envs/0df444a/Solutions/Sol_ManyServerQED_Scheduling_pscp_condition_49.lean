-- Prove2me | solution 1 for ManyServerQED.Scheduling.pscp_condition_49
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:47:09.037798+00:00
-- url     : https://prove2.me/submissions/1d09b7b8-dff3-48a5-a916-ac36587af3a8

import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_controlled_compact_containment

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling BellWilliams2001.ThresholdPolicy

private def excess {k : ℕ} (x : Fin k → ℝ) : ℝ := max (∑ i, x i) 0

private noncomputable def objective {k : ℕ} (D : DiffusionData k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (f : (Fin k → ℝ) → ℝ) (p : (Fin k → ℝ) × (Fin k → ℝ)) : ℝ :=
  (∑ i, (D.ell i + (D.mu i - D.theta i) * p.2 i - D.mu i * p.1 i) * grad f p.1 i)
    + Lt p.2 (p.1 - p.2)

private theorem objective_continuous {k : ℕ} (D : DiffusionData k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f) :
    Continuous (objective D Lt f) := by
  have hgrad (i : Fin k) : Continuous (fun p : (Fin k → ℝ) × (Fin k → ℝ) => grad f p.1 i) :=
    ((hf.1.continuous_fderiv (by norm_num)).clm_apply continuous_const).comp continuous_fst
  unfold objective
  exact (continuous_finsetSum _ fun i _ => by fun_prop).add
    (hA2.tilde_cont.comp (continuous_snd.prodMk (continuous_fst.sub continuous_snd)))

private theorem objective_control {k : ℕ} (D : DiffusionData k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (f : (Fin k → ℝ) → ℝ)
    (x u : Fin k → ℝ) :
    objective D Lt f (x, excess x • u) =
      (∑ i, drift D x u i * grad f x i) + costOfTilde Lt x u := by
  simp only [objective, excess, drift, costOfTilde, Pi.smul_apply, smul_eq_mul, mul_assoc]

private theorem norm_coord {k : ℕ} (x : Fin k → ℝ) (i : Fin k) : |x i| ≤ ‖x‖ := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i

private theorem excess_le {k : ℕ} (x : Fin k → ℝ) : excess x ≤ (k : ℝ) * ‖x‖ := by
  apply max_le
  · calc
      (∑ i, x i) ≤ ∑ _i : Fin k, ‖x‖ :=
        Finset.sum_le_sum fun i _ => (le_abs_self _).trans (norm_coord x i)
      _ = (k : ℝ) * ‖x‖ := by simp
  · positivity

private theorem norm_smul_simplex {k : ℕ} (x u : Fin k → ℝ)
    (hu : u ∈ stdSimplex ℝ (Fin k)) : ‖excess x • u‖ ≤ (k : ℝ) * ‖x‖ := by
  have hz : 0 ≤ excess x := le_max_right _ _
  have hunit : ‖u‖ ≤ 1 := (pi_norm_le_iff_of_nonneg zero_le_one).2 fun i => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hu.1 i)]
    exact (Finset.single_le_sum (fun j _ => hu.1 j) (Finset.mem_univ i)).trans_eq hu.2
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hz]
  exact (mul_le_of_le_one_right hz hunit).trans (excess_le x)

private theorem roundMap_error {k : ℕ} [NeZero k] (y : Fin k → ℝ) :
    ‖roundMap y - y‖ ≤ (k : ℝ) := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne k)
  refine (pi_norm_le_iff_of_nonneg (Nat.cast_nonneg k)).2 fun i => ?_
  simp only [Pi.sub_apply, Real.norm_eq_abs, roundMap]
  split_ifs with hi
  · rw [add_sub_cancel_left, abs_of_nonneg]
    · calc
        (∑ j ∈ Finset.univ.filter (fun j : Fin k => (j : ℕ) + 1 ≠ k), (y j - ⌊y j⌋)) ≤
            ∑ _j ∈ Finset.univ.filter (fun j : Fin k => (j : ℕ) + 1 ≠ k), (1 : ℝ) :=
          Finset.sum_le_sum fun j _ => by linarith [Int.lt_floor_add_one (y j)]
        _ ≤ (k : ℝ) := by
          simpa using (show ((Finset.univ.filter (fun j : Fin k => (j : ℕ) + 1 ≠ k)).card : ℝ) ≤
              (Finset.univ : Finset (Fin k)).card by exact_mod_cast Finset.card_filter_le _ _)
    · exact Finset.sum_nonneg fun j _ => sub_nonneg.mpr (Int.floor_le _)
  · rw [abs_of_nonpos (sub_nonpos.mpr (Int.floor_le _))]
    linarith [Int.lt_floor_add_one (y i)]

private theorem excess_scaled {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (n : ℕ) (hn : 0 < n) (X : Fin k → ℕ) :
    excess (M.Xhat0 n X) = max ((∑ i, (X i : ℝ)) - n) 0 / Real.sqrt n := by
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  unfold excess SystemSequence.Xhat0
  rw [← Finset.sum_div, Finset.sum_sub_distrib,
    ← Finset.sum_mul, show (∑ i, M.rho i) = 1 from M.sum_rho, one_mul]
  conv_lhs => rhs; rw [← zero_div (Real.sqrt (n : ℝ))]
  exact max_div_div_right hs.le _ _

private theorem eventual_feasible {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (B : ℝ) :
    ∀ᶠ n : ℕ in atTop, 0 < n ∧ ∀ X : Fin k → ℕ, ‖M.Xhat0 n X‖ ≤ B →
      ∀ i, max ((∑ j, (X j : ℝ)) - n) 0 ≤ (X i : ℝ) := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
  have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin k,
      ((k : ℝ) + 1) * B ≤ M.rho i * Real.sqrt (n : ℝ) := by
    rw [Filter.eventually_all]
    intro i
    have hp : 0 < M.rho i := div_pos (M.lam_pos i) (M.mu_pos i)
    filter_upwards [(tendsto_atTop.1 hroot) (((k : ℝ) + 1) * B / M.rho i)] with n hn
    exact (div_le_iff₀ hp).1 hn |>.trans_eq (mul_comm _ _)
  filter_upwards [eventually_gt_atTop 0, hall] with n hn hi
  refine ⟨hn, fun X hX i => ?_⟩
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hsq : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (Nat.cast_nonneg _)
  have hxi : -B ≤ M.Xhat0 n X i := by
    have := (norm_coord _ i).trans hX
    linarith [(abs_le.mp this).1]
  have hscale : (X i : ℝ) / Real.sqrt n = M.Xhat0 n X i + M.rho i * Real.sqrt n := by
    unfold SystemSequence.Xhat0
    apply (div_eq_iff hs.ne').2
    rw [add_mul, div_mul_cancel₀ _ hs.ne', mul_assoc, ← sq, hsq]
    ring
  apply (div_le_div_iff_of_pos_right hs).1
  rw [← excess_scaled M n hn X, hscale]
  have hsum := (excess_le (M.Xhat0 n X)).trans (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg k))
  linarith [hi i]

private theorem weighted_control_error {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k) (h : (Fin k → ℝ) → (Fin k → ℝ))
    (u0 : Fin k → ℝ) (n : ℕ) (hn : 0 < n) (X : Ω → ℝ → Fin k → ℕ) (ω : Ω) (t : ℝ)
    (hFeasible : ∀ i, max ((∑ j, (X ω t j : ℝ)) - n) 0 ≤ (X ω t i : ℝ)) :
    let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
    let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => Xr ω t i - M.pscpPhi h n (X ω t) i
    let x := M.Xhat n Xr ω t
    ‖excess x • uProc n u0 Xr Ψ ω t - excess x • h x‖ ≤ (k : ℝ) / Real.sqrt n := by
  dsimp only
  let x := M.Xhat0 n (X ω t)
  let q := (∑ i, (X ω t i : ℝ)) - n
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have he : excess x = max q 0 / Real.sqrt n := excess_scaled M n hn (X ω t)
  change ‖excess x • _ - excess x • h x‖ ≤ _
  by_cases hq : 0 < q
  · have hh : M.pscpPhi h n (X ω t) = roundMap (fun i => q * h x i) := by
      unfold SystemSequence.pscpPhi
      rw [if_pos hFeasible]
      change roundMap (fun i => max q 0 * h x i) = _
      rw [max_eq_left hq.le]
    have hr : (k : ℝ) / Real.sqrt n =
        (Real.sqrt (n : ℝ))⁻¹ * (k : ℝ) := by rw [div_eq_inv_mul]
    rw [hr]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simp only [Pi.sub_apply, Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul]
    rw [he, max_eq_left hq.le]
    unfold uProc
    rw [if_pos hq]
    change |q / Real.sqrt n * (((X ω t i : ℝ) -
      ((X ω t i : ℝ) - M.pscpPhi h n (X ω t) i)) / q) - q / Real.sqrt n * h x i| ≤ _
    rw [sub_sub_cancel, hh]
    have hcalc : q / Real.sqrt n *
        ((roundMap (fun j => q * h x j) i) / q) - q / Real.sqrt n * h x i =
        (Real.sqrt (n : ℝ))⁻¹ * (roundMap (fun j => q * h x j) i - q * h x i) := by
      field_simp [hs.ne', hq.ne']
    rw [hcalc, abs_mul, abs_of_nonneg (inv_nonneg.mpr hs.le)]
    exact mul_le_mul_of_nonneg_left
      ((norm_coord (roundMap (fun j => q * h x j) - fun j => q * h x j) i).trans
        (roundMap_error _)) (inv_nonneg.mpr hs.le)
  · rw [he, max_eq_right (le_of_not_gt hq), zero_div, zero_smul, zero_smul, sub_self, norm_zero]
    positivity

private noncomputable def pscpGap {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (f : (Fin k → ℝ) → ℝ) (h : (Fin k → ℝ) → (Fin k → ℝ))
    (u0 : Fin k → ℝ) (X : Ω → ℝ → Fin k → ℕ) (n : ℕ) (ω : Ω) (t : ℝ) : ℝ :=
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => Xr ω t i - M.pscpPhi h n (X ω t) i
  let x := M.Xhat n Xr ω t
  let u := uProc n u0 Xr Ψ ω t
  (∑ i, drift M.diffData x u i * grad f x i) + costOfTilde Lt x u -
    hamiltonian M.diffData (costOfTilde Lt) x (grad f x)

private theorem gap_on_bounded_states {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL : ℝ) (hA2 : Assumption2 Lt ϱ mL)
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (h : (Fin k → ℝ) → (Fin k → ℝ)) (hh_mem : ∀ y, h y ∈ stdSimplex ℝ (Fin k))
    (hh_min : ∀ y, ∑ i, drift M.diffData y (h y) i * grad f y i + costOfTilde Lt y (h y) =
      hamiltonian M.diffData (costOfTilde Lt) y (grad f y))
    (u0 : Fin k → ℝ) (B ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ (X : Ω → ℝ → Fin k → ℕ) (ω : Ω) (t : ℝ),
      ‖M.Xhat0 n (X ω t)‖ ≤ B → |pscpGap M Lt f h u0 X n ω t| ≤ ε := by
  let R : ℝ := max B ((k : ℝ) * B + 1)
  let C := Metric.closedBall (0 : (Fin k → ℝ) × (Fin k → ℝ)) R
  have hu := (isCompact_closedBall (0 : (Fin k → ℝ) × (Fin k → ℝ)) R).uniformContinuousOn_of_continuous
    (objective_continuous M.diffData Lt ϱ mL hA2 f hf).continuousOn
  obtain ⟨δ, hδ, hunif⟩ := Metric.uniformContinuousOn_iff.mp hu ε hε
  have hsmall : ∀ᶠ n : ℕ in atTop, (k : ℝ) / Real.sqrt n < min δ 1 := by
    have hroot : Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)) atTop atTop :=
      Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop
    have hlim : Tendsto (fun n : ℕ => (k : ℝ) / Real.sqrt n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hroot
    exact (tendsto_order.mp hlim).2 _ (lt_min hδ zero_lt_one)
  filter_upwards [eventual_feasible M B, hsmall] with n hn hs X ω t hX
  let x := M.Xhat0 n (X ω t)
  let Xr : Ω → ℝ → Fin k → ℝ := fun ω t i => X ω t i
  let Ψ : Ω → ℝ → Fin k → ℝ := fun ω t i => Xr ω t i - M.pscpPhi h n (X ω t) i
  let u := uProc n u0 Xr Ψ ω t
  let v := excess x • u
  let w := excess x • h x
  have herr : ‖v - w‖ ≤ (k : ℝ) / Real.sqrt n :=
    weighted_control_error M h u0 n hn.1 X ω t (hn.2 _ hX)
  have hw : ‖w‖ ≤ (k : ℝ) * B := (norm_smul_simplex x (h x) (hh_mem x)).trans
    (mul_le_mul_of_nonneg_left hX (Nat.cast_nonneg k))
  have hv : ‖v‖ ≤ (k : ℝ) * B + 1 := by
    calc
      ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ _ := by linarith [herr.trans (hs.trans_le (min_le_right ..)).le]
  have hc (y : Fin k → ℝ) (hy : ‖y‖ ≤ (k : ℝ) * B + 1) : (x, y) ∈ C := by
    change dist (x, y) 0 ≤ R
    rw [dist_zero_right, Prod.norm_def]
    exact max_le (hX.trans (le_max_left ..)) (hy.trans (le_max_right ..))
  have hd : dist (x, v) (x, w) < δ := by
    rw [Prod.dist_eq, dist_self, dist_eq_norm, max_eq_right (norm_nonneg _)]
    exact herr.trans_lt (hs.trans_le (min_le_left ..))
  have hobj := hunif _ (hc _ hv) _ (hc _ (hw.trans (by linarith))) hd
  change |(∑ i, drift M.diffData x u i * grad f x i) + costOfTilde Lt x u -
    hamiltonian M.diffData (costOfTilde Lt) x (grad f x)| ≤ ε
  rw [← hh_min x, ← objective_control, ← objective_control]
  simpa only [Real.dist_eq] using hobj.le

private theorem pscpPhi_le_excess {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}
    (M : SystemSequence Ω k) (h : (Fin k → ℝ) → (Fin k → ℝ))
    (hh : ∀ x, h x ∈ stdSimplex ℝ (Fin k)) (n : ℕ) (X : Fin k → ℕ) (i : Fin k) :
    M.pscpPhi h n X i ≤ max ((∑ j, (X j : ℝ)) - n) 0 := by
  let q : ℝ := max ((∑ j, (X j : ℝ)) - n) 0
  let x := M.Xhat0 n X
  have hq : 0 ≤ q := le_max_right _ _
  change (if ∀ j, q ≤ (X j : ℝ) then roundMap (fun j => q * h x j)
    else priorityPhi n X) i ≤ q
  split_ifs with hFeasible
  · let y : Fin k → ℝ := fun j => q * h x j
    have hy : ∀ j, 0 ≤ y j := fun j => mul_nonneg hq ((hh x).1 j)
    have hsum : (∑ j, y j) = q := by simp [y, ← Finset.mul_sum, (hh x).2]
    change roundMap y i ≤ q
    refine (show roundMap y i ≤ ∑ j, y j from ?_).trans_eq hsum
    unfold roundMap
    split_ifs with hi
    · have hsplit : Finset.univ.filter (fun j : Fin k => (j : ℕ) + 1 ≠ k) = Finset.univ.erase i := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, and_true]
        exact not_congr ⟨fun hj => Fin.ext (by omega), fun hj => by simpa [hj] using hi⟩
      rw [hsplit, ← Finset.sum_erase_add _ _ (Finset.mem_univ i), add_comm (y i)]
      apply add_le_add_left
      exact Finset.sum_le_sum fun j _ => sub_le_self _ (by
        exact_mod_cast Int.floor_nonneg.mpr (hy j))
    · exact (Int.floor_le _).trans (Finset.single_le_sum (fun j _ => hy j) (Finset.mem_univ i))
  · unfold priorityPhi
    let a : ℝ := (n : ℝ) - ∑ j ∈ Finset.univ.filter (fun j : Fin k => i < j), (X j : ℝ)
    change (X i : ℝ) - min (X i : ℝ) (max a 0) ≤ q
    rcases le_total (X i : ℝ) (max a 0) with h | h
    · rw [min_eq_left h, sub_self]
      exact hq
    · rw [min_eq_right h]
      have htotal : (X i : ℝ) + ∑ j ∈ Finset.univ.filter (fun j : Fin k => i < j), (X j : ℝ) ≤
          ∑ j, (X j : ℝ) := by
        calc
          _ = (∑ j ∈ Finset.univ.filter (fun j : Fin k => i < j), (X j : ℝ)) + (X i : ℝ) :=
            add_comm _ _
          _ ≤ (∑ j ∈ Finset.univ.erase i, (X j : ℝ)) + (X i : ℝ) := by
            apply add_le_add_left
            apply Finset.sum_le_sum_of_subset_of_nonneg
            · intro j hj
              have hj' := (Finset.mem_filter.mp hj).2
              exact Finset.mem_erase.mpr ⟨ne_of_gt hj', Finset.mem_univ j⟩
            · intro j _ _
              positivity
          _ = _ := Finset.sum_erase_add _ _ (Finset.mem_univ i)
      have hmax : a ≤ max a 0 := le_max_left _ _
      have hsum := le_max_left ((∑ j, (X j : ℝ)) - n) 0
      change (∑ j, (X j : ℝ)) - n ≤ q at hsum
      dsimp [a] at hmax ⊢
      linarith

theorem solution {Ω : Type*} [MeasurableSpace Ω] {k : ℕ} [NeZero k]
    (M : SystemSequence Ω k)
    (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (ϱ mL mU γ : ℝ)
    (hA2 : Assumption2 Lt ϱ mL) (hA3 : M.Assumption3 mL mU) (hγ : 0 < γ)
    (f : (Fin k → ℝ) → ℝ) (hf : IsC2Pol f)
    (hHJB : IsHJBSolution M.diffData (costOfTilde Lt) γ f)
    (h : (Fin k → ℝ) → (Fin k → ℝ)) (hh_meas : Measurable h)
    (hh_mem : ∀ y, h y ∈ stdSimplex ℝ (Fin k))
    (hh_min : ∀ y, ∑ i, drift M.diffData y (h y) i * grad f y i + costOfTilde Lt y (h y) =
      hamiltonian M.diffData (costOfTilde Lt) y (grad f y))
    (u0 : Fin k → ℝ) (hu0 : u0 ∈ stdSimplex ℝ (Fin k))
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Xs : ℕ → Ω → ℝ → Fin k → ℕ)
    (hXs : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (fun ω t i => (Xs n ω t i : ℝ))
      (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) :
    UocInProb M.P
      (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
              (uProc n u0 (fun ω t i => (Xs n ω t i : ℝ))
                (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω s) i *
            grad f (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s) i +
          costOfTilde Lt (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
            (uProc n u0 (fun ω t i => (Xs n ω t i : ℝ))
              (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)
            (grad f (M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω s)))])
      (fun _ => 0) := by
  let X : ℕ → Ω → ℝ → Fin k → ℝ := fun n ω t i => Xs n ω t i
  let Ψ : ℕ → Ω → ℝ → Fin k → ℝ := fun n ω t i => X n ω t i - M.pscpPhi h n (Xs n ω t) i
  let K : ℕ → Ω → ℝ → ℝ := fun n => pscpGap M Lt f h u0 (Xs n) n
  change UocInProb M.P (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) * K n ω s])
    (fun _ => 0)
  intro T hT ε hε
  have hQ (n : ℕ) (_ : 1 ≤ n) (ω : Ω) (t : ℝ) (i : Fin k) (_ : 0 ≤ t) :
      X n ω t i - Ψ n ω t i ≤ max ((∑ j, X n ω t j) - n) 0 := by
    dsimp [Ψ, X]
    rw [sub_sub_cancel]
    exact pscpPhi_le_excess M h hh_mem n (Xs n ω t) i
  refine tendsto_order.2 ⟨fun _ h => (not_lt_zero h).elim, fun η hη => ?_⟩
  obtain ⟨B, _, hB⟩ := controlled_compact_containment M X0 x hX0 X Ψ hXs hQ T hT η hη
  let δ : ℝ := ε / (2 * (T + 1))
  have hδ : 0 < δ := div_pos hε (by positivity)
  have hdeltaT : δ * T < ε := by
    dsimp [δ]
    calc
      ε / (2 * (T + 1)) * T ≤ ε / (2 * (T + 1)) * (T + 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hδ.le
      _ = ε / 2 := by field_simp
      _ < ε := by linarith
  filter_upwards [hB, gap_on_bounded_states M Lt ϱ mL hA2 f hf h hh_mem hh_min u0 B δ hδ] with n hn hgap
  refine (measure_mono (s := _) (t := {ω | ∃ t ∈ Set.Icc 0 T, B < ‖M.Xhat n (X n) ω t‖})
    ?_).trans_lt hn
  intro ω hω
  by_contra hbad
  have hpoint (s : ℝ) (hs : s ∈ Set.Icc 0 T) : |K n ω s| ≤ δ :=
    hgap (Xs n) ω s (le_of_not_gt fun h => hbad ⟨s, hs, h⟩)
  have hsupp : supDist (fun t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) * K n ω s])
      (fun _ => 0) T ≤ ENNReal.ofReal (δ * T) := by
    unfold supDist
    refine iSup_le fun t => iSup_le fun ht => ?_
    rw [Fin.sum_univ_one]
    simp only [Pi.zero_apply, sub_zero, Matrix.cons_val_zero]
    apply ENNReal.ofReal_le_ofReal
    rw [← Real.norm_eq_abs]
    calc
      ‖∫ s in (0 : ℝ)..t, Real.exp (-γ * s) * K n ω s‖ ≤ δ * |t - 0| := by
        apply intervalIntegral.norm_integral_le_of_norm_le_const
        intro s hs
        rw [Set.uIoc_of_le ht.1] at hs
        rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
        have hExp : Real.exp (-γ * s) ≤ 1 :=
          Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hγ.le) hs.1.le)
        exact (mul_le_of_le_one_left (abs_nonneg _) hExp).trans
          (hpoint s ⟨hs.1.le, hs.2.trans ht.2⟩)
      _ ≤ δ * T := by rw [sub_zero, abs_of_nonneg ht.1]; exact mul_le_mul_of_nonneg_left ht.2 hδ.le
  exact (not_le_of_gt ((ENNReal.ofReal_lt_ofReal_iff hε).2 hdeltaT)) (hω.trans hsupp)
