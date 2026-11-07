-- Prove2me | solution 1 for ManyServerQED.Scheduling.pscp_asymptotically_optimal
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-07T05:01:20.933463+00:00
-- url     : https://prove2.me/submissions/15180628-221c-4c89-8ea7-584629a9ab4a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BellWilliams2001_ThresholdPolicy_Paths
import Definitions.Def_ManyServerQED_Scheduling_Diffusion
import Definitions.Def_ManyServerQED_Scheduling_Model
import Definitions.Def_ManyServerQED_Scheduling_Policy
import Theorems.Thm_ManyServerQED_Scheduling_proposition_1
import Theorems.Thm_ManyServerQED_Scheduling_theorem_3
import Theorems.Thm_ManyServerQED_Scheduling_theorem_4_i
import Theorems.Thm_ManyServerQED_Scheduling_theorem_4_ii
import Theorems.Thm_ManyServerQED_Scheduling_pscp_condition_49

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal
open ManyServerQED.Scheduling

namespace PSCPRed

lemma roundMap_sum {k : ℕ} [NeZero k] (y : Fin k → ℝ) : ∑ i, roundMap y i = ∑ i, y i := by
  classical
  have hk : 0 < k := Nat.pos_of_ne_zero (NeZero.ne k)
  set last : Fin k := ⟨k - 1, by omega⟩
  have hfil : Finset.univ.filter (fun i : Fin k => (i : ℕ) + 1 = k) = {last} := by
    ext i; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro h; ext; simp [last]; omega
    · intro h; subst h; simp [last]; omega
  unfold roundMap
  rw [Finset.sum_ite, hfil, Finset.sum_singleton, Finset.sum_sub_distrib]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i : Fin k => (i : ℕ) + 1 = k) y,
    hfil, Finset.sum_singleton]
  ring

lemma min_split (a b n : ℝ) (ha : 0 ≤ a) (_hb : 0 ≤ b) :
    min a (max (n - b) 0) = min (b + a) n - min b n := by
  rcases le_total n b with h | h
  · rw [max_eq_right (by linarith), min_eq_right ha, min_eq_right (by linarith), min_eq_right h]
    ring
  · rw [max_eq_left (by linarith), min_eq_left h]
    rcases le_total a (n - b) with h2 | h2
    · rw [min_eq_left h2, min_eq_left (by linarith)]; ring
    · rw [min_eq_right h2, min_eq_right (by linarith)]

lemma priority_sum {k : ℕ} (n : ℕ) (X : Fin k → ℕ) :
    ∑ i, priorityPhi n X i = max (∑ i, (X i : ℝ) - n) 0 := by
  classical
  set T : ℕ → ℝ := fun m => ∑ j : Fin k, if m ≤ (j : ℕ) then (X j : ℝ) else 0 with hT
  have hS : ∀ i : Fin k,
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => i < j), (X j : ℝ) = T (i + 1) := by
    intro i; rw [Finset.sum_filter]; apply Finset.sum_congr rfl; intro j _
    simp only [Fin.lt_def]; rfl
  have hT1 : ∀ i : Fin k, T i = T (i + 1) + X i := by
    intro i; simp only [hT]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), ← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
    simp only [le_refl, if_true, Nat.not_succ_le_self, if_false]
    rw [zero_add, add_comm]; congr 1
    apply Finset.sum_congr rfl; intro j hj
    have : j ≠ i := Finset.ne_of_mem_erase hj
    have : (j : ℕ) ≠ i := fun h => this (Fin.ext h)
    by_cases h : (i : ℕ) ≤ j
    · rw [if_pos h, if_pos (by omega)]
    · rw [if_neg h, if_neg (by omega)]
  have hT0 : T 0 = ∑ i, (X i : ℝ) := by simp [hT]
  have hTk : T k = 0 := by
    simp only [hT]; apply Finset.sum_eq_zero; intro j _; rw [if_neg (by omega)]
  have hTnn : ∀ m, 0 ≤ T m := fun m => Finset.sum_nonneg (fun j _ => by positivity)
  have key : ∀ i : Fin k, priorityPhi n X i =
      (T i - min (T i) n) - (T (i + 1) - min (T (i+1)) n) := by
    intro i
    unfold priorityPhi
    rw [hS i, min_split _ _ _ (by positivity) (hTnn _), ← hT1 i]
    rw [hT1 i]; ring
  simp_rw [key]
  rw [Fin.sum_univ_eq_sum_range (fun i => (T i - min (T i) n) - (T (i + 1) - min (T (i+1)) n)) k,
    Finset.sum_range_sub', hT0, hTk]
  rw [min_eq_left (Nat.cast_nonneg n)]
  rcases le_total (∑ i, (X i : ℝ)) n with h | h
  · rw [min_eq_left h, max_eq_right (by linarith)]; ring
  · rw [min_eq_right h, max_eq_left (by linarith)]; ring


variable {Ω : Type*} [MeasurableSpace Ω] {k : ℕ}

lemma pscp_sum [NeZero k] (M : SystemSequence Ω k) (h : (Fin k → ℝ) → (Fin k → ℝ))
    (hh_mem : ∀ y, h y ∈ stdSimplex ℝ (Fin k)) (n : ℕ) (X : Fin k → ℕ) :
    ∑ i, M.pscpPhi h n X i = max (∑ i, (X i : ℝ) - n) 0 := by
  unfold SystemSequence.pscpPhi
  split_ifs
  · rw [roundMap_sum, ← Finset.mul_sum, (hh_mem _).2, mul_one]
  · exact priority_sum n X

lemma sum_Xhat (M : SystemSequence Ω k) (n : ℕ) (X : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ) :
    ∑ j, M.Xhat n X ω t j = (∑ j, X ω t j - n) / Real.sqrt n := by
  unfold SystemSequence.Xhat
  rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  have : ∑ i, M.rho i = 1 := M.sum_rho
  rw [this, one_mul]

lemma integrand_eq (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ)
    (n : ℕ) (hn : 1 ≤ n) (u0 : Fin k → ℝ) (X Ψ : Ω → ℝ → Fin k → ℝ) (ω : Ω) (t : ℝ)
    (hnn : ∀ i, 0 ≤ X ω t i - Ψ ω t i)
    (hwc : max (∑ i, X ω t i - n) 0 = ∑ i, (X ω t i - Ψ ω t i)) :
    Lt (Phihat n X Ψ ω t) (M.Psihat n Ψ ω t) =
      costOfTilde Lt (M.Xhat n X ω t) (uProc n u0 X Ψ ω t) := by
  have hsn : 0 < Real.sqrt n := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hPhi : Phihat n X Ψ ω t = max (∑ j, M.Xhat n X ω t j) 0 • uProc n u0 X Ψ ω t := by
    rw [sum_Xhat]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul, Phihat, uProc]
    split_ifs with hpos
    · rw [max_eq_left (div_nonneg hpos.le hsn.le)]
      field_simp
    · push Not at hpos
      rw [max_eq_right (div_nonpos_of_nonpos_of_nonneg hpos hsn.le), zero_mul]
      have h0 : ∑ i, (X ω t i - Ψ ω t i) = 0 := by rw [← hwc, max_eq_right hpos]
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnn i)] at h0
      rw [h0 i (Finset.mem_univ _), zero_div]
  unfold costOfTilde
  rw [← hPhi]
  congr 1
  funext i
  simp only [SystemSequence.Psihat, Pi.sub_apply, SystemSequence.Xhat, Phihat]
  ring

lemma cost_eq (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (n : ℕ) (hn : 1 ≤ n) (u0 : Fin k → ℝ) (X Ψ : Ω → ℝ → Fin k → ℝ)
    (hnn : ∀ ω t i, 0 ≤ t → 0 ≤ X ω t i - Ψ ω t i)
    (hwc : IsWorkConserving n X Ψ) :
    M.queueCost Lt γ n X Ψ = M.queueCostL (costOfTilde Lt) γ n u0 X Ψ := by
  unfold SystemSequence.queueCost SystemSequence.queueCostL
  congr 1; funext ω
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only
  rw [integrand_eq M Lt n hn u0 X Ψ ω t (fun i => hnn ω t i (le_of_lt ht)) (hwc ω t (le_of_lt ht))]

lemma cost_congr (M : SystemSequence Ω k) (Lt : (Fin k → ℝ) → (Fin k → ℝ) → ℝ) (γ : ℝ)
    (n : ℕ) (X1 Ψ1 X2 Ψ2 : Ω → ℝ → Fin k → ℝ)
    (hX : ∀ ω t, 0 ≤ t → X1 ω t = X2 ω t) (hΨ : ∀ ω t, 0 ≤ t → Ψ1 ω t = Ψ2 ω t) :
    M.queueCost Lt γ n X1 Ψ1 = M.queueCost Lt γ n X2 Ψ2 := by
  unfold SystemSequence.queueCost
  congr 1; funext ω
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have h1 := hX ω t (le_of_lt ht)
  have h2 := hΨ ω t (le_of_lt ht)
  unfold Phihat SystemSequence.Psihat
  beta_reduce
  rw [h1, h2]

lemma uoc_congr {m : ℕ} (P : Measure Ω) (Z1 Z2 : ℕ → Ω → ℝ → Fin m → ℝ) (z : ℝ → Fin m → ℝ)
    (h : ∀ᶠ n in atTop, ∀ ω s, 0 ≤ s → Z1 n ω s = Z2 n ω s)
    (h1 : BellWilliams2001.ThresholdPolicy.UocInProb P Z1 z) :
    BellWilliams2001.ThresholdPolicy.UocInProb P Z2 z := by
  intro t ht ε hε
  apply (h1 t ht ε hε).congr'
  filter_upwards [h] with n hn
  congr 1; ext ω
  simp only [Set.mem_setOf_eq, BellWilliams2001.ThresholdPolicy.supDist]
  rw [iSup_congr fun s => iSup_congr fun hs => by rw [hn ω s (Set.mem_Icc.1 hs).1]]

lemma toNat_floor_cast (a : ℝ) (m : ℤ) (hm : a = m) (ha : 0 ≤ a) :
    ((⌊a⌋.toNat : ℕ) : ℝ) = a := by
  subst hm
  have : 0 ≤ m := by exact_mod_cast ha
  rw [Int.floor_intCast]
  have h2 : ((m.toNat : ℤ) : ℝ) = (m : ℝ) := by rw [Int.toNat_of_nonneg this]
  exact_mod_cast h2

end PSCPRed

open PSCPRed BellWilliams2001.ThresholdPolicy

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
    (X0 : ℕ → Fin k → ℕ) (x : Fin k → ℝ)
    (hX0 : Tendsto (fun n => M.Xhat0 n (X0 n)) atTop (𝓝 x))
    (Xs : ℕ → Ω → ℝ → Fin k → ℕ)
    (hXs : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (fun ω t i => (Xs n ω t i : ℝ))
      (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧
      Tendsto (fun n => M.queueCost Lt γ n (fun ω t i => (Xs n ω t i : ℝ))
        (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i)) atTop (𝓝 c) ∧
      ∀ X Ψ : ℕ → Ω → ℝ → Fin k → ℝ,
        (∀ n, 1 ≤ n → M.IsSCP n (X0 n) (X n) (Ψ n) ∧ M.IsAdmissible n (X n) (Ψ n) ∧
          IsWorkConserving n (X n) (Ψ n)) →
        c ≤ liminf (fun n => M.queueCost Lt γ n (X n) (Ψ n)) atTop := by
  classical
  set u0 : Fin k → ℝ := h 0 with hu0def
  have hu0 : u0 ∈ stdSimplex ℝ (Fin k) := hh_mem 0
  -- Theorem 3: the value function is `f`
  obtain ⟨f0, -, hHJB0, huniq, hval, -⟩ :=
    theorem_3 M.diffData (costOfTilde Lt) ϱ mL γ hγ hA2.cost
  have hff0 : f = f0 := huniq f hf hHJB
  have hV : value M.diffData (costOfTilde Lt) γ x = ENNReal.ofReal (f x) := by
    rw [hff0]; exact (hval x).2
  -- the feedback map of the P-SCP, as a map `ℤ^k_+ → ℤ^k_+`
  let cond : ℕ → (Fin k → ℕ) → Prop := fun n X => ∃ v : Fin k → ℕ,
    (∀ i, (v i : ℝ) = X i - M.pscpPhi h n X i) ∧ (∀ i, v i ≤ X i) ∧ ∑ i, v i ≤ n
  let F : ℕ → (Fin k → ℕ) → (Fin k → ℕ) := fun n X =>
    if hc : cond n X then Classical.choose hc else 0
  have hF_le : ∀ n X i, F n X i ≤ X i := by
    intro n X i
    by_cases hc : cond n X
    · simp only [F, dif_pos hc]; exact (Classical.choose_spec hc).2.1 i
    · simp only [F, dif_neg hc]; exact Nat.zero_le _
  have hF_sum : ∀ n X, ∑ i, F n X i ≤ n := by
    intro n X
    by_cases hc : cond n X
    · simp only [F, dif_pos hc]; exact (Classical.choose_spec hc).2.2
    · simp only [F, dif_neg hc]; simp
  have hF_eq : ∀ n X, cond n X → ∀ i, (F n X i : ℝ) = X i - M.pscpPhi h n X i := by
    intro n X hc i
    simp only [F, dif_pos hc]; exact (Classical.choose_spec hc).1 i
  -- the states visited by `X^{n,∗}` satisfy the constraints
  have hvis : ∀ n, 1 ≤ n → ∀ ω t, 0 ≤ t → cond n (Xs n ω t) := by
    intro n hn ω t ht
    have hc := hXs n hn
    refine ⟨fun i => ⌊(Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i⌋.toNat, ?_, ?_, ?_⟩
    · intro i
      obtain ⟨m, hm⟩ := hc.psi_int ω t i ht
      exact toNat_floor_cast _ m hm (hc.psi_nonneg ω t i ht)
    · intro i
      obtain ⟨m, hm⟩ := hc.psi_int ω t i ht
      have h1 := toNat_floor_cast _ m hm (hc.psi_nonneg ω t i ht)
      have h2 := hc.phi_nonneg ω t i ht
      have : ((⌊(Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i⌋.toNat : ℕ) : ℝ) ≤ Xs n ω t i := by
        rw [h1]; linarith
      exact_mod_cast this
    · have hs := hc.servers ω t ht
      have : ((∑ i, ⌊(Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i⌋.toNat : ℕ) : ℝ) ≤ n := by
        push_cast
        rw [Finset.sum_congr rfl (fun i _ => toNat_floor_cast _ (hc.psi_int ω t i ht).choose
          (hc.psi_int ω t i ht).choose_spec (hc.psi_nonneg ω t i ht))]
        exact hs
      exact_mod_cast this
  -- `X^{n,∗}` solves (7) under the feedback rule `F`
  have hXsF : ∀ n, 1 ≤ n → M.IsControlled n (X0 n) (fun ω t i => (Xs n ω t i : ℝ))
      (fun ω t i => (F n (Xs n ω t) i : ℝ)) := by
    intro n hn
    have hc := hXs n hn
    have hE : ∀ ω t, 0 ≤ t → ∀ i,
        (F n (Xs n ω t) i : ℝ) = Xs n ω t i - M.pscpPhi h n (Xs n ω t) i :=
      fun ω t ht => hF_eq n _ (hvis n hn ω t ht)
    have hbusy : ∀ ω i t, 0 ≤ t → busyTime (fun ω t i => (F n (Xs n ω t) i : ℝ)) ω i t =
        busyTime (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω i t := by
      intro ω i t ht
      unfold busyTime
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      exact hE ω s hs.1 i
    have hqueue : ∀ ω i t, 0 ≤ t →
        queueTime (fun ω t i => (Xs n ω t i : ℝ)) (fun ω t i => (F n (Xs n ω t) i : ℝ)) ω i t =
        queueTime (fun ω t i => (Xs n ω t i : ℝ))
          (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) ω i t := by
      intro ω i t ht
      unfold queueTime
      apply intervalIntegral.integral_congr
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      simp only [hE ω s hs.1 i]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro ω t i ht; rw [hE ω t ht i]; exact hc.psi_int ω t i ht
    · intro ω t i ht; (try dsimp only); rw [hE ω t ht i]; exact hc.phi_int ω t i ht
    · intro ω t i ht; exact Nat.cast_nonneg _
    · intro ω t i ht; (try dsimp only); rw [hE ω t ht i]; exact hc.phi_nonneg ω t i ht
    · intro ω t ht; (try dsimp only); rw [Finset.sum_congr rfl (fun i _ => hE ω t ht i)]
      exact hc.servers ω t ht
    · intro ω i t ht
      obtain ⟨h1, h2⟩ := hc.integrable ω i t ht
      have hEq : Set.EqOn (fun s => (F n (Xs n ω s) i : ℝ))
          (fun s => (Xs n ω s i : ℝ) - M.pscpPhi h n (Xs n ω s) i) (Set.uIoo 0 t) := by
        intro s hs
        rw [Set.uIoo_of_le ht] at hs
        exact hE ω s hs.1.le i
      refine ⟨(intervalIntegrable_congr_uIoo hEq).2 h1, ?_⟩
      have hEq2 : Set.EqOn (fun s => (Xs n ω s i : ℝ) - (F n (Xs n ω s) i : ℝ))
          (fun s => (Xs n ω s i : ℝ) - ((Xs n ω s i : ℝ) - M.pscpPhi h n (Xs n ω s) i))
          (Set.uIoo 0 t) := by
        intro s hs
        rw [Set.uIoo_of_le ht] at hs
        simp only [hE ω s hs.1.le i]
      exact (intervalIntegrable_congr_uIoo hEq2).2 h2
    · intro ω t i ht
      rw [hbusy ω i t ht, hqueue ω i t ht]
      exact hc.eq7 ω t i ht
  -- Proposition 1: the solution is unique, an SCP and admissible
  have hP1 : ∀ n, ∃ Y : Ω → ℝ → Fin k → ℕ, 1 ≤ n →
      M.IsSCP n (X0 n) (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F n (Y ω t) i : ℝ)) ∧
      M.IsAdmissible n (fun ω t i => (Y ω t i : ℝ)) (fun ω t i => (F n (Y ω t) i : ℝ)) ∧
      ∀ ω t, 0 ≤ t → Xs n ω t = Y ω t := by
    intro n
    by_cases hn : 1 ≤ n
    · obtain ⟨Y, -, hYu, hscp, hadm⟩ :=
        proposition_1 M n hn (X0 n) (F n) (hF_le n) (hF_sum n)
      exact ⟨Y, fun _ => ⟨hscp, hadm, hYu _ (hXsF n hn)⟩⟩
    · exact ⟨Xs n, fun h' => absurd h' hn⟩
  choose Y hY using hP1
  have hPB : ∀ n, 1 ≤ n → ∀ ω t, 0 ≤ t → ∀ i,
      (F n (Y n ω t) i : ℝ) = Y n ω t i - M.pscpPhi h n (Y n ω t) i := by
    intro n hn ω t ht
    rw [← (hY n hn).2.2 ω t ht]
    exact hF_eq n _ (hvis n hn ω t ht)
  have hpolB : ∀ n, 1 ≤ n →
      M.IsSCP n (X0 n) (fun ω t i => (Y n ω t i : ℝ)) (fun ω t i => (F n (Y n ω t) i : ℝ)) ∧
      M.IsAdmissible n (fun ω t i => (Y n ω t i : ℝ)) (fun ω t i => (F n (Y n ω t) i : ℝ)) ∧
      IsWorkConserving n (fun ω t i => (Y n ω t i : ℝ)) (fun ω t i => (F n (Y n ω t) i : ℝ)) := by
    intro n hn
    refine ⟨(hY n hn).1, (hY n hn).2.1, ?_⟩
    intro ω t ht
    have e : ∀ i, (Y n ω t i : ℝ) - (F n (Y n ω t) i : ℝ) = M.pscpPhi h n (Y n ω t) i := by
      intro i; rw [hPB n hn ω t ht i]; ring
    rw [Finset.sum_congr rfl (fun i _ => e i), pscp_sum M h hh_mem n]
  -- costs of the P-SCP
  have hcostEq : ∀ n, 1 ≤ n →
      M.queueCost Lt γ n (fun ω t i => (Xs n ω t i : ℝ))
        (fun ω t i => (Xs n ω t i : ℝ) - M.pscpPhi h n (Xs n ω t) i) =
      M.queueCostL (costOfTilde Lt) γ n u0 (fun ω t i => (Y n ω t i : ℝ))
        (fun ω t i => (F n (Y n ω t) i : ℝ)) := by
    intro n hn
    rw [cost_congr M Lt γ n _ _ (fun ω t i => (Y n ω t i : ℝ))
      (fun ω t i => (F n (Y n ω t) i : ℝ))]
    · exact cost_eq M Lt γ n hn u0 _ _ (hpolB n hn).1.controlled.phi_nonneg (hpolB n hn).2.2
    · intro ω t ht; funext i; simp only [(hY n hn).2.2 ω t ht]
    · intro ω t ht; funext i; simp only [hPB n hn ω t ht i, (hY n hn).2.2 ω t ht]
  -- condition (49) for the P-SCP
  have h49A := pscp_condition_49 M Lt ϱ mL mU γ hA2 hA3 hγ f hf hHJB h hh_meas hh_mem hh_min
    u0 hu0 X0 x hX0 Xs hXs
  have h49B := uoc_congr M.P _ (fun n ω t => ![∫ s in (0 : ℝ)..t, Real.exp (-γ * s) *
        (∑ i, drift M.diffData (M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω s)
              (uProc n u0 (fun ω t i => (Y n ω t i : ℝ))
                (fun ω t i => (F n (Y n ω t) i : ℝ)) ω s) i *
            grad f (M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω s) i +
          costOfTilde Lt (M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω s)
            (uProc n u0 (fun ω t i => (Y n ω t i : ℝ))
              (fun ω t i => (F n (Y n ω t) i : ℝ)) ω s) -
          hamiltonian M.diffData (costOfTilde Lt) (M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω s)
            (grad f (M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω s)))]) _ (by
      filter_upwards [eventually_ge_atTop 1] with n hn
      intro ω s hs
      refine congrArg (fun z : ℝ => ![z]) ?_
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hs] at hu
      have hXh : M.Xhat n (fun ω t i => (Xs n ω t i : ℝ)) ω u =
          M.Xhat n (fun ω t i => (Y n ω t i : ℝ)) ω u := by
        funext i; simp only [SystemSequence.Xhat, (hY n hn).2.2 ω u hu.1]
      simp only [hXh, uProc, (hY n hn).2.2 ω u hu.1, hPB n hn ω u hu.1]) h49A
  have hlimsup := theorem_4_ii M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0 X0 x hX0 _ _ hpolB f hf hHJB h49B
  have hliminf := theorem_4_i M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0 X0 x hX0 _ _ hpolB
  refine ⟨ENNReal.ofReal (f x), ENNReal.ofReal_lt_top, ?_, ?_⟩
  · rw [← hV]
    have hT := tendsto_of_le_liminf_of_limsup_le hliminf hlimsup
    refine hT.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (hcostEq n hn).symm
  · intro X Ψ hpol
    rw [← hV]
    have h4 := theorem_4_i M Lt ϱ mL mU γ hA2 hA3 hγ u0 hu0 X0 x hX0 X Ψ hpol
    refine h4.trans (le_of_eq (Filter.liminf_congr ?_))
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (cost_eq M Lt γ n hn u0 _ _ (hpol n hn).1.controlled.phi_nonneg (hpol n hn).2.2).symm
