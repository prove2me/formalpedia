-- Prove2me | solution 1 for GreedWorks.OnlineTime.eq_13_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:38:27.785065+00:00
-- url     : https://prove2.me/submissions/7e9fa378-427f-4561-aefd-eeccfda57be6

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP

open MeasureTheory ProbabilityTheory GreedWorks.OnlineTime

set_option linter.unusedSectionVars false

namespace GW4Relax

/-! ## Overlap of `[a, a + L)` with the unit slot `[s, s + 1)` -/

noncomputable def ov (a L : ℝ) (s : ℕ) : ℝ := max (min (a + L) ((s : ℝ) + 1) - max a (s : ℝ)) 0

lemma ov_nonneg (a L : ℝ) (s : ℕ) : 0 ≤ ov a L s := le_max_right _ _

lemma ov_le_one (a L : ℝ) (s : ℕ) : ov a L s ≤ 1 := by
  unfold ov
  apply max_le _ zero_le_one
  have h1 : min (a + L) ((s : ℝ) + 1) ≤ (s : ℝ) + 1 := min_le_right _ _
  have h2 : (s : ℝ) ≤ max a (s : ℝ) := le_max_right _ _
  linarith

lemma ov_le_L (a L : ℝ) (hL : 0 ≤ L) (s : ℕ) : ov a L s ≤ L := by
  unfold ov
  apply max_le _ hL
  have h1 : min (a + L) ((s : ℝ) + 1) ≤ a + L := min_le_left _ _
  have h2 : a ≤ max a (s : ℝ) := le_max_left _ _
  linarith

lemma ov_eq_zero_of_le (a L : ℝ) (s : ℕ) (h : (s : ℝ) + 1 ≤ a) : ov a L s = 0 := by
  unfold ov
  apply max_eq_right
  have h1 : min (a + L) ((s : ℝ) + 1) ≤ (s : ℝ) + 1 := min_le_right _ _
  have h2 : a ≤ max a (s : ℝ) := le_max_left _ _
  linarith

lemma ov_zero (a : ℝ) (s : ℕ) : ov a 0 s = 0 := by
  unfold ov
  apply max_eq_right
  have h1 : min (a + 0) ((s : ℝ) + 1) ≤ a + 0 := min_le_left _ _
  have h2 : a ≤ max a (s : ℝ) := le_max_left _ _
  linarith

lemma ov_add_one (a L : ℝ) (hL : 0 ≤ L) (s : ℕ) :
    ov a (L + 1) s = ov a L s + ov (a + L) 1 s := by
  unfold ov
  rcases le_total (a + L) (s : ℝ) with h1 | h1
  · -- the first piece is empty
    have e1 : max (min (a + L) ((s : ℝ) + 1) - max a (s : ℝ)) 0 = 0 := by
      apply max_eq_right
      have := min_le_left (a + L) ((s : ℝ) + 1)
      have := le_max_right a (s : ℝ)
      linarith
    rw [e1, zero_add, max_eq_right (show a + L ≤ (s : ℝ) from h1),
      max_eq_right (show a ≤ (s : ℝ) by linarith)]
    congr 2; ring
  · rcases le_total (a + L) ((s : ℝ) + 1) with h2 | h2
    · rw [max_eq_left (show (s : ℝ) ≤ a + L from h1), min_eq_left h2]
      rcases le_total a (s : ℝ) with h3 | h3
      · rw [max_eq_right h3]
        rw [max_eq_left (show (0 : ℝ) ≤ a + L - s by linarith)]
        rw [show min (a + (L + 1)) ((s : ℝ) + 1) = (s : ℝ) + 1 from min_eq_right (by linarith)]
        rw [show min (a + L + 1) ((s : ℝ) + 1) = (s : ℝ) + 1 from min_eq_right (by linarith)]
        rw [max_eq_left (show (0 : ℝ) ≤ (s : ℝ) + 1 - s by linarith),
          max_eq_left (show (0 : ℝ) ≤ (s : ℝ) + 1 - (a + L) by linarith)]
        ring
      · rw [max_eq_left h3]
        rw [max_eq_left (show (0 : ℝ) ≤ a + L - a by linarith)]
        rw [show min (a + (L + 1)) ((s : ℝ) + 1) = (s : ℝ) + 1 from min_eq_right (by linarith)]
        rw [show min (a + L + 1) ((s : ℝ) + 1) = (s : ℝ) + 1 from min_eq_right (by linarith)]
        rw [max_eq_left (show (0 : ℝ) ≤ (s : ℝ) + 1 - a by linarith),
          max_eq_left (show (0 : ℝ) ≤ (s : ℝ) + 1 - (a + L) by linarith)]
        ring
    · -- the second piece is empty
      have e2 : max (min (a + L + 1) ((s : ℝ) + 1) - max (a + L) (s : ℝ)) 0 = 0 := by
        apply max_eq_right
        have := min_le_right (a + L + 1) ((s : ℝ) + 1)
        have := le_max_left (a + L) (s : ℝ)
        linarith
      rw [e2, add_zero, min_eq_right h2, min_eq_right (show (s : ℝ) + 1 ≤ a + (L + 1) by linarith)]

lemma ov_unit_hasSum (b : ℝ) (hb : 0 ≤ b) :
    HasSum (fun s => ov b 1 s) 1 ∧
      HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * ov b 1 s) (b + 1 / 2) := by
  set k := ⌊b⌋₊ with hk
  have hk1 : (k : ℝ) ≤ b := Nat.floor_le hb
  have hk2 : b < (k : ℝ) + 1 := Nat.lt_floor_add_one b
  have v0 : ov b 1 k = (k : ℝ) + 1 - b := by
    unfold ov
    rw [max_eq_left hk1, min_eq_right (by linarith)]
    exact max_eq_left (by linarith)
  have v1 : ov b 1 (k + 1) = b - k := by
    unfold ov
    push_cast
    rw [max_eq_right hk2.le, min_eq_left (by linarith)]
    rw [max_eq_left (by linarith)]; ring
  have vz : ∀ s ∉ ({k, k + 1} : Finset ℕ), ov b 1 s = 0 := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rcases lt_or_gt_of_ne hs.1 with h | h
    · apply ov_eq_zero_of_le
      have : (s : ℝ) + 1 ≤ k := by exact_mod_cast h
      linarith
    · have h' : k + 2 ≤ s := by omega
      have : (k : ℝ) + 2 ≤ s := by exact_mod_cast h'
      unfold ov
      apply max_eq_right
      have := min_le_left (b + 1) ((s : ℝ) + 1)
      have := le_max_right b (s : ℝ)
      linarith
  have hne : k ≠ k + 1 := by omega
  constructor
  · have : HasSum (fun s => ov b 1 s) (∑ s ∈ ({k, k + 1} : Finset ℕ), ov b 1 s) :=
      hasSum_sum_of_ne_finset_zero vz
    rw [Finset.sum_pair hne, v0, v1] at this
    convert this using 1; ring
  · have : HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * ov b 1 s)
        (∑ s ∈ ({k, k + 1} : Finset ℕ), ((s : ℝ) + 1 / 2) * ov b 1 s) :=
      hasSum_sum_of_ne_finset_zero (fun s hs => by simp only [vz s hs, mul_zero])
    rw [Finset.sum_pair hne, v0, v1] at this
    convert this using 1; push_cast; ring

lemma ov_hasSum (a : ℝ) (ha : 0 ≤ a) (L : ℕ) :
    HasSum (fun s => ov a L s) L ∧
      HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * ov a L s) (L * a + (L : ℝ) ^ 2 / 2) := by
  induction L with
  | zero =>
    simp only [Nat.cast_zero, ov_zero, mul_zero]
    exact ⟨by simpa using hasSum_zero, by simpa using hasSum_zero⟩
  | succ L ih =>
    have hu := ov_unit_hasSum (a + L) (by positivity)
    have e : ∀ s, ov a ((L + 1 : ℕ) : ℝ) s = ov a L s + ov (a + L) 1 s := by
      intro s; push_cast; exact ov_add_one a L (by positivity) s
    constructor
    · simp only [e]
      have := ih.1.add hu.1
      convert this using 1; push_cast; ring
    · simp only [e, mul_add]
      have := ih.2.add hu.2
      convert this using 1; push_cast; ring

/-! ## Column invariance of a nonanticipatory policy -/

variable {M : Type*} [Fintype M] {n : ℕ}

lemma start_eq_of_agree (pol : GreedWorks.OnlineList.Policy M n)
    (hNA : GreedWorks.OnlineList.IsNonanticipatory pol) (j : Fin n)
    (p q : GreedWorks.OnlineList.Realization M n) (hpq : ∀ i k, k ≠ j → p i k = q i k) :
    GreedWorks.OnlineList.start pol p j = GreedWorks.OnlineList.start pol q j := by
  -- if `start p j < start q j`, apply nonanticipation at `t = start p j` to `(q, p)`
  have key : ∀ p q : GreedWorks.OnlineList.Realization M n, (∀ i k, k ≠ j → p i k = q i k) →
      ¬ GreedWorks.OnlineList.start pol p j < GreedWorks.OnlineList.start pol q j := by
    intro p q hpq hlt
    set t := GreedWorks.OnlineList.start pol p j
    have h := hNA t q p (fun k hk => by
      have hkj : k ≠ j := by
        rintro rfl; exact absurd hk (not_le.mpr hlt)
      refine ⟨fun _ => (hpq _ k hkj), fun h' => ?_⟩
      rw [hpq _ k hkj]; exact h') j
    have := (h.1).mpr le_rfl
    exact absurd this (not_le.mpr hlt)
  rcases lt_trichotomy (GreedWorks.OnlineList.start pol p j)
    (GreedWorks.OnlineList.start pol q j) with h | h | h
  · exact absurd h (key p q hpq)
  · exact h
  · exact absurd h (key q p (fun i k hk => (hpq i k hk).symm))

lemma machine_eq_of_agree_at (pol : GreedWorks.OnlineList.Policy M n)
    (hNA : GreedWorks.OnlineList.IsNonanticipatory pol) (j : Fin n)
    (p q : GreedWorks.OnlineList.Realization M n) (hpq : ∀ i k, k ≠ j → p i k = q i k)
    (hz : p (GreedWorks.OnlineList.machine pol p j) j = 0 ↔
      q (GreedWorks.OnlineList.machine pol p j) j = 0) :
    GreedWorks.OnlineList.machine pol q j = GreedWorks.OnlineList.machine pol p j := by
  set t := GreedWorks.OnlineList.start pol p j
  have h := hNA t p q (fun k hk => by
    by_cases hkj : k = j
    · subst hkj
      constructor
      · intro hc
        unfold GreedWorks.OnlineList.completion at hc
        have h0 : (p (GreedWorks.OnlineList.machine pol p k) k : ℝ) = 0 := by
          have := Nat.cast_nonneg (α := ℝ) (p (GreedWorks.OnlineList.machine pol p k) k)
          linarith
        have h0' : p (GreedWorks.OnlineList.machine pol p k) k = 0 := by exact_mod_cast h0
        rw [h0', hz.mp h0']
      · intro hc
        unfold GreedWorks.OnlineList.completion at hc
        have hpos : p (GreedWorks.OnlineList.machine pol p k) k ≠ 0 := by
          intro h0; rw [h0] at hc; simp only [Nat.cast_zero, add_zero] at hc; exact lt_irrefl _ hc
        have hq : q (GreedWorks.OnlineList.machine pol p k) k ≠ 0 := fun h0 => hpos (hz.mpr h0)
        have : (0 : ℝ) < q (GreedWorks.OnlineList.machine pol p k) k := by
          exact_mod_cast Nat.pos_of_ne_zero hq
        linarith
    · exact ⟨fun _ => (hpq _ k hkj).symm, fun h' => by rw [← hpq _ k hkj]; exact h'⟩) j
  exact (h.2 le_rfl).2

lemma machine_eq_of_agree [DecidableEq M] (pol : GreedWorks.OnlineList.Policy M n)
    (hNA : GreedWorks.OnlineList.IsNonanticipatory pol) (j : Fin n)
    (p q : GreedWorks.OnlineList.Realization M n) (hpq : ∀ i k, k ≠ j → p i k = q i k) :
    GreedWorks.OnlineList.machine pol p j = GreedWorks.OnlineList.machine pol q j := by
  by_contra hne
  set a := GreedWorks.OnlineList.machine pol p j
  set b := GreedWorks.OnlineList.machine pol q j
  -- an intermediate realization: agrees with `p` at machine `a`, with `q` at machine `b`
  let r : GreedWorks.OnlineList.Realization M n := fun i k =>
    if k = j then (if i = b then q i k else p i k) else p i k
  have hpr : ∀ i k, k ≠ j → p i k = r i k := fun i k hk => by simp [r, hk]
  have hqr : ∀ i k, k ≠ j → q i k = r i k := fun i k hk => by simp [r, hk, ← hpq i k hk]
  have h1 : GreedWorks.OnlineList.machine pol r j = a :=
    machine_eq_of_agree_at pol hNA j p r hpr (by
      have : r a j = p a j := by simp [r, hne]
      rw [this])
  have h2 : GreedWorks.OnlineList.machine pol r j = b :=
    machine_eq_of_agree_at pol hNA j q r hqr (by
      have : r b j = q b j := by simp [r]
      rw [this])
  exact hne (h1.symm.trans h2)

/-! ## At most one unit of work per machine and slot -/

lemma ov_eq_volume (a L : ℝ) (s : ℕ) :
    ov a L s = (volume (Set.Ico a (a + L) ∩ Set.Ico (s : ℝ) ((s : ℝ) + 1))).toReal := by
  rw [Set.Ico_inter_Ico, Real.volume_Ico, ENNReal.toReal_ofReal']
  rfl

lemma slot_sum_le_one [DecidableEq M] (pol : GreedWorks.OnlineList.Policy M n)
    (p : GreedWorks.OnlineList.Realization M n)
    (hdisj : ∀ j k, j ≠ k → GreedWorks.OnlineList.machine pol p j =
      GreedWorks.OnlineList.machine pol p k →
      Disjoint (Set.Ico (GreedWorks.OnlineList.start pol p j)
        (GreedWorks.OnlineList.completion pol p j))
        (Set.Ico (GreedWorks.OnlineList.start pol p k)
          (GreedWorks.OnlineList.completion pol p k)))
    (i : M) (s : ℕ) :
    ∑ j : Fin n, (if GreedWorks.OnlineList.machine pol p j = i then
      ov (GreedWorks.OnlineList.start pol p j) (p i j) s else 0) ≤ 1 := by
  classical
  set T := Finset.univ.filter (fun j => GreedWorks.OnlineList.machine pol p j = i)
  set B := Set.Ico (s : ℝ) ((s : ℝ) + 1)
  set A : Fin n → Set ℝ := fun j => Set.Ico (GreedWorks.OnlineList.start pol p j)
    (GreedWorks.OnlineList.start pol p j + (p i j : ℝ)) ∩ B
  rw [← Finset.sum_filter]
  have hT : ∀ j ∈ T, GreedWorks.OnlineList.machine pol p j = i := fun j hj =>
    (Finset.mem_filter.mp hj).2
  have e : ∑ j ∈ T, ov (GreedWorks.OnlineList.start pol p j) (p i j) s =
      (volume (⋃ j ∈ T, A j)).toReal := by
    rw [measure_biUnion_finset, ENNReal.toReal_sum]
    · exact Finset.sum_congr rfl (fun j _ => ov_eq_volume _ _ _)
    · intro j _; exact measure_ne_top_of_subset Set.inter_subset_right (by simp [B])
    · intro j hj k hk hjk
      have h := hdisj j k hjk ((hT j hj).trans (hT k hk).symm)
      unfold GreedWorks.OnlineList.completion at h
      rw [hT j hj, hT k hk] at h
      exact (h.mono Set.inter_subset_left Set.inter_subset_left)
    · intro j _; exact measurableSet_Ico.inter measurableSet_Ico
  rw [e]
  have hsub : (⋃ j ∈ T, A j) ⊆ B := Set.iUnion₂_subset (fun j _ => Set.inter_subset_right)
  calc (volume (⋃ j ∈ T, A j)).toReal ≤ (volume B).toReal :=
        ENNReal.toReal_mono (by simp [B]) (measure_mono hsub)
    _ = 1 := by simp [B]

end GW4Relax


open MeasureTheory ProbabilityTheory GreedWorks.OnlineTime

set_option linter.unusedSectionVars false

namespace GW4Relax

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

open GreedWorks.OnlineList (Realization Policy)

lemma realize_measurable (I : StochasticInstance M n Ω) : Measurable (realize I) := by
  apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro k
  exact I.measurable i k

lemma comp_measurable (I : StochasticInstance M n Ω) (F : Realization M n → ℝ) :
    Measurable (fun ω => F (realize I ω)) :=
  (measurable_of_countable F).comp (realize_measurable I)

lemma natCast_measurable (I : StochasticInstance M n Ω) (i : M) (k : Fin n) :
    Measurable (fun ω => (I.P i k ω : ℝ)) :=
  (measurable_of_countable (fun x : ℕ => (x : ℝ))).comp (I.measurable i k)

/-- A column of processing times is independent of any function of the other columns. -/
lemma indep_col (I : StochasticInstance M n Ω) (i : M) (j : Fin n)
    (F : Realization M n → ℝ)
    (hF : ∀ p q : Realization M n, (∀ i k, k ≠ j → p i k = q i k) → F p = F q) :
    IndepFun (fun ω => (I.P i j ω : ℝ)) (fun ω => F (realize I ω)) I.Pr := by
  classical
  have hmeas : ∀ k, Measurable (fun ω => fun i => (I.P i k ω : ℝ)) := fun k =>
    measurable_pi_lambda _ (fun i => natCast_measurable I i k)
  have h := I.independentJobs.indepFun_finset {j} (Finset.univ.erase j) (by simp) hmeas
  let rebuild : (↥(Finset.univ.erase j) → M → ℝ) → Realization M n := fun x i k =>
    if hk : k ∈ Finset.univ.erase j then ⌊x ⟨k, hk⟩ i⌋₊ else 0
  have hreb : Measurable rebuild := by
    apply measurable_pi_lambda; intro i; apply measurable_pi_lambda; intro k
    by_cases hk : k ∈ Finset.univ.erase j
    · simp only [rebuild, hk, dif_pos]
      exact Nat.measurable_floor.comp ((measurable_pi_apply i).comp (measurable_pi_apply _))
    · simp only [rebuild, hk, dif_neg, not_false_eq_true]; exact measurable_const
  have h2 := h.comp (φ := fun x : ↥({j} : Finset (Fin n)) → M → ℝ =>
      x ⟨j, Finset.mem_singleton_self j⟩ i) (ψ := F ∘ rebuild)
    (by fun_prop)
    ((measurable_of_countable F).comp hreb)
  have e2 : ((F ∘ rebuild) ∘ fun (a : Ω) (k : ↥(Finset.univ.erase j)) (i : M) =>
      (I.P i (k : Fin n) a : ℝ)) = fun ω => F (realize I ω) := by
    funext ω
    simp only [Function.comp]
    apply hF
    intro i' k hk
    have hk' : k ∈ Finset.univ.erase j := by simp [hk]
    simp only [rebuild, hk', dif_pos, Nat.floor_natCast]
    rfl
  rw [e2] at h2
  exact h2


section Main

open Classical

variable (I : StochasticInstance M n Ω) (pol : Policy M n)

noncomputable def G (i : M) (j : Fin n) (s : ℕ) (p : Realization M n) : ℝ :=
  if GreedWorks.OnlineList.machine pol p j = i then
    ov (GreedWorks.OnlineList.start pol p j) (p i j) s else 0

noncomputable def ind (i : M) (j : Fin n) (p : Realization M n) : ℝ :=
  if GreedWorks.OnlineList.machine pol p j = i then 1 else 0

noncomputable def IS (i : M) (j : Fin n) (p : Realization M n) : ℝ :=
  if GreedWorks.OnlineList.machine pol p j = i then GreedWorks.OnlineList.start pol p j else 0

noncomputable def yv (i : M) (j : Fin n) (s : ℕ) : ℝ := ∫ ω, G pol i j s (realize I ω) ∂I.Pr

variable {I pol}

lemma start_nonneg (hpol : IsAdmissible I pol) (p : Realization M n) (j : Fin n) :
    0 ≤ GreedWorks.OnlineList.start pol p j :=
  le_trans (Nat.cast_nonneg _) ((hpol.1 p).2.1 j)

lemma G_nonneg (i : M) (j : Fin n) (s : ℕ) (p : Realization M n) : 0 ≤ G pol i j s p := by
  unfold G; split_ifs
  · exact ov_nonneg _ _ _
  · exact le_rfl

lemma G_le_one (i : M) (j : Fin n) (s : ℕ) (p : Realization M n) : G pol i j s p ≤ 1 := by
  unfold G; split_ifs
  · exact ov_le_one _ _ _
  · exact zero_le_one

lemma ind_indep (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    IndepFun (fun ω => (I.P i j ω : ℝ)) (fun ω => ind pol i j (realize I ω)) I.Pr := by
  classical
  refine indep_col I i j _ (fun p q hpq => ?_)
  unfold ind
  rw [machine_eq_of_agree pol hpol.2.1 j p q hpq]

lemma IS_indep (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    IndepFun (fun ω => (I.P i j ω : ℝ)) (fun ω => IS pol i j (realize I ω)) I.Pr := by
  classical
  refine indep_col I i j _ (fun p q hpq => ?_)
  unfold IS
  rw [machine_eq_of_agree pol hpol.2.1 j p q hpq, start_eq_of_agree pol hpol.2.1 j p q hpq]

lemma P_int (i : M) (j : Fin n) (hi : I.eligible i j) :
    Integrable (fun ω => (I.P i j ω : ℝ)) I.Pr := by
  have := I.probability
  exact (I.memLp i j hi).integrable (by norm_num)

lemma ind_int (i : M) (j : Fin n) : Integrable (fun ω => ind pol i j (realize I ω)) I.Pr := by
  haveI := I.probability
  refine Integrable.mono' (integrable_const (1 : ℝ)) (comp_measurable I _).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  unfold ind; split_ifs <;> simp

lemma IS_int (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    Integrable (fun ω => IS pol i j (realize I ω)) I.Pr := by
  refine Integrable.mono' (hpol.2.2 j) (comp_measurable I _).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  have h0 := start_nonneg hpol (realize I ω) j
  unfold IS GreedWorks.OnlineList.completion
  have hP := Nat.cast_nonneg (α := ℝ)
    (realize I ω (GreedWorks.OnlineList.machine pol (realize I ω) j) j)
  split_ifs
  · rw [Real.norm_of_nonneg h0]; linarith
  · simp only [norm_zero]; linarith

lemma Pind_int (i : M) (j : Fin n) (hi : I.eligible i j) :
    Integrable (fun ω => (I.P i j ω : ℝ) * ind pol i j (realize I ω)) I.Pr := by
  refine Integrable.mono' (P_int i j hi)
    ((natCast_measurable I i j).mul (comp_measurable I _)).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  have hP := Nat.cast_nonneg (α := ℝ) (I.P i j ω)
  unfold ind; split_ifs <;> simp

lemma hasSum1 (hpol : IsAdmissible I pol) (i : M) (j : Fin n) (hi : I.eligible i j) :
    HasSum (fun s => yv I pol i j s)
      (∫ ω, (I.P i j ω : ℝ) * ind pol i j (realize I ω) ∂I.Pr) := by
  have hpt : ∀ ω, HasSum (fun s => G pol i j s (realize I ω))
      ((I.P i j ω : ℝ) * ind pol i j (realize I ω)) := by
    intro ω
    unfold G ind
    split_ifs with h
    · rw [mul_one]
      exact (ov_hasSum _ (start_nonneg hpol (realize I ω) j) (I.P i j ω)).1
    · rw [mul_zero]; exact hasSum_zero
  refine hasSum_integral_of_dominated_convergence (fun s ω => G pol i j s (realize I ω))
    (fun s => (comp_measurable I _).aestronglyMeasurable)
    (fun s => ae_of_all _ (fun ω => le_of_eq (Real.norm_of_nonneg (G_nonneg _ _ _ _))))
    (ae_of_all _ (fun ω => (hpt ω).summable)) ?_ (ae_of_all _ hpt)
  have e : (fun ω => ∑' s, G pol i j s (realize I ω)) =
      fun ω => (I.P i j ω : ℝ) * ind pol i j (realize I ω) := funext (fun ω => (hpt ω).tsum_eq)
  rw [e]; exact Pind_int i j hi

lemma hasSum2 (hpol : IsAdmissible I pol) (i : M) (j : Fin n) (hi : I.eligible i j) :
    HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * yv I pol i j s)
      (∫ ω, ((I.P i j ω : ℝ) * IS pol i j (realize I ω) +
        (I.P i j ω : ℝ) ^ 2 / 2 * ind pol i j (realize I ω)) ∂I.Pr) := by
  haveI := I.probability
  have hpt : ∀ ω, HasSum (fun s : ℕ => ((s : ℝ) + 1 / 2) * G pol i j s (realize I ω))
      ((I.P i j ω : ℝ) * IS pol i j (realize I ω) +
        (I.P i j ω : ℝ) ^ 2 / 2 * ind pol i j (realize I ω)) := by
    intro ω
    unfold G ind IS
    split_ifs with h
    · have := (ov_hasSum _ (start_nonneg hpol (realize I ω) j) (I.P i j ω)).2
      rw [mul_one]; exact this
    · simp only [mul_zero, add_zero]; exact hasSum_zero
  simp only [yv, ← integral_const_mul]
  refine hasSum_integral_of_dominated_convergence
    (fun (s : ℕ) ω => ((s : ℝ) + 1 / 2) * G pol i j s (realize I ω))
    (fun s => ((comp_measurable I _).const_mul _).aestronglyMeasurable)
    (fun s => ae_of_all _ (fun ω => le_of_eq (Real.norm_of_nonneg
      (mul_nonneg (by positivity) (G_nonneg _ _ _ _)))))
    (ae_of_all _ (fun ω => (hpt ω).summable)) ?_ (ae_of_all _ hpt)
  have e : (fun ω => ∑' (s : ℕ), ((s : ℝ) + 1 / 2) * G pol i j s (realize I ω)) =
      fun ω => (I.P i j ω : ℝ) * IS pol i j (realize I ω) +
        (I.P i j ω : ℝ) ^ 2 / 2 * ind pol i j (realize I ω) :=
    funext (fun ω => (hpt ω).tsum_eq)
  rw [e]
  refine Integrable.add ((IS_indep hpol i j).integrable_mul (P_int i j hi) (IS_int hpol i j)) ?_
  refine Integrable.mono' (((I.memLp i j hi).integrable_sq).div_const 2)
    ((((natCast_measurable I i j).pow_const 2).div_const 2).mul
      (comp_measurable I _)).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
  unfold ind; split_ifs <;> simp <;> positivity

end Main

end GW4Relax


open MeasureTheory ProbabilityTheory GreedWorks.OnlineTime

set_option linter.unusedSectionVars false

namespace GW4Relax

open Classical

variable {M : Type*} [Fintype M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

open GreedWorks.OnlineList (Realization Policy)

variable {I : StochasticInstance M n Ω} {pol : Policy M n}

lemma E1 (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    ∫ ω, (I.P i j ω : ℝ) * ind pol i j (realize I ω) ∂I.Pr =
      mean I i j * ∫ ω, ind pol i j (realize I ω) ∂I.Pr :=
  (ind_indep hpol i j).integral_fun_mul_eq_mul_integral
    (natCast_measurable I i j).aestronglyMeasurable (comp_measurable I _).aestronglyMeasurable

lemma E2 (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    ∫ ω, (I.P i j ω : ℝ) * IS pol i j (realize I ω) ∂I.Pr =
      mean I i j * ∫ ω, IS pol i j (realize I ω) ∂I.Pr :=
  (IS_indep hpol i j).integral_fun_mul_eq_mul_integral
    (natCast_measurable I i j).aestronglyMeasurable (comp_measurable I _).aestronglyMeasurable

lemma E3 (hpol : IsAdmissible I pol) (i : M) (j : Fin n) :
    ∫ ω, (I.P i j ω : ℝ) ^ 2 * ind pol i j (realize I ω) ∂I.Pr =
      (∫ ω, (I.P i j ω : ℝ) ^ 2 ∂I.Pr) * ∫ ω, ind pol i j (realize I ω) ∂I.Pr := by
  have h := (ind_indep hpol i j).comp (φ := fun x : ℝ => x ^ 2) (ψ := id)
    (measurable_id.pow_const 2) measurable_id
  exact h.integral_fun_mul_eq_mul_integral
    ((natCast_measurable I i j).pow_const 2).aestronglyMeasurable
    (comp_measurable I _).aestronglyMeasurable

lemma G_int (i : M) (j : Fin n) (s : ℕ) :
    Integrable (fun ω => G pol i j s (realize I ω)) I.Pr := by
  have := I.probability
  refine Integrable.mono' (integrable_const (1 : ℝ)) (comp_measurable I _).aestronglyMeasurable
    (ae_of_all _ (fun ω => ?_))
  rw [Real.norm_of_nonneg (G_nonneg _ _ _ _)]
  exact G_le_one _ _ _ _

lemma inner_tsum (hpol : IsAdmissible I pol) (i : M) (j : Fin n) (hi : I.eligible i j) :
    ∑' s : ℕ, (yv I pol i j s / mean I i j * ((s : ℝ) + 1 / 2) +
      (1 - cvSquared I i j) / 2 * yv I pol i j s) =
      ∫ ω, IS pol i j (realize I ω) ∂I.Pr +
        ∫ ω, (I.P i j ω : ℝ) * ind pol i j (realize I ω) ∂I.Pr := by
  have := I.probability
  have h1 := hasSum1 hpol i j hi
  have h2 := hasSum2 hpol i j hi
  have hμ : 1 ≤ mean I i j := I.meanAtLeastOne i j hi
  have hμ0 : mean I i j ≠ 0 := by linarith
  have hsum := (h2.div_const (mean I i j)).add (h1.mul_left ((1 - cvSquared I i j) / 2))
  have e : (fun s : ℕ => yv I pol i j s / mean I i j * ((s : ℝ) + 1 / 2) +
      (1 - cvSquared I i j) / 2 * yv I pol i j s) =
      fun s : ℕ => ((s : ℝ) + 1 / 2) * yv I pol i j s / mean I i j +
        (1 - cvSquared I i j) / 2 * yv I pol i j s := funext (fun s => by ring)
  rw [e, hsum.tsum_eq]
  have hPS : Integrable (fun ω => (I.P i j ω : ℝ) * IS pol i j (realize I ω)) I.Pr :=
    (IS_indep hpol i j).integrable_mul (P_int i j hi) (IS_int hpol i j)
  have hP2 : Integrable (fun ω => (I.P i j ω : ℝ) ^ 2 / 2 * ind pol i j (realize I ω)) I.Pr := by
    refine Integrable.mono' (((I.memLp i j hi).integrable_sq).div_const 2)
      ((((natCast_measurable I i j).pow_const 2).div_const 2).mul
        (comp_measurable I _)).aestronglyMeasurable (ae_of_all _ (fun ω => ?_))
    unfold ind; split_ifs <;> simp <;> positivity
  rw [integral_add hPS hP2]
  have e2 : (fun ω => (I.P i j ω : ℝ) ^ 2 / 2 * ind pol i j (realize I ω)) =
      fun ω => (I.P i j ω : ℝ) ^ 2 * ind pol i j (realize I ω) / 2 := funext (fun ω => by ring)
  rw [E2 hpol i j, e2, integral_div, E3 hpol i j, E1 hpol i j]
  have hvar := variance_eq_sub (I.memLp i j hi)
  have hQ : ∫ ω, (I.P i j ω : ℝ) ^ 2 ∂I.Pr = variance (fun ω => (I.P i j ω : ℝ)) I.Pr +
      mean I i j ^ 2 := by
    rw [hvar]; unfold mean; simp [Pi.pow_apply]
  rw [hQ]
  unfold cvSquared
  field_simp
  ring

theorem relax (I : StochasticInstance M n Ω) :
    ∀ pol : Policy M n, IsAdmissible I pol →
      ∃ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y ∧
        valueS I.eligible (mean I) (cvSquared I) I.weight y ≤ policyCost I pol := by
  intro pol hpol
  have := I.probability
  have hel : ∀ p j, I.eligible (GreedWorks.OnlineList.machine pol p j) j :=
    fun p j => (hpol.1 p).1 j
  have yzero : ∀ i j s, ¬ I.eligible i j → yv I pol i j s = 0 := by
    intro i j s hi
    unfold yv
    have : ∀ ω, G pol i j s (realize I ω) = 0 := fun ω => by
      unfold G; rw [if_neg]; intro h; exact hi (h ▸ hel _ j)
    simp [this]
  -- the value of each `C^S_j`
  have hCS' : ∀ j, completionS I.eligible (mean I) (cvSquared I) (fun i j s => yv I pol i j s) j =
      ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j),
        (∫ ω, IS pol i j (realize I ω) ∂I.Pr +
          ∫ ω, (I.P i j ω : ℝ) * ind pol i j (realize I ω) ∂I.Pr) := by
    intro j
    unfold completionS
    exact Finset.sum_congr rfl (fun i hi => inner_tsum hpol i j (Finset.mem_filter.mp hi).2)
  have hCS : ∀ j, completionS I.eligible (mean I) (cvSquared I) (fun i j s => yv I pol i j s) j =
      ∫ ω, GreedWorks.OnlineList.completion pol (realize I ω) j ∂I.Pr := by
    intro j
    rw [hCS' j]
    calc _ = ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j),
          ∫ ω, (IS pol i j (realize I ω) + (I.P i j ω : ℝ) * ind pol i j (realize I ω)) ∂I.Pr :=
          Finset.sum_congr rfl (fun i hi => (integral_add (IS_int hpol i j)
            (Pind_int i j (Finset.mem_filter.mp hi).2)).symm)
      _ = ∫ ω, ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j),
          (IS pol i j (realize I ω) + (I.P i j ω : ℝ) * ind pol i j (realize I ω)) ∂I.Pr :=
          (integral_finset_sum _ (fun i hi => (IS_int hpol i j).add
            (Pind_int i j (Finset.mem_filter.mp hi).2))).symm
      _ = _ := by
          congr 1; funext ω
          unfold IS ind GreedWorks.OnlineList.completion
          simp_rw [mul_ite, mul_one, mul_zero]
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq]
          have hm : GreedWorks.OnlineList.machine pol (realize I ω) j ∈
              Finset.univ.filter (fun i => I.eligible i j) := by simp [hel]
          rw [if_pos hm, if_pos hm]
          rfl
  refine ⟨fun i j s => yv I pol i j s, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · intro i j s; exact integral_nonneg (fun ω => G_nonneg _ _ _ _)
  · intro i j s hi; exact yzero i j s hi
  · intro i j s hs
    show yv I pol i j s = 0
    unfold yv
    have : ∀ ω, G pol i j s (realize I ω) = 0 := fun ω => by
      unfold G; split_ifs
      · apply ov_eq_zero_of_le
        have h1 : ((s + 1 : ℕ) : ℝ) ≤ I.release j := by exact_mod_cast hs
        have h2 := (hpol.1 (realize I ω)).2.1 j
        push_cast at h1; linarith
      · rfl
    simp [this]
  · intro i j
    show Summable (fun s => yv I pol i j s)
    by_cases hi : I.eligible i j
    · exact (hasSum1 hpol i j hi).summable
    · rw [show (fun s => yv I pol i j s) = fun _ => 0 from funext (fun s => yzero i j s hi)]
      exact summable_zero
  · intro i j
    show Summable (fun s : ℕ => ((s : ℝ) + 1 / 2) * yv I pol i j s)
    by_cases hi : I.eligible i j
    · exact (hasSum2 hpol i j hi).summable
    · rw [show (fun s : ℕ => ((s : ℝ) + 1 / 2) * yv I pol i j s) = fun _ => 0 from
        funext (fun s => by rw [yzero i j s hi, mul_zero])]
      exact summable_zero
  · intro i s
    show ∑ j : Fin n, yv I pol i j s ≤ 1
    unfold yv
    rw [← integral_finset_sum _ (fun j _ => G_int i j s)]
    calc _ ≤ ∫ ω, (1 : ℝ) ∂I.Pr :=
          integral_mono (integrable_finset_sum _ (fun j _ => G_int i j s))
            (integrable_const 1) (fun ω => by
              have := slot_sum_le_one pol (realize I ω) (hpol.1 (realize I ω)).2.2 i s
              unfold G
              convert this using 0)
      _ = 1 := by simp
  · intro j
    show ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j),
      (∑' s, yv I pol i j s) / mean I i j = 1
    rw [Finset.sum_congr rfl (fun i hi => by
      have hi' := (Finset.mem_filter.mp hi).2
      have hμ : 1 ≤ mean I i j := I.meanAtLeastOne i j hi'
      rw [(hasSum1 hpol i j hi').tsum_eq, E1 hpol i j, mul_div_cancel_left₀ _ (by linarith)])]
    rw [← integral_finset_sum _ (fun i _ => ind_int i j)]
    have : ∀ ω, ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j),
        ind pol i j (realize I ω) = 1 := by
      intro ω
      unfold ind
      rw [Finset.sum_ite_eq]
      simp [hel]
    simp [this]
  · intro j
    rw [hCS' j]
    refine Finset.sum_le_sum (fun i hi => ?_)
    have hi' := (Finset.mem_filter.mp hi).2
    rw [(hasSum1 hpol i j hi').tsum_eq]
    have : 0 ≤ ∫ ω, IS pol i j (realize I ω) ∂I.Pr := integral_nonneg (fun ω => by
      unfold IS; split_ifs
      · exact start_nonneg hpol _ _
      · exact le_rfl)
    linarith
  · apply le_of_eq
    unfold valueS policyCost
    simp_rw [hCS]
    rw [integral_finset_sum _ (fun j _ => (hpol.2.2 j).const_mul _)]
    exact Finset.sum_congr rfl (fun j _ => (integral_const_mul _ _).symm)

end GW4Relax


open GW4Relax in
theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (I : StochasticInstance M n Ω) :
    ∀ pol : GreedWorks.OnlineList.Policy M n, IsAdmissible I pol →
      ∃ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y ∧
        valueS I.eligible (mean I) (cvSquared I) I.weight y ≤ policyCost I pol :=
  GW4Relax.relax I
