-- Prove2me | solution 1 for MultiPriceOnline.Hardness.eq_25
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T20:20:02.103455+00:00
-- url     : https://prove2.me/submissions/e9437419-d912-492a-9635-a40580ee7afa

import Mathlib
import Definitions.Def_MultiPriceOnline_Hardness_PriceSet
import Definitions.Def_MultiPriceOnline_Hardness_Model
import Definitions.Def_MultiPriceOnline_Hardness_Instance

open MultiPriceOnline.Hardness Finset

private lemma r_pos_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    ∀ j, 1 ≤ j → j ≤ m → 0 < r j := by
  intro j hj1 hjm
  induction j with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hj1 with h | h
    · rw [← h]; exact hr.1
    · have hk_pos : 0 < r k := ih (by omega) (by omega)
      have hlt : r k < r (k + 1) := hr.2 k (by omega) (by omega)
      linarith

private lemma r_mono_of_priceSet {m : ℕ} {r : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r) :
    ∀ j j', 1 ≤ j → j ≤ j' → j' ≤ m → r j ≤ r j' := by
  intro j j' hj1 hjj' hj'm
  induction j' with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hjj' with rfl | hlt
    · exact le_rfl
    · have h1 : r j ≤ r k := ih (by omega) (by omega)
      have h2 : r k < r (k + 1) := hr.2 k (by omega) (by omega)
      linarith

private lemma B_props {m : ℕ} {r α B : ℕ → ℝ} (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) :
    (∀ j, 1 ≤ j → j ≤ m → 0 < B j) ∧
    (∀ j, 2 ≤ j → j ≤ m → B j < B (j - 1)) ∧
    (∀ j j', 1 ≤ j → j ≤ j' → j' ≤ m → B j' ≤ B j) := by
  have hr_pos := r_pos_of_priceSet hr
  have hr1_pos : 0 < r 1 := hr.1
  have hexp_pos : ∀ j, 0 < Real.exp (-α j) := fun j => Real.exp_pos (-α j)
  have hB_eq : ∀ j, 1 ≤ j → j ≤ m → B j * (r j * Real.exp (-α j)) = r 1 * Real.exp (-α 1) := by
    intro j hj1 hjm
    rcases eq_or_lt_of_le hj1 with h | hj2
    · rw [← h, hB.1, one_mul]
    · have := hB.2 j hj2 hjm; linarith
  have hB_pos : ∀ j, 1 ≤ j → j ≤ m → 0 < B j := by
    intro j hj1 hjm
    have heq := hB_eq j hj1 hjm
    have h1 : 0 < r 1 * Real.exp (-α 1) := mul_pos hr1_pos (hexp_pos 1)
    have h2 : 0 < r j * Real.exp (-α j) := mul_pos (hr_pos j hj1 hjm) (hexp_pos j)
    nlinarith
  have hB_step : ∀ j, 2 ≤ j → j ≤ m → B j < B (j - 1) := by
    intro j hj2 hjm
    have hj_pos : 0 < r j := hr_pos j (by omega) hjm
    have hj1_pos : 0 < r (j - 1) := hr_pos (j - 1) (by omega) (by omega)
    have hr_lt : r (j - 1) < r j := by
      have h := hr.2 (j - 1) (by omega) (by omega)
      rwa [Nat.sub_add_cancel (by omega)] at h
    have hα_j1 : 0 < α (j - 1) := hα.1 (j - 1) (by omega) (by omega)
    have hexp_j1_lt : Real.exp (-α (j - 1)) < 1 := by
      rw [Real.exp_lt_one_iff]; linarith
    have h1 : r (j - 1) * Real.exp (-α (j - 1)) < r (j - 1) := by nlinarith
    have h7 : 1 - Real.exp (-α 1) = (1 - Real.exp (-α j)) / (1 - r (j - 1) / r j) :=
      hα.2.2 j hj2 hjm
    have hdenom_pos : 0 < 1 - r (j - 1) / r j := by
      rw [sub_pos, div_lt_one hj_pos]; exact hr_lt
    have h7' : (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) = 1 - Real.exp (-α j) := by
      rw [h7, div_mul_cancel₀ _ (ne_of_gt hdenom_pos)]
    have h7'' : (1 - Real.exp (-α 1)) * (r j - r (j - 1)) = r j - r j * Real.exp (-α j) := by
      have hdiv : (1 - r (j - 1) / r j) * r j = r j - r (j - 1) := by
        rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hj_pos)]
      calc
        (1 - Real.exp (-α 1)) * (r j - r (j - 1))
          = (1 - Real.exp (-α 1)) * ((1 - r (j - 1) / r j) * r j) := by rw [hdiv]
        _ = (1 - Real.exp (-α 1)) * (1 - r (j - 1) / r j) * r j := by ring
        _ = (1 - Real.exp (-α j)) * r j := by rw [h7']
        _ = r j - r j * Real.exp (-α j) := by ring
    have h2 : r (j - 1) < r j * Real.exp (-α j) := by
      have hexp1 : 0 < Real.exp (-α 1) := hexp_pos 1
      nlinarith
    have h_step : r (j - 1) * Real.exp (-α (j - 1)) < r j * Real.exp (-α j) := lt_trans h1 h2
    have hBj_eq := hB_eq j (by omega) hjm
    have hBj1_eq := hB_eq (j - 1) (by omega) (by omega)
    have hBj_pos : 0 < B j := hB_pos j (by omega) hjm
    have h_prod_pos : 0 < r (j - 1) * Real.exp (-α (j - 1)) := mul_pos hj1_pos (hexp_pos (j - 1))
    nlinarith
  have hB_anti : ∀ j j', 1 ≤ j → j ≤ j' → j' ≤ m → B j' ≤ B j := by
    intro j j' hj1 hjj' hj'm
    induction j' with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hjj' with rfl | hlt
      · exact le_rfl
      · have h1 : B k ≤ B j := ih (by omega) (by omega)
        have h2 : B (k + 1) < B k := hB_step (k + 1) (by omega) hj'm
        linarith
  exact ⟨hB_pos, hB_step, hB_anti⟩

private lemma filter_Icc_eq_Icc (m : ℕ) (P : ℕ → Prop) [DecidablePred P]
    (hdown : ∀ j j', 2 ≤ j → j ≤ j' → j' ≤ m → P j' → P j) :
    (Icc 2 m).filter P = Icc 2 (1 + ((Icc 2 m).filter P).card) := by
  induction m with
  | zero => simp
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · by_cases hP : P (k + 1)
      · have hall : (Icc 2 (k + 1)).filter P = Icc 2 (k + 1) := by
          rw [filter_eq_self]
          intro j hj
          rw [mem_Icc] at hj
          exact hdown j (k + 1) hj.1 hj.2 le_rfl hP
        rw [hall, Nat.card_Icc]
        have : 1 + (k + 1 + 1 - 2) = k + 1 := by omega
        rw [this]
      · have hsub : (Icc 2 (k + 1)).filter P = (Icc 2 k).filter P := by
          ext j
          simp only [mem_filter, mem_Icc]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            rcases eq_or_lt_of_le h2 with rfl | hlt
            · exact False.elim (hP h3)
            · exact ⟨⟨h1, by omega⟩, h3⟩
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨⟨h1, by omega⟩, h3⟩
        rw [hsub]
        exact ih (fun j j' hj hj' hjk => hdown j j' hj hj' (by omega))

private lemma phaseOf_bounds (n m : ℕ) (hm : 1 ≤ m) (B : ℕ → ℝ) (g : ℕ) :
    1 ≤ phaseOf n m B g ∧ phaseOf n m B g ≤ m := by
  unfold phaseOf
  have hle : ((Icc 2 m).filter (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g)).card ≤ (Icc 2 m).card :=
    card_filter_le _ _
  rw [Nat.card_Icc] at hle
  omega

private lemma r_telescope (r : ℕ → ℝ) (p : ℕ) (hp : 1 ≤ p) :
    r p = r 1 + ∑ j ∈ Icc 2 p, (r j - r (j - 1)) := by
  induction p with
  | zero => omega
  | succ k ih =>
    rcases eq_or_lt_of_le hp with h | hlt
    · rw [← h]; simp
    · have hk1 : 1 ≤ k := by omega
      have hsplit : Icc 2 (k + 1) = insert (k + 1) (Icc 2 k) := by
        ext j; simp only [mem_Icc, mem_insert]; omega
      rw [hsplit, sum_insert (by simp)]
      simp only [Nat.add_sub_cancel]
      have := ih hk1
      linarith

private lemma sum_div_eq (n k : ℕ) (hk : 0 < k) (f : ℕ → ℝ) :
    (∑ t ∈ range (n * k), f (t / k)) = (k : ℝ) * ∑ g ∈ range n, f g := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]
    have htail : (∑ x ∈ range k, f ((n * k + x) / k)) = (k : ℝ) * f n := by
      have hcongr : ∀ x ∈ range k, f ((n * k + x) / k) = f n := by
        intro x hx
        rw [mem_range] at hx
        have hdiv : (n * k + x) / k = n := by
          rw [mul_comm n k, Nat.mul_add_div hk, Nat.div_eq_of_lt hx, add_zero]
        rw [hdiv]
      rw [sum_congr rfl hcongr, sum_const, card_range, nsmul_eq_mul]
    rw [htail]
    ring

theorem solution {m : ℕ} {r α B : ℕ → ℝ} (hm : 1 ≤ m) (hr : MultiPriceOnline.Balance.IsPriceSet m r)
    (hα : MultiPriceOnline.Balance.IsBookingLimits m r α) (hB : IsPhaseB m r α B) (n k : ℕ) (π : Equiv.Perm (Fin n)) :
    OPT k m r (hardInstance n k m B π) = (k : ℝ) * ∑ g : Fin n, r (phaseOf n m B g) ∧
    (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k)
      ≤ OPT k m r (hardInstance n k m B π) ∧
    OPT k m r (hardInstance n k m B π)
      ≤ (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k) + k * (r m - r 1) := by
  have hr_pos := r_pos_of_priceSet hr
  have hr_mono := r_mono_of_priceSet hr
  obtain ⟨hB_pos, hB_step, hB_anti⟩ := B_props hr hα hB
  let A := hardInstance n k m B π
  let V : ℝ := (k : ℝ) * ∑ g : Fin n, r (phaseOf n m B g)
  have hOPT : OPT k m r A = V := by
    unfold OPT
    set S : Set ℝ := {v | ∃ x, LPFeasible k m A x ∧ v = lpObj m r A x}
    have h_ub : ∀ v ∈ S, v ≤ V := by
      rintro v ⟨x, hx, rfl⟩
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · dsimp [V, lpObj, A, hardInstance]
        simp
      · unfold lpObj
        have hstep1 : ∀ t : Fin A.T,
            (∑ i : Fin n, ∑ j ∈ Icc 1 m, A.p t i j * r j * x t i j) ≤
              r (phaseOf n m B ((t : ℕ) / k)) := by
          intro t
          have hp_bds := phaseOf_bounds n m hm B ((t : ℕ) / k)
          have hr_ph_pos : 0 < r (phaseOf n m B ((t : ℕ) / k)) :=
            hr_pos _ hp_bds.1 hp_bds.2
          have hterm : ∀ i : Fin n, ∀ j ∈ Icc 1 m,
              A.p t i j * r j * x t i j ≤ r (phaseOf n m B ((t : ℕ) / k)) * x t i j := by
            intro i j hj
            have hxj : 0 ≤ x t i j := hx.2.2 t i j
            apply mul_le_mul_of_nonneg_right _ hxj
            dsimp [A, hardInstance]
            split_ifs with hcond
            · rw [one_mul]
              exact hr_mono j _ hcond.2.1 hcond.2.2 hp_bds.2
            · rw [zero_mul]
              exact le_of_lt hr_ph_pos
          calc
            (∑ i : Fin n, ∑ j ∈ Icc 1 m, A.p t i j * r j * x t i j)
              ≤ ∑ i : Fin n, ∑ j ∈ Icc 1 m, r (phaseOf n m B ((t : ℕ) / k)) * x t i j :=
                sum_le_sum (fun i _ => sum_le_sum (fun j hj => hterm i j hj))
            _ = r (phaseOf n m B ((t : ℕ) / k)) * (∑ i : Fin n, ∑ j ∈ Icc 1 m, x t i j) := by
                simp only [← mul_sum]
            _ ≤ r (phaseOf n m B ((t : ℕ) / k)) * 1 :=
                mul_le_mul_of_nonneg_left (hx.2.1 t) (le_of_lt hr_ph_pos)
            _ = r (phaseOf n m B ((t : ℕ) / k)) := mul_one _
        calc
          (∑ t : Fin A.T, ∑ i : Fin n, ∑ j ∈ Icc 1 m, A.p t i j * r j * x t i j)
            ≤ ∑ t : Fin A.T, r (phaseOf n m B ((t : ℕ) / k)) := sum_le_sum (fun t _ => hstep1 t)
          _ = ∑ t ∈ range (n * k), r (phaseOf n m B (t / k)) := by
              exact Fin.sum_univ_eq_sum_range (fun t => r (phaseOf n m B (t / k))) (n * k)
          _ = (k : ℝ) * ∑ g ∈ range n, r (phaseOf n m B g) :=
              sum_div_eq n k hk (fun g => r (phaseOf n m B g))
          _ = V := by
              dsimp [V]
              rw [Fin.sum_univ_eq_sum_range (fun g => r (phaseOf n m B g)) n]
    have h_att : V ∈ S := by
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · refine ⟨fun _ _ _ => 0, ?_, ?_⟩
        · refine ⟨fun i => by simp, fun t => by simp, fun t i j => le_rfl⟩
        · dsimp [V, lpObj]
          simp
      · let x₀ : Fin A.T → Fin n → ℕ → ℝ := fun t i j =>
          if ((π.symm i : Fin n) : ℕ) = (t : ℕ) / k ∧ j = phaseOf n m B ((t : ℕ) / k) then 1 else 0
        refine ⟨x₀, ?_, ?_⟩
        · refine ⟨?_, ?_, ?_⟩
          · intro i
            have hinner : ∀ t : Fin A.T,
                (∑ j ∈ Icc 1 m, A.p t i j * x₀ t i j) =
                  if (t : ℕ) / k = ((π.symm i : Fin n) : ℕ) then 1 else 0 := by
              intro t
              have hp_bds := phaseOf_bounds n m hm B ((t : ℕ) / k)
              have hmem : phaseOf n m B ((t : ℕ) / k) ∈ Icc 1 m :=
                mem_Icc.mpr hp_bds
              have hcongr : ∀ j ∈ Icc 1 m,
                  A.p t i j * x₀ t i j =
                    if j = phaseOf n m B ((t : ℕ) / k) then
                      (if (t : ℕ) / k = ((π.symm i : Fin n) : ℕ) then (1 : ℝ) else 0)
                    else 0 := by
                intro j hj
                dsimp [A, hardInstance, x₀]
                split_ifs <;> try ring
                all_goals omega
              rw [sum_congr rfl hcongr, sum_ite_eq' (Icc 1 m) _ _, if_pos hmem]
            have hsum_t : (∑ t : Fin A.T, ∑ j ∈ Icc 1 m, A.p t i j * x₀ t i j) = (k : ℝ) := by
              rw [sum_congr rfl (fun t _ => hinner t)]
              change (∑ t : Fin (n * k), if (t : ℕ) / k = ((π.symm i : Fin n) : ℕ) then (1 : ℝ) else 0) = (k : ℝ)
              rw [Fin.sum_univ_eq_sum_range (fun t => if t / k = ((π.symm i : Fin n) : ℕ) then (1 : ℝ) else 0) (n * k)]
              rw [sum_div_eq n k hk (fun g => if g = ((π.symm i : Fin n) : ℕ) then (1 : ℝ) else 0)]
              rw [sum_ite_eq' (range n) ((π.symm i : Fin n) : ℕ) (fun _ => (1 : ℝ)),
                  if_pos (mem_range.mpr (π.symm i).isLt), mul_one]
            linarith
          · intro t
            have ht_div : (t : ℕ) / k < n := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact t.isLt)
            let g₀ : Fin n := ⟨(t : ℕ) / k, ht_div⟩
            have hp_bds := phaseOf_bounds n m hm B ((t : ℕ) / k)
            have hmem : phaseOf n m B ((t : ℕ) / k) ∈ Icc 1 m := mem_Icc.mpr hp_bds
            have hinner : ∀ i : Fin n,
                (∑ j ∈ Icc 1 m, x₀ t i j) = if i = π g₀ then 1 else 0 := by
              intro i
              have hi_iff : ((π.symm i : Fin n) : ℕ) = (t : ℕ) / k ↔ i = π g₀ := by
                change (π.symm i).val = g₀.val ↔ i = π g₀
                rw [← Fin.ext_iff, Equiv.symm_apply_eq]
              have hcongr : ∀ j ∈ Icc 1 m,
                  x₀ t i j = if j = phaseOf n m B ((t : ℕ) / k) then (if i = π g₀ then (1 : ℝ) else 0) else 0 := by
                intro j hj
                dsimp [x₀]
                by_cases h1 : ((π.symm i : Fin n) : ℕ) = (t : ℕ) / k
                · have h2 : i = π g₀ := hi_iff.mp h1
                  split_ifs <;> tauto
                · have h2 : i ≠ π g₀ := mt hi_iff.mpr h1
                  split_ifs <;> tauto
              rw [sum_congr rfl hcongr, sum_ite_eq' (Icc 1 m) _ _, if_pos hmem]
            rw [sum_congr rfl (fun i _ => hinner i), sum_ite_eq' univ (π g₀) (fun _ => (1 : ℝ)),
                if_pos (mem_univ _)]
          · intro t i j
            dsimp [x₀]
            split_ifs <;> linarith
        · symm
          unfold lpObj
          have h_t : ∀ t : Fin A.T,
              (∑ i : Fin n, ∑ j ∈ Icc 1 m, A.p t i j * r j * x₀ t i j) =
                r (phaseOf n m B ((t : ℕ) / k)) := by
            intro t
            have ht_div : (t : ℕ) / k < n := Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact t.isLt)
            let g₀ : Fin n := ⟨(t : ℕ) / k, ht_div⟩
            have hp_bds := phaseOf_bounds n m hm B ((t : ℕ) / k)
            have hmem : phaseOf n m B ((t : ℕ) / k) ∈ Icc 1 m := mem_Icc.mpr hp_bds
            have hinner : ∀ i : Fin n,
                (∑ j ∈ Icc 1 m, A.p t i j * r j * x₀ t i j) =
                  if i = π g₀ then r (phaseOf n m B ((t : ℕ) / k)) else 0 := by
              intro i
              have hi_iff : ((π.symm i : Fin n) : ℕ) = (t : ℕ) / k ↔ i = π g₀ := by
                change (π.symm i).val = g₀.val ↔ i = π g₀
                rw [← Fin.ext_iff, Equiv.symm_apply_eq]
              have hcongr : ∀ j ∈ Icc 1 m,
                  A.p t i j * r j * x₀ t i j =
                    if j = phaseOf n m B ((t : ℕ) / k) then
                      (if i = π g₀ then r (phaseOf n m B ((t : ℕ) / k)) else 0)
                    else 0 := by
                intro j hj
                dsimp [A, hardInstance, x₀]
                by_cases h1 : ((π.symm i : Fin n) : ℕ) = (t : ℕ) / k
                · have h2 : i = π g₀ := hi_iff.mp h1
                  have hle1 : (t : ℕ) / k ≤ ((π.symm i : Fin n) : ℕ) := by omega
                  have h1' := hp_bds.1
                  split_ifs <;> try (subst_vars; ring)
                  all_goals first | omega | tauto
                · have h2 : i ≠ π g₀ := mt hi_iff.mpr h1
                  split_ifs <;> try (subst_vars; ring)
                  all_goals first | omega | tauto
              rw [sum_congr rfl hcongr, sum_ite_eq' (Icc 1 m) _ _, if_pos hmem]
            rw [sum_congr rfl (fun i _ => hinner i), sum_ite_eq' univ (π g₀) _, if_pos (mem_univ _)]
          rw [sum_congr rfl (fun t _ => h_t t)]
          change (∑ t : Fin (n * k), r (phaseOf n m B ((t : ℕ) / k))) = V
          rw [Fin.sum_univ_eq_sum_range (fun t => r (phaseOf n m B (t / k))) (n * k)]
          rw [sum_div_eq n k hk (fun g => r (phaseOf n m B g))]
          dsimp [V]
          rw [Fin.sum_univ_eq_sum_range (fun g => r (phaseOf n m B g)) n]
    exact le_antisymm (csSup_le ⟨V, h_att⟩ h_ub) (le_csSup ⟨V, h_ub⟩ h_att)
  -- Now prove the two inequalities comparing V with ∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * n * k
  have h_sum_g : (∑ g : Fin n, r (phaseOf n m B g)) =
      (n : ℝ) * r 1 + ∑ j ∈ Icc 2 m, (r j - r (j - 1)) * ((n : ℝ) - (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ)) := by
    have h_each_g : ∀ g : Fin n,
        r (phaseOf n m B g) =
          r 1 + ∑ j ∈ Icc 2 m, (if ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ (g : ℕ) then r j - r (j - 1) else 0) := by
      intro g
      have hp_bds := phaseOf_bounds n m hm B g
      rw [r_telescope r (phaseOf n m B g) hp_bds.1]
      have hdown : ∀ j j', 2 ≤ j → j ≤ j' → j' ≤ m →
          ⌊(1 - B j') * (n : ℝ)⌋₊ ≤ (g : ℕ) → ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ (g : ℕ) := by
        intro j j' hj2 hjj' hj'm hle
        have hB_le : B j' ≤ B j := hB_anti j j' (by omega) hjj' hj'm
        have hmul : (1 - B j) * (n : ℝ) ≤ (1 - B j') * (n : ℝ) :=
          mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg n)
        exact le_trans (Nat.floor_mono hmul) hle
      have hfilt := filter_Icc_eq_Icc m (fun j => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ (g : ℕ)) hdown
      unfold phaseOf
      rw [← hfilt, sum_filter]
    rw [sum_congr rfl (fun g _ => h_each_g g), sum_add_distrib, sum_const, card_univ, Fintype.card_fin,
        nsmul_eq_mul, sum_comm]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [mem_Icc] at hj
    have hB_j_pos : 0 < B j := hB_pos j (by omega) hj.2
    have hB_j_le1 : B j ≤ 1 := by
      have := hB_anti 1 j le_rfl (by omega) hj.2
      rwa [hB.1] at this
    have hfloor_le_n : ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ n := by
      apply Nat.floor_le_of_le
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      nlinarith
    have hcount : (∑ g : Fin n, (if ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ (g : ℕ) then r j - r (j - 1) else 0)) =
        (r j - r (j - 1)) * ((n : ℝ) - (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ)) := by
      rw [Fin.sum_univ_eq_sum_range (fun g => if ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g then r j - r (j - 1) else 0) n]
      rw [← sum_filter]
      have hset : (range n).filter (fun g => ⌊(1 - B j) * (n : ℝ)⌋₊ ≤ g) = Ico ⌊(1 - B j) * (n : ℝ)⌋₊ n := by
        ext g; simp only [mem_filter, mem_range, mem_Ico]; omega
      rw [hset, sum_const, Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub hfloor_le_n, mul_comm]
    exact hcount
  have h_lhs_split : (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) =
      (n : ℝ) * r 1 + ∑ j ∈ Icc 2 m, (r j - r (j - 1)) * (B j * (n : ℝ)) := by
    have hsplit : Icc 1 m = insert 1 (Icc 2 m) := by
      ext j; simp only [mem_Icc, mem_insert]; omega
    rw [hsplit, sum_insert (by simp)]
    have h1 : (price r 1 - price r (1 - 1)) * B 1 * (n : ℝ) = (n : ℝ) * r 1 := by
      dsimp [price, MultiPriceOnline.Balance.pr]
      rw [hB.1]
      ring
    rw [h1]
    congr 1
    apply sum_congr rfl
    intro j hj
    rw [mem_Icc] at hj
    have hj0 : j ≠ 0 := by omega
    have hj10 : j - 1 ≠ 0 := by omega
    dsimp [price, MultiPriceOnline.Balance.pr]
    rw [if_neg hj0, if_neg hj10]
    ring
  have h_sum_factor : (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ) * (k : ℝ)) =
      (k : ℝ) * (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  have h_lb_g : (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) ≤
      ∑ g : Fin n, r (phaseOf n m B g) := by
    rw [h_lhs_split, h_sum_g]
    apply add_le_add le_rfl
    apply sum_le_sum
    intro j hj
    rw [mem_Icc] at hj
    have hr_diff_nonneg : 0 ≤ r j - r (j - 1) := by
      have := hr_mono (j - 1) j (by omega) (by omega) hj.2
      linarith
    have hB_j_le1 : B j ≤ 1 := by
      have := hB_anti 1 j le_rfl (by omega) hj.2
      rwa [hB.1] at this
    have hx_nonneg : 0 ≤ (1 - B j) * (n : ℝ) := mul_nonneg (by linarith) (Nat.cast_nonneg n)
    have hfloor_le : (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ) ≤ (1 - B j) * (n : ℝ) := Nat.floor_le hx_nonneg
    apply mul_le_mul_of_nonneg_left _ hr_diff_nonneg
    linarith
  have h_ub_g : (∑ g : Fin n, r (phaseOf n m B g)) ≤
      (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) + (r m - r 1) := by
    rw [h_lhs_split, h_sum_g, add_assoc]
    apply add_le_add le_rfl
    have htel : r m - r 1 = ∑ j ∈ Icc 2 m, (r j - r (j - 1)) := by
      have := r_telescope r m hm
      linarith
    rw [htel, ← sum_add_distrib]
    apply sum_le_sum
    intro j hj
    rw [mem_Icc] at hj
    have hr_diff_nonneg : 0 ≤ r j - r (j - 1) := by
      have := hr_mono (j - 1) j (by omega) (by omega) hj.2
      linarith
    have hx_lt : (1 - B j) * (n : ℝ) < (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    calc
      (r j - r (j - 1)) * ((n : ℝ) - (⌊(1 - B j) * (n : ℝ)⌋₊ : ℝ))
        ≤ (r j - r (j - 1)) * (B j * (n : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hr_diff_nonneg
      _ = (r j - r (j - 1)) * (B j * (n : ℝ)) + (r j - r (j - 1)) := by ring
  refine ⟨hOPT, ?_, ?_⟩
  · rw [hOPT, h_sum_factor]
    exact mul_le_mul_of_nonneg_left h_lb_g (Nat.cast_nonneg k)
  · rw [hOPT, h_sum_factor]
    calc
      (k : ℝ) * ∑ g : Fin n, r (phaseOf n m B g)
        ≤ (k : ℝ) * ((∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) + (r m - r 1)) :=
          mul_le_mul_of_nonneg_left h_ub_g (Nat.cast_nonneg k)
      _ = (k : ℝ) * (∑ j ∈ Icc 1 m, (price r j - price r (j - 1)) * B j * (n : ℝ)) + (k : ℝ) * (r m - r 1) := by ring
