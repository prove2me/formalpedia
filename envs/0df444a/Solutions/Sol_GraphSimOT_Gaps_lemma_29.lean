-- Prove2me | solution 1 for GraphSimOT.Gaps.lemma_29
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-23T04:10:16.222051+00:00
-- url     : https://prove2.me/submissions/30905809-e3dc-45c5-90aa-a2b8f6931e8a

import Mathlib
import Definitions.Def_GraphSimOT_Gaps_Distances
import Definitions.Def_GraphSimOT_Gaps_LocalEdit

open Matrix GraphSimOT.Gaps

namespace Lemma29Aux

lemma rhoH_cast_eq_sum {n : ℕ} (H : SimpleGraph (Fin n)) (w w' : Fin n) :
    (rhoH H w w' : ℝ) = ∑ w'' : Fin n, |adj H w w'' - adj H w' w''| := by
  classical
  unfold rhoH
  rw [Set.ncard_eq_toFinset_card', Finset.card_eq_sum_ones, Nat.cast_sum]
  set S : Finset (Fin n) := (symmDiff (H.neighborSet w) (H.neighborSet w')).toFinset
  have hsub : (∑ x ∈ S, ((1 : ℕ) : ℝ)) = ∑ w'' : Fin n, if w'' ∈ S then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr _ (fun _ _ => Nat.cast_one)
    ext x; simp
  rw [hsub]
  apply Finset.sum_congr rfl
  intro w'' _
  by_cases hw : H.Adj w w'' <;> by_cases hw' : H.Adj w' w'' <;>
    simp [S, Finset.mem_symmDiff, Set.mem_toFinset, SimpleGraph.mem_neighborSet, adj, hw, hw']

lemma adj_symm {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    adj G u v = adj G v u := by
  unfold adj
  by_cases h : G.Adj u v
  · simp [h, h.symm]
  · have h' : ¬ G.Adj v u := fun hvu => h hvu.symm
    simp [h, h']

lemma rhoH_le_localCost_add {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) (v w w' : Fin n) :
    (rhoH H w w' : ℝ) ≤ localCost G H Q v w + localCost G H Q v w' := by
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, -, hQcol⟩
  rw [rhoH_cast_eq_sum]
  calc
    ∑ w'' : Fin n, |adj H w w'' - adj H w' w''|
        = ∑ w'' : Fin n, (∑ v' : Fin n, Q v' w'') * |adj H w w'' - adj H w' w''| := by
            apply Finset.sum_congr rfl; intro w'' _
            rw [hQcol w'', one_mul]
    _ = ∑ v' : Fin n, ∑ w'' : Fin n, |adj H w w'' - adj H w' w''| * Q v' w'' := by
          have h1 : ∀ w'' : Fin n,
              (∑ v' : Fin n, Q v' w'') * |adj H w w'' - adj H w' w''| =
                ∑ v' : Fin n, |adj H w w'' - adj H w' w''| * Q v' w'' := by
            intro w''
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl; intro v' _; ring
          simp_rw [h1]
          exact Finset.sum_comm
    _ ≤ ∑ v' : Fin n, ∑ w'' : Fin n,
          (|adj G v v' - adj H w w''| * Q v' w'' + |adj G v v' - adj H w' w''| * Q v' w'') := by
          apply Finset.sum_le_sum; intro v' _
          apply Finset.sum_le_sum; intro w'' _
          rw [← add_mul]
          apply mul_le_mul_of_nonneg_right _ (hQnn v' w'')
          have htri : |adj H w w'' - adj H w' w''| =
              |(adj G v v' - adj H w' w'') - (adj G v v' - adj H w w'')| := by ring_nf
          rw [htri]
          exact (abs_sub _ _).trans_eq (add_comm _ _)
    _ = localCost G H Q v w + localCost G H Q v w' := by
          unfold localCost
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro v' _
          rw [← Finset.sum_add_distrib]

lemma deg_diff_le_localCost {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n)) (v w : Fin n) :
    |(∑ v' : Fin n, adj G v v') - (∑ w'' : Fin n, adj H w w'')| ≤ localCost G H Q v w := by
  rw [mem_doublyStochastic_iff_sum] at hQ
  rcases hQ with ⟨hQnn, hQrow, hQcol⟩
  have h1 : ∑ v' : Fin n, adj G v v' = ∑ v' : Fin n, ∑ w'' : Fin n, adj G v v' * Q v' w'' := by
    apply Finset.sum_congr rfl; intro v' _
    rw [← Finset.mul_sum, hQrow v', mul_one]
  have h2 : ∑ w'' : Fin n, adj H w w'' = ∑ v' : Fin n, ∑ w'' : Fin n, adj H w w'' * Q v' w'' := by
    calc
      ∑ w'' : Fin n, adj H w w'' = ∑ w'' : Fin n, adj H w w'' * (∑ v' : Fin n, Q v' w'') := by
          apply Finset.sum_congr rfl; intro w'' _
          rw [hQcol w'', mul_one]
      _ = ∑ w'' : Fin n, ∑ v' : Fin n, adj H w w'' * Q v' w'' := by
          apply Finset.sum_congr rfl; intro w'' _
          exact Finset.mul_sum _ _ _
      _ = ∑ v' : Fin n, ∑ w'' : Fin n, adj H w w'' * Q v' w'' := Finset.sum_comm
  rw [h1, h2, ← Finset.sum_sub_distrib]
  have hsub : ∀ v' : Fin n,
      (∑ w'' : Fin n, adj G v v' * Q v' w'') - (∑ w'' : Fin n, adj H w w'' * Q v' w'') =
        ∑ w'' : Fin n, (adj G v v' - adj H w w'') * Q v' w'' := by
    intro v'
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro w'' _; ring
  simp_rw [hsub]
  calc
    |∑ v' : Fin n, ∑ w'' : Fin n, (adj G v v' - adj H w w'') * Q v' w''|
        ≤ ∑ v' : Fin n, |∑ w'' : Fin n, (adj G v v' - adj H w w'') * Q v' w''| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ v' : Fin n, ∑ w'' : Fin n, |(adj G v v' - adj H w w'') * Q v' w''| :=
          Finset.sum_le_sum fun v' _ => Finset.abs_sum_le_sum_abs _ _
    _ = localCost G H Q v w := by
          unfold localCost
          apply Finset.sum_congr rfl; intro v' _
          apply Finset.sum_congr rfl; intro w'' _
          rw [abs_mul, abs_of_nonneg (hQnn v' w'')]

end Lemma29Aux

theorem solution {n : ℕ} (G H : SimpleGraph (Fin n)) (Q : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q ∈ doublyStochastic ℝ (Fin n))
    (hQopt : ∀ v w, 0 < Q v w → localCost G H Q v w ≤ dOT1 G H)
    (σ : Equiv.Perm (Fin n)) (hσ : ∀ v, 0 < Q v (σ v)) :
    (∀ v w, 0 < Q v w → (rhoH H (σ v) w : ℝ) ≤ 2 * dOT1 G H) ∧
    (dOT1 G H < 1 → ∀ v v', (G.Adj v v' ↔ H.Adj (σ v) (σ v'))) ∧
    (IsEmpty (G ≃g H) → 1 ≤ dOT1 G H) := by
  classical
  have hpart1 : ∀ v w, 0 < Q v w → (rhoH H (σ v) w : ℝ) ≤ 2 * dOT1 G H := by
    intro v w hQvw
    have hle := Lemma29Aux.rhoH_le_localCost_add G H Q hQ v (σ v) w
    have h1 := hQopt v (σ v) (hσ v)
    have h2 := hQopt v w hQvw
    linarith
  have hpart2 : dOT1 G H < 1 → ∀ v v', (G.Adj v v' ↔ H.Adj (σ v) (σ v')) := by
    intro hLlt
    have hQ' := hQ
    rw [mem_doublyStochastic_iff_sum] at hQ'
    rcases hQ' with ⟨hQnn, hQrow, -⟩
    let degG_Z : Fin n → ℤ := fun u => ∑ v' : Fin n, if G.Adj u v' then 1 else 0
    let degH_Z : Fin n → ℤ := fun x => ∑ w'' : Fin n, if H.Adj x w'' then 1 else 0
    have hdegG_cast : ∀ u : Fin n, (degG_Z u : ℝ) = ∑ v' : Fin n, adj G u v' := by
      intro u; simp only [degG_Z, adj, Int.cast_sum]; apply Finset.sum_congr rfl; intro v' _
      split_ifs <;> simp
    have hdegH_cast : ∀ x : Fin n, (degH_Z x : ℝ) = ∑ w'' : Fin n, adj H x w'' := by
      intro x; simp only [degH_Z, adj, Int.cast_sum]; apply Finset.sum_congr rfl; intro w'' _
      split_ifs <;> simp
    have hdeg_eq : ∀ u x : Fin n, 0 < Q u x → degG_Z u = degH_Z x := by
      intro u x hQux
      have hdiffR : |((degG_Z u - degH_Z x : ℤ) : ℝ)| < 1 := by
        rw [Int.cast_sub, hdegG_cast, hdegH_cast]
        exact (Lemma29Aux.deg_diff_le_localCost G H Q hQ u x).trans_lt
          ((hQopt u x hQux).trans_lt hLlt)
      rw [← Int.cast_abs] at hdiffR
      have hdiffZ : |degG_Z u - degH_Z x| < 1 := by exact_mod_cast hdiffR
      have hbounds := abs_lt.mp hdiffZ
      omega
    have hadj_supp : ∀ v w : Fin n, 0 < Q v w → ∀ w' : Fin n, adj H w' w = adj H w' (σ v) := by
      intro v w hQvw w'
      let z : Fin n → ℤ := fun w'' =>
        (if H.Adj (σ v) w'' then 1 else 0) - (if H.Adj w w'' then 1 else 0)
      have hz_sum : ∑ w'' : Fin n, z w'' = 0 := by
        simp only [z, Finset.sum_sub_distrib]
        change degH_Z (σ v) - degH_Z w = 0
        have h1 := hdeg_eq v (σ v) (hσ v)
        have h2 := hdeg_eq v w hQvw
        omega
      have hz_even : ∑ w'' : Fin n, |z w''| + ∑ w'' : Fin n, z w'' =
          2 * ∑ w'' : Fin n, (if H.Adj (σ v) w'' ∧ ¬ H.Adj w w'' then (1 : ℤ) else 0) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro w'' _
        by_cases h1 : H.Adj (σ v) w'' <;> by_cases h2 : H.Adj w w'' <;> simp [z, h1, h2]
      have hz_cast : ((∑ w'' : Fin n, |z w''| : ℤ) : ℝ) = (rhoH H (σ v) w : ℝ) := by
        rw [Lemma29Aux.rhoH_cast_eq_sum, Int.cast_sum]
        apply Finset.sum_congr rfl; intro w'' _
        by_cases h1 : H.Adj (σ v) w'' <;> by_cases h2 : H.Adj w w'' <;> simp [z, adj, h1, h2]
      have hz_lt2R : ((∑ w'' : Fin n, |z w''| : ℤ) : ℝ) < ((2 : ℤ) : ℝ) := by
        rw [hz_cast]
        have hbd := hpart1 v w hQvw
        push_cast
        linarith
      have hz_lt2 : ∑ w'' : Fin n, |z w''| < 2 := Int.cast_lt.mp hz_lt2R
      have hz_nn : 0 ≤ ∑ w'' : Fin n, |z w''| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      have hz_zero : ∑ w'' : Fin n, |z w''| = 0 := by omega
      have hw'_zero : |z w'| = 0 := by
        have hle : |z w'| ≤ ∑ w'' : Fin n, |z w''| :=
          Finset.single_le_sum (f := fun w'' => |z w''|) (fun _ _ => abs_nonneg _) (Finset.mem_univ w')
        linarith [abs_nonneg (z w')]
      rw [Lemma29Aux.adj_symm H w' w, Lemma29Aux.adj_symm H w' (σ v)]
      by_cases h1 : H.Adj (σ v) w' <;> by_cases h2 : H.Adj w w' <;>
        simp [z, adj, h1, h2] at hw'_zero ⊢
    intro v' v
    have hcost_eq : ∑ u : Fin n, |adj G v' u - adj H (σ v') (σ u)| = localCost G H Q v' (σ v') := by
      unfold localCost
      apply Finset.sum_congr rfl; intro u _
      have hinner : ∀ w : Fin n,
          |adj G v' u - adj H (σ v') w| * Q u w =
            |adj G v' u - adj H (σ v') (σ u)| * Q u w := by
        intro w
        rcases (hQnn u w).eq_or_lt with h0 | hpos
        · rw [← h0, mul_zero, mul_zero]
        · rw [hadj_supp u w hpos (σ v')]
      simp_rw [hinner, ← Finset.mul_sum, hQrow u, mul_one]
    have hlt1 : ∑ u : Fin n, |adj G v' u - adj H (σ v') (σ u)| < 1 := by
      rw [hcost_eq]
      exact (hQopt v' (σ v') (hσ v')).trans_lt hLlt
    have hsingle : |adj G v' v - adj H (σ v') (σ v)| ≤
        ∑ u : Fin n, |adj G v' u - adj H (σ v') (σ u)| :=
      Finset.single_le_sum (f := fun u => |adj G v' u - adj H (σ v') (σ u)|)
        (fun _ _ => abs_nonneg _) (Finset.mem_univ v)
    have hterm_lt : |adj G v' v - adj H (σ v') (σ v)| < 1 := hsingle.trans_lt hlt1
    by_cases hg : G.Adj v' v <;> by_cases hh : H.Adj (σ v') (σ v)
    · simp [hg, hh]
    · exfalso; simp [adj, hg, hh] at hterm_lt
    · exfalso; simp [adj, hg, hh] at hterm_lt
    · simp [hg, hh]
  have hpart3 : IsEmpty (G ≃g H) → 1 ≤ dOT1 G H := by
    intro hemp
    by_contra hlt
    have hlt' : dOT1 G H < 1 := lt_of_not_ge hlt
    have hiso := hpart2 hlt'
    let φ : G ≃g H :=
      { toEquiv := σ
        map_rel_iff' := fun {a b} => (hiso a b).symm }
    exact hemp.false φ
  exact ⟨hpart1, hpart2, hpart3⟩
