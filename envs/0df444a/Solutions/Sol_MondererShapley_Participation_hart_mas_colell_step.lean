-- Prove2me | solution 1 for MondererShapley.Participation.hart_mas_colell_step
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:50:13.758849+00:00
-- url     : https://prove2.me/submissions/57bff482-dc12-4cea-9680-7cbc0271e391

import Mathlib
import Definitions.Def_MondererShapley_Participation_Solution
import Definitions.Def_MondererShapley_Participation_shapleyOn

open Finset MondererShapley.Participation

namespace CoalitionProof

variable {ι : Type*} [DecidableEq ι]

lemma recurrence (ψ : Solution ι) (hψ : IsEfficient ψ)
    (v : Finset ι → ℝ) (hv : v ∅ = 0)
    (P : Finset ι → ℝ)
    (hP : ∀ S : Finset ι, ∀ i ∈ S, P S - P (S \ {i}) = ψ (S ∪ {i}) v i)
    (S : Finset ι) :
    (S.card : ℝ) * P S = v S + ∑ i ∈ S, P (S.erase i) := by
  have hs : (∑ i ∈ S, (P S - P (S.erase i))) = v S := by
    calc
      _ = ∑ i ∈ S, ψ S v i := by
        apply Finset.sum_congr rfl
        intro i hi
        have h := hP S i hi
        simpa [Finset.sdiff_singleton_eq_erase, hi] using h
      _ = v S := hψ S v hv
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at hs
  linarith

lemma normalized_unique (v : Finset ι → ℝ) (P Q : Finset ι → ℝ)
    (hempty : P ∅ = Q ∅)
    (hP : ∀ S : Finset ι, (S.card : ℝ) * P S = v S + ∑ i ∈ S, P (S.erase i))
    (hQ : ∀ S : Finset ι, (S.card : ℝ) * Q S = v S + ∑ i ∈ S, Q (S.erase i)) : P = Q := by
  funext S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases he : S = ∅
    · subst S
      exact hempty
    · have hcard : (S.card : ℝ) ≠ 0 := by
        exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr he)
      have hs : (∑ i ∈ S, P (S.erase i)) = ∑ i ∈ S, Q (S.erase i) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact ih _ (Finset.erase_ssubset hi)
      have hp := hP S
      have hq := hQ S
      rw [hs] at hp
      exact mul_left_cancel₀ hcard (hp.trans hq.symm)

end CoalitionProof


open Finset MondererShapley.Participation

namespace ShapleyProof

noncomputable def coeff (m k : ℕ) : ℝ :=
  ((k - 1).factorial : ℝ) * (m - k).factorial / m.factorial

noncomputable def weight (m k : ℕ) : ℝ :=
  (k.factorial : ℝ) * (m - k - 1).factorial / m.factorial

lemma factorial_split (m : ℕ) (hm : 0 < m) :
    (m.factorial : ℝ) = (m : ℝ) * (m - 1).factorial := by
  have he : m = (m - 1) + 1 := by omega
  conv_lhs => rw [he, Nat.factorial_succ]
  push_cast
  have heR : ((m - 1 : ℕ) : ℝ) + 1 = (m : ℝ) := by exact_mod_cast he.symm
  rw [heR]

lemma coeff_succ (m k : ℕ) : coeff m (k + 1) = weight m k := by
  have he : m - (k + 1) = m - k - 1 := by omega
  simp [coeff, weight, he]

lemma coeff_recurrence (m k : ℕ) (hk : k < m) :
    (m : ℝ) * coeff m k = ((m - k : ℕ) : ℝ) * coeff (m - 1) k := by
  have hm : 0 < m := by omega
  have hmk : 0 < m - k := by omega
  have he : m - 1 - k = m - k - 1 := by omega
  have hmf : ((m - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold coeff
  rw [factorial_split m hm, factorial_split (m - k) hmk, he]
  field_simp

lemma coeff_difference (m k : ℕ) (hk : k < m) (hk0 : 0 < k) :
    coeff m k - coeff (m - 1) k = -weight m k := by
  have hm : 0 < m := by omega
  have hmk : 0 < m - k := by omega
  have he : m - 1 - k = m - k - 1 := by omega
  have hmf : ((m - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  unfold coeff weight
  rw [factorial_split m hm, factorial_split (m - k) hmk, factorial_split k hk0, he]
  rw [Nat.cast_sub (Nat.le_of_lt hk)]
  field_simp
  <;> ring

variable {ι : Type*} [DecidableEq ι]

noncomputable def potential (v : Finset ι → ℝ) (S : Finset ι) : ℝ :=
  ∑ T ∈ S.powerset, coeff S.card T.card * v T

lemma marginal (v : Finset ι → ℝ) (hv : v ∅ = 0) (S : Finset ι) (i : ι) (hi : i ∈ S) :
    potential v S - potential v (S.erase i) = shapleyOn S v i := by
  have hs : S = insert i (S.erase i) := (Finset.insert_erase hi).symm
  have hsplit := Finset.sum_powerset_insert (s := S.erase i) (a := i) (by simp)
    (fun T => coeff S.card T.card * v T)
  rw [← hs] at hsplit
  unfold potential shapleyOn
  rw [hsplit, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  have hsub := Finset.mem_powerset.mp hT
  have hit : i ∉ T := by
    intro hit
    have hh := hsub hit
    simpa using hh
  have hcard : T.card < S.card := by
    have hc := Finset.card_le_card hsub
    rw [Finset.card_erase_of_mem hi] at hc
    have hp := Finset.card_pos.mpr ⟨i, hi⟩
    omega
  rw [Finset.card_insert_of_notMem hit, coeff_succ]
  have hweight : ((T.card.factorial * (S.card - T.card - 1).factorial : ℕ) /
      (S.card.factorial : ℝ)) = weight S.card T.card := by simp [weight, Nat.cast_mul]
  rw [hweight, Finset.card_erase_of_mem hi]
  by_cases he : T = ∅
  · subst T
    simp [hv]
  · have hdiff := coeff_difference S.card T.card hcard
      (Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he))
    nlinarith [congrArg (fun r : ℝ => r * v T) hdiff]

lemma powerset_erase (S : Finset ι) (i : ι) :
    (S.erase i).powerset = S.powerset.filter (fun T => i ∉ T) := by
  ext T
  simp [Finset.mem_powerset, Finset.subset_erase]

lemma erased_sum (S : Finset ι) (f : Finset ι → ℝ) :
    (∑ i ∈ S, ∑ T ∈ (S.erase i).powerset, f T) =
      ∑ T ∈ S.powerset, ((S.card - T.card : ℕ) : ℝ) * f T := by
  simp_rw [powerset_erase, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.sum_filter]
  have he : S.filter (fun i => i ∉ T) = S \ T := by ext i; simp
  rw [he]
  simp [Finset.sum_const, nsmul_eq_mul, Finset.card_sdiff,
    Finset.inter_eq_left.mpr (Finset.mem_powerset.mp hT)]

lemma potential_recurrence (v : Finset ι → ℝ) (hv : v ∅ = 0) (S : Finset ι) :
    (S.card : ℝ) * potential v S = v S + ∑ i ∈ S, potential v (S.erase i) := by
  by_cases he : S = ∅
  · subst S
    simp [hv]
  have hpos : 0 < S.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he)
  have hsum : (∑ i ∈ S, potential v (S.erase i)) =
      ∑ T ∈ S.powerset, ((S.card - T.card : ℕ) : ℝ) * (coeff (S.card - 1) T.card * v T) := by
    calc
      _ = ∑ i ∈ S, ∑ T ∈ (S.erase i).powerset, coeff (S.card - 1) T.card * v T := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [potential, Finset.card_erase_of_mem hi]
      _ = _ := erased_sum S _
  have hdiff : (S.card : ℝ) * potential v S - (∑ i ∈ S, potential v (S.erase i)) = v S := by
    rw [hsum, potential, Finset.mul_sum, ← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single S]
    · simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero,
        zero_mul, mul_one, sub_zero, coeff]
      rw [factorial_split S.card hpos]
      have hn : (S.card : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hpos
      have hf : ((S.card - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero _
      field_simp
    · intro T hT hne
      have hcard : T.card < S.card := Finset.card_lt_card
        (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.mem_powerset.mp hT, hne⟩)
      have hc := coeff_recurrence S.card T.card hcard
      nlinarith [congrArg (fun r : ℝ => r * v T) hc]
    · intro hnot
      exact False.elim (hnot (Finset.mem_powerset.mpr Finset.Subset.rfl))
  linarith

lemma hart (ψ : Solution ι) (hψ : IsEfficient ψ) (v : Finset ι → ℝ) (hv : v ∅ = 0) :
    (∃ P : Finset ι → ℝ, ∀ S : Finset ι, ∀ i ∈ S,
      P S - P (S \ {i}) = ψ (S ∪ {i}) v i) ↔
      ∀ S : Finset ι, ∀ i ∈ S, ψ S v i = shapleyOn S v i := by
  constructor
  · rintro ⟨P, hP⟩
    let Q : Finset ι → ℝ := fun S => P S - P ∅
    have hQ : ∀ S : Finset ι, (S.card : ℝ) * Q S = v S + ∑ i ∈ S, Q (S.erase i) := by
      intro S
      have hr := CoalitionProof.recurrence ψ hψ v hv P hP S
      simp only [Q, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
      nlinarith
    have hEq : Q = potential v := CoalitionProof.normalized_unique v Q (potential v)
      (by simp [Q, potential, hv]) hQ (potential_recurrence v hv)
    intro S i hi
    have hm := hP S i hi
    simp only [Finset.sdiff_singleton_eq_erase, Finset.union_singleton,
      Finset.insert_eq_of_mem hi] at hm
    have hs := congrFun hEq S
    have hs' := congrFun hEq (S.erase i)
    have hh := marginal v hv S i hi
    dsimp [Q] at hs hs'
    linarith
  · intro h
    refine ⟨potential v, ?_⟩
    intro S i hi
    simpa [Finset.sdiff_singleton_eq_erase, hi, h S i hi] using marginal v hv S i hi

end ShapleyProof

theorem solution {ι : Type*} [DecidableEq ι] (ψ : Solution ι) (hψ : IsEfficient ψ)
    (v : Finset ι → ℝ) (hv : v ∅ = 0) :
    (∃ P : Finset ι → ℝ, ∀ S : Finset ι, ∀ i ∈ S, P S - P (S \ {i}) = ψ (S ∪ {i}) v i) ↔
      ∀ S : Finset ι, ∀ i ∈ S, ψ S v i = shapleyOn S v i := by
  exact ShapleyProof.hart ψ hψ v hv

#print axioms solution
