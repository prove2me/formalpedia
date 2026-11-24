-- Prove2me | solution 1 for MeanBudgetXC.lemma_3_7
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T17:02:01.725343+00:00
-- url     : https://prove2.me/submissions/e61e6c31-5dca-436f-8f87-bd01cf48b2c3

import Mathlib
import Definitions.Def_MeanBudgetXC_rltPolytope

namespace MeanBudgetXC

theorem entry_comm_aux7 {V : Type*} [DecidableEq V] (q : Pair V → ℝ) (i j : V) :
    entry q i j = entry q j i := by
  unfold entry
  by_cases h : i = j
  · subst h; rfl
  · rw [dif_neg h, dif_neg (Ne.symm h)]
    exact congrArg q (Subtype.ext Sym2.eq_swap)

theorem entry_ind_aux7 {V : Type*} [DecidableEq V] (S : Finset V) (i j : V) :
    entry (fun e : Pair V => if e.1.toFinset ⊆ S then (1 : ℝ) else 0) i j =
      if i ≠ j ∧ i ∈ S ∧ j ∈ S then 1 else 0 := by
  unfold entry
  by_cases h : i = j
  · rw [dif_pos h, if_neg (fun hc => hc.1 h)]
  · rw [dif_neg h]
    simp only [Sym2.toFinset_mk_eq, Finset.insert_subset_iff, Finset.singleton_subset_iff]
    by_cases hij : i ∈ S ∧ j ∈ S
    · rw [if_pos hij, if_pos ⟨h, hij⟩]
    · rw [if_neg hij, if_neg (fun hc => hij hc.2)]

theorem entry_lin_aux7 {V : Type*} [DecidableEq V] (a b : Pair V → ℝ) (t : ℝ) (i j : V) :
    entry (fun e => (a e - t * b e) / (1 - t)) i j =
      (entry a i j - t * entry b i j) / (1 - t) := by
  unfold entry
  split_ifs <;> simp

theorem row_ind_aux7 {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) (i : V) :
    ∑ j, (if i ≠ j ∧ i ∈ S ∧ j ∈ S then (1 : ℝ) else 0) =
      ((S.card : ℝ) - 1) * (if i ∈ S then 1 else 0) := by
  rw [Finset.sum_boole]
  by_cases hi : i ∈ S
  · have hf : (Finset.univ.filter fun j => i ≠ j ∧ i ∈ S ∧ j ∈ S) = S.erase i := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
      constructor
      · rintro ⟨h1, -, h3⟩; exact ⟨Ne.symm h1, h3⟩
      · rintro ⟨h1, h3⟩; exact ⟨Ne.symm h1, hi, h3⟩
    rw [hf, Finset.card_erase_of_mem hi, if_pos hi,
      Nat.cast_sub (Finset.card_pos.mpr ⟨i, hi⟩)]
    simp
  · have hf : (Finset.univ.filter fun j => i ≠ j ∧ i ∈ S ∧ j ∈ S) = ∅ := by
      ext j; simp [hi]
    rw [hf, if_neg hi]; simp

end MeanBudgetXC

open MeanBudgetXC in
theorem solution {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (hd2 : 2 ≤ d)
    (hdN : d ≤ Fintype.card V) (xy : (V → ℝ) × (Pair V → ℝ)) (hxy : xy ∈ rltPolytope V d)
    (S : Finset V) (hS : S.card = d) (hin : ∀ i ∈ S, 1 / 2 < xy.1 i)
    (hout : ∀ j ∉ S, xy.1 j < 1 / 2) :
    xy = ((fun i => if i ∈ S then 1 else 0), fun e => if e.1.toFinset ⊆ S then 1 else 0) ∨
      xy ∉ Set.extremePoints ℝ (rltPolytope V d) := by
  classical
  by_cases hEq : xy =
      ((fun i => if i ∈ S then 1 else 0), fun e => if e.1.toFinset ⊆ S then 1 else 0)
  · exact Or.inl hEq
  right
  intro hext
  set z0 : (V → ℝ) × (Pair V → ℝ) :=
    ((fun i => if i ∈ S then 1 else 0), fun e => if e.1.toFinset ⊆ S then 1 else 0) with hz0
  simp only [rltPolytope, Set.mem_ofPred_eq] at hxy
  obtain ⟨hx01, hsum, hmc, hrow⟩ := hxy
  have hne : (Finset.univ : Finset V).Nonempty := by
    obtain ⟨i, _⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
    exact ⟨i, Finset.mem_univ i⟩
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun i => |xy.1 i - 1 / 2|) hne
  set t := |xy.1 k - 1 / 2| with ht
  have hsep : ∀ i, (i ∈ S → 1 / 2 + t ≤ xy.1 i) ∧ (i ∉ S → xy.1 i ≤ 1 / 2 - t) := by
    intro i
    have h := hk i (Finset.mem_univ i)
    constructor
    · intro hi
      have := hin i hi
      rw [abs_of_pos (by linarith)] at h; linarith
    · intro hi
      have := hout i hi
      rw [abs_of_neg (by linarith)] at h; linarith
  have ht0 : 0 < t := by
    by_cases hkS : k ∈ S
    · have := hin k hkS; rw [ht, abs_of_pos (by linarith)]; linarith
    · have := hout k hkS; rw [ht, abs_of_neg (by linarith)]; linarith
  have ht1 : t ≤ 1 / 2 := by
    have := hx01 k
    rw [ht]
    exact abs_sub_le_iff.mpr ⟨by linarith [this.2], by linarith [this.1]⟩
  have h1t : 0 < 1 - t := by linarith
  have hfact : ∀ i, if i ∈ S then 1 / 2 + t ≤ xy.1 i else xy.1 i ≤ 1 / 2 - t := by
    intro i
    split_ifs with h
    · exact (hsep i).1 h
    · exact (hsep i).2 h
  have hz0mem : z0 ∈ rltPolytope V d := by
    simp only [rltPolytope, Set.mem_ofPred_eq, hz0]
    refine ⟨fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_⟩
    · split_ifs <;> norm_num
    · rw [Finset.sum_boole]; simp [hS]
    · rw [entry_ind_aux7]
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;> norm_num [hi, hj, hij]
    · rw [Finset.sum_congr rfl (fun j _ => entry_ind_aux7 S i j), row_ind_aux7, hS]
  have hz0' := hz0mem
  simp only [rltPolytope, Set.mem_ofPred_eq] at hz0'
  obtain ⟨-, hzsum, -, hzrow⟩ := hz0'
  set w : (V → ℝ) × (Pair V → ℝ) := ((fun i => (xy.1 i - t * z0.1 i) / (1 - t)),
      fun e => (xy.2 e - t * z0.2 e) / (1 - t)) with hw
  have hwmem : w ∈ rltPolytope V d := by
    simp only [rltPolytope, Set.mem_ofPred_eq, hw]
    refine ⟨fun i => ⟨?_, ?_⟩, ?_, fun i j hij => ?_, fun i => ?_⟩
    · apply div_nonneg _ h1t.le
      have fi := hfact i
      have hzi : z0.1 i = if i ∈ S then 1 else 0 := rfl
      rw [hzi]
      by_cases hi : i ∈ S
      · rw [if_pos hi] at fi ⊢; linarith
      · rw [if_neg hi] at fi ⊢; linarith [(hx01 i).1]
    · rw [div_le_one h1t]
      have fi := hfact i
      have hzi : z0.1 i = if i ∈ S then 1 else 0 := rfl
      rw [hzi]
      by_cases hi : i ∈ S
      · rw [if_pos hi] at fi ⊢; linarith [(hx01 i).2]
      · rw [if_neg hi] at fi ⊢; linarith
    · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, hzsum,
        div_eq_iff (ne_of_gt h1t)]
      ring
    · rw [entry_lin_aux7]
      have hZ : entry z0.2 i j = if i ∈ S ∧ j ∈ S then 1 else 0 := by
        simp only [hz0]; rw [entry_ind_aux7]; simp [hij]
      have hzi : z0.1 i = if i ∈ S then 1 else 0 := rfl
      have hzj : z0.1 j = if j ∈ S then 1 else 0 := rfl
      rw [hZ, hzi, hzj]
      have Y0 := (hmc i j hij).1
      have Yi := (hmc i j hij).2.1
      have MC := (hmc i j hij).2.2
      have Yj : entry xy.2 i j ≤ xy.1 j := by
        rw [entry_comm_aux7]; exact (hmc j i (Ne.symm hij)).2.1
      have fi := hfact i
      have fj := hfact j
      by_cases hi : i ∈ S <;> by_cases hj : j ∈ S <;>
        simp only [hi, hj, ↓reduceIte, and_true, true_and, and_false, false_and, and_self]
          at fi fj ⊢ <;>
        refine ⟨div_nonneg (by linarith) h1t.le,
          (div_le_div_iff_of_pos_right h1t).mpr (by linarith), ?_⟩ <;>
        rw [← add_div, div_sub_one (ne_of_gt h1t), div_le_div_iff_of_pos_right h1t] <;>
        linarith
    · rw [Finset.sum_congr rfl (fun j _ => entry_lin_aux7 xy.2 z0.2 t i j), ← Finset.sum_div,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hrow i, hzrow i, ← mul_div_assoc]
      congr 1
      ring
  have hseg : xy ∈ openSegment ℝ z0 w := by
    refine ⟨t, 1 - t, ht0, h1t, by ring, ?_⟩
    have h1t' : (1 - t) ≠ 0 := ne_of_gt h1t
    refine Prod.ext (funext fun i => ?_) (funext fun e => ?_)
    · simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ h1t']
      ring
    · simp only [Prod.snd_add, Prod.smul_snd, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hw]
      rw [mul_div_assoc', mul_div_cancel_left₀ _ h1t']
      ring
  have h := (mem_extremePoints.mp hext).2 z0 hz0mem w hwmem hseg
  exact hEq h.1.symm
