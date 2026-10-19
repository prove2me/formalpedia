-- Prove2me | solution 1 for LandauFunction.landau_le_exp_div_e
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:31:57.804097+00:00
-- url     : https://prove2.me/submissions/948380c1-b5f9-40ed-98a5-5273a9c4affa

import Mathlib
import Definitions.Def_LandauFunction_landau
open LandauFunction

namespace LandauPartition

lemma lcm_eq_one_of_le_one (s : Multiset ℕ) (h : ∀ a ∈ s, a ≤ 1) (hpos : ∀ a ∈ s, 0 < a) :
    s.lcm = 1 := by
  apply Nat.eq_one_of_dvd_one
  rw [Multiset.lcm_dvd]
  intro b hb
  have : b = 1 := le_antisymm (h b hb) (hpos b hb)
  rw [this]

/-- The partition of `n` attached to a permutation of `Fin n`. -/
def permPartition (n : ℕ) (σ : Equiv.Perm (Fin n)) : Nat.Partition n where
  parts := σ.cycleType + Multiset.replicate (n - σ.support.card) 1
  parts_pos := by
    intro i hi
    rcases Multiset.mem_add.mp hi with h | h
    · exact lt_of_lt_of_le (by norm_num) (Equiv.Perm.two_le_of_mem_cycleType h)
    · rw [Multiset.eq_of_mem_replicate h]; norm_num
  parts_sum := by
    have h1 := Equiv.Perm.sum_cycleType σ
    have h2 : σ.support.card ≤ n := by
      have := Finset.card_le_univ σ.support
      simpa using this
    rw [Multiset.sum_add, h1, Multiset.sum_replicate, smul_eq_mul, mul_one]
    omega

lemma permPartition_lcm (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (permPartition n σ).parts.lcm = orderOf σ := by
  simp only [permPartition]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (Multiset.replicate _ 1)
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha])
    (fun a ha => by rw [Multiset.eq_of_mem_replicate ha]; norm_num),
    lcm_one_right, Equiv.Perm.lcm_cycleType]
  exact normalize_eq _

lemma exists_perm (n : ℕ) (p : Nat.Partition n) :
    ∃ σ : Equiv.Perm (Fin n), orderOf σ = p.parts.lcm := by
  set m := p.parts.filter (fun a => 2 ≤ a) with hm
  have hsum : m.sum ≤ Fintype.card (Fin n) := by
    rw [Fintype.card_fin, ← p.parts_sum]
    calc m.sum ≤ m.sum + (p.parts.filter (fun a => ¬ 2 ≤ a)).sum := Nat.le_add_right _ _
      _ = p.parts.sum := by rw [← Multiset.sum_add, hm, Multiset.filter_add_not]
  obtain ⟨σ, hσ⟩ := (Equiv.Perm.exists_with_cycleType_iff (α := Fin n)).mpr
    ⟨hsum, fun a ha => (Multiset.mem_filter.mp ha).2⟩
  refine ⟨σ, ?_⟩
  rw [← Equiv.Perm.lcm_cycleType, hσ]
  conv_rhs => rw [← Multiset.filter_add_not (fun a => 2 ≤ a) p.parts]
  rw [Multiset.lcm_add, lcm_eq_one_of_le_one (p.parts.filter (fun a => ¬ 2 ≤ a))
    (fun a ha => by have := (Multiset.mem_filter.mp ha).2; omega)
    (fun a ha => p.parts_pos (Multiset.mem_filter.mp ha).1), lcm_one_right]
  exact (normalize_eq _).symm

end LandauPartition

open LandauPartition in
theorem landau_eq_sup (n : ℕ) :
    landau n = (Finset.univ : Finset (Nat.Partition n)).sup fun p => p.parts.lcm := by
  unfold landau
  apply le_antisymm
  · refine Finset.sup_le fun σ _ => ?_
    rw [← permPartition_lcm]
    exact Finset.le_sup (f := fun p : Nat.Partition n => p.parts.lcm) (Finset.mem_univ _)
  · refine Finset.sup_le fun p _ => ?_
    obtain ⟨σ, hσ⟩ := exists_perm n p
    rw [← hσ]
    exact Finset.le_sup (f := fun σ : Equiv.Perm (Fin n) => orderOf σ) (Finset.mem_univ _)

namespace LandauPartition

lemma nat_lt_exp (a : ℕ) : (a : ℝ) < Real.exp (a / Real.exp 1) := by
  have he0 : 0 < Real.exp 1 := Real.exp_pos 1
  have he1 := Real.exp_one_gt_d9
  have he2 := Real.exp_one_lt_d9
  have hne : (a : ℝ) / Real.exp 1 - 1 ≠ 0 := by
    intro h
    have : (a : ℝ) = Real.exp 1 := by
      field_simp at h; linarith
    rcases le_or_gt a 2 with ha | ha
    · have : (a : ℝ) ≤ 2 := by exact_mod_cast ha
      linarith
    · have : (3 : ℝ) ≤ a := by exact_mod_cast ha
      linarith
  have h := Real.add_one_lt_exp hne
  rw [sub_add_cancel, Real.exp_sub] at h
  rw [div_lt_div_iff_of_pos_right he0] at h
  exact h

lemma prod_le_exp (s : Multiset ℕ) :
    (s.prod : ℝ) ≤ Real.exp (s.sum / Real.exp 1) ∧
      (s ≠ 0 → (s.prod : ℝ) < Real.exp (s.sum / Real.exp 1)) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a t ih =>
    have ha := nat_lt_exp a
    have hP : (0 : ℝ) ≤ t.prod := by positivity
    have hE : 0 < Real.exp (t.sum / Real.exp 1) := Real.exp_pos _
    have key : ((a ::ₘ t).prod : ℝ) < Real.exp ((a ::ₘ t).sum / Real.exp 1) := by
      rw [Multiset.prod_cons, Multiset.sum_cons, Nat.cast_mul, Nat.cast_add, add_div, Real.exp_add]
      calc (a : ℝ) * t.prod ≤ a * Real.exp (t.sum / Real.exp 1) :=
            mul_le_mul_of_nonneg_left ih.1 (Nat.cast_nonneg a)
        _ < Real.exp (a / Real.exp 1) * Real.exp (t.sum / Real.exp 1) :=
            mul_lt_mul_of_pos_right ha hE
    exact ⟨key.le, fun _ => key⟩

lemma lcm_le_prod (s : Multiset ℕ) (hpos : ∀ i ∈ s, 0 < i) : s.lcm ≤ s.prod := by
  have h0 : 0 ∉ s := fun h => lt_irrefl 0 (hpos 0 h)
  apply Nat.le_of_dvd (Nat.pos_of_ne_zero (Multiset.prod_ne_zero h0))
  exact Multiset.lcm_dvd.mpr fun b hb => Multiset.dvd_prod hb

end LandauPartition

open LandauPartition in
theorem solution (n : ℕ) :
    (landau n : ℝ) ≤ Real.exp (n / Real.exp 1) ∧
      ((landau n : ℝ) = Real.exp (n / Real.exp 1) ↔ n = 0) := by
  obtain ⟨p, _, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Nat.Partition n))
    Finset.univ_nonempty (fun p => p.parts.lcm)
  rw [landau_eq_sup, hp]
  have hl : (p.parts.lcm : ℝ) ≤ p.parts.prod := by
    exact_mod_cast lcm_le_prod p.parts (fun i hi => p.parts_pos hi)
  have hb := prod_le_exp p.parts
  rw [p.parts_sum] at hb
  refine ⟨hl.trans hb.1, ⟨fun heq => ?_, fun hn => ?_⟩⟩
  · by_contra hn
    have hne : p.parts ≠ 0 := by
      intro h; apply hn; rw [← p.parts_sum, h, Multiset.sum_zero]
    linarith [hb.2 hne]
  · subst hn
    have h0 : p.parts = 0 := by
      rw [Multiset.eq_zero_iff_forall_notMem]
      intro a ha
      have h1 := p.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      rw [p.parts_sum] at h2
      omega
    rw [h0]
    simp
