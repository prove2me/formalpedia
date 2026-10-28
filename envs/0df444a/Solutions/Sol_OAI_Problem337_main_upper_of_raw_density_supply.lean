-- Prove2me | solution 1 for OAI.Problem337.main_upper_of_raw_density_supply
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T10:09:21.998315+00:00
-- url     : https://prove2.me/submissions/6492ec22-04ba-4443-9f47-32dbb82e78cb

import Mathlib
import Definitions.Def_EgyptianFractions
import Definitions.Def_OAIQ8EF000

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_ResidueStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Rescale an arbitrary positive unit-fraction list by a positive integer. -/
theorem unit_fraction_list_scale {k : ℕ} (n : Fin k → ℕ) (z : ℕ)
    (hn : ∀ i, 0 < n i) (hz : 0 < z) :
    (∀ i, 0 < z * n i) ∧
      (∑ i : Fin k, (1 : ℚ) / (z * n i : ℕ)) =
        (1 : ℚ) / z * (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) := by
  refine ⟨fun i => Nat.mul_pos hz (hn i), ?_⟩
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  rw [one_div_mul_one_div]

/-- Adjoining the unit fraction produced by a residue step lifts any expansion
of the smaller numerator. Repeated denominators are deliberately permitted. -/
theorem residue_step_list {k : ℕ} (M Q u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (ht : 0 < t) (hz : 0 < z)
    (htM : t ∣ M) (hres : Q * t + h = u * z)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = (h : ℚ) / (M * Q : ℕ)) :
    ∃ n' : Fin (k + 1) → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin (k + 1), (1 : ℚ) / (n' i : ℚ)) = (u : ℚ) / (M * Q : ℕ) := by
  have hMt : M / t * t = M := Nat.div_mul_cancel htM
  have hMtpos : 0 < M / t := by nlinarith
  obtain ⟨hpos, hscale⟩ := unit_fraction_list_scale n z hn hz
  refine ⟨Fin.cons ((M / t) * z) (fun i => z * n i), ?_, ?_⟩
  · intro i
    exact Fin.cases (Nat.mul_pos hMtpos hz) hpos i
  · rw [Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    rw [hscale, hsum]
    exact (residue_step_identity M Q u t z h hM hQ ht hz htM hres).symm

/-- Passing from a smaller denominator factor to a divisible larger one only
scales all unit denominators, and does not add terms. -/
theorem unit_fraction_list_change_factor {k : ℕ} (M Q Qnext h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext) (hdiv : Qnext ∣ Q)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      (h : ℚ) / (M * Qnext : ℕ)) :
    ∃ n' : Fin k → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin k, (1 : ℚ) / (n' i : ℚ)) = (h : ℚ) / (M * Q : ℕ) := by
  have hfac : Q / Qnext * Qnext = Q := Nat.div_mul_cancel hdiv
  have hfacpos : 0 < Q / Qnext := by nlinarith
  obtain ⟨hpos, hscale⟩ := unit_fraction_list_scale n (Q / Qnext) hn hfacpos
  refine ⟨fun i => (Q / Qnext) * n i, hpos, ?_⟩
  rw [hscale, hsum]
  have hMq : (0 : ℚ) < M := by exact_mod_cast hM
  have hQq : (0 : ℚ) < Q := by exact_mod_cast hQ
  have hQnextq : (0 : ℚ) < Qnext := by exact_mod_cast hQnext
  have hfacq : (0 : ℚ) < (Q / Qnext : ℕ) := by exact_mod_cast hfacpos
  have heq : ((Q / Qnext : ℕ) : ℚ) * Qnext = Q := by exact_mod_cast hfac
  push_cast
  field_simp
  nlinarith

/-- The full backward step, allowing the denominator factor to change by
an integer divisor between adjacent levels. -/
theorem residue_step_list_change_factor {k : ℕ} (M Q Qnext u t z h : ℕ)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext)
    (ht : 0 < t) (hz : 0 < z) (htM : t ∣ M) (hdiv : Qnext ∣ Q)
    (hres : Q * t + h = u * z)
    (n : Fin k → ℕ) (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) =
      (h : ℚ) / (M * Qnext : ℕ)) :
    ∃ n' : Fin (k + 1) → ℕ, (∀ i, 0 < n' i) ∧
      (∑ i : Fin (k + 1), (1 : ℚ) / (n' i : ℚ)) = (u : ℚ) / (M * Q : ℕ) := by
  obtain ⟨n', hn', hsum'⟩ :=
    unit_fraction_list_change_factor M Q Qnext h hM hQ hQnext hdiv n hn hsum
  exact residue_step_list M Q u t z h hM hQ ht hz htM hres n' hn' hsum'

/-- Every positive unit fraction in a list of total less than one has
an integer denominator at least two. -/
theorem unit_fraction_denominators_two_of_sum_lt_one {k : ℕ} (n : Fin k → ℕ)
    (hn : ∀ i, 0 < n i)
    (hsum : (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) < 1) :
    ∀ i, 2 ≤ n i := by
  intro i
  have hle : (1 : ℚ) / n i ≤ ∑ j : Fin k, (1 : ℚ) / n j :=
    Finset.single_le_sum (f := fun j : Fin k => (1 : ℚ) / n j) (fun j _ => by positivity) (Finset.mem_univ i)
  have hlt : (1 : ℚ) / n i < 1 := lt_of_le_of_lt hle hsum
  by_contra h
  have hni : n i = 1 := by have := hn i; omega
  simp [hni] at hlt

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BackwardExpansions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337.Descent

theorem UnitListAtMost.mono {x : ℚ} {B C : ℕ}
    (h : UnitListAtMost x B) (hBC : B ≤ C) : UnitListAtMost x C := by
  obtain ⟨k, hk, n, hn, hsum⟩ := h
  exact ⟨k, hk.trans hBC, n, hn, hsum⟩

theorem unitListAtMost_zero (B : ℕ) : UnitListAtMost 0 B := by
  refine ⟨0, Nat.zero_le _, Fin.elim0, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · simp

theorem UnitListAtMost.change_factor {B M Q Qnext h : ℕ}
    (H : UnitListAtMost ((h : ℚ) / (M * Qnext : ℕ)) B)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext) (hdiv : Qnext ∣ Q) :
    UnitListAtMost ((h : ℚ) / (M * Q : ℕ)) B := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  obtain ⟨n', hn', hsum'⟩ := unit_fraction_list_change_factor
    M Q Qnext h hM hQ hQnext hdiv n hn hsum
  exact ⟨k, hk, n', hn', hsum'⟩

theorem UnitListAtMost.residue_step {B M Q Qnext u t z h : ℕ}
    (H : UnitListAtMost ((h : ℚ) / (M * Qnext : ℕ)) B)
    (hM : 0 < M) (hQ : 0 < Q) (hQnext : 0 < Qnext)
    (ht : 0 < t) (hz : 0 < z) (htM : t ∣ M) (hdiv : Qnext ∣ Q)
    (hres : Q * t + h = u * z) :
    UnitListAtMost ((u : ℚ) / (M * Q : ℕ)) (B + 1) := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  obtain ⟨n', hn', hsum'⟩ := residue_step_list_change_factor
    M Q Qnext u t z h hM hQ hQnext ht hz htM hdiv hres n hn hsum
  exact ⟨k + 1, Nat.add_le_add_right hk 1, n', hn', hsum'⟩

/-- Backward propagation of bounded expansions through good numerator sets.
The hypotheses encode exactly the inherited-membership and successful-residue
alternatives in the dense-family construction. -/
theorem backward_good_set_expansions
    (M d B : ℕ) (Q : ℕ → ℕ) (G : ℕ → Set ℕ)
    (hM : 0 < M) (hQ : ∀ j, j ≤ d → 0 < Q j)
    (hdiv : ∀ j, j < d → Q (j + 1) ∣ Q j)
    (hterminal : ∀ u ∈ G d,
      UnitListAtMost ((u : ℚ) / (M * Q d : ℕ)) B)
    (hstep : ∀ j, j < d → ∀ u ∈ G j,
      u ∈ G (j + 1) ∨ ∃ t z h : ℕ,
        0 < t ∧ t ∣ M ∧ 0 < z ∧ Q j * t + h = u * z ∧
          (h = 0 ∨ h ∈ G (j + 1))) :
    ∀ j, j ≤ d → ∀ u ∈ G j,
      UnitListAtMost ((u : ℚ) / (M * Q j : ℕ)) (B + (d - j)) := by
  intro j hj
  induction hj using Nat.decreasingInduction with
  | self =>
      intro u hu
      simpa using hterminal u hu
  | of_succ j hj ih =>
      intro u hu
      have hQj := hQ j (by omega)
      have hQnext := hQ (j + 1) (by omega)
      rcases hstep j hj u hu with hu' | ⟨t, z, h, ht, htM, hz, hres, hh⟩
      · exact ((ih u hu').change_factor hM hQj hQnext (hdiv j hj)).mono (by omega)
      · have H : UnitListAtMost ((h : ℚ) / (M * Q (j + 1) : ℕ))
            (B + (d - (j + 1))) := by
          rcases hh with rfl | hh
          · simpa using unitListAtMost_zero (B + (d - (j + 1)))
          · exact ih h hh
        exact (H.residue_step hM hQj hQnext ht hz htM (hdiv j hj) hres).mono (by omega)

/-- If a propagated fraction is below one, its positive denominators are
all at least two, as required by the dense-family interface. -/
theorem UnitListAtMost.denominators_two {x : ℚ} {B : ℕ}
    (H : UnitListAtMost x B) (hx : x < 1) :
    ∃ k : ℕ, k ≤ B ∧ ∃ n : Fin k → ℕ,
      (∀ i, 2 ≤ n i) ∧ (∑ i : Fin k, (1 : ℚ) / (n i : ℚ)) = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H
  exact ⟨k, hk, n, unit_fraction_denominators_two_of_sum_lt_one n hn (hsum ▸ hx), hsum⟩

end Problem337.Descent

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_BadPredecessorCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- An indexed bipartite degree count. Repeated values of the maps retain
separate indices in `I`, exactly as required by the divisor descent. -/
theorem indexed_predecessor_count
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (U : Finset α) (H : Finset β) (I : Finset ι)
    (r : ι → α → β) (w : ι → β → ℝ) (L : ℝ) (hL : 0 < L)
    (hleft : ∀ u ∈ U, L ≤ ((I.filter (fun i => r i u ∈ H)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ H,
      ((U.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (U.card : ℝ) ≤ (∑ i ∈ I, ∑ h ∈ H, w i h) / L := by
  classical
  have hswap : (∑ u ∈ U, (I.filter (fun i => r i u ∈ H)).card) =
      ∑ i ∈ I, (U.filter (fun u => r i u ∈ H)).card := by
    simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Finset.sum_comm
  apply (le_div_iff₀ hL).2
  calc
    (U.card : ℝ) * L = ∑ _u ∈ U, L := by simp
    _ ≤ ∑ u ∈ U, ((I.filter (fun i => r i u ∈ H)).card : ℝ) :=
      Finset.sum_le_sum hleft
    _ = ∑ i ∈ I, ((U.filter (fun u => r i u ∈ H)).card : ℝ) := by
      exact_mod_cast hswap
    _ = ∑ i ∈ I, ∑ h ∈ H, ((U.filter (fun u => r i u = h)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact_mod_cast (Finset.sum_card_fiberwise_eq_card_filter U H (r i)).symm
    _ ≤ ∑ i ∈ I, ∑ h ∈ H, w i h := by
      exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (hright i hi))

/-- The degree count with an inherited set and an exceptional set removed. -/
theorem indexed_predecessor_count_with_exceptions
    {α β ι : Type*} [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (S E B U : Finset α) (H : Finset β) (I : Finset ι)
    (r : ι → α → β) (w : ι → β → ℝ) (L : ℝ) (hL : 0 < L)
    (hcover : S ⊆ E ∪ B ∪ U)
    (hleft : ∀ u ∈ U, L ≤ ((I.filter (fun i => r i u ∈ H)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ H,
      ((U.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (S.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) +
      (∑ i ∈ I, ∑ h ∈ H, w i h) / L := by
  have hcard : S.card ≤ E.card + B.card + U.card := by
    have h1 := Finset.card_le_card hcover
    have h2 := Finset.card_union_le (E ∪ B) U
    have h3 := Finset.card_union_le E B
    omega
  have hcardR : (S.card : ℝ) ≤ (E.card : ℝ) + (B.card : ℝ) + (U.card : ℝ) := by
    exact_mod_cast hcard
  have hU := indexed_predecessor_count U H I r w L hL hleft hright
  linarith

/-- The exact finite combinatorial inequality used to propagate bad numerators.
`H` is the current bad set, `Hnext` the next bad set, and `E` the Fourier
exception set. Fibers may be bounded by truncated divisor counts. -/
theorem descent_bad_predecessor_count
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (Y : ℝ) (ρ : ℝ)
    (r : ι → ℕ → ℕ) (w : ι → ℕ → ℝ)
    (hρ : 0 < ρ) (hI : I.Nonempty)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / 2 ≤ ((I.filter (fun i => r i u ∈ Hnext)).card : ℝ))
    (hright : ∀ i ∈ I, ∀ h ∈ Hnext,
      ((H.filter (fun u => r i u = h)).card : ℝ) ≤ w i h) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (2 / (ρ * (I.card : ℝ))) * (∑ i ∈ I, ∑ h ∈ Hnext, w i h) := by
  classical
  let U := H.filter (fun u => u ∉ E ∧ Y < (u : ℝ))
  have hIpos : (0 : ℝ) < (I.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hI
  have hL : 0 < ρ * (I.card : ℝ) / 2 := by positivity
  have hcover : H ⊆ E ∪ Hnext ∪ U := by
    intro u hu
    by_cases huE : u ∈ E
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ huE)
    · by_cases huY : (u : ℝ) ≤ Y
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (hinherit u hu huY))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hu, huE, lt_of_not_ge huY⟩)
  have h := indexed_predecessor_count_with_exceptions H E Hnext U Hnext I r w
    (ρ * (I.card : ℝ) / 2) hL hcover
    (fun u hu => by
      obtain ⟨huH, huE, huY⟩ := Finset.mem_filter.mp hu
      exact hleft u huH huE huY)
    (fun i hi h hh => by
      have hsub : U.filter (fun u => r i u = h) ⊆ H.filter (fun u => r i u = h) := by
        intro u hu
        obtain ⟨huU, hur⟩ := Finset.mem_filter.mp hu
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp huU).1, hur⟩
      have hcard : ((U.filter (fun u => r i u = h)).card : ℝ) ≤
          ((H.filter (fun u => r i u = h)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
      exact hcard.trans (hright i hi h hh))
  convert h using 1 <;> first | rfl | ring


/-- A fiber of a residue map consists of divisors of the shifted numerator. -/
theorem predecessor_fiber_le_divisors
    (H : Finset ℕ) (X : ℝ) (N h : ℕ) (r : ℕ → ℕ)
    (hN : 0 < N) (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hdiv : ∀ u ∈ H, u ∣ N + r u) :
    (H.filter (fun u => r u = h)).card ≤
      ((N + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card := by
  apply Finset.card_le_card
  intro u hu
  obtain ⟨huH, hur⟩ := Finset.mem_filter.mp hu
  apply Finset.mem_filter.mpr
  constructor
  · apply Nat.mem_divisors.mpr
    constructor
    · simpa only [hur] using hdiv u huH
    · omega
  · exact hX u huH

/-- The manuscript's bad-pair inequality, with actual truncated divisor counts. -/
theorem descent_bad_predecessor_divisor_count
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (X Y ρ : ℝ)
    (r : ι → ℕ → ℕ) (N : ι → ℕ)
    (hρ : 0 < ρ) (hI : I.Nonempty)
    (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hN : ∀ i ∈ I, 0 < N i)
    (hdiv : ∀ i ∈ I, ∀ u ∈ H, u ∣ N i + r i u)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / 2 ≤ ((I.filter (fun i => r i u ∈ Hnext)).card : ℝ)) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (2 / (ρ * (I.card : ℝ))) *
        (∑ i ∈ I, ∑ h ∈ Hnext,
          (((N i + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)) := by
  apply descent_bad_predecessor_count H Hnext E I Y ρ r _ hρ hI hinherit hleft
  intro i hi h hh
  exact_mod_cast predecessor_fiber_le_divisors H X (N i) h (r i)
    (hN i hi) hX (hdiv i hi)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RemoveRepetitions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- Replacing two equal unit fractions by two unequal smaller-first terms. -/
theorem reciprocal_pair_replacement (m : ℕ) (hm : 3 ≤ m) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ a < m ∧
      (1 : ℚ) / a + 1 / b = 1 / m + 1 / m := by
  rcases Nat.even_or_odd m with he | ho
  · rcases he with ⟨p, rfl⟩
    have hp : 2 ≤ p := by omega
    refine ⟨p + 1, p * (p + 1), by omega, by nlinarith, by omega, ?_⟩
    have hp0 : (p : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
  · rcases ho with ⟨p, rfl⟩
    have hp : 1 ≤ p := by omega
    refine ⟨p + 1, (p + 1) * (2 * p + 1), by omega, by nlinarith, by omega, ?_⟩
    push_cast
    field_simp
    ring

/-- Effect of a one-coordinate replacement on a finite reciprocal sum. -/
theorem reciprocal_sum_update {k : ℕ} (n : Fin k → ℕ) (i : Fin k) (a : ℕ) :
    (∑ t, (1 : ℚ) / (Function.update n i a t : ℚ)) =
      (∑ t, (1 : ℚ) / (n t : ℚ)) + 1 / (a : ℚ) - 1 / (n i : ℚ) := by
  classical
  simp_rw [Function.apply_update (fun _ (v : ℕ) => (1 : ℚ) / v)]
  rw [Finset.sum_update_of_mem (Finset.mem_univ i)]
  rw [Finset.sdiff_singleton_eq_erase, Finset.sum_erase_eq_sub (Finset.mem_univ i)]
  ring

/-- Two-coordinate replacement preserves the sum when the two reciprocals agree. -/
theorem reciprocal_sum_update_two {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i ≠ j) (a b : ℕ)
    (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j) :
    (∑ t, (1 : ℚ) / (Function.update (Function.update n i a) j b t : ℚ)) =
      ∑ t, (1 : ℚ) / (n t : ℚ) := by
  rw [reciprocal_sum_update, reciprocal_sum_update]
  simp only [Function.update_of_ne hij.symm]
  linarith

/-- Any first-coordinate decrease beats a later-coordinate change lexicographically. -/
theorem lex_update_two_lt {k : ℕ} (n : Fin k → ℕ) {i j : Fin k}
    (hij : i < j) (a b : ℕ) (ha : a < n i) :
    Pi.Lex (· < ·) (· < ·) (Function.update (Function.update n i a) j b) n := by
  refine ⟨i, ?_, ?_⟩
  · intro t ht
    simp [Function.update_of_ne (ne_of_lt ht), Function.update_of_ne (ne_of_lt (ht.trans hij))]
  · simpa [Function.update_of_ne (ne_of_lt hij)] using ha

/-- Takenouchi cleanup, proved using a lexicographically least tuple.
No distinctness or ordering is required of the original representation. -/
theorem remove_repetitions_below_one {k : ℕ} (x : ℚ)
    (hx : x < 1) (original : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ original i)
    (hsum : (∑ i, (1 : ℚ) / (original i : ℚ)) = x) :
    ∃ n : Fin k → ℕ, (∀ i, 2 ≤ n i) ∧ StrictMono n ∧
      (∑ i, (1 : ℚ) / (n i : ℚ)) = x := by
  classical
  let S : Set (Fin k → ℕ) :=
    {n | (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x}
  have hwf : WellFounded (Pi.Lex (· < ·) (fun {i : Fin k} (a b : ℕ) => a < b)) :=
    Pi.Lex.wellFounded (· < ·) (fun _ => wellFounded_lt)
  obtain ⟨n, hn, hminimal⟩ := hwf.has_min S ⟨original, hpos, hsum⟩
  change (∀ i, 1 ≤ n i) ∧ (∑ i, (1 : ℚ) / (n i : ℚ)) = x at hn
  have hreplace (i j : Fin k) (hij : i < j) (a b : ℕ)
      (ha : 1 ≤ a) (hb : 1 ≤ b) (halt : a < n i)
      (hab : (1 : ℚ) / a + 1 / b = 1 / n i + 1 / n j) : False := by
    apply hminimal (Function.update (Function.update n i a) j b) ?_
      (lex_update_two_lt n hij a b halt)
    constructor
    · intro t
      by_cases htj : t = j
      · subst t
        simpa using hb
      · by_cases hti : t = i
        · subst t
          simpa [Function.update_of_ne htj] using ha
        · simpa [Function.update_of_ne htj, Function.update_of_ne hti] using hn.1 t
    · rw [reciprocal_sum_update_two n hij.ne a b hab]
      exact hn.2
  have hsingle (i : Fin k) : (1 : ℚ) / n i ≤ x := by
    calc
      (1 : ℚ) / n i ≤ ∑ t : Fin k, (1 : ℚ) / n t := by
        exact Finset.single_le_sum (f := fun t : Fin k => (1 : ℚ) / n t) (fun t _ => by positivity) (Finset.mem_univ i)
      _ = x := hn.2
  have htwo : ∀ i, 2 ≤ n i := by
    intro i
    have hi := hn.1 i
    by_contra! h
    have heq : n i = 1 := by omega
    have := hsingle i
    norm_num [heq] at this
    linarith
  refine ⟨n, htwo, ?_, hn.2⟩
  intro i j hij
  by_contra! hnot
  rcases lt_or_eq_of_le hnot with hlt | heq
  · exact hreplace i j hij (n j) (n i) (hn.1 j) (hn.1 i) hlt (add_comm _ _)
  · have hpair : (1 : ℚ) / n i + 1 / n j ≤ x := by
      calc
        (1 : ℚ) / n i + 1 / n j = ∑ t ∈ ({i, j} : Finset (Fin k)), (1 : ℚ) / n t :=
          (Finset.sum_pair (f := fun t : Fin k => (1 : ℚ) / n t) hij.ne).symm
        _ ≤ ∑ t : Fin k, (1 : ℚ) / n t :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => by positivity)
        _ = x := hn.2
    have hm : 3 ≤ n i := by
      have hi := htwo i
      by_contra! h
      have heq2 : n i = 2 := by omega
      rw [heq, heq2] at hpair
      norm_num at hpair
      linarith
    obtain ⟨a, b, ha, hb, halt, hab⟩ := reciprocal_pair_replacement (n i) hm
    exact hreplace i j hij a b ha hb halt (by simpa [heq] using hab)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_CleanupApplications
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
namespace Problem337

/-- List-form interface for the dense-family and quantitative-tail constructions. -/
theorem egyptian_expansion_of_list (x : ℚ) (hx : x < 1) (l : List ℕ)
    (hpos : ∀ d ∈ l, 1 ≤ d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = x) :
    ∃ n : Fin l.length → ℕ, IsEgyptianExpansion x n := by
  apply remove_repetitions_below_one x hx l.get
  · intro i
    exact hpos _ (l.get_mem i)
  · have h := hsum
    rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn] at h
    exact h

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensePairing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- A dense subset of an initial interval represents an interior integer as a
sum of two of its elements, provided fewer than half its positive splits are
spoiled by missing elements. -/
theorem dense_pairing {N n : ℕ} (G : Finset ℕ) (hn : n ≤ N)
    (hcard : 2 * (Finset.Icc 1 N \ G).card < n - 1) :
    ∃ u ∈ G, ∃ v ∈ G, u + v = n := by
  classical
  by_contra h
  push Not at h
  let H := Finset.Icc 1 N \ G
  have hsub : Finset.Icc 1 (n - 1) ⊆ H ∪ H.image (fun u => n - u) := by
    intro u hu
    have hu' := Finset.mem_Icc.mp hu
    have hun : u ≤ n := by omega
    by_cases huG : u ∈ G
    · have hvG : n - u ∉ G := by
        intro hv
        exact h u huG (n - u) hv (by omega)
      have hvH : n - u ∈ H := by
        apply Finset.mem_sdiff.mpr
        exact ⟨Finset.mem_Icc.mpr (by omega), hvG⟩
      apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨n - u, hvH, by omega⟩
    · apply Finset.mem_union_left
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_Icc.mpr (by omega), huG⟩
  have hc := calc
    (Finset.Icc 1 (n - 1)).card ≤ (H ∪ H.image (fun u => n - u)).card :=
      Finset.card_le_card hsub
    _ ≤ H.card + (H.image (fun u => n - u)).card := Finset.card_union_le _ _
    _ ≤ H.card + H.card := Nat.add_le_add_left Finset.card_image_le _
  have hI : (Finset.Icc 1 (n - 1)).card = n - 1 := by simp
  rw [hI] at hc
  dsimp [H] at hc
  omega

/-- The real-parameter form used in the dense-family argument. -/
theorem dense_pairing_real (X : ℝ) (G : Finset ℕ) (n : ℕ)
    (hX : 4 < X) (hnlow : X / 2 ≤ (n : ℝ)) (hnup : (n : ℝ) ≤ X)
    (hbad : ((Finset.Icc 1 ⌊X⌋₊ \ G).card : ℝ) ≤ X / 8) :
    ∃ u ∈ G, ∃ v ∈ G, u + v = n := by
  apply dense_pairing G (Nat.le_floor hnup)
  have hc : (2 * (Finset.Icc 1 ⌊X⌋₊ \ G).card + 1 : ℝ) < (n : ℝ) := by
    nlinarith
  have hc' : 2 * (Finset.Icc 1 ⌊X⌋₊ \ G).card + 1 < n := by
    exact_mod_cast hc
  omega

/-- The largest integer multiple not exceeding `X` is at least `X / 2`,
provided the step size is positive and does not exceed `X`. -/
theorem floor_multiple_bounds {X a : ℝ} (ha : 0 < a) (haX : a ≤ X) :
    X / 2 ≤ (⌊X / a⌋₊ : ℝ) * a ∧ (⌊X / a⌋₊ : ℝ) * a ≤ X := by
  have ht : 1 ≤ X / a := (le_div_iff₀ ha).mpr (by simpa using haX)
  have hfloor : 1 ≤ ⌊X / a⌋₊ := Nat.le_floor (by simpa using ht)
  have hfloorR : (1 : ℝ) ≤ (⌊X / a⌋₊ : ℝ) := by exact_mod_cast hfloor
  have hlt := Nat.lt_floor_add_one (X / a)
  have hhalf : X / a ≤ 2 * (⌊X / a⌋₊ : ℝ) := by linarith
  have hmul := (div_le_iff₀ ha).mp hhalf
  have hupper := (le_div_iff₀ ha).mp (Nat.floor_le (by positivity : 0 ≤ X / a))
  constructor <;> nlinarith

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DenseExpansion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- Scaling every unit denominator divides the represented rational by the
same scale. Repetitions in the list are allowed. -/
theorem reciprocal_sum_map_mul (ds : List ℕ) (g : ℕ) :
    ((ds.map (fun d : ℕ => g * d)).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum / (g : ℚ) := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
      simp only [List.map_cons, List.sum_cons, ih, Nat.cast_mul]
      rw [add_div]
      congr 1
      rw [mul_comm, div_mul_eq_div_div]

/-- The dense-family additive argument for rational unit-fraction lists.
The lists supplied for good numerators may contain repeated denominators;
distinctification can be applied after adjoining a greedy prefix. -/
theorem dense_expansion_of_lists
    (X : ℝ) (a C M L : ℕ) (G : Finset ℕ)
    (ha : 0 < a) (hC : 0 < C) (hM : 0 < M) (hX : 4 < X)
    (haM : ((a * M : ℕ) : ℝ) ≤ X)
    (hdense : ((Finset.Icc 1 ⌊X⌋₊ \ G).card : ℝ) ≤ X / 8)
    (hG : ∀ u ∈ G, ∃ ds : List ℕ,
      (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ L ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (u : ℚ) / ((M * C : ℕ) : ℚ)) :
    ∃ ds : List ℕ, (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ 2 * L ∧
      (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum = (a : ℚ) / (C : ℚ) := by
  classical
  let d := a * M
  let g := ⌊X / (d : ℝ)⌋₊
  have hd : 0 < d := Nat.mul_pos ha hM
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hdX : (d : ℝ) ≤ X := haM
  have hg : 1 ≤ g := Nat.le_floor ((le_div_iff₀ hdR).mpr (by simpa using hdX))
  have hbounds := floor_multiple_bounds hdR hdX
  have hnlow : X / 2 ≤ ((g * d : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul] using hbounds.1
  have hnup : ((g * d : ℕ) : ℝ) ≤ X := by
    simpa only [Nat.cast_mul] using hbounds.2
  obtain ⟨u, hu, v, hv, huv⟩ := dense_pairing_real X G (g * d) hX hnlow hnup hdense
  obtain ⟨us, hus, hlenU, hsumU⟩ := hG u hu
  obtain ⟨vs, hvs, hlenV, hsumV⟩ := hG v hv
  refine ⟨(us ++ vs).map (fun q => g * q), ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    have hr2 : 2 ≤ r := (List.mem_append.mp hr).elim (hus r) (hvs r)
    have : r ≤ g * r := by simpa using Nat.mul_le_mul_right r hg
    omega
  · simp only [List.length_map, List.length_append]
    omega
  · rw [reciprocal_sum_map_mul]
    simp only [List.map_append, List.sum_append, hsumU, hsumV]
    have hg0 : (g : ℚ) ≠ 0 := by exact_mod_cast (by omega : g ≠ 0)
    have hM0 : (M : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hM)
    have hC0 : (C : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
    have hcast : (u : ℚ) + (v : ℚ) = (g : ℚ) * ((a : ℚ) * (M : ℚ)) := by
      exact_mod_cast huv
    push_cast
    rw [← add_div, hcast]
    field_simp

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DescentHolder
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
open scoped BigOperators

namespace Problem337

/-- Finite Hölder with one factor equal to one, in the normalization used
for the exceptional set in the descent. -/
theorem sum_le_card_rpow_mul_moment
    {ι : Type*} (H : Finset ι) (f : ι → ℝ) (r : ℝ)
    (hr : 1 < r) (hf : ∀ i ∈ H, 0 ≤ f i) :
    (∑ i ∈ H, f i) ≤
      (H.card : ℝ) ^ (1 - 1 / r) * (∑ i ∈ H, f i ^ r) ^ (1 / r) := by
  have hpq := Real.HolderConjugate.conjExponent hr
  have hq : 1 / Real.conjExponent r = 1 - 1 / r := by
    have h := hpq.inv_add_inv_eq_one
    simp only [one_div] at *
    linarith
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg H hpq.symm
    (f := fun _ => (1 : ℝ)) (g := f) (by intro i hi; norm_num) hf
  simpa only [one_mul, Real.one_rpow, Finset.sum_const, nsmul_eq_mul,
    mul_one, hq] using h

/-- Algebraic normalization of the Hölder moment bound. -/
theorem normalized_moment_factor
    (x Y E r : ℝ) (hx : 0 ≤ x) (hY : 0 < Y) :
    x ^ (1 - 1 / r) * (Y * Real.exp E) ^ (1 / r) =
      Y * Real.exp (E / r) * (x / Y) ^ (1 - 1 / r) := by
  rw [Real.mul_rpow hY.le (Real.exp_pos E).le, ← Real.exp_mul]
  rw [Real.div_rpow hx hY.le]
  have hpow : Y ^ (1 / r) = Y / Y ^ (1 - 1 / r) := by
    have he : 1 / r = 1 - (1 - 1 / r) := by ring
    conv_lhs => rw [he]
    rw [Real.rpow_sub hY, Real.rpow_one]
  rw [hpow]
  rw [div_eq_mul_inv E r]
  ring_nf

/-- A moment estimate on an ambient finite set controls its restriction to
an exceptional set, including the empty exceptional set. -/
theorem descent_holder_bound
    {ι : Type*} (I H : Finset ι) (f : ι → ℝ) (Y E r : ℝ)
    (hHI : H ⊆ I) (hf : ∀ i ∈ I, 0 ≤ f i) (hY : 0 < Y) (hr : 1 < r)
    (hmoment : (∑ i ∈ I, f i ^ r) ≤ Y * Real.exp E) :
    (∑ i ∈ H, f i) ≤
      Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) := by
  have hfH : ∀ i ∈ H, 0 ≤ f i := fun i hi => hf i (hHI hi)
  have hsum0 : 0 ≤ ∑ i ∈ H, f i ^ r :=
    Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (hfH i hi) r)
  have hsum : (∑ i ∈ H, f i ^ r) ≤ Y * Real.exp E := by
    apply le_trans _ hmoment
    exact Finset.sum_le_sum_of_subset_of_nonneg hHI
      (fun i hi _ => Real.rpow_nonneg (hf i hi) r)
  calc
    (∑ i ∈ H, f i) ≤
        (H.card : ℝ) ^ (1 - 1 / r) * (∑ i ∈ H, f i ^ r) ^ (1 / r) :=
      sum_le_card_rpow_mul_moment H f r hr hfH
    _ ≤ (H.card : ℝ) ^ (1 - 1 / r) * (Y * Real.exp E) ^ (1 / r) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.rpow_le_rpow hsum0 hsum (by positivity)
      · exact Real.rpow_nonneg (by positivity) _
    _ = Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) :=
      normalized_moment_factor _ Y E r (by positivity) hY

/-- Summing the uniform restricted moment estimate over a finite indexed
family does not require that distinct indices have distinct values. -/
theorem indexed_descent_holder_bound
    {ι κ : Type*} (J : Finset ι) (I H : Finset κ) (f : ι → κ → ℝ)
    (Y E r : ℝ) (hHI : H ⊆ I) (hY : 0 < Y) (hr : 1 < r)
    (hf : ∀ j ∈ J, ∀ i ∈ I, 0 ≤ f j i)
    (hmoment : ∀ j ∈ J, (∑ i ∈ I, f j i ^ r) ≤ Y * Real.exp E) :
    (∑ j ∈ J, ∑ i ∈ H, f j i) ≤
      (J.card : ℝ) * (Y * Real.exp (E / r) *
        ((H.card : ℝ) / Y) ^ (1 - 1 / r)) := by
  calc
    (∑ j ∈ J, ∑ i ∈ H, f j i) ≤
        ∑ _j ∈ J, Y * Real.exp (E / r) * ((H.card : ℝ) / Y) ^ (1 - 1 / r) := by
      apply Finset.sum_le_sum
      intro j hj
      exact descent_holder_bound I H (f j) Y E r hHI (hf j hj) hY hr (hmoment j hj)
    _ = _ := by simp

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityLoss
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- The bad-predecessor bound permits a polynomial loss in the lower degree;
indexed multiplicities and the actual truncated divisor fibers are retained. -/
theorem descent_bad_predecessor_divisor_count_loss
    {ι : Type*} [DecidableEq ι]
    (H Hnext E : Finset ℕ) (I : Finset ι) (X Y ρ P : ℝ)
    (res : ι → ℕ → ℕ) (N : ι → ℕ)
    (hρ : 0 < ρ) (hP : 0 < P) (hI : I.Nonempty)
    (hX : ∀ u ∈ H, (u : ℝ) ≤ X)
    (hN : ∀ i ∈ I, 0 < N i)
    (hdiv : ∀ i ∈ I, ∀ u ∈ H, u ∣ N i + res i u)
    (hinherit : ∀ u ∈ H, (u : ℝ) ≤ Y → u ∈ Hnext)
    (hleft : ∀ u ∈ H, u ∉ E → Y < (u : ℝ) →
      ρ * (I.card : ℝ) / P ≤ ((I.filter (fun i => res i u ∈ Hnext)).card : ℝ)) :
    (H.card : ℝ) ≤ (E.card : ℝ) + (Hnext.card : ℝ) +
      (P / (ρ * (I.card : ℝ))) *
        (∑ i ∈ I, ∑ h ∈ Hnext,
          (((N i + h).divisors.filter (fun u : ℕ => (u : ℝ) ≤ X)).card : ℝ)) := by
  have hJ : (0 : ℝ) < I.card := by exact_mod_cast Finset.card_pos.mpr hI
  have h := descent_bad_predecessor_divisor_count H Hnext E I X Y (2 * ρ / P)
    res N (by positivity) hI hX hN hdiv hinherit (by
      intro u hu huE huY
      convert hleft u hu huE huY using 1
      all_goals try with_reducible_and_instances rfl
      ring)
  have hfac : 2 / ((2 * ρ / P) * (I.card : ℝ)) = P / (ρ * (I.card : ℝ)) := by
    field_simp
  simpa only [hfac] using h

/-- Moment normalization with a general loss factor. A polynomial loss can
be absorbed by the separately proved exponential coefficient estimate. -/
theorem descent_recurrence_of_pair_and_moment_loss
    (a B T X Y ρ ε E r J P : ℝ) (hX : 0 < X) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (hJ : 0 < J) (hP : 0 ≤ P) (hY : Y = ρ * X)
    (hB0 : 0 ≤ B) (hBY : B ≤ Y) (hr : 1 < r)
    (hcoeff : 1 + P * Real.exp (E / r) ≤ Real.exp (2 * E))
    (hpair : a ≤ X * ε + B + (P / (ρ * J)) * T)
    (hsum : T ≤ J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) :
    a / X ≤ ε + Real.exp (2 * E) * (B / Y) ^ (1 - 1 / r) := by
  have hY0 : 0 < Y := by rw [hY]; positivity
  have hδ0 : 0 ≤ B / Y := div_nonneg hB0 hY0.le
  have hδ1 : B / Y ≤ 1 := (div_le_one hY0).mpr hBY
  have hinv : 0 ≤ 1 / r := by positivity
  have hδ : B / Y ≤ (B / Y) ^ (1 - 1 / r) :=
    Real.self_le_rpow_of_le_one hδ0 hδ1 (by linarith)
  have hρδ : ρ * (B / Y) ≤ B / Y := by nlinarith
  have hpow : 0 ≤ (B / Y) ^ (1 - 1 / r) := Real.rpow_nonneg hδ0 _
  have hbound : a ≤ X * ε + B + (P / (ρ * J)) *
      (J * (Y * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r))) := by
    exact hpair.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hsum (by positivity)))
  have hnorm : a / X ≤ ε + ρ * (B / Y) +
      P * Real.exp (E / r) * (B / Y) ^ (1 - 1 / r) := by
    apply (div_le_iff₀ hX).mpr
    apply hbound.trans
    apply le_of_eq
    subst Y
    field_simp
  have hmul := mul_le_mul_of_nonneg_right hcoeff hpow
  nlinarith

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DescentDecay
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter
open scoped Topology

namespace Problem337.DescentDecay

/-- The negative term in the density recurrence dominates the positive term. -/
theorem eventually_exponent_bound (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    ∀ᶠ S : ℝ in atTop,
      A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S ≤
        -(S ^ (1 / 4 : ℝ)) := by
  have hA1 : 0 < A + 1 := by linarith
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (div_pos hc hA1)
  filter_upwards [hsmall, eventually_gt_atTop (1 : ℝ)] with S hsmall hS
  have hS0 : 0 < S := lt_trans zero_lt_one hS
  have hlog : 0 < Real.log S := Real.log_pos hS
  rw [Real.norm_of_nonneg hlog.le,
    Real.norm_of_nonneg (Real.rpow_nonneg hS0.le _)] at hsmall
  have hprod : (A + 1) * Real.log S ≤ c * S ^ (1 / 2 : ℝ) := by
    calc
      (A + 1) * Real.log S ≤
          (A + 1) * (c / (A + 1) * S ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall hA1.le
      _ = c * S ^ (1 / 2 : ℝ) := by field_simp
  have hp : S ^ (1 / 2 : ℝ) * S ^ (1 / 4 : ℝ) = S ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_add hS0]
    norm_num
  have hscaled : (A + 1) * S ^ (1 / 4 : ℝ) ≤
      c * S ^ (3 / 4 : ℝ) / Real.log S := by
    apply (le_div_iff₀ hlog).mpr
    calc
      (A + 1) * S ^ (1 / 4 : ℝ) * Real.log S =
          ((A + 1) * Real.log S) * S ^ (1 / 4 : ℝ) := by ring
      _ ≤ (c * S ^ (1 / 2 : ℝ)) * S ^ (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right hprod (Real.rpow_nonneg hS0.le _)
      _ = c * S ^ (3 / 4 : ℝ) := by rw [mul_assoc, hp]
  nlinarith

/-- The coarse density bound tends to zero, uniformly in its fixed constants. -/
theorem tendsto_density_envelope_zero (A c K : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hK : 0 ≤ K) :
    Tendsto (fun S : ℝ => K * Real.log S *
      Real.exp (A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S))
      atTop (𝓝 0) := by
  have hsmall := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).bound
    (show (0 : ℝ) < 1 by norm_num)
  have hmajor : Tendsto (fun S : ℝ => K *
      (S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ))))) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4))
    simpa using h.const_mul K
  apply squeeze_zero' _ _ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with S hS
    exact mul_nonneg (mul_nonneg hK (Real.log_nonneg hS)) (Real.exp_pos _).le
  · filter_upwards [hsmall, eventually_exponent_bound A c hA hc,
      eventually_gt_atTop (1 : ℝ)] with S hsmall hexp hS
    have hS0 : 0 ≤ S := by linarith
    have hlog : 0 ≤ Real.log S := Real.log_nonneg hS.le
    rw [Real.norm_of_nonneg hlog,
      Real.norm_of_nonneg (Real.rpow_nonneg hS0 _), one_mul] at hsmall
    calc
      K * Real.log S * Real.exp
          (A * S ^ (1 / 4 : ℝ) - c * S ^ (3 / 4 : ℝ) / Real.log S) ≤
          K * S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ))) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hsmall hK) (Real.exp_le_exp.mpr hexp)
          (Real.exp_pos _).le (mul_nonneg hK (Real.rpow_nonneg hS0 _))
      _ = K * (S ^ (1 / 4 : ℝ) * Real.exp (-(S ^ (1 / 4 : ℝ)))) := by ring

/-- In particular the exceptional density is eventually at most one eighth. -/
theorem eventually_density_envelope_le_eighth (c K r : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop,
      K * Real.log S * Real.exp
        (2 * r * S ^ (1 / 4 : ℝ) - (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S) ≤
          1 / 8 := by
  have h := (tendsto_density_envelope_zero (2 * r) (c / 2) K
    (by positivity) (by positivity) hK).eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 8)
  exact h.mono fun _ hS => hS.le

/-- Uniform endgame for the unrolled recurrence with variable depth and scale. -/
theorem eventually_descent_bound_le_eighth (c K r : ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 0 ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ m d : ℝ,
      S / (2 * Real.log S) ≤ m → 0 ≤ d → d ≤ K * Real.log S →
      d * Real.exp (2 * r * S ^ (1 / 4 : ℝ) - c * m * S ^ (-1 / 4 : ℝ)) ≤
        1 / 8 := by
  filter_upwards [eventually_density_envelope_le_eighth c K r hc hK hr,
    eventually_gt_atTop (1 : ℝ)] with S hbound hS
  intro m d hm hd hdK
  have hS0 : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hpower : S * S ^ (-1 / 4 : ℝ) = S ^ (3 / 4 : ℝ) := by
    calc
      S * S ^ (-1 / 4 : ℝ) = S ^ (1 : ℝ) * S ^ (-1 / 4 : ℝ) := by
        rw [Real.rpow_one]
      _ = S ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hS0]; norm_num
  have hm' : (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S ≤
      c * m * S ^ (-1 / 4 : ℝ) := by
    calc
      (c / 2) * S ^ (3 / 4 : ℝ) / Real.log S =
          c * (S / (2 * Real.log S)) * S ^ (-1 / 4 : ℝ) := by
        rw [← hpower]
        ring
      _ ≤ c * m * S ^ (-1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hc.le)
          (Real.rpow_nonneg hS0.le _)
  apply le_trans _ hbound
  exact mul_le_mul hdK (Real.exp_le_exp.mpr (by linarith))
    (Real.exp_pos _).le (mul_nonneg hK hlog.le)

end Problem337.DescentDecay

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DescentRecurrence
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- A finite iteration estimate for the exceptional-set recurrence.  The
factor `A ^ (1 / (1 - α))` absorbs the geometric sum of exponents. -/
theorem descent_recurrence_bound
    (δ : ℕ → ℝ) (d : ℕ) (ε A α : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hδ0 : δ 0 = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ (j + 1) ≤ ε + A * (δ j) ^ α) :
    δ d ≤ (d : ℝ) * A ^ (1 / (1 - α)) * ε ^ (α ^ d) := by
  let B : ℝ := A ^ (1 / (1 - α))
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hB1 : 1 ≤ B := Real.one_le_rpow hA (by positivity)
  have hB0 : 0 ≤ B := le_trans zero_le_one hB1
  have hBfixed : A * B ^ α = B := by
    dsimp [B]
    rw [← Real.rpow_mul hA0]
    calc
      A * A ^ (1 / (1 - α) * α) = A ^ (1 + 1 / (1 - α) * α) := by
        rw [Real.rpow_add hApos, Real.rpow_one]
      _ = A ^ (1 / (1 - α)) := by
        congr 1
        field_simp [show 1 - α ≠ 0 by linarith]
        ring
  have hbound : ∀ j ≤ d, δ j ≤ (j : ℝ) * B * ε ^ (α ^ j) := by
    intro j
    induction j with
    | zero =>
      intro _
      simp [hδ0]
    | succ j ih =>
      intro hj
      have hjd : j ≤ d := by omega
      have hjlt : j < d := by omega
      have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
      have hpowε : 0 ≤ ε ^ (α ^ (j + 1)) := Real.rpow_nonneg hε0 _
      have hεsmall : ε ≤ ε ^ (α ^ (j + 1)) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge' hε0 hε1
          (pow_nonneg hα0.le _) (pow_le_one₀ hα0.le hα1.le)
      have hjpow : (j : ℝ) ^ α ≤ j := by
        cases j with
        | zero => simp [Real.zero_rpow hα0.ne']
        | succ j =>
          exact Real.rpow_le_self_of_one_le (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le j)) hα1.le
      have hpower : ((j : ℝ) * B * ε ^ (α ^ j)) ^ α =
          (j : ℝ) ^ α * B ^ α * ε ^ (α ^ (j + 1)) := by
        rw [Real.mul_rpow (mul_nonneg hj0 hB0) (Real.rpow_nonneg hε0 _),
          Real.mul_rpow hj0 hB0, ← Real.rpow_mul hε0, pow_succ]
      calc
        δ (j + 1) ≤ ε + A * (δ j) ^ α := hstep j hjlt
        _ ≤ ε + A * ((j : ℝ) * B * ε ^ (α ^ j)) ^ α := by
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (hδ j hjd) (ih hjd) hα0.le) hA0)
        _ = ε + (j : ℝ) ^ α * B * ε ^ (α ^ (j + 1)) := by
          rw [hpower]
          calc
            ε + A * ((j : ℝ) ^ α * B ^ α * ε ^ (α ^ (j + 1))) =
                ε + (j : ℝ) ^ α * (A * B ^ α) * ε ^ (α ^ (j + 1)) := by ring
            _ = _ := by rw [hBfixed]
        _ ≤ ε ^ (α ^ (j + 1)) + (j : ℝ) * B * ε ^ (α ^ (j + 1)) := by
          exact add_le_add hεsmall
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hjpow hB0) hpowε)
        _ ≤ (j + 1 : ℕ) * B * ε ^ (α ^ (j + 1)) := by
          push_cast
          nlinarith [mul_le_mul_of_nonneg_right hB1 hpowε]
  exact hbound d le_rfl

/-- The same estimate with the direction of indexing used by the backwards
construction of good numerator sets. -/
theorem descent_recurrence_bound_backward
    (δ : ℕ → ℝ) (d : ℕ) (ε A α : ℝ)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (hA : 1 ≤ A)
    (hα0 : 0 < α) (hα1 : α < 1)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ j ≤ ε + A * (δ (j + 1)) ^ α) :
    δ 0 ≤ (d : ℝ) * A ^ (1 / (1 - α)) * ε ^ (α ^ d) := by
  have h := descent_recurrence_bound (fun j => δ (d - j)) d ε A α
    hε0 hε1 hA hα0 hα1 (by simpa using hδd)
    (fun j _ => hδ (d - j) (Nat.sub_le d j)) (by
      intro j hj
      have ht : d - (j + 1) < d := by omega
      have heq : d - (j + 1) + 1 = d - j := by omega
      simpa only [heq] using hstep (d - (j + 1)) ht)
  simpa using h

/-- Exponential form of the finite exceptional-density estimate. -/
theorem descent_recurrence_exp_bound
    (δ : ℕ → ℝ) (d : ℕ) (a b α : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hα0 : 0 < α) (hα1 : α < 1)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d,
      δ j ≤ Real.exp (-b) + Real.exp a * (δ (j + 1)) ^ α) :
    δ 0 ≤ (d : ℝ) * Real.exp (a / (1 - α) - b * α ^ d) := by
  have h := descent_recurrence_bound_backward δ d (Real.exp (-b)) (Real.exp a) α
    (Real.exp_pos _).le (Real.exp_le_one_iff.mpr (by linarith))
    (Real.one_le_exp_iff.mpr ha) hα0 hα1 hδd hδ hstep
  calc
    δ 0 ≤ (d : ℝ) * (Real.exp a) ^ (1 / (1 - α)) *
        (Real.exp (-b)) ^ (α ^ d) := h
    _ = (d : ℝ) * Real.exp (a / (1 - α) - b * α ^ d) := by
      rw [← Real.exp_mul, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
      congr 2
      ring

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DescentDepth
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
namespace Problem337

/-- A logarithmic estimate uniform over the moment orders used in the
exceptional-set descent. -/
theorem log_one_sub_reciprocal_lower (r : ℝ) (hr : 2 ≤ r) :
    -(2 / r) ≤ Real.log (1 - 1 / r) := by
  have hrpos : 0 < r := by linarith
  have hr1 : 0 < r - 1 := by linarith
  have hα : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hα)
  rw [Real.log_inv] at hlog
  have hident : (1 - 1 / r)⁻¹ - 1 = 1 / (r - 1) := by
    field_simp
    ring
  have hfrac : 1 / (r - 1) ≤ 2 / r := by
    apply (div_le_div_iff₀ hr1 hrpos).mpr
    linarith
  rw [hident] at hlog
  linarith

/-- A moment order at least eight times the logarithmic depth constant
ensures that the repeated Hölder exponent loses at most a fourth power. -/
theorem descent_power_lower
    (r K S : ℝ) (d : ℕ) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
    (hS : 1 ≤ S) (hd : (d : ℝ) ≤ K * Real.log S) :
    S ^ (-(1 / 4 : ℝ)) ≤ (1 - 1 / r) ^ d := by
  have hrpos : 0 < r := by linarith
  have hSpos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hlogS : 0 ≤ Real.log S := Real.log_nonneg hS
  have hα : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hlog := log_one_sub_reciprocal_lower r hr
  have hlogmul := mul_le_mul_of_nonneg_left hlog (Nat.cast_nonneg d : (0 : ℝ) ≤ d)
  have hdepth : 2 * (d : ℝ) / r ≤ Real.log S / 4 := by
    apply (div_le_div_iff₀ hrpos (by norm_num : (0 : ℝ) < 4)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hKr hlogS]
  rw [Real.rpow_def_of_pos hSpos]
  apply (Real.le_log_iff_exp_le (pow_pos hα d)).mp
  rw [Real.log_pow]
  simp only [div_eq_mul_inv] at hlogmul hdepth ⊢
  nlinarith

/-- The explicit finite density estimate, before the final asymptotic
comparison of the positive and negative terms in the exponent. -/
theorem descent_density_exp_bound
    (δ : ℕ → ℝ) (d : ℕ) (r K S c m : ℝ)
    (hr : 2 ≤ r) (hKr : 8 * K ≤ r) (hS : 1 ≤ S)
    (hc : 0 ≤ c) (hm : 0 ≤ m) (hd : (d : ℝ) ≤ K * Real.log S)
    (hδd : δ d = 0) (hδ : ∀ j ≤ d, 0 ≤ δ j)
    (hstep : ∀ j < d, δ j ≤ Real.exp (-c * m) +
      Real.exp (2 * S ^ (1 / 4 : ℝ)) * (δ (j + 1)) ^ (1 - 1 / r)) :
    δ 0 ≤ (d : ℝ) * Real.exp
      (2 * r * S ^ (1 / 4 : ℝ) - c * m * S ^ (-(1 / 4 : ℝ))) := by
  have hrpos : 0 < r := by linarith
  have hS0 : 0 ≤ S := le_trans zero_le_one hS
  have hα0 : 0 < 1 - 1 / r := by
    have : 1 / r < (1 : ℝ) := (div_lt_one hrpos).mpr (by linarith)
    linarith
  have hα1 : 1 - 1 / r < 1 := by
    have : 0 < 1 / r := div_pos zero_lt_one hrpos
    linarith
  have hrec := descent_recurrence_exp_bound δ d (2 * S ^ (1 / 4 : ℝ)) (c * m)
    (1 - 1 / r) (by positivity) (mul_nonneg hc hm) hα0 hα1 hδd hδ
    (by simpa only [neg_mul] using hstep)
  have hid : 2 * S ^ (1 / 4 : ℝ) / (1 - (1 - 1 / r)) =
      2 * r * S ^ (1 / 4 : ℝ) := by
    field_simp
    ring
  rw [hid] at hrec
  apply hrec.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg d)
  apply Real.exp_le_exp.mpr
  have hpow := descent_power_lower r K S d hr hKr hS hd
  nlinarith [mul_le_mul_of_nonneg_left hpow (mul_nonneg hc hm)]

end Problem337

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GoodNumeratorSets
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

private theorem goodNumeratorAux_subset
    (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) (n j : ℕ) :
    goodNumeratorAux X I res n j ⊆ Finset.Icc 1 ⌊X j⌋₊ := by
  cases n with
  | zero => exact Finset.Subset.refl _
  | succ n => exact Finset.filter_subset _ _

/-- The good numerator sets exist for arbitrary finite indexed residue maps.
No arithmetic distribution or analytic estimate is required for this recursion. -/
theorem exists_good_numerator_sets
    (d : ℕ) (X : ℕ → ℝ) (I : ℕ → Finset ℕ) (res : ℕ → ℕ → ℕ → ℕ) :
    ∃ G : ℕ → Finset ℕ,
      (∀ j ≤ d, G j ⊆ Finset.Icc 1 ⌊X j⌋₊) ∧
      G d = Finset.Icc 1 ⌊X d⌋₊ ∧
      (∀ j < d, ∀ u : ℕ, u ∈ G j ↔
        u ∈ Finset.Icc 1 ⌊X j⌋₊ ∧
        (u ∈ G (j + 1) ∨ ∃ i ∈ I j, res j i u = 0 ∨ res j i u ∈ G (j + 1))) := by
  classical
  let G : ℕ → Finset ℕ := fun j => goodNumeratorAux X I res (d - j) j
  refine ⟨G, fun j _ => goodNumeratorAux_subset X I res (d - j) j, ?_, ?_⟩
  · simp [G, goodNumeratorAux]
  · intro j hj u
    have hsub : d - j = (d - (j + 1)) + 1 := by omega
    change u ∈ goodNumeratorAux X I res (d - j) j ↔ _
    rw [hsub]
    simp only [goodNumeratorAux, Finset.mem_filter]
    rfl

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityAssembly
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators
open Filter

namespace Problem337

private theorem card_le_cutoff {H : Finset ℕ} {X : ℝ}
    (hX : 0 ≤ X) (hH : H ⊆ Finset.Icc 1 ⌊X⌋₊) : (H.card : ℝ) ≤ X := by
  have hcard : H.card ≤ ⌊X⌋₊ := by
    simpa using Finset.card_le_card hH
  exact (Nat.cast_le.mpr hcard).trans (Nat.floor_le hX)

/-- Pair counting and the actual shifted divisor moment give the normalized
nonlinear recurrence, including inherited bad numerators and list multiplicity. -/
theorem DensityBadFamily.recurrence
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityBadFamily S m ρ r c d)
    (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (hr : 1 < r)
    (j : ℕ) (hj : j < d) :
    ((F.bad j).card : ℝ) / F.cutoff j ≤ Real.exp (-c * m) +
      Real.exp (2 * S ^ (1 / 4 : ℝ)) *
        (((F.bad (j + 1)).card : ℝ) / F.cutoff (j + 1)) ^ (1 - 1 / r) := by
  have hjle : j ≤ d := by omega
  have hjnext : j + 1 ≤ d := by omega
  have hX : 0 < F.cutoff j := F.cutoff_pos j hjle
  have hY : 0 < F.cutoff (j + 1) := F.cutoff_pos (j + 1) hjnext
  have hJ : (0 : ℝ) < (F.indices j).card := by
    exact_mod_cast Finset.card_pos.mpr (F.indices_nonempty j hj)
  have hbounded : ∀ u ∈ F.bad j, (u : ℝ) ≤ F.cutoff j := by
    intro u hu
    have huf : u ≤ ⌊F.cutoff j⌋₊ := (Finset.mem_Icc.mp (F.bad_bounded j hjle hu)).2
    exact (Nat.cast_le.mpr huf).trans (Nat.floor_le hX.le)
  have hpair := descent_bad_predecessor_divisor_count_loss (F.bad j) (F.bad (j + 1))
    (F.exceptional j) (F.indices j) (F.cutoff j) (F.cutoff (j + 1)) ρ F.loss
    (F.residue j) (F.shift j) hρ0 F.loss_pos (F.indices_nonempty j hj) hbounded
    (F.shift_pos j hj) (F.residue_dvd j hj) (F.inherited j hj) (F.many_residues j hj)
  change ((F.bad j).card : ℝ) ≤ ((F.exceptional j).card : ℝ) +
    ((F.bad (j + 1)).card : ℝ) + (F.loss / (ρ * (F.indices j).card)) *
      (∑ i ∈ F.indices j, ∑ h ∈ F.bad (j + 1),
        densityDivisorCount (F.cutoff j) (F.shift j i + h)) at hpair
  have hpair' : ((F.bad j).card : ℝ) ≤ F.cutoff j * Real.exp (-c * m) +
    ((F.bad (j + 1)).card : ℝ) + (F.loss / (ρ * (F.indices j).card)) *
      (∑ i ∈ F.indices j, ∑ h ∈ F.bad (j + 1),
        densityDivisorCount (F.cutoff j) (F.shift j i + h)) := by
    exact hpair.trans (add_le_add (add_le_add (F.exception_bound j hj) le_rfl) le_rfl)
  have hsum := indexed_descent_holder_bound (F.indices j)
    (Finset.Icc 1 ⌊F.cutoff (j + 1)⌋₊) (F.bad (j + 1))
    (fun i h => densityDivisorCount (F.cutoff j) (F.shift j i + h))
    (F.cutoff (j + 1)) (S ^ (1 / 4 : ℝ)) r (F.bad_bounded (j + 1) hjnext)
    hY hr (by intros; exact Nat.cast_nonneg _) (F.moment_bound j hj)
  exact descent_recurrence_of_pair_and_moment_loss _ _ _ _ _ _ _ _ _ _ _ hX hρ0 hρ1 hJ
    F.loss_pos.le (F.cutoff_step j hj) (Nat.cast_nonneg _)
    (card_le_cutoff hY.le (F.bad_bounded (j + 1) hjnext)) hr F.loss_bound hpair' hsum

/-- The full counting/analytic density conclusion, conditional on explicit
residue and shifted-divisor-moment data, uniformly in all finite families. -/
theorem eventually_density_bad_card_le_eighth
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ : ℝ) (d : ℕ) (F : DensityBadFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 → ((F.bad 0).card : ℝ) ≤ F.cutoff 0 / 8 := by
  filter_upwards [DescentDecay.eventually_descent_bound_le_eighth c K r hc hK
    (by linarith), eventually_gt_atTop (1 : ℝ)] with S hdecay hS
  intro m ρ d F hm hd hρ0 hρ1
  have hS0 : 0 < S := by linarith
  have hlog : 0 < Real.log S := Real.log_pos hS
  have hm0 : 0 ≤ m := le_trans (by positivity) hm
  let δ : ℕ → ℝ := fun j => ((F.bad j).card : ℝ) / F.cutoff j
  have hδd : δ d = 0 := by simp [δ, F.terminal_empty]
  have hδ0 : ∀ j ≤ d, 0 ≤ δ j := by
    intro j hj
    exact div_nonneg (Nat.cast_nonneg _) (F.cutoff_pos j hj).le
  have hbound := descent_density_exp_bound δ d r K S c m hr hKr hS.le hc.le hm0 hd
    hδd hδ0 (fun j hj => F.recurrence hρ0 hρ1 (by linarith) j hj)
  have hsmall : δ 0 ≤ 1 / 8 := hbound.trans (by
    simpa only [neg_div] using hdecay m d hm (Nat.cast_nonneg d) hd)
  have hX : 0 < F.cutoff 0 := F.cutoff_pos 0 (Nat.zero_le d)
  have hcard := (div_le_iff₀ hX).mp hsmall
  simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hcard

/-- The same good-set specification supplies genuine unit-fraction lists;
this is not an additional expansion hypothesis at intermediate levels. -/
theorem DensityResidueFamily.good_expansions
    {S m ρ r c : ℝ} {d : ℕ} (F : DensityResidueFamily S m ρ r c d)
    (G : ℕ → Finset ℕ) (hG : F.GoodSets G) :
    ∀ j ≤ d, ∀ u ∈ G j,
      Descent.UnitListAtMost ((u : ℚ) / (F.denominator * F.factor j : ℕ))
        (F.baseLength + (d - j)) := by
  apply Descent.backward_good_set_expansions F.denominator d F.baseLength F.factor
    (fun j => (G j : Set ℕ)) F.denominator_pos F.factor_pos F.factor_dvd
  · intro u hu
    exact F.terminal_expansions u (hG.2.1 ▸ hu)
  · intro j hj u hu
    obtain ⟨huI, huStep⟩ := (hG.2.2 j hj u).mp hu
    rcases huStep with huNext | ⟨i, hi, hres⟩
    · exact Or.inl huNext
    · exact Or.inr ⟨F.divisor j i, F.quotient j i u, F.residue j i u,
        F.divisor_pos j hj i hi, F.divisor_dvd j hj i hi,
        F.quotient_pos j hj i hi u huI, F.residue_eq j hj i hi u huI, hres⟩

/-- Complete finite/analytic density construction from raw residue and moment
supply. The intermediate good sets and their expansions are constructed here. -/
theorem eventually_residue_family_dense
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 →
      ∃ G : Finset ℕ, G ⊆ Finset.Icc 1 ⌊F.cutoff 0⌋₊ ∧
        ((Finset.Icc 1 ⌊F.cutoff 0⌋₊ \ G).card : ℝ) ≤ F.cutoff 0 / 8 ∧
        ∀ u ∈ G, Descent.UnitListAtMost
          ((u : ℚ) / (F.denominator * F.factor 0 : ℕ)) (F.baseLength + d) := by
  filter_upwards [eventually_density_bad_card_le_eighth c K r hc hK hr hKr] with S hS
  intro m ρ d F hm hd hρ0 hρ1
  obtain ⟨G, hG⟩ := exists_good_numerator_sets d F.cutoff F.indices F.residue
  have hGood : F.GoodSets G := hG
  refine ⟨G 0, hG.1 0 (Nat.zero_le d), ?_, ?_⟩
  · exact hS m ρ d (F.toBadFamily G hGood) hm hd hρ0 hρ1
  · intro u hu
    simpa using F.good_expansions G hGood 0 (Nat.zero_le d) u hu

/-- Conversion to the list interface used by the elementary dense-family
reduction, retaining the same length bound. -/
theorem Descent.UnitListAtMost.to_density_list_two {x : ℚ} {B : ℕ}
    (H : Descent.UnitListAtMost x B) (hx : x < 1) :
    ∃ l : List ℕ, (∀ n ∈ l, 2 ≤ n) ∧ l.length ≤ B ∧
      (l.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum = x := by
  obtain ⟨k, hk, n, hn, hsum⟩ := H.denominators_two hx
  refine ⟨List.ofFn n, ?_, by simpa using hk, ?_⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    exact hn i
  · simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hsum

/-- A directly consumable list version of the density proposition. The only
additional hypotheses are the supplied terminal-length budget and the fact
that all represented fractions lie below one. -/
theorem eventually_residue_family_dense_lists
    (c K r : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ (m ρ L : ℝ) (d : ℕ) (F : DensityResidueFamily S m ρ r c d),
      S / (2 * Real.log S) ≤ m → (d : ℝ) ≤ K * Real.log S →
      0 < ρ → ρ ≤ 1 →
      ((F.baseLength + d : ℕ) : ℝ) ≤ L * Real.log S →
      F.cutoff 0 < ((F.denominator * F.factor 0 : ℕ) : ℝ) →
      ∃ G : Finset ℕ,
        ((Finset.Icc 1 ⌊F.cutoff 0⌋₊ \ G).card : ℝ) ≤ F.cutoff 0 / 8 ∧
        ∀ u ∈ G, ∃ ds : List ℕ,
          (∀ n ∈ ds, 2 ≤ n) ∧ (ds.length : ℝ) ≤ L * Real.log S ∧
          (ds.map (fun n : ℕ => (1 : ℚ) / (n : ℚ))).sum =
            (u : ℚ) / (F.denominator * F.factor 0 : ℕ) := by
  filter_upwards [eventually_residue_family_dense c K r hc hK hr hKr] with S hS
  intro m ρ L d F hm hd hρ0 hρ1 hlen hfrac
  obtain ⟨G, hGI, hholes, hG⟩ := hS m ρ d F hm hd hρ0 hρ1
  refine ⟨G, hholes, ?_⟩
  intro u hu
  have huX : (u : ℝ) ≤ F.cutoff 0 :=
    (Nat.cast_le.mpr (Finset.mem_Icc.mp (hGI hu)).2).trans
      (Nat.floor_le (F.cutoff_pos 0 (Nat.zero_le d)).le)
  have huD : u < F.denominator * F.factor 0 := by exact_mod_cast huX.trans_lt hfrac
  have hD : (0 : ℚ) < (F.denominator * F.factor 0 : ℕ) := by
    exact_mod_cast Nat.mul_pos F.denominator_pos (F.factor_pos 0 (Nat.zero_le d))
  have huq : (u : ℚ) / (F.denominator * F.factor 0 : ℕ) < 1 :=
    (div_lt_one hD).mpr (by exact_mod_cast huD)
  obtain ⟨ds, hds, hdslen, hdssum⟩ := (hG u hu).to_density_list_two huq
  exact ⟨ds, hds, (Nat.cast_le.mpr hdslen).trans hlen, hdssum⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_DensityParameters
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- Exponential ranges in the elementary passage from density to all numerators.
The constants are exactly `D_X = D_M + 2` and `D_C = 4 D_X`. -/
theorem dense_preparation_ranges (DM S : ℝ) (hDM : 1 < DM) (hS : 1 ≤ S) :
    1 < Real.exp (4 * (DM + 2) * S) ∧
    Real.exp S < Real.exp (4 * (DM + 2) * S) ∧
    4 < Real.exp ((DM + 2) * S) ∧
    (Real.exp (4 * (DM + 2) * S)) ^ 2 =
      Real.exp (2 * (4 * (DM + 2)) * S) ∧
    (∀ A M : ℝ, 0 ≤ A → A ≤ Real.exp S →
      0 ≤ M → M ≤ Real.exp (DM * S) →
      A * M ≤ Real.exp ((DM + 2) * S)) := by
  have hS0 : 0 < S := by linarith
  have hDM0 : 0 < DM := by linarith
  have hDX : 3 < (DM + 2) * S := by nlinarith
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply Real.one_lt_exp_iff.mpr
    positivity
  · apply Real.exp_lt_exp.mpr
    nlinarith
  · have := Real.add_one_le_exp ((DM + 2) * S)
    linarith
  · rw [sq, ← Real.exp_add]
    congr 1
    ring
  · intro A M hA hAb hM hMM
    calc
      A * M ≤ Real.exp S * Real.exp (DM * S) :=
        mul_le_mul hAb hMM hM (Real.exp_pos S).le
      _ = Real.exp (S + DM * S) := (Real.exp_add _ _).symm
      _ ≤ Real.exp ((DM + 2) * S) := Real.exp_le_exp.mpr (by nlinarith)

/-- A simultaneous eventual cutoff for all elementary density-parameter
requirements and a supplied lower threshold on `log b`. -/
theorem eventually_dense_preparation_ranges (DM S0 : ℝ) (hDM : 1 < DM) :
    ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      2 ≤ b ∧ S0 ≤ Real.log (b : ℝ) ∧ 1 ≤ Real.log (b : ℝ) ∧
      (b : ℝ) < Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) ∧
      4 < Real.exp ((DM + 2) * Real.log (b : ℝ)) := by
  have ht : Filter.Tendsto (fun b : ℕ => Real.log (b : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have he := (Filter.eventually_ge_atTop (2 : ℕ)).and
    ((ht.eventually_ge_atTop S0).and (ht.eventually_ge_atTop 1))
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp he
  refine ⟨b0, fun b hb => ?_⟩
  obtain ⟨hb2, hS0, hS1⟩ := hb0 b hb
  have hr := dense_preparation_ranges DM (Real.log (b : ℝ)) hDM hS1
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  exact ⟨hb2, hS0, hS1, by simpa [Real.exp_log hbpos] using hr.2.1, hr.2.2.1⟩

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GreedyBudget
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- A natural greedy step budget logarithmic in `S`, sufficient for a target
unreduced denominator `exp (D*S)`. -/
theorem exists_logarithmic_greedy_budget (D S : ℝ)
    (hS : Real.exp 1 ≤ S) (hDS : D ≤ S * Real.log 2) :
    ∃ N : ℕ,
      ((N + 1 : ℕ) : ℝ) ≤ (2 / Real.log 2 + 2) * Real.log S ∧
      Real.exp (D * S) * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hS0 : 0 < S := (Real.exp_pos 1).trans_le hS
  have hlogS : 1 ≤ Real.log S := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  let N : ℕ := ⌈2 * Real.log S / Real.log 2⌉₊
  have harg : 0 ≤ 2 * Real.log S / Real.log 2 := by positivity
  have hNlower : 2 * Real.log S ≤ (N : ℝ) * Real.log 2 := by
    exact (div_le_iff₀ htwo).mp (Nat.le_ceil _)
  have hNupper : (N : ℝ) < 2 * Real.log S / Real.log 2 + 1 :=
    Nat.ceil_lt_add_one harg
  have hpow : S ^ 2 ≤ (2 : ℝ) ^ N := by
    calc
      S ^ 2 = Real.exp (2 * Real.log S) := by
        rw [show (2 : ℝ) = (2 : ℕ) from rfl, Real.exp_nat_mul, Real.exp_log hS0]
      _ ≤ Real.exp ((N : ℝ) * Real.log 2) := Real.exp_le_exp.mpr hNlower
      _ = (2 : ℝ) ^ N := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  refine ⟨N, ?_, ?_⟩
  · push_cast
    have heq : 2 * Real.log S / Real.log 2 = (2 / Real.log 2) * Real.log S := by ring
    rw [heq] at hNupper
    nlinarith
  · have hcap : D * S ≤ (2 : ℝ) ^ N * Real.log 2 := by
      calc
        D * S ≤ (S * Real.log 2) * S := mul_le_mul_of_nonneg_right hDS hS0.le
        _ = S ^ 2 * Real.log 2 := by ring
        _ ≤ (2 : ℝ) ^ N * Real.log 2 := mul_le_mul_of_nonneg_right hpow htwo.le
    have hpositive : 0 < Real.exp (D * S) * (1 / 2 : ℝ) ^ (2 ^ N) := by positivity
    apply (Real.log_le_log_iff hpositive zero_lt_one).mp
    rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp, Real.log_pow,
      Real.log_one]
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      ring
    rw [hhalf]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    nlinarith

/-- The budget above is uniformly `O(log(log b))` for polynomial target
unreduced denominators, without choosing any numerical cutoff. -/
theorem eventually_logarithmic_greedy_budget (D : ℝ) :
    ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      ∃ N : ℕ,
        ((N + 1 : ℕ) : ℝ) ≤
          (2 / Real.log 2 + 2) * Real.log (Real.log (b : ℝ)) ∧
        Real.exp (D * Real.log (b : ℝ)) * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
  have ht : Filter.Tendsto (fun b : ℕ => Real.log (b : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have he : ∀ᶠ b : ℕ in Filter.atTop,
      Real.exp 1 ≤ Real.log (b : ℝ) ∧ D / Real.log 2 ≤ Real.log (b : ℝ) :=
    (ht.eventually_ge_atTop (Real.exp 1)).and (ht.eventually_ge_atTop (D / Real.log 2))
  obtain ⟨b0, hb0⟩ := Filter.eventually_atTop.mp he
  refine ⟨b0, fun b hb => ?_⟩
  exact exists_logarithmic_greedy_budget D (Real.log (b : ℝ)) (hb0 b hb).1
    ((div_le_iff₀ htwo).mp (hb0 b hb).2)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GreedyStep
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
namespace Problem337

/-- Arithmetic data for one step of the greedy Egyptian fraction algorithm. -/
theorem greedy_step_data (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hr : b % a ≠ 0) :
    ∃ z c : ℕ, 2 ≤ z ∧ 0 < c ∧ c < a ∧ c < b * z ∧
      (a : ℚ) / b = 1 / (z : ℚ) + (c : ℚ) / (b * z : ℕ) ∧
      (c : ℚ) / (b * z : ℕ) < 1 / (z : ℚ) := by
  let z := b / a + 1
  let c := a - b % a
  have hmod : b % a < a := Nat.mod_lt b ha
  have hquot : 1 ≤ b / a := Nat.one_le_div_iff ha |>.2 (by omega)
  have hz : 2 ≤ z := by dsimp [z]; omega
  have hc : 0 < c := by dsimp [c]; omega
  have hca : c < a := by dsimp [c]; omega
  have hcb : c < b := lt_trans hca hab
  have heq : a * z = b + c := by
    have hd := Nat.mod_add_div b a
    dsimp [z, c]
    rw [Nat.mul_add, Nat.mul_one]
    omega
  have hcz : c < b * z := by nlinarith
  have hbq : (0 : ℚ) < b := by exact_mod_cast (lt_trans ha hab)
  have hzq : (0 : ℚ) < z := by exact_mod_cast (by omega : 0 < z)
  have heqq : (a : ℚ) * z = b + c := by exact_mod_cast heq
  refine ⟨z, c, hz, hc, hca, hcz, ?_, ?_⟩
  · push_cast
    field_simp
    nlinarith
  · push_cast
    apply (div_lt_div_iff₀ (mul_pos hbq hzq) hzq).2
    have hcbq : (c : ℚ) < b := by exact_mod_cast hcb
    nlinarith

/-- The terminal, divisible case of the greedy algorithm. -/
theorem greedy_terminal_data (a b : ℕ) (ha : 0 < a) (hab : a < b)
    (hr : b % a = 0) :
    2 ≤ b / a ∧ (a : ℚ) / b = 1 / (b / a : ℕ) := by
  have hd : a * (b / a) = b := by
    have h := Nat.mod_add_div b a
    omega
  have hq : 2 ≤ b / a := by
    by_contra h
    have : b / a ≤ 1 := by omega
    have : a * (b / a) ≤ a := by nlinarith
    omega
  refine ⟨hq, ?_⟩
  have hbq : (0 : ℚ) < b := by exact_mod_cast (lt_trans ha hab)
  have hqq : (0 : ℚ) < (b / a : ℕ) := by exact_mod_cast (by omega : 0 < b / a)
  have hdq : (a : ℚ) * (b / a : ℕ) = b := by exact_mod_cast hd
  field_simp
  exact hdq

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_GreedyPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open scoped BigOperators

namespace Problem337

/-- A greedy step decreases the numerator and squares the remaining value. -/
theorem ordinary_greedy_step_bounded (a b : ℕ) (ha : 0 < a) (hab : a < b) :
    ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
      (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
        (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
      (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2 ∧
      (c : ℝ) / ((b * z : ℕ) : ℝ) < 1 / 2 := by
  have hb : 0 < b := lt_trans ha hab
  by_cases hr : b % a = 0
  · obtain ⟨hz, hsplit⟩ := greedy_terminal_data a b ha hab hr
    refine ⟨b / a, 0, hz, Nat.div_le_self b a, ha, ?_, ?_, ?_⟩
    · simpa using hsplit
    · simp only [Nat.cast_zero, zero_div]
      positivity
    · norm_num
  · obtain ⟨z, c, hz, hc, hca, hcbz, hsplit, htail⟩ :=
      greedy_step_data a b ha hab hr
    have hz0 : 0 < z := by omega
    have hbQ : (b : ℚ) ≠ 0 := by positivity
    have hzQ : (z : ℚ) ≠ 0 := by positivity
    have heqQ : (a : ℚ) * z = b + c := by
      push_cast at hsplit
      field_simp at hsplit
      nlinarith
    have heq : a * z = b + c := by exact_mod_cast heqQ
    have hzb : z ≤ b := by
      by_contra h
      have hz' : b + 1 ≤ z := by omega
      have hmul := Nat.mul_le_mul_left a hz'
      have hba : b ≤ a * b := by nlinarith
      nlinarith
    have hbR : (0 : ℝ) < b := by positivity
    have hzR : (0 : ℝ) < z := by positivity
    have hcaR : (c : ℝ) < a := by exact_mod_cast hca
    have habR : (a : ℝ) < b := by exact_mod_cast hab
    have hz2R : (2 : ℝ) ≤ z := by exact_mod_cast hz
    have heqR : (a : ℝ) * z = b + c := by exact_mod_cast heq
    have haR : (0 : ℝ) < a := by positivity
    have hcR : (0 : ℝ) < c := by positivity
    refine ⟨z, c, hz, hzb, hca, hsplit, ?_, ?_⟩
    · push_cast
      rw [div_pow]
      apply (div_le_div_iff₀ (mul_pos hbR hzR) (pow_pos hbR 2)).2
      have hh : (c : ℝ) * b ≤ (a : ℝ) ^ 2 * z := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hh hbR.le]
    · push_cast
      apply (div_lt_iff₀ (mul_pos hbR hzR)).2
      nlinarith

/-- The finite stopping argument needs only the squaring estimate for a greedy step. -/
theorem greedy_preparation_of_squaring
    (step : ∀ a b : ℕ, 0 < a → a < b →
      ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
        (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
          (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
        (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2)
    (N : ℕ) :
    ∀ (a b : ℕ) (T u : ℝ), 0 < a → a < b → 1 < T →
      (b : ℝ) < T ^ 2 → 0 ≤ u → (a : ℝ) / (b : ℝ) ≤ u →
      T * u ^ (2 ^ N) ≤ 1 → PreparedGreedyPrefix a b T N := by
  induction N with
  | zero =>
    intro a b T u ha hab hT hbT hu hxu hcap
    have hb : (0 : ℝ) < b := by exact_mod_cast (lt_trans ha hab)
    have haR : (1 : ℝ) ≤ a := by exact_mod_cast ha
    have hmul : (a : ℝ) ≤ u * b := (div_le_iff₀ hb).1 hxu
    have hu0 : 0 < u := by nlinarith
    have hTb : T ≤ (b : ℝ) := by
      simp only [pow_zero, pow_one] at hcap
      nlinarith
    refine ⟨[], a, b, by simp, by simp, le_rfl, by omega, ?_, Or.inr ?_⟩
    · simp
    · exact ⟨ha, hTb, hbT⟩
  | succ N ih =>
    intro a b T u ha hab hT hbT hu hxu hcap
    by_cases hTb : T ≤ (b : ℝ)
    · refine ⟨[], a, b, by simp, by simp, le_rfl, by omega, ?_, Or.inr ?_⟩
      · simp
      · exact ⟨ha, hTb, hbT⟩
    have hb_lt : (b : ℝ) < T := lt_of_not_ge hTb
    obtain ⟨z, c, hz, hzb, hca, hsplit, hsq⟩ := step a b ha hab
    have hb : 0 < b := lt_trans ha hab
    have hz0 : 0 < z := by omega
    have hbz : 0 < b * z := Nat.mul_pos hb hz0
    by_cases hc : c = 0
    · refine ⟨[z], 0, 1, by simp, ?_, by omega, by omega, ?_, Or.inl rfl⟩
      · simpa using hz
      · simpa [hc] using hsplit.symm
    have hc0 : 0 < c := Nat.pos_of_ne_zero hc
    have hcbz : c < b * z := by nlinarith
    have hbzT : ((b * z : ℕ) : ℝ) < T ^ 2 := by
      have hbR : (0 : ℝ) < b := by exact_mod_cast hb
      have hzbR : (z : ℝ) ≤ b := by exact_mod_cast hzb
      push_cast
      nlinarith
    have hxu0 : 0 ≤ (a : ℝ) / (b : ℝ) := by positivity
    have hcu : (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ u ^ 2 := by
      calc
        _ ≤ ((a : ℝ) / (b : ℝ)) ^ 2 := hsq
        _ ≤ u ^ 2 := pow_le_pow_left₀ hxu0 hxu 2
    have hcap' : T * (u ^ 2) ^ (2 ^ N) ≤ 1 := by
      have hex : 2 * 2 ^ N = 2 ^ (N + 1) := by simp [pow_succ, Nat.mul_comm]
      rw [← pow_mul, hex]
      exact hcap
    obtain ⟨l, A, C, hlen, hden, hAa, hC, hsum, halt⟩ :=
      ih c (b * z) T (u ^ 2) hc0 hcbz hT hbzT (sq_nonneg u) hcu hcap'
    refine ⟨z :: l, A, C, ?_, ?_, le_trans hAa (Nat.le_of_lt hca), hC, ?_, halt⟩
    · simp only [List.length_cons]
      omega
    · intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact hz
      · exact hden d hd
    · change (1 : ℚ) / (z : ℚ) + (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum +
        (A : ℚ) / (C : ℚ) = (a : ℚ) / (b : ℚ)
      linarith

/-- Prefixes may be prefixed by a single valid unit-fraction step. -/
theorem PreparedGreedyPrefix.prepend {a b z c N : ℕ} {T : ℝ}
    (h : PreparedGreedyPrefix c (b * z) T N) (hz : 2 ≤ z) (hca : c ≤ a)
    (hsplit : (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
      (c : ℚ) / ((b * z : ℕ) : ℚ)) : PreparedGreedyPrefix a b T (N + 1) := by
  obtain ⟨l, A, C, hlen, hden, hAc, hC, hsum, halt⟩ := h
  refine ⟨z :: l, A, C, ?_, ?_, le_trans hAc hca, hC, ?_, halt⟩
  · simp only [List.length_cons]
    omega
  · intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact hz
    · exact hden d hd
  · change (1 : ℚ) / (z : ℚ) + (l.map (fun d => (1 : ℚ) / (d : ℚ))).sum +
      (A : ℚ) / (C : ℚ) = (a : ℚ) / (b : ℚ)
    linarith

/-- Quantitative denominator preparation: `N+1` steps suffice as soon as
`T ≤ 2^(2^N)`. No reduction of the remaining fraction is performed. -/
theorem greedy_preparation_power (a b N : ℕ) (T : ℝ)
    (ha : 0 < a) (hab : a < b) (hbT : (b : ℝ) < T)
    (hTcap : T ≤ (2 : ℝ) ^ (2 ^ N)) : PreparedGreedyPrefix a b T (N + 1) := by
  obtain ⟨z, c, hz, hzb, hca, hsplit, hsq, hhalf⟩ := ordinary_greedy_step_bounded a b ha hab
  have hb : 0 < b := lt_trans ha hab
  have hz0 : 0 < z := by omega
  have hbz : 0 < b * z := Nat.mul_pos hb hz0
  have hT : 1 < T := by
    have hb2 : (2 : ℝ) ≤ b := by exact_mod_cast (show 2 ≤ b by omega)
    linarith
  by_cases hc : c = 0
  · refine ⟨[z], 0, 1, by simp, ?_, by omega, by omega, ?_, Or.inl rfl⟩
    · simpa using hz
    · simpa [hc] using hsplit.symm
  have hc0 : 0 < c := Nat.pos_of_ne_zero hc
  have hcbz : c < b * z := by nlinarith
  have hbzT : ((b * z : ℕ) : ℝ) < T ^ 2 := by
    have hbR : (0 : ℝ) < b := by positivity
    have hzbR : (z : ℝ) ≤ b := by exact_mod_cast hzb
    push_cast
    nlinarith
  have hcap : T * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1 := by
    rw [one_div_pow, mul_one_div]
    exact (div_le_one (by positivity)).2 hTcap
  have step : ∀ a b : ℕ, 0 < a → a < b →
      ∃ z c : ℕ, 2 ≤ z ∧ z ≤ b ∧ c < a ∧
        (a : ℚ) / (b : ℚ) = (1 : ℚ) / (z : ℚ) +
          (c : ℚ) / ((b * z : ℕ) : ℚ) ∧
        (c : ℝ) / ((b * z : ℕ) : ℝ) ≤ ((a : ℝ) / (b : ℝ)) ^ 2 := by
    intro a b ha hab
    obtain ⟨z, c, hz, hzb, hca, hsplit, hsq, _⟩ := ordinary_greedy_step_bounded a b ha hab
    exact ⟨z, c, hz, hzb, hca, hsplit, hsq⟩
  have hp := greedy_preparation_of_squaring step N c (b * z) T (1 / 2)
    hc0 hcbz hT hbzT (by norm_num) (le_of_lt hhalf) hcap
  exact hp.prepend hz (Nat.le_of_lt hca) hsplit

/-- Equivalent stopping bound in the form convenient for logarithmic budgets. -/
theorem greedy_preparation (a b N : ℕ) (T : ℝ)
    (ha : 0 < a) (hab : a < b) (hbT : (b : ℝ) < T)
    (hcap : T * (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1) :
    PreparedGreedyPrefix a b T (N + 1) := by
  apply greedy_preparation_power a b N T ha hab hbT
  rw [one_div_pow, mul_one_div] at hcap
  exact (div_le_one (by positivity)).1 hcap

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_MainUpperReduction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section

namespace Problem337

/-- A positive unit-fraction list below one controls the actual minimum length. -/
theorem egyptianLength_le_list_length {a b : ℕ} (hab : a < b)
    (l : List ℕ) (hden : ∀ d ∈ l, 2 ≤ d)
    (hsum : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
      (a : ℚ) / (b : ℚ)) : egyptianLength a b ≤ l.length := by
  have hb : (0 : ℚ) < b := by exact_mod_cast (show 0 < b by omega)
  obtain ⟨n, hn⟩ := egyptian_expansion_of_list ((a : ℚ) / (b : ℚ))
    ((div_lt_one hb).mpr (by exact_mod_cast hab)) l
    (fun d hd => le_trans (by decide) (hden d hd)) hsum
  exact Nat.sInf_le (show l.length ∈ egyptianLengths a b from ⟨n, hn⟩)

/-- For one fixed large denominator, the dense input and greedy preparation give
an explicit uniform length coefficient. -/
theorem egyptianLength_upper_of_dense_at
    (DM L : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (b N : ℕ) (hb : 2 ≤ b) (hS : Real.exp 1 ≤ Real.log (b : ℝ))
    (hbudget : ((N + 1 : ℕ) : ℝ) ≤
      (2 / Real.log 2 + 2) * Real.log (Real.log (b : ℝ)))
    (hcap : Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) *
      (1 / 2 : ℝ) ^ (2 ^ N) ≤ 1)
    (hdensity : ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * Real.log (b : ℝ)) →
      DenseEgyptianFamily DM L (Real.log (b : ℝ)) C) :
    ∀ a : ℕ, 1 ≤ a → a < b →
      (egyptianLength a b : ℝ) ≤
        (2 / Real.log 2 + 2 + 2 * L + 2) * Real.log (Real.log (b : ℝ)) := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hloglog : 1 ≤ Real.log (Real.log (b : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hS
    simpa using this
  have hS1 : 1 ≤ Real.log (b : ℝ) := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hrange := dense_preparation_ranges DM (Real.log (b : ℝ)) hDM hS1
  have hbT : (b : ℝ) < Real.exp (4 * (DM + 2) * Real.log (b : ℝ)) := by
    simpa [Real.exp_log hbpos] using hrange.2.1
  intro a ha hab
  obtain ⟨l, A, C, hlen, hden, hAa, hC, hsum, halt⟩ :=
    greedy_preparation a b N (Real.exp (4 * (DM + 2) * Real.log (b : ℝ)))
      ha hab hbT hcap
  simp only [List.bind_eq_flatMap, List.pure_def, ← List.map_eq_flatMap,
    List.map_map, Function.comp_def] at hsum
  rcases halt with hA0 | ⟨hA, hClow, hCup⟩
  · have hsum' : (l.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (a : ℚ) / (b : ℚ) := by simpa only [hA0, Nat.cast_zero, zero_div, add_zero] using hsum
    have hmin := egyptianLength_le_list_length hab l hden hsum'
    have hminR : (egyptianLength a b : ℝ) ≤ l.length := by exact_mod_cast hmin
    have hlenR : (l.length : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hlen
    nlinarith
  · have hCup' : (C : ℝ) ≤
        Real.exp (2 * (4 * (DM + 2)) * Real.log (b : ℝ)) := by
      rw [hrange.2.2.2.1] at hCup
      exact hCup.le
    obtain ⟨M, G, hMlow, hMup, hholes, hG⟩ := hdensity C hClow hCup'
    have hM : 0 < M := by
      have : (0 : ℝ) < M := (Real.exp_pos _).trans hMlow
      exact_mod_cast this
    have hAM : ((A * M : ℕ) : ℝ) ≤ Real.exp ((DM + 2) * Real.log (b : ℝ)) := by
      push_cast
      apply hrange.2.2.2.2 A M (by positivity) ?_ (by positivity) hMup
      rw [Real.exp_log hbpos]
      exact_mod_cast (show A ≤ b by omega)
    let K : ℕ := ⌈L * Real.log (Real.log (b : ℝ))⌉₊
    have hGK : ∀ u ∈ G, ∃ ds : List ℕ,
        (∀ d ∈ ds, 2 ≤ d) ∧ ds.length ≤ K ∧
        (ds.map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
          (u : ℚ) / ((M * C : ℕ) : ℚ) := by
      intro u hu
      obtain ⟨ds, hd, hl, hs⟩ := hG u hu
      refine ⟨ds, hd, ?_, hs⟩
      have hh : (ds.length : ℝ) ≤ K := hl.trans (Nat.le_ceil _)
      exact_mod_cast hh
    obtain ⟨tail, htail, htaillen, htailsum⟩ := dense_expansion_of_lists
      (Real.exp ((DM + 2) * Real.log (b : ℝ))) A C M K G hA hC hM
      hrange.2.2.1 hAM hholes hGK
    have hall : ∀ d ∈ l ++ tail, 2 ≤ d := by
      intro d hd
      exact (List.mem_append.mp hd).elim (hden d) (htail d)
    have hfullsum : ((l ++ tail).map (fun d : ℕ => (1 : ℚ) / (d : ℚ))).sum =
        (a : ℚ) / (b : ℚ) := by
      rw [List.map_append, List.sum_append, htailsum]
      exact hsum
    have hmin := egyptianLength_le_list_length hab (l ++ tail) hall hfullsum
    have hminR : (egyptianLength a b : ℝ) ≤ (l.length : ℝ) + tail.length := by
      exact_mod_cast (show egyptianLength a b ≤ l.length + tail.length by simpa using hmin)
    have hlenR : (l.length : ℝ) ≤ (N + 1 : ℕ) := by exact_mod_cast hlen
    have htailR : (tail.length : ℝ) ≤ 2 * (K : ℝ) := by exact_mod_cast htaillen
    have hK : (K : ℝ) < L * Real.log (Real.log (b : ℝ)) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    nlinarith

/-- Complete elementary reduction of the uniform upper bound to the dense-family
proposition. All other inputs (greedy stopping, splitting, and distinctification)
are proved in the imported modules. -/
theorem main_upper_of_dense_family
    (DM L S0 : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (hdensity : ∀ S : ℝ, S0 ≤ S → ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      DenseEgyptianFamily DM L S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  let c2 : ℝ := 2 / Real.log 2 + 2 + 2 * L + 2
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc2 : 0 < c2 := by dsimp [c2]; positivity
  obtain ⟨b1, hbudget⟩ := eventually_logarithmic_greedy_budget (4 * (DM + 2))
  obtain ⟨b2, hparams⟩ := eventually_dense_preparation_ranges DM (max S0 (Real.exp 1)) hDM
  refine ⟨c2, hc2, max b1 b2, fun b hb => ?_⟩
  obtain ⟨N, hN, hcap⟩ := hbudget b (le_trans (le_max_left _ _) hb)
  obtain ⟨hb2, hS, _, _, _⟩ := hparams b (le_trans (le_max_right _ _) hb)
  have hS0 : S0 ≤ Real.log (b : ℝ) := (le_max_left _ _).trans hS
  have hSexp : Real.exp 1 ≤ Real.log (b : ℝ) := (le_max_right _ _).trans hS
  have hupper : ∀ a : ℕ, 1 ≤ a → a < b →
      (egyptianLength a b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) :=
    egyptianLength_upper_of_dense_at DM L hDM hL b N hb2 hSexp hN hcap
      (hdensity (Real.log (b : ℝ)) hS0)
  have hloglog : 1 ≤ Real.log (Real.log (b : ℝ)) := by
    have := Real.log_le_log (Real.exp_pos 1) hSexp
    simpa using this
  have hnonneg : 0 ≤ c2 * Real.log (Real.log (b : ℝ)) := by positivity
  have hmax : maxEgyptianLength b ≤ ⌊c2 * Real.log (Real.log (b : ℝ))⌋₊ := by
    unfold maxEgyptianLength
    apply Finset.sup_le
    intro a ha
    by_cases hapos : 1 ≤ a
    · rw [ite_eq_left hapos]
      exact Nat.le_floor (hupper a hapos (Finset.mem_range.mp ha))
    · simp [hapos]
  exact (show (maxEgyptianLength b : ℝ) ≤
    (⌊c2 * Real.log (Real.log (b : ℝ))⌋₊ : ℝ) by exact_mod_cast hmax).trans
      (Nat.floor_le hnonneg)

end Problem337

end

end OAI
end

section
-- module Solutions.OAIQ8_EF.EgyptianFractions_RawDensityUpper
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI
noncomputable section
open Filter

namespace Problem337

/-- The checked density descent supplies exactly the input to the elementary
main-upper reduction. No additional fraction-size hypothesis is needed. -/
theorem eventually_dense_family_of_raw_supply
    (DM L c K r : ℝ) (hDM : 1 < DM) (hc : 0 < c) (hK : 0 ≤ K)
    (hr : 2 ≤ r) (hKr : 8 * K ≤ r) :
    ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      RawDensitySupply DM L c K r S C → DenseEgyptianFamily DM L S C := by
  filter_upwards [eventually_residue_family_dense_lists c K r hc hK hr hKr,
    eventually_ge_atTop (1 : ℝ)] with S hS hS1
  intro C hC hraw
  obtain ⟨m, ρ, d, F, hm, hd, hρ0, hρ1, hlen, hcut, hfactor, hMlow, hMup⟩ := hraw
  have hfrac : F.cutoff 0 < ((F.denominator * F.factor 0 : ℕ) : ℝ) := by
    rw [hcut, hfactor]
    have hX : Real.exp ((DM + 2) * S) < Real.exp (4 * (DM + 2) * S) := by
      apply Real.exp_lt_exp.mpr
      nlinarith
    have hMone : (1 : ℝ) ≤ F.denominator := by
      exact_mod_cast F.denominator_pos
    have hprod : (C : ℝ) ≤ ((F.denominator * C : ℕ) : ℝ) := by
      push_cast
      simpa using mul_le_mul_of_nonneg_right hMone (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
    exact hX.trans_le (hC.trans hprod)
  obtain ⟨G, hholes, hG⟩ := hS m ρ L d F hm hd hρ0 hρ1 hlen hfrac
  refine ⟨F.denominator, G, hMlow, hMup, ?_, ?_⟩
  · simpa only [hcut] using hholes
  · simpa only [hfactor] using hG

/-- Final composition of the two checked reductions. The sole remaining
construction premise is eventual existence of the raw arithmetic supply. -/
theorem main_upper_of_raw_density_supply_oai
    (DM L c K r : ℝ) (hDM : 1 < DM) (hL : 0 < L)
    (hc : 0 < c) (hK : 0 ≤ K) (hr : 2 ≤ r) (hKr : 8 * K ≤ r)
    (hsupply : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      RawDensitySupply DM L c K r S C) :
    ∃ c2 : ℝ, 0 < c2 ∧ ∃ b0 : ℕ, ∀ b : ℕ, b0 ≤ b →
      (maxEgyptianLength b : ℝ) ≤ c2 * Real.log (Real.log (b : ℝ)) := by
  have hdense : ∀ᶠ S : ℝ in atTop, ∀ C : ℕ,
      Real.exp (4 * (DM + 2) * S) ≤ (C : ℝ) →
      (C : ℝ) ≤ Real.exp (2 * (4 * (DM + 2)) * S) →
      DenseEgyptianFamily DM L S C := by
    filter_upwards [hsupply,
      eventually_dense_family_of_raw_supply DM L c K r hDM hc hK hr hKr] with S hraw hS
    intro C hClow hCup
    exact hS C hClow (hraw C hClow hCup)
  obtain ⟨S0, hS0⟩ := eventually_atTop.mp hdense
  exact main_upper_of_dense_family DM L S0 hDM hL hS0

end Problem337


end

end OAI
end

theorem solution : type_of% @OAI.Problem337.main_upper_of_raw_density_supply_oai := @OAI.Problem337.main_upper_of_raw_density_supply_oai
