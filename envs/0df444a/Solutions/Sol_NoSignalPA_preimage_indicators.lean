-- Prove2me | solution 1 for NoSignalPA.preimage_indicators
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-01T21:48:17.449213+00:00
-- url     : https://prove2.me/submissions/21de0ab4-62eb-4fef-b876-ffcecbd39060

import Mathlib
import Definitions.Def_NoSignalPA_Str
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability

theorem solution {Nr Ns : ℕ} (k : NoSignalPA.Str Ns) (S : Finset (NoSignalPA.Str Nr))
    (v : NoSignalPA.Str Nr → Bool) :
    OAI.ThorpCompatibility.uniformProbability
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ∀ a ∈ S, decide (h a = k) = v a)
      = ∏ a ∈ S, (if v a then ((2 : ℝ) ^ Ns)⁻¹ else 1 - ((2 : ℝ) ^ Ns)⁻¹) := by
  classical
  -- the admissible values at each point: a product set
  set T : NoSignalPA.Str Nr → Finset (NoSignalPA.Str Ns) := fun a =>
    if a ∈ S then (if v a then {k} else Finset.univ.erase k) else Finset.univ with hTdef
  have hmem : ∀ h : NoSignalPA.Str Nr → NoSignalPA.Str Ns,
      (∀ a ∈ S, decide (h a = k) = v a) ↔ h ∈ Fintype.piFinset T := by
    intro h
    rw [Fintype.mem_piFinset]
    constructor
    · intro H a
      by_cases ha : a ∈ S
      · have := H a ha
        cases hv : v a
        · rw [hv] at this
          simp only [hTdef, if_pos ha, hv]
          simpa using this
        · rw [hv] at this
          simp only [hTdef, if_pos ha, hv]
          simpa using this
      · simp [hTdef, ha]
    · intro H a ha
      have := H a
      cases hv : v a
      · simp only [hTdef, if_pos ha, hv] at this
        simpa using this
      · simp only [hTdef, if_pos ha, hv] at this
        simpa using this
  have key : ((Finset.univ.filter
      (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ∀ a ∈ S, decide (h a = k) = v a)).card : ℝ)
      = (Fintype.piFinset T).card := by
    rw [show (Finset.univ.filter
        (fun h : NoSignalPA.Str Nr → NoSignalPA.Str Ns => ∀ a ∈ S, decide (h a = k) = v a)) =
        Fintype.piFinset T from Finset.ext fun h => by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact hmem h]
  unfold OAI.ThorpCompatibility.uniformProbability
  have hgoal : ((Fintype.piFinset T).card : ℝ) /
      (Fintype.card (NoSignalPA.Str Nr → NoSignalPA.Str Ns) : ℝ) =
      ∏ a ∈ S, (if v a then ((2 : ℝ) ^ Ns)⁻¹ else 1 - ((2 : ℝ) ^ Ns)⁻¹) := by
    have hcardV : (Fintype.card (NoSignalPA.Str Ns) : ℝ) = (2 : ℝ) ^ Ns := by
      simp [NoSignalPA.Str, Fintype.card_bool, Fintype.card_fin]
    have hcard : ((Fintype.card (NoSignalPA.Str Nr → NoSignalPA.Str Ns) : ℕ) : ℝ) =
        ∏ _a : NoSignalPA.Str Nr, (2 : ℝ) ^ Ns := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, hcardV]
    rw [Fintype.card_piFinset, hcard, Nat.cast_prod, ← Finset.prod_div_distrib]
    have h2 : (2 : ℝ) ^ Ns ≠ 0 := by positivity
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ Ns := one_le_pow₀ (by norm_num)
    rw [← Finset.prod_subset (Finset.subset_univ S)]
    · refine Finset.prod_congr rfl fun a ha => ?_
      simp only [hTdef, if_pos ha]
      cases v a
      · simp only [Bool.false_eq_true, if_false]
        rw [Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ,
          Nat.cast_sub (Fintype.card_pos), hcardV]
        field_simp
        norm_num
      · simp
    · intro a _ ha
      simp only [hTdef, if_neg ha, Finset.card_univ]
      rw [hcardV, div_self h2]
  rw [← hgoal, ← key]
  congr
