-- Prove2me | solution 1 for InventoryControl.serial_relaxed_min_exists
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-27T16:42:56.550529+00:00
-- url     : https://prove2.me/submissions/e0922b52-485b-44ac-8a76-86a0f5614759

import Mathlib
import Definitions.Def_InventoryControl_serial

open InventoryControl in
theorem solution {N : ℕ} (A e : Fin N → ℝ) (d : ℝ) (hd : 0 < d)
    (hA : ∀ i, 0 < A i) (he : ∀ i, 0 < e i) :
    ∃ Qrel : Fin N → ℝ, (∀ i, 0 < Qrel i) ∧ SerialNested Qrel ∧
      ∀ Q : Fin N → ℝ, (∀ i, 0 < Q i) → SerialNested Q →
        serialCost A e d Qrel ≤ serialCost A e d Q := by
  have hterm_pos : ∀ (Q : Fin N → ℝ), (∀ i, 0 < Q i) → ∀ i,
      0 < eoqCost (A i) d (e i) (Q i) := by
    intro Q hQ i
    unfold eoqCost
    have := hQ i
    have := hA i
    have := he i
    positivity
  have hterm_le : ∀ (Q : Fin N → ℝ), (∀ i, 0 < Q i) → ∀ i,
      eoqCost (A i) d (e i) (Q i) ≤ serialCost A e d Q := by
    intro Q hQ i
    unfold serialCost
    exact Finset.single_le_sum (f := fun j => eoqCost (A j) d (e j) (Q j))
      (fun j _ => (hterm_pos Q hQ j).le) (Finset.mem_univ i)
  let Q0 : Fin N → ℝ := fun _ => 1
  have hQ0pos : ∀ i, 0 < Q0 i := fun _ => one_pos
  let C0 : ℝ := serialCost A e d Q0
  let a : Fin N → ℝ := fun i => d * A i / C0
  let b : Fin N → ℝ := fun i => 2 * C0 / e i
  have hC0pos : ∀ _i : Fin N, 0 < C0 := fun i =>
    lt_of_lt_of_le (hterm_pos Q0 hQ0pos i) (hterm_le Q0 hQ0pos i)
  have hapos : ∀ i, 0 < a i := fun i => by
    have := hC0pos i
    have := hA i
    show 0 < d * A i / C0
    positivity
  let S : Set (Fin N → ℝ) :=
    (Set.univ.pi fun i => Set.Icc (a i) (b i)) ∩ {Q | SerialNested Q}
  have hScpt : IsCompact S := by
    apply IsCompact.inter_right (isCompact_univ_pi fun i => isCompact_Icc)
    have hset : {Q : Fin N → ℝ | SerialNested Q} =
        ⋂ i : Fin N, ⋂ j : Fin N, ⋂ (_ : j.val = i.val + 1), {Q | Q i ≤ Q j} := by
      ext Q
      simp [SerialNested]
    rw [hset]
    exact isClosed_iInter fun i => isClosed_iInter fun j => isClosed_iInter fun _ =>
      isClosed_le (continuous_apply i) (continuous_apply j)
  have hQ0S : Q0 ∈ S := by
    refine ⟨?_, ?_⟩
    · intro i _
      have h1 : eoqCost (A i) d (e i) (Q0 i) ≤ C0 := hterm_le Q0 hQ0pos i
      have hc := hC0pos i
      have hAi := hA i
      have hei := he i
      have hdA : 0 < d * A i := mul_pos hd hAi
      have h1' : 1 / 2 * e i + d * A i ≤ C0 := by
        have : eoqCost (A i) d (e i) (Q0 i) = 1 / 2 * e i + d * A i := by
          show (1 : ℝ) / 2 * e i + d / 1 * A i = 1 / 2 * e i + d * A i
          ring
        linarith
      constructor
      · show d * A i / C0 ≤ 1
        rw [div_le_iff₀ hc]
        linarith
      · show 1 ≤ 2 * C0 / e i
        rw [le_div_iff₀ hei]
        linarith
    · intro i j _
      exact le_refl (1 : ℝ)
  have hcont : ContinuousOn (serialCost A e d) S := by
    have hfun : serialCost A e d =
        fun Q : Fin N → ℝ => ∑ i, (Q i / 2 * e i + d / Q i * A i) := by
      funext Q
      rfl
    rw [hfun]
    apply continuousOn_finsetSum
    intro i _
    apply ContinuousOn.add
    · exact (((continuous_apply i).div_const 2).mul continuous_const).continuousOn
    · apply ContinuousOn.mul _ continuousOn_const
      apply ContinuousOn.div continuousOn_const (continuous_apply i).continuousOn
      intro Q hQ
      exact (lt_of_lt_of_le (hapos i) (hQ.1 i (Set.mem_univ i)).1).ne'
  obtain ⟨Qrel, hQrelS, hmin⟩ := hScpt.exists_isMinOn ⟨Q0, hQ0S⟩ hcont
  have hQrelpos : ∀ i, 0 < Qrel i := fun i =>
    lt_of_lt_of_le (hapos i) (hQrelS.1 i (Set.mem_univ i)).1
  refine ⟨Qrel, hQrelpos, hQrelS.2, ?_⟩
  intro Q hQ hnest
  have hle0 : serialCost A e d Qrel ≤ C0 := hmin hQ0S
  by_cases hQS : Q ∈ S
  · exact hmin hQS
  · have hex : ∃ i, ¬ (a i ≤ Q i ∧ Q i ≤ b i) := by
      by_contra hcon
      exact hQS ⟨fun i _ => not_not.mp (fun h => hcon ⟨i, h⟩), hnest⟩
    obtain ⟨i, hi⟩ := hex
    have hc := hC0pos i
    have h1 := hterm_le Q hQ i
    have hQi := hQ i
    have hAi := hA i
    have hei := he i
    refine le_trans hle0 (le_trans ?_ h1)
    show C0 ≤ Q i / 2 * e i + d / Q i * A i
    by_cases hlo : a i ≤ Q i
    · have hhi : b i < Q i := by
        by_contra h
        exact hi ⟨hlo, not_lt.mp h⟩
      have hhi' : 2 * C0 < Q i * e i := by
        have : 2 * C0 / e i < Q i := hhi
        rwa [div_lt_iff₀ hei] at this
      have : 0 ≤ d / Q i * A i := by positivity
      nlinarith
    · have hlo' : Q i * C0 < d * A i := by
        have : Q i < d * A i / C0 := not_le.mp hlo
        rwa [lt_div_iff₀ hc] at this
      have h2 : C0 ≤ d / Q i * A i := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hQi]
        nlinarith
      have : 0 ≤ Q i / 2 * e i := by positivity
      linarith
