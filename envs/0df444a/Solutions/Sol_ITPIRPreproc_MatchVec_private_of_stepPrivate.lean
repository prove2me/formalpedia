-- Prove2me | solution 1 for ITPIRPreproc.MatchVec.private_of_stepPrivate
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:01:42.678238+00:00
-- url     : https://prove2.me/submissions/d4135317-93e3-4ed0-baec-e50bde769dae

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_CompilerInvariants

open MeasureTheory
open scoped ENNReal

namespace ITPIRPreproc.MatchVec

open WordRAM

private lemma map_tape_zero : Measure.map (fun ω : Tapes => tape ω 0) tapeLaw = coinTape := by
  have hf : Measurable (fun ω : Tapes => tape ω 0) := by
    unfold tape
    exact measurable_pi_lambda _ (fun k => measurable_pi_apply (0, k))
  unfold coinTape
  apply Measure.eq_infinitePi
  intro s t ht
  let emb : ℕ ↪ ℕ × ℕ :=
    { toFun := fun k => (0, k)
      inj' := by intro a b h; simpa using congrArg Prod.snd h }
  let s' : Finset (ℕ × ℕ) := s.map emb
  let t' : ℕ × ℕ → Set Bool := fun p =>
    if p.1 = 0 ∧ p.2 ∈ s then t p.2 else Set.univ
  have hpre : (fun ω : Tapes => tape ω 0) ⁻¹' ((s : Set ℕ).pi t) =
      ((s' : Set (ℕ × ℕ)).pi t') := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Finset.mem_coe]
    constructor
    · intro h p hp
      change p ∈ s' at hp
      obtain ⟨k, hk, rfl⟩ := Finset.mem_map.mp hp
      change ω (0, k) ∈ t' (0, k)
      simpa [t', tape, hk] using h k hk
    · intro h k hk
      have hx := h (0, k) (Finset.mem_map.mpr ⟨k, hk, rfl⟩)
      simpa [t', hk, tape] using hx
  rw [Measure.map_apply hf (MeasurableSet.pi s.countable_toSet (fun i _ => ht i)), hpre]
  have ht' : ∀ p ∈ s', MeasurableSet (t' p) := by
    intro p hp
    by_cases h : p.1 = 0 ∧ p.2 ∈ s
    · simpa [t', h] using ht p.2
    · simp [t', h]
  have hval := Measure.infinitePi_pi
    (μ := fun _ : ℕ × ℕ => (PMF.uniformOfFintype Bool).toMeasure) (s := s') (t := t') ht'
  change (Measure.infinitePi fun _ : ℕ × ℕ => (PMF.uniformOfFintype Bool).toMeasure)
    (((s' : Finset (ℕ × ℕ)) : Set (ℕ × ℕ)).pi t') = _
  rw [hval, Finset.prod_map]
  apply Finset.prod_congr rfl
  intro k hk
  change (PMF.uniformOfFintype Bool).toMeasure (t' (0, k)) =
    (PMF.uniformOfFintype Bool).toMeasure (t k)
  congr 1
  simp [t', hk]

private lemma tapeLaw_tape_zero (B : Set (ℕ → Bool)) (hB : MeasurableSet B) :
    tapeLaw {ω | tape ω 0 ∈ B} = coinTape B := by
  have hf : Measurable (fun ω : Tapes => tape ω 0) := by
    unfold tape
    exact measurable_pi_lambda _ (fun k => measurable_pi_apply (0, k))
  rw [← map_tape_zero, Measure.map_apply hf hB]
  rfl

private lemma coinTape_univ : coinTape (Set.univ : Set (ℕ → Bool)) = 1 := by
  unfold coinTape
  exact measure_univ

private noncomputable def simFromStep (step : ℕ → List (List Bool) → List Bool → ℝ≥0∞) :
    ℕ → List (List Bool) → ℝ≥0∞
  | 0, qs => if qs = [] then 1 else 0
  | T + 1, qs => match qs.reverse with
    | [] => 0
    | q :: rev => simFromStep step T rev.reverse * step T rev.reverse q

end ITPIRPreproc.MatchVec

open ITPIRPreproc.MatchVec

/-- One-step adversary-independent query factorization implies perfect privacy for the whole
adaptive experiment. -/
theorem solution (S : Scheme) (n lam : ℕ) (h : StepPrivate S n lam) :
    PerfectlyPrivate S n lam := by
  intro D
  obtain ⟨step, hstep⟩ := h D
  refine ⟨ITPIRPreproc.MatchVec.simFromStep step, ?_⟩
  intro A hA T
  induction T with
  | zero =>
      intro B hB qs
      by_cases hqs : qs = []
      · subst qs
        simp only [history, List.map_nil, ITPIRPreproc.MatchVec.simFromStep, ↓reduceIte, mul_one,
          and_true]
        exact ITPIRPreproc.MatchVec.tapeLaw_tape_zero B hB
      · simp only [history, List.map_nil, ITPIRPreproc.MatchVec.simFromStep, hqs, ↓reduceIte,
          mul_zero]
        rw [show {ω | tape ω 0 ∈ B ∧ [] = qs} = ∅ by ext; simp [hqs]]
        simp
  | succ T ih =>
      intro B hB qs
      cases hr : qs.reverse with
      | nil =>
          have hqs : qs = [] := by simpa using congrArg List.reverse hr
          subst qs
          simp only [ITPIRPreproc.MatchVec.simFromStep, List.reverse_nil, mul_zero]
          rw [show {ω | tape ω 0 ∈ B ∧ (history S n lam D A ω (T + 1)).map Round.query = []} =
              ∅ by ext ω; simp [history_succ_roundAt]]
          simp
      | cons q rev =>
          have hqs : qs = rev.reverse ++ [q] := by
            simpa using congrArg List.reverse hr
          rw [hqs]
          have hevent :
              {ω | tape ω 0 ∈ B ∧
                  (history S n lam D A ω (T + 1)).map Round.query = rev.reverse ++ [q]} =
                {ω | tape ω 0 ∈ B ∧
                  (history S n lam D A ω T).map Round.query = rev.reverse ∧
                  (roundAt S n lam D A ω T).query = q} := by
            ext ω
            simp only [history_succ_roundAt, List.map_append, List.map_cons, List.map_nil,
              ← List.concat_eq_append, List.map_concat, List.concat_inj]
          rw [hevent, hstep A hA T B hB rev.reverse q]
          have hpref : tapeLaw {ω | (history S n lam D A ω T).map Round.query = rev.reverse} =
              ITPIRPreproc.MatchVec.simFromStep step T rev.reverse := by
            have hu := ih Set.univ MeasurableSet.univ rev.reverse
            simpa only [Set.mem_univ, true_and, ITPIRPreproc.MatchVec.coinTape_univ, one_mul] using hu
          rw [hpref]
          simp only [ITPIRPreproc.MatchVec.simFromStep, List.reverse_append, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.reverse_reverse, mul_assoc, List.singleton_append]
