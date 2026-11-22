-- Prove2me | solution 1 for MixedManna.claim_1
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T23:15:44.675436+00:00
-- url     : https://prove2.me/submissions/6285da22-63ed-401b-b0fe-43f5e34f42bb

import Mathlib
import Definitions.Def_MixedManna_StandingAssumptions
import Definitions.Def_MixedManna_IsAdmissibleDelta
import Definitions.Def_MixedManna_lcpSolutions

set_option autoImplicit false

open Classical MixedManna

theorem solution {N M : Type*} [Fintype N] [Fintype M] (I : Instance N M)
    (hI : StandingAssumptions I) (P R : ℝ) (hP : 0 < P) (δ : M → ℝ)
    (hδ : IsAdmissibleDelta I δ) (ε : ℝ) (hε : 0 < ε) (x : LCPVar I)
    (hx : x ∈ lcpSolutions I P R δ ε) (hp : ∀ j, pv x j < P) (σ : Seg I) (hσ : IsLastSeg σ) :
    (¬ IsGood I (segItem σ) → sv x σ = 0) ∧
      (IsGood I (segItem σ) → 0 < pv x (segItem σ) → sv x σ = 0) := by
  simp only [lcpSolutions, lcpPolyhedron, Set.mem_ofPred_eq] at hx
  obtain ⟨⟨hp0, hf0, hr0, hs0, hz0, hagent, hprice, hspend, hseg⟩, -, hpc, -, hsc⟩ := hx
  have hsum : fv x σ ≤ ∑ σ' : Seg I, if segItem σ' = segItem σ then fv x σ' else 0 := by
    have := Finset.single_le_sum
      (f := fun σ' : Seg I => if segItem σ' = segItem σ then fv x σ' else 0)
      (fun σ' _ => by
        split_ifs
        · exact hf0 σ'
        · exact le_rfl) (Finset.mem_univ σ)
    simpa using this
  have hlen : lcpLength I ε σ = 1 + ε := by simp [lcpLength, hσ]
  have key : fv x σ ≤ P - pv x (segItem σ) → sv x σ = 0 := by
    intro hfle
    have hpos : 0 < segSlack I P ε x σ := by
      simp only [segSlack, hlen]
      have := mul_pos hε (sub_pos.2 (hp (segItem σ)))
      nlinarith
    rcases mul_eq_zero.mp (hsc σ) with h | h
    · exact h
    · exact absurd h hpos.ne'
  constructor
  · intro hbad
    apply key
    have := hprice (segItem σ)
    simp only [priceSlack, if_neg hbad] at this
    linarith
  · intro hgood hpj
    apply key
    have hps : priceSlack I P δ x (segItem σ) = 0 :=
      (mul_eq_zero.mp (hpc (segItem σ))).resolve_left hpj.ne'
    simp only [priceSlack, if_pos hgood] at hps
    have hδj := (hδ (segItem σ) hgood).1
    have : 0 ≤ δ (segItem σ) * zv x := mul_nonneg (by linarith) hz0
    linarith
