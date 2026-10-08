-- Prove2me | solution 1 for MondererShapley.Participation.eq_6_2
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T00:23:34.540735+00:00
-- url     : https://prove2.me/submissions/70a2a5b3-2c07-4f92-9b5d-8ca4394871aa

import Mathlib
import Definitions.Def_MondererShapley_ClosedPath_IsPotentialGame
import Definitions.Def_MondererShapley_Participation_participationPayoff
import Definitions.Def_MondererShapley_Participation_profileOf
open MondererShapley.Participation
private theorem joiners_profile {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Finset ι) :
    joiners (profileOf S) = S := by
  ext i
  simp [joiners, profileOf]

private theorem profile_joiners {ι : Type*} [Fintype ι] [DecidableEq ι] (y : ι → Bool) :
    profileOf (joiners y) = y := by
  funext i
  cases h : y i <;> simp [profileOf, joiners, h]

private theorem update_profile_false {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) :
    Function.update (profileOf S) i false = profileOf (S.erase i) := by
  funext j
  by_cases h : j = i <;> simp [profileOf, Function.update, h]

private theorem update_profile_true {ι : Type*} [DecidableEq ι] (S : Finset ι) (i : ι) :
    Function.update (profileOf S) i true = profileOf (insert i S) := by
  funext j
  by_cases h : j = i <;> simp [profileOf, Function.update, h]


/-- (6.2): the participation game is a potential game iff there is `Q : Y → ℝ` with
`Q(ε_S) − Q(ε_{S∖{i}}) = ψ(v_{S∪{i}})(i) − cⁱ` for every `S ⊆ N` and every `i ∈ S`. -/
theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (ψ : Solution ι) (c : ι → ℝ)
    (v : Finset ι → ℝ) :
    MondererShapley.ClosedPath.IsPotentialGame (Y := fun _ : ι => Bool) (participationPayoff ψ c v) ↔
      ∃ Q : (ι → Bool) → ℝ, ∀ S : Finset ι, ∀ i ∈ S,
        Q (profileOf S) - Q (profileOf (S \ {i})) = ψ (S ∪ {i}) v i - c i := by
  constructor
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro S i hi
    have h := hQ i (profileOf S) true false
    have htr : Function.update (profileOf S) i true = profileOf S := by
      rw [update_profile_true, Finset.insert_eq_of_mem hi]
    rw [htr, update_profile_false] at h
    simpa [participationPayoff, profileOf, hi, joiners_profile,
      Finset.sdiff_singleton_eq_erase, Finset.union_singleton, Finset.insert_eq_of_mem hi] using h.symm
  · rintro ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    intro i y a b
    let S := insert i (joiners y)
    have hi : i ∈ S := Finset.mem_insert_self _ _
    have ht : Function.update y i true = profileOf S := by
      rw [← profile_joiners y, update_profile_true]
    have hf : Function.update y i false = profileOf (S.erase i) := by
      rw [← profile_joiners y, update_profile_false]
      simp [S]
    have he := hQ S i hi
    have hp : participationPayoff ψ c v i (Function.update y i true) -
        participationPayoff ψ c v i (Function.update y i false) =
        Q (Function.update y i true) - Q (Function.update y i false) := by
      rw [ht, hf]
      simpa [participationPayoff, profileOf, hi, joiners_profile,
        Finset.sdiff_singleton_eq_erase, Finset.union_singleton,
        Finset.insert_eq_of_mem hi] using he.symm
    cases a <;> cases b
    · simp
    · linarith
    · exact hp
    · simp

#print axioms solution
