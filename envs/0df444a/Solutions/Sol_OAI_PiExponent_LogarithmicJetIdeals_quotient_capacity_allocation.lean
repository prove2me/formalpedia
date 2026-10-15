-- Prove2me | solution 1 for OAI.PiExponent.LogarithmicJetIdeals.quotient_capacity_allocation
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-14T22:00:59.747599+00:00
-- url     : https://prove2.me/submissions/2ec28925-b241-4420-9183-5be646969917

import Definitions.Def_OAI_PiExponent_AdmissibleFormalInterpolation
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals
import Definitions.Def_OAI_PiExponent_LogarithmicJetIdeals_LocalCoordinatePolynomial

open OAI.PiExponent
open OAI.PiExponent.LogarithmicJetIdeals
open scoped BigOperators

theorem solution
    {m : ℕ} (e : Fin (m + 1) → ℕ) (d : Fin (m + 1) →₀ ℕ) (n : ℕ)
    (hcapacity : n ≤ ∑ i, d i / e i) :
    ∃ k : Fin (m + 1) →₀ ℕ, k.sum (fun _ x => x) = n ∧
      ∀ i, k i * e i ≤ d i := by
  classical
  let Slot := Σ i : Fin (m + 1), Fin (d i / e i)
  let slots : Finset Slot := Finset.univ
  have hslots : n ≤ slots.card := by
    simpa [slots, Slot, Fintype.card_sigma] using hcapacity
  obtain ⟨t, hts, htcard⟩ := Finset.exists_subset_card_eq hslots
  let f : Fin (m + 1) → ℕ := fun i =>
    (t.filter fun x : Slot => x.1 = i).card
  let k : Fin (m + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm f
  have hsum : (∑ i, f i) = n := by
    dsimp [f]
    rw [← Finset.card_eq_sum_card_fiberwise
      (f := fun x : Slot => x.1) (s := t) (t := Finset.univ) (by simp)]
    exact htcard
  refine ⟨k, ?_, ?_⟩
  · dsimp [k]
    rw [Finsupp.equivFunOnFinite_symm_sum]
    exact hsum
  · intro i
    have hfilter :
        (t.filter fun x : Slot => x.1 = i) ⊆
          (slots.filter fun x : Slot => x.1 = i) :=
      Finset.filter_subset_filter _ hts
    have hfiber : Fintype.card {x : Slot // x.1 = i} = d i / e i := by
      let fiberEquiv : {x : Slot // x.1 = i} ≃ Fin (d i / e i) :=
        { toFun := fun x =>
            cast (congrArg (fun j : Fin (m + 1) => Fin (d j / e j)) x.2) x.1.2
          invFun := fun j => ⟨⟨i, j⟩, rfl⟩
          left_inv := by
            rintro ⟨⟨j, a⟩, hj⟩
            cases hj
            rfl
          right_inv := by
            intro j
            rfl }
      rw [Fintype.card_congr fiberEquiv, Fintype.card_fin]
    have hcount :
        (t.filter fun x : Slot => x.1 = i).card ≤ d i / e i := by
      calc
        (t.filter fun x : Slot => x.1 = i).card ≤
            (slots.filter fun x : Slot => x.1 = i).card :=
          Finset.card_le_card hfilter
        _ = d i / e i := by
          change (Finset.univ.filter fun x : Slot => x.1 = i).card = d i / e i
          rw [← Finset.card_subtype (fun x : Slot => x.1 = i) Finset.univ]
          simpa using hfiber
    have hmul : k i * e i ≤ (d i / e i) * e i :=
      Nat.mul_le_mul_right _ (by simpa [k, f] using hcount)
    exact le_trans hmul (Nat.div_mul_le_self (d i) (e i))