-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.weakCompositionFiber_card_decomp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:25:40.773774+00:00
-- url     : https://prove2.me/submissions/09da356d-d284-4100-970c-d10fd56321e3

import Mathlib
import Mathlib.Tactic
import Definitions.Def_weakCompositionFiber

open scoped BigOperators
open OAI.PiExponent.LiteralAnalytic in
theorem solution
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (e : σ → ℕ) (k : ℕ) :
    Fintype.card
        (OAI.PiExponent.LiteralAnalytic.weakCompositionFiber (Σ i, Fin (e i)) k) =
      ∑ n : σ → Fin (k + 1),
        (if ∑ i, (n i).val = k then
          ∏ i,
            Fintype.card
              {g : Fin (e i) → Fin ((n i).val + 1) //
                Finset.univ.sum (fun j => (g j).val) = (n i).val}
         else 0) := by
  classical
  let W := weakCompositionFiber (Σ i, Fin (e i)) k
  have hsum : ∀ f : W, ∑ i, ∑ j : Fin (e i), ((f.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ) = k := by
    intro f
    have := f.2
    rw [Fintype.sum_sigma] at this
    exact this
  have hle : ∀ (f : W) (i : σ), ∑ j : Fin (e i), ((f.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ) ≤ k := by
    intro f i
    exact (Finset.single_le_sum (f := fun i => ∑ j : Fin (e i), ((f.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)).trans_eq (hsum f)
  let N : W → (σ → Fin (k + 1)) := fun f i =>
    ⟨∑ j : Fin (e i), ((f.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ), Nat.lt_succ_of_le (hle f i)⟩
  rw [Fintype.card_congr (Equiv.sigmaFiberEquiv N).symm, Fintype.card_sigma]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  split_ifs with hn
  · rw [← Fintype.card_pi]
    refine Fintype.card_congr ?_
    exact {
      toFun := fun f i => ⟨fun j => ⟨(f.1.1 ⟨i, j⟩ : ℕ), by
          have h1 : ∑ j : Fin (e i), ((f.1.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ) = n i := by
            have := congrArg (fun g => ((g i : Fin (k + 1)) : ℕ)) f.2
            simpa [N] using this
          have h2 := Finset.single_le_sum (f := fun j => ((f.1.1 ⟨i, j⟩ : Fin (k + 1)) : ℕ))
            (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
          omega⟩, by
          have := congrArg (fun g => ((g i : Fin (k + 1)) : ℕ)) f.2
          simpa [N] using this⟩
      invFun := fun G => ⟨⟨fun x => ⟨((G x.1).1 x.2 : ℕ), by
          have := ((G x.1).1 x.2).isLt
          have := (n x.1).isLt
          omega⟩, by
          rw [Fintype.sum_sigma]
          exact (Finset.sum_congr rfl (fun i _ => (G i).2)).trans hn⟩, by
          funext i
          apply Fin.ext
          simp only [N]
          exact (G i).2⟩
      left_inv := fun f => by
        apply Subtype.ext; apply Subtype.ext; funext x; rfl
      right_inv := fun G => by
        funext i; apply Subtype.ext; funext j; rfl }
  · rw [Fintype.card_eq_zero_iff]
    refine ⟨fun f => hn ?_⟩
    have := f.2
    rw [← this]
    simp only [N]
    exact hsum f.1
