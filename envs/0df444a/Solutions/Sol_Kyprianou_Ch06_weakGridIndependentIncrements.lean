-- Prove2me | solution 1 for Kyprianou.Ch06.weakGridIndependentIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:43:20.912214+00:00
-- url     : https://prove2.me/submissions/b30b2bb1-33ab-4a8e-b9cd-ddff89343cd8

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Definitions.Def_Kyprianou_Ch06_FinCompressionIndexHelpers
import Theorems.Thm_Kyprianou_Ch06_iIndepFun_finInsertZero
import Theorems.Thm_Kyprianou_Ch06_strictGridIndependentIncrements

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The Chapter 6 strict-grid independent-increment cylinder hypothesis
already implies independence on non-strict monotone finite grids. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hprob : P Set.univ = 1)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i}) :
    ProbabilityTheory.HasIndependentIncrements X P := by
  intro m
  induction m with
  | zero =>
      intro t ht
      have hs : StrictMono t := by
        intro a b hab
        have heq : a = b := by
          apply Fin.ext
          omega
        exact False.elim (lt_irrefl a (heq ▸ hab))
      exact Kyprianou.Ch06.strictGridIndependentIncrements
        P X hprob hindep 0 t hs
  | succ n ih =>
      intro t ht
      by_cases hs : StrictMono t
      · exact Kyprianou.Ch06.strictGridIndependentIncrements
          P X hprob hindep (n + 1) t hs
      · have heq : ∃ k : Fin (n + 1), t k.castSucc = t k.succ := by
          by_contra hn
          push_neg at hn
          apply hs
          apply Fin.strictMono_iff_lt_succ.mpr
          intro i
          have hle : t i.castSucc ≤ t i.succ :=
            ht (Fin.castSucc_le_succ i)
          exact lt_of_le_of_ne hle (hn i)
        obtain ⟨k, hdup⟩ := heq
        let τ : Fin (n + 1) → NNReal :=
          fun i => t (k.succ.succAbove i)
        have hτmono : Monotone τ := by
          intro a b hab
          exact ht ((Fin.succAboveOrderEmb k.succ).monotone hab)
        let f : Fin (n + 1) → Ω → Real :=
          fun i ω => X (t i.succ) ω - X (t i.castSucc) ω
        let g : Fin n → Ω → Real :=
          fun i ω => X (τ i.succ) ω - X (τ i.castSucc) ω
        have hz : f k = fun _ => 0 := by
          funext ω
          simp [f, hdup]
        have hr : ∀ j : Fin n, f (k.succAbove j) = g j := by
          intro j
          have hright : t ((k.succAbove j).succ) =
              t (k.succ.succAbove j.succ) :=
            congrArg t (Kyprianou.Ch06.compressedGrid_endIndex n k j)
          have hleft : t ((k.succAbove j).castSucc) =
              t (k.succ.succAbove j.castSucc) := by
            by_cases hjk : j.val = k.val
            · obtain ⟨h1,h2⟩ :=
                Kyprianou.Ch06.compressedGrid_startIndex_eq n k j hjk
              rw [h1,h2]
              exact hdup.symm
            · exact congrArg t
                (Kyprianou.Ch06.compressedGrid_startIndex_ne n k j hjk)
          funext ω
          change X (t ((k.succAbove j).succ)) ω -
              X (t ((k.succAbove j).castSucc)) ω =
            X (t (k.succ.succAbove j.succ)) ω -
              X (t (k.succ.succAbove j.castSucc)) ω
          rw [hright, hleft]
        exact Kyprianou.Ch06.iIndepFun_finInsertZero
          P hprob n f g k hz hr (ih τ hτmono)
