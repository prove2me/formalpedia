-- Prove2me | solution 1 for LocalSearchFL.CFL.service_cost_lemma_5_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T13:17:00.352324+00:00
-- url     : https://prove2.me/submissions/77688346-bdea-46d2-a52f-da2afe96a9cd

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt

set_option autoImplicit false

namespace LocalSearchFL.CFL.F8581EF4

open LocalSearchFL.CFL

/-- The add move: add a copy of `O.loc o` to `X` and reroute the clients of copy `o` of `O`. -/
noncomputable def addSol {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}
    (X O : CFLSol Cl Fa u) (o : Fin O.n) : CFLSol Cl Fa u where
  n := X.n + 1
  loc := Fin.snoc (α := fun _ => Fa) X.loc (O.loc o)
  σ := fun j => by
    classical
    exact if O.σ j = o then Fin.last X.n else Fin.castSucc (X.σ j)
  cap := by
    classical
    intro s
    induction s using Fin.lastCases with
    | last =>
      simp only [Fin.snoc_last]
      refine le_trans (Finset.card_le_card ?_) (O.cap o)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_contra h
      rw [if_neg h] at hj
      exact (Fin.castSucc_lt_last _).ne hj
    | cast s =>
      simp only [Fin.snoc_castSucc]
      refine le_trans (Finset.card_le_card ?_) (X.cap s)
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      by_cases h : O.σ j = o
      · rw [if_pos h] at hj
        exact absurd hj.symm (Fin.castSucc_lt_last _).ne
      · rw [if_neg h] at hj
        exact Fin.castSucc_injective _ hj

lemma addSol_nbr {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}
    (X O : CFLSol Cl Fa u) (o : Fin O.n) : IsAddNbr X (addSol X O o) := by
  refine ⟨O.loc o, ?_⟩
  show Multiset.map (Fin.snoc (α := fun _ => Fa) X.loc (O.loc o))
      (Finset.univ : Finset (Fin (X.n + 1))).val = Multiset.map X.loc Finset.univ.val + {O.loc o}
  rw [Fin.univ_castSuccEmb, Finset.cons_val, Multiset.map_cons, Finset.map_val,
    Multiset.map_map]
  simp only [Function.comp_def, Fin.coe_castSuccEmb, Fin.snoc_castSucc, Fin.snoc_last]
  rw [add_comm, Multiset.singleton_add]

lemma addSol_costF {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (f : Fa → ℝ)
    (X O : CFLSol Cl Fa u) (o : Fin O.n) :
    costF f (addSol X O o) = costF f X + f (O.loc o) := by
  show ∑ s : Fin (X.n + 1), f (Fin.snoc (α := fun _ => Fa) X.loc (O.loc o) s) =
    ∑ s : Fin X.n, f (X.loc s) + f (O.loc o)
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

lemma addSol_costS {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ} (I : MetricInstance Cl Fa)
    (X O : CFLSol Cl Fa u) (o : Fin O.n) :
    costS I (addSol X O o) = costS I X +
      ∑ j : Cl, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
  classical
  simp only [costS, addSol]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  by_cases h : O.σ j = o
  · simp [h]
  · simp [h]

end LocalSearchFL.CFL.F8581EF4

open LocalSearchFL.CFL.F8581EF4 in
open LocalSearchFL.CFL in
theorem solution {Cl Fa : Type} [Fintype Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costS I X ≤ costF f O + costS I O := by
  classical
  have key : ∀ o : Fin O.n, 0 ≤ f (O.loc o) +
      ∑ j : Cl, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
    intro o
    have h := hX (addSol X O o) (Or.inl (addSol_nbr X O o))
    simp only [cost, addSol_costF, addSol_costS] at h
    linarith
  have hsum := Finset.sum_nonneg (fun o (_ : o ∈ (Finset.univ : Finset (Fin O.n))) => key o)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hsum
  have h2 : ∀ j : Cl, (∑ o : Fin O.n,
      (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0)) =
      I.c j (O.loc (O.σ j)) - I.c j (X.loc (X.σ j)) := by
    intro j
    rw [Finset.sum_ite_eq]
    simp
  simp only [h2, Finset.sum_sub_distrib] at hsum
  simp only [costS, costF]
  linarith
