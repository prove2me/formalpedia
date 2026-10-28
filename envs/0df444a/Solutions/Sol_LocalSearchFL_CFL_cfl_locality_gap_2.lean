-- Prove2me | solution 2 for LocalSearchFL.CFL.cfl_locality_gap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T09:48:19.775085+00:00
-- url     : https://prove2.me/submissions/f759d743-9f38-4d2b-b342-96115fe87de2

import Mathlib
import Definitions.Def_LocalSearchFL_CFL_IsCFLLocalOpt
import Theorems.Thm_LocalSearchFL_CFL_facility_cost_lemma_5_3

-- carved verbatim out of submission b890743d-8250-48a2-a4bc-6c78568438e6, lines 451-456

section
open LocalSearchFL
open LocalSearchFL.CFL

theorem aux_add_exists {Cl Fa : Type} [Fintype Cl] [DecidableEq Cl] {u : Fa → ℕ}
    (I : MetricInstance Cl Fa) (f : Fa → ℝ) (X : CFLSol Cl Fa u)
    (a : Fa) (P : Finset Cl) (hP : P.card ≤ u a) :
    ∃ Y : CFLSol Cl Fa u, IsAddNbr X Y ∧
      cost I f Y = costF f X + f a +
        ∑ j, (if j ∈ P then I.c j a else I.c j (X.loc (X.σ j))) := by
  classical
  let loc' : Fin (X.n + 1) → Fa := Fin.snoc (α := fun _ => Fa) X.loc a
  let σ' : Cl → Fin (X.n + 1) := fun j => if j ∈ P then Fin.last _ else (X.σ j).castSucc
  have hcap' : ∀ s, (Finset.univ.filter (fun j => σ' j = s)).card ≤ u (loc' s) := by
    intro s
    induction s using Fin.lastCases with
    | last =>
      have hsub : Finset.univ.filter (fun j => σ' j = Fin.last _) ⊆ P := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ'] at hj
        by_contra h
        rw [if_neg h] at hj
        exact absurd hj (Fin.castSucc_ne_last _)
      have : loc' (Fin.last _) = a := by simp [loc']
      rw [this]
      exact (Finset.card_le_card hsub).trans hP
    | cast i =>
      have hsub : Finset.univ.filter (fun j => σ' j = i.castSucc) ⊆
          Finset.univ.filter (fun j => X.σ j = i) := by
        intro j hj
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, σ'] at hj ⊢
        by_cases h : j ∈ P
        · rw [if_pos h] at hj; exact absurd hj.symm (Fin.castSucc_ne_last _)
        · rw [if_neg h] at hj; exact Fin.castSucc_injective _ hj
      have : loc' i.castSucc = X.loc i := by simp [loc']
      rw [this]
      exact (Finset.card_le_card hsub).trans (X.cap i)
  refine ⟨{ n := X.n + 1, loc := loc', σ := σ', cap := hcap' }, ⟨a, ?_⟩, ?_⟩
  · simp only [CFLSol.facMultiset]
    rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ']
    simp only [loc', List.concat_eq_append, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Multiset.coe_add]; rfl
  · simp only [cost, costF, costS]
    rw [Fin.sum_univ_castSucc]
    have h1 : ∑ i : Fin X.n, f (loc' i.castSucc) = ∑ i, f (X.loc i) := by simp [loc']
    have h2 : loc' (Fin.last _) = a := by simp [loc']
    have h3 : ∑ j, I.c j (loc' (σ' j)) =
        ∑ j, (if j ∈ P then I.c j a else I.c j (X.loc (X.σ j))) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : j ∈ P
      · simp [σ', h, loc']
      · simp [σ', h, loc']
    rw [h1, h2, h3]

theorem service_core {Cl Fa : Type} [Fintype Cl] {u : Fa → ℕ}
    (I : MetricInstance Cl Fa) (f : Fa → ℝ)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    costS I X ≤ costF f O + costS I O := by
  classical
  have key : ∀ o : Fin O.n, 0 ≤ f (O.loc o) +
      ∑ j, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
    intro o
    obtain ⟨Y, hY, hc⟩ := aux_add_exists I f X (O.loc o) (Finset.univ.filter (fun j => O.σ j = o))
      (O.cap o)
    have hle := hX Y (Or.inl hY)
    rw [hc] at hle
    unfold cost costS at hle
    have : ∑ j, (if j ∈ Finset.univ.filter (fun j => O.σ j = o) then I.c j (O.loc o)
        else I.c j (X.loc (X.σ j))) = ∑ j, I.c j (X.loc (X.σ j)) +
        ∑ j, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j)) else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      by_cases h : O.σ j = o <;> simp [h]
    linarith
  have hs := Finset.sum_nonneg (fun o (_ : o ∈ Finset.univ) => key o)
  rw [Finset.sum_add_distrib, Finset.sum_comm] at hs
  have : ∀ j : Cl, ∑ o : Fin O.n, (if O.σ j = o then I.c j (O.loc o) - I.c j (X.loc (X.σ j))
      else 0) = I.c j (O.loc (O.σ j)) - I.c j (X.loc (X.σ j)) := by
    intro j; rw [Finset.sum_ite_eq]; simp
  simp only [this, Finset.sum_sub_distrib] at hs
  unfold costF costS
  linarith

theorem gap_core {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by
  have h1 := LocalSearchFL.CFL.facility_cost_lemma_5_3 I u hu f hf X hX O
  have h2 := service_core I f X hX O
  have h3 : 0 ≤ costS I O := Finset.sum_nonneg (fun j _ => I.nonneg _ _)
  unfold cost
  linarith

end

section
open LocalSearchFL.CFL

theorem solution {Cl Fa : Type} [Fintype Cl] [Nonempty Cl]
    (I : MetricInstance Cl Fa) (u : Fa → ℕ) (hu : ∀ i, 0 < u i) (f : Fa → ℝ) (hf : ∀ i, 0 ≤ f i)
    (X : CFLSol Cl Fa u) (hX : IsCFLLocalOpt I f X) (O : CFLSol Cl Fa u) :
    cost I f X ≤ 4 * cost I f O := by
  exact gap_core I u hu f hf X hX O

end
