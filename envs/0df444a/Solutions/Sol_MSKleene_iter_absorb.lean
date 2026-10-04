-- Prove2me | solution 1 for MSKleene.iter_absorb
-- status  : ACCEPTED   (prove)
-- author  : @Cosme
-- created : 2026-09-08T16:18:34.418176+00:00
-- url     : https://prove2.me/submissions/eab3d9d3-c444-4d50-9d3b-550538f752d0

import Definitions.Def_MSKleene_Iteration
import Theorems.Thm_MSKleene_subst_family
import Mathlib.Data.List.MinMax

open MSKleene
open Classical

private theorem iterStage_mono {S : Type} {sig : Signature S} {X : SSet S}
    {s : S} (z : X s) (L : Set (Term sig X s)) :
    Monotone (iterStage z L) :=
  monotone_nat_of_le_succ (fun i R hR => by
    rw [iterStage_succ]
    exact Or.inl hR)

theorem solution {S : Type} (sig : Signature S) (X : SSet S) {s : S}
    (z : X s) (L : Set (Term sig X s)) :
    substP z (iterate z L) s L ⊆ iterate z L := by
  intro R hR
  unfold substP at hR
  rcases Set.mem_iUnion.mp hR with ⟨P, hP⟩
  rcases Set.mem_iUnion.mp hP with ⟨hPL, hPR⟩
  rw [(subst_family sig X z (iterate z L) P).1] at hPR
  rcases hPR with ⟨qs, hqs, hEq⟩
  have hstage : ∀ α, ∃ i : ℕ, qs α ∈ iterStage z L i := by
    intro α
    simpa only [iterate, Set.mem_iUnion] using hqs α
  choose f hf using hstage
  let n : ℕ := (List.ofFn f).foldr max 0
  have hfn : ∀ α, f α ≤ n := by
    intro α
    exact List.le_max_of_le (List.mem_ofFn.mpr ⟨α, rfl⟩) (Nat.le_refl _)
  have hqsn : ∀ α, qs α ∈ iterStage z L n := by
    intro α
    exact iterStage_mono z L (hfn α) (hf α)
  have hsub : R ∈ (show Set (Term sig X s) from
      (substHom z (iterStage z L n)).toFun s P) := by
    rw [(subst_family sig X z (iterStage z L n) P).1]
    exact ⟨qs, hqsn, hEq⟩
  have hnext : R ∈ iterStage z L (n + 1) := by
    rw [iterStage_succ]
    right
    unfold substP
    apply Set.mem_iUnion.mpr
    refine ⟨P, ?_⟩
    apply Set.mem_iUnion.mpr
    exact ⟨hPL, hsub⟩
  unfold iterate
  exact Set.mem_iUnion.mpr ⟨n + 1, hnext⟩
