-- Prove2me | solution 1 for HarelTarjan.SymOrder.nca_algorithm_correct
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-03T09:10:02.381877+00:00
-- url     : https://prove2.me/submissions/d5125d71-d828-4047-8cf2-05aed50970b5

import Mathlib
import Definitions.Def_HarelTarjan_SymOrder_Tree
import Definitions.Def_HarelTarjan_SymOrder_Sym
import Definitions.Def_HarelTarjan_SymOrder_Algorithms
import Theorems.Thm_HarelTarjan_SymOrder_ncaDepthAlg_correct
import Theorems.Thm_HarelTarjan_SymOrder_depthAlg_correct

open HarelTarjan.SymOrder

private theorem lcp_prefix_left : ∀ s t : List Bool, lcp s t <+: s
  | [], _ => by simp [lcp]
  | _ :: _, [] => by simp [lcp]
  | a :: s, b :: t => by
    by_cases h : a = b
    · subst b
      simpa [lcp] using lcp_prefix_left s t
    · simp [lcp, h]

theorem solution {d : ℕ} (v w : Vertex d) :
    ∀ u : Vertex d, sym u = depthAlgNum v (ncaDepthAlg v w) ↔ u = nca v w := by
  rw [ncaDepthAlg_correct]
  have hle : depth (nca v w) ≤ depth v := lcp_length_le_left v.1 w.1
  have heq : ancestorAtDepth v (depth (nca v w)) = nca v w := by
    apply Subtype.ext
    exact (List.prefix_iff_eq_take.mp (lcp_prefix_left v.1 w.1)).symm
  intro u
  rw [(depthAlg_correct v (depth (nca v w)) hle).2.2 u, heq]
