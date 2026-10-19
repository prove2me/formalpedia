-- Prove2me | solution 1 for OAI.Saxl.polytabloid_rowWord
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:03:07.66134+00:00
-- url     : https://prove2.me/submissions/a119b805-e1f2-4332-acd1-3f5bea18a91d

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic

open OAI OAI.Saxl
open scoped TensorProduct
universe uG uV uW


theorem solution {n : ℕ} {μ : YoungDiagram} (t : Tableau n μ) :
    polytabloid t (rowWord t) = 1 := by
  classical
  unfold polytabloid
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single (1 : columnGroup t)]
  · simp
  · intro g _ hg
    have key : rowWord t ∘ (g : Equiv.Perm (Fin n)) ≠ rowWord t := by
      intro h
      apply hg
      ext i : 2
      have h1 := congrFun h i
      have h2 := g.2 i
      have h3 : (t ((g : Equiv.Perm (Fin n)) i)).val = (t i).val := by
        simp only [rowWord, Function.comp_apply, Fin.mk.injEq] at h1
        exact Prod.ext h1 h2
      have := t.injective (Subtype.ext h3)
      simpa using this
    change _ * (Pi.single (rowWord t) (1:ℂ) : WordSpace n _) (rowWord t ∘ (g : Equiv.Perm (Fin n))) = 0
    rw [Pi.single_apply, if_neg key, mul_zero]
  · intro h; exact absurd (@Finset.mem_univ _ (Fintype.ofFinite _) _) h

