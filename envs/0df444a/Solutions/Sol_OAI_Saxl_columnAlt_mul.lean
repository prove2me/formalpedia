-- Prove2me | solution 1 for OAI.Saxl.columnAlt_mul
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:03:33.448267+00:00
-- url     : https://prove2.me/submissions/820909b7-2ea8-4460-b172-1d6871ba39da

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX


theorem solution {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  letI := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul, smul_mul_assoc]
  congr 1
  rw [mul_comm (signC (g : Equiv.Perm (Fin n))), ← mul_assoc, signC_mul_self, one_mul]

