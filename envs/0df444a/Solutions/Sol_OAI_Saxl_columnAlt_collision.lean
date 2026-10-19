-- Prove2me | solution 1 for OAI.Saxl.columnAlt_collision
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T00:04:01.149922+00:00
-- url     : https://prove2.me/submissions/668c3747-7cfd-462b-9035-8ab512d5d65f

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid

open OAI OAI.Saxl
open scoped TensorProduct
universe uX
theorem h42_columnAlt_mul {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (h : columnGroup t) :
    columnAlt (d := d) t * wordRep n d (h : Equiv.Perm (Fin n)) =
      signC (h : Equiv.Perm (Fin n)) • columnAlt t := by
  classical
  let _ := Fintype.ofFinite (columnGroup t)
  unfold columnAlt
  rw [Finset.sum_mul, Finset.smul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
  simp only [Equiv.coe_mulRight, Subgroup.coe_mul, map_mul, smul_smul, smul_mul_assoc]
  congr 1
  rw [mul_comm (signC (g : Equiv.Perm (Fin n))), ← mul_assoc, signC_mul_self, one_mul]

theorem solution {n d : ℕ} {μ : YoungDiagram} (t : Tableau n μ)
    (a : Fin n → Fin d) (i j : Fin n) (hij : i ≠ j)
    (hc : (t i).val.2 = (t j).val.2) (ha : a i = a j) :
    columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
  classical
  have hτ : Equiv.swap i j ∈ columnGroup t := by
    intro k
    rcases eq_or_ne k i with rfl | hki
    · simp [hc]
    rcases eq_or_ne k j with rfl | hkj
    · simp [hc]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hfix : wordRep n d (Equiv.swap i j) (Pi.single a (1 : ℂ)) = Pi.single a 1 := by
    rw [wordRep_single]
    congr 1
    funext k
    simp only [Function.comp_apply, Equiv.swap_inv]
    rcases eq_or_ne k i with rfl | hki
    · simp [ha]
    rcases eq_or_ne k j with rfl | hkj
    · simp [ha]
    rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
  have hm := congrArg (fun f => f (Pi.single a (1 : ℂ))) (h42_columnAlt_mul (d := d) t ⟨_, hτ⟩)
  simp only [Module.End.mul_apply, LinearMap.smul_apply, hfix, signC_def,
    Equiv.Perm.sign_swap hij] at hm
  have : (2 : ℂ) • columnAlt t (Pi.single a (1 : ℂ)) = 0 := by
    rw [two_smul]; nth_rewrite 1 [hm]; simp
  exact (smul_eq_zero.1 this).resolve_left two_ne_zero

