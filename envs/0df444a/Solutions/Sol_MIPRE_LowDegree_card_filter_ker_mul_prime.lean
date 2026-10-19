-- Prove2me | solution 1 for MIPRE.LowDegree.card_filter_ker_mul_prime
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:29.973854+00:00
-- url     : https://prove2.me/submissions/e1fe840b-dc6d-4db2-839f-893b3f67d693

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/Anticomm.lean (solution of MIPRE.LowDegree.card_filter_ker_mul_prime);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.RingTheory.Trace.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset MvPolynomial
variable {F V : Type*} [Field F] [Fintype F] [DecidableEq F] [AddCommGroup V] [Module F V]
  [Fintype V] [DecidableEq V]
omit [DecidableEq V] in
theorem _root_.solution (τ : V →ₗ[F] F) (hτ : τ ≠ 0) :
    #{r ∈ (univ : Finset V) | τ r = 0} * Fintype.card F = Fintype.card V := by
  classical
  obtain ⟨v, hv⟩ : ∃ v : V, τ v ≠ 0 := by
    by_contra h
    exact hτ (LinearMap.ext fun r => not_ne_iff.mp (fun hr => h ⟨r, hr⟩))
  -- every fibre has the same cardinality as the kernel
  have hfib : ∀ a : F, #{r ∈ (univ : Finset V) | τ r = a} = #{r ∈ (univ : Finset V) | τ r = 0} := by
    intro a
    refine Finset.card_bij' (fun r _ => r - (a / τ v) • v) (fun r _ => r + (a / τ v) • v)
      ?_ ?_ ?_ ?_ <;> intro r hr <;> simp only [Finset.mem_filter, Finset.mem_univ,
        true_and, map_sub, map_add, map_smul] at hr ⊢
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, sub_self]
    · rw [hr, smul_eq_mul, div_mul_cancel₀ _ hv, zero_add]
    · rw [sub_add_cancel]
    · rw [add_sub_cancel_right]
  have hcard : Fintype.card V = ∑ a : F, #{r ∈ (univ : Finset V) | τ r = a} := by
    rw [← Finset.card_univ]
    exact Finset.card_eq_sum_card_fiberwise fun r _ => Finset.mem_univ (τ r)
  rw [hcard, Finset.sum_congr rfl fun a (_ : a ∈ univ) => hfib a, Finset.sum_const,
    Finset.card_univ, mul_comm, smul_eq_mul]
end MIPRE.LowDegree
