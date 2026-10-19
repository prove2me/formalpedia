-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.sum_sum_le_card_mul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:15.874936+00:00
-- url     : https://prove2.me/submissions/740267c7-9e12-4d25-a6af-f25495a98829

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.sum_sum_le_card_mul);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
/-- Averaging over a family, as a weight times a count of family members. -/
theorem sum_sum_filter_eq_sum_card {Seed ι : Type*} [Fintype Seed] [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (cond : Seed → ι → Prop) [∀ σ i, Decidable (cond σ i)] :
    (∑ σ : Seed, ∑ i ∈ Finset.univ.filter (fun i => cond σ i), w i)
      = ∑ i : ι, w i * (Finset.univ.filter (fun σ : Seed => cond σ i)).card := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution {S ι : Type*} [Fintype S] [Fintype ι] [DecidableEq ι]
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (cond : S → ι → Prop) [∀ σ i, Decidable (cond σ i)]
    (T : Finset ι) (B : ℝ) (M : ℕ)
    (hsub : ∀ σ i, cond σ i → i ∈ T) (hB : ∀ i ∈ T, w i ≤ B)
    (hM : ∀ i ∈ T, (Finset.univ.filter (fun σ : S => cond σ i)).card ≤ M) :
    (∑ σ : S, ∑ i ∈ Finset.univ.filter (fun i => cond σ i), w i)
      ≤ (T.card : ℝ) * (B * M) := by
  classical
  rw [sum_sum_filter_eq_sum_card]
  rw [← Finset.sum_subset (Finset.subset_univ T) (fun i _ hi => ?_)]
  · refine (Finset.sum_le_card_nsmul T _ (B * M) ?_).trans ?_
    · intro i hi
      refine mul_le_mul (hB i hi) ?_ (Nat.cast_nonneg _) (le_trans (hw i) (hB i hi))
      exact_mod_cast hM i hi
    · rw [nsmul_eq_mul]
  · have he : (Finset.univ.filter (fun σ : S => cond σ i)) = ∅ :=
      Finset.eq_empty_iff_forall_notMem.mpr fun σ hσ =>
        hi (hsub σ i (Finset.mem_filter.mp hσ).2)
    rw [he]
    simp
end MIPRE.LIDT.Adapter
