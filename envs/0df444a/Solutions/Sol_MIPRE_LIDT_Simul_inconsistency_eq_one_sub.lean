-- Prove2me | solution 1 for MIPRE.LIDT.Simul.inconsistency_eq_one_sub
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:46.26906+00:00
-- url     : https://prove2.me/submissions/2ca4d749-acb4-4794-bfdd-8f3c565c952f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Extraction.lean (solution of MIPRE.LIDT.Simul.inconsistency_eq_one_sub);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Background_LIDT_Coefficients
import Definitions.Def_MIPRE_Background_LIDT_Extraction
import Theorems.Thm_MIPRE_sum_bornProb

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Simul
open Finset MIPRE MIPRE.LIDT
open scoped Kronecker
open Matrix
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {K m d r : ℕ}
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
    {μ : X → ℝ} (hμ1 : ∑ x, μ x = 1) {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    (M : X → POVM A dA) (N : X → POVM A dB) :
    inconsistency μ ψ M N
      = 1 - ∑ x, μ x * ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
  have hx : ∀ x, (∑ a, ∑ b, if a = b then (0 : ℝ) else
      (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
      = 1 - ∑ a, bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
    intro x
    have h1 := sum_bornProb hψ (M x) (N x)
    have hsplit : ∀ a, (∑ b, if a = b then (0 : ℝ) else
        (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
        = ∑ b, bornProb ψ (((M x).mats a).val) (((N x).mats b).val)
          - bornProb ψ (((M x).mats a).val) (((N x).mats a).val) := by
      intro a
      have : ∀ b, (if a = b then (0 : ℝ) else
          (star ψ ⬝ᵥ ((((M x).mats a).val ⊗ₖ ((N x).mats b).val) *ᵥ ψ)).re)
          = bornProb ψ (((M x).mats a).val) (((N x).mats b).val)
            - if a = b then bornProb ψ (((M x).mats a).val) (((N x).mats b).val) else 0 := by
        intro b
        split_ifs <;> simp [bornProb]
      rw [Finset.sum_congr rfl fun b _ => this b, Finset.sum_sub_distrib, Finset.sum_ite_eq,
        if_pos (Finset.mem_univ a)]
    rw [Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_sub_distrib, h1]
  unfold inconsistency
  rw [Finset.sum_congr rfl fun x _ => by rw [hx x],
    Finset.sum_congr rfl fun x _ => mul_sub (μ x) 1 _, Finset.sum_sub_distrib]
  simp [hμ1]
end MIPRE.LIDT.Simul
