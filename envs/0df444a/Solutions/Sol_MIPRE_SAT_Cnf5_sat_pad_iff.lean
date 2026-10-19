-- Prove2me | solution 1 for MIPRE.SAT.Cnf5.sat_pad_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:50:12.717984+00:00
-- url     : https://prove2.me/submissions/6f11d812-16d2-42c9-8cf6-6035506a1296

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Padding.lean (solution of MIPRE.SAT.Cnf5.sat_pad_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
import Definitions.Def_MIPRE_Foundations_SAT_Decoupled
import Definitions.Def_MIPRE_Foundations_SAT_Padding

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Cnf5
theorem _root_.solution {ℓ r ℓ' r' : ℕ} (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (φ : Cnf5 (Fin (2 ^ ℓ)) (Fin (2 ^ ℓ))
      (Fin (2 ^ r)) (Fin (2 ^ r)) (Fin (2 ^ r)))
    (a b : Fin (2 ^ ℓ') → Bool) (w₁ w₂ w₃ : Fin (2 ^ r') → Bool) :
    (pad hℓ hr φ).Sat a b w₁ w₂ w₃ ↔
      φ.Sat (a ∘ blockInclusion hℓ) (b ∘ blockInclusion hℓ)
        (w₁ ∘ blockInclusion hr) (w₂ ∘ blockInclusion hr) (w₃ ∘ blockInclusion hr) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → a i = decide ((i : ℕ) % 2 = 0)) ∧
      (∀ i : Fin (2 ^ ℓ'), 2 ^ ℓ ≤ (i : ℕ) → b i = decide ((i : ℕ) % 2 = 0)) := by
  constructor
  · intro h
    refine ⟨fun c hc => h _ (Or.inl ⟨c, hc, rfl⟩), ?_, ?_⟩
    · intro i hi
      have h' := h ⟨⟨i, decide ((i : ℕ) % 2 = 0)⟩,
        falseLit b, falseLit w₁, falseLit w₂, falseLit w₃⟩ (Or.inr (Or.inl ⟨hi, rfl⟩))
      exact (lit_true_iff a i _).mp (by simpa [Clause5.eval, eval_falseLit] using h')
    · intro i hi
      have h' := h ⟨falseLit a, ⟨i, decide ((i : ℕ) % 2 = 0)⟩,
        falseLit w₁, falseLit w₂, falseLit w₃⟩ (Or.inr (Or.inr ⟨hi, rfl⟩))
      exact (lit_true_iff b i _).mp (by simpa [Clause5.eval, eval_falseLit] using h')
  · rintro ⟨hφ, ha, hb⟩ c (⟨c₀, hc₀, rfl⟩ | ⟨hi, ho⟩ | ⟨hi, ho⟩)
    · exact hφ c₀ hc₀
    · have h : c.l₁.eval a = true := (lit_true_iff a c.l₁.var c.l₁.pos).mpr
        ((ha c.l₁.var hi).trans ho.symm)
      simp [Clause5.eval, h]
    · have h : c.l₂.eval b = true := (lit_true_iff b c.l₂.var c.l₂.pos).mpr
        ((hb c.l₂.var hi).trans ho.symm)
      simp [Clause5.eval, h]
end MIPRE.SAT.Cnf5
