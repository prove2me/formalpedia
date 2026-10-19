-- Prove2me | solution 1 for MIPRE.SAT.Circuit.DescribesDecider.of_pad
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:52:34.0893+00:00
-- url     : https://prove2.me/submissions/96015978-d2de-4072-a83a-e9028a966792

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/SAT/Padding.lean (solution of MIPRE.SAT.Circuit.DescribesDecider.of_pad);
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
import Theorems.Thm_MIPRE_SAT_Cnf5_sat_pad_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.SAT
section
/-- Beyond twice the answer length the tape is `10`, starting at the even position. -/
theorem tapeBits_eq_blank {s : Cost.BitStr} {T p : ℕ} (hs : s.length ≤ T) (hp : 2 * T ≤ p) :
    tapeBits s p = decide (p % 2 = 0) := by
  have hnone : s[p / 2]? = none := List.getElem?_eq_none (by omega)
  simp only [tapeBits, hnone, cellBits]
  split_ifs with h <;> simp [h]
end
end MIPRE.SAT

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SAT.Circuit.DescribesDecider
theorem _root_.solution {C C' : Circuit} {ℓ r ℓ' r' : ℕ}
    {D : Decider} {n T : ℕ} {x y : Cost.BitStr}
    (hC : C.DescribesDecider ℓ r D n x y T) (hℓ : ℓ ≤ ℓ') (hr : r ≤ r')
    (hT : 2 * T ≤ 2 ^ ℓ)
    (hpad : C'.formula5 ℓ' r' = Cnf5.pad hℓ hr (C.formula5 ℓ r)) :
    C'.DescribesDecider ℓ' r' D n x y T := by
  intro a b
  constructor
  · rintro ⟨w₁, w₂, w₃, hsat⟩
    rw [hpad, Cnf5.sat_pad_iff] at hsat
    obtain ⟨ap, bp, hap, hbp, ha, hb, hacc⟩ :=
      (hC (a ∘ Cnf5.blockInclusion hℓ) (b ∘ Cnf5.blockInclusion hℓ)).mp
        ⟨_, _, _, hsat.1⟩
    refine ⟨ap, bp, hap, hbp, ?_, ?_, hacc⟩
    · intro j
      by_cases hj : (j : ℕ) < 2 ^ ℓ
      · exact ha ⟨j, hj⟩
      · exact (hsat.2.1 j (by omega)).trans (tapeBits_eq_blank hap (by omega)).symm
    · intro j
      by_cases hj : (j : ℕ) < 2 ^ ℓ
      · exact hb ⟨j, hj⟩
      · exact (hsat.2.2 j (by omega)).trans (tapeBits_eq_blank hbp (by omega)).symm
  · rintro ⟨ap, bp, hap, hbp, ha, hb, hacc⟩
    obtain ⟨w₁, w₂, w₃, hsat⟩ :=
      (hC (a ∘ Cnf5.blockInclusion hℓ) (b ∘ Cnf5.blockInclusion hℓ)).mpr
        ⟨ap, bp, hap, hbp, (fun j => ha (Cnf5.blockInclusion hℓ j)),
          (fun j => hb (Cnf5.blockInclusion hℓ j)), hacc⟩
    refine ⟨Cnf5.extendBlock w₁, Cnf5.extendBlock w₂, Cnf5.extendBlock w₃, ?_⟩
    rw [hpad, Cnf5.sat_pad_iff]
    refine ⟨by simpa using hsat, ?_, ?_⟩
    · intro j hj
      exact (ha j).trans (tapeBits_eq_blank hap (by omega))
    · intro j hj
      exact (hb j).trans (tapeBits_eq_blank hbp (by omega))
end MIPRE.SAT.Circuit.DescribesDecider
