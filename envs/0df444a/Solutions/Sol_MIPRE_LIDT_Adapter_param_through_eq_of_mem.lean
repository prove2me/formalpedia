-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.param_through_eq_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:36.664983+00:00
-- url     : https://prove2.me/submissions/fc590861-9256-4570-b2fa-26939185f762

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (solution of MIPRE.LIDT.Adapter.param_through_eq_of_mem);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
theorem _root_.solution {v : Fin n → F} (hv : ∃ j, v j ≠ 0) (u : Fin n → F) (t : F) :
    Line.param (Line.through u v) ((Line.through u v).1 + t • (Line.through u v).2) = t := by
  classical
  set j := Fin.find (fun k => v k ≠ 0) hv with hj
  have hvj : v j ≠ 0 := Fin.find_spec hv
  have hthr : Line.through u v = (u - u j • ((v j)⁻¹ • v), (v j)⁻¹ • v) := by
    rw [Line.through, dif_pos hv]
  have hd2 : (Line.through u v).2 = (v j)⁻¹ • v := by rw [hthr]
  have hex' : ∃ k, ((Line.through u v).2) k ≠ 0 := by
    refine ⟨j, ?_⟩
    rw [hd2]
    simpa using mul_ne_zero (inv_ne_zero hvj) hvj
  have hfind : Fin.find (fun k => ((Line.through u v).2) k ≠ 0) hex' = j := by
    rw [Fin.find_eq_iff]
    refine ⟨?_, fun k hk => ?_⟩
    · rw [hd2]
      simpa using mul_ne_zero (inv_ne_zero hvj) hvj
    · have h0 : v k = 0 := not_not.mp (Fin.find_min hv (hj ▸ hk))
      rw [hd2]
      simp [h0]
  have hb : (Line.through u v).1 j = 0 := by
    rw [hthr]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [inv_mul_cancel₀ hvj, mul_one, sub_self]
  have hd : (Line.through u v).2 j = 1 := by
    rw [hd2]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact inv_mul_cancel₀ hvj
  simp only [Line.param, dif_pos hex', hfind, Pi.add_apply, Pi.smul_apply, smul_eq_mul, hb, hd,
    mul_one, zero_add]
end MIPRE.LIDT.Adapter
