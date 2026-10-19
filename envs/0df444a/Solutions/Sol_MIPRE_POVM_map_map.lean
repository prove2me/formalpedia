-- Prove2me | solution 1 for MIPRE.POVM.map_map
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:45:06.881999+00:00
-- url     : https://prove2.me/submissions/63159cd4-00d0-46d1-af5b-bad7dec90f2a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Distances.lean (solution of MIPRE.POVM.map_map);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Theorems.Thm_MIPRE_POVM_ext_prime

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.POVM
open ComplexOrder Matrix
variable {n : Type*} [Fintype n]
variable {X A d : Type*} [Fintype X] [Fintype A] [Fintype d] [DecidableEq d]
theorem _root_.solution {B C : Type*} [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]
    (M : POVM A d) (f : A → B) (g : B → C) :
    (M.map f).map g = M.map fun a => g (f a) := by
  classical
  refine POVM.ext_prime fun c => ?_
  have hmaps : ∀ a ∈ Finset.univ.filter fun a => g (f a) = c,
      f a ∈ Finset.univ.filter fun b => g b = c := fun a ha =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp ha).2⟩
  have hfil : ∀ b ∈ Finset.univ.filter fun b => g b = c,
      (Finset.univ.filter fun a => g (f a) = c).filter (fun a => f a = b)
        = Finset.univ.filter fun a => f a = b := by
    intro b hb
    rw [Finset.filter_filter]
    refine Finset.filter_congr fun a _ => ⟨fun h => h.2, fun h => ⟨?_, h⟩⟩
    rw [h]
    exact (Finset.mem_filter.mp hb).2
  rw [POVM.map_mats, POVM.map_mats,
    ← Finset.sum_fiberwise_of_maps_to hmaps fun a => ((M.mats a).val)]
  exact Finset.sum_congr rfl fun b hb => by rw [POVM.map_mats, ← hfil b hb]
end MIPRE.POVM
