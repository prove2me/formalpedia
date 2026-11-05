-- Prove2me | solution 1 for GeneralPieces.GenF.Yent_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:59:10.103317+00:00
-- url     : https://prove2.me/submissions/6825597d-8ab0-4ce9-b1ed-bb38cad7439e

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_ClauseBound_Boson_Basic_sum_erase_cast


set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
variable {R : Type} [CommRing R] [Algebra ℚ R]
namespace GeneralPieces.GenF
theorem _root_.solution (e : ℤ → R) (he : ∀ x y, e x * e y = e (x + y)) (n : ℕ) (b : List ℕ) (τ σ : Multiset ℕ) :
    Yent e (n :: b) τ σ = ∑ l ∈ τ.toFinset, ((bet n l : ℚ) • e ((l : ℤ) - n)) * Yent e b (τ.erase l) σ +
      ∑ k ∈ σ.toFinset, (((k : ℚ) * σ.count k * bet n (-(k : ℤ))) • e (-(k : ℤ) - n)) * Yent e b τ (σ.erase k) := by
  unfold Yent
  rw [op, nop, Int.cast_add, Int.cast_sum, Int.cast_sum, add_smul, Finset.sum_smul, Finset.sum_smul]
  congr 1
  · refine Finset.sum_congr rfl fun l hl => ?_
    have hl' := Multiset.mem_toFinset.1 hl
    rw [cre, if_pos hl', Basic.sum_erase_cast hl', smul_mul_smul_comm, he, Int.cast_mul, List.sum_cons, Nat.cast_add]
    congr 2
    · congr 2
      ring
    · ring
  · refine Finset.sum_congr rfl fun k hk => ?_
    have hk' := Multiset.mem_toFinset.1 hk
    rw [ann, Basic.sum_erase_cast hk', smul_mul_smul_comm, he, List.sum_cons, Nat.cast_add, show (τ.sum : ℤ) - σ.sum + k = τ.sum - (σ.sum - k) by ring,
      Int.cast_mul, Int.cast_mul, Int.cast_mul, Int.cast_natCast, Int.cast_natCast]
    congr 1
    · ring
    · congr 1
      ring
end GeneralPieces.GenF
