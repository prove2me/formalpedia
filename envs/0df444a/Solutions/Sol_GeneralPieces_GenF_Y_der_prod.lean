-- Prove2me | solution 1 for GeneralPieces.GenF.Y.der_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T22:59:15.495733+00:00
-- url     : https://prove2.me/submissions/5d686cdd-5761-4223-913b-f9e15c9e7f2c

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_GenF_Borel
import Definitions.Def_GeneralPieces_GenF_NormalL
import Definitions.Def_ClauseBound_Boson_Basic
import Definitions.Def_GeneralPieces_GenF_Y
import Theorems.Thm_GeneralPieces_Series_cf_add
import Theorems.Thm_GeneralPieces_Series_cf_neg
import Theorems.Thm_GeneralPieces_Series_cf_smul
import Theorems.Thm_GeneralPieces_Series_cf_sub
import Theorems.Thm_GeneralPieces_Series_cf_zero
attribute [local simp] GeneralPieces.Series.cf_add
attribute [local simp] GeneralPieces.Series.cf_neg
attribute [local simp] GeneralPieces.Series.cf_smul
attribute [local simp] GeneralPieces.Series.cf_sub
attribute [local simp] GeneralPieces.Series.cf_zero



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.GenF
open GeneralPieces.Series ClauseBound.Boson MvPowerSeries
open GeneralPieces.GenF.Y
namespace GeneralPieces.GenF.Y
theorem _root_.solution {R B ι : Type} [CommRing R] [CommRing B] [Algebra R B] [DecidableEq ι] (d : Derivation R B B) (s : Multiset ι) (f : ι → B) :
    d (s.map f).prod = ∑ k ∈ s.toFinset, s.count k • (d (f k) * ((s.erase k).map f).prod) := by
  rw [← Finset.sum_multiset_map_count]
  induction s using Multiset.induction_on with
  | empty => simp
  | cons k s ih =>
    rw [Multiset.map_cons, Multiset.prod_cons, Derivation.leibniz, smul_eq_mul, smul_eq_mul, ih, Multiset.map_cons, Multiset.sum_cons, Multiset.erase_cons_head, add_comm,
      ← Multiset.sum_map_mul_left, mul_comm]
    congr 1
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun j hj => ?_)
    rw [Multiset.erase_cons_tail_of_mem hj, Multiset.map_cons, Multiset.prod_cons]
    ring
end GeneralPieces.GenF.Y
