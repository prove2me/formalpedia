-- Prove2me | solution 1 for GeneralPieces.Rate.nPat_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T05:06:15.867414+00:00
-- url     : https://prove2.me/submissions/d4f3ec0c-d1e1-40dc-afce-c5d18c268c47

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_ClauseBound_Gen_Rate_four_nRect_le
import Theorems.Thm_ClauseBound_Gen_Rate_nPat_le
import Theorems.Thm_ClauseBound_Gen_Rate_two_lam_le
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_TM_Run_trans
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hx : 18 ≤ x₀) (l lam B : ℕ) (hlam : 1 ≤ lam) :
    nPat P (step P x₀ l) lam ≤ (g x₀ l ^ 2 * (lam + B)) ^ (c * (g x₀ l ^ 4 / 4)) := by
  refine (nPat_le hP hx l lam B hlam).trans (Nat.pow_le_pow_right ?_ (Nat.mul_le_mul_left _ ?_))
  · have := two_lam_le hx l lam B; omega
  · have := four_nRect_le (g x₀ l); omega
end GeneralPieces.Rate
