-- Prove2me | solution 1 for GeneralPieces.Rate.capSum_le_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T04:46:09.584303+00:00
-- url     : https://prove2.me/submissions/8e0c0e46-f444-4335-829d-04a16bcc4801

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GeneralPieces_Rec_Chain
import Definitions.Def_GeneralPieces_Num_PartAUse
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_ClauseBound_Gen_Rate
import Definitions.Def_GeneralPieces_Rec_Rate
import Theorems.Thm_Groundwork_PolyT_all
import Theorems.Thm_Groundwork_Prog_NetE_cap_le
attribute [local fun_prop] Groundwork.PolyT.all



set_option autoImplicit false
section
section
open GeneralPieces GeneralPieces.Rate
open Groundwork PaddedDescent.F ClauseBound.Alg ClauseBound.Gen ClauseBound.Gen.Rate Levels.Gen
variable {P : PiecesF} {ρ : ℝ} {c x₀ : ℕ}
namespace GeneralPieces.Rate
theorem _root_.solution (hP : Par P ρ c) (hm : P.m = 1) (lam : ℕ) (hlam : 1 ≤ lam) : capSum P 0 lam ≤ 4 * lam := by
  unfold capSum
  apply Finset.sup_le
  intro i hi
  have hi' := Finset.mem_range.1 hi
  have h1 := (hP.spec 0 lam hlam).cap_le false i hi'
  have h2 := (hP.spec 0 lam hlam).cap_le true i hi'
  rw [hm] at h1 h2
  omega
end GeneralPieces.Rate
