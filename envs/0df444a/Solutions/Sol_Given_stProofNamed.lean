-- Prove2me | solution 1 for Given.stProofNamed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T11:25:07.538205+00:00
-- url     : https://prove2.me/submissions/9835e89c-e2f1-40e0-ae11-9e0f56bea8ef

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_Given_Level
import Mathlib.Tactic
import Definitions.Def_Given_End
import Theorems.Thm_Given_onFormula
import Theorems.Thm_Eight_ViaGrouping_Correct_onFormula
import Theorems.Thm_Eight_two_le_of_le
import Theorems.Thm_P2M_ClauseBound_ParityChecks_Params_Big_hA__29d1a60c342c
import Theorems.Thm_P2M_Eight_delta__le_fd4e6e087c27
import Theorems.Thm_Printed_cost_of_bound
import Theorems.Thm_Printed_decidesSparse_of_cost
import Theorems.Thm_Printed_onFormula
import Theorems.Thm_Printed_stGroupingPoly
import Theorems.Thm_Printed_stGroupingTied
import Theorems.Thm_Suffices_stSuffices


set_option autoImplicit false
section
section
open Given
open Finset Groundwork Groundwork.Prog Groundwork.Prog.Count Eight Eight.SecNetworks Eight.ViaGrouping Paper QueryMachines Printed
namespace Given
theorem _root_.solution : StProofNamed := by
  intro δ Mc τ K M Cc hδ hδ1 hM hEn hK hp hA
  have hM' : (1 : ℝ) ≤ Mc := by exact_mod_cast hM
  -- «Let … δ' = δ/(3M) ≤ 1/3.»
  have hδ' : 0 < δ / (3 * (Mc : ℝ)) := div_pos hδ (by linarith)
  have h3 := Eight.delta'_le hδ1 hM'
  have hK2 := Eight.two_le_of_le hδ' h3 hK
  -- Lemma 1 for (K, δ'/12)
  obtain ⟨C₁, hC₁⟩ := stGroupingTied K _ M Cc hK2 (by positivity) hA
  have hg : 0 < 3 * K ^ 8 := Nat.mul_pos (by norm_num) (pow_pos (by omega) 8)
  -- the network of Φ and the paragraph «Cost»
  obtain ⟨hpoly, hbound⟩ := onFormula hg 3 hC₁
  obtain ⟨A, hA'⟩ := cost_of_bound hδ' (by linarith) hg hK hbound
  -- «By Lemma 4 with ε = δ/3, it suffices …», «so the total time is O(2^{δn})»
  have hs := Suffices.stSuffices δ Mc τ hδ hM hEn
  exact ⟨hs.1 _ (hpoly (stGroupingPoly _ _ _ hp)), hs.2 _ A (decidesSparse_of_cost hA')⟩
end Given
