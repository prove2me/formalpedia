-- Prove2me | solution 1 for GraphProblems.stShapeColor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T18:41:15.78358+00:00
-- url     : https://prove2.me/submissions/c47cf0f5-89d3-4a0c-92a0-178434337f94

/- Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0; SPDX-License-Identifier: Apache-2.0.
Source and original notices: https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/eth/NOTICE -/
import Definitions.Def_GraphProblems_Blocks
import Definitions.Def_GraphProblems_Color
import Theorems.Thm_GraphProblems_Color_mem_pairs
import Theorems.Thm_GraphProblems_Color_idx_lt

set_option autoImplicit false
section
section
open GraphProblems
open Groundwork Groundwork.Prog CountKSat Finset
open Color
namespace GraphProblems
theorem _root_.solution : StShapeColor := by
  intro k n m C hC
  rw [colorF] at hC
  rcases List.mem_append.1 hC with hC | hC
  · rcases List.mem_append.1 hC with hC | hC
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hC
      refine ⟨by rw [List.length_map, List.length_range]; exact le_max_left _ _, fun l hl => ?_⟩
      obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hl
      exact idx_lt (List.mem_range.1 hv) (List.mem_range.1 hc)
    · obtain ⟨v, hv, hC⟩ := List.mem_flatMap.1 hC
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hC
      have hq1 := mem_pairs.1 (List.mem_filter.1 hq).1
      refine ⟨le_max_right _ _, fun l hl => ?_⟩
      rcases List.mem_pair.1 hl with rfl | rfl
      · exact idx_lt (List.mem_range.1 hv) hq1.1
      · exact idx_lt (List.mem_range.1 hv) hq1.2
  · obtain ⟨p, hp, hC⟩ := List.mem_flatMap.1 hC
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hC
    have hp1 := mem_pairs.1 (List.mem_filter.1 hp).1
    refine ⟨le_max_right _ _, fun l hl => ?_⟩
    rcases List.mem_pair.1 hl with rfl | rfl
    · exact idx_lt hp1.1 (List.mem_range.1 hc)
    · exact idx_lt hp1.2 (List.mem_range.1 hc)
end GraphProblems
