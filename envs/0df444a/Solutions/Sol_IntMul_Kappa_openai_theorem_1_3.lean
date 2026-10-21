-- Prove2me | solution 3 for IntMul.Kappa.openai_theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-16T21:36:19.952206+00:00
-- url     : https://prove2.me/submissions/4c50079b-fc4f-46b4-8df6-9281c207723d

import Mathlib
import Definitions.Def_IntMul_MultitapeModel
import Definitions.Def_IntMul_KappaFramework
import Definitions.Def_IntMul_KappaJainData
import Theorems.Thm_IntMul_Kappa_jain_round6_framework
import Theorems.Thm_IntMul_Kappa_openai_round6_small_moments
import Theorems.Thm_IntMul_Kappa_openai_round6_easy_assembly

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open IntMul IntMul.Kappa

theorem solution : KappaBound (1 / 2 ^ 182) := by
  obtain ⟨hbit, hcx⟩ := IntMul.Kappa.openai_round6_small_moments
  exact IntMul.Kappa.jain_round6_framework
    (1 / 10 ^ 7) (1 / 10 ^ 7) (1 / 2) (10 ^ 15) (10 ^ 15)
    (1 / 2 ^ 182) (by norm_num) (by norm_num)
    hbit hcx IntMul.Kappa.openai_round6_easy_assembly
