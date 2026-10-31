-- Prove2me | solution 1 for HuangN13.N13ConstructedSpecialization.specialCode_add
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-10-30T16:20:57.974527+00:00
-- url     : https://prove2.me/submissions/ab846e93-2b51-4b44-8d30-c8b205a6a103

import Mathlib
import Definitions.Def_MazurN13_L4
import Definitions.Def_HuangN13_SeparationDataCore
import Theorems.Thm_HuangN13_N13ConstructedSpecialization_chosen_code_balance

set_option autoImplicit false

namespace MazurProof.N13SpecialDegreeFourCode
end MazurProof.N13SpecialDegreeFourCode
section
section
set_option autoImplicit false
namespace MazurProof.N13ConstructedSpecialization
noncomputable section
open N13SpecialDivisorCharts N13CoherentChartComparison
open N13SpecialAbelCode hiding EffectiveDivisorTwo
open N13SpecialDegreeFourCode
theorem specialCode_add (P Q : G) : specialCode (P + Q) = specialCode P + specialCode Q := by
  have h := HuangN13.N13ConstructedSpecialization.chosen_code_balance P Q
  unfold specialCode
  linear_combination -h
end
end MazurProof.N13ConstructedSpecialization
end
end


set_option autoImplicit false
open Polynomial
theorem solution (P Q : MazurProof.N13ConstructedSpecialization.G) : MazurProof.N13ConstructedSpecialization.specialCode (P + Q) = MazurProof.N13ConstructedSpecialization.specialCode P + MazurProof.N13ConstructedSpecialization.specialCode Q := by
  exact MazurProof.N13ConstructedSpecialization.specialCode_add P Q
