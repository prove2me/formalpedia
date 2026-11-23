-- Prove2me | solution 1 for LindbladTolerant.Testing.optimal_tolerant_testing
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:51.873329+00:00
-- url     : https://prove2.me/submissions/0f84ce74-e730-4d7c-b769-18fbf8ef708a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_LindbladTolerant_Testing_algorithm
import Theorems.Thm_LindbladTolerant_Testing_time_upper_bound
import Theorems.Thm_LindbladTolerant_Testing_time_lower_bound

set_option autoImplicit false
open scoped ComplexOrder

theorem solution : LindbladTolerant.Testing.UniformUpper ∧
    LindbladTolerant.Testing.UniformLower := by
  exact ⟨LindbladTolerant.Testing.time_upper_bound,
    LindbladTolerant.Testing.time_lower_bound⟩
