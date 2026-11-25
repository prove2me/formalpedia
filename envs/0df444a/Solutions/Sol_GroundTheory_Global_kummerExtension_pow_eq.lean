-- Prove2me | solution 1 for GroundTheory.Global.kummerExtension_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T06:59:43.146796+00:00
-- url     : https://prove2.me/submissions/d3c4aa64-644c-42c9-b293-9dada8cea64c

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Degree
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingInfinite
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_SplittingKummer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.Global
open IsDedekindDomain NumberField Module IntermediateField GroundTheory.ProfCoh
open scoped TensorProduct
variable {K : Type*} [Field K] {n : ℕ} [NeZero n] [HasEnoughRootsOfUnity K n]
  {Ω : Type*} [Field Ω] [Algebra K Ω] {Δ : Subgroup Kˣ}
  {F E : Type*} [Field F] [Field E] [Algebra K F] [Algebra F E] [Algebra K E]
  [IsScalarTower K F E]
omit [NeZero n] [HasEnoughRootsOfUnity K n] [IsScalarTower K F E]
namespace GroundTheory.Global
theorem _root_.solution {y : kummerExtension K n Ω Δ} {a : K}
    (hy : (y : Ω) ^ n = algebraMap K Ω a) :
    y ^ n = algebraMap K (kummerExtension K n Ω Δ) a :=
  Subtype.ext (by rw [IntermediateField.coe_pow, hy]; rfl)
end GroundTheory.Global
