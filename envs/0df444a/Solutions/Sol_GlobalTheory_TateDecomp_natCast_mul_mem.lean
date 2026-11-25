-- Prove2me | solution 1 for GlobalTheory.TateDecomp.natCast_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:34:15.412198+00:00
-- url     : https://prove2.me/submissions/4e6a8876-74f0-4708-a7c0-5a8d3185a863

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_LevelLetterCocycles_DataNLoc
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_HTBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IntegersEqSumZetaPowStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TateDecompositionCompletedCyclotomicIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.TateDecomp
variable {l : ℕ} [Fact l.Prime]
namespace GlobalTheory.TateDecomp
theorem _root_.solution {G : AddSubgroup (PadicComplex l)} {x : PadicComplex l} (hx : x ∈ G)
    (m : ℕ) : (l : PadicComplex l) ^ m * x ∈ G := by
  have := nsmul_mem hx (l ^ m)
  rwa [nsmul_eq_mul, Nat.cast_pow] at this
end GlobalTheory.TateDecomp
