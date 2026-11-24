-- Prove2me | solution 1 for GlobalTheory.GLintCover.v_eq_one_of_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:04.825196+00:00
-- url     : https://prove2.me/submissions/4d8b4e73-f3f0-4faf-8f2c-bf07e0a936ce

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_KpqSubgroupCompact
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsAdicCompleteAndCardQuotientAdicCompletionInteg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_DetCoverMatrixValuationOne
import Theorems.Thm_Formalism_UG_Final_KpqSubgroupCompact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open Formalism.UG (GLint)
noncomputable section
open GlobalTheory GlobalTheory.GLintCover
variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}
namespace GlobalTheory.GLintCover
theorem _root_.solution {x y : v.adicCompletion F} (hx : x ∈ Formalism.UG.Ov F v) (hy : y ∈ Formalism.UG.Ov F v)
    (hxy : x * y = 1) : Valued.v x = 1 := by
  have h1 : Valued.v x * Valued.v y = 1 := by rw [← map_mul, hxy, map_one]
  have hy1 : Valued.v y ≤ 1 := hy
  have hx1 : Valued.v x ≤ 1 := hx
  refine le_antisymm hx1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = Valued.v x * Valued.v y := h1.symm
    _ ≤ Valued.v x := mul_le_of_le_one_right' hy1
end GlobalTheory.GLintCover
