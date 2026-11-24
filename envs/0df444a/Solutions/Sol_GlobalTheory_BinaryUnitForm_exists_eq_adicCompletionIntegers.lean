-- Prove2me | solution 1 for GlobalTheory.BinaryUnitForm.exists_eq_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:54:53.243995+00:00
-- url     : https://prove2.me/submissions/764e8169-2ee1-488b-b307-5187dcc79111

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsEqTransposeMulMapOfIdempotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_FiniteResidueFieldAdicCompletionIntegers
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
import Theorems.Thm_GlobalTheory_BinaryUnitForm_exists_eq_of_henselian
import Theorems.Thm_GlobalTheory_SelfDualGenus_finite_residueField_adicCompletionIntegers
import Theorems.Thm_GlobalTheory_SelfDualGenus_isAdicComplete_adicCompletionIntegers


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField IsLocalRing
open GlobalTheory GlobalTheory.BinaryUnitForm
namespace GlobalTheory.BinaryUnitForm
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F),
    IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F,
      r ^ 2 + t * r * s + n * s ^ 2 = u := by
  intro F _ _ v t n u hD hu
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  exact exists_eq_of_henselian t n u hD hu
end GlobalTheory.BinaryUnitForm
