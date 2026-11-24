-- Prove2me | solution 1 for GlobalTheory.SW.IpPos.hasLevel_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:34:05.413088+00:00
-- url     : https://prove2.me/submissions/c770fbd7-7072-4352-858e-2dc7b087fb7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_FinsumQuotientOfLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBounds
import Theorems.Thm_GlobalTheory_SW_IpPos_intM_natCast_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.IpPos
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
open Matrix Complex
open scoped ComplexConjugate Real
open NumberField
variable {K κ ι : Type} [Field K] [NumberField K] [Fintype κ] [Fintype ι]
omit [NumberField K] [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.IpPos
namespace _root_.GlobalTheory.SW.IpPos
theorem _root_.solution {R : ℕ} {φ : Matrix κ ι K → ℂ} (h : _root_.GlobalTheory.SW.HasLevel R φ)
    (S : ℕ) : _root_.GlobalTheory.SW.HasLevel (R * S) φ := by
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · rw [Nat.cast_mul, mul_comm, mul_smul]
    exact _root_.GlobalTheory.SW.IpPos.intM_natCast_smul S (h.1 x hx)
  · rw [Nat.cast_mul, mul_smul]
    exact h.2 x _ (_root_.GlobalTheory.SW.IpPos.intM_natCast_smul S hy)
end _root_.GlobalTheory.SW.IpPos
end GlobalTheory.SW.IpPos
