-- Prove2me | solution 1 for GlobalTheory.SW.Vac.exists_ex_of_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:48:30.559909+00:00
-- url     : https://prove2.me/submissions/3823f41c-5c8d-4780-8027-48eb5498bf21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInnerProductSelfNonnegBoundsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsExOfPow

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Vac
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.Vac
theorem _root_.solution {z : ℂ} {m : ℕ} (hm : 0 < m) (h : z ^ m = 1) :
    ∃ r : ℚ, z * ex (2 * r) = 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨i, -, hi⟩ := (Complex.isPrimitiveRoot_exp m hm.ne').eq_pow_of_pow_eq_one h
  refine ⟨-(i / m), ?_⟩
  rw [← hi, ex, ← Complex.exp_nat_mul, ← Complex.exp_add]
  have : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [← Complex.exp_zero]; congr 1
  push_cast; field_simp; ring
end GlobalTheory.SW.Vac
