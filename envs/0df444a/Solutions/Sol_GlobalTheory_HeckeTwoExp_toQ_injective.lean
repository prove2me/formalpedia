-- Prove2me | solution 1 for GlobalTheory.HeckeTwoExp.toQ_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:33.592191+00:00
-- url     : https://prove2.me/submissions/4254d30b-71f7-413b-ba6e-bd4abd98a3f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AbsNormEqProd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
noncomputable section
open GlobalTheory GlobalTheory.HeckeTwoExp
variable {F : Type} [Field F] [NumberField F]
namespace GlobalTheory.HeckeTwoExp
theorem _root_.solution (𝔞 𝔟 : Frac F) : Function.Injective (toQ 𝔞 𝔟) := by
  rintro ⟨c, ν⟩ ⟨c', ν'⟩ h
  obtain ⟨ε, h1, h2⟩ := Quotient.exact h
  dsimp only at h1 h2
  have hc : c = c' := by
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact Quotient.sound ⟨ε, h2⟩
  subst hc
  have hne : c.out.1 ≠ 0 := c.out.2.2
  have hε : ((ε : 𝓞 F) : F) = 1 := by
    have h3 : (((ε : 𝓞 F) : F) - 1) * c.out.1 = 0 := by linear_combination -h2
    exact sub_eq_zero.1 ((mul_eq_zero.1 h3).resolve_right hne)
  have hε' : (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) = 1 := by
    have := unit_inv_mul ε; rw [hε, mul_one] at this; exact this
  rw [hε', one_mul] at h1
  have : ν = ν' := Subtype.ext (Subtype.ext h1.symm)
  subst this
  rfl
end GlobalTheory.HeckeTwoExp
