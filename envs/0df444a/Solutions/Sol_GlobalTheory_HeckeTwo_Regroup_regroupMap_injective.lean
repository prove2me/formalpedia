-- Prove2me | solution 1 for GlobalTheory.HeckeTwo.Regroup.regroupMap_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:44:57.472808+00:00
-- url     : https://prove2.me/submissions/54bee712-e409-4cbd-991e-67e2be13daa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PartialZetaFunctionalEquation_ee0156e8c041b1a2
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KFacDifferentiable
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TsumLatticePairUnitQuotientRegroup
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_unit_eq_one
import Theorems.Thm_GlobalTheory_HeckeTwo_Regroup_mkU_eq

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
open GlobalTheory GlobalTheory.HeckeTwo GlobalTheory.HeckeTwo.Regroup
variable {F : Type} [Field F] [NumberField F]
variable (𝔞 𝔟 : Frac F)
namespace GlobalTheory.HeckeTwo.Regroup
theorem _root_.solution : Function.Injective (regroupMap 𝔞 𝔟) := by
  rintro (c | ⟨c, a⟩) (c' | ⟨c', a'⟩) h
  · obtain ⟨ε, h1, -⟩ := Quotient.exact h
    congr 1
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    exact mkU_eq ε h1
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    exact absurd (h2.trans (mul_zero _)) c'.out.2.2
  · obtain ⟨ε, -, h2⟩ := Quotient.exact h
    dsimp only [leftPt, rightPt] at h2
    have := congrArg (fun x => (((ε⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * x) h2
    simp only [← mul_assoc, unit_inv_mul, one_mul, mul_zero] at this
    exact absurd this.symm c.out.2.2
  · obtain ⟨ε, h1, h2⟩ := Quotient.exact h
    have hc : c = c' := by
      rw [← Quotient.out_eq c, ← Quotient.out_eq c']
      exact mkU_eq ε h2
    subst hc
    have hε : ε = 1 := unit_eq_one c.out.2.2 h2.symm
    subst hε
    have ha : a' = a := Subtype.ext (by simpa [rightPt] using h1)
    subst ha
    rfl
end GlobalTheory.HeckeTwo.Regroup
