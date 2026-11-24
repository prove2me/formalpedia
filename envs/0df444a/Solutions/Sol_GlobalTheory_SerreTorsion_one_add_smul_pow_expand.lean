-- Prove2me | solution 1 for GlobalTheory.SerreTorsion.one_add_smul_pow_expand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:00:09.043799+00:00
-- url     : https://prove2.me/submissions/d743d586-c7c6-4130-95e3-62a60f830e4a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqOneOfPowEqOneOfCongrOne
import Theorems.Thm_GlobalTheory_SerreTorsion_one_add_pow_expand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.SerreTorsion
variable {E : Type} [Ring E]
namespace GlobalTheory.SerreTorsion
theorem _root_.solution (c : ℕ) (ψ : E) (n : ℕ) :
    ∃ z : E, (1 + c • ψ) ^ n = 1 + c • (n • ψ + (n.choose 2 * c) • ψ ^ 2 + (c ^ 2) • z) := by
  obtain ⟨y, hy⟩ := one_add_pow_expand (c • ψ) n
  refine ⟨ψ ^ 3 * y, ?_⟩
  rw [hy, smul_pow, smul_pow, smul_mul_assoc]
  module
end GlobalTheory.SerreTorsion
