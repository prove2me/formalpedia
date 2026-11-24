-- Prove2me | solution 1 for GlobalTheory.LagSplit.mem_range_secH_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:25:57.052494+00:00
-- url     : https://prove2.me/submissions/8fb624ac-4e9e-4383-a0d3-a4b0f384d576

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SymplecticGenerators_SymplecticCharacters_SubConjTransposeOfSymm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_BetaEqZeroOfCharacter
import Theorems.Thm_GlobalTheory_LagSplit_secH_apply
import Theorems.Thm_GlobalTheory_LagSplit_perProj_eq_zero_iff
import Theorems.Thm_GlobalTheory_LagSplit_two_I_imC_inv_mul
import Theorems.Thm_GlobalTheory_LagSplit_star_mulVec_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Key.Chi
open GlobalTheory GlobalTheory.LagSplit
variable {g : ℕ}
namespace GlobalTheory.LagSplit
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hY : IsUnit (τ.map Complex.im).det)
    (u : Fin g ⊕ Fin g → ℂ) : u ∈ LinearMap.range (secH τ) ↔ perProj τ (star u) = 0 := by
  have key : perProj τ (star u) = 0 ↔ u ∘ Sum.inl = -(τ.map star *ᵥ (u ∘ Sum.inr)) := by
    rw [perProj_eq_zero_iff, ← star_inj, star_neg, star_mulVec_map]
    have h1 : star ((star u) ∘ Sum.inl) = u ∘ (Sum.inl : Fin g → _) := by ext i; simp
    have h2 : star ((star u) ∘ Sum.inr) = u ∘ (Sum.inr : Fin g → _) := by ext i; simp
    rw [h1, h2]
  rw [key]
  constructor
  · rintro ⟨z, rfl⟩
    simp [secH_apply]
  · intro h
    refine ⟨((2 * I) • imC τ) *ᵥ (u ∘ Sum.inr), ?_⟩
    rw [secH_apply, Matrix.mulVec_mulVec (u ∘ Sum.inr), two_I_imC_inv_mul hY, Matrix.one_mulVec, ← h]
    ext (i | i) <;> rfl
end GlobalTheory.LagSplit
