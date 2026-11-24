-- Prove2me | solution 1 for GlobalTheory.CongruenceIndex.congruence_finiteIndex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:21.232488+00:00
-- url     : https://prove2.me/submissions/410e90c3-2a9f-4444-90d4-a877ed0622f3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_CongruenceFiniteIndex
import Theorems.Thm_GlobalTheory_CongruenceIndex_exists_finset_cosets

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceIndex
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
open NumberField Matrix
open scoped nonZeroDivisors
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
  {Gm : Matrix (Fin r) (Fin r) E} {Λ : Submodule (𝓞 E) (Fin r → E)}
namespace GlobalTheory.CongruenceIndex
namespace _root_.GlobalTheory.CongruenceIndex
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M : ℕ) (Gm : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)), Λ.FG → 0 < M → ∃ Γ : Subgroup (GL (Fin r) E), (∀ γ, γ ∈ Γ ↔ _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ ∧ (∀ v ∈ Λ, ∃ w ∈ Λ, (γ : Matrix (Fin r) (Fin r) E) *ᵥ v = v + M • w)) ∧ ∃ S : Finset (GL (Fin r) E), ∀ γ, _root_.ReciprocityTheory.ChartRestriction.G.FD.IsUStab Gm Λ γ → ∃ s ∈ S, s⁻¹ * γ ∈ Γ := by
  intro E _ _ _ r M Gm Λ hΛ hM
  exact ⟨_root_.GlobalTheory.CongruenceIndex.congruenceSubgroup Gm Λ M, fun γ => Iff.rfl,
    _root_.GlobalTheory.CongruenceIndex.exists_finset_cosets (Gm := Gm) hΛ hM⟩
end _root_.GlobalTheory.CongruenceIndex
end GlobalTheory.CongruenceIndex
